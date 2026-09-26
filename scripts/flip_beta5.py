#!/usr/bin/env python3
"""β.5's ACTUAL edit, driven to a FIXPOINT — the flip that does not stop
(DOCS item 263).

Every flip in row 12 prints its own ceiling:

    LOWER BOUND — the build stopped at the first failing module, so no
    definition behind it was attempted

`dropClose`, `PendingNode.close_with_ssl` and `PendingNode.pendingFlow` all
live in `L4YAML/Proofs/Production/StreamAccum.lean`, which the library root
imports.  `lake build` dies there, so **not one of item 238's twenty-four
reproofs has ever been elaborated against a post-β.5 source tree**.  The graph
walk in `Tests/Guards/Proofs/DropDependents.lean` reads twenty-six instead, and
a dependency closure is a CEILING: it prices a rebuild, not a rewrite.

This gate removes the ceiling.  It applies β.5's edit for real —

    retire   `PendingNode.pendingFlow`, constructor, docstring and
             `close_with_ssl`'s arm together (`flip_supplier.py --end retire`)
    drop     `SLYamlStream.scannerDrop`, arm and docstring (`flip_drop.py`)
    delete   `dropClose`, which item 238 measured as the arm RESTATED and item
             239 refuted in the post-β.5 model.  Sorrying it instead would
             carry its one consumer on a lemma known to be false, so it goes.

— and then LOOPS: build, read the broken declarations, replace each broken
declaration's PROOF with `sorry` leaving its statement byte-identical, rebuild.
The rounds are the waves.  Round 1 is what the truncated flips already see;
everything after it is what nothing in this row has looked at.

## Why `sorry` is the right patch and what it separates

A consumer depends on its supplier's TYPE, not on its proof (item 238's `S=0`,
and Lean's definitional proof irrelevance is exact about it).  `sorry` keeps the
type and loses only the proof, so the fixpoint splits the two edges that walk
could only separate on paper:

    BROKEN       the declaration's own proof does not elaborate — it owes work
    RESTATEMENT  the error is in its STATEMENT, so no proof can fix it
    CARRIED      it elaborates, but only because a sorried supplier does
    FREE         it elaborates on its standing axiom profile

**The last two are the reason this gate does not stop at a green build.**  A
tree that builds with seven sorries in it is not a tree that is proved, and
reading the fixpoint's silence as "the other seventeen are free" would be §8's
*a clean build is not a proof* committed by the instrument that exists to
refute it.  So the gate ends with an axiom census over the twenty-four and
reports CARRIED and FREE apart.

## What it cannot see

**Propagation, never truth.**  A declaration that still elaborates may be FALSE
in the post-β.5 model — item 239 proved exactly that for `close_with_ssl`,
which item 238's graph had called reprovable.  This gate prices the BUILD.
Falsity is `Tests/Guards/Proofs/DropFalsity.lean`'s question and is not asked
here.

Destructive while it runs — it edits two library files in place — so every one
is restored from its own backup in a `finally` and the md5s are printed at both
ends.  A run that dies between them leaves the backups beside the sources.

    scripts/flip_beta5.py                    # the whole fixpoint
    scripts/flip_beta5.py --max-rounds 3     # stop early, still restores
    scripts/flip_beta5.py --log-dir DIR      # keep every round's build log
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ACC = ROOT / "L4YAML" / "Proofs" / "Production" / "StreamAccum.lean"
DOC = ROOT / "L4YAML" / "Surface" / "Document.lean"

_here = Path(__file__).resolve().parent


def _load(name: str, fname: str):
    spec = importlib.util.spec_from_file_location(name, _here / fname)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


#: One instrument, five gates: item 210's error mapper and the two existing
#: flips' own edits, so this gate cannot drift from them in silence.
flip210 = _load("flip210", "flip_210.py")
flipdrop = _load("flipdrop", "flip_drop.py")
flipsup = _load("flipsup", "flip_supplier.py")

#: `dropClose`, docstring and body.  Anchored on content (item 210's rule).
DROPCLOSE = (
    "/-- The flow share of the escape, spent at one place: the OPAQUE resume a\n"
    "    depth-0 flow open hands `pendingFlow`, the one park with nothing to\n"
    "    compose through.  The gap constructor absorbs any span, so one captured\n"
    "    stream serves every position. -/\n"
    "lemma dropClose {sp_start sp_x : SurfPos} (h_stream : SLYamlStream sp_start sp_x) :\n"
    "    ∀ sp_e sp_m, SSLComments sp_e sp_m → SLYamlStream sp_start sp_m :=\n"
    "  fun _ sp_m h_ssl => SLYamlStream.scannerDrop sp_start sp_x _ sp_m h_stream h_ssl\n")

#: A declaration whose proof may be replaced by `sorry`.  A data `def` may NOT:
#: `sorry` keeps a Prop's type and loses only its proof, but it changes a data
#: definition's VALUE, and every `rfl`, `decide` and `native_decide` above it
#: then breaks for a reason that is this gate's and not β.5's.  One silent one
#: here would inflate every later wave, so the gate refuses and says so.
PROP_KEYWORDS = ("lemma", "theorem", "example")

#: `flip_210.DECL_HEAD` with `example` added.  Item 229's rule puts this row's
#: exhibits in `example`s, and a walk that cannot name one reports it as a hole
#: — the control run stalled on exactly that.  `flip_210`'s own regex is NOT
#: widened: four standing gates quote counts taken with it.
HEAD = re.compile(
    r"^(?:private |protected |@\[[^\]]*\]\s*)*"
    r"(?:lemma|theorem|def|abbrev|instance|structure|inductive|example)"
    r"(?: ([A-Za-z_][A-Za-z0-9_'!?.]*)|\b)")

#: Terminates a declaration's span.  Anything at column 0 that opens a new
#: top-level form; the span between two of these is one declaration.
TERMINATOR = re.compile(
    r"^(/--|/-!|-{2,}|@\[|end\b|namespace\b|section\b|open\b|variable\b|"
    r"attribute\b|run_cmd\b|#|set_option\b|private\b|protected\b|noncomputable\b|"
    r"lemma\b|theorem\b|def\b|abbrev\b|instance\b|structure\b|inductive\b|"
    r"example\b|macro\b|syntax\b|elab\b|deriving\b|import\b)")


# ---------------------------------------------------------------------------
# The edit
# ---------------------------------------------------------------------------

def beta5_edits() -> dict[Path, str]:
    """β.5's three deletions, each taken from the gate that already owns it."""
    acc = ACC.read_text()
    acc = flipsup._edit_retire(acc)          # the park, arm and docstring
    n = acc.count(DROPCLOSE)
    if n != 1:
        sys.exit(f"expected exactly one `dropClose` block in "
                 f"{ACC.relative_to(ROOT)}, found {n}; the lemma moved and this "
                 "gate needs re-aiming")
    acc = acc.replace(DROPCLOSE, "")

    doc = DOC.read_text()
    hits = flipdrop.ARM.findall(doc)
    if len(hits) != 1:
        sys.exit(f"expected exactly one `scannerDrop` arm in "
                 f"{DOC.relative_to(ROOT)}, found {len(hits)}; the production "
                 "moved and this gate needs re-aiming")
    doc = flipdrop.ARM.sub("\n", doc)
    return {ACC: acc, DOC: doc}


# ---------------------------------------------------------------------------
# Locating a declaration and replacing its proof
# ---------------------------------------------------------------------------

def decl_span(lines: list[str], idx: int) -> tuple[int, int, str, str] | None:
    """(start, end, keyword, name) of the declaration containing line `idx`.

    `start` is the head line, `end` is exclusive.  Returns None when the line
    sits outside any declaration — a `run_cmd`, a module docstring, an `#eval`
    — which is reported rather than dropped, because a location this gate
    cannot name is a hole in the count.
    """
    for i in range(min(idx, len(lines) - 1), -1, -1):
        m = HEAD.match(lines[i])
        if m:
            kw = lines[i].split()[0].lstrip("@[")
            for c in ("private", "protected", "noncomputable"):
                if kw == c:
                    kw = lines[i].split()[1]
            end = len(lines)
            for j in range(i + 1, len(lines)):
                if TERMINATOR.match(lines[j]):
                    end = j
                    break
            # an `example` has no name; the line is its address
            return (i, end, kw, m.group(1) or f"example@{i + 1}")
        if TERMINATOR.match(lines[i]) and not HEAD.match(lines[i]):
            return None
    return None


def command_span(lines: list[str], idx: int) -> tuple[int, int]:
    """The top-level COMMAND containing line `idx` — a `run_cmd`, a
    `#guard_msgs` and what it guards, an `#assert_*`.

    A docstring closing immediately above belongs to the command: that is how
    `#guard_msgs` carries its expected message, and neutralizing the command
    without it leaves a docstring attached to nothing.
    """
    idx = max(0, min(idx, len(lines) - 1))
    start = idx
    # An error is reported where it FAILED, which for a `run_cmd` is a line
    # deep inside its body.  The span is the enclosing top-level form, so walk
    # back to its head first; a span that started at the failing line left the
    # command's own opening behind and turned one broken module into a cascade.
    while start > 0 and not TERMINATOR.match(lines[start]):
        start -= 1
    # `open … in`, `set_option … in`, `attribute … in` bind to the command
    # below them: neutralizing the command without its modifier leaves the
    # modifier applying to whatever comes next, which is how the control run
    # turned one broken census into two.
    while start > 0 and MODIFIER.match(lines[start - 1]):
        start -= 1
    if start > 0 and lines[start - 1].rstrip().endswith("-/"):
        j = start - 1
        while j >= 0 and not lines[j].lstrip().startswith("/--"):
            # A walk that crosses a declaration or an ordinary block comment is
            # not reading a docstring — it is reading whatever is above one, and
            # extending the span there would comment out real work.  This fired
            # on a `-/` that a previous round's own neutralization had written.
            if HEAD.match(lines[j]) or lines[j].startswith("/-"):
                j = -1
                break
            j -= 1
        if j >= 0:
            start = j
    end = len(lines)
    k = idx + 1
    while k < len(lines):
        if TERMINATOR.match(lines[k]) and not MODIFIER.match(lines[k - 1]):
            end = k
            break
        k += 1
    return start, end


#: A command MODIFIER: a top-level form ending in `in`, which binds to the
#: command that follows it.
MODIFIER = re.compile(
    r"^(open|set_option|attribute|variable|universe|local|scoped|@\[|private|"
    r"protected|noncomputable)\b.*\bin\s*$")


def with_docstring(lines: list[str], start: int) -> int:
    """Extend a declaration's span back over its docstring and attributes.

    **A docstring left attached to a comment is a parse error**, not a silent
    one: Lean reports `unexpected token; expected 'lemma'` at the line after it.
    Neutralizing a declaration without its own docstring is how this gate's
    first run turned one deletion into a seven-round cascade.
    """
    while start > 0:
        prev = lines[start - 1]
        if prev.startswith("@[") or MODIFIER.match(prev):
            start -= 1
            continue
        if prev.rstrip().endswith("-/"):
            j = start - 1
            while j >= 0 and not lines[j].lstrip().startswith("/--"):
                if HEAD.match(lines[j]) or lines[j].startswith("/-"):
                    j = -1
                    break
                j -= 1
            if j >= 0:
                start = j
                continue
        break
    return start


def neutralize(lines: list[str], start: int, end: int,
               allow_decl: bool = False) -> list[str]:
    """Comment out one top-level command, so the module elaborates and the
    build reaches what is behind it.

    **This is a bigger intervention than a `sorry` and is reported apart.**  A
    `sorry` keeps a statement and loses a proof; this removes a CHECK.  It is
    only ever applied to a span that declares nothing — asserted here, because
    commenting out a declaration would delete work and read as progress.
    """
    if not allow_decl:
        for ln in lines[start:end]:
            if HEAD.match(ln):
                raise AssertionError(
                    f"the span to neutralize declares something: {ln[:80]!r}")
    return (lines[:start] + ["/- β.5 fixpoint: this census's pins move with the "
                             "deletion; neutralized to reach what is behind it"]
            + lines[start:end] + ["-/"] + lines[end:])


#: A Lean string literal, and a CHARACTER literal that is not the prime of an
#: identifier (`s'`, `sp_scan'`).  Both must go before brackets are counted:
#: `(h_c : c = \'[\' \u2228 c = \'{\')` is three opening brackets to a naive
#: counter and zero to a correct one, and one such line puts every later
#: reading off by two.
LITERAL = re.compile(r'"(?:\\.|[^"\\])*"' r"|(?<![A-Za-z0-9_'])'(?:\\.|[^'\\])'")


def code_of(line: str) -> str:
    """The bracket-significant part of a line: literals and the line comment
    removed, in that order — a `--` inside a string is not a comment."""
    s = LITERAL.sub("", line)
    return s.split("--")[0] if "--" in s else s


def body_start(lines: list[str], start: int, end: int) -> int | None:
    """The line holding the top-level `:=` that separates statement from proof.

    Depth is counted from the declaration head over `(`, `[` and `{`, so binder
    defaults `(n : Nat := 0)` and structure instances are inside and the first
    `:=` at depth zero is the body's.
    """
    depth = 0
    for i in range(start, end):
        code = code_of(lines[i])
        for ch in code:
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
        if depth == 0 and ":=" in code:
            return i
    return None


def classify(lines: list[str], line_no: int) -> tuple[str, str, str, int, int, int]:
    """(verdict, keyword, name, start, end, split) for the error at `line_no`.

    The verdict is one of `sorried` (its proof can be replaced), `restatement`
    (the error is at or above the `:=`, so it is in the STATEMENT and no proof
    repairs it), `data` (not a Prop — see `PROP_KEYWORDS`), `nobody` (no
    top-level `:=`, which means the span reader is wrong and must be fixed
    rather than worked around), or `unmapped`.
    """
    span = decl_span(lines, line_no - 1)
    if span is None:
        return ("unmapped", "", "", -1, -1, -1)
    start, end, kw, name = span
    if kw not in PROP_KEYWORDS:
        return ("data", kw, name, start, end, -1)
    split = body_start(lines, start, end)
    if split is None:
        return ("nobody", kw, name, start, end, -1)
    if line_no - 1 < split:
        return ("restatement", kw, name, start, end, split)
    return ("sorried", kw, name, start, end, split)


def apply_sorry(lines: list[str], start: int, end: int, split: int) -> list[str]:
    """Replace one declaration's proof with `sorry`, statement byte-identical.

    Callers apply these in DESCENDING `start` order: a patch shortens the file,
    so a round that applied them top-down would read every later error location
    against a file that had already moved under it.
    """
    head = lines[split]
    cut = head.index(":=", code_of(head).index(":="))
    return lines[:split] + [head[:cut] + ":= sorry"] + lines[end:]


# ---------------------------------------------------------------------------
# The fixpoint
# ---------------------------------------------------------------------------

def md5(path: Path) -> str:
    return hashlib.md5(path.read_bytes()).hexdigest()


def build(log_dir: Path | None, tag: str) -> tuple[int, str]:
    out = subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True,
                         text=True)
    log = out.stdout + out.stderr
    if log_dir:
        (log_dir / f"flip.beta5.{tag}.log").write_text(log)
    return out.returncode, log


def run(max_rounds: int, log_dir: Path | None, probe: Path | None) -> int:
    # Every file this gate writes is backed up the FIRST time it is touched —
    # the fixpoint sorries declarations in modules nothing knew about when it
    # started, and a backup list fixed at the two edited files would restore
    # two of them and leave the rest flipped.
    before: dict[Path, str] = {}
    backups: dict[Path, Path] = {}

    def touch(path: Path) -> None:
        if path in backups:
            return
        before[path] = md5(path)
        b = path.with_suffix(path.suffix + ".beta5-backup")
        shutil.copy(path, b)
        backups[path] = b
        print(f"md5 before  {path.relative_to(ROOT)}  {before[path]}")

    touch(ACC)
    touch(DOC)

    sorried: list[tuple[int, str, str]] = []     # (round, keyword, name)
    restated: list[tuple[int, str, str]] = []
    refused: list[tuple[int, str, str]] = []
    pinned: list[tuple[int, str, int]] = []
    deleted: list[tuple[int, str, str]] = []
    unmapped: list[str] = []
    rounds = 0
    rc = 1
    try:
        state = beta5_edits()
        print(f"EDIT retire pendingFlow + delete scannerDrop + delete dropClose")
        for rnd in range(1, max_rounds + 1):
            for p, t in state.items():
                p.write_text(t)
            rc, log = build(log_dir, f"round{rnd}")
            rounds = rnd
            if rc == 0:
                print(f"ROUND {rnd} CLEAN — the fixpoint is reached")
                break
            locs = sorted({(m.group(1), int(m.group(2)))
                           for m in flip210.ERROR_LOC.finditer(log)})
            # Every location is classified against THIS round's text before any
            # of it is patched, and the patches are then applied bottom-up.
            byfile: dict[Path, list[tuple[int, str, str, str, int, int, int]]] = {}
            for rel, line in locs:
                path = ROOT / rel
                if not path.exists():
                    unmapped.append(f"no such file: {rel}")
                    continue
                if path not in state:
                    touch(path)
                    state[path] = path.read_text()
                byfile.setdefault(path, []).append((line, rel, "", "", 0, 0, 0))
            progress = 0
            for path, rows in byfile.items():
                rel = rows[0][1]
                lines = state[path].split("\n")
                decls: dict[tuple[int, int], tuple[str, str, str, int]] = {}
                pins: list[tuple[int, int]] = []
                for line, _rel, *_ in rows:
                    verdict, kw, name, start, end, split = classify(lines, line)
                    if verdict == "unmapped":
                        # not inside any declaration: a top-level CHECK whose
                        # pins the deletion moves.  Instrument debt, not proof
                        # debt — neutralized so the build reaches what is
                        # behind it, and counted in its own population.
                        pins.append(command_span(lines, line - 1))
                        continue
                    key = (start, end)
                    prev = decls.get(key)
                    # one declaration, one verdict: a statement error outranks a
                    # body error in the same span, because sorrying its proof
                    # would leave the real error in place and the round would
                    # read as progress.
                    if prev is None or (prev[0] == "sorried" and verdict != "sorried"):
                        decls[key] = (verdict, kw, name, split)
                # two errors in one command are one neutralization
                merged: list[tuple[int, int]] = []
                for a, b in sorted(set(pins)):
                    if merged and a <= merged[-1][1]:
                        merged[-1] = (merged[-1][0], max(merged[-1][1], b))
                    else:
                        merged.append((a, b))
                for (start, end), row, _ in sorted(
                        [(k, decls[k], "d") for k in decls]
                        + [((a, b), ("pin", "", "", -1), "p") for a, b in merged],
                        key=lambda kv: -kv[0][0]):
                    verdict, kw, name, split = row
                    if verdict == "sorried":
                        lines = apply_sorry(lines, start, end, split)
                        sorried.append((rnd, kw, f"{rel}:{name}"))
                        progress += 1
                        print(f"ROUND {rnd} SORRIED   {kw} {name}  ({rel})")
                    elif verdict == "pin":
                        lines = neutralize(lines, start, end)
                        pinned.append((rnd, rel, start + 1))
                        progress += 1
                        print(f"ROUND {rnd} PIN MOVED {rel}:{start + 1}-{end}"
                              "  — a census the deletion re-reads; neutralized")
                    elif verdict == "restatement":
                        restated.append((rnd, kw, f"{rel}:{name}"))
                        print(f"ROUND {rnd} RESTATEMENT {kw} {name}  ({rel}:"
                              f"{start + 1})  — the error is in the STATEMENT; "
                              "no proof repairs it")
                    elif verdict == "data":
                        if rel.startswith("Tests/"):
                            # An instrument's own helper that names the deleted
                            # constant is a DELETION, the verdict β.5 gives the
                            # exhibits — not a reproof.  `sorry` is refused here
                            # on purpose: it would change a VALUE (F1).
                            lines = neutralize(lines, with_docstring(lines, start),
                                               end, allow_decl=True)
                            deleted.append((rnd, kw, f"{rel}:{name}"))
                            progress += 1
                            print(f"ROUND {rnd} DELETED   {kw} {name}  ({rel}:"
                                  f"{start + 1})  — a data definition whose "
                                  "VALUE names the deletion; not sorriable")
                        else:
                            refused.append((rnd, kw, f"{rel}:{name}"))
                            print(f"ROUND {rnd} REFUSED   {kw} {name}  ({rel}:"
                                  f"{start + 1})  — a LIBRARY data definition "
                                  "names the deletion; sorrying it would change "
                                  "a VALUE and deleting it is not this gate's "
                                  "call")
                    else:
                        unmapped.append(f"{verdict}: {rel}:{name} @{start + 1}")
                state[path] = "\n".join(lines)
            print(f"ROUND {rnd} patched {progress} declaration(s); "
                  f"{len(locs)} error location(s)")
            if progress == 0:
                print(f"ROUND {rnd} STUCK — every remaining error is a "
                      "RESTATEMENT, a refusal or unmappable; the fixpoint "
                      "cannot advance and the rest of the tree stays unread")
                break

        print()
        print(f"ROUNDS {rounds}  rc={rc}")
        print(f"SORRIED {len(sorried)}")
        for rnd, kw, n in sorried:
            print(f"  wave{rnd} {kw} {n}")
        print(f"RESTATEMENTS {len(restated)}")
        for rnd, kw, n in restated:
            print(f"  wave{rnd} {kw} {n}")
        print(f"REFUSED {len(refused)}")
        for rnd, kw, n in refused:
            print(f"  wave{rnd} {kw} {n}")
        print(f"DELETED {len(deleted)}")
        for rnd, kw, n in deleted:
            print(f"  wave{rnd} {kw} {n}")
        print(f"PINSMOVED {len(pinned)}")
        for rnd, rel, ln in pinned:
            print(f"  wave{rnd} {rel}:{ln}")
        print(f"UNMAPPED {len(unmapped)}")
        for u in unmapped:
            print(f"  {u}")
        waves = sorted({r for r, _, _ in sorried} | {r for r, _, _ in restated}
                       | {r for r, _, _ in deleted} | {r for r, _, _ in pinned})
        print("WAVES " + "  ".join(
            f"w{w}={sum(1 for r, _, _ in sorried if r == w)}" for w in waves))

        if probe is not None:
            print()
            print(f"=== AXIOM CENSUS ({'at the FIXPOINT' if rc == 0 else 'at a STUCK point: only what built is readable'}) ===")
            scratch = ROOT / "L4YAML" / "Scratch"
            scratch.mkdir(parents=True, exist_ok=True)
            dest = scratch / probe.name
            shutil.copy(probe, dest)
            out = subprocess.run(["lake", "env", "lean", str(dest.relative_to(ROOT))],
                                 cwd=ROOT, capture_output=True, text=True)
            axlog = out.stdout + out.stderr
            if log_dir:
                (log_dir / "flip.beta5.axioms.log").write_text(axlog)
            print(f"PROBE exit={out.returncode}")
            print(axlog)
            shutil.rmtree(scratch, ignore_errors=True)
            if out.returncode != 0:
                print("THE PROBE DID NOT ELABORATE — a module it imports did "
                      "not build, so no profile was read.  A missing reading is "
                      "not a clean one.")
            m = re.search(r"CENSUS gone=(\d+) carried=(\d+) free=(\d+)", axlog)
            census = (f"gone={m.group(1)} carried={m.group(2)} free={m.group(3)}"
                      if m else "gone=? carried=? free=?")
        else:
            census = "gone=? carried=? free=?"

        # The one line `Tests/Guards/Proofs/ParkBill.lean` pins.  Checked from
        # THIS side: nothing in Lean can re-derive a property of a source tree
        # that does not exist, and a pin compared against itself is an empty
        # check (§9).
        fixline = (f"rounds={rounds} clean={int(rc == 0)} "
                   f"sorried={len(sorried)} restated={len(restated)} "
                   f"deleted={len(deleted)} refused={len(refused)} "
                   f"pins={len(pinned)} "
                   f"waves=[{','.join(str(sum(1 for r, _, _ in sorried if r == w)) for w in waves)}] "
                   f"{census}")
        print()
        print(f"FIXLINE {fixline}")
        pin_file = ROOT / "Tests" / "Guards" / "Proofs" / "ParkBill.lean"
        if pin_file.exists():
            # `\s*` and not a literal space: the pin is long enough that the
            # string sits on the line below its `:=`, and a regex that required
            # them on one line read the pin as ABSENT.  It said MISSING rather
            # than agreeing, which is the right direction to fail in, but it is
            # still a failure and it is what the gate battery caught.
            pm = re.search(r'def expectedFixpoint : String :=\s*"([^"]*)"',
                           pin_file.read_text())
            if pm is None:
                print("FIX-PIN MISSING — ParkBill.lean no longer carries "
                      "`expectedFixpoint`; this gate has nothing to agree with")
            elif pm.group(1) == fixline:
                print("FIX-PIN agrees")
            else:
                print(f"FIX-PIN MOVED\n  got      {fixline}\n  "
                      f"expected {pm.group(1)}")
        else:
            print("FIX-PIN MISSING — Tests/Guards/Proofs/ParkBill.lean is not "
                  "in the tree; nothing pins this reading")
    finally:
        for q, b in backups.items():
            shutil.copy(b, q)
            b.unlink()
        ok = True
        for q, h in before.items():
            after = md5(q)
            print(f"md5 after   {q.relative_to(ROOT)}  {after}")
            ok = ok and after == h
        if not ok:
            sys.exit("the restore did not restore; fix the sources before "
                     "trusting anything else in this run")
        print("rebuilding so no later probe reads the flipped oleans...")
        subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-rounds", type=int, default=25)
    ap.add_argument("--log-dir", metavar="DIR")
    ap.add_argument("--probe", metavar="LEAN",
                    help="a Lean file to elaborate at the fixpoint (the axiom "
                         "census); copied into L4YAML/Scratch and removed after")
    args = ap.parse_args()
    return run(args.max_rounds,
               Path(args.log_dir) if args.log_dir else None,
               Path(args.probe) if args.probe else None)


if __name__ == "__main__":
    raise SystemExit(main())
