#!/usr/bin/env python3
"""The value-line PACK's punt surface, measured by ONE flip of the family's NAMED alternative
(item 311; item 301's instrument, retargeted from the tails to the body).

`block_dispatch_deferred_stamp_nopack` is applied where a class-A `:` (the explicit value of a
`?` frame, at the frame's column) lands on a park whose value-line pack is `Or.inr`.  Every
value-line pack, chain pack and value-line stack in `StreamAccum` — the `PendingNode` fields, the
premises that restate them, the conclusions that hand them on, the key-pack records and the flow
frame — is typed `… ∨ PackAlt sc` (`∨ PackAltG g` on the frame, whose alternative is the gate's):
ONE alternative with one body, `True` until the lanes of 12.3.4.2 pay it (`BlockDeferralClasses`
§30).  A one-field flip (§7, §9 of `BlockDeferralClasses`) reads the field's own producers; the
family's price is every producer that hands ANY of them `Or.inr`, which only the whole flip reads.

Two flips, one instrument (item 312 added the second):

* **`--alt false` (the default)** — both bodies become `False` in one patched tree, so every
  `Or.inr trivial` on the family fails and every `Or.inr h` relays.  This reads the DECLINES: the
  sites a lane must replace by a payment.
* **`--alt refused` (the RESIDUE)** — `PackAlt sc` becomes `ExplicitValueRefused sc`, the predicate
  the family will carry; `PackAltG g` stays `True` (the frame's carrier is lane (d)'s open
  question), every `PackAlt`-level lemma whose `trivial` body names its predicate-level proof after
  `-- refused:` gets that proof (`PackAlt.ofRefused` the identity, a transport its
  `ExplicitValueRefused.step_…`; counted as `promised=`), `PackAltG.ofPark` holds as it is and
  `PackAlt.ofGateClose` is sorried (`stubs=1`).  A bare `trivial` still fails (an unpaid
  decline), and so does every relay BETWEEN TWO PARK STATES — `Or.inr h` with `h : PackAlt sc`
  where `PackAlt s'` is owed, `.imp f id` across a step — which `--alt false` cannot see (`False`
  to `False` is the identity).  Those are the TRANSPORTS a lane must prove (one preservation
  lemma per dispatch kind, item 308's pricing), and the residue line counts them apart.

`lake env lean` runs to a fixpoint.  Each round, an error at `trivial`/`True.intro`/`⟨⟩` is a
DECLINE (the site is sorried and the round continues); an error at a parenthesized group or a
lone identifier whose expected type the message names is a RELAY — from an unflipped `∨ True`
source (wrapped in `ofTrue_probe`) or, in the residue, from another park state (wrapped in
`alt_probe`, `PackAlt sc → PackAlt s'` by `sorry`; an `Or` landing gets `.imp id alt_probe`, a
bare `id` becomes `fun h => alt_probe h`); both probes are spliced in front of the first
declaration.  Any other shape stops the census, since a wrong wrap cascades.  The three
conversion stubs — `PackAlt.ofRefused` (the payment), `PackAltG.ofPark` (a park's alternative
into the frame it opens), `PackAlt.ofGateClose` (the frame's into the park its close builds) —
are the lanes' obligations, not sites, and are reported as `stubs=`.  `StreamAccum.lean` is
restored byte-identical whatever happens.

Reads one line, pinned in `BlockDeferralClasses.expectedPackFlip` (`--alt false`) and
`expectedPackResidue` (`--alt refused`):

    PACK-FLIP    sites=… decls=… rounds=… decline=… relay=… leaf=… uncond=… stubs=…
    PACK-RESIDUE sites=… decls=… rounds=… decline=… relayTrue=… relayState=… leaf=… uncond=… stubs=… promised=…

`leaf` counts the declines inside a match arm or an `else` — `| … => Or.inr trivial`,
`| … => exact Or.inr trivial`, `else Or.inr trivial`, `· exact Or.inr trivial` — conditional on
an INCOMING optional declining — and `uncond` the bare ones; the two are the census's reading of
transport versus root.  `--tsv PATH` writes the per-site rows (round, line, column, kind,
declaration, message head, source line)."""
import argparse
import hashlib
import re
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
T = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
PIN = ROOT / "Tests/Guards/Proofs/BlockDeferralClasses.lean"
PACKALT = "abbrev PackAlt (_sc : ScannerState) : Prop := True"
PACKALTG = "abbrev PackAltG (_g : Option ScannerState) : Prop := True"
MODES = {
    # body of PackAlt, body of PackAltG, and what the two frame stubs' `trivial` becomes (None = left as it is)
    "false": dict(alt="False", altG="False",
                  stubs={"lemma PackAltG.ofPark ": "sorry", "lemma PackAlt.ofGateClose ": "sorry"}),
    "refused": dict(alt="ExplicitValueRefused _sc", altG=None,
                    stubs={"lemma PackAltG.ofPark ": None, "lemma PackAlt.ofGateClose ": "sorry"}),
}
# A `PackAlt`-level lemma whose body is `trivial` while `PackAlt` is `True` names, after `-- refused:`,
# the predicate-level proof that stands in its place once `PackAlt` is the predicate (item 313):
# `PackAlt.ofRefused` is `_h`, a transport `ExplicitValueRefused.step_… … _h`.  The `False` flip sorries
# such a body (it is a lemma, not a site: counted in `stubs`); the residue substitutes the promise
# (counted in `promised`).
REFUSED = re.compile(r"\btrivial(\s+)-- refused: (.+?)\s*$")
OPEN, CLOSE = "([{⟨", ")]}⟩"
LEAF = re.compile(r"^(\| .*=> (exact )?Or\.inr trivial|else Or\.inr trivial|· exact Or\.inr trivial)")
# item 361: the elim-conditioned fallback — a producer that pays the alternative with a real fact
# when its carrier's `inl` is in hand and declines, named, when the carrier is absent
# (`h_ref.elim (fun h => Or.inr (PackAlt.ofRefused h)) (fun _ => Or.inr trivial)`, item 360's
# six value-park faces under a nested `?`); the decline is conditional on an INCOMING optional
# exactly as a match arm's is, so it is a `leaf`, listed by site as the `nested-?` roster
# item 362: the paid side may be a bridge application rather than a bare name
# (`PackAlt.ofRefused (RegisterWitness.refused_of_markedCols_nil …)` at the flow closes)
ELIM_LEAF = re.compile(r"\.elim \(fun \w+ => Or\.inr \(PackAlt\.\w+ .+\)\) \(fun _ => Or\.inr trivial\)")
# item 365: the same conditional pay handed as a lemma ARGUMENT rather than a face —
# `(h_alt := h_refused.elim (fun h => PackAlt.ofRefused h) (fun _ => trivial))` at the eleven
# content producers (and inside `PackAlt.step_preprocess … ( … )` at the three
# `content_dispatch_after_close` callers); the decline is the same `nested-?` leaf
ELIM_ARG = re.compile(r"\.elim \(fun \w+ => PackAlt\.\w+ \w+\) \(fun _ => trivial\)")
ERR = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): error: (.*)")
HEADER = re.compile(r"^\S+\.lean:\d+:\d+: (error|warning|info)")
# Lean stops at 100 errors by default (`maxErrors`); a round must see every site to converge honestly
LEAN_ARGS = ["-DmaxErrors=5000"]


def check_pin(name, label, line):
    """The pin is a literal in the guard, checked from THIS side: nothing in
    Lean can re-derive a reading of a patched tree."""
    m = re.search(rf'def {name} : String :=\n  "([^"]*)"', PIN.read_text())
    if not m:
        print(f"{label} absent")
        return
    if m.group(1) == line:
        print(f"{label} agrees")
    else:
        print(f"{label} MOVED\n  got      {line}\n  expected {m.group(1)}")
        sys.exit(1)


def relay_types(msg):
    """From a type-mismatch message, the type the term HAS and the type the position EXPECTS
    (each flattened to one line), or `None`s when the message has no such pair."""
    text = "\n".join(msg)
    m = re.search(r"has type\n(.*?)\nbut is expected to have type\n(.*?)(?:\nin the application|\Z)", text, re.S)
    if not m:
        return None, None
    flat = lambda t: " ".join(t.split())
    return flat(m.group(1)), flat(m.group(2))


def outer_alt(t):
    """The right disjunct of a flattened type's OUTERMOST `∨`, or `None` when it has none."""
    depth, last = 0, None
    i = 0
    while i < len(t):
        c = t[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and t.startswith(" ∨ ", i):
            last = i
        i += 1
    return None if last is None else t[last + 3:].strip()


def balanced_end(lines, ln, col):
    depth, i, j = 0, ln, col
    while True:
        s = lines[i]
        while j < len(s):
            if s.startswith("--", j):
                break
            if s[j] in OPEN:
                depth += 1
            elif s[j] in CLOSE:
                depth -= 1
                if depth == 0:
                    return i, j
            j += 1
        i += 1
        j = 0
        if i >= len(lines):
            raise SystemExit("unbalanced group")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tsv", type=Path, default=None)
    ap.add_argument("--max-rounds", type=int, default=40)
    ap.add_argument("--dump-dir", type=Path, default=None,
                    help="item 356: write the patched StreamAccum of every round here (round-N.lean), to read a mis-rewrite")
    ap.add_argument("--alt", choices=sorted(MODES), default="false",
                    help="false: the declines (PACK-FLIP); refused: the residue under the predicate (PACK-RESIDUE)")
    args = ap.parse_args()
    mode = MODES[args.alt]
    md5 = lambda p: hashlib.md5(p.read_bytes()).hexdigest()
    m0 = md5(T)
    orig = T.read_text()
    orig_lines = orig.split("\n")
    L = orig.split("\n")
    flipped = 0
    for old, body in ((PACKALT, mode["alt"]), (PACKALTG, mode["altG"])):
        hits = [i for i, l in enumerate(L) if l == old]
        assert len(hits) == 1, (old, hits)
        if body is not None:
            L[hits[0]] = old[: -len("True")] + body
            flipped += 1
    promised = stubs = 0
    for i, l in enumerate(L):
        if (m := REFUSED.search(l)):
            if args.alt == "refused":
                L[i] = l[: m.start()] + "(" + m.group(2) + ")"
                promised += 1
            else:
                L[i] = l[: m.start()] + "sorry"
                stubs += 1
    for head, body in mode["stubs"].items():
        i = next(i for i, l in enumerate(L) if l.startswith(head))
        j = next(k for k in range(i, i + 3) if L[k].endswith(":= trivial"))
        if body is None:
            continue
        L[j] = L[j][: -len("trivial")] + body
        if body == "sorry":
            stubs += 1
    print(f"--alt {args.alt}: flipped {flipped} bodies, sorried {stubs} stubs, substituted {promised} promised bodies")
    i0 = next(i for i, l in enumerate(L) if re.match(r"^(private )?(lemma|theorem|def|abbrev|structure|inductive) ", l))
    while L[i0 - 1].strip() != "":
        i0 -= 1
    probe = ["theorem ofTrue_probe {P : Prop} (h : P ∨ True) : P ∨ " + ("False" if args.alt == "false" else "PackAlt sc") + " :=",
             "  h.elim Or.inl (fun _ => Or.inr sorry)", "",
             "theorem alt_probe {sc sc' : ScannerState} (_h : PackAlt sc) : PackAlt sc' := sorry", ""]
    if args.alt == "false":
        probe = probe[:2] + [""]
    else:
        probe[0] = "theorem ofTrue_probe {P : Prop} {sc : ScannerState} (h : P ∨ True) : P ∨ PackAlt sc :="
    L = L[:i0] + probe + L[i0:]
    shift = len(probe)

    def oline(ln):
        return ln + 1 - shift if ln >= i0 + shift else ln + 1

    def odecl(n):
        d = "?"
        for k in range(min(n, len(orig_lines))):
            m = re.match(r"^(?:private )?(?:lemma|theorem|def|abbrev|structure|inductive) (\S+)", orig_lines[k])
            if m:
                d = m.group(1)
        return d

    census, seen, rounds = [], set(), 0
    bak = T.with_suffix(".lean.pack-flip.bak")
    shutil.copyfile(T, bak)
    t0 = time.time()
    stop = False
    try:
        for rnd in range(1, args.max_rounds + 1):
            rounds = rnd
            T.write_text("\n".join(L))
            if args.dump_dir:
                args.dump_dir.mkdir(parents=True, exist_ok=True)
                (args.dump_dir / f"round-{rnd}.lean").write_text("\n".join(L))
            r = subprocess.run(["lake", "env", "lean", *LEAN_ARGS, str(T.relative_to(ROOT))], cwd=ROOT,
                               capture_output=True, text=True)
            if args.tsv:
                # item 312: every round's raw output beside the TSV, so a wrap decision can be re-read
                args.tsv.with_name(f"{args.tsv.stem}-round{rnd}.out").write_text(r.stdout + r.stderr)
            errs, full, cur = {}, {}, None
            for l in (r.stdout + r.stderr).split("\n"):
                if (m := ERR.match(l)):
                    cur = (int(m.group(1)) - 1, int(m.group(2)))
                    errs.setdefault(cur, m.group(3)[:100])
                    full.setdefault(cur, [m.group(3)])
                elif HEADER.match(l):
                    cur = None                       # a warning or an info, not ours
                elif cur is not None:
                    full[cur].append(l.strip())      # `has type` / `but is expected to have type` are NOT indented
            print(f"round {rnd}: {len(errs)} errors ({time.time() - t0:.0f}s)")
            # item 358: a group probed in front of an applicator (`Or.inr (PackAlt.ofRefused h)`) must stay one
            # argument — the `ofTrue_probe (…)` wrap is parenthesised (was `Function expected`, two sites of #99).
            # item 358: an `Invalid ⟨…⟩` at the pattern of an `.imp (fun ⟨…⟩ => …) (fun h => alt_probe h)` relay
            # is the probe already placed at that `id` (the pattern lost its expected type with it), not a new
            # site — read as settled, so the round converges instead of stopping on its own edit
            probed = {k for k, v in errs.items() if v.startswith("Invalid `⟨...⟩` notation")
                      and L[k[0]][k[1]:].startswith("⟨")
                      and (kk := L[k[0]].rfind("(fun ", 0, k[1])) != -1
                      and re.match(r"\s+\(fun h => alt_probe h\)", L[(bb := balanced_end(L, k[0], kk))[0]][bb[1] + 1:])}
            if probed:
                print(f"  {len(probed)} pattern(s) of an already-probed `.imp … (fun h => alt_probe h)` relay, settled")
                errs = {k: v for k, v in errs.items() if k not in probed}
            if not errs:
                break
            for (ln, col), msg in sorted(errs.items(), reverse=True):
                s, o, text = L[ln], oline(ln), L[ln][col:]
                is_mismatch = msg.startswith(("Application type mismatch", "type mismatch", "Type mismatch"))
                kw = re.match(r"(fun|by|match|if|let|have|show|do|⟨)\b", text) or text.startswith("⟨")
                if msg.startswith("maximum number of errors"):
                    print(f"  cap notice at L{o}:{col} — raise LEAN_ARGS' maxErrors")
                    continue
                if (ln, col) in seen:
                    kind, stop = "UNHANDLED", True
                    print(f"  UNHANDLED recurrence at L{o}:{col}: {text[:60]!r} :: {msg}")
                elif (msg.startswith("Invalid `⟨...⟩` notation") and text.startswith("⟨")
                      and (k := s.rfind("(fun ", 0, col)) != -1
                      and (mm := re.match(r"(\s+)id\b", L[(be := balanced_end(L, ln, k))[0]][be[1] + 1:]))):
                    # item 312: an `Invalid ⟨…⟩` at the pattern of `(X.imp (fun ⟨…⟩ => …) id)` is the state relay
                    # at that `id` — the unifier gives up on `id : PackAlt sc → PackAlt s'` and the pattern loses
                    # its expected type — so the probe goes where `id` stands
                    el, ec = be
                    tail = L[el][ec + 1:]
                    L[el] = L[el][:ec + 1] + mm.group(1) + "(fun h => alt_probe h)" + tail[mm.end():]
                    kind = "RELAY-STATE"
                    o, col = oline(el), ec + 1 + len(mm.group(1))
                elif not is_mismatch or kw:
                    # item 312: a cascade of a sibling's mismatch in the same round (an `omega` that lost a
                    # hypothesis, an anonymous constructor whose expected type an unsolved mvar left open);
                    # skipped untouched this round, and an UNHANDLED recurrence if it is still there next round
                    kind = "CASCADE"
                    print(f"  cascade at L{o}:{col}: {text[:50]!r} :: {msg[:60]}")
                elif any(text.startswith(t) for t in ("trivial", "True.intro", "⟨⟩")):
                    tok = next(t for t in ("trivial", "True.intro", "⟨⟩") if text.startswith(t))
                    L[ln] = s[:col] + "sorry" + s[col + len(tok):]
                    kind = "DECLINE"
                elif text.startswith("(") or ((m := re.match(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", text))
                                             and (re.match(r"\s*($|[),⟩])", text[m.end():])
                                                  or (re.match(r"\s", text[m.end():])
                                                      and msg.startswith("Application type mismatch")))):
                    # what the site hands on, and what the position owes; an identifier followed by
                    # more arguments is an ARGUMENT only when the message says so (item 312)
                    has, expects = relay_types(full.get((ln, col), []))
                    alt_has = outer_alt(has) if has is not None else None
                    # the OUTER alternative decides (an inner `∨ True` — a cover option — says nothing);
                    # a bare `id` has a function type and no outer `∨`, so its mention of `PackAlt` decides
                    state_relay = args.alt != "false" and has is not None and (
                        (alt_has is not None and alt_has != "True") or (alt_has is None and "PackAlt" in has))
                    if text.startswith("(") and args.alt == "false" and re.match(r"\(+\s*PackAlt\.", text):
                        # item 358: a producer paying the alternative with a real fact (`PackAlt.ofRefused h`,
                        # `PackAlt.step_…`) has nothing to say once the alternative is `False` — a decline
                        # here, not a relay (the refused lane counts the same body as `promised`)
                        el, ec = balanced_end(L, ln, col)
                        if el == ln:
                            L[ln] = s[:col] + "sorry" + s[ec + 1:]
                        else:
                            L[el] = L[el][ec + 1:]
                            L[ln] = s[:col] + "sorry"
                            for mid in range(ln + 1, el):
                                L[mid] = ""
                        kind = "DECLINE"
                        seen.add((ln, col))
                        census.append((rnd, o, col, kind, odecl(o), msg, orig_lines[o - 1].strip()[:110]))
                        continue
                    if text.startswith("("):
                        el, ec = balanced_end(L, ln, col)
                        head, tail = ("(", ".imp id alt_probe)") if state_relay else ("(ofTrue_probe (", "))")
                        # item 356: when the group closes on its own line, the two edits must compose —
                        # writing `L[ln]` from the stale `s` after editing `L[el]` dropped the tail
                        # (`(Or.inr ((PackAlt.ofRefused h)))` lost its `.imp id alt_probe)`, and the
                        # parse error cascaded into `cases` alternatives two rounds running)
                        if el == ln:
                            s2 = s[:ec + 1] + tail + s[ec + 1:]
                            L[ln] = s2[:col] + head + s2[col:]
                        else:
                            L[el] = L[el][:ec + 1] + tail + L[el][ec + 1:]
                            L[ln] = s[:col] + head + s[col:]
                    else:
                        ident = m.group(0)
                        if state_relay and ident == "id":
                            L[ln] = s[:col] + "(fun h => alt_probe h)" + s[col + m.end():]
                        elif state_relay and expects is not None and expects.startswith("PackAlt "):
                            L[ln] = s[:col] + "alt_probe (" + ident + ")" + s[col + m.end():]
                        elif state_relay:
                            L[ln] = s[:col] + "((" + ident + ").imp id alt_probe)" + s[col + m.end():]
                        else:
                            L[ln] = s[:col] + "(ofTrue_probe (" + ident + "))" + s[col + m.end():]
                    kind = "RELAY-STATE" if state_relay else "RELAY"
                else:
                    kind, stop = "UNHANDLED", True
                    print(f"  UNHANDLED shape at L{o}:{col}: {text[:70]!r} :: {msg}")
                seen.add((ln, col))
                census.append((rnd, o, col, kind, odecl(o), msg, orig_lines[o - 1].strip()[:110]))
            if stop:
                print("stopping on an unhandled site")
                break
        else:
            print("did not converge")
    finally:
        shutil.copyfile(bak, T)
        bak.unlink()
    assert md5(T) == m0, "StreamAccum NOT restored"
    if args.tsv:
        args.tsv.write_text("\n".join("\t".join(str(x) for x in c) for c in census) + "\n")
    by = Counter(c[4] for c in census if c[3] != "CASCADE")
    for d, n in sorted(by.items()):
        print(f"  {n:3d}  {d}")
    kinds = Counter(c[3] for c in census)
    # the class is read off the WHOLE original line (the census tuple keeps a 110-char prefix for
    # the TSV only): `slot_ride`'s `h_alt.elim …` closes past the prefix (#110 review)
    def src(c): return orig_lines[c[1] - 1].strip()
    elim_sites = [c for c in census if c[3] == "DECLINE" and not LEAF.match(src(c))
                  and (ELIM_LEAF.search(src(c)) or ELIM_ARG.search(src(c)))]
    leaf = sum(1 for c in census if c[3] == "DECLINE" and LEAF.match(src(c))) + len(elim_sites)
    uncond = kinds["DECLINE"] - leaf
    for c in elim_sites:
        print(f"  nested-? {c[4]}:{c[1]}")
    if args.alt == "false":
        line = (f"sites={len(census)} decls={len(by)} rounds={rounds} decline={kinds['DECLINE']} "
                f"relay={kinds['RELAY']} leaf={leaf} uncond={uncond} stubs={stubs}")
        label, pin = "PACK-FLIP", "expectedPackFlip"
    else:
        sites = len(census) - kinds["CASCADE"]
        line = (f"sites={sites} decls={len(by)} rounds={rounds} decline={kinds['DECLINE']} "
                f"relayTrue={kinds['RELAY']} relayState={kinds['RELAY-STATE']} leaf={leaf} uncond={uncond} "
                f"stubs={stubs} promised={promised}")
        label, pin = "PACK-RESIDUE", "expectedPackResidue"
    if kinds["CASCADE"]:
        line += f" cascade={kinds['CASCADE']}"
    if kinds["UNHANDLED"]:
        line += f" unhandled={kinds['UNHANDLED']}"
    print(f"{label} {line}")
    check_pin(pin, f"{label}-PIN", line)


if __name__ == "__main__":
    main()
