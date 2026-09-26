#!/usr/bin/env python3
"""β.5's DEAD BRANCHES, deleted rather than sorried (DOCS item 264).

Item 263 drove β.5's edit to a sorry-fixpoint and read THIRTEEN broken proofs,
seven of them in the library.  It then split the seven by the ERROR each one
stopped at: five said `Invalid alternative name 'pendingFlow'`, which is a
branch to delete, and two said something else, which item 263 recorded as the
two REAL repairs.

**An error kind is a hypothesis about a repair, and only a build settles it.**
A `sorry` keeps a statement and loses a proof, so a fixpoint can say a proof
breaks and never say what repairing it costs.  This gate makes the five
deletions for real and measures what is left:

    control   β.5's three deletions alone — the seven, re-derived here so the
              delta below is a reading of this run and not of item 263's.
    arms      the same, plus the five dead arms and `accum_flow_open_depth0`'s
              dead block, DELETED.

Both ends build `lake build L4YAML` — the library alone.  Item 263 already
priced the Tests side, and mixing the guard tree's thirty-seven pinned censuses
back in would bury the one number this gate exists to produce.

**`accum_flow_open_depth0` is in BOTH ends, and that is the reading.**  Its dead
arm goes with the other five, and `have opaque_resume` goes with it — the arm was
its only consumer.  What does NOT go is `have drop_ride`, where β.5's `dropClose`
is actually spent: three LIVE arms take it, one each off `pendingProps`,
`pendingBlock` and `pendingMapValue`, all at the same place — the run-end half of
the flow open's under-run.  So the `arms` end leaves this lemma broken at
`dropClose` alone, with the dead branch subtracted, and that residue is the
repair rather than the error item 263 read.

Each deletion is anchored on CONTENT (item 210's rule) and asserted unique, so a
re-indent or a rewrite re-aims the gate loudly instead of matching silently.  The
SPAN is then computed structurally — from the anchor to the next non-blank line
at or left of the anchor's own indent — and a leading comment block at that same
indent is taken with it, because a comment describing a deleted arm is not a
comment about anything.

Destructive while it runs: it edits `L4YAML/Proofs/Production/StreamAccum.lean`
and `L4YAML/Surface/Document.lean` in place, restores both in a `finally`, and
prints the md5 of each before and after.

    scripts/beta5_arms.py                 # both ends
    scripts/beta5_arms.py --end arms      # one end
    scripts/beta5_arms.py --log-dir DIR   # keep the build logs
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ACC = ROOT / "L4YAML" / "Proofs" / "Production" / "StreamAccum.lean"
DOC = ROOT / "L4YAML" / "Surface" / "Document.lean"


def _load(name: str, fname: str):
    spec = importlib.util.spec_from_file_location(
        name, Path(__file__).resolve().parent / fname)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


#: β.5's own edit and item 210's error mapper come from the gates that already
#: own them, so this one cannot drift from them in silence.
beta5 = _load("beta5", "flip_beta5.py")
flip210 = _load("flip210", "flip_210.py")

# ---------------------------------------------------------------------------
# The dead branches.  `(tag, owner, anchor)` — the anchor's FIRST line is the
# head of the block to delete and the rest is there to make it unique.
# ---------------------------------------------------------------------------

DEAD = [
    ("nic0", "PendingNode.nic0",
     "  | pendingFlow => assumption\n"),
    ("arm_tight_or_col", "PendingNode.arm_tight_or_col",
     "  | pendingFlow _ _ _ _ h_arm _ _ => exact h_arm\n"),
    ("dirRoute", "PendingNode.dirRoute",
     "  | pendingFlow =>\n"
     "    exact absurd h_allow (by simp [show sc.allowDirectives = false from"
     " by assumption])\n"),
    ("accum_block_pending", "accum_block_pending",
     "  | pendingFlow _ _ _ _ h_arm77 _ h_nic0F =>\n"),
    ("accum_content_pending", "accum_content_pending",
     "  | pendingFlow _ _ _ _ _ _ h_nic0F =>\n"),
    # `accum_flow_open_depth0` is three deletions in one proof: the arm, and the
    # two `have`s that only the arm consumes.  `drop_ride` is where β.5's
    # `dropClose` is spent, so if this end elaborates then that spend was dead
    # code and item 263's second real repair is not one.
    ("flow_arm", "accum_flow_open_depth0",
     "  | pendingFlow =>\n"
     "    -- The deferred state: its own closing strategy is the drop, and the"
     " flow\n"),
    ("flow_opaque_resume", "accum_flow_open_depth0",
     "  have opaque_resume : sp_scan.col ≠ 0 → GStar SSWhite sp_scan"
     " sp_prep →\n"),
]

#: A line that is only a comment, at a given indent.  A block of these directly
#: above a deleted arm describes the arm and goes with it.
COMMENT = re.compile(r"^\s*--")


def indent_of(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def block_span(lines: list[str], head: int) -> tuple[int, int]:
    """`[start, end)` of the block whose head line is `lines[head]`.

    Forward to the first non-blank line at or left of the head's indent;
    backward over a contiguous run of comment lines at exactly that indent.
    """
    ind = indent_of(lines[head])
    end = head + 1
    while end < len(lines):
        if lines[end].strip() and indent_of(lines[end]) <= ind:
            break
        end += 1
    start = head
    while (start > 0 and COMMENT.match(lines[start - 1])
           and indent_of(lines[start - 1]) == ind):
        start -= 1
    return start, end


def delete_dead(src: str) -> tuple[str, list[str]]:
    """Delete every block in `DEAD`, bottom-up, and report what went."""
    lines = src.split("\n")
    spans: list[tuple[int, int, str]] = []
    for tag, owner, anchor in DEAD:
        n = src.count(anchor)
        if n != 1:
            sys.exit(f"anchor `{tag}` matches {n} times in "
                     f"{ACC.relative_to(ROOT)}, expected 1; the proof moved and "
                     "this gate needs re-aiming")
        head = src[:src.index(anchor)].count("\n")
        start, end = block_span(lines, head)
        # The span must not swallow a sibling arm: exactly one `| ` at the
        # head's own indent, and it is the head's.
        ind = indent_of(lines[head])
        sibs = [i for i in range(start, end)
                if lines[i].lstrip(" ").startswith("| ")
                and indent_of(lines[i]) == ind]
        if lines[head].lstrip(" ").startswith("| ") and sibs != [head]:
            sys.exit(f"the span for `{tag}` covers {len(sibs)} arms, not one: "
                     f"lines {[i + 1 for i in sibs]}")
        spans.append((start, end, f"{tag} [{owner}] lines "
                                  f"{start + 1}-{end} ({end - start})"))
    spans.sort(reverse=True)
    for start, end, _ in spans:
        del lines[start:end]
    return "\n".join(lines), [note for _, _, note in reversed(spans)]


def arms_edits() -> dict[Path, str]:
    """β.5's three deletions, plus the eight dead blocks."""
    edits = beta5.beta5_edits()
    acc, notes = delete_dead(edits[ACC])
    for note in notes:
        print(f"  DELETED  {note}")
    return {ACC: acc, DOC: edits[DOC]}


ENDS = {
    "control": (beta5.beta5_edits,
                "β.5's three deletions alone — item 263's seven, re-derived"),
    "arms": (arms_edits,
             "…and the dead branches deleted — what is left is the REPAIR"),
}

# ---------------------------------------------------------------------------
# Reading the build
# ---------------------------------------------------------------------------


def md5(path: Path) -> str:
    return hashlib.md5(path.read_bytes()).hexdigest()


def owner_of(lines: list[str], line_no: int) -> str:
    """The declaration containing 1-based `line_no`, by item 263's own regex."""
    for i in range(min(line_no, len(lines)) - 1, -1, -1):
        m = beta5.HEAD.match(lines[i])
        if m:
            return m.group(1) or f"<anonymous@{i + 1}>"
    return "<none>"


def broken(log: str, texts: dict[Path, str]) -> list[tuple[str, str, int]]:
    """`(file, declaration, line)` for every error the build reported."""
    by_rel = {str(p.relative_to(ROOT)): t.split("\n") for p, t in texts.items()}
    out: list[tuple[str, str, int]] = []
    seen: set[tuple[str, str]] = set()
    for m in flip210.ERROR_LOC.finditer(log):
        rel, line = m.group(1), int(m.group(2))
        lines = by_rel.get(rel)
        name = owner_of(lines, line) if lines else "<not-edited>"
        if (rel, name) in seen:
            continue
        seen.add((rel, name))
        out.append((rel, name, line))
    return out


def run_end(name: str, log_dir: Path | None) -> list[tuple[str, str, int]]:
    edit, blurb = ENDS[name]
    print(f"=== END {name}: {blurb} ===")
    before = {p: md5(p) for p in (ACC, DOC)}
    for p, h in before.items():
        print(f"md5 before  {p.relative_to(ROOT)}  {h}")
    originals = {p: p.read_text() for p in (ACC, DOC)}
    try:
        texts = edit()
        for p, t in texts.items():
            p.write_text(t)
        out = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT,
                             capture_output=True, text=True)
        log = out.stdout + out.stderr
        if log_dir:
            (log_dir / f"arms.{name}.log").write_text(log)
        rows = broken(log, texts)
    finally:
        for p, t in originals.items():
            p.write_text(t)
    after = {p: md5(p) for p in (ACC, DOC)}
    for p in (ACC, DOC):
        flag = "==" if before[p] == after[p] else "!! DIFFERS"
        print(f"md5 after   {p.relative_to(ROOT)}  {after[p]}  {flag}")
        if before[p] != after[p]:
            sys.exit(f"{p} was not restored")
    print(f"BROKEN {len(rows)}")
    for rel, decl, line in rows:
        print(f"  {rel}:{line}  {decl}")
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--end", choices=sorted(ENDS), action="append")
    ap.add_argument("--log-dir", type=Path)
    args = ap.parse_args()
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
    ends = args.end or ["control", "arms"]

    counts: dict[str, list[tuple[str, str, int]]] = {}
    for name in ends:
        counts[name] = run_end(name, args.log_dir)
        print()

    if set(ends) == set(ENDS):
        ctl = {d for _, d, _ in counts["control"]}
        arm = {d for _, d, _ in counts["arms"]}
        armline = (f"control={len(ctl)} arms={len(arm)} dead={len(ctl - arm)} "
                   f"left=[{','.join(sorted(arm))}]")
        print(f"ARMLINE {armline}")
        if arm - ctl:
            print(f"  NEW under `arms` (a second wave): {sorted(arm - ctl)}")
        # Nothing in Lean can re-derive this line — it is a property of a source
        # tree that does not exist — so the pin lives in the guard tree and is
        # checked from here.  A pin checked against itself is an empty check.
        pin_file = ROOT / "Tests" / "Guards" / "Proofs" / "ParkBill.lean"
        if not pin_file.exists():
            print("ARM-PIN MISSING — Tests/Guards/Proofs/ParkBill.lean is not "
                  "in the tree; nothing pins this reading")
            return 0
        pm = re.search(r'def expectedArms : String :=\s*"([^"]*)"',
                       pin_file.read_text())
        if pm is None:
            print("ARM-PIN MISSING — ParkBill.lean no longer carries "
                  "`expectedArms`; this gate has nothing to agree with")
        elif pm.group(1) == armline:
            print("ARM-PIN agrees")
        else:
            print(f"ARM-PIN MOVED\n  got      {armline}\n  "
                  f"expected {pm.group(1)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
