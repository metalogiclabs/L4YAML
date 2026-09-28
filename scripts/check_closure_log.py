#!/usr/bin/env python3
"""CI gate: the β.5 closure log is an ordered, gap-declared sequence.

`DOCS.md`'s "Row 12 — β.5 closure log" is a flat run of `### Item N (DATE)`
entries that readers and later entries navigate by number: an entry cites
"item 212" and expects the reader to find it by scanning forward.  Nothing
checked that ordering, and it drifted three times — items 139 and 140 landed
reversed, 159/160/161 landed out of sequence, and 244 landed before 243 — each
costing a commit that did nothing but move text.  This gate makes the ordering
a build failure instead of a later observation.

Checks (each a hard failure):

1. **Headings parse.**  Every `### Item N ...` heading carries a number and a
   trailing `(YYYY-MM-DD)`.  A heading whose date is missing or malformed is
   invisible to checks 3 and 4, so it fails here rather than passing silently.
2. **Numbers ascend, strictly.**  Entries appear in increasing item order, so
   appending is unambiguous and a cited number is found by scanning one way.
   An item split across sessions carries a letter (`Item 67a`) and orders by
   `(number, letter)`; a repeated key means two entries claim one item.
3. **Dates do not regress.**  The log is chronological as well as numbered;
   an entry dated before its predecessor means it was inserted in the wrong
   place even when its number happens to fit.
4. **Gaps are declared.**  A missing number must appear in `DECLARED_GAPS`
   with the anchor that documents it elsewhere in `DOCS.md`, and that anchor
   must resolve to a real heading.  An undeclared gap is a lost entry.
5. **The declaration does not rot.**  Every number in `DECLARED_GAPS` must
   still be absent from the log.  Writing the missing entry without removing
   its excuse leaves a stale claim behind, which is how the Reflections index
   drifted, so it fails the same way here.

Usage:  python3 scripts/check_closure_log.py
"""

import re
import sys
from pathlib import Path

DOCS = Path("DOCS.md")

#: Item numbers with no `### Item N` entry in the closure log, each mapped to
#: the `DOCS.md` anchor that documents it instead.  A runtime-repair item is
#: written up under the defect it fixed, not as a closure-log row.
DECLARED_GAPS = {
    18: "surrogate-hex-escapes-decoded-to-nul",
}

HEADING_RE = re.compile(r"^###\s+Item\s+(\d+)([a-z]?)\b(.*)$")
DATE_RE = re.compile(r"\((\d{4}-\d{2}-\d{2})\)\s*$")
#: GitHub's heading-anchor slug: lowercase, punctuation dropped, spaces to `-`.
SLUG_DROP = re.compile(r"[^\w\s-]")


def slug(title: str) -> str:
    return SLUG_DROP.sub("", title.strip().lower()).replace(" ", "-")


def main() -> int:
    if not DOCS.exists():
        print(f"{DOCS}: not found (run from the repository root)")
        return 2

    lines = DOCS.read_text(encoding="utf-8").splitlines()
    anchors = {slug(ln.lstrip("#").strip()) for ln in lines if ln.startswith("#")}

    errors = []
    entries = []  # (lineno, number, date)

    for lineno, ln in enumerate(lines, 1):
        m = HEADING_RE.match(ln)
        if not m:
            continue
        number, letter, rest = int(m.group(1)), m.group(2), m.group(3)
        d = DATE_RE.search(rest)
        if not d:
            errors.append(f"DOCS.md:{lineno}: item {number}{letter} — heading "
                          f"has no trailing (YYYY-MM-DD) date")
            continue
        entries.append((lineno, (number, letter), d.group(1)))

    if not entries:
        print("DOCS.md: no `### Item N (DATE)` entries found — the gate is "
              "matching nothing, which is a defect in the gate")
        return 2

    # 2 + 3: order, in file order.
    def name(key):
        return f"{key[0]}{key[1]}"

    for (pl, pk, pd), (ll, k, dt) in zip(entries, entries[1:]):
        if k <= pk:
            errors.append(f"DOCS.md:{ll}: item {name(k)} follows item "
                          f"{name(pk)} (DOCS.md:{pl}) — entries must strictly "
                          f"ascend by (number, letter)")
        if dt < pd:
            errors.append(f"DOCS.md:{ll}: item {name(k)} dated {dt} follows "
                          f"item {name(pk)} dated {pd} (DOCS.md:{pl}) — dates "
                          f"must not regress")

    present = {k[0] for _, k, _ in entries}
    lo, hi = entries[0][1][0], entries[-1][1][0]

    # 4: every gap declared, and its anchor real.
    for n in range(lo, hi + 1):
        if n in present:
            continue
        anchor = DECLARED_GAPS.get(n)
        if anchor is None:
            errors.append(f"DOCS.md: item {n} has no closure-log entry and no "
                          f"DECLARED_GAPS row — add the entry, or declare "
                          f"where it is documented")
        elif anchor not in anchors:
            errors.append(f"scripts/check_closure_log.py: DECLARED_GAPS[{n}] "
                          f"points at #{anchor}, which is not a heading in "
                          f"DOCS.md")

    # 5: no stale declaration.
    for n in sorted(DECLARED_GAPS):
        if n in present:
            errors.append(f"scripts/check_closure_log.py: DECLARED_GAPS[{n}] "
                          f"excuses an item that now HAS a closure-log entry "
                          f"— drop the row")
        elif not lo <= n <= hi:
            errors.append(f"scripts/check_closure_log.py: DECLARED_GAPS[{n}] "
                          f"is outside the log's range {lo}..{hi} — it "
                          f"excuses nothing")

    if errors:
        for e in errors:
            print(e)
        print(f"\nCLOSURE-LOG: {len(errors)} error(s) over {len(entries)} "
              f"entries (items {lo}..{hi})")
        return 1

    print(f"CLOSURE-LOG: {len(entries)} entries, items {lo}..{hi}, ascending; "
          f"dates non-decreasing; {len(DECLARED_GAPS)} gap(s) declared")
    return 0


if __name__ == "__main__":
    sys.exit(main())
