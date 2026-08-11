#!/usr/bin/env python3
"""CI gate: the Reflections index describes itself accurately.

`Tests/Reflections.lean` has two independent halves.  Its `import` lines are
load-bearing (they are what makes the demos build), and `check_import_closure.py`
already gates those.  Below them is a *narrative* index: `## theme` /
`### sub-theme (Reflections N, M, ...)` headings, each followed by
`* `DemoModule` — Reflection N (...)` bullets.  Nothing checked that half, and it
drifted: Reflections 630-641 sat for weeks under a sub-theme whose own number
list never mentioned them, while that list claimed five of them, so a reader
searching by number was sent to the wrong block or to none.

Checks (each a hard failure):

1. **Bullet names resolve.**  Every bullet's backticked module is imported by the
   index.  (Not the converse — the docstring declares the bullet list PARTIAL, so
   an imported demo with no bullet is deliberate, not a defect.)
2. **Bullets are claimed.**  Every Reflection number in a bullet's label appears
   in the number list of the sub-theme heading that bullet sits under.  A demo
   covering several reflections must have all of them listed.
3. **Claims are backed.**  Every number in a sub-theme's list has a bullet in
   that same block.  A list is a description of its block, not a wish.
4. **No number is claimed twice.**  Two bullets carrying the same Reflection
   number means one of them is misattributed.
5. **Blocks ascend.**  Bullets within a block are ordered by their primary
   (first) Reflection number, so appending is unambiguous.

Usage:  python3 scripts/check_reflection_index.py
"""

import re
import sys
from pathlib import Path

INDEX = Path("Tests/Reflections.lean")

IMPORT_RE = re.compile(r"^import\s+Tests\.Reflections\.(\S+)", re.M)
SUBTHEME_RE = re.compile(r"^###\s+(.*?)\s*\(Reflections?\s+([^)]*)\)\s*$")
BULLET_RE = re.compile(r"^\*\s+`([A-Za-z0-9_.]+)`\s*—\s*(.*)$")


def expand(inner: str) -> set:
    """`245–248, 251` -> {245, 246, 247, 248, 251}. En- and hyphen-dashes both."""
    out = set()
    for tok in inner.split(","):
        tok = tok.strip()
        m = re.fullmatch(r"(\d+)\s*[–-]\s*(\d+)", tok)
        if m:
            out.update(range(int(m.group(1)), int(m.group(2)) + 1))
        elif tok.isdigit():
            out.add(int(tok))
    return out


def label_numbers(rest: str) -> list:
    """Reflection numbers a bullet claims: those before its first '(' — the
    label, not the prose, which cites other reflections freely."""
    return [int(n) for n in re.findall(r"\b\d{3}\b", rest.split("(")[0])]


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    text = (repo / INDEX).read_text()
    imported = set(IMPORT_RE.findall(text))
    failures = []

    # Walk the narrative half, grouping bullets under their sub-theme.
    blocks, cur = [], None
    for lineno, line in enumerate(text.split("\n"), 1):
        if line.startswith("## "):
            cur = None
        elif m := SUBTHEME_RE.match(line):
            cur = {"line": lineno, "name": m.group(1), "claimed": expand(m.group(2)),
                   "bullets": []}
            blocks.append(cur)
        elif (m := BULLET_RE.match(line)) and cur is not None:
            cur["bullets"].append({"line": lineno, "module": m.group(1),
                                   "nums": label_numbers(m.group(2))})

    if not blocks:
        print(f"{INDEX}: no `### sub-theme (Reflections ...)` headings found — "
              "has the index format changed?")
        return 1

    owner = {}
    for b in blocks:
        for bullet in b["bullets"]:
            # 1. bullet names resolve
            if bullet["module"] not in imported:
                failures.append(
                    f"{INDEX}:{bullet['line']}: bullet `{bullet['module']}` is not "
                    f"imported by the index")
            if not bullet["nums"]:
                failures.append(
                    f"{INDEX}:{bullet['line']}: bullet `{bullet['module']}` names no "
                    f"Reflection number before its '('")
            for n in bullet["nums"]:
                # 2. bullets are claimed by their own sub-theme
                if n not in b["claimed"]:
                    failures.append(
                        f"{INDEX}:{bullet['line']}: Reflection {n} "
                        f"(`{bullet['module']}`) is not in the list of its sub-theme "
                        f"\"{b['name']}\" ({INDEX}:{b['line']})")
                # 4. no number claimed twice
                if n in owner:
                    failures.append(
                        f"{INDEX}:{bullet['line']}: Reflection {n} also claimed at "
                        f"{INDEX}:{owner[n]}")
                else:
                    owner[n] = bullet["line"]

        # 3. claims are backed
        present = {n for bl in b["bullets"] for n in bl["nums"]}
        for n in sorted(b["claimed"] - present):
            where = f", whose bullet is at {INDEX}:{owner[n]}" if n in owner else ""
            failures.append(
                f"{INDEX}:{b['line']}: \"{b['name']}\" lists Reflection {n} but has "
                f"no such bullet{where}")

        # 5. blocks ascend by primary number
        primaries = [(bl["nums"][0], bl["line"], bl["module"]) for bl in b["bullets"]
                     if bl["nums"]]
        for (n1, _, m1), (n2, l2, m2) in zip(primaries, primaries[1:]):
            if n2 < n1:
                failures.append(
                    f"{INDEX}:{l2}: `{m2}` (Reflection {n2}) follows `{m1}` "
                    f"(Reflection {n1}) — block \"{b['name']}\" is not ascending")

    demos = len({bl["module"] for b in blocks for bl in b["bullets"]})
    if failures:
        print(f"Reflections index: {len(failures)} problem(s)\n")
        for f in failures:
            print(f"  {f}")
        print(f"\n{len(blocks)} sub-themes, {demos} bulleted demos, "
              f"{len(owner)} reflections indexed.")
        return 1

    print(f"Reflections index OK: {len(blocks)} sub-themes, {demos} bulleted demos, "
          f"{len(owner)} reflections indexed, {len(imported)} demos imported.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
