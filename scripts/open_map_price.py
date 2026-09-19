#!/usr/bin/env python3
"""Price the DISPATCH-FLOOR ring behind `pendingMapValue`'s six producers (item 209).

Item 208 measured three rings behind ring 1's seventh arm and paid none of
them: `accum_block_on_closeThenBlock`'s COMPACT FILL needs a top conjunct on
`h_vslot` (1 payer, `scripts/vslot_top_price.py`), that payer needs a top field
on `pendingMapValue` (6 producers, `scripts/park_top_price.py pendingMapValue`),
and each of those six `*_open_map` lemmas would build such a field from a
dispatch floor NONE of them holds -- `s_prep.currentIndent <= s_prep.col`, the
premise `scanKey_top_le` and `scanValue_top_le` both take.

That third ring was recorded as UNMEASURED, and item 208's own rule says a
number no instrument re-derives is a guess.  This is the instrument.  It adds
the floor premise to all six signatures at once, builds, and counts the
APPLICATIONS that break -- collapsing cascades the way item 208 taught, because
an application whose arguments are `by` blocks reports one error per block and
the raw error list counts how a call is WRITTEN, not how many calls there are.

Usage:
    python3 scripts/open_map_price.py            # all six
    python3 scripts/open_map_price.py colon_open_map [...]   # a subset
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

LEMMAS = [
    "colon_open_map",
    "question_open_map",
    "colon_open_map_explicit",
    "compact_open_map",
    "colon_open_map_implicit",
    "colon_open_map_props",
]

PROBE = "    -- DISPATCH-FLOOR PROBE (scripts/open_map_price.py)"
FIELD = "    (h_disp_floor : s_prep.currentIndent ≤ (s_prep.col : Int)) :"


def sig_end(lines, start):
    """Index of the line that closes a lemma's signature (`... ) :`)."""
    for j in range(start, start + 400):
        if lines[j].rstrip().endswith(") :"):
            return j
    raise AssertionError(f"no signature end below line {start + 1}")


def apply_probe(lines, names):
    starts = {}
    for i, line in enumerate(lines):
        m = re.match(r"^(?:private )?lemma (\w+)[ {(]", line)
        if m and m.group(1) in names:
            starts[m.group(1)] = i
    missing = [n for n in names if n not in starts]
    assert not missing, f"not found: {missing}"
    out = list(lines)
    for name in sorted(names, key=lambda n: -starts[n]):
        end = sig_end(out, starts[name])
        out[end : end + 1] = [
            out[end].rstrip()[:-2].rstrip(),
            PROBE,
            FIELD,
        ]
    return out


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def) (\w+)", lines[i])
        if m:
            decl = m.group(1)
    return decl


def main():
    names = sys.argv[1:] or list(LEMMAS)
    bad = [n for n in names if n not in LEMMAS]
    if bad:
        sys.exit(f"unknown lemma(s) {bad}; known: {', '.join(LEMMAS)}")

    original = TARGET.read_text()
    backup = TARGET.with_suffix(".lean.openmap-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched = apply_probe(original.split("\n"), names)
        TARGET.write_text("\n".join(patched))
        print(f"probe: dispatch floor on {len(names)} lemma(s) -> {', '.join(names)}")
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    patched = apply_probe(TARGET.read_text().split("\n"), names)
    pat = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    census = sorted({int(m.group(1)) for m in
                     (pat.match(l) for l in body.split("\n")) if m})

    # Anchors: APPLICATIONS of a probed lemma -- never its own declaration.
    anchors = []
    for i, line in enumerate(patched):
        if re.match(r"^(?:private )?lemma ", line):
            continue
        for name in names:
            if re.search(rf"\b{name}\b", line) and "--" not in line.split(name)[0]:
                anchors.append((i + 1, name))
                break

    groups, unanchored = {}, []
    for raw in census:
        prior = [a for a in anchors if a[0] <= raw]
        if not prior:
            unanchored.append(raw)
        else:
            groups.setdefault(prior[-1], []).append(raw)

    print(f"\nraw error sites: {len(census)}")
    print(f"applications:    {len(groups) + len(unanchored)}   <- the RING")
    by_decl, by_lemma = {}, {}
    for (aline, name), hits in groups.items():
        by_decl.setdefault(enclosing_decl(patched, aline), []).append(aline)
        by_lemma.setdefault(name, []).append(aline)
    for raw in unanchored:
        by_decl.setdefault(enclosing_decl(patched, raw), []).append(raw)
    print(f"declarations:    {len(by_decl)}\n")
    for decl, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(hits):3d}  {decl}")
    print("\nby probed lemma (which producer each caller feeds):")
    for name in names:
        print(f"  {len(by_lemma.get(name, [])):3d}  {name}")
    cascaded = {a: h for a, h in groups.items() if len(h) > 1}
    if cascaded:
        print(f"\ncollapsed cascades ({sum(len(h) - 1 for h in cascaded.values())} "
              f"errors were not callers):")
        for (aline, name), hits in sorted(cascaded.items()):
            print(f"  L{aline}  {name}  <- errors at "
                  + ", ".join(str(h) for h in hits))
    if unanchored:
        print(f"\nUNANCHORED ({len(unanchored)}): no application literal precedes "
              f"these, so they count one-for-one and the total is a CEILING:")
        for raw in unanchored:
            print(f"  L{raw}  in {enclosing_decl(patched, raw)}")
    if not census:
        print("  (none -- every caller already holds the floor)")


if __name__ == "__main__":
    main()
