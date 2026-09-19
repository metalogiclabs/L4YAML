#!/usr/bin/env python3
"""Price the SLOT-TOP conjunct (item 208) -- ring 1's seventh producer.

Item 204 priced `pendingBlock.h_park_top` at 7 producers and item 205 paid six
of them.  The seventh is `accum_block_on_closeThenBlock`'s COMPACT FILL: a
`-` scanned inline off an already-open `[185]`/`[186]` slot (`? - a`).  Its
floor cannot come from the landing -- no break was crossed -- so it has to come
from the park, and the park's face for that arm is the `h_vslot` premise.  The
conjunct it is missing is the stack top at the slot's own index:

    sc.currentIndent <= (nv : Int)

Item 205 recorded the price of that conjunct as "`pendingMapValue.h_vslot`'s
own conjunct (item 204's other six)" and marked the row "not measured here".
This script measures it, the way `park_top_price.py` measures a constructor's:
add the conjunct, build, and group the failures by the DECLARATION containing
them.  A caller that punts (`Or.inr trivial`) is unaffected and does not appear,
which is the point -- the price of a conjunct is its `Or.inl` payers, not the
premise's call sites.

Errors are anchored the way `park_top_price.py` anchors them, so a payer whose
witness is a TUPLE of nested matches counts once rather than once per broken
arm.  That correction is the whole difference between this number and the one
it replaces: the raw error list reads FIVE and the payer is ONE.

Usage:
    python3 scripts/vslot_top_price.py
"""
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

# The premise's opening line, and the conjunct to splice in behind the anchor
# stream.  Matching on the full line keeps the probe from firing on the
# constructor field of the same name (`pendingMapValue.h_vslot`), whose shape
# is different.
ANCHOR = ("    (h_vslot : (∃ (nv : Nat) (sp_a : SurfPos), "
          "SLYamlStream sp_start sp_a ∧")
PROBE = "      -- SLOT-TOP PROBE (scripts/vslot_top_price.py)\n      sc.currentIndent ≤ (nv : Int) ∧"
CONSUMER = "accum_block_on_closeThenBlock"


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def) (\w+)", lines[i])
        if m:
            decl = m.group(1)
    return decl


def apply_probe(lines):
    idx = [i for i, l in enumerate(lines) if l == ANCHOR]
    assert len(idx) == 1, f"anchor matched {len(idx)} lines, expected 1"
    out = list(lines)
    out[idx[0] : idx[0] + 1] = [ANCHOR] + PROBE.split("\n")
    return out


def main():
    original = TARGET.read_text()
    backup = TARGET.with_suffix(".lean.vslot-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched = apply_probe(original.split("\n"))
        TARGET.write_text("\n".join(patched))
        print(f"probe: slot-top conjunct on {CONSUMER}'s h_vslot")
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    pat = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    census = {}
    for line in body.split("\n"):
        m = pat.match(line)
        if m:
            census.setdefault(int(m.group(1)), None)
    for raw in census:
        census[raw] = enclosing_decl(patched, raw)

    # The consumer's own `rcases` breaks too; it is not a producer.
    payers = {r: d for r, d in census.items() if d != CONSUMER}
    consumer = {r: d for r, d in census.items() if d == CONSUMER}

    # An error is not a payer.  A witness built by `match h_vslot with | Or.inl
    # ... => Or.inl <tuple>` breaks in every arm of every nested match inside
    # the tuple, so the raw list reads FIVE for a census of ONE.  Anchor each
    # error on the nearest preceding mention of the field it is built FROM --
    # the repo's idiom for paying an `v True` premise names it on the opening
    # line -- and print what collapsed.
    field = re.compile(r"h_vslot\w*")
    anchors = [i + 1 for i, l in enumerate(patched) if field.search(l)]
    groups, unanchored = {}, []
    for raw in sorted(payers):
        prior = [a for a in anchors if a <= raw]
        (unanchored.append(raw) if not prior
         else groups.setdefault(prior[-1], []).append(raw))

    print(f"\nraw error sites: {len(census)}")
    print(f"  in {CONSUMER} (the CONSUMER reading the conjunct, "
          f"not a producer): {len(consumer)}")
    print(f"  outside it (raw):                                    {len(payers)}")
    print(f"\nPAYERS: {len(groups) + len(unanchored)}   <- the conjunct's price")
    by_decl = {}
    for a, hits in groups.items():
        by_decl.setdefault(enclosing_decl(patched, a), []).append((a, hits))
    for raw in unanchored:
        by_decl.setdefault(payers[raw], []).append((raw, [raw]))
    print(f"declarations: {len(by_decl)}\n")
    for decl, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(hits):3d}  {decl}   (L"
              + ", L".join(str(a) for a, _ in sorted(hits)) + ")")
    cascaded = {a: h for a, h in groups.items() if len(h) > 1}
    if cascaded:
        print(f"\ncollapsed cascades "
              f"({sum(len(h) - 1 for h in cascaded.values())} errors were not "
              f"payers):")
        for a, hits in sorted(cascaded.items()):
            print(f"  L{a}  {patched[a - 1].strip()[:64]}")
            print(f"        <- errors at " + ", ".join(map(str, hits)))
    if unanchored:
        print(f"\nUNANCHORED ({len(unanchored)}): no `h_vslot` mention precedes "
              f"these, so they count one-for-one and the total is a CEILING:")
        for raw in unanchored:
            print(f"  L{raw}  in {payers[raw]}")
    if not payers:
        print("  (none -- every caller punts, and the conjunct is free)")


if __name__ == "__main__":
    main()
