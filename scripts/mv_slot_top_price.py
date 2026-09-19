#!/usr/bin/env python3
"""Price the SLOT's own stack top on `pendingMapValue.h_vslot` (item 209).

Item 208 recorded ring 1's seventh arm as three rings deep and priced the
first two: one payer on `accum_block_pending`'s relay
(`scripts/vslot_top_price.py`), and a top field on `pendingMapValue` with SIX
producers (`scripts/park_top_price.py pendingMapValue`).  That second number
prices a field asked of EVERY producer.  The consumer does not read one: the
compact fill reads the top only where the SLOT is there, and `h_vslot`'s left
disjunct is where the slot is stated -- so the honest field is a CONJUNCT
inside that disjunct, and its price is the producers that pay the disjunct,
not the producers of the constructor.

This script measures that difference.  It splices the top into `h_vslot`'s
left disjunct, builds, and separates

  * CONSUMERS -- declarations that READ `pendingMapValue.h_vslot` (their
    tuple patterns now bind one component too few), from
  * PRODUCERS -- the `*_open_map` lemmas that BUILD it,

collapsing cascades the way item 208 taught, because an argument written as a
`match` reports one error per arm and the raw list counts how a payment is
WRITTEN rather than how many payments there are.
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

ANCHOR = "      (h_vslot : (sp_scan.col = n + 1 ∧ ∀ sp_v : SurfPos,"
PROBE = ("      -- SLOT-TOP PROBE (scripts/mv_slot_top_price.py)\n"
         "      (h_vslot : (sc.currentIndent ≤ (n : Int) ∧ sp_scan.col = n + 1 ∧ "
         "∀ sp_v : SurfPos,")

PRODUCERS = ["colon_open_map", "question_open_map", "colon_open_map_explicit",
             "compact_open_map", "colon_open_map_implicit", "colon_open_map_props"]


def apply_probe(lines):
    hits = [i for i, l in enumerate(lines) if l.rstrip() == ANCHOR.rstrip()]
    assert len(hits) == 1, f"anchor matched {len(hits)} lines"
    out = list(lines)
    out[hits[0] : hits[0] + 1] = PROBE.split("\n")
    return out


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def) (\w+)", lines[i])
        if m:
            decl = m.group(1)
    return decl


def main():
    original = TARGET.read_text()
    backup = TARGET.with_suffix(".lean.mvslot-bak")
    shutil.copyfile(TARGET, backup)
    try:
        TARGET.write_text("\n".join(apply_probe(original.split("\n"))))
        print("probe: slot top inside pendingMapValue.h_vslot's left disjunct")
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    patched = apply_probe(TARGET.read_text().split("\n"))
    pat = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    census = sorted({int(m.group(1)) for m in
                     (pat.match(l) for l in body.split("\n")) if m})

    # Anchor every error on the nearest preceding constructor application.
    anchors = [i + 1 for i, l in enumerate(patched)
               if "PendingNode.pendingMapValue" in l and not l.strip().startswith("--")]
    groups, unanchored = {}, []
    for raw in census:
        prior = [a for a in anchors if a <= raw]
        # An error inside a producer belongs to that producer's application;
        # an error in a declaration that holds no application is a CONSUMER.
        decl = enclosing_decl(patched, raw)
        if prior and enclosing_decl(patched, prior[-1]) == decl:
            groups.setdefault(prior[-1], []).append(raw)
        else:
            unanchored.append(raw)

    prod_hits = {a: h for a, h in groups.items()
                 if enclosing_decl(patched, a) in PRODUCERS}
    other_hits = {a: h for a, h in groups.items() if a not in prod_hits}
    cons = {}
    for raw in unanchored:
        cons.setdefault(enclosing_decl(patched, raw), []).append(raw)

    print(f"\nraw error sites: {len(census)}")
    print(f"PRODUCERS (pay the conjunct):  {len(prod_hits)}")
    for a, h in sorted(prod_hits.items()):
        print(f"    L{a}  {enclosing_decl(patched, a)}"
              + (f"   [{len(h)} raw]" if len(h) > 1 else ""))
    if other_hits:
        print(f"other applications:            {len(other_hits)}")
        for a, h in sorted(other_hits.items()):
            print(f"    L{a}  {enclosing_decl(patched, a)}   [{len(h)} raw]")
    print(f"CONSUMERS (read the tuple):    {len(cons)} declaration(s),"
          f" {sum(len(v) for v in cons.values())} raw")
    for d, hits in sorted(cons.items(), key=lambda kv: -len(kv[1])):
        print(f"    {len(hits):3d}  {d}")
    silent = [p for p in PRODUCERS
              if p not in {enclosing_decl(patched, a) for a in prod_hits}]
    print(f"\nproducers that did NOT break ({len(silent)}) — they pay "
          f"`Or.inr trivial` and owe nothing:")
    for p in silent:
        print(f"    {p}")
    if not census:
        print("  (none)")


if __name__ == "__main__":
    main()
