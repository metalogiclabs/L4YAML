#!/usr/bin/env python3
"""Price the park-TOP carrier (item 205) by paying its first ring and re-running.

Item 204 proved `block_dispatch_deferred_stamp_compact`'s class FALSE from one
missing number -- the indent stack's top at an entry park, `sc.currentIndent <= n`
-- and priced the carrier by adding the field and counting the build errors: 7
producers.  That count is a census of ONE RING.  Every one of those 7 producers
can pay (item 205 paid them all), but 5 of them pay only from a premise their
own callers must supply, and those callers are the next ring.

This script re-derives the rings.  It edits a COPY of the constructor's
signature in place, builds the module, groups the failures by the DECLARATION
that contains them (never by line number -- line numbers move, declarations do
not), and restores the file.

Usage:
    python3 scripts/park_top_price.py ring1       # the carrier field on pendingBlock
    python3 scripts/park_top_price.py all         # the park-top invariant, all parks
    python3 scripts/park_top_price.py noPending   # ONE park's producers (item 208)

`ring1` reproduces item 204's number.  `all` is item 205's cross-check: the same
carrier asked of every block-context park at once, which is the transitive
closure's floor.

The PER-PARK mode (item 208) answers a different question from either: how many
sites BUILD one constructor.  A new required field makes every application site
fail on arity whether or not the field is provable there, so the error list is
the constructor's producer census exactly -- which is the number a decision to
add a field to that park is spending.  Item 208 added it because `noPending`'s
count was a SENTENCE: item 116 wrote "exactly EIGHT producers", items 135, 186
and 205 each spent it again, and no instrument had ever re-derived it.
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

# Constructor -> the park-position variable its signature binds.  `pendingDirective`
# is excluded: it is the flow-context park and reaches no block dispatch.
PARKS = {
    "noPending": "sp",
    "pendingContent": "sp_scan",
    "pendingProps": "sp_scan",
    "pendingDocEnd": "sp_scan",
    "pendingDocStart": "sp_scan",
    "pendingFlow": "sp_scan",
    "pendingBlockContent": "sp_scan",
    "pendingMapValue": "sp_scan",
}

PROBE = "  -- PARK-TOP PROBE (scripts/park_top_price.py)\n"


def constructor_spans(lines):
    """Map each PendingNode constructor to the index of its conclusion line."""
    spans = {}
    current = None
    for i, line in enumerate(lines):
        m = re.match(r"^  \| (\w+) \(sp_start", line)
        if m:
            current = m.group(1)
        elif current and line.strip().startswith("PendingNode sc "):
            spans[current] = i
            current = None
    return spans


def apply_probe(lines, which):
    spans = constructor_spans(lines)
    if which == "ring1":
        targets = {"pendingBlock": "n"}
    elif which == "all":
        targets = dict(PARKS)
        targets["pendingBlock"] = "n"
    else:
        targets = {which: "n" if which == "pendingBlock" else PARKS[which]}
    out = list(lines)
    for name, var in sorted(targets.items(), key=lambda kv: -spans[kv[0]]):
        concl = spans[name]
        sig = concl - 1
        assert out[sig].rstrip().endswith(") :"), out[sig]
        bound = "(n : Int)" if var == "n" else f"({var}.col : Int)"
        out[sig : sig + 1] = [
            out[sig].rstrip()[:-2].rstrip(),
            PROBE.rstrip("\n"),
            f"      (h_park_top : sc.currentIndent ≤ {bound}) :",
        ]
    return out, sorted(targets)


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def) (\w+)", lines[i])
        if m:
            decl = m.group(1)
    return decl


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "ring1"
    if which not in ("ring1", "all") and which not in PARKS and which != "pendingBlock":
        sys.exit("usage: park_top_price.py [ring1|all|"
                 + "|".join(sorted(list(PARKS) + ["pendingBlock"])) + "]")

    original = TARGET.read_text()
    backup = TARGET.with_suffix(".lean.parktop-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched, names = apply_probe(original.split("\n"), which)
        TARGET.write_text("\n".join(patched))
        print(f"probe: {which} -> {', '.join(names)}")
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    src = TARGET.read_text().split("\n")
    seen, census = set(), {}
    pat = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    for line in body.split("\n"):
        m = pat.match(line)
        if not m:
            continue
        # The probe shifts line numbers; map back through the probe lines added.
        raw = int(m.group(1))
        if raw in seen:
            continue
        seen.add(raw)
        census[raw] = None
    # Re-attribute against the PATCHED text, which is what the numbers refer to.
    patched, _ = apply_probe(src, which)
    for raw in census:
        census[raw] = enclosing_decl(patched, raw)

    # Item 208: collapse CASCADES.  An error is not a producer.  A constructor
    # application whose arguments are `by` blocks reports one failure per broken
    # block, so the raw error list over-counts it -- `noPending` reads 11 that
    # way and is 8.  Anchor each error on the nearest preceding APPLICATION of
    # the probed constructor and count anchors, printing every group that
    # collapsed so the collapse is checkable rather than asserted.
    anchors = []
    for i, line in enumerate(patched):
        for name in names:
            if f"PendingNode.{name}" in line and "--" not in line.split(
                    f"PendingNode.{name}")[0]:
                anchors.append((i + 1, name))
                break
    groups, unanchored = {}, []
    for raw in sorted(census):
        prior = [a for a in anchors if a[0] <= raw]
        if not prior:
            unanchored.append(raw)
        else:
            groups.setdefault(prior[-1], []).append(raw)

    print(f"\nraw error sites: {len(census)}")
    print(f"applications:    {len(groups) + len(unanchored)}"
          f"   <- the producer census")
    by_decl = {}
    for (aline, _name), hits in groups.items():
        by_decl.setdefault(enclosing_decl(patched, aline), []).append((aline, hits))
    for raw in unanchored:
        by_decl.setdefault(census[raw], []).append((raw, [raw]))
    print(f"declarations:    {len(by_decl)}\n")
    for decl, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(hits):3d}  {decl}")
    cascaded = {a: h for a, h in groups.items() if len(h) > 1}
    if cascaded:
        print(f"\ncollapsed cascades ({sum(len(h) - 1 for h in cascaded.values())} "
              f"errors were not producers):")
        for (aline, name), hits in sorted(cascaded.items()):
            print(f"  L{aline}  PendingNode.{name}  <- errors at "
                  + ", ".join(str(h) for h in hits))
    if unanchored:
        print(f"\nUNANCHORED ({len(unanchored)}): no constructor literal precedes "
              f"these, so they are counted one-for-one and the total is a CEILING:")
        for raw in unanchored:
            print(f"  L{raw}  in {census[raw]}")
    if not census:
        print("  (none -- the carrier is already discharged everywhere)")


if __name__ == "__main__":
    main()
