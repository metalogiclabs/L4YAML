#!/usr/bin/env python3
"""Price the ARMED-AT-COLUMN-ZERO carrier (item 206) -- ring 2 of item 205's ring.

Item 205 paid the first ring of `_stamp_compact`'s carrier and found that three
of its seven producers can pay only from `h_nic0` -- item 154's flag, read at a
BLOCK landing:

    sp_scan.col = 0 -> sc.needIndentCheck = true

That flag is a field on `pendingContent` (as an OPTION) and on nothing else.
Item 205 measured which parks would have to carry it and recorded the counts
from a single reading; this script re-derives each one by paying it and
re-running, exactly as `park_top_price.py` does for the park TOP.

The number that matters is `pendingFlow`'s: its one producer is
`block_dispatch_deferred` itself, so its count is a claim about how far the
carrier's price re-enters the escape being retired.

MEASURED (item 206, and none of the five matched the reading item 205 recorded
for it except `pendingDocEnd` and `pendingBlockContent`):

    pendingContent       12 sites /  4 declarations   (item 205 read 17)
    pendingDocEnd         1       /  1
    pendingDocStart       2       /  2                (item 205 read 4)
    pendingFlow           1       /  1                (item 205 read 10)  -- PAID
    pendingBlockContent   6       /  2

`pendingFlow`'s field LANDED at item 206 and the other four at item 207, so
every count above is now DISCHARGED and a re-run of any mode prices a SECOND
field rather than the first.  That is the mode's own control: the census is
stable across the payment, and all five reproduce.  `sites` is the other
control: it threads the premise through the escape and each of its wrappers and
lands on the escape's own application sites, reproducing from cold the count
`block_dispatch_deferred`'s docstring records -- ELEVEN across FOUR consumer
lemmas when item 206 built it, and **NINE across FOUR** since item 209 deleted
`_stamp_compact` (3 `accum_block_on_closeThenBlock`, 3
`..._pendingBlockContent`, 2 `..._pendingBlock`, 1 `accum_content_pending`).

Item 210 repaired this mode twice over: item 208's cascade collapse anchored its
failures on a constructor literal and reported 9 sites as 1, and item 209's
deletion fired a control that pinned the wrapper COUNT.  Neither item re-ran it.
A count the campaign is moving is the one thing a control must not pin.

`payers` (item 207) splits the paid ring by the TERM each site spends, which is
the number item 206 forecast and got wrong: it predicted `content_park_nic_any`
at eighteen sites, and the split is 13 / 3 / 5.

    content_park_nic_any   14   (13 ring-2 + 1 the escape's own, item 206)
    content_park_nic        3   (item 154's, block-scalar arms, unchanged)
    nic0_of_col_pos         5   (2 flow closes + 3 marker parks)

Usage:
    python3 scripts/park_nic0_price.py pendingFlow
    python3 scripts/park_nic0_price.py all
    python3 scripts/park_nic0_price.py escape     # the field + the escape's premise
    python3 scripts/park_nic0_price.py sites      # threaded to the escape's own sites
    python3 scripts/park_nic0_price.py payers     # the paid ring, split by term
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

# The five parks item 205 named as ring 2.  `pendingContent` already carries the
# flag as an OPTION (`... v True`); probing it with a REQUIRED field measures the
# same thing the item priced -- the producers that would have to make it
# unconditional.
PARKS = ["pendingContent", "pendingDocEnd", "pendingDocStart",
         "pendingFlow", "pendingBlockContent"]

PROBE = "  -- NIC0 PROBE (scripts/park_nic0_price.py)\n"
FIELD = "      (h_nic0_probe : sp_scan.col = 0 → sc.needIndentCheck = true) :"

# `block_dispatch_deferred`'s own signature, for the `escape` mode: the premise
# its `pendingFlow` application would need if the field were required.
ESCAPE_ANCHOR = "    (h_nic0 : sp_scan'.col = 0 → s'.needIndentCheck = true) :"
ESCAPE_PROBE = ("    -- NIC0 PROBE (scripts/park_nic0_price.py)\n"
                "    (h_nic0_probe : sp_scan'.col = 0 → s'.needIndentCheck = true)\n")

# `sites` mode threads the premise mechanically through the escape AND each of
# its wrappers, so the failures land at the escape's application sites rather
# than at the signatures between them.  One build sees one ring; this is the
# ring after `escape`'s.
WRAP_ANCHOR = "    (h_nic0 : sp_scan'.col = 0 → s'.needIndentCheck = true)"
WRAP_PROBE = "    (h_nic0_probe : sp_scan'.col = 0 → s'.needIndentCheck = true)"
# Post-item-206: the real `h_nic0` is threaded through both, so the probe's
# extra field rides behind it.
PARK_CALL = ("   PendingNode.pendingFlow sp_start sp_X sp_scan' "
             "h_stream h_arm h_nodir h_nic0,")
ESCAPE_CALL = ("  block_dispatch_deferred sp_start sp_X sp_scan' s' "
               "h_stream h_arm hcorr h_nodir h_nic0")


def constructor_spans(lines):
    """Map each PendingNode constructor to the index of its conclusion line."""
    spans, current = {}, None
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
    if which == "all":
        targets = PARKS
    elif which in ("escape", "sites"):
        targets = ["pendingFlow"]
    else:
        targets = [which]
    out = list(lines)
    for name in sorted(targets, key=lambda n: -spans[n]):
        sig = spans[name] - 1
        assert out[sig].rstrip().endswith(") :"), out[sig]
        out[sig : sig + 1] = [out[sig].rstrip()[:-2].rstrip(),
                              PROBE.rstrip("\n"), FIELD]
    if which == "escape":
        idx = [i for i, l in enumerate(out) if l == ESCAPE_ANCHOR]
        assert len(idx) == 1, idx
        out[idx[0]] = ESCAPE_PROBE + ESCAPE_ANCHOR
    if which == "sites":
        # The escape's own signature, then each wrapper's, then the calls.
        n_sig = n_park = n_call = 0
        for i, l in enumerate(out):
            if l == WRAP_ANCHOR + " :":
                out[i] = WRAP_ANCHOR + "\n" + WRAP_PROBE + " :"; n_sig += 1
            elif l == WRAP_ANCHOR:
                out[i] = WRAP_ANCHOR + "\n" + WRAP_PROBE; n_sig += 1
            elif l == PARK_CALL:
                out[i] = PARK_CALL[:-1] + " h_nic0_probe,"; n_park += 1
            elif l == ESCAPE_CALL:
                out[i] = ESCAPE_CALL + " h_nic0_probe"; n_call += 1
        # **Item 210: pin the RELATION, not the literal.**  This control read
        # `(n_sig, n_park, n_call) == (5, 1, 4)` — the escape plus its four
        # wrappers — and item 209 deleted `_stamp_compact`, so the assertion
        # fired and the mode could not run at all.  A count the campaign is
        # actively moving is the one thing a control must not pin: every wrapper
        # contributes one signature and one call, the escape contributes the
        # remaining signature and the single `pendingFlow` application, and that
        # holds however many wrappers are left.
        assert n_park == 1 and n_call >= 1 and n_sig == n_call + 1, (
            f"splice landed on {n_sig} signatures, {n_park} park applications "
            f"and {n_call} escape calls; expected one signature per wrapper "
            f"plus the escape's own, one call per wrapper, and one park")
    return out, sorted(targets)


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def) (\w+)", lines[i])
        if m:
            decl = m.group(1)
    return decl


# `payers` mode: the three terms a paid site can spend, matched at APPLICATION
# position (an open paren before the name) so the declarations and the prose
# that names them are not counted.

# The block dispatch's landing arms and the dispatcher that cases the park.  A
# flag payment inside one of these is the LANDING's (item 210's census), not a
# park producer's (item 207's ring 2).
LANDING_DECLS = {
    "accum_block_pending", "accum_block_on_noPending",
    "accum_block_on_closeThenBlock", "accum_block_on_pendingContent",
    "accum_block_on_pendingBlockContent", "accum_block_on_pendingBlock",
}

PAYERS = [
    ("content_park_nic_any", re.compile(r"\(content_park_nic_any\b")),
    ("content_park_nic", re.compile(r"\(content_park_nic hbs\b")),
    ("nic0_of_col_pos", re.compile(r"\(nic0_of_col_pos\b")),
]


def payers_census():
    """Split the PAID ring by the term each site spends (item 207)."""
    lines = TARGET.read_text().split("\n")
    census = {name: [] for name, _ in PAYERS}
    for i, line in enumerate(lines):
        for name, pat in PAYERS:
            if pat.search(line):
                census[name].append((i + 1, enclosing_decl(lines, i + 1)))
    total = sum(len(v) for v in census.values())
    print(f"paid sites: {total}\n")
    for name, hits in census.items():
        by_decl = {}
        for ln, decl in hits:
            by_decl.setdefault(decl, 0)
            by_decl[decl] += 1
        print(f"  {len(hits):3d}  {name}")
        for decl, n in sorted(by_decl.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"         {n:3d}  {decl}")
    # **Item 210: the total spans TWO rings now, so the mode splits them.**
    # Item 207 printed `total - 1` and called the remainder ring 2, which was
    # true while every site in the file was a park PRODUCER.  Items 208 and 209
    # paid the flag at the block LANDING too, and those payments spend the same
    # three terms — so the undifferentiated total silently absorbed a second
    # ring.  The split is by the declaration a site sits in: a landing consumer
    # or the dispatcher that cases the park, against everything else.
    landing = sum(1 for hits in census.values() for _, decl in hits
                  if decl in LANDING_DECLS)
    print(f"\nring 2, the park PRODUCERS (total minus the landing's payments "
          f"and the escape's own site): {total - landing - 1}")
    print(f"the LANDING's own payments (item 210's ring): {landing}")


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "pendingFlow"
    if which == "payers":
        payers_census()
        return
    if which not in PARKS + ["all", "escape", "sites"]:
        sys.exit(f"usage: park_nic0_price.py "
                 f"[{'|'.join(PARKS)}|all|escape|sites|payers]")

    original = TARGET.read_text()
    backup = TARGET.with_suffix(".lean.nic0-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched, names = apply_probe(original.split("\n"), which)
        TARGET.write_text("\n".join(patched))
        print(f"probe: {which} -> {', '.join(names)}"
              + (" + block_dispatch_deferred premise" if which == "escape"
                 else " + escape and every wrapper threaded" if which == "sites"
                 else ""))
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    src = TARGET.read_text().split("\n")
    patched, _ = apply_probe(src, which)
    pat = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    census = {}
    for line in body.split("\n"):
        m = pat.match(line)
        if m:
            census.setdefault(int(m.group(1)), None)
    for raw in census:
        census[raw] = enclosing_decl(patched, raw)

    # Item 208: an error is not a producer.  A constructor application whose
    # arguments are `by` blocks reports one failure per broken block, which is
    # how `noPending` read 11 for a census of 8 (`park_top_price.py`).  Anchor
    # each error on the nearest preceding APPLICATION and print what collapsed.
    # **Item 210: the collapse needs the anchor the MODE is measuring.**  In
    # `sites` the failures land at the ESCAPE's application sites, not at
    # constructor applications, so a constructor-literal anchor list put all
    # nine of them behind the single `PendingNode.pendingFlow` inside the escape
    # and reported a census of 1.  The collapse item 208 added to fix
    # `noPending`'s cascade broke this mode the same day, and nothing re-ran it.
    if which == "sites":
        esc = re.compile(r"(^|[ (⟨])block_dispatch_deferred\w*\b")
        anchors = [(i + 1, "block_dispatch_deferred")
                   for i, line in enumerate(patched)
                   if esc.search(line) and "`" not in line
                   and not re.match(r"^(private )?lemma ", line)
                   and not line.lstrip().startswith("--")]
    else:
        anchors = [(i + 1, f"PendingNode.{n}")
                   for i, line in enumerate(patched) for n in names
                   if f"PendingNode.{n}" in line]
    groups, unanchored = {}, []
    for raw in sorted(census):
        prior = [a for a in anchors if a[0] <= raw]
        (unanchored.append(raw) if not prior
         else groups.setdefault(prior[-1], []).append(raw))

    print(f"\nraw error sites: {len(census)}")
    print(f"applications:    {len(groups) + len(unanchored)}   <- the producer census")
    by_decl = {}
    for (aline, _n), hits in groups.items():
        by_decl.setdefault(enclosing_decl(patched, aline), []).append(hits)
    for raw in unanchored:
        by_decl.setdefault(census[raw], []).append([raw])
    print(f"declarations:    {len(by_decl)}\n")
    for decl, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(hits):3d}  {decl}")
    cascaded = {a: h for a, h in groups.items() if len(h) > 1}
    if cascaded:
        print(f"\ncollapsed cascades "
              f"({sum(len(h) - 1 for h in cascaded.values())} errors were not "
              f"producers):")
        for (aline, n), hits in sorted(cascaded.items()):
            print(f"  L{aline}  {n}  <- errors at "
                  + ", ".join(map(str, hits)))
    if unanchored:
        print(f"\nUNANCHORED ({len(unanchored)}): no constructor literal precedes "
              f"these, so they are counted one-for-one and the total is a CEILING:")
        for raw in unanchored:
            print(f"  L{raw}  in {census[raw]}")
    if not census:
        print("  (none -- the carrier is already discharged everywhere)")


if __name__ == "__main__":
    main()
