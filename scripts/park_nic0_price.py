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
control: it threads the premise through the escape and its four wrappers and
lands on the ELEVEN application sites across FOUR consumer lemmas, reproducing
from cold the count `block_dispatch_deferred`'s own docstring records.

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
    python3 scripts/park_nic0_price.py sites      # threaded to the 11 application sites
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

# `sites` mode threads the premise mechanically through the escape AND its four
# wrappers, so the failures land at the ELEVEN application sites rather than at
# the five signatures between them.  One build sees one ring; this is the ring
# after `escape`'s.
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
        out[sig] = out[sig].rstrip()[:-2].rstrip() + "\n" + PROBE + FIELD
    if which == "escape":
        idx = [i for i, l in enumerate(out) if l == ESCAPE_ANCHOR]
        assert len(idx) == 1, idx
        out[idx[0]] = ESCAPE_PROBE + ESCAPE_ANCHOR
    if which == "sites":
        # The escape's own signature, then each wrapper's, then the two calls.
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
        assert (n_sig, n_park, n_call) == (5, 1, 4), (n_sig, n_park, n_call)
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
    # The escape's own site (item 206) rides in `content_park_nic_any`'s count;
    # ring 2 proper is the remaining twenty-one.
    print(f"\nring 2 (total minus the escape's own site): {total - 1}")


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
                 else " + escape + 4 wrappers threaded" if which == "sites" else ""))
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

    print(f"\nproducer sites: {len(census)}")
    by_decl = {}
    for raw, decl in census.items():
        by_decl.setdefault(decl, []).append(raw)
    print(f"declarations:   {len(by_decl)}\n")
    for decl, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(hits):3d}  {decl}")
    if not census:
        print("  (none -- the carrier is already discharged everywhere)")


if __name__ == "__main__":
    main()
