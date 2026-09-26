#!/usr/bin/env python3
"""Price item 265's carrier by producers (DOCS item 266).

Item 265 named ONE fact the run-end refutation needs -- *the flow collection
closes with the open's column still on the indent stack* -- and showed that no
hypothesis of `accum_flow_open_depth0` can deliver it, because the gates that
kill the input run three to five steps later.  §10 prices a missing carrier by
the PRODUCERS it touches, not by the goal it would close, and this script is
that census.

The transport the carrier needs already exists: `ParkAnchor sc0 s d` runs a fact
from a depth-0 flow OPEN to its CLOSE and is spent there by
`ParkAnchor.dangling_eq`, whose premises are item 265's `deathShape` component
for component.  What blocks it is one field -- `parkProp`, "the park's last real
token is a node property" -- which holds at 18 of the 144 landings and is a pure
PASSENGER in every transport lemma.

Four probes, four rings, each a different question:

    passenger the carrier as a field on `ParkAnchor`  -> who BUILDS the anchor
    heavy     the same fact read off the array        -> the same, not a passenger
    prop      `parkProp` deleted from `ParkAnchor`    -> who TOUCHES it at all
    consumer  one new hypothesis on `accum_flow_open_depth0`
                                                      -> who must SUPPLY it
    gate      one new hypothesis on `propsPark_open_gate`
                                                      -> who chooses the anchor

A new required field makes every application site fail on arity whether or not
the field is provable there, so the error list is the producer census exactly
(the reading item 208 established for `scripts/park_top_price.py`).

Errors are grouped by the DECLARATION that contains them -- never by line
number, which moves.  The script edits a COPY in place and always restores.

Usage:
    python3 scripts/carrier_price.py passenger
    python3 scripts/carrier_price.py all        # every probe, one line each
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

STRUCT = "structure ParkAnchor (sc0 s : ScannerState) (d : Nat) : Prop where"
PROP_FIELD = "  parkProp : ∃ k, prevRealIdx? sc0.tokens sc0.tokens.size = some k ∧"
PROP_CONT = "    sc0.tokens[k]!.val.isNodeProperty = true"
# The carrier itself, as a field.  Measured (`scripts/` has no probe for this;
# `Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean` §6 pins it): the open's
# column IS the park's own cursor column, at all 144 landings, so the carrier is
# a fact about `sc0` ALONE -- a passenger every transport lemma carries for free.
PASSENGER = ("  parkOpenCol : sc0.indents.any "
             "(fun e => e.column == (sc0.col : Int)) = true")
# The same fact read off the ARRAY instead of the cursor.  It mentions `s`, so it
# is not a passenger: every transport lemma would have to re-prove it above the
# park's prefix, which `below` does not reach.  Kept as the second reading, so
# the passenger claim is a COMPARISON and not an assertion.
HEAVY = ("  parkOpenCol : sc0.indents.any "
         "(fun e => e.column == (s.tokens[sc0.tokens.size]!.pos.col : Int)) = true")

CONSUMER = "lemma accum_flow_open_depth0 (sc : ScannerState)"
GATE = "lemma propsPark_open_gate {sc s_prep s' : ScannerState} {sp_scan : SurfPos} {c : Char}"
HYP = "    (h_carrier_266 : True → sc.indents = sc.indents ∧ 0 = 0)"

PROBES = ("passenger", "heavy", "prop", "consumer", "gate")


def _index(lines, needle):
    hits = [i for i, l in enumerate(lines) if l.rstrip() == needle]
    assert len(hits) == 1, f"expected exactly one {needle!r}, found {len(hits)}"
    return hits[0]


def apply_probe(lines, which):
    out = list(lines)
    if which in ("passenger", "heavy"):
        i = _index(out, STRUCT)
        out.insert(i + 1, PASSENGER if which == "passenger" else HEAVY)
    elif which == "prop":
        i = _index(out, PROP_FIELD)
        assert out[i + 1].rstrip() == PROP_CONT, out[i + 1]
        del out[i : i + 2]
    elif which in ("consumer", "gate"):
        # A new binder goes in FIRST position, right after the head line: the
        # variable it mentions is bound there, and no binder list has to be
        # parsed to find the end of one.
        head = CONSUMER if which == "consumer" else GATE
        i = _index(out, head)
        out.insert(i + 1, HYP)
    else:
        raise AssertionError(which)
    return out


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def|structure|abbrev) "
                     r"([A-Za-z_][A-Za-z0-9_.'!?]*)", lines[i])
        if m:
            decl = m.group(1)
    return decl


def run(which, verbose=True):
    original = TARGET.read_text()
    backup = TARGET.with_suffix(".lean.carrier266-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched = apply_probe(original.split("\n"), which)
        TARGET.write_text("\n".join(patched))
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    pat = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    raw = sorted({int(m.group(1)) for m in
                  (pat.match(l) for l in body.split("\n")) if m})
    # A probe that breaks NOTHING has not been applied -- an empty census over an
    # unedited file is the vacuous reading §9 warns about.
    if not raw:
        raise SystemExit(f"{which}: the probe broke nothing -- it did not apply")
    by_decl = {}
    for r in raw:
        by_decl.setdefault(enclosing_decl(patched, r), []).append(r)
    if verbose:
        print(f"probe {which}: {len(raw)} error sites in {len(by_decl)} declarations\n")
        for decl, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            print(f"  {len(hits):3d}  {decl}")
    return len(raw), len(by_decl), sorted(by_decl)


PIN = ROOT / "Tests" / "Guards" / "Proofs" / "ScannerFlowOpenUnderRun.lean"


def expected():
    """The literal Lean carries and no Lean code can re-derive."""
    if not PIN.exists():
        return None
    m = re.search(r'def expectedCarrierPrice : String :=\s*\n?\s*"([^"]*)"',
                  PIN.read_text())
    return m.group(1) if m else None


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "passenger"
    if which == "all":
        rows = []
        for p in PROBES:
            n, d, names = run(p, verbose=False)
            rows.append((p, n, d, names))
            print(f"{p:9s} errors={n:3d}  declarations={d:2d}  "
                  + ", ".join(names))
        got = " ".join(f"{p}={d}" for p, n, d, _ in rows)
        print("\nCARRIER-PRICE " + got)
        want = expected()
        if want is None:
            print(f"no pin in {PIN.relative_to(ROOT)}")
            return 1
        if want != got:
            print(f"CARRIER-PIN DISAGREES\n  Lean:   {want}\n  script: {got}")
            return 1
        print(f"CARRIER-PIN agrees with {PIN.relative_to(ROOT)}")
        return 0
    if which not in PROBES:
        sys.exit("usage: carrier_price.py [" + "|".join(PROBES) + "|all]")
    run(which)
    return 0


if __name__ == "__main__":
    sys.exit(main() or 0)
