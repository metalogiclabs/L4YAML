#!/usr/bin/env python3
"""Price the BUILT carrier by producers (DOCS items 266, 267).

Item 266 priced the carrier before it existed, by adding it to `ParkAnchor` as
a field and counting the declarations the arity flip broke.  Item 267 built it,
and the shape it took is not the shape that was priced: the transport core is
its own structure (`ParkCore`), the `[96]` property rides it as one payload
(`ParkAnchor`) and the carrier as another (`ParkSlot`).  So the same instrument
is aimed at the built object.

Five probes, five rings, each a different question:

    core      one required field on `ParkCore`   -> who BUILDS the transport
    slot      one required field on `ParkSlot`   -> who builds the CARRIER
    prop      `parkProp` renamed out from under  -> who READS the `[96]` payload
    consumer  one new hypothesis on `accum_flow_open_depth0`
                                                  -> who must SUPPLY it
    gate      one new hypothesis on `propsPark_open_gate`
                                                  -> who chooses the anchor

A new required field makes every construction site fail on arity whether or not
the field is provable there, so the error list is the producer census exactly
(the reading item 208 established for `scripts/park_top_price.py`).  A RENAME is
what prices a payload the split left in place: deleting the only own-field of a
structure that `extends` another is a different edit, not a smaller one.

Errors are grouped by the DECLARATION that contains them -- never by line
number, which moves.  The script edits a COPY in place and always restores.

Usage:
    python3 scripts/carrier_price.py core
    python3 scripts/carrier_price.py all        # every probe, one line each
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

CORE_STRUCT = "structure ParkCore (sc0 s : ScannerState) (d : Nat) : Prop where"
SLOT_STRUCT = ("structure ParkSlot (sc0 s : ScannerState) (d : Nat) : Prop "
               "extends ParkCore sc0 s d where")
#: A required field that is TRUE of every state: the census is of the sites that
#: must now write something there, not of the sites where the fact is hard.
FIELD = "  probe267 : sc0.indents.size = sc0.indents.size"

PROP_FIELD = "  parkProp : ∃ k, prevRealIdx? sc0.tokens sc0.tokens.size = some k ∧"
PROP_RENAMED = "  parkProp267 : ∃ k, prevRealIdx? sc0.tokens sc0.tokens.size = some k ∧"

CONSUMER = "lemma accum_flow_open_depth0 (sc : ScannerState)"
GATE = "lemma propsPark_open_gate {sc s_prep s' : ScannerState} {sp_scan : SurfPos} {c : Char}"
HYP = "    (h_carrier_266 : True → sc.indents = sc.indents ∧ 0 = 0)"

PROBES = ("core", "slot", "prop", "consumer", "gate")


def _index(lines, needle):
    hits = [i for i, l in enumerate(lines) if l.rstrip() == needle]
    assert len(hits) == 1, f"expected exactly one {needle!r}, found {len(hits)}"
    return hits[0]


def apply_probe(lines, which):
    out = list(lines)
    if which in ("core", "slot"):
        i = _index(out, CORE_STRUCT if which == "core" else SLOT_STRUCT)
        out.insert(i + 1, FIELD)
    elif which == "prop":
        i = _index(out, PROP_FIELD)
        out[i] = PROP_RENAMED
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
    backup = TARGET.with_suffix(".lean.carrier-price-bak")
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
    which = sys.argv[1] if len(sys.argv) > 1 else "core"
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
