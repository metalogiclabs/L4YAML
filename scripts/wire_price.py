#!/usr/bin/env python3
"""Price the WIRING of item 267's carrier, by producers (DOCS item 268).

Item 267 built `ParkSlot` — the transport core plus the column the depth-0 open
landed at, still standing on the park's indent stack — and two spends that fire
the gates a landing dies at.  Nothing consumes it: `accum_flow_open_depth0`
hands `h_kpkg none`, so the frame the under-run's open pushes is UNGATED, its
node route is unconditional, and only `dropClose` can supply one.

Item 268's question is what it costs to gate that frame.  Four probes, four
rings, each a different question:

    gate      `GateOf` gains an arity        -> who READS the frame's gate
    anchor    `FlowBaseAnchor` gains a third
              conjunct (`ParkSlot`)          -> who BUILDS a gated frame
    route     `FlowBaseRoutes.value` gains a
              hypothesis                     -> who supplies and who applies
                                                the node reading
    eof       `scanNextToken_none_stream`
              gains a hypothesis             -> who drives the END-OF-INPUT
                                                consumer

Each probe makes an edit that fails on ARITY, so the error list is the census of
sites that must write something rather than of sites where the fact is hard --
the reading item 208 established for `scripts/park_top_price.py` and item 266
re-used for `scripts/carrier_price.py`.

Errors are grouped by the DECLARATION that contains them, never by line number.
The script edits the file in place and always restores it.

**What this reads and what it does not.**  The probe elaborates
`StreamAccum.lean` alone (`lake env lean`), so the census is the LIBRARY's own
chain.  Guard files that mention the same names are counted separately by
`--wide`, which builds the tree instead and costs minutes rather than seconds.

Usage:
    python3 scripts/wire_price.py gate
    python3 scripts/wire_price.py all          # every probe, one line each
    python3 scripts/wire_price.py all --wide   # …over the whole tree
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

GATEOF_HEAD = "def GateOf : Option ScannerState → Prop"
GATEOF_NONE = "  | none => True"
GATEOF_SOME = "  | some sc0 => danglingNodePos? sc0 = none"
GATEOF_HEAD2 = "def GateOf : Option ScannerState → Nat → Prop"
GATEOF_NONE2 = "  | none, _ => True"
GATEOF_SOME2 = "  | some sc0, _ => danglingNodePos? sc0 = none"

ANCHOR_ARM = "  | some sc0, s, d => ParkAnchor sc0 s d ∧ ParkFloor sc0 s d"
ANCHOR_ARM2 = ("  | some sc0, s, d => ParkAnchor sc0 s d ∧ ParkFloor sc0 s d "
               "∧ ParkSlot sc0 s d")

ROUTE_FIELD = "  value : GateOf g → ∀ sp_ne sp_mid, SFlowContent n .flowOut sp_br sp_ne →"
ROUTE_FIELD2 = ("  value : GateOf g → 0 = 0 → ∀ sp_ne sp_mid, "
                "SFlowContent n .flowOut sp_br sp_ne →")

EOF_HEAD = "lemma scanNextToken_none_stream (sc : ScannerState)"
#: A hypothesis that is TRUE everywhere: the census is of the sites that must
#: now write something there, not of the sites where the fact is hard.
HYP = "    (h_wire268 : True → sc.indents = sc.indents ∧ 0 = 0)"

PROBES = ("gate", "anchor", "route", "eof")


def _index(lines, needle):
    hits = [i for i, l in enumerate(lines) if l.rstrip() == needle]
    assert len(hits) == 1, f"expected exactly one {needle!r}, found {len(hits)}"
    return hits[0]


def apply_probe(lines, which):
    out = list(lines)
    if which == "gate":
        out[_index(out, GATEOF_HEAD)] = GATEOF_HEAD2
        out[_index(out, GATEOF_NONE)] = GATEOF_NONE2
        out[_index(out, GATEOF_SOME)] = GATEOF_SOME2
    elif which == "anchor":
        out[_index(out, ANCHOR_ARM)] = ANCHOR_ARM2
    elif which == "route":
        out[_index(out, ROUTE_FIELD)] = ROUTE_FIELD2
    elif which == "eof":
        # A new binder goes in FIRST position, right after the head line: the
        # variable it mentions is bound there, and no binder list has to be
        # parsed to find the end of one.
        out.insert(_index(out, EOF_HEAD) + 1, HYP)
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


def run(which, verbose=True, wide=False):
    original = TARGET.read_text()
    backup = TARGET.with_suffix(".lean.wire-price-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched = apply_probe(original.split("\n"), which)
        TARGET.write_text("\n".join(patched))
        cmd = (["lake", "build"] if wide
               else ["lake", "env", "lean", str(TARGET.relative_to(ROOT))])
        proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    here = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    other = re.compile(r"^(?!L4YAML/Proofs/Production/StreamAccum\.lean)"
                       r"([A-Za-z0-9_./-]+\.lean):(\d+):\d+: error")
    raw = sorted({int(m.group(1)) for m in
                  (here.match(l) for l in body.split("\n")) if m})
    away = sorted({m.group(1) for m in
                   (other.match(l) for l in body.split("\n")) if m})
    # A probe that breaks NOTHING has not been applied -- an empty census over
    # an unedited file is the vacuous reading §9 warns about.
    if not raw and not away:
        raise SystemExit(f"{which}: the probe broke nothing -- it did not apply")
    by_decl = {}
    for r in raw:
        by_decl.setdefault(enclosing_decl(patched, r), []).append(r)
    if verbose:
        print(f"probe {which}: {len(raw)} error sites in {len(by_decl)} "
              f"declarations\n")
        for decl, hits in sorted(by_decl.items(),
                                 key=lambda kv: (-len(kv[1]), kv[0])):
            print(f"  {len(hits):3d}  {decl}")
        if away:
            print("\n  files outside the module: " + ", ".join(away))
    return len(raw), len(by_decl), sorted(by_decl), away


PIN = ROOT / "Tests" / "Guards" / "Proofs" / "ScannerFlowOpenUnderRun.lean"


def expected():
    """The literal Lean carries and no Lean code can re-derive."""
    if not PIN.exists():
        return None
    m = re.search(r'def expectedWirePrice : String :=\s*\n?\s*"([^"]*)"',
                  PIN.read_text())
    return m.group(1) if m else None


def main():
    argv = [a for a in sys.argv[1:] if a != "--wide"]
    wide = "--wide" in sys.argv
    which = argv[0] if argv else "gate"
    if which == "all":
        rows = []
        for p in PROBES:
            n, d, names, away = run(p, verbose=False, wide=wide)
            rows.append((p, n, d, names))
            line = f"{p:7s} errors={n:3d}  declarations={d:2d}  " + ", ".join(names)
            if away:
                line += f"   | outside: {len(away)} files"
            print(line)
        got = " ".join(f"{p}={d}" for p, n, d, _ in rows)
        print("\nWIRE-PRICE " + got)
        want = expected()
        if want is None:
            print(f"no pin in {PIN.relative_to(ROOT)}")
            return 1
        if want != got:
            print(f"WIRE-PIN DISAGREES\n  Lean:   {want}\n  script: {got}")
            return 1
        print(f"WIRE-PIN agrees with {PIN.relative_to(ROOT)}")
        return 0
    if which not in PROBES:
        sys.exit("usage: wire_price.py [" + "|".join(PROBES) + "|all] [--wide]")
    run(which, wide=wide)
    return 0


if __name__ == "__main__":
    sys.exit(main() or 0)
