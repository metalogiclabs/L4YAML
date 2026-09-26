#!/usr/bin/env python3
"""Every dispatcher GATE named in the tree's prose resolves in the environment
(DOCS item 265).

Item 172 moved §8.1's floor for a flow open from the open's own step to the
close and the check that used to run there, `scanNextToken_checkBlockFlowIndent`,
stopped existing.  The name did not: item 265 found it in **thirty-two** places
across **fourteen** files, including the comment on the very arm that was being
priced, where it carried the claim that the arm was REFUTED — two lines above
the line that rides the escape.  Nothing checks a backticked identifier in a
docstring against the environment, so a deleted gate can keep describing the
dispatcher indefinitely, and a reader pricing that arm reads the comment first.

This is that check, for the gate vocabulary only:

  * `scanNextToken_…`, `scanLoop_…`, `scanLoopIx_…` written out in full, and
  * `check<Upper>…` written short, which is how the prose usually names them.

A name resolves if it is the final component of a constant in the wide
environment, bare or under any of the three prefixes.  Family references
(`dispatchStructural_none_*`) are not constants and are counted separately;
so are names a line break splits across two lines, which this script cannot
see and says so rather than scoring them as clean.

    scripts/gate_vocab.py           # the census, compared against the pin
    scripts/gate_vocab.py --list    # …and every mention of every name

The pin lives in `Tests/Guards/Proofs/GateVocabulary.lean`, which is also the one
file the scan skips: it has to spell the deleted gate out to say what the check
is for, and that exclusion is reported as `self=` rather than left silent.  Lean
cannot read
its own comments, so the reading is Python's and the LITERAL is Lean's.
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / "L4YAML" / "Scratch"
PIN = ROOT / "Tests" / "Guards" / "Proofs" / "GateVocabulary.lean"

_spec = importlib.util.spec_from_file_location(
    "drop_sweep", Path(__file__).resolve().parent / "drop_sweep.py")
drop_sweep = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(drop_sweep)

PREFIXES = ("scanNextToken_", "scanLoop_", "scanLoopIx_")

#: A backticked gate name, qualified or short.  The closing backtick is
#: required: an identifier a line break splits is counted by `WRAP`, not here.
QUAL = re.compile(r"`((?:scanNextToken_|scanLoop_|scanLoopIx_)[A-Za-z0-9_']+)`")
#: …and the short form.  Two capitalized segments are required: every gate in
#: the dispatcher has at least two (`checkBareDocument`, `checkFlowValueIndent`),
#: and requiring them keeps one-letter macros such as `checkM` out.
SHORT = re.compile(r"`(check(?:[A-Z][a-z0-9']+){2,}[A-Za-z0-9_']*)`")
#: An opening backtick on a gate name with no closing backtick on the line.
WRAP = re.compile(r"`(?:scanNextToken_|scanLoop_|scanLoopIx_|check[A-Z])[A-Za-z0-9_']*$")

DUMP = """{imports}

open Lean Elab Command in
run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    out := out.push n.getString!
  IO.FS.writeFile "{out}" (String.intercalate "\\n" out.toList.eraseDups)
  logInfo m!"dumped"
"""


def sources() -> list[Path]:
    return sorted(p for p in (list((ROOT / "L4YAML").rglob("*.lean"))
                              + list((ROOT / "Tests").rglob("*.lean")))
                  if "/Scratch/" not in str(p))


def scan() -> tuple[dict[str, list[tuple[str, int]]], int, int, int]:
    """(name -> mentions, family references, line-wrapped openings, mentions
    inside the pin file itself).

    The pin file has to spell the deleted gate out in order to say what this
    check is for, so it is the one file excluded — and the exclusion is
    counted rather than silent."""
    hits: dict[str, list[tuple[str, int]]] = defaultdict(list)
    families = wrapped = mine = 0
    for p in sources():
        rel = str(p.relative_to(ROOT))
        if p == PIN:
            mine += sum(len(pat.findall(line)) for line in p.read_text().splitlines()
                        for pat in (QUAL, SHORT))
            continue
        for i, line in enumerate(p.read_text().splitlines(), 1):
            for pat in (QUAL, SHORT):
                for m in pat.finditer(line):
                    hits[m.group(1)].append((rel, i))
            families += len(re.findall(
                r"`(?:scanNextToken_|scanLoop_|scanLoopIx_|check[A-Z])"
                r"[A-Za-z0-9_']*\*`", line))
            if WRAP.search(line):
                wrapped += 1
    return hits, families, wrapped, mine


def constants(quiet: bool) -> set[str]:
    wide, _entry, _unbuilt = drop_sweep.modules()
    SCRATCH.mkdir(exist_ok=True)
    out = SCRATCH / "gateconsts.txt"
    probe = SCRATCH / "GateVocabDump.lean"
    probe.write_text(DUMP.format(
        imports="\n".join(f"import {m}" for m in wide), out=out))
    try:
        rc, log = drop_sweep.run(probe)
        if rc != 0 or not out.exists():
            print(log.strip()[-2000:], file=sys.stderr)
            raise SystemExit("gate_vocab: the environment dump did not run")
        names = set(out.read_text().split())
    finally:
        probe.unlink(missing_ok=True)
        out.unlink(missing_ok=True)
    if not quiet:
        print(f"environment: {len(names)} distinct final name components")
    return names


def expected() -> str | None:
    if not PIN.exists():
        return None
    m = re.search(r'def expectedGateVocab : String :=\s*\n?\s*"([^"]*)"',
                  PIN.read_text())
    return m.group(1) if m else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true",
                    help="print every mention of every gate name")
    args = ap.parse_args()

    hits, families, wrapped, mine = scan()
    if not hits:
        print("gate_vocab: no gate name found in any comment — the scan is "
              "reading nothing, which is not the same as a clean tree")
        return 1
    names = constants(quiet=False)

    def ok(n: str) -> bool:
        return n in names or any(p + n in names for p in PREFIXES)

    unresolved = sorted(n for n in hits if not ok(n))
    mentions = sum(len(v) for v in hits.values())
    got = (f"names={len(hits)} mentions={mentions} families={families} "
           f"wrapped={wrapped} self={mine} unresolved={len(unresolved)}")
    print("GATEVOCAB " + got)

    if args.list:
        for n in sorted(hits):
            print(f"  {'OK ' if ok(n) else 'MISS'} {n}  ({len(hits[n])})")
    for n in unresolved:
        print(f"  UNRESOLVED {n}")
        for f, i in hits[n]:
            print(f"      {f}:{i}")

    rc = 0
    want = expected()
    if want is None:
        print(f"no pin in {PIN.relative_to(ROOT)}")
        rc = 1
    elif want != got:
        print(f"GATE-PIN DISAGREES\n  Lean:   {want}\n  script: {got}")
        rc = 1
    else:
        print(f"GATE-PIN agrees with {PIN.relative_to(ROOT)}")
    if unresolved:
        rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
