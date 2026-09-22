#!/usr/bin/env python3
"""Run the flow-key SUPPLY flip gate and report the DEFINITIONS it breaks
(DOCS item 233).

`FlowBaseRoutes.key`'s HEAD conjunct promises

    ∀ sp_end, SFlowContent n .flowOut sp_br sp_end →
      ImplicitKeyHead sp_key sp_end ∨ True

and that `∨ True` is where the eight `FlowKeyLift` conversions' `SepResidue`
is thrown away.  This gate tightens the promise to take the two facts
`[193] c-s-implicit-json-key` supplies about everything that reaches a `:` —
the key crosses no line, and the input did not run out — and drops the
disjunction:

    ∀ sp_end, SFlowContent n .flowOut sp_br sp_end →
      ¬ BreakBetween sp_br sp_end → ¬ L4YAML.Surface.atEnd sp_end →
      ImplicitKeyHead sp_key sp_end

then builds and reports the definitions that stop compiling.  That set is the
supply side's price, measured rather than forecast, and item 210's rule
applies: **record definitions, not line numbers.**

**The count is a LOWER bound and the gate says so.**  All four slot sites are
in one module, so `lake build` stops there and every job behind it is never
attempted; a definition that would have broken downstream is invisible to this
run.  An error count is a property of how a proof is written (item 228's own
instrument debt), and a count taken from a build that stopped is a property of
where it stopped as well.

    scripts/flip_supply.py                    # run the gate end to end
    scripts/flip_supply.py --map <build.log>  # just map an existing log

Destructive while it runs — it edits `L4YAML/Proofs/Production/StreamAccum.lean`
in place — so it restores from its own backup in a `finally` and prints the md5
both before and after.  A run that dies between the two leaves the backup
beside the source.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML" / "Proofs" / "Production" / "StreamAccum.lean"

#: The four sites that spell the head promise: `FlowBaseRoutes.key` itself and
#: the three lemmas that restate it (`flowKeyPack_of_close`,
#: `flowKeyRoute_of_open`, `flowKeyRoute_of_root`).  The left endpoint differs
#: between them (`sp_br` on the frame, `sp_prep` on the routes), so the
#: hypothesis is built from what the line itself says rather than typed in.
SITES = 4
PAT = re.compile(
    r"\(∀ sp_end, SFlowContent (\w+) \.flowOut (\w+) sp_end →\n"
    r"(\s*)ImplicitKeyHead sp_key sp_end ∨ True\)")

#: The log mapper is item 210's; one instrument, two gates.
_spec = importlib.util.spec_from_file_location(
    "flip210", Path(__file__).resolve().parent / "flip_210.py")
flip210 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(flip210)


def tighten(m: re.Match) -> str:
    idx, left, pad = m.group(1), m.group(2), m.group(3)
    return (f"(∀ sp_end, SFlowContent {idx} .flowOut {left} sp_end →\n"
            f"{pad}¬ BreakBetween {left} sp_end → ¬ L4YAML.Surface.atEnd sp_end →\n"
            f"{pad}ImplicitKeyHead sp_key sp_end)")


def md5(path: Path) -> str:
    return hashlib.md5(path.read_bytes()).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--map", metavar="LOG",
                    help="map an existing build log instead of running the gate")
    ap.add_argument("--log", metavar="PATH", help="write the build log here")
    args = ap.parse_args()

    if args.map:
        return 1 if flip210.report(Path(args.map).read_text()) else 0

    before = md5(SRC)
    print(f"md5 before  {before}")
    src = SRC.read_text()
    flipped, n = PAT.subn(tighten, src)
    print(f"SITES {n}")
    if n != SITES:
        sys.exit(f"the head promise no longer reads as {SITES} sites of the "
                 "expected shape; this gate needs re-aiming")
    backup = SRC.with_suffix(".lean.flip-backup")
    shutil.copy(SRC, backup)
    bad = 0
    try:
        SRC.write_text(flipped)
        out = subprocess.run(["lake", "build"], cwd=ROOT,
                             capture_output=True, text=True)
        log = out.stdout + out.stderr
        if args.log:
            Path(args.log).write_text(log)
        if out.returncode == 0:
            print("THE FLIP BUILT CLEAN — the tightening costs nothing, which "
                  "is a finding and not a pass")
            return 1
        bad = flip210.report(log)
        print("LOWER BOUND — the build stopped at the first failing module, so "
              "no definition behind it was attempted")
    finally:
        shutil.copy(backup, SRC)
        backup.unlink()
        after = md5(SRC)
        print(f"md5 after   {after}")
        if after != before:
            sys.exit("the restore did not restore; fix the source before "
                     "trusting anything else in this run")
        print("rebuilding so no later probe reads the flipped oleans...")
        subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
