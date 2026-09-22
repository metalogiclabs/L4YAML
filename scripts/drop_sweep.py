#!/usr/bin/env python3
"""Sweep the WHOLE tree for proof-term dependents of `SLYamlStream.scannerDrop`
(DOCS item 238).

`Tests/Guards/Proofs/DropDependents.lean` re-derives the same four counts at
every build, but it can only read its own import closure, and item 237's own
first pass read 109 of 230 modules while reporting a library.  This script is
the wide reading: it imports **every** `L4YAML.*` and `Tests.*` module that has
an olean, walks the elaborated environment once, and then probes separately the
modules that cannot share an environment with the others.

Those are the executable entry points — each defines `main` at the root
namespace, and two of them in one environment is an import error, not a
measurement.  They are probed one at a time against their own closure, so the
sweep covers the tree rather than the part of it that happens to compose.

    scripts/drop_sweep.py            # the wide walk plus the per-entry-point probes
    scripts/drop_sweep.py --quick    # the wide walk only

The generated Lean lives in `L4YAML/Scratch/` and is removed on the way out;
the numbers go to stdout.  Nothing is edited, so this script is not
destructive — unlike `flip_drop.py`, which deletes the arm for real.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / "L4YAML" / "Scratch"
LIB = ROOT / ".lake" / "build" / "lib" / "lean"
INSTRUMENT = ROOT / "Tests" / "Guards" / "Proofs" / "DropDependents.lean"
DROP = "`L4YAML.Surface.SLYamlStream.scannerDrop"

#: The walk itself lives in `Tests/Guards/Proofs/DropDependents.lean` and is
#: what that file pins against its own, narrower closure.  One implementation,
#: two closures — which is the only way the two numbers can be compared.
WALK_BODY = """
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let c \u2190 Tests.Guards.DropDependents.census
  logInfo m!"WIDE closure={c.closureModules} {Tests.Guards.DropDependents.render c}"
  logInfo m!"WIDE-DIRECT {c.direct}"
  logInfo m!"WIDE-TRANS {c.trans}"
  logInfo m!"WIDE-RAWELIM {c.rawElim}"
"""

ONE = """
open Lean
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let target := (`{mod} : Name)
  let mut hits : Nat := 0
  let mut decls : Nat := 0
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some i =>
      if env.header.moduleNames[i.toNat]! == target then
        decls := decls + 1
        let v := (ci.value? (allowOpaque := true)).getD ci.type
        if (v.getUsedConstants ++ ci.type.getUsedConstants).any
             (· == {drop}) then
          hits := hits + 1
          logInfo m!"HIT {{n}}"
  logInfo m!"MOD {mod} decls={{decls}} dropRefs={{hits}}"
"""


#: A root-namespace `main`.  Two of these in one environment is an import
#: error, so they are held out of the wide walk and probed one at a time.
MAIN = re.compile(r"^\s*(?:unsafe |partial )*def main\b", re.M)


def modules() -> tuple[list[str], list[str], list[str]]:
    """(composable, entry points, no olean).  The third is reported, not dropped:
    a module the sweep cannot read is a hole in it, and a silent skip is how a
    census reports its own reach as a library's."""
    wide, entry, unbuilt = [], [], []
    for p in sorted(list((ROOT / "L4YAML").rglob("*.lean"))
                    + list((ROOT / "Tests").rglob("*.lean"))):
        if "/Scratch/" in str(p):
            continue
        m = str(p.relative_to(ROOT))[:-len(".lean")].replace("/", ".")
        if not (LIB / (m.replace(".", "/") + ".olean")).exists():
            unbuilt.append(m)
            continue
        (entry if MAIN.search(p.read_text()) else wide).append(m)
    return wide, entry, unbuilt


def run(path: Path) -> tuple[int, str]:
    r = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="skip the per-entry-point probes")
    args = ap.parse_args()
    SCRATCH.mkdir(exist_ok=True)
    mods, excluded, unbuilt = modules()
    closure = 0
    for m in unbuilt:
        # No olean and no Lake target: nothing can elaborate it, so it is
        # UNMEASURED rather than clean.  Naming it is the whole obligation —
        # a sweep that skips it silently reports its own reach as the tree's.
        print(f"NO-OLEAN {m} (no Lake target; UNMEASURED by this sweep)")
    walk = SCRATCH / "DropSweep.lean"
    try:
        for _ in range(64):
            walk.write_text("\n".join(f"import {m}" for m in mods) + "\n\n" + WALK_BODY)
            code, out = run(walk)
            m = re.search(r"import ([A-Za-z0-9_.]+) failed|module ([A-Za-z0-9_.]+) "
                          r"does not exist|lean/([A-Za-z0-9_/]+)\.olean', incompatible", out)
            if not m:
                break
            bad = (m.group(1) or m.group(2)
                   or (m.group(3) or "").replace("/", "."))
            excluded.append(bad)
            mods = [x for x in mods if x != bad]
        else:
            sys.exit("the walk never composed; 64 modules refused and that is "
                     "not an import conflict but a broken build")
        if code != 0:
            print(out)
            sys.exit("the walk did not run clean")
        census = ""
        for line in out.splitlines():
            if line.startswith("WIDE"):
                print(line)
                m2 = re.search(r"closure=(\d+)", line)
                if m2:
                    closure = int(m2.group(1))
                # The four counts the whole tree reads.  They are NOT the ones
                # the instrument's own `run_cmd` reads: `census` filters by a
                # declaration's module and a declaration being elaborated has
                # none, so the instrument is blind to its own module and to any
                # module that does not import it (DOCS item 239).  Both numbers
                # are pinned, separately, so neither can move unnoticed.
                m3 = re.search(r"(D=\d+ .*)$", line)
                if m3:
                    census = m3.group(1)
        print(f"WIDE imported={len(mods)} excluded={len(excluded)}")
        if "Tests.Guards.Proofs.DropDependents" not in mods:
            sys.exit("the walk's own module is not in the import list; "
                     "`lake build` it first or this sweep measures nothing")
        if args.quick:
            return 0
        probe = SCRATCH / "DropOne.lean"
        decls = hits = reported = 0
        unreadable: list[str] = []
        for mod in excluded:
            # `Lean.Elab.Command` is what `run_cmd` needs.  Most modules pull
            # it in transitively; `Tests.QueryResults` does not, and without
            # this line its probe fails and contributes a silent zero.
            probe.write_text(f"import {mod}\nimport Lean.Elab.Command\n"
                             + ONE.format(mod=mod, drop=DROP))
            _, o = run(probe)
            if "MOD " not in o:
                # A `lean_exe` that is not a DEFAULT target keeps whatever olean
                # it last got, so `lake build` never refreshes it and a
                # toolchain bump leaves it unreadable for good.  Building it by
                # name is the whole fix, and it is what makes this count the
                # same on a machine that has never seen the old toolchain.
                subprocess.run(["lake", "build", mod], cwd=ROOT,
                               capture_output=True, text=True)
                _, o = run(probe)
            saw = False
            for line in o.splitlines():
                if line.startswith("HIT "):
                    print(line)
                    hits += 1
                elif line.startswith("MOD "):
                    saw = True
                    reported += 1
                    decls += int(line.split("decls=")[1].split()[0])
            if not saw:
                unreadable.append(mod)
                print(f"UNREADABLE {mod} :: "
                      + " ".join(o.splitlines()[:1]))
        wide = (f"closure={closure} imported={len(mods)} "
                f"excluded={len(excluded)} readable={reported} "
                f"unreadable={len(unreadable)} excludedDecls={decls} "
                f"excludedDropRefs={hits}")
        print(f"EXCLUDED modules={len(excluded)} readable={reported} "
              f"unreadable={len(unreadable)} decls={decls} dropRefs={hits}")
        print(f"WIDE-LINE {wide}")
        pinned = re.search(r'def expectedWide : String :=\s*\n?\s*"([^"]*)"',
                           INSTRUMENT.read_text())
        if not pinned:
            sys.exit("no `expectedWide` pin in the instrument to compare "
                     "against; this sweep would report a number nothing holds")
        # Lean's string gap: a trailing `\` swallows the newline and the
        # indentation that follows it.  Without this the comparison reads the
        # source's line break as part of the pinned value and never matches.
        pin = re.sub(r"\\\s*\n\s*", "", pinned.group(1))
        if pin != wide:
            sys.exit(f"the sweep and the instrument disagree:\n"
                     f"  swept  {wide}\n  pinned {pin}")
        pinnedC = re.search(r'def expectedWideCensus : String :=\s*\n?\s*"([^"]*)"',
                            INSTRUMENT.read_text())
        if not pinnedC:
            sys.exit("no `expectedWideCensus` pin in the instrument; the four "
                     "counts the whole tree reads would go unchecked")
        pinC = re.sub(r"\\\s*\n\s*", "", pinnedC.group(1))
        if pinC != census:
            sys.exit(f"the sweep and the instrument disagree on the counts:\n"
                     f"  swept  {census}\n  pinned {pinC}")
        print("WIDE-PIN agrees with Tests/Guards/Proofs/DropDependents.lean")

        for mod in excluded:
            print(f"EXCLUDED-MOD {mod}")
    finally:
        for f in (SCRATCH / "DropSweep.lean", SCRATCH / "DropOne.lean"):
            f.unlink(missing_ok=True)
        if SCRATCH.exists() and not any(SCRATCH.iterdir()):
            SCRATCH.rmdir()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
