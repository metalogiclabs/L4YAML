#!/usr/bin/env python3
"""Run the `SLYamlStream.scannerDrop` flip gate and report the DEFINITIONS it
breaks (DOCS item 238).

Row 12's β.5 names the deletion of this constructor.  The gate performs the
deletion — docstring and arm together, located by content and not by line
number (item 210's rule) — builds, and reports what stops compiling.

**The count is a LOWER bound and this gate is the weakest of the three.**  Both
construction sites live in `L4YAML/Proofs/Production/StreamAccum.lean`, which
the library root imports, so `lake build` stops there and every module behind
it — including the two `Tests/Guards` instruments that build the same term —
is never attempted.  The proof-term walk in
`Tests/Guards/Proofs/DropDependents.lean` reads the same question off the
elaborated environment in one pass and misses nothing, so here the CHEAP
instrument dominates the expensive one.  The flip is kept because it is the
only one of the two that checks the deletion actually elaborates.

    scripts/flip_drop.py                    # run the gate end to end
    scripts/flip_drop.py --map <build.log>  # just map an existing log

Destructive while it runs — it edits `L4YAML/Surface/Document.lean` in place —
so it restores from its own backup in a `finally` and prints the md5 both
before and after.  A run that dies between the two leaves the backup beside
the source.
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
DOC = ROOT / "L4YAML" / "Surface" / "Document.lean"

#: The arm and the docstring that documents it, anchored on the first words of
#: each and on the arm's own premises.  Anchoring on the text means a re-indent
#: or a docstring rewrite re-aims the gate loudly instead of silently matching
#: the wrong arm.
ARM = re.compile(
    r"\n  /-- Scanner content absorption:.*?"
    r"\n  \| scannerDrop \(s s₁ s₂ s' : SurfPos\) :"
    r"\n      SLYamlStream s s₁ →"
    r"\n      SSLComments s₂ s' →"
    r"\n      SLYamlStream s s'\n",
    re.S)

#: The log mapper is item 210's; one instrument, three gates.
_spec = importlib.util.spec_from_file_location(
    "flip210", Path(__file__).resolve().parent / "flip_210.py")
flip210 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(flip210)


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

    before = md5(DOC)
    print(f"md5 before  {before}")
    src = DOC.read_text()
    hits = ARM.findall(src)
    if len(hits) != 1:
        sys.exit(f"expected exactly one scannerDrop arm in "
                 f"{DOC.relative_to(ROOT)}, found {len(hits)}; the production "
                 "moved and this gate needs re-aiming")
    print("SITES 2  (dropClose and PendingNode.close_with_ssl, both in "
          "L4YAML/Proofs/Production/StreamAccum.lean)")
    backup = DOC.with_suffix(".lean.drop-backup")
    shutil.copy(DOC, backup)
    try:
        DOC.write_text(ARM.sub("\n", src))
        out = subprocess.run(["lake", "build"], cwd=ROOT,
                             capture_output=True, text=True)
        log = out.stdout + out.stderr
        if args.log:
            Path(args.log).write_text(log)
        if out.returncode == 0:
            print("THE FLIP BUILT CLEAN — the arm is already unused, which is "
                  "a finding and not a pass")
            return 1
        bad = flip210.report(log)
        print("LOWER BOUND — the build stopped at the first failing module, "
              "so no definition behind it was attempted")
    finally:
        shutil.copy(backup, DOC)
        backup.unlink()
        after = md5(DOC)
        print(f"md5 after   {after}")
        if after != before:
            sys.exit("the restore did not restore; fix the source before "
                     "trusting anything else in this run")
        print("rebuilding so no later probe reads the flipped oleans...")
        subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
