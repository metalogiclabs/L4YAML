#!/usr/bin/env python3
"""Give `BlockStack` a second arm and report what stops typechecking (DOCS item 246).

The three standing flips tighten or delete a PRODUCTION and `flip_supplier.py`
changes a lemma's TYPE.  This one ADDS A CONSTRUCTOR to a carrier, which is a
third edge: nothing that builds `BlockStack.nil` or states `BlockStack sp sp'`
moves, and what breaks is every proof that case-splits on the carrier and was
total on `nil` alone — item 127 measured the same two matches from the other
direction, by deleting the old arms.

    arm     `BlockStack` gains `seqEntryOpen`: `s-indent(n)` and the `-`
            scanned, `s-l+block-indented` awaited — `SBlockSeqEntries.single`'s
            first two premises, held at the frame's end the way
            `SeqFrame.midQuestion` holds its `?`.  The edge traveled is the
            carrier's READERS, the case splits.
    retire  the arm added AND both absorptions (`absorb_stacks`,
            `absorb_stacksB`) deleted.  With the arm both are FALSE as stated
            — a stream cannot absorb an open entry — so their repair is a
            restatement and the edge traveled is the ABSORPTIONS' readers: the
            second wave, reported beside `arm` and not as a point of a
            lattice.

Which entry the arm opens does not change the count — any non-reflexive arm
breaks the same total matches — so the arm's CONTENT is judged elsewhere:
`Tests/Guards/Proofs/CarrierArmPrice.lean` §1 grades it by the connectivity of
its premises, against the mandate's failure mode (an arm relating two
positions its premises do not connect is `scannerDrop` under another name).

**What the count is.**  Both ends leave a well-typed carrier behind, so every
error is a proof that no longer elaborates.  Both counts are LOWER BOUNDS in
the flips' standing sense — the build stops at the first failing module, so a
reader outside `StreamAccum` is never attempted — and the guard's §2/§3 are
the complete sets, environment-resolved.  This script checks each end's
`StreamAccum` breakage against the lists the guard pins, so "the flip agrees
with the census" is a reading rather than two numbers that happen to match.

    scripts/flip_carrier.py                 # both ends
    scripts/flip_carrier.py --end arm       # one end
    scripts/flip_carrier.py --map <log>     # just map an existing log

Destructive while it runs — it edits `L4YAML/Proofs/Production/StreamAccum.lean`
in place — so each end restores from its own backup in a `finally` and prints
the md5 both before and after.  A run that dies between the two leaves the
backup beside the source.
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
GUARD = ROOT / "Tests" / "Guards" / "Proofs" / "CarrierArmPrice.lean"
MOD = "L4YAML.Proofs.StreamAccum."

#: The log mapper is item 210's; one instrument, six gates.
_spec = importlib.util.spec_from_file_location(
    "flip210", Path(__file__).resolve().parent / "flip_210.py")
flip210 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(flip210)

# ---------------------------------------------------------------------------
# The anchors.  Every one is located by CONTENT (item 210's rule): a re-indent
# or a docstring rewrite re-aims the gate loudly instead of matching silently.
# ---------------------------------------------------------------------------

#: The carrier, whole.
CARRIER = ("inductive BlockStack : SurfPos → SurfPos → Prop where\n"
           "  /-- No active block collections. At document level or stream start. -/\n"
           "  | nil (sp : SurfPos) : BlockStack sp sp\n")

#: The arm, verbatim the guard's `BlockStackOpen.seqEntryOpen`.
ARM = ("  /-- FLIP (scripts/flip_carrier.py): a block sequence entry OPENED at\n"
       "      indentation `n` — `s-indent(n)` and the `-` scanned,\n"
       "      `s-l+block-indented` awaited. -/\n"
       "  | seqEntryOpen (n : Nat) (sp sp_i sp' : SurfPos)\n"
       "      (hind : SIndent n sp sp_i) (hdash : GLit '-' sp_i sp') : BlockStack sp sp'\n")

#: The two absorptions, docstring and proof together.
ABSORB = ("/-- Absorb both markers into the stream: three coincident positions, so the\n"
          "    incoming stream IS the outgoing one. -/\n"
          "lemma absorb_stacks (sp_start sp_gram sp_block sp_flow : SurfPos)\n"
          "    (h_stream : SLYamlStream sp_start sp_gram)\n"
          "    (h_stack : BlockStack sp_gram sp_block)\n"
          "    (h_flow : FlowStack sp_block sp_flow) : SLYamlStream sp_start sp_flow := by\n"
          "  cases h_flow with\n"
          "  | nil => cases h_stack with\n"
          "    | nil => exact h_stream\n")

ABSORB_B = ("/-- Absorb the block marker + a CLOSED (`nil`, depth 0) `FlowStackB` into the\n"
            "    stream.  The `open` case is vacuous at depth 0 (`FlowOpenStack` has positive\n"
            "    depth). -/\n"
            "lemma absorb_stacksB {g : Option ScannerState} (sp_start sp_gram sp_block sp_flow : SurfPos)\n"
            "    (h_stream : SLYamlStream sp_start sp_gram)\n"
            "    (h_stack : BlockStack sp_gram sp_block)\n"
            "    {n : Nat} {ks km : Array Bool} {kc : Nat} {tl : FrameTail}\n"
            "    (h_flow : FlowStackB sp_start n kc g 0 ks km tl sp_block sp_flow) : SLYamlStream sp_start sp_flow := by\n"
            "  cases h_flow with\n"
            "  | nil => cases h_stack with\n"
            "    | nil => exact h_stream\n"
            "  | «open» _ _ _ _ _ _ h => exact absurd (FlowOpenStack_depth_pos h) (by omega)\n")


def _sub1(src: str, old: str, new: str) -> str:
    n = src.count(old)
    if n != 1:
        sys.exit(f"expected exactly one occurrence of\n---\n{old}---\nin "
                 f"{SRC.relative_to(ROOT)}, found {n}; the text moved and "
                 "this gate needs re-aiming")
    return src.replace(old, new)


def _edit_arm(src: str) -> str:
    return _sub1(src, CARRIER, CARRIER + ARM)


def _edit_retire(src: str) -> str:
    src = _edit_arm(src)
    src = _sub1(src, ABSORB, "")
    return _sub1(src, ABSORB_B, "")


ENDS = {
    "arm": (_edit_arm,
            "BlockStack gains an arm — the edge is the carrier's READERS"),
    "retire": (_edit_retire,
               "the arm added and both absorptions deleted — the edge is the "
               "ABSORPTIONS' readers, the second wave"),
}


def md5(path: Path) -> str:
    return hashlib.md5(path.read_bytes()).hexdigest()


def carrier_errors(flipped: str, log: str) -> int:
    """Errors inside the carrier's own declaration: an arm that does not
    elaborate would break everything and measure nothing."""
    lines = flipped.split("\n")
    start = next(i for i, l in enumerate(lines) if l.startswith("inductive BlockStack"))
    end = next(i for i in range(start + 1, len(lines)) if lines[i] == "")
    rel = str(SRC.relative_to(ROOT))
    return sum(1 for m in flip210.ERROR_LOC.finditer(log)
               if m.group(1) == rel and start < int(m.group(2)) <= end)


def pinned(name: str) -> set[str]:
    """The `StreamAccum` subset of a list the guard pins, as source names."""
    src = GUARD.read_text()
    m = re.search(rf"def {name} : List String :=\n((?:  .*\n)+?)\n", src)
    if not m:
        sys.exit(f"{GUARD.relative_to(ROOT)} no longer pins `{name}`; this gate "
                 "needs re-aiming")
    names = re.findall(r'"([^"]+)"', m.group(1))
    return {n[len(MOD):] for n in names if n.startswith(MOD)}


def expected(end: str) -> set[str]:
    readers = pinned("expectedReaders")
    if end == "arm":
        return readers
    absorptions = {"absorb_stacks", "absorb_stacksB"}
    return (readers - absorptions) | pinned("expectedAbsorbReaders")


def run_end(name: str, log_dir: Path | None) -> int | None:
    edit, blurb = ENDS[name]
    print(f"=== END {name}: {blurb} ===")
    before = md5(SRC)
    print(f"md5 before  {before}")
    src = SRC.read_text()
    backup = SRC.with_suffix(f".lean.carrier-{name}-backup")
    shutil.copy(SRC, backup)
    count = None
    try:
        flipped = edit(src)
        SRC.write_text(flipped)
        out = subprocess.run(["lake", "build"], cwd=ROOT,
                             capture_output=True, text=True)
        log = out.stdout + out.stderr
        if log_dir:
            (log_dir / f"flip.carrier.{name}.log").write_text(log)
        n_car = carrier_errors(flipped, log)
        print(f"CARRIER errors={n_car}"
              + ("  — the arm ELABORATES, so every error below is a reader's"
                 if n_car == 0 else
                 "  — THE ARM ITSELF DOES NOT ELABORATE; the count below "
                 "measures nothing"))
        if out.returncode == 0:
            print("THE FLIP BUILT CLEAN — the carrier has no reader, which is "
                  "a finding and not a pass")
            count = 0
            got: set[str] = set()
        else:
            defs, nlocs, complaints = flip210.broken_definitions(log)
            for d in defs:
                print(f"BROKEN {d}")
            for c in complaints:
                print(f"UNMAPPED {c}")
            print(f"COUNT {len(defs)} definitions from {nlocs} locations")
            print("LOWER BOUND — the build stopped at the first failing "
                  "module, so no definition behind it was attempted")
            count = len(defs)
            got = set(defs)
        want = expected(name)
        if got == want:
            print(f"CARRIER-PIN agrees with {GUARD.relative_to(ROOT)} "
                  f"({len(want)} StreamAccum names)")
        else:
            print(f"CARRIER-PIN DISAGREES with {GUARD.relative_to(ROOT)}: "
                  f"flip-only {sorted(got - want)} census-only {sorted(want - got)}")
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
    return count


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--end", choices=[*ENDS, "all"], default="all")
    ap.add_argument("--map", metavar="LOG",
                    help="map an existing build log instead of running the gate")
    ap.add_argument("--log-dir", metavar="DIR", help="write the build logs here")
    args = ap.parse_args()

    if args.map:
        return 1 if flip210.report(Path(args.map).read_text()) else 0

    log_dir = Path(args.log_dir) if args.log_dir else None
    names = list(ENDS) if args.end == "all" else [args.end]
    counts = {n: run_end(n, log_dir) for n in names}
    if len(counts) > 1:
        print("CARRIER " + "  ".join(f"{n}={c}" for n, c in counts.items()))
        print("Two waves of one edge, not a ratio: `arm` is what the carrier's "
              "own readers cost, `retire` is what those readers' readers cost "
              "once the readers cannot be repaired in place.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
