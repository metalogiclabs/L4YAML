#!/usr/bin/env bash
set -euo pipefail
: "${R2_ACCEPTED_LIB:?Original matching accepted production library is required}"
: "${R2_BASE_LIB:?Qualified #392 library with the existing census instruments is required}"
: "${R2_MAP_LIB:?Checked new research modules from replay-proofs.sh are required}"
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary is required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2ScannerMapOwnership/reconstruct-accepted.sh
task_replay="$task_root/verification/map-accepted-replay"
task_objects="$task_replay/objects"
mkdir -p "$task_objects/L4YAML/Proofs/Production"
cp -as --no-clobber "$R2_ACCEPTED_LIB/." "$task_objects/"
for task_module in StreamAccum DocumentProduction; do
  for task_old in "$task_objects/L4YAML/Proofs/Production/$task_module".*; do
    rm -f "$task_old"
  done
done
export LEAN_PATH="$R2_MAP_LIB:$task_objects:$R2_BASE_LIB"
cp "$task_replay/sources/accepted.lean" "$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
(cd "$task_replay"
  "$R2_LEAN_BIN" -j1 -o "$task_objects/L4YAML/Proofs/Production/StreamAccum.olean" \
    L4YAML/Proofs/Production/StreamAccum.lean) > "$task_replay/stream.log" 2>&1
"$R2_LEAN_BIN" -j1 -o "$task_objects/L4YAML/Proofs/Production/DocumentProduction.olean" \
  L4YAML/Proofs/Production/DocumentProduction.lean > "$task_replay/document.log" 2>&1
R2_MAP_EXPECT_WIRED=1 R2_MAP_AUDIT_OUTPUT="$task_replay/actual.json" \
  "$R2_LEAN_BIN" -j1 Research/R2ScannerMapOwnership/AcceptedAudit.lean > "$task_replay/audit-actual.log" 2>&1
R2_MAP_CENSUS_OUTPUT="$task_replay/census-actual.json" \
  "$R2_LEAN_BIN" -j1 Research/R2ScannerMapOwnership/Census.lean > "$task_replay/census-actual.log" 2>&1
export LEAN_PATH="$R2_ACCEPTED_LIB:$R2_BASE_LIB"
R2_MAP_EXPECT_WIRED=0 R2_MAP_AUDIT_OUTPUT="$task_replay/baseline.json" \
  "$R2_LEAN_BIN" -j1 Research/R2ScannerMapOwnership/AcceptedAudit.lean > "$task_replay/audit-baseline.log" 2>&1
R2_MAP_CENSUS_OUTPUT="$task_replay/census-baseline.json" \
  "$R2_LEAN_BIN" -j1 Research/R2ScannerMapOwnership/Census.lean > "$task_replay/census-baseline.log" 2>&1
export LEAN_PATH="$R2_MAP_LIB:$R2_ACCEPTED_LIB:$R2_BASE_LIB"
cp "$task_replay/sources/erased-step.lean" "$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
if (cd "$task_replay"
    "$R2_LEAN_BIN" -j1 L4YAML/Proofs/Production/StreamAccum.lean) \
    > "$task_replay/erased-step.log" 2>&1; then task_status=0; else task_status=$?; fi
test "$task_status" -eq 1
if "$R2_LEAN_BIN" -j1 "$task_replay/JointWitness.lean" > "$task_replay/erased-joint.log" 2>&1; then
  task_status=0
else task_status=$?; fi
test "$task_status" -eq 1
printf 'CONNECTED-REPLAY accepted_modules=2 expected_erasure_rejections=2\n'
