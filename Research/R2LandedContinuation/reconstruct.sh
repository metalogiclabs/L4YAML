#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
mkdir -p verification
bash Research/R2ContinuationContract/reconstruct.sh > verification/landed-parent-reconstruction.log
task_replay="$task_root/verification/diagnostic-replay"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
cp verification/sources/marked-pair.lean "$task_source"
patch -s -p1 -d "$task_replay" < Research/R2LandedContinuation/landed-family.patch
cp "$task_source" verification/sources/landed-positive.lean
patch -s -p1 -d "$task_replay" < Research/R2LandedContinuation/erased-family.patch
cp "$task_source" verification/sources/landed-erased.lean
sha256sum -c Research/R2LandedContinuation/SOURCES.sha256

if [ "${1:-}" = --compile ]; then
  : "${R2_BASE_LIB:?Set R2_BASE_LIB to the matching original accepted library}"
  : "${R2_LEAN_BIN:?Set R2_LEAN_BIN to the pinned Lean binary}"
  export LEAN_PATH="$R2_BASE_LIB"
  for task_variant in positive erased; do
    cp "verification/sources/landed-$task_variant.lean" "$task_source"
    if (cd "$task_replay" && "$R2_LEAN_BIN" L4YAML/Proofs/Production/StreamAccum.lean) \
        > "Research/R2LandedContinuation/logs/producer-$task_variant.log" 2>&1; then
      task_status=0
    else
      task_status=$?
    fi
    printf '%s\n' "$task_status" > "Research/R2LandedContinuation/logs/producer-$task_variant.exit"
    test "$task_status" -eq 1
  done
fi
