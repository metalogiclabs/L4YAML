#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2CloseValueFamily/reconstruct.sh
task_replay="$task_root/verification/map-thread-replay"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
mkdir -p "$(dirname "$task_source")"
cp verification/close-family-replay/sources/positive.lean "$task_source"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2ScannerMapOwnership/map-thread.patch
cp "$task_source" "$task_replay/positive.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean \
  Research/R2UnmarkedOwner/ProducerAudit.inc.lean \
  Research/R2UnmarkedOwner/CompositionAudit.inc.lean \
  Research/R2CloseValueFamily/ProductionAudit.inc.lean \
  Research/R2ScannerMapOwnership/ThreadAudit.inc.lean > "$task_replay/audited.lean"
sha256sum -c Research/R2ScannerMapOwnership/SOURCES.sha256
if [ "${1:-}" = --compile ]; then
  : "${R2_BASE_LIB:?Original matching accepted library is required}"
  : "${R2_MAP_LIB:?Checked scanner ownership modules are required}"
  : "${R2_LEAN_BIN:?Pinned Lean binary is required}"
  export LEAN_PATH="$R2_MAP_LIB:$R2_BASE_LIB"
  for task_variant in positive audited; do
    cp "$task_replay/$task_variant.lean" "$task_source"
    if (cd "$task_replay" && "$R2_LEAN_BIN" -j1 L4YAML/Proofs/Production/StreamAccum.lean) \
        > "$task_replay/$task_variant.log" 2>&1; then task_status=0; else task_status=$?; fi
    printf '%s exit=%s\n' "$task_variant" "$task_status"
    test "$task_status" -eq 1
  done
fi
