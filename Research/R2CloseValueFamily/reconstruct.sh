#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2UnmarkedOwner/reconstruct.sh
task_replay="$task_root/verification/close-family-replay"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
task_sources="$task_replay/sources"
mkdir -p "$(dirname "$task_source")" "$task_sources"
cp verification/unmarked-reconstruction/sources/integrated.lean "$task_source"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2CloseValueFamily/close-family.patch
cp "$task_source" "$task_sources/positive.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean \
  Research/R2UnmarkedOwner/ProducerAudit.inc.lean \
  Research/R2UnmarkedOwner/CompositionAudit.inc.lean \
  Research/R2CloseValueFamily/ProductionAudit.inc.lean > "$task_sources/audited.lean"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2CloseValueFamily/erased-reader.patch
cp "$task_source" "$task_sources/erased-reader.lean"
for task_phase in initial funded-draft; do
  cp "$task_sources/positive.lean" "$task_source"
  patch --fuzz=0 -s -p1 -d "$task_replay" < "Research/R2CloseValueFamily/lineage/$task_phase-from-positive.patch"
  cp "$task_source" "$task_sources/$task_phase.lean"
done
cp "$task_sources/audited.lean" "$task_source"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2CloseValueFamily/lineage/audited-v1-from-final.patch
cp "$task_source" "$task_sources/audited-v1.lean"
sha256sum -c Research/R2CloseValueFamily/SOURCES.sha256

if [ "${1:-}" = --compile ]; then
  : "${R2_BASE_LIB:?Original matching accepted library is required}"
  : "${R2_LEAN_BIN:?Pinned Lean binary is required}"
  export LEAN_PATH="$R2_BASE_LIB"
  for task_variant in positive audited erased-reader; do
    cp "$task_sources/$task_variant.lean" "$task_source"
    if (cd "$task_replay" && "$R2_LEAN_BIN" -j1 L4YAML/Proofs/Production/StreamAccum.lean) \
        > "$task_replay/$task_variant.log" 2>&1; then task_status=0; else task_status=$?; fi
    printf '%s exit=%s\n' "$task_variant" "$task_status"
    test "$task_status" -eq 1
  done
fi
