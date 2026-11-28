#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2ContinuationContract/reconstruct.sh
task_replay="$task_root/verification/unmarked-reconstruction"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
task_sources="$task_replay/sources"
mkdir -p "$(dirname "$task_source")" "$task_sources"
cp verification/sources/marked-pair.lean "$task_source"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2UnmarkedOwner/unmarked-owner.patch
cp "$task_source" "$task_sources/paired.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean Research/R2UnmarkedOwner/ProducerAudit.inc.lean > "$task_sources/paired-audited.lean"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2UnmarkedOwner/colon-composition.patch
cp "$task_source" "$task_sources/composed.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean Research/R2UnmarkedOwner/ProducerAudit.inc.lean > "$task_sources/composed-audited.lean"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2LandedContinuation/landed-family.patch
cp "$task_source" "$task_sources/integrated.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean Research/R2UnmarkedOwner/ProducerAudit.inc.lean Research/R2UnmarkedOwner/CompositionAudit.inc.lean > "$task_sources/integrated-audited.lean"
cp "$task_sources/paired.lean" "$task_source"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2UnmarkedOwner/erased-reader.patch
cp "$task_source" "$task_sources/erased-reader.lean"
sha256sum -c Research/R2UnmarkedOwner/SOURCES.sha256

if [ "${1:-}" = --compile ]; then
  : "${R2_BASE_LIB:?Matching original accepted library required}"
  : "${R2_LEAN_BIN:?Pinned Lean binary required}"
  export LEAN_PATH="$R2_BASE_LIB"
  for task_variant in paired-audited composed-audited integrated-audited erased-reader; do
    cp "$task_sources/$task_variant.lean" "$task_source"
    if "$R2_LEAN_BIN" "$task_source" > "$task_replay/$task_variant.log" 2>&1; then task_status=0; else task_status=$?; fi
    printf '%s exit=%s\n' "$task_variant" "$task_status"
    test "$task_status" -eq 1
  done
fi
