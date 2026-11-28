#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2ContinuationContract/reconstruct.sh
task_replay="$task_root/verification/colon-supplier-diagnostic"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
task_sources="$task_root/verification/colon-supplier-sources"
mkdir -p "$(dirname "$task_source")" "$task_sources"
cp verification/sources/audited-positive.lean "$task_source"
patch -s -p1 -d "$task_replay" < Research/R2ColonSupplier/integration.patch
cp "$task_source" "$task_sources/integrated.lean"
{
  cat "$task_source"
  printf '\nprivate def r2SupplierExpectedFunded : Bool := false\n'
  cat Research/R2ColonSupplier/ProductionAudit.inc.lean
} > "$task_sources/integrated-audited.lean"
patch -s -p1 -d "$task_replay" < Research/R2ColonSupplier/supplied-callers.patch
cp "$task_source" "$task_sources/supplied-audited.lean"
patch -s -p1 -d "$task_replay" < Research/R2ColonSupplier/owner-from-cover-negative.patch
cp "$task_source" "$task_sources/negative.lean"
sha256sum -c Research/R2ColonSupplier/SOURCES.sha256

if [ "${1:-}" = --compile ]; then
  : "${R2_BASE_LIB:?Set R2_BASE_LIB to the matching accepted library}"
  : "${R2_LEAN_BIN:?Set R2_LEAN_BIN to the pinned Lean 4.36.0 binary}"
  export LEAN_PATH="$R2_BASE_LIB"
  for task_variant in integrated-audited supplied-audited negative; do
    cp "$task_sources/$task_variant.lean" "$task_source"
    if (cd "$task_replay" && "$R2_LEAN_BIN" L4YAML/Proofs/Production/StreamAccum.lean) \
        > "$task_sources/$task_variant.log" 2>&1; then
      task_exit=0
    else
      task_exit=$?
    fi
    printf '%s exit=%s\n' "$task_variant" "$task_exit"
    test "$task_exit" -eq 1
  done
fi
