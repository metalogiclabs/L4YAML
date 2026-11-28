#!/usr/bin/env bash
set -euo pipefail
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2ScannerMapOwnership/reconstruct.sh
task_base="$task_root/verification/map-thread-replay/positive.lean"
printf '%s\n' "6d54f507055cf34c7de5d3250617b0d3798e8cafae90a6f1ed3f61d60edefdd3  $task_base" | sha256sum -c -
task_replay="$task_root/verification/mandatory-migration-replay"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
mkdir -p "$(dirname "$task_source")"
"$R2_LEAN_BIN" --run Research/R2MandatoryContext/Prepare.lean "$task_base" "$task_source" --fund-four
if [ "${1:-}" = --compile ]; then
  : "${R2_MAP_LIB:?Checked scanner ownership modules required}"
  : "${R2_DIAGNOSTIC_LIB:?Original matching accepted 9f1f7bc6 production imports required}"
  export LEAN_PATH="$R2_MAP_LIB:$R2_DIAGNOSTIC_LIB"
  task_exit=0
  (cd "$task_replay"; "$R2_LEAN_BIN" -j1 L4YAML/Proofs/Production/StreamAccum.lean) \
    > Research/R2MandatoryContext/logs/migration-funded.log 2>&1 || task_exit=$?
  printf '%s\n' "$task_exit" > Research/R2MandatoryContext/logs/migration-funded.exit
  test "$task_exit" -eq 1
  xz --compress --stdout Research/R2MandatoryContext/logs/migration-funded.log | base64 -w 76 \
    > Research/R2MandatoryContext/logs/migration-funded.log.xz.b64
  printf 'EXPECTED REJECTION whole migration (read exact labelled residuals)\n'
fi
