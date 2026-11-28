#!/usr/bin/env bash
set -euo pipefail
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
: "${R2_BASE_LIB:?Matching accepted qualified production library required}"
: "${R2_SUPPORT_LIB:?Matching b26c9bfd Research object directory required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_out="$task_root/verification/actual-value-proof-replay"
task_logs="$task_root/Research/R2ActualValueSuppliers/logs"
mkdir -p "$task_out/Research/R2ActualValueSuppliers" "$task_logs"
for task_directory in "$R2_SUPPORT_LIB"/Research/*; do
  task_name=$(basename "$task_directory")
  test "$task_name" != R2ActualValueSuppliers
  ln -sfnT "$task_directory" "$task_out/Research/$task_name"
done
export LEAN_PATH="$task_out:$R2_BASE_LIB"
for task_module in Controls Producers First Unkeyed Witness Audit; do
  task_exit=0
  "$R2_LEAN_BIN" -j1 -o "$task_out/Research/R2ActualValueSuppliers/$task_module.olean" \
    "Research/R2ActualValueSuppliers/$task_module.lean" > "$task_logs/$task_module.log" 2>&1 || task_exit=$?
  printf '%s\n' "$task_exit" > "$task_logs/$task_module.exit"
  if [ "$task_exit" -ne 0 ]; then
    rm -f "$task_out/Research/R2ActualValueSuppliers/$task_module.olean"
    printf 'FAILED %s\n' "$task_module"
    exit "$task_exit"
  fi
  printf 'CHECKED %s\n' "$task_module"
done
task_exit=0
"$R2_LEAN_BIN" -j1 Research/R2ActualValueSuppliers/ErasedReader.lean > "$task_logs/ErasedReader.log" 2>&1 || task_exit=$?
printf '%s\n' "$task_exit" > "$task_logs/ErasedReader.exit"
test "$task_exit" -eq 1
test "$(rg -c ': error:' "$task_logs/ErasedReader.log")" -eq 1
printf 'EXPECTED REJECTION actual same-map context reader\n'
for task_log in "$task_logs"/*.log; do
  xz --compress --stdout "$task_log" | base64 -w 76 > "$task_log.xz.b64"
done
