#!/usr/bin/env bash
# CI gate: the Reflections narrative index describes itself accurately
# (see scripts/check_reflection_index.py).  Complements check-import-closure.sh,
# which gates the index's `import` half.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 scripts/check_reflection_index.py
