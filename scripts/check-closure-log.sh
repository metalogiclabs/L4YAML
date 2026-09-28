#!/usr/bin/env bash
# CI gate: DOCS.md's β.5 closure log ascends, does not regress in date, and
# declares its gaps (see scripts/check_closure_log.py).  Complements
# check-reflection-index.sh, which gates the Reflections narrative index.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 scripts/check_closure_log.py
