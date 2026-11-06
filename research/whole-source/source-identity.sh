#!/usr/bin/env bash
# Tracked-input identity only: not cache-free or environment equivalence.
set -euo pipefail
cd -- "$(git rev-parse --show-toplevel)"

compare() {
  local baseline target
  baseline=$(git rev-parse --verify --end-of-options "$1^{tree}")
  target=$(git rev-parse --verify --end-of-options "${2:-HEAD}^{tree}")
  # Fail closed for every tracked path, object, mode and gitlink except these
  # explicit research surfaces. Never exclude all workflows, scripts or docs.
  git diff --exit-code --no-ext-diff --no-textconv --ignore-submodules=none "$baseline" "$target" -- . \
    ':(top,exclude)research/**' \
    ':(top,exclude,literal).github/workflows/accepted-source-slices.yml' \
    ':(top,exclude,literal).github/workflows/quoted-pack-freshness.yml' \
    ':(top,exclude,literal).github/workflows/quoted-production-qualification.yml' \
    ':(top,exclude,literal).github/workflows/structural-boundaries.yml' \
    ':(top,exclude,literal).github/workflows/whole-source-directives.yml'
}

check() {
  compare "$1" HEAD
  # Unlike the baseline comparison, the pre/post working-copy check excludes
  # nothing: the research proofs and qualification infrastructure must not move.
  git -c core.fileMode=true diff --exit-code --no-ext-diff --no-textconv --ignore-submodules=none HEAD -- .
  local status line
  status=$(git submodule status --recursive)
  while IFS= read -r line; do
    if test -n "$line" && test "${line:0:1}" != ' '; then
      printf 'Submodule uninitialized, conflicted or at wrong revision: %s\n' "$line" >&2
      return 1
    fi
  done <<< "$status"
  # Include untracked/ignored content in submodules, not just tracked diffs.
  git submodule foreach --quiet --recursive \
    'status=$(git status --porcelain --untracked-files=all --ignored) || exit 1; test -z "$status" || { echo "Dirty submodule: $displaypath" >&2; exit 1; }' || return 1
}

record() {
  check "$1"
  mkdir -p -- "$2"
  git rev-parse HEAD > "$2/head.txt"
  # Complete Git tree preserves symlink modes and gitlink identities as well as
  # all research/workflow inputs. Submodule status records recursive revisions.
  git ls-tree -r HEAD > "$2/source-tree.txt"
  git submodule status --recursive > "$2/submodule-heads.txt"
  git ls-tree -rz HEAD | while IFS= read -r -d '' entry; do
    metadata=${entry%%$'\t'*}
    path=${entry#*$'\t'}
    read -r mode type object <<< "$metadata"
    if test "$type" = blob; then sha256sum -- "$path"; fi
  done > "$2/source-sha256.txt"
}

verify() {
  check "$1"
  # Same full scope as record; do not silently rebaseline any manifest.
  git rev-parse HEAD | cmp -- "$2/head.txt" -
  git ls-tree -r HEAD | cmp -- "$2/source-tree.txt" -
  git submodule status --recursive | cmp -- "$2/submodule-heads.txt" -
  sha256sum --check "$2/source-sha256.txt" > "$2/source-recheck.txt"
}

case "${1:-}" in
  compare) shift; compare "$@" ;;
  record) shift; record "$@" ;;
  verify) shift; verify "$@" ;;
  *) printf 'Usage: bash source-identity.sh {compare BASE [TREE]|record BASE DIR|verify BASE DIR}\n' >&2; exit 2 ;;
esac
