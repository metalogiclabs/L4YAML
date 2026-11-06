#!/usr/bin/env bash
# Real-Git regressions: a narrowed input selection or unchecked submodule must fail.
set -euo pipefail
helper="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/source-identity.sh"
fixture=$(mktemp -d)
trap 'rm -r -- "$fixture"' EXIT
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null
export GIT_AUTHOR_NAME=fixture GIT_AUTHOR_EMAIL=fixture@example.invalid
export GIT_COMMITTER_NAME=fixture GIT_COMMITTER_EMAIL=fixture@example.invalid
git init -q "$fixture/sub"
printf 'suite one\n' > "$fixture/sub/case.yaml"
git -C "$fixture/sub" add .
git -C "$fixture/sub" commit -qm first
suite_one=$(git -C "$fixture/sub" rev-parse HEAD)
printf 'suite two\n' > "$fixture/sub/case.yaml"
git -C "$fixture/sub" commit -qam second
suite_two=$(git -C "$fixture/sub" rev-parse HEAD)
git init -q "$fixture/main"
cd "$fixture/main"
mkdir -p L4YAML Tests Scripts Demo tools scripts Blueprint research/whole-source .github/workflows
for path in L4YAML/Input.lean Tests/Input.lean Scripts/Input.lean lakefile.lean lean-toolchain lake-manifest.json L4YAML.lean Scripts.lean Demo.lean Demo/Input.lean tools/CollectStats.lean scripts/capstones.txt DOCS.md Blueprint/04-capstones.md research/whole-source/Proof.lean .github/workflows/test-coverage.yml; do
  printf 'original\n' > "$path"
done
for name in accepted-source-slices quoted-pack-freshness quoted-production-qualification structural-boundaries whole-source-directives; do
  printf 'original\n' > ".github/workflows/$name.yml"
done
git -c protocol.file.allow=always submodule add -q "$fixture/sub" yaml-test-suite
git -C yaml-test-suite checkout -q --detach "$suite_one"
git add .
git commit -qm baseline
baseline=$(git rev-parse HEAD)
changed=$(printf 'changed\n' | git hash-object -w --stdin)
tree_with() {
  git read-tree "$baseline"
  git update-index --add --cacheinfo "$1" "$2" "$3"
  git write-tree
}
expect() {
  local want=$1 label=$2 status=0
  shift 2
  "$@" > "$fixture/output" 2>&1 || status=$?
  if test "$status" != "$want"; then
    printf 'FAIL %s: expected exit %s, got %s\n' "$label" "$want" "$status"
    cat "$fixture/output"
    exit 1
  fi
  printf 'PASS %s (exit %s)\n' "$label" "$status"
}
if test "${1:-}" = --old-guard; then
  candidate=$(tree_with 100644 "$changed" L4YAML.lean)
  # Exact baseline workflow selection: the forbidden root change is invisible.
  expect 1 'old narrow guard must reject root input' git diff --quiet "$baseline" "$candidate" -- L4YAML Tests Scripts lakefile.lean lean-toolchain lake-manifest.json
  exit 0
fi
expect 0 same-baseline bash "$helper" compare "$baseline" "$baseline"
candidate=$(tree_with 100644 "$changed" research/whole-source/Proof.lean)
expect 0 research-only bash "$helper" compare "$baseline" "$candidate"
for name in accepted-source-slices quoted-pack-freshness quoted-production-qualification structural-boundaries whole-source-directives; do
  candidate=$(tree_with 100644 "$changed" ".github/workflows/$name.yml")
  expect 0 "named-workflow-only:$name" bash "$helper" compare "$baseline" "$candidate"
done
for path in L4YAML.lean Scripts.lean Demo.lean Demo/Input.lean tools/CollectStats.lean scripts/capstones.txt DOCS.md Blueprint/04-capstones.md .gitmodules L4YAML/Input.lean Tests/Input.lean Scripts/Input.lean .github/workflows/test-coverage.yml new-input.txt; do
  candidate=$(tree_with 100644 "$changed" "$path")
  expect 1 "reject:$path" bash "$helper" compare "$baseline" "$candidate"
done
git read-tree "$baseline"
git update-index --cacheinfo 100644 "$changed" research/whole-source/Proof.lean
git update-index --cacheinfo 100644 "$changed" L4YAML.lean
candidate=$(git write-tree)
expect 1 reject-mixed-research-and-root bash "$helper" compare "$baseline" "$candidate"
expect 1 reject-root-change-from-nested-cwd bash -c 'cd research/whole-source; bash "$1" compare "$2" "$3"' _ "$helper" "$baseline" "$candidate"
candidate=$(tree_with 160000 "$suite_two" yaml-test-suite)
expect 1 reject-gitlink bash "$helper" compare "$baseline" "$candidate"
original=$(git rev-parse "$baseline:tools/CollectStats.lean")
candidate=$(tree_with 100755 "$original" tools/CollectStats.lean)
expect 1 reject-mode-change bash "$helper" compare "$baseline" "$candidate"
link=$(printf 'L4YAML.lean' | git hash-object -w --stdin)
candidate=$(tree_with 120000 "$link" tools/CollectStats.lean)
expect 1 reject-type-change bash "$helper" compare "$baseline" "$candidate"
git read-tree "$baseline"
git update-index --force-remove DOCS.md
candidate=$(git write-tree)
expect 1 reject-deletion bash "$helper" compare "$baseline" "$candidate"
git read-tree "$baseline"
expect 0 record-clean-initialized-submodule bash "$helper" record "$baseline" "$fixture/evidence"
expect 0 verify-clean-initialized-submodule bash "$helper" verify "$baseline" "$fixture/evidence"
printf 'dirty\n' > yaml-test-suite/case.yaml
expect 1 reject-dirty-submodule bash "$helper" verify "$baseline" "$fixture/evidence"
git -C yaml-test-suite add case.yaml
expect 1 reject-staged-submodule bash "$helper" record "$baseline" "$fixture/dirty-evidence"
git -C yaml-test-suite read-tree "$suite_one"
printf 'suite one\n' > yaml-test-suite/case.yaml
printf 'extra\n' > yaml-test-suite/untracked.yaml
expect 1 reject-untracked-submodule bash "$helper" verify "$baseline" "$fixture/evidence"
rm -- yaml-test-suite/untracked.yaml
printf 'ignored.yaml\n' >> "$(git -C yaml-test-suite rev-parse --absolute-git-dir)/info/exclude"
printf 'extra\n' > yaml-test-suite/ignored.yaml
expect 1 reject-ignored-submodule-content bash "$helper" verify "$baseline" "$fixture/evidence"
rm -- yaml-test-suite/ignored.yaml
git -C yaml-test-suite checkout -q --detach "$suite_two"
expect 1 reject-wrong-submodule-revision bash "$helper" verify "$baseline" "$fixture/evidence"
git -C yaml-test-suite checkout -q --detach "$suite_one"
printf 'dirty\n' > L4YAML.lean
expect 1 reject-dirty-root-input bash "$helper" verify "$baseline" "$fixture/evidence"
printf 'original\n' > L4YAML.lean
chmod +x L4YAML.lean
expect 1 reject-working-mode-change bash "$helper" verify "$baseline" "$fixture/evidence"
chmod -x L4YAML.lean
printf 'dirty\n' > research/whole-source/Proof.lean
expect 1 reject-mutated-research-input bash "$helper" verify "$baseline" "$fixture/evidence"
printf 'original\n' > research/whole-source/Proof.lean
printf 'corrupt\n' > "$fixture/evidence/source-tree.txt"
expect 1 reject-changed-manifest bash "$helper" verify "$baseline" "$fixture/evidence"
expect 0 rerecord-clean bash "$helper" record "$baseline" "$fixture/evidence"
git -c protocol.file.allow=always submodule deinit -q yaml-test-suite
expect 1 reject-uninitialized-submodule bash "$helper" record "$baseline" "$fixture/uninitialized-evidence"
expect 128 reject-unknown-baseline bash "$helper" compare not-a-revision HEAD
printf 'All full-input identity controls passed.\n'
