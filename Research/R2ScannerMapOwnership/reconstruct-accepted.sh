#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_replay="$task_root/verification/map-accepted-replay"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
mkdir -p "$(dirname "$task_source")" "$task_replay/sources"
cp L4YAML/Proofs/Production/StreamAccum.lean "$task_source"
printf '%s\n' 'f1eece1acca9f124666aa8fcc8fe5b591c316df35b292b32ed28af491a25772a  L4YAML/Proofs/Production/StreamAccum.lean' | sha256sum -c -
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2ScannerMapOwnership/accepted-loop.patch
cp "$task_source" "$task_replay/sources/accepted.lean"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2ScannerMapOwnership/erased-step.patch
cp "$task_source" "$task_replay/sources/erased-step.lean"
cp Research/R2ScannerMapOwnership/JointWitness.lean "$task_replay/JointWitness.lean"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2ScannerMapOwnership/erased-joint-reader.patch
sha256sum -c Research/R2ScannerMapOwnership/ACCEPTED-SOURCES.sha256
