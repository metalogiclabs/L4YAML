import Research.R2JointFrames.State
import Lean

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Proofs R2JointFrames

namespace R2MarkedMaps

def checkMaps (s : ScannerState) : Bool :=
  (List.range s.pendingKeys.size).all fun i =>
    if (s.pendingKeys[i]?.getD none).isSome then
      (s.indents[i]?).any fun e => !e.isSequence
    else true

def samples : List String := [
  "", " ", "a\n", "?\n", "? a\n: b\n", "- a\n- b\n",
  "? - ? a\n    : b\n  - c\n: d\n", "? - ? a\n  - c\n: d\n",
  "? ? - a\n    - b\n  : c\n: d\n", "a: [1, {b: 2}]\n",
  "? [a, {b: c}]\n: &d e\n", "a: &x !!str b\n", "? |\n  a\n: b\n",
  "---\na: b\n...\n---\nc: d\n", "%YAML 1.2\n---\na: b\n",
  "- a\n? b\n: c\n", "a:\n  - x\n  ? c\n  : 2\n",
  "? - a\n- c\n: d\n", "? ? a\n  : b\n- c\n: d\n"]

def prefixCheck (fuel : Nat) (s : ScannerState) : Bool :=
  checkMaps s && match fuel with
  | 0 => true
  | f+1 => match scanNextToken s with
    | .ok (some next) => prefixCheck f next
    | _ => true

-- Initial and first two steps, and all available states up to the declared
-- bound. Refusal is not interpreted as acceptance of a complete source.
#guard samples.all fun input =>
  let seed := (ScannerState.mk' input).emit .streamStart
  [0,1,2,128].all fun fuel => prefixCheck fuel seed

def corrupted : ScannerState :=
  { ScannerState.mk' "" with
      indents := #[{column := -1, isSequence := false}, {column := 0, isSequence := true}],
      pendingKeys := #[none, some 0] }
#guard !checkMaps corrupted

#eval IO.println s!"MAP-ADVERSARIAL inputs={samples.length} fuels=0,1,2,128 corrupted_sequence_mark=rejected"

end R2MarkedMaps
