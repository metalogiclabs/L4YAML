import Research.R2SequenceContext.Controls

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness

namespace R2CompletionControls

def firstScalar (input : String) : Option ScannerState :=
  let rec go (s : ScannerState) (fuel : Nat) : Option ScannerState :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match scanNextToken s with
      | .ok (some next) =>
        if next.tokens.size > s.tokens.size && next.tokens.back?.any (fun t =>
          match t.val with | .scalar .. => true | _ => false)
        then some next else go next fuel
      | _ => none
  go ((ScannerState.mk' input).emit .streamStart) ((input.utf8ByteSize + 1) * 4)

def scalarState (input : String) : ScannerState :=
  (firstScalar input).getD (ScannerState.mk' input)

def plain : String := "? - a\n  - b\n: c\n"
def anchored : String := "? - &p a\n  - b\n: c\n"
def taggedAnchored : String := "? - !foo &p a\n  - b\n: c\n"
def anchoredTagged : String := "? - &p !foo a\n  - b\n: c\n"
def blockScalar : String := "? - |\n    a\n  - b\n: c\n"
def multiline : String := "? - \"a\n    b\"\n  - c\n: d\n"

example : (firstScalar "").isNone := by decide +kernel
example : (firstScalar plain).isSome = true := by decide +kernel
lemma plainMarks : markedCols (scalarState plain) = [0] := by decide +kernel
example : (scalarState plain).offset = 5 ∧ (scalarState plain).col = 5 := by decide +kernel
example : markedCols (scalarState anchored) = [0] := by decide +kernel
example : markedCols (scalarState taggedAnchored) = [0] := by decide +kernel
example : markedCols (scalarState anchoredTagged) = [0] := by decide +kernel
example : markedCols (scalarState blockScalar) = [0] := by decide +kernel
example : markedCols (scalarState multiline) = [0] := by decide +kernel

#guard (L4YAML.TokenParser.parseYaml plain).isOk
#guard (L4YAML.TokenParser.parseYaml anchored).isOk
#guard (L4YAML.TokenParser.parseYaml taggedAnchored).isOk
#guard (L4YAML.TokenParser.parseYaml anchoredTagged).isOk
#guard (L4YAML.TokenParser.parseYaml blockScalar).isOk
#guard (L4YAML.TokenParser.parseYaml multiline).isOk

end R2CompletionControls
