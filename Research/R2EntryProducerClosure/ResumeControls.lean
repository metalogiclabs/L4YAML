import L4YAML.Parser.Composition
import L4YAML.Proofs.Scanner.RegisterWitness

open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.RegisterWitness

def resumeInputs : List (String × String) := [
  ("sibling-question", "?\n  ?\n    a: b\n  ? c\n: w"),
  ("sibling-question-explicit-value", "?\n  ?\n    a: b\n  ? c\n  : - d\n: w"),
  ("implicit-to-question", "?\n  a: b\n  ? c\n  : - d\n: w"),
  ("sequence-map-question", "?\n  - a: b\n    ? c\n    : - d\n: w"),
  ("two-values-after-completed-inner", "? ? ? a\n    : b\n  : - c\n: d")]

def resumeSteps : Nat → ScannerState → List (Char × Nat × List Nat × List Nat × List Nat)
  | 0, _ => []
  | fuel + 1, sc =>
    match scanNextToken_preprocess sc, scanNextToken sc with
    | .ok (some (prep, c)), .ok (some out) =>
      let tail := resumeSteps fuel out
      if c == '?' || c == ':' then
        (c, prep.col, markedCols sc, markedCols prep, markedCols out) :: tail
      else tail
    | _, _ => []

#eval resumeInputs.map (fun (name, input) =>
  (name, (parseYaml input).isOk,
    resumeSteps (4 * input.length + 32) ((ScannerState.mk' input).emit .streamStart)))

#guard resumeInputs.all (fun (_, input) => (parseYaml input).isOk)
