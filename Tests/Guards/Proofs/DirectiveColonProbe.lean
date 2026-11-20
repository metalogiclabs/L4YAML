/- Capstone 7.7 falsification control. These are native reachable states and
an actual scanner/parser disagreement, NOT a proof of grammar non-membership.
Global hRoute remains UNKNOWN until the annotated grammar decides the case. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.Reachability
public import L4YAML.Parser.TokenParser
public meta import L4YAML.Proofs.Serialization.TraceOf.Reachability
public meta import L4YAML.Parser.TokenParser
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.DirectiveColonProbe
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
open L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def steps (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 => match scanNextToken s with
    | .ok (some t) => steps t n
    | _ => none

lemma steps_reachable {input : String} {s t : ScannerState} {n : Nat}
    (reach : ScannerReachable input s) (run : steps s n = some t) :
    ScannerReachable input t := by
  induction n generalizing s with
  | zero => exact Option.some.inj run ▸ reach
  | succ n ih =>
    simp only [steps] at run
    cases he : scanNextToken s with
    | error e => rw [he] at run; cases run
    | ok next =>
      rw [he] at run
      cases next with
      | none => cases run
      | some mid => exact ih (reach.step he) run

def input : String := "? -\n  :\n...\n%YAML 1.2\n---\ny"
def seed : ScannerState := scanSeed input
def afterTwo : ScannerState := (steps seed 2).getD seed
def colon : ScannerState := match scanNextToken_preprocess afterTwo with
  | .ok (some (s, _)) => s
  | _ => seed
def directed : ScannerState := (steps seed 5).getD seed

lemma candidate_reaches_directive : ScannerReachable input directed :=
  steps_reachable (n := 5) (.seed) (by cbv)

lemma candidate_directive_flags : directed.allowDirectives = true ∧
    directed.seenYamlDirective = true ∧ directed.offset = 21 := by cbv

/-- At the actual native colon, clearing the cross-line explicit-key stamp
turns off the premise guarding the at-sequence-indent refusal. -/
lemma candidate_native_gate :
    scanNextToken_preprocess afterTwo = .ok (some (colon, ':')) ∧
    colon.currentIndent = 2 ∧ colon.col = 2 ∧
    colon.simpleKey.possible = true ∧
    (scanValueClearKey colon).simpleKey.possible = false ∧
    atSequenceIndent (scanValueClearKey colon) = true ∧
    scanValueValidate (scanValueClearKey colon) = .ok () := by cbv; decide

private def disagrees (body : String) : Bool :=
  let src := body ++ "\n...\n%YAML 1.2\n---\ny"
  match scanFiltered src with
  | .ok ts => !(L4YAML.TokenParser.parseStream ts).isOk
  | .error _ => false

#guard (["? -\n  :", "?\n -\n :", "?\n  -\n  :", "?\n- -\n  :"] : List String).all disagrees
-- Native minimal-body reproduction, independent of the following directive.
#guard (scanFiltered "? -\n  :").isOk
#guard !((scanFiltered "? -\n  :").bind (fun ts => L4YAML.TokenParser.parseStream ts)).isOk
/-- The exact bounded falsification experiment: three chunks with two
separators, all cases retained. It is an observation, not a grammar oracle. -/
def sweepSummary : Nat × Nat × List String := Id.run do
  let chunks := ["a", "b", "'a'", "[a]", "{a: b}", "&a", "!x", "?", ":", "-", "", "#c"]
  let separators := [" ", "\n", "\n ", "\n  ", "\n- ", ": "]
  let mut total : Nat := 0
  let mut accepted : Nat := 0
  let mut failures : List String := []
  for a in chunks do
    for b in chunks do
      for c in chunks do
        for x in separators do
          for y in separators do
            let body := a ++ x ++ b ++ y ++ c
            total := total + 1
            match scanFiltered (body ++ "\n...\n%YAML 1.2\n---\ny") with
            | .error _ => pure ()
            | .ok ts =>
              accepted := accepted + 1
              if !(L4YAML.TokenParser.parseStream ts).isOk then
                failures := failures ++ [body]
  return (total, accepted, failures)
#guard sweepSummary == (62208, 26350,
  ["? -\n  :", "?\n -\n :", "?\n  -\n  :", "?\n- -\n  :"])
#print axioms L4YAML.Tests.Guards.DirectiveColonProbe.candidate_reaches_directive
#print axioms L4YAML.Tests.Guards.DirectiveColonProbe.candidate_native_gate
end L4YAML.Tests.Guards.DirectiveColonProbe
end Blanket
