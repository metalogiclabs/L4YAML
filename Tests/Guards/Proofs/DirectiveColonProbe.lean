/- Capstone 7.7 falsification control. These are native reachable states and
an actual scanner/parser disagreement, NOT a proof of grammar non-membership.
Global hRoute remains UNKNOWN until the annotated grammar decides the case. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.Reachability
public import L4YAML.Parser.TokenParser
public import L4YAML.Scanner.IndexedDispatch
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

/-- The candidate reaches the actual colon, but cannot cross it after the
scanner-validation change. This is a bounded regression, NOT a proof of
non-membership in the annotated source grammar. The original successful
five-step witness is pinned at parent e389fcb62b95b9da954bd81c14427d56e3417dfd. -/
lemma candidate_reaches_colon : ScannerReachable input afterTwo :=
  steps_reachable (n := 2) (.seed) (by cbv)

lemma candidate_native_guard :
    scanNextToken_preprocess afterTwo = .ok (some (colon, ':')) ∧
    colon.currentIndent = 2 ∧ colon.col = 2 ∧
    colon.simpleKey.possible = true ∧
    (scanValueClearKey colon).simpleKey.possible = false ∧
    atSequenceIndent (scanValueClearKey colon) = true ∧
    scanValueValidate (scanValueClearKey colon) =
      .error (.trailingContent colon.line colon.col) := by cbv; decide

/-- Directly pins the first newly rejected native edge. -/
lemma candidate_stops_before_directive :
    scanNextToken afterTwo = .error (.trailingContent colon.line colon.col) := by cbv

#guard (["? -\n  :", "?\n -\n :", "?\n  -\n  :", "?\n- -\n  :"] : List String).all
  (fun body => !(scanFiltered (body ++ "\n...\n%YAML 1.2\n---\ny")).isOk)
-- Indexed scanner parity on the same four native source witnesses; this
-- checks the separate indexed implementation rather than assuming parity.
#guard (["? -\n  :", "?\n -\n :", "?\n  -\n  :", "?\n- -\n  :"] : List String).all
  (fun body => !(L4YAML.Scanner.Indexed.ScannerStateIx.scanIx
    (body ++ "\n...\n%YAML 1.2\n---\ny")).isOk)
-- Legitimate explicit mapping values must remain accepted in both scanners.
#guard (scanFiltered "? a\n: b").isOk
#guard (L4YAML.Scanner.Indexed.ScannerStateIx.scanIx "? a\n: b").isOk
#guard (scanFiltered "- ? a\n  : b").isOk
#guard (L4YAML.Scanner.Indexed.ScannerStateIx.scanIx "- ? a\n  : b").isOk
-- Native minimal-body reproduction, independent of the following directive.
#guard !(scanFiltered "? -\n  :").isOk
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
-- Assert that the old four parser-only failures no longer reach the parser.
-- The new exact acceptance count is logged and must be pinned after qualification.
#guard sweepSummary == (62208, 26346, [])
#print axioms L4YAML.Tests.Guards.DirectiveColonProbe.candidate_reaches_colon
#print axioms L4YAML.Tests.Guards.DirectiveColonProbe.candidate_native_guard
end L4YAML.Tests.Guards.DirectiveColonProbe
end Blanket
