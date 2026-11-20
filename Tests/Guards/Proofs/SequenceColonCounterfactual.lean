/-! Bounded counterfactual on the unpatched, exact parent
14eb6dbab845d2ac61f171a9ed61906d3f9ffb2f. Does not replace the
scanner, change a predicate, or assert global grammar membership. -/
module
public import Tests.Guards.Proofs.CompactRouteCensus
public meta import Tests.Guards.Proofs.CompactRouteCensus
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.SequenceColonCounterfactual
open L4YAML L4YAML.Scanner
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Exact new guard evaluated at the ordinary block-indicator dispatch, but
without modifying the old scanner's control flow. -/
def proposedGuardAt (s : ScannerState) : Bool :=
  match scanNextToken_preprocess s with
  | .ok (some (prep, ':')) =>
    let dispatch := if prep.allowDirectives then
      { prep with allowDirectives := false, documentEverStarted := true }
      else prep
    let cleared := scanValueClearKey dispatch
    !cleared.inFlow && !cleared.simpleKey.possible && atSequenceIndent cleared
  | _ => false

partial def visitsNewGuard (s : ScannerState) : Nat → Bool
  | 0 => false
  | n + 1 =>
    if proposedGuardAt s then true
    else match scanNextToken s with
      | .ok (some t) => visitsNewGuard t n
      | _ => false

def oldAcceptedAtNewGuard : List String :=
  L4YAML.Tests.Guards.CompactRouteCensus.programs.filter fun p =>
    let (_, _, ok) := L4YAML.Tests.Guards.CompactRouteCensus.probe p
    ok && visitsNewGuard ((ScannerState.mk' p).emit .streamStart) 200

#eval (oldAcceptedAtNewGuard.length, oldAcceptedAtNewGuard.map reprStr)
#print axioms L4YAML.Tests.Guards.SequenceColonCounterfactual.proposedGuardAt
end L4YAML.Tests.Guards.SequenceColonCounterfactual
end Blanket
