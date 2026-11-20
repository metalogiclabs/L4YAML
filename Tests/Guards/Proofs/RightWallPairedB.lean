/-
MathGraph Right-Wall — paired Arm B, property-directed route.
Exact tree source is corrected PR359 head plus lawful directive route helpers:
d6ff3d1de0d02e1edbb4eb9b88fa3478ca76684d.

Shared protected consumer, same as Arm A:
  TraceWellFormed "a\n*x"

This trial does NOT import Arm A's 667-line after-case proof or cheat with
sorry/axioms. It proves the genuine semantic reduction and explicitly
leaves source-to-event non-reference provenance as a named residual.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.Document

@[expose] public section Blanket

namespace L4YAML.Proofs.RightWallPairedB

open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.SerializationWellFormed

/-! If an event list never USES an alias or tag, it is necessarily
well-formed in any document environment. Definitions and boundaries
can occur and are harmless without a use operation. -/
def NoUses : List Event → Prop
  | [] => True
  | .useAlias _ :: _ => False
  | .useTag _ :: _ => False
  | _ :: tail => NoUses tail

lemma noUses_implies_WellFormedFrom (env : Env) (events : List Event)
    (h : NoUses events) : WellFormedFrom env events := by
  induction events generalizing env with
  | nil => trivial
  | cons event tail ih =>
    cases event <;> simp only [NoUses] at h
    · exact ih _ h
    · exact ih _ h
    · exact ih _ h
    · exact False.elim h
    · exact ih _ h
    · exact False.elim h

lemma noUses_implies_SerializationWellFormed (events : List Event)
    (h : NoUses events) : SerializationWellFormed events :=
  noUses_implies_WellFormedFrom {} events h

/-- The direct-property strategy's first meaningful missing subgoal.
Unlike event-list uniqueness, this asks only that NO alias or tag USE
appears under any valid derivation of the fixed plain scalar.
It remains unproved for the source: an unconditional goal MUST NOT
be inferred from this conditional lemma. -/
def PlainScalarNoUses (source : String) : Prop :=
  ∀ ev, TraceOf source ev → NoUses ev

theorem property_directed_fixed_goal
    (hSourceInvariant : PlainScalarNoUses "a\n*x") :
    TraceWellFormed "a\n*x" := by
  intro ev hDerivation
  exact noUses_implies_SerializationWellFormed ev
    (hSourceInvariant ev hDerivation)

#print axioms noUses_implies_WellFormedFrom
#print axioms noUses_implies_SerializationWellFormed
#print axioms property_directed_fixed_goal

end L4YAML.Proofs.RightWallPairedB
end Blanket
