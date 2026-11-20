/-
MathGraph Right-Wall candidate: semantic-verdict coherence versus complete
trace uniqueness.  Exact source lineage: L4YAML owner
b9e0a5b52f8731afbe603b4ae0f32df438073319.
Proof applies to the project's actual TraceOf and SerializationWellFormed
definitions. The two-trace strictness model below is an abstract control,
NOT an actual corrected-YAML witness.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section Blanket

namespace L4YAML.Proofs.RightWallVerdict

open L4YAML
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
The capstone's TraceWellFormed goal is universal *acceptability* of traces.
Uniqueness of the entire event list is a sufficient but stronger condition.
-/

/-- All valid grammar derivations agree on the *serialization verdict*.
    It allows different event lists where that distinction has no effect
    on the protected property. -/
def VerdictCoherent (source : String) : Prop :=
  ∀ (ev₁ ev₂ : List Event),
    TraceOf source ev₁ → TraceOf source ev₂ →
    (SerializationWellFormed ev₁ ↔ SerializationWellFormed ev₂)

/-- The currently planned S4 uniqueness proof is sufficient for coherence. -/
lemma uniqueness_implies_verdict_coherence (source : String)
    (hUnique : ∀ (ev₁ ev₂ : List Event),
      TraceOf source ev₁ → TraceOf source ev₂ → ev₁ = ev₂) :
    VerdictCoherent source := by
  intro ev₁ ev₂ h₁ h₂
  rw [hUnique ev₁ ev₂ h₁ h₂]

/-- S3+S5 plus verdict coherence is enough for the same *universal*
    TraceWellFormed conclusion, without requiring literal trace uniqueness. -/
lemma scanner_trace_closes_universal_if_verdict_coherent
    (source : String) (scannerEvents : List Event)
    (hS3 : TraceOf source scannerEvents)
    (hCoherent : VerdictCoherent source)
    (hS5 : SerializationWellFormed scannerEvents) :
    TraceWellFormed source := by
  intro ev hTrace
  exact (hCoherent ev scannerEvents hTrace hS3).mpr hS5

/-- The precise boundary: once S3 supplies one existing well-formed
    scanner trace (S5), *verdict coherence is equivalent to the intended
    universal trace-well-formedness goal*. No stronger S4 claim is required
    by this logical step. This does NOT prove coherence for L4YAML. -/
theorem verdict_coherence_iff_trace_well_formed_of_valid_scanner_trace
    (source : String) (scannerEvents : List Event)
    (hS3 : TraceOf source scannerEvents)
    (hS5 : SerializationWellFormed scannerEvents) :
    VerdictCoherent source ↔ TraceWellFormed source := by
  constructor
  · intro hCoherent
    exact scanner_trace_closes_universal_if_verdict_coherent
      source scannerEvents hS3 hCoherent hS5
  · intro hAll ev₁ ev₂ h₁ h₂
    exact ⟨fun _ => hAll ev₂ h₂, fun _ => hAll ev₁ h₁⟩

/-!
Abstract strictness control (NOT a theorem about actual TraceOf):
Two different event streams can both be SerializationWellFormed.
A relation accepting precisely those two streams has total semantic
validity but not unique event lists.
-/
private def TwoValidTraces (ev : List Event) : Prop :=
  ev = [] ∨ ev = [.defineAnchor "x"]

private lemma two_valid_traces_wf (ev : List Event)
    (h : TwoValidTraces ev) : SerializationWellFormed ev := by
  rcases h with h | h
  · subst ev
    simp [SerializationWellFormed, WellFormedFrom]
  · subst ev
    simp [SerializationWellFormed, WellFormedFrom]

lemma toy_semantic_validity_with_multiple_traces :
    (∀ ev, TwoValidTraces ev → SerializationWellFormed ev) ∧
    ¬ (∀ ev₁ ev₂, TwoValidTraces ev₁ → TwoValidTraces ev₂ → ev₁ = ev₂) := by
  constructor
  · exact two_valid_traces_wf
  · intro hUnique
    have h : ([] : List Event) = [.defineAnchor "x"] :=
      hUnique [] [.defineAnchor "x"] (Or.inl rfl) (Or.inr rfl)
    cases h

#print axioms uniqueness_implies_verdict_coherence
#print axioms scanner_trace_closes_universal_if_verdict_coherent
#print axioms verdict_coherence_iff_trace_well_formed_of_valid_scanner_trace
#print axioms toy_semantic_validity_with_multiple_traces

end L4YAML.Proofs.RightWallVerdict
end Blanket
