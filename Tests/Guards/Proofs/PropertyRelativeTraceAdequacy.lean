/-
Property-relative trace adequacy for the EXACT NASA JPL metagraph-problem
experimental source, commit aeacc60258b89fc1c5bb34b6f0ba9a5286801c02.

Purpose: test whether trace equality is unnecessarily stronger than the
specific requirement used by Group 7.7: well-formed serialization traces.

This file introduces no axioms and changes no production definitions.
-/
module

public import Tests.Guards.Proofs.TraceOfBlockAmbiguity

@[expose] public section Blanket

namespace L4YAML.Tests.Guards.PropertyRelativeTraceAdequacy

open L4YAML
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.SerializationWellFormed

/-- The property-relative condition sufficient to transport the
serialization well-formedness verdict across legitimate grammar traces.
This explicitly permits two unequal event traces with the same verdict. -/
def WFAdequacy (input : String) : Prop :=
  ∀ e₁ e₂ : List Event,
    TraceOf input e₁ → TraceOf input e₂ →
    (SerializationWellFormed e₁ ↔ SerializationWellFormed e₂)

/-- S3 supplies the scanner's observed trace; the consumer only needs
WFAdequacy, not equality of the whole event lists. -/
theorem scanner_wf_lifts_without_uniqueness
    (input : String) (observed : List Event)
    (hScanTrace : TraceOf input observed)
    (hScanWF : SerializationWellFormed observed)
    (hAdequacy : WFAdequacy input) :
    TraceWellFormed input := by
  intro ev hev
  exact (hAdequacy observed ev hScanTrace hev).mp hScanWF

/-- Full trace uniqueness is a SUFFICIENT but unnecessarily strong
condition for property-relative well-formedness agreement. -/
theorem uniqueness_implies_wf_adequacy
    (input : String)
    (hUnique : ∀ e₁ e₂ : List Event,
      TraceOf input e₁ → TraceOf input e₂ → e₁ = e₂) :
    WFAdequacy input := by
  intro e₁ e₂ h₁ h₂
  rw [hUnique e₁ e₂ h₁ h₂]

private theorem wf_empty : SerializationWellFormed ([] : List Event) := by
  rw [serializationWellFormed_iff_check]
  decide

private theorem wf_single_anchor :
    SerializationWellFormed [Event.defineAnchor "x"] := by
  rw [serializationWellFormed_iff_check]
  decide

/-- The project's checked ambiguity example is HARMLESS for the specific
well-formedness verdict on these TWO traces. This is NOT yet a
universal WFAdequacy theorem for that input. -/
theorem distinct_wellformed_ambiguity :
    TraceOf "a\n&x" [] ∧
    TraceOf "a\n&x" [Event.defineAnchor "x"] ∧
    ([] : List Event) ≠ [Event.defineAnchor "x"] ∧
    SerializationWellFormed ([] : List Event) ∧
    SerializationWellFormed [Event.defineAnchor "x"] := by
  exact ⟨Tests.Guards.TraceOfBlockAmbiguity.traceOf_plain,
    Tests.Guards.TraceOfBlockAmbiguity.traceOf_anchor,
    by decide, wf_empty, wf_single_anchor⟩

/-- The other checked ambiguity example is CONSEQUENTIAL: the empty
scanner trace is well formed, but a different derivation contains
an undefined alias. Thus property-relative adequacy really fails there. -/
theorem alias_counterexample_refutes_wf_adequacy :
    ¬ WFAdequacy "a\n*x" := by
  intro hAdequacy
  have hBoth := hAdequacy []
    [Event.useAlias "x"]
    Tests.Guards.TraceOfBlockAmbiguity.traceOf_plainStar
    Tests.Guards.TraceOfBlockAmbiguity.traceOf_alias
  exact Tests.Guards.TraceOfBlockAmbiguity.not_wf_alias
    (hBoth.mp wf_empty)

#print axioms L4YAML.Tests.Guards.PropertyRelativeTraceAdequacy.scanner_wf_lifts_without_uniqueness
#print axioms L4YAML.Tests.Guards.PropertyRelativeTraceAdequacy.uniqueness_implies_wf_adequacy
#print axioms L4YAML.Tests.Guards.PropertyRelativeTraceAdequacy.distinct_wellformed_ambiguity
#print axioms L4YAML.Tests.Guards.PropertyRelativeTraceAdequacy.alias_counterexample_refutes_wf_adequacy

end L4YAML.Tests.Guards.PropertyRelativeTraceAdequacy

end Blanket
