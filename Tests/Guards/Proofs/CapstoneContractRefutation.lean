/-
A SOURCE-INDEXED TEST OF THE PLANNED GROUP 7.7 CONTRACT

Based on the exact NASA JPL experiment/metagraph-problem source tree
aeacc60258b89fc1c5bb34b6f0ba9a5286801c02 (Lean 4.35.0).
No production code, surface grammar or existing theorem is modified.

This intentionally checks the *forward* claimed implication in
EXPERIMENT.md §0.1, rather than attempting to finish the S3 proof.
-/
module

public import Tests.Guards.Proofs.TraceOfBlockAmbiguity
public import L4YAML.Parser.Composition
public import L4YAML.Surface.Document
public meta import L4YAML.Parser.Composition

@[expose] public section Blanket

namespace L4YAML.Tests.Guards.CapstoneContractRefutation

open L4YAML
open L4YAML.TokenParser
open L4YAML.Proofs.Serialization.TraceOf

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Actual native API accepts the historical YAML input as one document.
This is a concrete executable calculation, not a postulated parse success. -/
theorem accepted_input :
    ∃ docs, L4YAML.TokenParser.parseYaml "a\n*x" = .ok docs := by
  have hok : (L4YAML.TokenParser.parseYaml "a\n*x").isOk = true := by native_decide
  cases h : L4YAML.TokenParser.parseYaml "a\n*x" with
  | error err =>
    simp at hok
  | ok docs =>
    exact ⟨docs, rfl⟩

/-- This previously checked lemma comes from the exact owner experiment:
the existing annotated grammar also parses '*x' as a separate alias
document, producing an ill-formed trace. -/
theorem current_grammar_requirement_refuted :
    ¬ TraceWellFormed "a\n*x" :=
  Tests.Guards.TraceOfBlockAmbiguity.traceWellFormed_refuted

/-- A direct refutation of the *forward* proposed capstone guarantee
under the pinned current formal grammar and native parser. -/
theorem proposed_forward_false :
    ¬ (∀ input : String,
      (∃ docs, L4YAML.TokenParser.parseYaml input = .ok docs) →
      TraceWellFormed input) := by
  intro h
  exact current_grammar_requirement_refuted (h "a\n*x" accepted_input)

/-- Even replacing the *first* conjunct by an arbitrary exact surface
language predicate cannot fix this specific false biconditional while its
TraceWellFormed conjunct is unchanged. -/
theorem no_biconditional_with_current_trace
    (ExactSurfaceLanguage : String → Prop) :
    ¬ (∀ input : String,
      (∃ docs, L4YAML.TokenParser.parseYaml input = .ok docs) ↔
      (ExactSurfaceLanguage input ∧ TraceWellFormed input)) := by
  intro h
  have both := (h "a\n*x").mp accepted_input
  exact current_grammar_requirement_refuted both.2

/-- In the same source, the existing *forward* InYamlLanguage target
is true of every string, so an acceptance=>membership theorem proves no
negative recognition property until scannerDrop is removed. -/
theorem language_accepts_every_string (input : String) :
    L4YAML.Surface.InYamlLanguage input := by
  refine ⟨⟨[], 0⟩, ?_, rfl⟩
  exact L4YAML.Surface.SLYamlStream.scannerDrop
    ⟨input.toList, 0⟩ ⟨input.toList, 0⟩ ⟨[], 0⟩ ⟨[], 0⟩
    (.single _ _ _ _ (.nil _) (.none _) (.nil _))
    (.startOfLine [] ⟨[], 0⟩ (.nil _))

#print axioms L4YAML.Tests.Guards.CapstoneContractRefutation.language_accepts_every_string
#print axioms L4YAML.Tests.Guards.CapstoneContractRefutation.accepted_input
#print axioms L4YAML.Tests.Guards.CapstoneContractRefutation.current_grammar_requirement_refuted
#print axioms L4YAML.Tests.Guards.CapstoneContractRefutation.proposed_forward_false
#print axioms L4YAML.Tests.Guards.CapstoneContractRefutation.no_biconditional_with_current_trace

end L4YAML.Tests.Guards.CapstoneContractRefutation

end Blanket
