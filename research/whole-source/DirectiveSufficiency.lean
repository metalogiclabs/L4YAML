module

public import DirectiveDiscipline
public meta import DirectiveDiscipline

/-!
# Adversarial consumer of the version-disciplined source premise

Group 7.7 dependency: directive-source adequacy -> actual scanner correspondence
-> public acceptance. This checks the premise BEFORE attempting that bridge.
An empty TAG handle is admitted by the existing source constructors and the
version-count refinement. It is rejected by the actual public parser.
Source derivations are kernel proofs; the runtime observation is explicitly
separate. This is a counterexample to sufficiency, not full-language closure.
-/

namespace MathGraph.WholeSource.DirectiveSufficiency
@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open MathGraph.WholeSource.DirectiveDiscipline
open MathGraph.WholeSource.DirectiveTrace (Accepted)

def bad : String := "%TAG \n---"

/-- The existing TAG source constructor permits an empty handle and prefix. -/
lemma empty_tag_line (rest : List Char) :
    SLDirective ⟨['%', 'T', 'A', 'G', ' ', '\n'] ++ rest, 0⟩
      ⟨rest, 0⟩ := by
  refine .tag (' ' :: '\n' :: rest) 0
    ⟨'\n' :: rest, 5⟩ ⟨'\n' :: rest, 5⟩
    ⟨'\n' :: rest, 5⟩ ⟨'\n' :: rest, 5⟩ ⟨rest, 0⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s' h
    cases h with
    | mk _ _ _ hp =>
      exact hp.2.1 (by decide : L4YAML.CharPredicates.isWhiteSpaceProp ' ')
  · exact .cons _ _ _ (.space _ 4) (.nil _)
  · exact .nil _
  · intro s' h
    cases h with
    | mk _ _ _ hp =>
      rcases hp with hp | hp
      · simp [L4YAML.CharPredicates.isWordCharProp,
          L4YAML.CharPredicates.isAsciiLetterProp] at hp
      · cases hp
  · exact .nil _
  · exact .nil _
  · exact .withComment _ _ _ (.noSep _ _ (.break _ _ (.lf rest 5))) (.nil _)

/-- Non-vacuous witness: the invalid directive satisfies the CURRENT refinement. -/
lemma bad_refined_run : VersionDisciplinedRun
    ⟨bad.toList, 0⟩ ⟨"---".toList, 0⟩ [] := by
  constructor
  · exact .mk _ _ _ [] [] ⟨empty_tag_line ['-', '-', '-'], by decide⟩ (.nil _)
  · decide

lemma bad_trace : TraceOf bad [Event.beginDocument] := by
  have hc : SSLComments ⟨[], 3⟩ ⟨[], 3⟩ :=
    .withComment _ _ _ (.noSep _ _ (.eof 3)) (.nil _)
  have hb : TLExplicitBody ⟨[], 3⟩ ⟨[], 3⟩ [] :=
    .right _ _ [] (.mk _ _ _ [] [] ⟨.mk _, rfl⟩ ⟨hc, rfl⟩)
  exact ⟨3, .single _ _ _ _ [Event.beginDocument] [] (.nil _)
    (.some _ _ _ (.directive _ _ _
      (.mk _ _ _ _ [] [] bad_refined_run.1 (.mk []) hb))) (.nil _)⟩

lemma bad_trace_wellFormed : SerializationWellFormed [Event.beginDocument] :=
  trivial

/-- Explicit candidate contract for the empty-body directive-document fragment.
It uses original source syntax, consumes the full source, and has no execution
premise. The counterexample below prevents promoting this contract. -/
def RefinedEmptyDocument (input : String) : Prop :=
  VersionDisciplinedRun ⟨input.toList, 0⟩ ⟨"---".toList, 0⟩ []

lemma refined_empty_completeness_refuted_of_rejection
    (hbad : ¬ Accepted bad) :
    ¬ (∀ input, RefinedEmptyDocument input → Accepted input) := by
  intro hall
  exact hbad (hall bad bad_refined_run)

namespace Runtime

-- Positive controls distinguish malformed TAG syntax from rejecting TAGs.
#guard (TokenParser.parseYaml "%TAG ! tag:x\n---").toOption.isSome = true
#guard (TokenParser.parseYaml "%TAG !! tag:x\n---").toOption.isSome = true
#guard (TokenParser.parseYaml "%TAG !t! tag:x\n---").toOption.isSome = true
#guard (TokenParser.parseYaml bad).toOption.isSome = false
#guard (TokenParser.parseYaml "%TAG \r\n---").toOption.isSome = false
#guard (TokenParser.parseYaml "%TAG \n---\n").toOption.isSome = false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma rejects_bad : (TokenParser.parseYaml bad).toOption.isSome = false := by
  decide

lemma rejection_bad : ¬ Accepted bad := by
  rintro ⟨docs, hdocs⟩
  have h := rejects_bad
  rw [hdocs] at h
  change true = false at h
  cases h

end Runtime

lemma refined_empty_completeness_refuted :
    ¬ (∀ input, RefinedEmptyDocument input → Accepted input) :=
  refined_empty_completeness_refuted_of_rejection Runtime.rejection_bad

/-- Adding the actual whole-source trace and its WF condition does not repair
the insufficiency. This is still an existential-trace result, not the universal
TraceWellFormed capstone. -/
lemma refined_traced_completeness_refuted :
    ¬ (∀ input ev, RefinedEmptyDocument input →
      TraceOf input ev → SerializationWellFormed ev → Accepted input) := by
  intro hall
  exact Runtime.rejection_bad
    (hall bad [Event.beginDocument] bad_refined_run bad_trace bad_trace_wellFormed)

#print axioms refined_traced_completeness_refuted
#print axioms empty_tag_line
#print axioms bad_refined_run
#print axioms bad_trace
#print axioms bad_trace_wellFormed
#print axioms refined_empty_completeness_refuted_of_rejection
#print axioms Runtime.rejects_bad
#print axioms refined_empty_completeness_refuted

end
end MathGraph.WholeSource.DirectiveSufficiency
