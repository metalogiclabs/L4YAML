module

public import DirectiveControls
public meta import DirectiveControls
public import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Proofs.Serialization.TraceOf.Document

/-!
# A whole-source obstruction to acceptance through erased directive traces

Research HEAD: metalogiclabs 3cdbed8694840cba94cad105a1a093843821ac98.
Underlying unchanged production source: nasa-jpl/L4YAML
64795a8db28ccfdae85082c93b6453001ae9d3e4.
Qualification is external: official pinned CI receipts for the exact source
commit govern proof and runtime status. This file alone makes no passing claim,
and no local Lean execution is claimed.

This is an external audit of the Group 7.7 grammar-completeness boundary, not a
new library capstone: source derivations → the same well-formed erased trace →
failure of completeness from one trace, and of any event-predicate acceptance
characterization. The second source has duplicate version directives and is
not valid YAML 1.2.2. Correct parser rejection is not a runtime defect.

The witnesses consume the literal original inputs, using only the annotated
grammar's ordinary constructors. The `%YAML` lines carry no event, and the
empty explicit body contributes no event. No scannerDrop or emitted surrogate
is involved. This does NOT establish or refute the universal `TraceWellFormed`
capstone: one well-formed trace does not show that all source traces are so.

Ordinary source and relation proofs precede and do not depend on the isolated
`Runtime` observations. Only its two concrete Bool leaves use native_decide.
-/

namespace MathGraph.WholeSource.DirectiveTrace

@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open MathGraph.WholeSource.DirectiveControls (one two publicAccept)

/-- Acceptance is exactly existential success of the actual public parser. -/
def Accepted (input : String) : Prop :=
  ∃ docs, TokenParser.parseYaml input = .ok docs

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

/-- One version line, reusable before any remaining original-source tail. -/
private lemma yamlLine (rest : List Char) :
    SLDirective ⟨['%', 'Y', 'A', 'M', 'L', ' ', '1', '.', '2', '\n'] ++ rest, 0⟩
      ⟨rest, 0⟩ := by
  refine .yaml (' ' :: '1' :: '.' :: '2' :: '\n' :: rest) 0
    ⟨'1' :: '.' :: '2' :: '\n' :: rest, 6⟩
    ⟨'.' :: '2' :: '\n' :: rest, 7⟩
    ⟨'2' :: '\n' :: rest, 8⟩ ⟨'\n' :: rest, 9⟩ ⟨rest, 0⟩ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s' h
    cases h with
    | mk _ _ _ hp =>
      exact hp.2.1 (by decide : L4YAML.CharPredicates.isWhiteSpaceProp ' ')
  · exact .cons _ _ _ (.space _ 5) (.nil _)
  · exact .mk _ _ _ (.mk '1' _ 6 (by unfold isNsDecDigit; decide)) (.nil _)
  · exact .mk _ 7
  · exact .mk _ _ _ (.mk '2' _ 8 (by unfold isNsDecDigit; decide)) (.nil _)
  · exact .withComment _ _ _ (.noSep _ _ (.break _ _ (.lf rest 9))) (.nil _)

private lemma emptyBody : TLExplicitBody ⟨[], 3⟩ ⟨[], 3⟩ [] :=
  .right _ _ [] (.mk _ _ _ [] [] ⟨.mk _, rfl⟩ ⟨eofComments 3, rfl⟩)

/-- Reusable original-source directive prefix, ending immediately before `---`.
The suffix remains present in the source position and is not re-emitted. -/
lemma one_directive_run :
    TPlus TLDirective ⟨"%YAML 1.2\n---".toList, 0⟩ ⟨"---".toList, 0⟩ [] :=
  .mk _ _ _ [] [] ⟨yamlLine ['-', '-', '-'], by decide⟩ (.nil _)

/-- Exact original-source witness for one version directive. -/
lemma trace_one : TraceOf "%YAML 1.2\n---" [Event.beginDocument] := by
  exact ⟨3, .single _ _ _ _ [Event.beginDocument] [] (.nil _)
    (.some _ _ _ (.directive _ _ _
      (.mk _ _ _ _ [] [] one_directive_run (.mk []) emptyBody)))
    (.nil _)⟩

/-- Exact original-source witness for two version directives. Duplication is
admitted by the present formal relation, although this is not valid YAML. -/
lemma trace_two : TraceOf "%YAML 1.2\n%YAML 1.2\n---" [Event.beginDocument] := by
  refine ⟨3, .single _ _ _ _ [Event.beginDocument] [] (.nil _)
    (.some _ _ _ (.directive _ _ _ (.mk _ _ _ _ [] [] ?_ (.mk []) emptyBody)))
    (.nil _)⟩
  exact .mk _ _ _ [] []
    ⟨yamlLine "%YAML 1.2\n---".toList, by decide⟩
    (.cons _ _ _ [] [] ⟨yamlLine ['-', '-', '-'], by decide⟩ (.nil _))

lemma trace_wellFormed : SerializationWellFormed [Event.beginDocument] :=
  trivial

/-- Exact answer-preservation criterion for a relation: shared observations
must preserve the protected answer. The reverse direction needs no choice;
an observable is accepted when some related source is accepted. -/
lemma factorization_iff_shared_observable_agreement {Source Observation : Type}
    (R : Source → Observation → Prop) (A : Source → Prop) :
    (∃ P : Observation → Prop, ∀ input ev, R input ev → (A input ↔ P ev)) ↔
      (∀ first second ev, R first ev → R second ev → (A first ↔ A second)) := by
  constructor
  · rintro ⟨P, hP⟩ first second ev hfirst hsecond
    exact (hP first ev hfirst).trans (hP second ev hsecond).symm
  · intro hagree
    refine ⟨fun ev => ∃ input, R input ev ∧ A input, ?_⟩
    intro input ev hinput
    constructor
    · intro ha
      exact ⟨input, hinput, ha⟩
    · rintro ⟨other, hother, ha⟩
      exact (hagree other input ev hother hinput).mp ha

/-- A shared observable with conflicting protected answers cannot support any
predicate factorization. There is no choice of checker in this statement. -/
lemma no_factorization_of_collision {Source Observation : Type}
    (R : Source → Observation → Prop) (A : Source → Prop)
    {yes no : Source} {shared : Observation}
    (hyes : R yes shared) (hno : R no shared)
    (ayes : A yes) (ano : ¬ A no) :
    ¬ ∃ P : Observation → Prop, ∀ input ev, R input ev → (A input ↔ P ev) := by
  rintro ⟨P, hP⟩
  exact ano ((hP no shared hno).mpr ((hP yes shared hyes).mp ayes))

/-- Kernel-only conditional obstruction for the existing source derivations.
Concrete public-parser observations are arguments, not hidden assumptions. -/
lemma no_event_predicate_of_conflicting_answers
    (hone : Accepted one) (htwo : ¬ Accepted two) :
    ¬ ∃ P : List Event → Prop,
      ∀ input ev, TraceOf input ev → (Accepted input ↔ P ev) :=
  no_factorization_of_collision TraceOf Accepted trace_one trace_two hone htwo

lemma one_trace_source_completeness_refuted_of_rejection
    (htwo : ¬ Accepted two) :
    ¬ (∀ input ev, TraceOf input ev → SerializationWellFormed ev → Accepted input) := by
  intro h
  exact htwo (h two [Event.beginDocument] trace_two trace_wellFormed)

namespace Runtime

/-- Concrete native observation; inspect independently of source proofs. -/
lemma accepts_one : publicAccept one = true := by native_decide

/-- Concrete native observation; rejection of invalid duplicate directives. -/
lemma rejects_two : publicAccept two = false := by native_decide

lemma acceptance_one : Accepted "%YAML 1.2\n---" := by
  have h := accepts_one
  cases hr : TokenParser.parseYaml "%YAML 1.2\n---" with
  | error e =>
    change (TokenParser.parseYaml "%YAML 1.2\n---").toOption.isSome = true at h
    rw [hr] at h
    change false = true at h
    cases h
  | ok docs => exact ⟨docs, hr⟩

lemma rejection_two : ¬ Accepted "%YAML 1.2\n%YAML 1.2\n---" := by
  rintro ⟨docs, hdocs⟩
  have h := rejects_two
  change (TokenParser.parseYaml "%YAML 1.2\n%YAML 1.2\n---").toOption.isSome = false at h
  rw [hdocs] at h
  change true = false at h
  cases h

end Runtime

/-- One existing well-formed trace cannot justify source completeness. This is
strictly weaker than assuming the universal `TraceWellFormed` premise. -/
lemma one_trace_source_completeness_refuted :
    ¬ (∀ input ev, TraceOf input ev → SerializationWellFormed ev → Accepted input) :=
  one_trace_source_completeness_refuted_of_rejection Runtime.rejection_two

/-- No predicate whatsoever on this erased event list characterizes public
acceptance for every existing original-source derivation. -/
lemma no_event_predicate_characterizes_acceptance :
    ¬ ∃ P : List Event → Prop,
      ∀ input ev, TraceOf input ev → (Accepted input ↔ P ev) :=
  no_event_predicate_of_conflicting_answers Runtime.acceptance_one Runtime.rejection_two

end

end MathGraph.WholeSource.DirectiveTrace

#print axioms MathGraph.WholeSource.DirectiveTrace.one_directive_run
#print axioms MathGraph.WholeSource.DirectiveTrace.factorization_iff_shared_observable_agreement
#print axioms MathGraph.WholeSource.DirectiveTrace.one_trace_source_completeness_refuted_of_rejection
