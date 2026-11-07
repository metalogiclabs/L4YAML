module

public import CapstoneObstructions
public import DirectiveParse
public meta import L4YAML.Parser.Composition

/-! Group 7.7 normative boundary. Surface.Basic already documents permissive
comment characters. This consumer makes its consequence for ANY exact language
predicate excluding raw SOH explicit. YAML 1.2.2 [1], [2], [27], [75] exclude
raw U+0001; quoted escapes producing that value are different source strings.
The experiment rejects the hypothesis that this is only a grammar/scanner
mismatch: the actual public parser accepts it. No production change is made.
-/

namespace MathGraph.WholeSource.CapstoneCommentBoundary
@[expose] public section
open L4YAML Surface
open MathGraph.WholeSource.CapstoneObstructions (Accepted)
open MathGraph.TraceExplicitRepairAudit

def commentInput : String := "#\x01"
def NoRawSOH (input : String) : Prop := '\x01' ∉ input.toList

-- Empty/minimal legal and illegal controls, including source vs decoded value.
#guard (TokenParser.parseYaml "").isOk
#guard (TokenParser.parseYaml "#").isOk
#guard (TokenParser.parseYaml "#a").isOk
#guard (TokenParser.parseYaml commentInput).isOk
#guard (TokenParser.parseYaml "#\x01\n").isOk
#guard !(TokenParser.parseYaml "\"\x01\"").isOk
#guard (TokenParser.parseYaml "\"\\x01\"").isOk

lemma comment_derivation : SLComment ⟨commentInput.toList, 0⟩ ⟨[], 2⟩ :=
  .mk _ _ _ _ (.startOfLine _)
    (.some _ _ (.mk _ 0 _ (.cons _ _ _
      (.mk '\x01' [] 1 (by unfold isCommentTextChar L4YAML.CharPredicates.isLineBreakProp; decide))
      (.nil _)))) (.eof 2)

lemma repaired_comment : RepairedStream ⟨commentInput.toList, 0⟩ ⟨[], 2⟩ [] :=
  comment_preserved (empty_at _) comment_derivation

lemma comment_violates_character_requirement : ¬ NoRawSOH commentInput := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma runtime_accepts_comment : (TokenParser.parseYaml commentInput).toOption.isSome = true := by
  decide +kernel

lemma comment_accepted : Accepted commentInput := by
  have h := runtime_accepts_comment
  cases hr : TokenParser.parseYaml commentInput with
  | error e =>
    rw [hr] at h
    cases h
  | ok docs => exact ⟨docs, hr⟩

/-- A necessary normative condition already conflicts with frozen runtime.
This is a precise obstruction, not a formalization of all YAML semantics. -/
lemma normative_character_soundness_refuted :
    ¬ (∀ input, Accepted input → NoRawSOH input) := by
  intro h
  exact comment_violates_character_requirement (h commentInput comment_accepted)

/-- No RHS respecting even this necessary raw-character restriction can be
equivalent to acceptance of the unchanged public parser on ALL strings. -/
lemma no_normative_iff_on_frozen_runtime (Language : String → Prop)
    (hchar : ∀ s, Language s → NoRawSOH s) :
    ¬ (∀ s, Accepted s ↔ Language s) := by
  intro h
  exact comment_violates_character_requirement
    (hchar commentInput ((h commentInput).mp comment_accepted))

/-- The previously qualified empty-document family itself includes the same
non-normative character. This is reuse of its general theorem, not evaluation
of another synthetic parser. Its runtime theorem stays valid; interpreting it
as normative YAML membership would be invalid. -/
lemma retained_empty_family_accepts_raw_soh :
    Accepted "%YAML 1.2 #\x01\n---\n" := by
  apply MathGraph.WholeSource.DirectiveParse.original_empty_document_parses
    _ ['1'] ['2'] ['\x01']
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    unfold isNsDecDigit
    decide
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    unfold isNsDecDigit
    decide
  · decide
  · decide
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    decide
  · decide

end
end MathGraph.WholeSource.CapstoneCommentBoundary

#print axioms MathGraph.WholeSource.CapstoneCommentBoundary.repaired_comment
#print axioms MathGraph.WholeSource.CapstoneCommentBoundary.normative_character_soundness_refuted
#print axioms MathGraph.WholeSource.CapstoneCommentBoundary.no_normative_iff_on_frozen_runtime
#print axioms MathGraph.WholeSource.CapstoneCommentBoundary.retained_empty_family_accepts_raw_soh
