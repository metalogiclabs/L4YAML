module

public import TraceExplicitRepairAudit
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Production.Acceptance.Quoted
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Production.Acceptance.Quoted

/-! Group 7.7: test the proposed stream repair before spending a completeness
proof on it. The broad quoted-leaf defect is already documented in
Production/Acceptance/Quoted.lean. The new consumer below shows it survives
the existing explicit-only, drop-free stream repair AND a well-formed trace.
No production semantics or grammar is changed. Qualification is external.
-/

namespace MathGraph.WholeSource.CapstoneObstructions
@[expose] public section
open L4YAML Surface CharPredicates
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.SerializationWellFormed
open MathGraph.TraceExplicitRepairAudit

def Accepted (s : String) : Prop := ∃ docs, TokenParser.parseYaml s = .ok docs
def bad : String := "\"\x01\""

-- Adversarial controls precede the claim: retain a legal quoted body, empty
-- body, escaped control, and multibyte body. A raw control is not an escape.
#guard (TokenParser.parseYaml "\"\"").isOk
#guard (TokenParser.parseYaml "\"a\"").isOk
#guard (TokenParser.parseYaml "\"\\x01\"").isOk
#guard (TokenParser.parseYaml "\"é\"").isOk
#guard !(TokenParser.parseYaml bad).isOk
#guard !(Scanner.scan bad).isOk

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

/-- Three source characters, one illegal payload character; deleting the
payload gives the accepted empty quoted scalar (control above). -/
lemma broad_leaf : SCDoubleQuoted 0 .flowOut ⟨bad.toList, 0⟩ ⟨[], 3⟩ :=
  .mk 0 .flowOut _ _ _ _ (.mk _ 0)
    (.single 0 _ _ (.cons _ _ _
      (.plain '\x01' ['"'] 1 (by unfold isLineBreakProp; decide) (by decide) (by decide))
      (.nil _))) (.mk [] 2)

/-- This whole-source witness uses only the single-document arm of the
already defined repair: neither scannerDrop nor implicitContinue is available. -/
lemma repaired_bad : RepairedStream ⟨bad.toList, 0⟩ ⟨[], 3⟩ [] :=
  .single _ _ _ _ [] [] (.nil _)
    (.some _ _ [] (.bare _ _ [] (.mk _ _ []
      (.flowInBlock 0 .blockIn _ _ _ _ []
        (.inline 0 _ _ (.startOfLine _))
        (.content 0 .flowOut _ _ [] (.doubleQ 0 .flowOut _ _ broad_leaf))
        (eofComments 3))))) (.nil _)

lemma bad_trace_wf : SerializationWellFormed ([] : List Event) := trivial

def RepairedWellFormed (s : String) : Prop :=
  ∃ col ev, RepairedStream ⟨s.toList, 0⟩ ⟨[], col⟩ ev ∧ SerializationWellFormed ev

lemma bad_in_repaired : RepairedWellFormed bad :=
  ⟨3, [], repaired_bad, bad_trace_wf⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma rejects_bad : (TokenParser.parseYaml bad).toOption.isSome = false := by
  decide +kernel

lemma bad_not_accepted : ¬ Accepted bad := by
  rintro ⟨docs, hd⟩
  have h := rejects_bad
  rw [hd] at h
  cases h

/-- Stream repair plus existential serialization WF is insufficient even with
NO directives, aliases, tags, collections, or document continuation. This does
not assert the universal TraceWellFormed premise for the rejected source. -/
lemma repaired_completeness_refuted :
    ¬ (∀ s, RepairedWellFormed s → Accepted s) := by
  intro h
  exact bad_not_accepted (h bad bad_in_repaired)

/-- The source restriction required at this leaf is already present in the
independent nb-json predicate [2]; it is not a parser-success premise. -/
lemma payload_not_nb_json : ¬ isNbJsonProp '\x01' := by
  unfold isNbJsonProp
  decide

/-- Reuse the existing independently restricted character grammar, rather
than adding a predicate that calls the scanner. -/
lemma repaired_leaf_excludes_bad :
    ¬ L4YAML.Proofs.Acceptance.DQCharOk ⟨['\x01', '"'], 1⟩ ⟨['"'], 2⟩ := by
  intro h
  cases h with
  | plain _ _ _ hj _ _ => exact payload_not_nb_json hj

-- Reuse the documented scannerDrop construction, specialized to a shortest
-- nonempty rejection. This is a consumer/refutation, not a novel universality
-- discovery (Tests.Guards.Proofs.SuffixGapAudit already proves universality).
lemma bracket_in_current_language : InYamlLanguage "[" := by
  refine ⟨⟨[], 0⟩, ?_, rfl⟩
  exact .scannerDrop _ _ ⟨[], 0⟩ _
    (.single _ _ _ _ (.nil _) (.none _) (.nil _)) (eofComments 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma bracket_rejected : (TokenParser.parseYaml "[").toOption.isSome = false := by
  decide +kernel

#guard (TokenParser.parseYaml "").isOk
#guard (TokenParser.parseYaml "[]").isOk

lemma original_converse_refuted :
    ¬ (∀ s, InYamlLanguage s → Accepted s) := by
  intro h
  obtain ⟨docs, hd⟩ := h "[" bracket_in_current_language
  have hb := bracket_rejected
  rw [hd] at hb
  cases hb

end
end MathGraph.WholeSource.CapstoneObstructions

#print MathGraph.WholeSource.CapstoneObstructions.repaired_completeness_refuted
#print MathGraph.WholeSource.CapstoneObstructions.original_converse_refuted
#print axioms MathGraph.WholeSource.CapstoneObstructions.broad_leaf
#print axioms MathGraph.WholeSource.CapstoneObstructions.repaired_bad
#print axioms MathGraph.WholeSource.CapstoneObstructions.rejects_bad
#print axioms MathGraph.WholeSource.CapstoneObstructions.repaired_completeness_refuted
#print axioms MathGraph.WholeSource.CapstoneObstructions.repaired_leaf_excludes_bad
#print axioms MathGraph.WholeSource.CapstoneObstructions.original_converse_refuted
