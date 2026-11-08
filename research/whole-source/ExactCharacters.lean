module
public import L4YAML.Surface.Basic
public meta import Lean
set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactCharacters
open L4YAML.Surface L4YAML.CharPredicates

/-! Group 7.7 dependency: exact character leaves -> exact recursive syntax ->
independent source language. Source: YAML 1.2.2 [1], [2], [27], [34], [75],
blob 2f078ec32749a55b5ad961899ed0f344037260e0. No runtime acceptance definitions.
This is not a completed grammar, nor a change to production semantics. -/

/-- [1] c-printable, including both line-break code points. -/
def CPrintable (c : Char) : Prop :=
  c = '\t' ∨ c = '\n' ∨ c = '\r' ∨
  (c.val ≥ 0x20 ∧ c.val ≤ 0x7E) ∨ c = '\u0085' ∨
  (c.val ≥ 0xA0 ∧ c.val ≤ 0xD7FF) ∨
  (c.val ≥ 0xE000 ∧ c.val ≤ 0xFFFD) ∨
  (c.val ≥ 0x10000 ∧ c.val ≤ 0x10FFFF)
/-- [2] nb-json: quoted content admits non-C0 characters. -/
def NbJson (c : Char) : Prop :=
  c = '\t' ∨ (c.val ≥ 0x20 ∧ c.val ≤ 0x10FFFF)
/-- [27] nb-char, also the body class used by [75] comments. -/
def NbChar (c : Char) : Prop :=
  CPrintable c ∧ c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ '\uFEFF'
/-- [34] ns-char. -/
def NsChar (c : Char) : Prop := NbChar c ∧ c ≠ ' ' ∧ c ≠ '\t'
instance (c : Char) : Decidable (CPrintable c) := by unfold CPrintable; infer_instance
instance (c : Char) : Decidable (NbJson c) := by unfold NbJson; infer_instance
instance (c : Char) : Decidable (NbChar c) := by unfold NbChar; infer_instance
instance (c : Char) : Decidable (NsChar c) := by unfold NsChar; infer_instance

-- Adversarial boundary tests before the bridge proofs. These do not mutate
-- protected production tests. No scanner or parser is called by these checks.
#guard CPrintable '\n' ∧ CPrintable '\r' ∧ ¬ isPrintableProp '\n' ∧ ¬ isPrintableProp '\r'
#guard NbJson '\u007F' ∧ ¬ CPrintable '\u007F'
#guard NbJson '\u0080' ∧ ¬ CPrintable '\u0080'
#guard CPrintable '\u0085' ∧ NbChar '\u0085'
#guard ¬ NbJson '\u0001' ∧ ¬ NbChar '\u0001'
#guard CPrintable '\uFEFF' ∧ ¬ NbChar '\uFEFF'
#guard NbJson '\uFFFE' ∧ ¬ CPrintable '\uFFFE'
#guard NbJson '\uFFFF' ∧ ¬ CPrintable '\uFFFF'
#guard CPrintable '\uD7FF' ∧ CPrintable '\uE000' ∧ CPrintable '\U0010FFFF'
#guard NbChar '\t' ∧ ¬ NsChar '\t'
#guard isCommentTextChar '\u0001' ∧ ¬ NbChar '\u0001'

lemma printable_repair (c : Char) :
    CPrintable c ↔ isPrintableProp c ∨ c = '\n' ∨ c = '\r' := by
  simp [CPrintable, isPrintableProp, or_assoc, or_left_comm, or_comm]

lemma nb_json_reuse (c : Char) : NbJson c ↔ isNbJsonProp c := by
  simp [NbJson, isNbJsonProp]

lemma nb_char_reuse (c : Char) : NbChar c ↔ isNbChar c := by
  rw [NbChar, printable_repair]
  simp only [isNbChar, isLineBreakProp, isLineFeedProp, isCarriageReturnProp,
    beq_iff_eq, not_or]
  grind

lemma ns_char_reuse (c : Char) : NsChar c ↔ isNsChar c := by
  rw [NsChar, nb_char_reuse]
  simp only [isNbChar, isNsChar, isWhiteSpaceProp, isSpaceProp, isTabProp,
    beq_iff_eq, not_or]
  grind

-- Requirement-removal witnesses: neither loss can hide behind a green
-- consumer check. Raw SOH separates permissive comments; DEL separates a
-- blanket printable restriction from quoted nb-json.
lemma comment_relaxation_detected :
    isCommentTextChar '\u0001' ∧ ¬ NbChar '\u0001' := by decide
lemma quoted_overrestriction_detected :
    NbJson '\u007F' ∧ ¬ CPrintable '\u007F' := by decide

#check printable_repair
#check nb_json_reuse
#check nb_char_reuse
#check ns_char_reuse
open Lean Elab Command in
run_cmd do
  for n in [``printable_repair, ``nb_json_reuse, ``nb_char_reuse, ``ns_char_reuse,
      ``comment_relaxation_detected, ``quoted_overrestriction_detected] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"EXACT_CHARACTERS_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.ExactCharacters
