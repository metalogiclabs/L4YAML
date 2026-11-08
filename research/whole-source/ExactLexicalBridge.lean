module
public import ExactLexical
public import L4YAML.Proofs.Production.Acceptance.Quoted
public meta import ExactLexical
public meta import L4YAML.Proofs.Production.Acceptance.Quoted
public meta import Lean
set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactLexicalBridge
open L4YAML.Surface L4YAML.Grammar L4YAML.Proofs.Acceptance
open MathGraph.WholeSource.ExactCharacters MathGraph.WholeSource.ExactLexical

-- Adversarial values before universal reuse proofs. Hex validity is checked
-- separately from digit syntax; escaped controls remain allowed.
#guard NamedEscape '\t' ∧ NamedEscape 'N' ∧ ¬ NamedEscape 'x' ∧ ¬ NamedEscape 'q'
#guard HexValue ['0','0','0','1'] = 1 ∧ (HexValue ['0','0','0','1']).isValidChar
#guard ¬ (HexValue ['D','8','0','0']).isValidChar
#guard ¬ (HexValue ['0','0','1','1','0','0','0','0']).isValidChar
#guard (HexValue ['0','0','1','0','F','F','F','F']).isValidChar
#guard HexValue ['f','f'] = 255

lemma named_escape_reuse (c : Char) : NamedEscape c ↔ isNamedEscapeChar c := by
  unfold isNamedEscapeChar resolveNamedEscape
  split <;> simp_all [NamedEscape]

lemma double_char_reuse (s s' : SurfPos) : DoubleChar s s' ↔ DQCharOk s s' := by
  constructor
  · intro h
    cases h with
    | plain c rest col hj hb hq => exact .plain c rest col ((nb_json_reuse c).mp hj) hb hq
    | escape ec rest col hv => exact .escape ec rest col ((named_escape_reuse ec).mp hv)
    | hexEscape2 rest col a b ha hb hv => exact .hexEscape2 rest col a b ha hb hv
    | hexEscape4 rest col a b c d ha hb hc hd hv => exact .hexEscape4 rest col a b c d ha hb hc hd hv
    | hexEscape8 rest col a b c d e f g h ha hb hc hd he hf hg hh hv =>
      exact .hexEscape8 rest col a b c d e f g h ha hb hc hd he hf hg hh hv
  · intro h
    cases h with
    | plain c rest col hj hb hq => exact .plain c rest col ((nb_json_reuse c).mpr hj) hb hq
    | escape ec rest col hv => exact .escape ec rest col ((named_escape_reuse ec).mpr hv)
    | hexEscape2 rest col a b ha hb hv => exact .hexEscape2 rest col a b ha hb hv
    | hexEscape4 rest col a b c d ha hb hc hd hv => exact .hexEscape4 rest col a b c d ha hb hc hd hv
    | hexEscape8 rest col a b c d e f g h ha hb hc hd he hf hg hh hv =>
      exact .hexEscape8 rest col a b c d e f g h ha hb hc hd he hf hg hh hv

lemma single_char_reuse (s s' : SurfPos) : SingleChar s s' ↔ SQCharOk s s' := by
  constructor
  · intro h
    cases h with
    | plain c rest col hj hq => exact .plain c rest col ((nb_json_reuse c).mp hj) hq
    | escapedQuote rest col => exact .escapedQuote rest col
  · intro h
    cases h with
    | plain c rest col hj hq => exact .plain c rest col ((nb_json_reuse c).mpr hj) hq
    | escapedQuote rest col => exact .escapedQuote rest col

lemma star_congr {P Q : SurfPos → SurfPos → Prop}
    (h : ∀ s s', P s s' ↔ Q s s') (s s' : SurfPos) : GStar P s s' ↔ GStar Q s s' := by
  constructor
  · intro hp
    induction hp with
    | nil s => exact .nil s
    | cons a b c hp _ ih => exact .cons a b c ((h a b).mp hp) ih
  · intro hq
    induction hq with
    | nil s => exact .nil s
    | cons a b c hq _ ih => exact .cons a b c ((h a b).mpr hq) ih

lemma double_body_reuse (s s' : SurfPos) : DoubleBody s s' ↔ GStar DQCharOk s s' :=
  star_congr double_char_reuse s s'
lemma single_body_reuse (s s' : SurfPos) : SingleBody s s' ↔ GStar SQCharOk s s' :=
  star_congr single_char_reuse s s'

private lemma comment_body_to_legacy {s s' : SurfPos}
    (hbody : GStar (GChar NbChar) s s') : GStar SCommentChar s s' := by
  induction hbody with
  | nil s => exact .nil s
  | cons a b c hc _ ih =>
    cases hc with
    | mk ch rest col hn =>
      refine .cons _ _ _ (.mk _ _ _ ?_) ih
      exact ((nb_char_reuse ch).mp hn).1

lemma comment_to_legacy {s s' : SurfPos} (h : CommentText s s') : SCNbCommentText s s' := by
  cases h with
  | mk rest col out hbody =>
    exact SCNbCommentText.mk _ _ _ (comment_body_to_legacy hbody)

lemma raw_control_excluded (rest : List Char) (col : Nat) (out : SurfPos) :
    ¬ DoubleChar ⟨'\u0001' :: rest, col⟩ out := by
  intro h
  cases h <;> simp_all [NbJson]
lemma doubled_quote (rest : List Char) (col : Nat) :
    SingleChar ⟨'\'' :: '\'' :: rest, col⟩ ⟨rest, col + 2⟩ := .escapedQuote rest col

#check double_char_reuse
#check single_char_reuse
#check double_body_reuse
#check single_body_reuse
#check comment_to_legacy
open Lean Elab Command in
run_cmd do
  for n in [``named_escape_reuse, ``double_char_reuse, ``single_char_reuse,
      ``double_body_reuse, ``single_body_reuse, ``comment_to_legacy,
      ``raw_control_excluded, ``doubled_quote] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"EXACT_LEXICAL_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.ExactLexicalBridge
