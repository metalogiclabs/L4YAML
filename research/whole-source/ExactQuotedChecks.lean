module
public import ExactQuoted
public import ExactLexicalBridge
public meta import Lean
set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactQuotedChecks
open L4YAML L4YAML.Surface
open MathGraph.WholeSource.ExactCharacters MathGraph.WholeSource.ExactLexical
open MathGraph.WholeSource.ExactQuoted MathGraph.WholeSource.ExactLexicalBridge

private lemma zero_prefix (s : SurfPos) : SFlowLinePrefix 0 s s :=
  .mk 0 s s s (.zero s) (.none s)
private lemma folded_lf (rest : List Char) (col : Nat) :
    FlowFolded 0 ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩ := by
  exact .mk _ _ _ _ (.none _) (.right _ _ (.lf rest col)) (zero_prefix _)

-- Positive syntax witnesses exercise both multiline alternatives before reuse.
lemma double_flow_break (rest : List Char) (col : Nat) :
    DoubleText 0 .flowIn ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩ := by
  exact .mk _ _ _ (.nil _) (.left _ _ (.empty _ _ (.right _ _ (folded_lf rest col))))
lemma single_flow_break (rest : List Char) (col : Nat) :
    SingleText 0 .flowOut ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩ := by
  exact .mk _ _ _ (.nil _) (.left _ _ (.empty _ _ (folded_lf rest col)))
lemma double_multiline_document_node :
    DoubleQuoted 0 .flowIn ⟨['"', '\n', '"'], 0⟩ ⟨[], 1⟩ := by
  exact .mk _ _ _ _ (.mk _ _) (double_flow_break ['"'] 1) (.mk _ _)
lemma single_multiline_document_node :
    SingleQuoted 0 .flowOut ⟨['\'', '\n', '\''], 0⟩ ⟨[], 1⟩ := by
  exact .mk _ _ _ _ (.mk _ _) (single_flow_break ['\''] 1) (.mk _ _)

lemma double_key_rejects_break (n col endCol : Nat) :
    ¬ DoubleText n .blockKey ⟨['\n'], col⟩ ⟨[], endCol⟩ := by
  intro h
  change DoubleBody _ _ at h
  cases h with
  | cons _ _ _ hc _ => cases hc <;> simp_all [NbJson]
lemma single_key_rejects_break (n col endCol : Nat) :
    ¬ SingleText n .flowKey ⟨['\n'], col⟩ ⟨[], endCol⟩ := by
  intro h
  change SingleBody _ _ at h
  cases h with
  | cons _ _ _ hc _ => cases hc <;> simp_all [NbJson]
lemma crlf_not_split (col : Nat) :
    ¬ Break ⟨['\r', '\n'], col⟩ ⟨['\n'], 0⟩ := by
  intro h
  cases h <;> simp_all

-- Exact consumer types at all positions; no assumed scanner success.
lemma double_key_reuse (n : Nat) (s t : SurfPos) :
    DoubleText n .blockKey s t ↔ GStar L4YAML.Proofs.Acceptance.DQCharOk s t :=
  double_body_reuse s t
lemma single_key_reuse (n : Nat) (s t : SurfPos) :
    SingleText n .flowKey s t ↔ GStar L4YAML.Proofs.Acceptance.SQCharOk s t :=
  single_body_reuse s t
lemma unsupported_context_excluded (n : Nat) (s t : SurfPos) :
    ¬ DoubleText n .blockIn s t ∧ ¬ SingleText n .blockOut s t := by
  simp [DoubleText, SingleText]

#check double_key_reuse
#check single_key_reuse
#check double_multiline_document_node
#check single_multiline_document_node
#check double_key_rejects_break
#check single_key_rejects_break
open Lean Elab Command in
run_cmd do
  for n in [``double_flow_break, ``single_flow_break, ``double_multiline_document_node,
      ``single_multiline_document_node, ``double_key_rejects_break, ``single_key_rejects_break,
      ``crlf_not_split, ``double_key_reuse, ``single_key_reuse, ``unsupported_context_excluded] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"EXACT_QUOTED_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.ExactQuotedChecks
