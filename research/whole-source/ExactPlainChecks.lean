module

public import ExactPlain
public meta import Lean

set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactPlainChecks

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open MathGraph.WholeSource.ExactPlain MathGraph.WholeSource.ExactQuoted

/-! Group 7.7 boundary controls pin the remaining source suffix. -/

local instance (ctx : YamlContext) (ch : Char) : Decidable (isNsPlainSafe ctx ch) := by
  cases ctx <;> unfold isNsPlainSafe isNsChar <;> infer_instance

private lemma starts_a (ctx : YamlContext) (rest : List Char) :
    SNsPlainFirst ctx ⟨'a' :: rest, 0⟩ ⟨rest, 1⟩ :=
  .nonIndicator _ _ _ _ (by cases ctx <;> decide) (by decide)

private lemma ends_before (ctx : YamlContext) (rest : List Char) :
    SNsPlainOneLine ctx ⟨'a' :: rest, 0⟩ ⟨rest, 1⟩ :=
  .mk _ _ _ _ (starts_a ctx rest) (.nil _)

private lemma final_b (ctx : YamlContext) (col : Nat) :
    GStar (SNbNsPlainInLineEntry ctx) ⟨['b'], col⟩ ⟨[], col + 1⟩ :=
  .cons _ _ _ (.mk _ _ _ _ (.nil _) (.safe _ 'b' [] col (by cases ctx <;> decide)
    (by decide) (by decide))) (.nil _)

/-- The full scalar and its strict prefix are both grammatical spans.
A caller must derive the stop condition from the remaining source. -/
lemma colon_has_two_spans :
    Plain 0 .flowKey ⟨['a', ':', 'b'], 0⟩ ⟨[], 3⟩ ∧
    Plain 0 .flowKey ⟨['a', ':', 'b'], 0⟩ ⟨[':', 'b'], 1⟩ :=
  ⟨.mk _ _ _ _ (starts_a _ _) (.cons _ _ _
    (.mk _ _ _ _ (.nil _) (.colonSafe _ 'a' 'b' [] 1 (by decide))) (final_b _ 2)),
    ends_before _ _⟩

lemma hash_content :
    Plain 0 .flowKey ⟨['a', '#', 'b'], 0⟩ ⟨[], 3⟩ :=
  .mk _ _ _ _ (starts_a _ _) (.cons _ _ _ (.hash _ _ _ (.mk ['b'] 1)) (final_b _ 2))

private lemma stops_after_a (ctx : YamlContext) (rest : List Char)
    (hRest : ∀ t, ¬ SNbNsPlainInLineEntry ctx ⟨rest, 1⟩ t) {t : SurfPos}
    (h : SNsPlainOneLine ctx ⟨'a' :: rest, 0⟩ t) : t = ⟨rest, 1⟩ := by
  cases h with
  | mk _ _ hFirst hTail =>
    cases hFirst
    cases hTail with
    | nil => rfl
    | cons _ _ _ he _ => exact False.elim (hRest _ he)

lemma colon_before_space_stops (rest : List Char) :
    Plain 0 .flowKey ⟨'a' :: ':' :: ' ' :: rest, 0⟩ ⟨':' :: ' ' :: rest, 1⟩ ∧
      ∀ t, Plain 0 .flowKey ⟨'a' :: ':' :: ' ' :: rest, 0⟩ t →
        t = ⟨':' :: ' ' :: rest, 1⟩ := by
  refine ⟨ends_before _ _, fun _ h => stops_after_a _ _ ?_ h⟩
  intro t he
  cases he with
  | mk _ _ hw hc =>
    cases hw with
    | nil =>
      cases hc with
      | safe _ _ _ _ hn _ => exact hn rfl
      | colonSafe _ _ _ _ hs => exact (by decide : ¬ isNsPlainSafe .flowKey ' ') hs
    | cons _ _ _ h _ => cases h
  | hash _ hh => cases hh

lemma separated_hash_stops (rest : List Char) :
    Plain 0 .flowKey ⟨'a' :: ' ' :: '#' :: rest, 0⟩ ⟨' ' :: '#' :: rest, 1⟩ ∧
      ∀ t, Plain 0 .flowKey ⟨'a' :: ' ' :: '#' :: rest, 0⟩ t →
        t = ⟨' ' :: '#' :: rest, 1⟩ := by
  refine ⟨ends_before _ _, fun _ h => stops_after_a _ _ ?_ h⟩
  intro t he
  cases he with
  | mk _ _ hw hc =>
    cases hw with
    | nil => cases hc with | safe _ _ _ hs _ _ => exact (by decide : ¬ isNsPlainSafe .flowKey ' ') hs
    | cons _ _ _ h hRest =>
      cases h
      cases hRest with
      | nil => cases hc with | safe _ _ _ _ _ hn => exact hn rfl
      | cons _ _ _ hh _ => cases hh
  | hash _ hh => cases hh

lemma closing_bracket_context :
    Plain 0 .blockKey ⟨['a', ']', 'b'], 0⟩ ⟨[], 3⟩ ∧
    Plain 0 .flowKey ⟨['a', ']', 'b'], 0⟩ ⟨[']', 'b'], 1⟩ ∧
    ∀ t, Plain 0 .flowKey ⟨['a', ']', 'b'], 0⟩ t → t = ⟨[']', 'b'], 1⟩ := by
  refine ⟨.mk _ _ _ _ (starts_a _ _) (.cons _ _ _
    (.mk _ _ _ _ (.nil _) (.safe _ ']' ['b'] 1 (by decide) (by decide) (by decide))) (final_b _ 2)),
    ends_before _ _, fun _ h => stops_after_a _ _ ?_ h⟩
  intro t he
  cases he with
  | mk _ _ hw hc =>
    cases hw with
    | nil => cases hc with | safe _ _ _ hs _ _ => exact (by decide : ¬ isNsPlainSafe .flowKey ']') hs
    | cons _ _ _ h _ => cases h
  | hash _ hh => cases hh

lemma multiline_flow_crlf :
    Plain 1 .flowIn ⟨['a', '\r', '\n', ' ', 'b'], 0⟩ ⟨[], 2⟩ :=
  .mk _ _ _ (ends_before _ _) (.cons _ _ _
    (.mk _ _ _ _
      (.mk _ _ _ _ (.none _) (.right _ _ (.crlf _ _))
        (.mk _ _ _ _ (.succ _ _ _ _ (.zero _)) (.none _)))
      (.safe _ 'b' [] 1 (by decide) (by decide) (by decide)) (.nil _))
    (.nil _))

lemma key_stops_before_crlf (n : Nat) (ctx : YamlContext)
    (hCtx : ctx = .blockKey ∨ ctx = .flowKey) (rest : List Char) :
    Plain n ctx ⟨'a' :: '\r' :: '\n' :: rest, 0⟩ ⟨'\r' :: '\n' :: rest, 1⟩ ∧
      ∀ t, Plain n ctx ⟨'a' :: '\r' :: '\n' :: rest, 0⟩ t → t = ⟨'\r' :: '\n' :: rest, 1⟩ := by
  have hStop : ∀ t, ¬ SNbNsPlainInLineEntry ctx ⟨'\r' :: '\n' :: rest, 1⟩ t := by
    intro t he
    cases he with
    | mk _ _ hw hc =>
      cases hw with
      | nil =>
        cases hc with
        | safe _ _ _ hs _ _ => rcases hCtx with rfl | rfl <;> exact (by decide : ¬ isNsPlainSafe _ '\r') hs
      | cons _ _ _ h _ => cases h
    | hash _ hh => cases hh
  rcases hCtx with rfl | rfl <;> exact ⟨ends_before _ _, fun _ h => stops_after_a _ _ hStop h⟩

#check one_line_to_guarded
#check scan_flow_plain_to_indicator
open Lean Elab Command in
run_cmd do
  for n in [``colon_has_two_spans, ``hash_content, ``colon_before_space_stops, ``separated_hash_stops,
      ``closing_bracket_context, ``multiline_flow_crlf, ``key_stops_before_crlf, ``one_line_to_guarded,
      ``scan_flow_plain_to_indicator] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"EXACT_PLAIN_AXIOMS {n}: {axs}"

end MathGraph.WholeSource.ExactPlainChecks
