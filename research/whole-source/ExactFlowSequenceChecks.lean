module

public import ExactFlowSequence
public meta import Lean

set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactFlowSequenceChecks

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open MathGraph.WholeSource.ExactFlowSequence
open MathGraph.WholeSource.ExactPlain (Plain)
open MathGraph.WholeSource.ExactQuoted

private lemma no_first_comma (ctx : YamlContext) (rest : List Char) (col : Nat) (t : SurfPos) :
    ¬ SNsPlainFirst ctx ⟨',' :: rest, col⟩ t := by
  intro h
  cases h with
  | nonIndicator _ _ _ _ h => exact h (by decide)

private lemma no_plain_comma (ctx : YamlContext) (rest : List Char) (col : Nat) (t : SurfPos)
    (h : SNsPlainOneLine ctx ⟨',' :: rest, col⟩ t) : False := by
  cases h with
  | mk _ _ hFirst _ => exact no_first_comma _ _ _ _ hFirst

lemma no_leading_comma (n : Nat) (ctx : YamlContext) (rest : List Char) (col : Nat) (t : SurfPos) :
    ¬ Body n ctx ⟨',' :: rest, col⟩ t := by
  intro h
  cases h with
  | close h => cases h
  | entry h _ _ =>
    cases h with
    | plain h =>
      cases ctx <;> simp only [Plain] at h
      all_goals
        first
        | exact h
        | exact no_plain_comma _ _ _ _ h
        | cases h with
          | mk _ _ hLine _ => exact no_plain_comma _ _ _ _ hLine
    | single h => cases h with | mk _ _ _ h _ _ => cases h
    | double h => cases h with | mk _ _ _ h _ _ => cases h
    | sequence _ h _ _ => cases h

private lemma no_inline_at_colon (rest : List Char) (col : Nat) (t : SurfPos) :
    ¬ SSeparateInLine ⟨':' :: rest, col + 1⟩ t := by
  intro h
  cases h with
  | whites _ _ h => cases h with | mk _ _ h _ => cases h

private lemma no_separate_at_colon (n : Nat) (ctx : YamlContext) (rest : List Char)
    (col : Nat) (t : SurfPos) : ¬ Separate n ctx ⟨':' :: rest, col + 1⟩ t := by
  intro h
  cases ctx <;> simp only [Separate] at h
  all_goals
    first
    | exact no_inline_at_colon rest col t h
    | cases h with
      | right h => exact no_inline_at_colon rest col t h
      | left h =>
        cases h with | mk _ _ hComments _ =>
          cases hComments with | mk _ _ hStart _ =>
            cases hStart with
            | right h => exact Nat.noConfusion h.1
            | left h =>
              cases h with | mk _ _ hBefore hEnd =>
                cases hBefore with
                | none =>
                  cases hEnd with
                  | left h => cases h
                  | right h => cases h.1
                | some _ h =>
                  cases h with | mk _ _ hInline _ => exact no_inline_at_colon rest col _ hInline

lemma colon_cannot_be_owned_delimiter (n : Nat) (ctx : YamlContext) (rest : List Char)
    (col : Nat) (delimiter t : SurfPos)
    (hSep : GOpt (Separate n ctx) ⟨':' :: rest, col + 1⟩ delimiter) :
    ¬ AfterEntry n ctx delimiter t := by
  intro h
  cases hSep with
  | none =>
    obtain ⟨c, _, hChars, hKind⟩ := after_entry_indicator h
    have hc : ':' = c := (List.cons.inj hChars).1
    subst c
    cases hKind <;> contradiction
  | some _ h => exact no_separate_at_colon n ctx rest col _ h

private lemma plain_a (rest : List Char) (col : Nat) :
    Plain 0 .flowIn ⟨'a' :: rest, col⟩ ⟨rest, col + 1⟩ :=
  .mk _ _ _ (.mk _ _ _ _ (.nonIndicator _ _ _ _ (by
    unfold isNsPlainSafe isNsChar
    decide) (by decide)) (.nil _)) (.nil _)

private lemma empty_single (rest : List Char) (col : Nat) :
    SingleQuoted 0 .flowIn ⟨'\'' :: '\'' :: rest, col⟩ ⟨rest, col + 2⟩ :=
  .mk _ _ _ _ (.mk _ _) (.mk _ _ _ (.nil _) (.right _ _ (.nil _))) (.mk _ _)

/-- A plain entry and a recursively nested quoted entry with trailing commas. -/
lemma mixed_nested :
    Node 0 .flowOut ⟨"[[a,],['',],]".toList, 0⟩ ⟨[], 13⟩ := by
  change Node 0 .flowOut ⟨['[', '[', 'a', ',', ']', ',', '[', '\'', '\'', ',', ']', ',', ']'], 0⟩ ⟨[], 13⟩
  exact .sequence trivial (.mk _ _) (.none _) (.entry
    (.sequence trivial (.mk _ _) (.none _) (.entry (.plain (plain_a _ _))
      (.none _) (.comma (.mk _ _) (.none _) (.close (.mk _ _)))))
    (.none _) (.comma (.mk _ _) (.none _) (.entry
      (.sequence trivial (.mk _ _) (.none _) (.entry (.single (empty_single _ _))
        (.none _) (.comma (.mk _ _) (.none _) (.close (.mk _ _)))))
      (.none _) (.comma (.mk _ _) (.none _) (.close (.mk _ _))))))

lemma commented_empty :
    Node 1 .flowOut ⟨['[', ' ', '#', '\r', '\n', ' ', ']'], 0⟩ ⟨[], 2⟩ := by
  let afterOpen : SurfPos := ⟨[' ', '#', '\r', '\n', ' ', ']'], 1⟩
  let afterComment : SurfPos := ⟨['\r', '\n', ' ', ']'], 3⟩
  let afterBreak : SurfPos := ⟨[' ', ']'], 0⟩
  let beforeClose : SurfPos := ⟨[']'], 1⟩
  have hComment : SeparatedComment afterOpen afterComment :=
    .mk _ _ _ (.whites _ _ (.mk _ _ _ (.space _ _) (.nil _)))
      (.some _ _ (.mk _ _ _ (.nil _)))
  have hComments : CommentLines afterOpen afterBreak :=
    .mk _ _ _ (.left _ _ (.mk _ _ _ (.some _ _ hComment) (.left _ _ (.crlf _ _)))) (.nil _)
  have hPrefix : SFlowLinePrefix 1 afterBreak beforeClose :=
    .mk _ _ _ _ (.succ _ _ _ _ (.zero _)) (.none _)
  exact .sequence trivial (.mk _ _) (.some _ _ (.left _ _ (.mk _ _ _ hComments hPrefix)))
    (.close (.mk _ _))

lemma key_cannot_cross_break (n col : Nat) (rest : List Char) :
    ¬ GOpt (Separate n .flowKey) ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩ := by
  intro h
  have hw := key_separation_whites h
  cases hw with
  | cons => cases ‹SSWhite _ _›

#check scan_plain_before_after_entry
open Lean Elab Command in
run_cmd do
  for n in [``after_entry_indicator, ``key_separation_whites, ``scan_plain_before_after_entry,
      ``no_leading_comma, ``colon_cannot_be_owned_delimiter, ``mixed_nested, ``commented_empty,
      ``key_cannot_cross_break] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"EXACT_FLOW_SEQUENCE_AXIOMS {n}: {axs}"

end MathGraph.WholeSource.ExactFlowSequenceChecks
