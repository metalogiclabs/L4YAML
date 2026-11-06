module
public import DirectiveDispatch
public meta import L4YAML.Parser.Composition

/-!
# Comment termination for original-source directives

Capstone path: independent comment source → exact scanner landing → directive
composition → Group 7.7 grammar completeness. Runtime sidecar only. Comment
characters exclude CR/LF; printable-character fidelity is not claimed here.
-/
namespace MathGraph.WholeSource.DirectiveComments
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open MathGraph.WholeSource.DirectiveBridge
open MathGraph.WholeSource.DirectiveTransfer
open MathGraph.WholeSource.DirectiveDispatch

private def accepts (s : String) : Bool := (L4YAML.TokenParser.parseYaml s).toOption.isSome
#guard accepts "%YAML 1.2 #\n---" = true
#guard accepts "%YAML 1.2 # café λ\n---" = true
#guard accepts "%YAML 1.2#bad\n---" = false
#guard accepts "%YAML 1.2 #a\r\n---" = true
#guard accepts "%YAML 1.2 #a\n%YAML 1.2 #b\n---" = false
#guard accepts "%TAG !e! tag:example.org,2026: # café\n--- !e!x value" = true
#guard (skipToEndOfLineLoop (ScannerState.mk' "a\n") 0).offset = 0
#guard (skipToEndOfLineLoop (ScannerState.mk' "a\n") 1).offset = 1
#guard (skipToEndOfLineLoop (ScannerState.mk' "é\n") 2).offset = 2

/-- The runtime discards the spelling but follows exactly the retained generic
collector. This lets its source-landing proof be reused without new induction. -/
lemma skip_eq_collect (sc : ScannerState) (acc : String) (fuel : Nat) :
    skipToEndOfLineLoop sc fuel = (collectRun (fun c => !isLineBreakBool c) sc acc fuel).2 := by
  induction fuel generalizing sc acc with
  | zero => rfl
  | succ n ih =>
    cases hp : sc.peek? with
    | none => simp [skipToEndOfLineLoop, collectRun, hp]
    | some c =>
      cases hb : isLineBreakBool c <;>
        simp [skipToEndOfLineLoop, collectRun, hp, hb, ih]

lemma not_break_test (c : Char) :
    (!isLineBreakBool c) = true ↔ c ≠ '\n' ∧ c ≠ '\r' := by
  simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool]

lemma comment_landing (sc : ScannerState) (cs rest : List Char) (col : Nat)
    (hcs : ∀ c ∈ cs, c ≠ '\n' ∧ c ≠ '\r')
    (hc : ScannerSurfCorr sc ⟨cs ++ '\n' :: rest, col⟩) :
    ScannerSurfCorr (skipToEndOfLine sc) ⟨'\n' :: rest, col + cs.length⟩ ∧
      Keeps sc (skipToEndOfLine sc) ∧ DirectiveContextKeeps sc (skipToEndOfLine sc) := by
  have hs : Stops (fun c => c ≠ '\n' ∧ c ≠ '\r') ('\n' :: rest) := by
    intro c he; simp only [List.head?_cons, Option.some.injEq] at he
    subst c; simp
  have hf := fuel_of_corr hc
  obtain ⟨out, last, heq, _, hlast, hk⟩ := collectRun_accepts
    (fun c => c ≠ '\n' ∧ c ≠ '\r') (fun c => !isLineBreakBool c)
    not_break_test (fun _ h => h) cs hcs ('\n' :: rest) hs sc "" col
    (sc.inputEnd - sc.offset) hc (by simp only [List.length_append, List.length_cons] at hf; omega)
  have he : skipToEndOfLine sc = last := by
    unfold skipToEndOfLine
    rw [skip_eq_collect sc "", heq]
  have hctx := collectRun_directiveContext (fun c => !isLineBreakBool c) sc "" (sc.inputEnd - sc.offset)
  rw [heq] at hctx
  rw [he]
  exact ⟨hlast, hk, hctx⟩

lemma skip_preserves_present (sc : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop sc fuel).directivesPresent = sc.directivesPresent := by
  have ha (s : ScannerState) : s.advance.directivesPresent = s.directivesPresent := by
    unfold ScannerState.advance
    split <;> (try split) <;> (try split) <;> rfl
  induction fuel generalizing sc with
  | zero => rfl
  | succ n ih =>
    cases hp : sc.peek? with
    | none => simp [skipToEndOfLineLoop, hp]
    | some c =>
      simp only [skipToEndOfLineLoop, hp]
      split
      · rfl
      · exact (ih _).trans (ha _)

/-- The body accepts a separated comment and stops at its initial hash. -/
lemma yaml_body_before_comment (origin sc : ScannerState) (major minor rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ []) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨major ++ '.' :: (minor ++ ' ' :: '#' :: rest), col⟩)
    (hlimit : origin.inputEnd = sc.inputEnd) (hseen : origin.seenYamlDirective = false) :
    ∃ out, scanYamlDirective origin sc origin.currentPos = .ok out ∧
      ScannerSurfCorr out ⟨'#' :: rest, col + major.length + 1 + minor.length + 1⟩ ∧
      out.tokens = sc.tokens.push { pos := origin.currentPos, val := .versionDirective (String.ofList major).toNat! (String.ofList minor).toNat! } ∧
      out.seenYamlDirective = true ∧ out.directivesPresent = true := by
  have hs : Stops isNsDecDigit (' ' :: '#' :: rest) := by
    intro c hc
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst c
    simp [isNsDecDigit]
  obtain ⟨ma, middle, mi, last, heqMa, heqMi, hma', hmi', hlast, hk⟩ :=
    version_digits_accepts major minor (' ' :: '#' :: rest) hma hmi hs sc col hcorr
  have hmaEq : ma = String.ofList major := by
    rw [← String.toList_inj, String.toList_ofList]; exact hma'
  have hmiEq : mi = String.ofList minor := by
    rw [← String.toList_inj, String.toList_ofList]; exact hmi'
  subst ma; subst mi
  have hnonempty (cs : List Char) (hne : cs ≠ []) : (String.ofList cs).isEmpty = false := by
    apply String.isEmpty_eq_false_iff.mpr
    intro he
    have hh := congrArg String.toList he
    simp only [String.toList_ofList, String.toList_empty] at hh
    exact hne hh
  have hsep : LexRun isWhiteSpaceProp [' ']
      ⟨' ' :: '#' :: rest, col + major.length + 1 + minor.length⟩
      ⟨'#' :: rest, col + major.length + 1 + minor.length + 1⟩ := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro c hc; simp only [List.mem_singleton] at hc; subst c; decide
    · intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc; subst c; decide
  obtain ⟨hcws, hkws⟩ := whitespace_accepts hsep last hlast
  have hp := (peek_of_corr hcws).1
  have hcols : ((skipWhitespace last).col == last.col) = false := by
    rw [hcws.col_eq, hlast.col_eq]
    simp
  let final := { (skipWhitespace last).emitAt origin.currentPos
      (.versionDirective (String.ofList major).toNat! (String.ofList minor).toNat!) with
        seenYamlDirective := true, directivesPresent := true }
  have hfinal : ScannerSurfCorr final ⟨'#' :: rest, col + major.length + 1 + minor.length + 1⟩ := by
    have he := L4YAML.Proofs.ScalarCoupling.corr_of_emitAt origin.currentPos
      (.versionDirective (String.ofList major).toNat! (String.ofList minor).toNat!) hcws
    exact ⟨he.chars_from, he.col_eq, he.end_eq, he.input_prefix, he.indent_cols_nonneg⟩
  refine ⟨final, ?_, hfinal, ?_, rfl, rfl⟩
  · unfold scanYamlDirective
    simp [hseen, hlimit, heqMa, heqMi, hp, hcols, hnonempty major hneMa,
      hnonempty minor hneMi, final]
  · simp only [final, ScannerState.emitAt]
    rw [hkws.1, hk.1]

#print axioms skip_eq_collect
#print axioms comment_landing
#print axioms skip_preserves_present
#print axioms yaml_body_before_comment
end
end MathGraph.WholeSource.DirectiveComments
