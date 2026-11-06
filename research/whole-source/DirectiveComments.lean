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
  | zero => simp [skipToEndOfLineLoop, collectRun]
  | succ n ih =>
    cases hp : sc.peek? with
    | none => simp [skipToEndOfLineLoop, collectRun, hp]
    | some c =>
      cases hb : isLineBreakBool c
      · simpa only [skipToEndOfLineLoop, collectRun, hp, hb, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] using ih sc.advance (acc.push c)
      · simp [skipToEndOfLineLoop, collectRun, hp, hb]

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
    by_cases h : s.offset < s.inputEnd
    · simp only [h, ite_true]
      split <;> (try split) <;> rfl
    · simp only [h, ite_false]
  induction fuel generalizing sc with
  | zero => simp [skipToEndOfLineLoop]
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
    rw [← hcws.col_eq, ← hlast.col_eq]
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

lemma yaml_comment_dispatch (sc : ScannerState) (major minor comment rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hcorr : ScannerSurfCorr sc
      ⟨'%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' :: (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: rest))), 0⟩)
    (hallow : sc.allowDirectives = true) (hseen : sc.seenYamlDirective = false) :
    ∃ out, scanDirective sc = .ok out ∧
      ScannerSurfCorr out ⟨'\n' :: rest, 6 + major.length + 1 + minor.length + 1 + (1 + comment.length)⟩ ∧
      out.tokens = sc.tokens.push { pos := sc.currentPos, val := .versionDirective (String.ofList major).toNat! (String.ofList minor).toNat! } ∧
      out.seenYamlDirective = true ∧ out.directivesPresent = true := by
  let body := major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: rest))
  have hcadv := advance_corr hcorr (by decide) (by decide)
  have hnameSyntax : LexRun isNsChar ['Y','A','M','L']
      ⟨'Y' :: 'A' :: 'M' :: 'L' :: ' ' :: body, 1⟩ ⟨' ' :: body, 5⟩ := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> unfold isNsChar <;> decide
    · intro c hc
      simp only [List.head?_cons, Option.some.injEq] at hc
      subst c
      intro hn
      exact hn.2.1 (by decide)
  have hfuel := fuel_of_corr hcadv
  have hiadv := (keeps_advance sc).2.1
  obtain ⟨name, sc₁, hname, hn, hc₁, hk₁⟩ := collectDirectiveNameLoop_accepts
    hnameSyntax sc.advance hcadv (sc.inputEnd - sc.advance.offset) (by
      simpa only [body, hiadv, Nat.lt_succ_iff] using hfuel)
  have hn' : name = "YAML" := by simpa using hn
  subst name
  have hsep : LexRun isWhiteSpaceProp [' '] ⟨' ' :: body, 5⟩ ⟨body, 6⟩ := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro c hc; simp only [List.mem_singleton] at hc; subst c; decide
    · cases major with
      | nil => exact False.elim (hneMa rfl)
      | cons c cs =>
        intro d hd
        simp only [body, List.cons_append, List.head?_cons, Option.some.injEq] at hd
        subst d
        exact digit_not_white (hma c (by simp))
  obtain ⟨hc₂, hk₂⟩ := whitespace_accepts hsep sc₁ hc₁
  have hlim : sc.inputEnd = (skipWhitespace sc₁).inputEnd := by
    rw [hk₂.2.1, hk₁.2.1, hiadv]
  obtain ⟨out, hok, hco, htok, hs, hd⟩ := yaml_body_before_comment sc (skipWhitespace sc₁)
    major minor (comment ++ '\n' :: rest) hma hmi hneMa hneMi 6 hc₂ hlim hseen
  obtain ⟨hland, hkland, hctx⟩ := comment_landing out ('#' :: comment) rest
    (6 + major.length + 1 + minor.length + 1) (by
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · decide
      · exact hcomment c hc) hco
  refine ⟨skipToEndOfLine out, ?_, ?_, ?_, ?_, ?_⟩
  · unfold scanDirective
    simp only [hallow, Bool.not_true, Bool.false_eq_true, ite_false, hname]
    simp only [show ("YAML" == "YAML") = true from rfl, ite_true, hok]

  · simpa [List.length_cons, Nat.add_comm] using hland
  · rw [hkland.1, htok, hk₂.1, hk₁.1, (keeps_advance sc).1]
  · exact hctx.seenYamlDirective.trans hs
  · exact (skip_preserves_present out _).trans hd


/-- End-to-end directive consumer from original source; the suffix is not parsed. -/
lemma original_comment_declaration (input : String) (major minor comment rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: rest)))) :
    ∃ out, scanDirective (ScannerState.mk' input) = .ok out ∧
      (L4YAML.TokenParser.parseDirectives (L4YAML.TokenParser.ParseState.mk' out.tokens)).1 =
        #[.yaml (toString (String.ofList major).toNat! ++ "." ++ toString (String.ofList minor).toNat!)] ∧
      out.seenYamlDirective = true ∧ out.directivesPresent = true := by
  have hc := initial_corr input input.toList (chars_from_zero_toList input)
  rw [hsource] at hc
  obtain ⟨out, hok, _, ht, hs, hd⟩ := yaml_comment_dispatch (ScannerState.mk' input)
    major minor comment rest hma hmi hneMa hneMi hcomment hc rfl rfl
  refine ⟨out, hok, ?_, hs, hd⟩
  have ht' : out.tokens = #[{ pos := (ScannerState.mk' input).currentPos, val := .versionDirective (String.ofList major).toNat! (String.ofList minor).toNat! }] := by
    simpa [ScannerState.mk'] using ht
  rw [ht']
  exact parser_consumes_version _ _ _

/-- Inserting a separated comment preserves the actual declaration answer.
This compares actual runtime consumers on two constructed original inputs;
it does not infer semantic equality merely from equal acceptance. -/
lemma comment_insertion_preserves_declaration (major minor comment rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r') :
    ∃ plainOut commentOut,
      scanDirective (ScannerState.mk' (String.ofList
        ('%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' :: (major ++ '.' :: (minor ++ '\n' :: rest))))) = .ok plainOut ∧
      scanDirective (ScannerState.mk' (String.ofList
        ('%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' :: (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: rest)))))) = .ok commentOut ∧
      (L4YAML.TokenParser.parseDirectives (L4YAML.TokenParser.ParseState.mk' plainOut.tokens)).1 =
      (L4YAML.TokenParser.parseDirectives (L4YAML.TokenParser.ParseState.mk' commentOut.tokens)).1 := by
  obtain ⟨plainOut, hp, hv⟩ := original_yaml_declaration
    (String.ofList ('%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' :: (major ++ '.' :: (minor ++ '\n' :: rest))))
    major minor rest hma hmi hneMa hneMi (String.toList_ofList _)
  obtain ⟨commentOut, hc, hw, _, _⟩ := original_comment_declaration
    (String.ofList ('%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' :: (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: rest)))))
    major minor comment rest hma hmi hneMa hneMi hcomment (String.toList_ofList _)
  exact ⟨plainOut, commentOut, hp, hc, hv.trans hw.symm⟩

#print axioms comment_insertion_preserves_declaration
#print axioms original_comment_declaration
#print axioms yaml_comment_dispatch
#print axioms skip_eq_collect
#print axioms comment_landing
#print axioms skip_preserves_present
#print axioms yaml_body_before_comment
end
end MathGraph.WholeSource.DirectiveComments
