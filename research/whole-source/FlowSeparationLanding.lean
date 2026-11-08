module

public import FlowCloseLanding
public import L4YAML.Proofs.Production.Acceptance.BlockScalar
public import L4YAML.Proofs.Production.Acceptance.Properties
public import L4YAML.Proofs.Scanner.ScanStrictCoupling
public meta import Lean

/-! Group 7.7, production [137]. Derive the close landing for arbitrary
flow whitespace and comment lines at the stream indentation floor. -/

@[expose] public section
namespace MathGraph.WholeSource.FlowSeparationLanding

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.ScannerCoupling L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.ScanStrictCoupling
open MathGraph.WholeSource.FlowCloseLanding

/-- A sequence of whitespace runs separated by YAML breaks. CRLF is one
break, enforced by `SBBreakOk`. A comment requires inline separation
or a start-of-line position. Closing bracket indentation is checked by the caller. -/
inductive FlowCloseSeparation : SurfPos → SurfPos → Prop where
  | inline {start stop} : GStar SSWhite start stop → FlowCloseSeparation start stop
  | next {start atBreak nextLine stop} :
      GStar SSWhite start atBreak → SBBreakOk atBreak nextLine →
      FlowCloseSeparation nextLine stop → FlowCloseSeparation start stop

  | commented {start rest hashCol atBreak nextLine stop} :
      SSeparateInLine start ⟨'#' :: rest, hashCol⟩ →
      GStar (GChar CommentCharOk) ⟨rest, hashCol + 1⟩ atBreak →
      SBBreakOk atBreak nextLine → FlowCloseSeparation nextLine stop →
      FlowCloseSeparation start stop

private def multilineWhitespaceControl : Bool := Id.run do
  let initial := (ScannerState.mk' "[[\"a\" \r\n\t\r \n\t ], x]").emit .streamStart
  let .ok (some outer) := scanNextToken initial | return false
  let .ok (some inner) := scanNextToken outer | return false
  let .ok (some child) := scanNextToken inner | return false
  let .ok (some closed) := scanNextToken child | return false
  return child.peek? == some ' ' && closed.peek? == some ',' &&
    closed.line == child.line + 3 && closed.col == 3 &&
    closed.flowLevel == 1 && closed.simpleKey.possible &&
    closed.simpleKey.tokenIndex == (child.simpleKeyStack.back?.getD {}).tokenIndex

#guard multilineWhitespaceControl
#guard (TokenParser.parseYaml "[[\"a\" # inline\r\n# next\n\t ], x]").isOk

private lemma whitespace_in_flow (s : ScannerState)
    (hFlow : s.inFlow = true) (hIndent : s.currentIndent < 0) :
    skipToContentWs s = .ok (skipWhitespace s) := by
  have hFlowSpace : (skipSpaces s).inFlow = true := by
    simpa only [ScannerState.inFlow, skipSpaces_preserves_flowLevel] using hFlow
  have hIndentSpace : (skipSpaces s).currentIndent = s.currentIndent := by
    simp only [ScannerState.currentIndent,
      L4YAML.Proofs.PreprocessIndentStable.skipSpaces_preserves_indents]
  simp [skipToContentWs, hFlowSpace, hIndentSpace,
    show ¬ ((skipSpaces s).col : Int) ≤ s.currentIndent from by omega,
    skipWhitespace_skipSpaces]

private lemma at_break {s : ScannerState} {a b : SurfPos}
    (hBreak : SBBreakOk a b) (hCorr : ScannerSurfCorr s a) :
    ∃ c, s.peek? = some c ∧ isLineBreakBool c = true ∧ c ≠ '#' := by
  cases hBreak
  · exact ⟨'\n', (peek_of_corr hCorr).1, by decide, by decide⟩
  · exact ⟨'\r', (peek_of_corr hCorr).1, by decide, by decide⟩
  · exact ⟨'\r', (peek_of_corr hCorr).1, by decide, by decide⟩

private lemma skip_comment (s : ScannerState) {start atBreak : SurfPos}
    {rest : List Char} {hashCol : Nat} (hSource : ScannerSurfCorr s start)
    (hWhite : SSeparateInLine start ⟨'#' :: rest, hashCol⟩)
    (hText : GStar (GChar CommentCharOk) ⟨rest, hashCol + 1⟩ atBreak)
    (hStop : ∀ c, atBreak.chars.head? = some c → isLineBreakBool c = true) :
    ScannerSurfCorr (skipToContentComment (skipWhitespace s)) atBreak ∧
      atBreak.chars.length < start.chars.length := by
  have hStar : GStar SSWhite start ⟨'#' :: rest, hashCol⟩ := by
    cases hWhite with
    | whites _ _ h => exact GPlus.toGStar h
    | startOfLine => exact .nil _
  obtain ⟨hHash, _⟩ := skipWhitespace_accepts s hStar hSource (by simp) (by simp)
  have hPeek := (peek_of_corr hHash).1
  have hEligible : ((skipWhitespace s).col == 0 ||
      match (skipWhitespace s).peekBack? with
      | some c => isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF'
      | none => true) = true := by
    cases hWhite with
    | whites _ _ h =>
      obtain ⟨w, hBack, hWhiteChar⟩ := peekBack_white_of_whites hSource hHash
        (skipWhitespace_input s) h
      simp [hBack, hWhiteChar]
    | startOfLine =>
      have hCol : (skipWhitespace s).col = 0 := hHash.col_eq.symm
      simp [hCol]
  let afterHash := (skipWhitespace s).advance
  have hAfterHash : ScannerSurfCorr afterHash ⟨rest, hashCol + 1⟩ :=
    advance_corr hHash (by decide) (by decide)
  obtain ⟨hAtBreak, _⟩ := collectCommentTextLoop_accepts hText hStop afterHash ""
    (afterHash.inputEnd - afterHash.offset) hAfterHash (by have := fuel_of_corr hAfterHash; omega)
  generalize hCollect : collectCommentTextLoop afterHash ""
    (afterHash.inputEnd - afterHash.offset) = collected at hAtBreak
  obtain ⟨text, parked⟩ := collected
  have hComment : skipToContentComment (skipWhitespace s) =
      { parked with comments := parked.comments.push ((skipWhitespace s).currentPos, text) } := by
    unfold skipToContentComment
    simp only [hPeek, show (skipWhitespace s).advance = afterHash from rfl, hCollect]
    cases hBack : (skipWhitespace s).peekBack? <;>
      simp_all
  refine ⟨hComment ▸ corr_of_comments hAtBreak _, ?_⟩
  have hWhiteLen := GStar_SSWhite_length hStar
  have hTextLen := GStar_GChar_length hText
  simp at hWhiteLen hTextLen
  omega

private lemma skip_loop {start : SurfPos} (c : Char) (tail : List Char) (col : Nat)
    (hSpace : c ≠ ' ') (hTab : c ≠ '\t') (hHash : c ≠ '#')
    (hBreakChar : isLineBreakBool c = false)
    (hGrammar : FlowCloseSeparation start ⟨c :: tail, col⟩) :
    ∀ (s : ScannerState) (fuel : Nat), ScannerSurfCorr s start →
      s.inFlow = true → s.currentIndent < 0 → start.chars.length ≤ fuel →
      ∃ land, skipToContentLoop s fuel = .ok land ∧
        ScannerSurfCorr land ⟨c :: tail, col⟩ := by
  generalize hEnd : (⟨c :: tail, col⟩ : SurfPos) = stop at hGrammar ⊢
  induction hGrammar with
  | @inline start stop hWhite =>
    subst stop
    intro s fuel hCorr hFlow hIndent hFuel
    obtain ⟨hLand, _⟩ := skipWhitespace_accepts s hWhite hCorr (by simpa using hSpace) (by simpa using hTab)
    have hPeek := (peek_of_corr hLand).1
    have hComment : skipToContentComment (skipWhitespace s) = skipWhitespace s := by
      simp [skipToContentComment, hPeek, hHash]
    have hLen := GStar_SSWhite_length hWhite
    cases fuel with
    | zero => simp at hLen; omega
    | succ fuel =>
      exact ⟨skipWhitespace s, by
        simp only [skipToContentLoop, whitespace_in_flow s hFlow hIndent, hComment,
          hPeek, hBreakChar, Bool.false_eq_true,
          ite_false], hLand⟩
  | @next start atBreak nextLine stop hWhite hBreak _ ih =>
    intro s fuel hCorr hFlow hIndent hFuel
    have hBreakLen := hBreak.length_lt
    have hWhiteLen := GStar_SSWhite_length hWhite
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨hAtBreak, hKeepWhite⟩ := skipWhitespace_accepts s hWhite hCorr
        (by cases hBreak <;> simp) (by cases hBreak <;> simp)
      obtain ⟨c, hPeek, hLB, hNotComment⟩ := at_break hBreak hAtBreak
      let next := consumeNewline (skipWhitespace s)
      obtain ⟨hNext, hKeepNext⟩ := consumeNewline_accepts _ hBreak hAtBreak
      have hNextFlow : next.inFlow = true := by
        simpa only [next, ScannerState.inFlow,
          L4YAML.Proofs.ScannerCorrectness.consumeNewline_preserves_flowLevel,
          skipWhitespace_preserves_flowLevel] using hFlow
      have hNextIndent : next.currentIndent < 0 :=
        (hKeepWhite.trans hKeepNext).currentIndent ▸ hIndent
      obtain ⟨land, hLoop, hLand⟩ := ih hEnd next fuel hNext hNextFlow hNextIndent (by omega)
      have hComment : skipToContentComment (skipWhitespace s) = skipWhitespace s := by
        simp [skipToContentComment, hPeek, hNotComment]
      exact ⟨land, by
        simp only [skipToContentLoop, whitespace_in_flow s hFlow hIndent, hComment,
          hPeek, hLB, ite_true, show consumeNewline (skipWhitespace s) = next from rfl,
          hNextFlow, Bool.not_true, Bool.false_eq_true, ite_false, hLoop], hLand⟩

  | @commented start rest hashCol atBreak nextLine stop hWhite hText hBreak _ ih =>
    intro s fuel hCorr hFlow hIndent hFuel
    have hStop : ∀ c, atBreak.chars.head? = some c → isLineBreakBool c = true := by
      cases hBreak <;> simp <;> decide
    obtain ⟨hAtBreak, hCommentLen⟩ := skip_comment s hCorr hWhite hText hStop
    have hBreakLen := hBreak.length_lt
    cases fuel with
    | zero => omega
    | succ fuel =>
      let comment := skipToContentComment (skipWhitespace s)
      obtain ⟨c, hPeek, hLB, _⟩ := at_break hBreak hAtBreak
      change comment.peek? = some c at hPeek
      let next := consumeNewline comment
      obtain ⟨hNext, hKeepNext⟩ := consumeNewline_accepts comment hBreak hAtBreak
      have hNextFlow : next.inFlow = true := by
        simpa only [next, comment, ScannerState.inFlow,
          L4YAML.Proofs.ScannerCorrectness.consumeNewline_preserves_flowLevel,
          skipToContentComment_preserves_flowLevel, skipWhitespace_preserves_flowLevel] using hFlow
      have hNextIndent : next.currentIndent < 0 := by
        rw [hKeepNext.currentIndent]
        simpa only [comment, ScannerState.currentIndent,
          L4YAML.Proofs.PreprocessIndentStable.skipToContentComment_preserves_indents,
          L4YAML.Proofs.PreprocessIndentStable.skipWhitespace_preserves_indents] using hIndent
      obtain ⟨land, hLoop, hLand⟩ := ih hEnd next fuel hNext hNextFlow hNextIndent (by omega)
      exact ⟨land, by
        simp only [skipToContentLoop, whitespace_in_flow s hFlow hIndent,
          show skipToContentComment (skipWhitespace s) = comment from rfl,
          hPeek, hLB, ite_true, show consumeNewline comment = next from rfl,
          hNextFlow, Bool.not_true, Bool.false_eq_true, ite_false, hLoop], hLand⟩

lemma skip_flow_separation (s : ScannerState) {start : SurfPos} (c : Char)
    (tail : List Char) (col : Nat)
    (hSource : ScannerSurfCorr s start)
    (hGrammar : FlowCloseSeparation start ⟨c :: tail, col⟩)
    (hFlow : s.inFlow = true) (hIndent : s.currentIndent < 0)
    (hSpace : c ≠ ' ') (hTab : c ≠ '\t') (hHash : c ≠ '#')
    (hBreak : isLineBreakBool c = false) :
    ∃ land, skipToContent s = .ok land ∧ ScannerSurfCorr land ⟨c :: tail, col⟩ :=
  skip_loop c tail col hSpace hTab hHash hBreak hGrammar s
    (s.inputEnd - s.offset + 1) hSource hFlow hIndent (by
      have := fuel_of_corr hSource
      omega)

lemma nested_close_after_grammar_separation (s : ScannerState) (tail : List Char) (col : Nat)
    {start : SurfPos} (hSource : ScannerSurfCorr s start)
    (hGrammar : FlowCloseSeparation start ⟨']' :: tail, col⟩)
    (hDepth : s.flowLevel ≥ 2) (hKind : s.flowStack.back? = some true)
    (hIndent : s.currentIndent < 0) (hDirectives : s.directivesPresent = false) :
    ∃ final, scanNextToken s = .ok (some final) ∧
      ScannerSurfCorr final ⟨tail, col + 1⟩ ∧ final.flowLevel = s.flowLevel - 1 ∧
      final.simpleKeyStack = s.simpleKeyStack.pop ∧
      final.simpleKey = s.simpleKeyStack.back?.getD {} ∧
      (∀ i, i < s.tokens.size → final.tokens[i]? = s.tokens[i]?) ∧
      final.flowStack = s.flowStack.pop ∧ final.indents = s.indents ∧
      final.directivesPresent = false ∧
      filteredValues final.tokens = filteredValues s.tokens ++ [.flowSequenceEnd] := by
  have hFlow : s.inFlow = true := by simp [ScannerState.inFlow]; omega
  obtain ⟨land, hSkip, hLand⟩ := skip_flow_separation s ']' tail col
    hSource hGrammar hFlow hIndent (by decide) (by decide) (by decide) (by decide)
  have hLandIndent : land.currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent
    rw [L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s land hSkip]
  have hCol : land.col = col := hLand.col_eq.symm
  obtain ⟨final, hStep, hSuffix, hRest⟩ := nested_close_after_separation s land tail
    hSkip (hCol ▸ hLand) hDepth hKind (by omega)
    ((skipToContent_dp s land hSkip).trans hDirectives)
  exact ⟨final, hStep, by simpa only [hCol] using hSuffix, hRest⟩

#check nested_close_after_grammar_separation
#print axioms nested_close_after_grammar_separation

end MathGraph.WholeSource.FlowSeparationLanding
