module

public import FlowSeparationLanding
public meta import Lean

/-! Group 7.7, production [137]. Discharge the child-to-close handoff for an
independently derived double-quoted child at the stream indentation floor. -/

@[expose] public section
namespace MathGraph.WholeSource.FlowQuotedChild

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.EmitterScannability L4YAML.Proofs.FlowAdjacency
open MathGraph.WholeSource.FlowCloseLanding

lemma quoted_child_step (s : ScannerState) {start stop : SurfPos}
    (hSource : ScannerSurfCorr s start) (hQuote : SCDoubleQuotedOk start stop)
    (hFlow : s.inFlow = true) (hIndent : s.currentIndent < 0)
    (hDirectives : s.directivesPresent = false)
    (hPrevious : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ child, scanNextToken s = .ok (some child) ∧ ScannerSurfCorr child stop ∧
      child.flowLevel = s.flowLevel ∧ child.flowStack = s.flowStack ∧
      child.indents = s.indents ∧ child.directivesPresent = false ∧
      child.simpleKeyStack = s.simpleKeyStack ∧ s.tokens.size ≤ child.tokens.size ∧
      (∀ i, i < s.tokens.size → child.tokens[i]? = s.tokens[i]?) ∧
      (∃ value, lastRealTokenVal? child.tokens = some (.scalar value .doubleQuoted) ∧
        filteredValues child.tokens = filteredValues s.tokens ++ [.scalar value .doubleQuoted]) := by
  have hOpen : ∃ rest, start.chars = '"' :: rest := by
    rcases hQuote with ⟨_, _, _, hOpen, _, _⟩
    cases hOpen
    exact ⟨_, rfl⟩
  obtain ⟨rest, hChars⟩ := hOpen
  have hStart : start = ⟨'"' :: rest, s.col⟩ := by
    have hCol := hSource.col_eq
    cases start
    simp_all
  subst start
  let pp := saveSimpleKey s
  have hPre : scanNextToken_preprocess s = .ok (some (pp, '"')) :=
    scanNextToken_preprocess_flow s '"' rest s.col hSource hFlow
      (by decide) (by decide) (by decide)
  have hPPFlow : pp.inFlow = true := (saveSimpleKey_preserves_inFlow s).trans hFlow
  have hPPIndent : pp.currentIndent < 0 := by
    simpa only [pp, ScannerState.currentIndent, saveSimpleKey_preserves_indents] using hIndent
  have hPPSource : ScannerSurfCorr pp ⟨'"' :: rest, s.col⟩ :=
    L4YAML.Proofs.StructureCoupling.saveSimpleKey_corr _ _ hSource
  have hPPPeek := peekAt_zero_corr pp _ hPPSource '"' rest rfl
  have hStruct : scanNextToken_dispatchStructural pp '"' = .ok none := by
    simp [scanNextToken_dispatchStructural, atDocumentStart, atDocumentEnd, hPPPeek,
      show ¬((pp.col : Int) ≤ pp.currentIndent) from by omega, pure, Except.pure]
  let ad := if pp.allowDirectives then
    { pp with allowDirectives := false, documentEverStarted := true } else pp
  have hAdTokens : ad.tokens = pp.tokens := by simp only [ad]; split <;> rfl
  have hAdFlow : ad.inFlow = true := by simp only [ad]; split <;> exact hPPFlow
  have hAdSource : ScannerSurfCorr ad ⟨'"' :: rest, s.col⟩ := by
    simp only [ad]; split
    · exact ⟨hPPSource.chars_from, hPPSource.col_eq, hPPSource.end_eq, hPPSource.input_prefix, hPPSource.indent_cols_nonneg⟩
    · exact hPPSource
  have hFlowDispatch : scanNextToken_dispatchFlowIndicators ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (checkFlowAdjacency_ok_of_notCompletes (fun t ht =>
        saveSimpleKey_preserves_completesFalse s hPrevious t (hAdTokens ▸ ht)))
  obtain ⟨quoted, value, hScan, hQuotedSource, hTokens⟩ :=
    scanDoubleQuoted_accepts ad hAdSource hQuote (Or.inl hAdFlow)
  let child := if quoted.simpleKey.possible then
    { quoted with simpleKey := { quoted.simpleKey with endLine := quoted.line } } else quoted
  have hContent : scanNextToken_dispatchContent ad '"' = .ok child := by
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, Except.pure, hScan, child, ite_true, ite_false]
  have hStep := scanNextToken_via_content_dispatch s pp ad child '"' hPre hStruct rfl
    (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ hFlow) hFlowDispatch
    (dispatchBlockIndicators_none_quote _) (scanNextToken_checkAdjacentValue_ok_of_ne_colon _ (by decide))
    hContent ((saveSimpleKey_preserves_directivesPresent s).trans hDirectives)
    (scanNextToken_checkBareDocument_ok_of_inFlow _ hPPFlow)
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ hFlow)
  have hLevel : quoted.flowLevel = s.flowLevel := by
    rw [L4YAML.Proofs.ScannerCorrectness.scanDoubleQuoted_preserves_flowLevel ad quoted hScan]
    simp only [ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have hStack : quoted.flowStack = s.flowStack := by
    rw [L4YAML.Proofs.ScannerFlowStack.scanDoubleQuoted_preserves_flowStack ad quoted hScan]
    simp only [ad]; split <;> exact saveSimpleKey_preserves_flowStack s
  have hIndents : quoted.indents = s.indents := by
    rw [scanDoubleQuoted_preserves_indents ad quoted hScan]
    simp only [ad]; split <;> exact saveSimpleKey_preserves_indents s
  have hDP : quoted.directivesPresent = false := by
    rw [scanDoubleQuoted_preserves_dp ad quoted hScan]
    simp only [ad]; split <;> exact (saveSimpleKey_preserves_directivesPresent s).trans hDirectives
  have hKeys : quoted.simpleKeyStack = s.simpleKeyStack := by
    rw [L4YAML.Proofs.ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack ad quoted hScan]
    simp only [ad]; split <;> exact L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  have hChildTokens : child.tokens = quoted.tokens := by simp only [child]; split <;> rfl
  have hSize : s.tokens.size ≤ pp.tokens.size :=
    L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_tokens_monotonic s
  refine ⟨child, hStep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [child]; split
    · exact ⟨hQuotedSource.chars_from, hQuotedSource.col_eq, hQuotedSource.end_eq,
        hQuotedSource.input_prefix, hQuotedSource.indent_cols_nonneg⟩
    · exact hQuotedSource
  · simp only [child]; split <;> exact hLevel
  · simp only [child]; split <;> exact hStack
  · simp only [child]; split <;> exact hIndents
  · simp only [child]; split <;> exact hDP
  · simp only [child]; split <;> exact hKeys
  · rw [hChildTokens, hTokens, Array.size_push, hAdTokens]
    exact Nat.le_trans hSize (Nat.le_succ _)
  · intro i hi
    have hPPBound : i < pp.tokens.size := Nat.lt_of_lt_of_le hi hSize
    rw [hChildTokens, hTokens, hAdTokens, Array.getElem?_push,
      ite_eq_right (by omega : i ≠ pp.tokens.size),
      Array.getElem?_eq_getElem hPPBound, Array.getElem?_eq_getElem hi]
    exact congrArg some (L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_prefix s i hi)
  · refine ⟨value, ?_, ?_⟩
    · rw [hChildTokens, hTokens]
      exact lastRealTokenVal_push_non_ph _ _ (by simp)
    · rw [hChildTokens, hTokens, filteredValues_push _ _ (by simp), hAdTokens]
      exact congrArg (· ++ [.scalar value .doubleQuoted]) (filteredValues_saveSimpleKey s)

open MathGraph.WholeSource.FlowSeparationLanding

/-- Leading separation is part of the quoted scanner step. The landing does
not add a transition, even when the quote begins at column zero. -/
lemma quoted_child_after_separation (s : ScannerState) {start quote stop : SurfPos}
    (hSource : ScannerSurfCorr s start) (hLeading : FlowCloseSeparation start quote)
    (hQuote : SCDoubleQuotedOk quote stop)
    (hFlow : s.inFlow = true) (hIndent : s.currentIndent < 0)
    (hDirectives : s.directivesPresent = false)
    (hPrevious : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ child, scanNextToken s = .ok (some child) ∧ ScannerSurfCorr child stop ∧
      child.flowLevel = s.flowLevel ∧ child.flowStack = s.flowStack ∧
      child.indents = s.indents ∧ child.directivesPresent = false ∧
      child.simpleKeyStack = s.simpleKeyStack ∧ s.tokens.size ≤ child.tokens.size ∧
      (∀ i, i < s.tokens.size → child.tokens[i]? = s.tokens[i]?) ∧
      (∃ value, lastRealTokenVal? child.tokens = some (.scalar value .doubleQuoted) ∧
        filteredValues child.tokens = filteredValues s.tokens ++ [.scalar value .doubleQuoted]) := by
  have hOpen : ∃ rest, quote.chars = '"' :: rest := by
    rcases hQuote with ⟨_, _, _, hopen, _, _⟩
    cases hopen
    exact ⟨_, rfl⟩
  obtain ⟨rest, hChars⟩ := hOpen
  have hQuotePos : quote = ⟨'"' :: rest, quote.col⟩ := by
    cases quote
    simp_all
  rw [hQuotePos] at hLeading hQuote
  obtain ⟨land, hSkip, hLand⟩ := skip_flow_separation s '"' rest quote.col hSource hLeading
    hFlow hIndent (by decide) (by decide) (by decide) (by decide)
  have hLevel := L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_flowLevel s land hSkip
  have hTokens := L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_tokens s land hSkip
  have hIndents := L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s land hSkip
  have hLandFlow : land.inFlow = true := by
    simpa only [ScannerState.inFlow, hLevel] using hFlow
  have hLandIndent : land.currentIndent < 0 := by
    simpa only [ScannerState.currentIndent, hIndents] using hIndent
  obtain ⟨hPeek, hMore⟩ := peek_of_chars_cons land '"' rest quote.col hLand
  have hPark := skipToContent_of_content_char land '"' hPeek
    (by decide) (by decide) (by decide) hMore
  have hPre : scanNextToken_preprocess s = scanNextToken_preprocess land := by
    unfold scanNextToken_preprocess
    rw [hSkip, hPark]
  have hStep := scanNextToken_eq_of_preprocess s land hPre
  obtain ⟨child, hScan, hChild, hDepth, hStack, hChildIndents, hDP, hKeys, hSize, hPrefix, value, hLast, hEffect⟩ :=
    quoted_child_step land hLand hQuote hLandFlow hLandIndent
      ((L4YAML.Proofs.ScanStrictCoupling.skipToContent_dp s land hSkip).trans hDirectives)
      (by simpa only [hTokens] using hPrevious)
  exact ⟨child, hStep.trans hScan, hChild, hDepth.trans hLevel,
    hStack.trans (L4YAML.Proofs.ScannerFlowStack.skipToContent_preserves_flowStack s land hSkip),
    hChildIndents.trans hIndents, hDP,
    hKeys.trans (L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_simpleKeyStack s land hSkip),
    by simpa only [hTokens] using hSize, by simpa only [hTokens] using hPrefix, value, hLast, by simpa only [hTokens] using hEffect⟩

/-- The child and close are two actual scanner steps. The pending key restored
by the close is the one saved before scanning the child. -/
lemma quoted_child_and_close (s : ScannerState) {start quote stop : SurfPos}
    (tail : List Char) (col : Nat)
    (hSource : ScannerSurfCorr s start) (hLeading : FlowCloseSeparation start quote)
    (hQuote : SCDoubleQuotedOk quote stop)
    (hSeparation : FlowCloseSeparation stop ⟨']' :: tail, col⟩)
    (hDepth : s.flowLevel ≥ 2) (hKind : s.flowStack.back? = some true)
    (hIndent : s.currentIndent < 0)
    (hDirectives : s.directivesPresent = false)
    (hPrevious : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ final, ScanChain s 2 final ∧ ScannerSurfCorr final ⟨tail, col + 1⟩ ∧
      final.flowLevel = s.flowLevel - 1 ∧
      final.simpleKeyStack = s.simpleKeyStack.pop ∧
      final.simpleKey = s.simpleKeyStack.back?.getD {} ∧
      (∀ i, i < s.tokens.size → final.tokens[i]? = s.tokens[i]?) ∧
      final.flowStack = s.flowStack.pop ∧ final.indents = s.indents ∧
      final.directivesPresent = false ∧
      (∃ value, filteredValues final.tokens =
        filteredValues s.tokens ++ [.scalar value .doubleQuoted, .flowSequenceEnd]) := by
  have hFlow : s.inFlow = true := by simp [ScannerState.inFlow]; omega
  obtain ⟨child, hStep, hChildSource, hLevel, hStack, hIndents, hDP, hKeys, hSize, hPrefix, value, _, hEffect⟩ :=
    quoted_child_after_separation s hSource hLeading hQuote hFlow hIndent hDirectives hPrevious
  have hChildIndent : child.currentIndent < 0 := by
    simpa only [ScannerState.currentIndent, hIndents] using hIndent
  obtain ⟨final, hClose, hTail, hFinalLevel, hFinalStack, hFinalKey, hFinalPrefix, hFinalFlowStack, hFinalIndents, hFinalDP, hCloseEffect⟩ :=
    nested_close_after_grammar_separation child tail col hChildSource hSeparation
      (hLevel ▸ hDepth) (hStack ▸ hKind) hChildIndent hDP
  refine ⟨final, (ScanChain.single hStep).trans (ScanChain.single hClose), hTail,
    hFinalLevel.trans (congrArg (· - 1) hLevel),
    hFinalStack.trans (congrArg Array.pop hKeys),
    hFinalKey.trans (congrArg (·.back?.getD {}) hKeys), ?_,
    hFinalFlowStack.trans (congrArg Array.pop hStack), hFinalIndents.trans hIndents, hFinalDP, value, ?_⟩
  · intro i hi
    exact (hFinalPrefix i (Nat.lt_of_lt_of_le hi hSize)).trans (hPrefix i hi)
  · rw [hCloseEffect, hEffect, List.append_assoc]
    rfl

/-- One nested sequence containing a double-quoted entry. The three steps
include the opening bracket that saves the exact key later restored. -/
lemma nested_sequence_quoted_entry (s : ScannerState) (body tail : List Char) (col : Nat)
    {stop : SurfPos} (hSource : ScannerSurfCorr s ⟨'[' :: body, s.col⟩)
    (hQuote : SCDoubleQuotedOk ⟨body, s.col + 1⟩ stop)
    (hSeparation : FlowCloseSeparation stop ⟨']' :: tail, col⟩)
    (hDepth : s.flowLevel > 0) (hIndent : s.currentIndent < 0)
    (hColumn : s.col > 0) (hLine : AllTokensOnLine s s.line) (hEnd : EndLineOnLine s)
    (hDirectives : s.directivesPresent = false)
    (hPrevious : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ final, ScanChain s 3 final ∧ ScannerSurfCorr final ⟨tail, col + 1⟩ ∧
      final.flowLevel = s.flowLevel ∧ final.simpleKeyStack = s.simpleKeyStack ∧
      final.simpleKey = (saveSimpleKey s).simpleKey := by
  have hFlow : s.inFlow = true := by simp [ScannerState.inFlow]; omega
  obtain ⟨mid, hOpen, hMidSource, hMidDepth, hMidDP, hMidIndents, _,
    hMidCol, _, _, _, _, hMidKeyPop, _, _, hMidKeys, hMidPrevious, hMidStack, _⟩ :=
    scanNextToken_flow_open_nested s body hSource hFlow hIndent hColumn hLine
      hEnd hDirectives hPrevious
  have hMidIndent : mid.currentIndent < 0 := by
    simpa only [ScannerState.currentIndent, hMidIndents] using hIndent
  have hMidKind : mid.flowStack.back? = some true := by simp [hMidStack]
  obtain ⟨final, hChain, hTail, hFinalLevel, hFinalStack, hFinalKey, _⟩ :=
    quoted_child_and_close mid tail col (hMidCol ▸ hMidSource) (.inline (.nil _)) hQuote hSeparation
      (by omega) hMidKind hMidIndent (hMidDP.trans hDirectives) hMidPrevious
  refine ⟨final, (ScanChain.single hOpen).trans hChain, hTail, by omega,
    hFinalStack.trans hMidKeyPop, ?_⟩
  simpa [hMidKeys] using hFinalKey

private def quotedChildControl : Bool := Id.run do
  let input := "[[\"a\\tb\" # tail\r\n\t ], x]"
  let initial := (ScannerState.mk' input).emit .streamStart
  let .ok (some outer) := scanNextToken initial | return false
  let .ok (some inner) := scanNextToken outer | return false
  let .ok (some child) := scanNextToken inner | return false
  let .ok (some final) := scanNextToken child | return false
  return child.simpleKeyStack == inner.simpleKeyStack &&
    final.simpleKey == (saveSimpleKey outer).simpleKey &&
    final.simpleKeyStack == outer.simpleKeyStack && final.peek? == some ',' &&
    (TokenParser.parseYaml input).isOk

#guard quotedChildControl

#check nested_sequence_quoted_entry
#print axioms nested_sequence_quoted_entry

#check quoted_child_and_close
#print axioms quoted_child_and_close
#print axioms quoted_child_after_separation

end MathGraph.WholeSource.FlowQuotedChild
