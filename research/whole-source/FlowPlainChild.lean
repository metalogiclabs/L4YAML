module
public import ExactPlain
public import FlowQuotedChild
public import L4YAML.Proofs.Scanner.FlowIndentStable
public meta import Lean

/-! Group 7.7: a one-line plain flow entry with an ordinary initial
character reaches its parent-owned delimiter through scanNextToken. -/
@[expose] public section
namespace MathGraph.WholeSource.FlowPlainChild

open L4YAML Scanner Surface CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.EmitterScannability L4YAML.Proofs.FlowAdjacency
open MathGraph.WholeSource.ExactPlain
open MathGraph.WholeSource.FlowCloseLanding

private lemma flow_loop_dp (s : ScannerState) (content spaces : String) (fuel : Nat)
    (contentIndent inputEnd : Nat) (result : PlainScalarResult)
    (h : collectPlainScalarLoop s content spaces fuel true contentIndent inputEnd = .ok result) :
    result.state.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s content spaces with
  | zero => simp only [collectPlainScalarLoop, Except.ok.injEq] at h; subst h; rfl
  | succ f ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; rfl
    · split at h
      · rename_i rTerm hTerm
        simp only [Except.ok.injEq] at h; subst h
        rw [L4YAML.Proofs.ScalarCoupling.terminates_state_eq _ s content spaces true rTerm hTerm]
      · split at h
        · simp only [ite_true, bind, Except.bind] at h
          split at h
          · exact absurd h (by simp)
          · rename_i folded hFold
            split at h
            · simp only [Except.ok.injEq] at h; subst h; rfl
            · split at h
              · exact absurd h (by simp)
              · generalize hLoop : collectPlainScalarLoop folded.2
                    (content ++ folded.1) "" f true contentIndent inputEnd = cont at h
                cases cont with
                | error e => simp at h
                | ok inner =>
                  dsimp only [] at h
                  split at h
                  · simp only [Except.ok.injEq] at h; subst h; rfl
                  · simp only [Except.ok.injEq] at h; subst h
                    exact (ih _ _ _ hLoop).trans (foldQuotedNewlines_preserves_dp _ _ hFold)
        · split at h
          · exact (ih _ _ _ h).trans (advance_dp s)
          · split at h
            · simp only [Except.ok.injEq] at h; subst h; rfl
            · exact (ih _ _ _ h).trans (advance_dp s)

private lemma scan_flow_plain_dp {s child : ScannerState} (hFlow : s.inFlow = true)
    (hScan : scanPlainScalar s = .ok child) : child.directivesPresent = s.directivesPresent := by
  unfold scanPlainScalar at hScan
  simp only [hFlow, ite_true, bind, Except.bind] at hScan
  split at hScan
  · exact absurd hScan (by simp)
  · rename_i result hLoop
    simp only [Except.ok.injEq] at hScan
    subst child
    exact flow_loop_dp _ _ _ _ _ _ _ hLoop

lemma plain_child_step (s : ScannerState) {c : Char} {rest : List Char} {col : Nat}
    {contentEnd delimiter : SurfPos}
    (hSource : ScannerSurfCorr s ⟨c :: rest, col⟩)
    (hFirst : ¬ isIndicatorProp c) (hCol : 0 < col)
    (hSpan : SNsPlainOneLine .flowIn ⟨c :: rest, col⟩ contentEnd)
    (hWhite : GStar SSWhite contentEnd delimiter)
    (hDelimiter : ∃ d tail, delimiter.chars = d :: tail ∧ (d = ',' ∨ d = ']'))
    (hFlow : s.inFlow = true) (hIndent : s.currentIndent < 0)
    (hDP : s.directivesPresent = false)
    (hPrevious : ∀ v, lastRealTokenVal? s.tokens = some v → v.completesFlowValue = false) :
    ∃ child, scanNextToken s = .ok (some child) ∧ ScannerSurfCorr child delimiter ∧
      child.flowLevel = s.flowLevel ∧ child.flowStack = s.flowStack ∧
      child.indents = s.indents ∧ child.directivesPresent = false ∧
      child.simpleKeyStack = s.simpleKeyStack ∧
      (∃ value, lastRealTokenVal? child.tokens = some (.scalar value .plain) ∧
        filteredValues child.tokens = filteredValues s.tokens ++ [.scalar value .plain]) := by
  have hNot (d : Char) (hd : isIndicatorProp d) : c ≠ d := fun h => hFirst (h ▸ hd)
  have hInd : isIndicatorBool c = false := Bool.eq_false_iff.mpr (fun h => hFirst ((isIndicator_iff c).mp h))
  have hStartFacts : isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧
      (∀ next, canStartPlainScalarBool c next true = true) := by
    have hg := one_line_to_guarded hSpan
    cases hg with
    | mk _ _ hf _ =>
      cases hf with
      | nonIndicator _ _ _ hs hi =>
        obtain ⟨hw, hb, _, hp, hBom⟩ := isPlainSafe_facts hs
        have hDash := hNot '-' (by decide)
        have hQ := hNot '?' (by decide)
        have hColon := hNot ':' (by decide)
        exact ⟨hw, hb, fun next => by
          simp [canStartPlainScalarBool, hDash, hQ, hColon, hInd, hw, hb, hp, bne, hBom]⟩
      | indicator _ _ _ _ hEx _ =>
        rcases hEx with rfl | rfl | rfl <;> exact False.elim (hFirst (by decide))
  obtain ⟨hWS, hLB, hStart⟩ := hStartFacts
  let pp := saveSimpleKey s
  have hPre := scanNextToken_preprocess_flow s c rest col hSource hFlow hWS hLB (hNot '#' (by decide))
  have hPPFlow : pp.inFlow = true := (saveSimpleKey_preserves_inFlow s).trans hFlow
  have hPPIndent : pp.currentIndent < 0 := by
    simpa only [pp, ScannerState.currentIndent, saveSimpleKey_preserves_indents] using hIndent
  have hPPSource : ScannerSurfCorr pp ⟨c :: rest, col⟩ :=
    L4YAML.Proofs.StructureCoupling.saveSimpleKey_corr _ _ hSource
  have hColEq : col = pp.col := hPPSource.col_eq
  have hPCol : pp.col ≠ 0 := hColEq ▸ Nat.ne_of_gt hCol
  have hStruct : scanNextToken_dispatchStructural pp c = .ok none := by
    simp [scanNextToken_dispatchStructural, hPCol,
      show ¬((pp.col : Int) ≤ pp.currentIndent) from by omega, pure, Except.pure]
  let ad := if pp.allowDirectives then
    { pp with allowDirectives := false, documentEverStarted := true } else pp
  have hAdTokens : ad.tokens = pp.tokens := by simp only [ad]; split <;> rfl
  have hAdFlow : ad.inFlow = true := by simp only [ad]; split <;> exact hPPFlow
  have hAdSource : ScannerSurfCorr ad ⟨c :: rest, col⟩ := by
    simp only [ad]; split
    · exact ⟨hPPSource.chars_from, hPPSource.col_eq, hPPSource.end_eq,
        hPPSource.input_prefix, hPPSource.indent_cols_nonneg⟩
    · exact hPPSource
  have hFlowDispatch : scanNextToken_dispatchFlowIndicators ad c = .ok none :=
    dispatchFlowIndicators_none _ _ (hNot '[' (by decide)) (hNot ']' (by decide))
      (hNot '{' (by decide)) (hNot '}' (by decide)) (hNot ',' (by decide))
      (checkFlowAdjacency_ok_of_notCompletes (fun v ht =>
        saveSimpleKey_preserves_completesFalse s hPrevious v (hAdTokens ▸ ht)))
  have hIndicator : ∃ d tail, delimiter.chars = d :: tail ∧ isFlowIndicatorProp d := by
    obtain ⟨d, tail, hChars, rfl | rfl⟩ := hDelimiter <;> exact ⟨_, _, hChars, by decide⟩
  obtain ⟨child, value, hScan, hChild, hTokens⟩ :=
    scan_flow_plain_to_indicator ad (Or.inl rfl) hAdSource hAdFlow hSpan hWhite hIndicator
      (doc_of_col_pos hAdSource hCol)
  have hBlock : scanNextToken_dispatchBlockIndicators ad c = .ok none := by
    simp [scanNextToken_dispatchBlockIndicators, hNot '-' (by decide), hNot '?' (by decide),
      hNot ':' (by decide), pure, Except.pure]
  have hContent : scanNextToken_dispatchContent ad c = .ok child := by
    simp [scanNextToken_dispatchContent, hNot '&' (by decide), hNot '*' (by decide),
      hNot '!' (by decide), hNot '|' (by decide), hNot '>' (by decide), hNot '"' (by decide),
      hNot '\'' (by decide), hAdFlow, hStart, hScan]
  have hStep := scanNextToken_via_content_dispatch s pp ad child c hPre hStruct rfl
    (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ hFlow) hFlowDispatch hBlock
    (scanNextToken_checkAdjacentValue_ok_of_ne_colon _ (hNot ':' (by decide)))
    hContent ((saveSimpleKey_preserves_directivesPresent s).trans hDP)
    (scanNextToken_checkBareDocument_ok_of_inFlow _ hPPFlow)
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ hFlow)
  refine ⟨child, hStep, hChild, ?_, ?_, ?_, ?_, ?_, value, ?_, ?_⟩
  · rw [L4YAML.Proofs.ScannerCorrectness.scanPlainScalar_preserves_flowLevel ad child hScan]
    simp only [ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  · rw [L4YAML.Proofs.ScannerFlowStack.scanPlainScalar_preserves_flowStack ad child hScan]
    simp only [ad]; split <;> exact saveSimpleKey_preserves_flowStack s
  · rw [L4YAML.Proofs.FlowIndentStable.scanPlainScalar_preserves_indents hScan]
    simp only [ad]; split <;> exact saveSimpleKey_preserves_indents s
  · rw [scan_flow_plain_dp hAdFlow hScan]
    simp only [ad]; split <;> exact (saveSimpleKey_preserves_directivesPresent s).trans hDP
  · rw [L4YAML.Proofs.ScannerCorrectness.scanPlainScalar_preserves_simpleKeyStack ad child hScan]
    simp only [ad]; split <;> exact L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · rw [hTokens]
    exact lastRealTokenVal_push_non_ph _ _ (by simp)
  · rw [hTokens, filteredValues_push _ _ (by simp), hAdTokens]
    exact congrArg (· ++ [.scalar value .plain]) (filteredValues_saveSimpleKey s)

#print axioms plain_child_step

end MathGraph.WholeSource.FlowPlainChild
