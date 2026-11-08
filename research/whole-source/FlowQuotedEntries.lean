module

public import FlowQuotedChild
public meta import Lean

/-! Group 7.7, productions [137]–[139]. Induct over a source-defined list of
double-quoted entries. Separation before a comma and before the closing bracket
is consumed by the actual scanner, as is leading separation before each quote. -/

@[expose] public section
namespace MathGraph.WholeSource.FlowQuotedEntries

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.EmitterScannability L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.CloseStaleExplicitKey
open MathGraph.WholeSource.FlowSeparationLanding MathGraph.WholeSource.FlowQuotedChild

lemma comma_after_grammar_separation (s : ScannerState) {start : SurfPos}
    (tail : List Char) (col : Nat) (hSource : ScannerSurfCorr s start)
    (hSep : FlowCloseSeparation start ⟨',' :: tail, col⟩)
    (hFlow : s.inFlow = true) (hIndent : s.currentIndent < 0)
    (hDirectives : s.directivesPresent = false)
    (hLast : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry) :
    ∃ next, scanNextToken s = .ok (some next) ∧ ScannerSurfCorr next ⟨tail, col + 1⟩ ∧
      next.flowLevel = s.flowLevel ∧ next.flowStack = s.flowStack ∧
      next.indents = s.indents ∧ next.directivesPresent = false ∧
      next.simpleKeyStack = s.simpleKeyStack ∧
      lastRealTokenVal? next.tokens = some .flowEntry := by
  obtain ⟨land, hSkip, hLand⟩ := skip_flow_separation s ',' tail col
    hSource hSep hFlow hIndent (by decide) (by decide) (by decide) (by decide)
  have hLandDepth := skipToContent_preserves_flowLevel s land hSkip
  have hLandFlow : land.inFlow = true := by simpa only [ScannerState.inFlow, hLandDepth] using hFlow
  obtain ⟨hPeek, hMore⟩ := peek_of_chars_cons land ',' tail col hLand
  let ready := saveSimpleKey land
  have hReadyFlow : ready.inFlow = true := (saveSimpleKey_preserves_inFlow land).trans hLandFlow
  have hPre : scanNextToken_preprocess s = .ok (some (ready, ',')) := by
    have hHas : land.hasMore = true := by unfold ScannerState.hasMore; exact decide_eq_true hMore
    unfold scanNextToken_preprocess
    rw [hSkip]
    simp only [bind, Except.bind, pure, Except.pure, hHas, hLandFlow, Bool.not_true,
      Bool.false_eq_true, Bool.false_and, ite_false, Nat.lt_irrefl, decide_false,
      closeStaleExplicitKey_of_inFlow _ hReadyFlow, saveSimpleKey_preserves_peek, hPeek, ready]
  have hReadySource : ScannerSurfCorr ready ⟨',' :: tail, col⟩ :=
    L4YAML.Proofs.StructureCoupling.saveSimpleKey_corr _ _ hLand
  have hReadyPeek := peekAt_zero_corr ready _ hReadySource ',' tail rfl
  have hLandIndents := L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s land hSkip
  have hReadyIndents : ready.indents = s.indents :=
    (saveSimpleKey_preserves_indents land).trans hLandIndents
  have hReadyIndent : ready.currentIndent < 0 := by
    simpa only [ScannerState.currentIndent, hReadyIndents] using hIndent
  have hStructural : scanNextToken_dispatchStructural ready ',' = .ok none := by
    simp [scanNextToken_dispatchStructural, atDocumentStart, atDocumentEnd, hReadyPeek,
      show ¬((ready.col : Int) ≤ ready.currentIndent) from by omega, pure, Except.pure]
  let dispatched := if ready.allowDirectives then
    { ready with allowDirectives := false, documentEverStarted := true } else ready
  have hDispatchedDepth : dispatched.flowLevel = s.flowLevel := by
    simp only [dispatched]; split <;>
      exact (L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_flowLevel land).trans hLandDepth
  have hPositive : dispatched.flowLevel > 0 := by
    rw [hDispatchedDepth]
    exact of_decide_eq_true hFlow
  have hDispatchedSource : ScannerSurfCorr dispatched ⟨',' :: tail, col⟩ := by
    simp only [dispatched]; split
    · exact ⟨hReadySource.chars_from, hReadySource.col_eq, hReadySource.end_eq,
        hReadySource.input_prefix, hReadySource.indent_cols_nonneg⟩
    · exact hReadySource
  have hCol : dispatched.col = col := hDispatchedSource.col_eq.symm
  have hTokens : dispatched.tokens = ready.tokens := by simp only [dispatched]; split <;> rfl
  have hDispatchedLast : ∀ t, lastRealTokenVal? dispatched.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
    intro t ht
    rw [hTokens] at ht
    apply saveSimpleKey_preserves_lastRealTokenVal_ne_flow land _ t ht
    simpa only [skipToContent_preserves_tokens s land hSkip] using hLast
  have hReadyDP : ready.directivesPresent = false :=
    (saveSimpleKey_preserves_directivesPresent land).trans ((L4YAML.Proofs.ScanStrictCoupling.skipToContent_dp s land hSkip).trans hDirectives)
  obtain ⟨hEntry, hTail, hLevel, hDP, hIndents, _⟩ :=
    scanFlowEntry_detail dispatched tail (hCol ▸ hDispatchedSource) hDispatchedLast
  let next := { (dispatched.emit .flowEntry).advance with
    simpleKeyAllowed := true,
    explicitKeyLine := none, simpleKey := { possible := false } }
  have hStep : scanNextToken s = .ok (some next) :=
    scanNextToken_via_flow_dispatch s ready dispatched next ',' hPre hStructural rfl
      (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ hFlow)
      (dispatchFlowIndicators_comma dispatched hPositive hDispatchedLast) hReadyDP
      (scanNextToken_checkBareDocument_ok_of_inFlow _ hReadyFlow)
      (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ hFlow)
  refine ⟨next, hStep, by simpa only [next, hCol] using hTail,
    hLevel.trans hDispatchedDepth, ?_, hIndents.trans ?_, hDP.trans ?_, ?_, ?_⟩
  · rw [L4YAML.Proofs.ScannerFlowStack.scanFlowEntry_preserves_flowStack _ _ hEntry]
    simp only [dispatched]; split <;>
      exact (L4YAML.Proofs.ScannerFlowStack.saveSimpleKey_preserves_flowStack land).trans
        (L4YAML.Proofs.ScannerFlowStack.skipToContent_preserves_flowStack s land hSkip)
  · simp only [dispatched]; split <;> exact hReadyIndents
  · simp only [dispatched]; split <;> exact hReadyDP
  · rw [scanFlowEntry_preserves_simpleKeyStack _ _ hEntry]
    simp only [dispatched]; split <;> exact
      (saveSimpleKey_preserves_simpleKeyStack land).trans (skipToContent_preserves_simpleKeyStack s land hSkip)
  · change lastRealTokenVal? ((dispatched.emit .flowEntry).advance.tokens) = _
    rw [advance_preserves_tokens]
    exact lastRealTokenVal_push_non_ph _ _ (by simp)

/-- Nonempty quoted entries followed by separation up to a fixed close.
The natural index counts entries and does not depend on scanner execution. -/
inductive QuotedEntries (tail : List Char) (closeCol : Nat) : Nat → SurfPos → Prop where
  | single {start quote stop} : FlowCloseSeparation start quote →
      SCDoubleQuotedOk quote stop →
      FlowCloseSeparation stop ⟨']' :: tail, closeCol⟩ → QuotedEntries tail closeCol 1 start
  | more {n start quote stop rest commaCol} : FlowCloseSeparation start quote →
      SCDoubleQuotedOk quote stop →
      FlowCloseSeparation stop ⟨',' :: rest, commaCol⟩ →
      QuotedEntries tail closeCol n ⟨rest, commaCol + 1⟩ →
      QuotedEntries tail closeCol (n + 1) start

lemma quoted_entries_and_close {tail : List Char} {closeCol n : Nat} {start : SurfPos}
    (hEntries : QuotedEntries tail closeCol n start) :
    ∀ s : ScannerState, ScannerSurfCorr s start →
      s.flowLevel ≥ 2 → s.flowStack.back? = some true →
      s.currentIndent < 0 → s.directivesPresent = false →
      (∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) →
      ∃ final, ScanChain s (2 * n) final ∧ ScannerSurfCorr final ⟨tail, closeCol + 1⟩ ∧
        final.flowLevel = s.flowLevel - 1 ∧
        final.simpleKeyStack = s.simpleKeyStack.pop ∧
        final.simpleKey = s.simpleKeyStack.back?.getD {} := by
  induction hEntries with
  | single hLeading hQuote hSep =>
    intro s hSource hDepth hKind hIndent hDP hPrevious
    obtain ⟨final, hChain, hTail, hLevel, hStack, hKey, _⟩ :=
      quoted_child_and_close s tail closeCol hSource hLeading hQuote hSep
        hDepth hKind hIndent hDP hPrevious
    exact ⟨final, hChain, hTail, hLevel, hStack, hKey⟩
  | @more n start quote stop rest commaCol hLeading hQuote hSep _ ih =>
    intro s hSource hDepth hKind hIndent hDP hPrevious
    have hFlow : s.inFlow = true := by simp [ScannerState.inFlow]; omega
    obtain ⟨child, hChild, hChildSource, hLevel, hFlowStack, hIndents, hChildDP, hKeys,
      _, _, value, hLast⟩ := quoted_child_after_separation s hSource hLeading hQuote hFlow hIndent hDP hPrevious
    have hChildFlow : child.inFlow = true := by simpa only [ScannerState.inFlow, hLevel] using hFlow
    have hChildIndent : child.currentIndent < 0 := by
      simpa only [ScannerState.currentIndent, hIndents] using hIndent
    obtain ⟨next, hComma, hNextSource, hNextLevel, hNextFlowStack, hNextIndents,
      hNextDP, hNextKeys, hNextLast⟩ :=
      comma_after_grammar_separation child rest commaCol hChildSource hSep
        hChildFlow hChildIndent hChildDP (by
          intro t ht
          rw [hLast] at ht
          cases ht
          exact ⟨nofun, nofun, nofun⟩)
    have hNextIndent : next.currentIndent < 0 := by
      simpa only [ScannerState.currentIndent, hNextIndents, hIndents] using hIndent
    have hNextDepth := hNextLevel.trans hLevel
    have hNextSaved := hNextKeys.trans hKeys
    obtain ⟨final, hChain, hTail, hFinalDepth, hFinalStack, hFinalKey⟩ :=
      ih next hNextSource (by omega) (by rwa [hNextFlowStack, hFlowStack])
        hNextIndent hNextDP (by
          intro t ht
          rw [hNextLast] at ht
          cases ht
          rfl)
    refine ⟨final, ?_, hTail, hFinalDepth.trans (congrArg (· - 1) hNextDepth),
      hFinalStack.trans (congrArg Array.pop hNextSaved),
      hFinalKey.trans (congrArg (·.back?.getD {}) hNextSaved)⟩
    have hTogether := ((ScanChain.single hChild).trans (ScanChain.single hComma)).trans hChain
    simpa only [show 1 + 1 + 2 * n = 2 * (n + 1) by omega] using hTogether

lemma nested_sequence_quoted_entries (s : ScannerState)
    (body tail : List Char) (closeCol n : Nat)
    (hSource : ScannerSurfCorr s ⟨'[' :: body, s.col⟩)
    (hEntries : QuotedEntries tail closeCol n ⟨body, s.col + 1⟩)
    (hDepth : s.flowLevel > 0) (hIndent : s.currentIndent < 0)
    (hColumn : s.col > 0) (hLine : AllTokensOnLine s s.line) (hEnd : EndLineOnLine s)
    (hDP : s.directivesPresent = false)
    (hPrevious : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ final, ScanChain s (1 + 2 * n) final ∧ ScannerSurfCorr final ⟨tail, closeCol + 1⟩ ∧
      final.flowLevel = s.flowLevel ∧ final.simpleKeyStack = s.simpleKeyStack ∧
      final.simpleKey = (saveSimpleKey s).simpleKey := by
  have hFlow : s.inFlow = true := by simp [ScannerState.inFlow]; omega
  obtain ⟨mid, hOpen, hMidSource, hMidDepth, hMidDP, hMidIndents, _,
    hMidCol, _, _, _, _, hMidKeyPop, _, _, hMidKeys, hMidPrevious, hMidStack, _⟩ :=
    scanNextToken_flow_open_nested s body hSource hFlow hIndent hColumn hLine
      hEnd hDP hPrevious
  have hMidIndent : mid.currentIndent < 0 := by
    simpa only [ScannerState.currentIndent, hMidIndents] using hIndent
  have hMidKind : mid.flowStack.back? = some true := by simp [hMidStack]
  obtain ⟨final, hChain, hTail, hFinalDepth, hFinalStack, hFinalKey⟩ :=
    quoted_entries_and_close hEntries mid (hMidCol ▸ hMidSource) (by omega)
      hMidKind hMidIndent (hMidDP.trans hDP) hMidPrevious
  refine ⟨final, (ScanChain.single hOpen).trans hChain, hTail, by omega,
    hFinalStack.trans hMidKeyPop, ?_⟩
  simpa [hMidKeys] using hFinalKey

private def entriesControl : Bool := Id.run do
  let input := "[[ # before first\r\n\"a\" # first\r\n, # before second\n\"b\" \n,\t \"c\" # last\n], x]"
  let initial := (ScannerState.mk' input).emit .streamStart
  let .ok (some outer) := scanNextToken initial | return false
  let .ok (some inner) := scanNextToken outer | return false
  let .ok (some first) := scanNextToken inner | return false
  let .ok (some comma) := scanNextToken first | return false
  let .ok (some second) := scanNextToken comma | return false
  let .ok (some comma2) := scanNextToken second | return false
  let .ok (some third) := scanNextToken comma2 | return false
  let .ok (some closed) := scanNextToken third | return false
  return lastRealTokenVal? comma.tokens == some .flowEntry &&
    comma.simpleKeyStack == inner.simpleKeyStack &&
    closed.simpleKey == (saveSimpleKey outer).simpleKey &&
    closed.simpleKeyStack == outer.simpleKeyStack && closed.peek? == some ',' &&
    (TokenParser.parseYaml input).isOk

#guard entriesControl

#check nested_sequence_quoted_entries
#print axioms nested_sequence_quoted_entries
#check quoted_entries_and_close
#print axioms quoted_entries_and_close
#print axioms comma_after_grammar_separation

end MathGraph.WholeSource.FlowQuotedEntries
