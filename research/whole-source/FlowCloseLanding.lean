module

public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public import L4YAML.Proofs.Scanner.ScannerFlowStackPreservation
public import L4YAML.Proofs.Coupling.StructureCoupling
public import L4YAML.Proofs.Coupling.ScannerCoupling
public import L4YAML.Parser.Composition
public meta import Lean

/-! Group 7.7, production [137]. The operational nested close is independent
of the emitter's whole-array line invariant. The landing is the actual
separation step of the scanner, not a guessed post-child position. -/

@[expose] public section
namespace MathGraph.WholeSource.FlowCloseLanding

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.ScannerFlowStack L4YAML.Proofs.ScannerCoupling

/-- Values in the scanner's actual token array after removing placeholders. -/
def filteredValues (ts : Array (Positioned YamlToken)) : List YamlToken :=
  (ts.filter (fun t => t.val != .placeholder)).toList.map (·.val)

lemma filteredValues_push (ts : Array (Positioned YamlToken)) (t : Positioned YamlToken)
    (h : t.val ≠ .placeholder) :
    filteredValues (ts.push t) = filteredValues ts ++ [t.val] := by
  have hp : (t.val != .placeholder) = true := bne_iff_ne.mpr h
  simp [filteredValues, hp]

lemma filteredValues_saveSimpleKey (s : ScannerState) :
    filteredValues (saveSimpleKey s).tokens = filteredValues s.tokens := by
  unfold filteredValues
  rw [saveSimpleKey_filter_placeholder]

lemma nested_close_after_separation (s land : ScannerState) (tail : List Char)
    (hSkip : skipToContent s = .ok land)
    (hSource : ScannerSurfCorr land ⟨']' :: tail, land.col⟩)
    (hDepth : s.flowLevel ≥ 2) (hKind : s.flowStack.back? = some true)
    (hIndent : land.currentIndent < (land.col : Int))
    (hDirectives : land.directivesPresent = false) :
    ∃ final, scanNextToken s = .ok (some final) ∧
      ScannerSurfCorr final ⟨tail, land.col + 1⟩ ∧
      final.flowLevel = s.flowLevel - 1 ∧
      final.simpleKeyStack = s.simpleKeyStack.pop ∧
      final.simpleKey = s.simpleKeyStack.back?.getD {} ∧
      (∀ i, i < s.tokens.size → final.tokens[i]? = s.tokens[i]?) ∧
      final.flowStack = s.flowStack.pop ∧ final.indents = s.indents ∧
      final.directivesPresent = false ∧
      filteredValues final.tokens = filteredValues s.tokens ++ [.flowSequenceEnd] := by
  have hLandDepth := skipToContent_preserves_flowLevel s land hSkip
  have hLandFlow : land.inFlow = true := by simp [ScannerState.inFlow]; omega
  have hFlow : s.inFlow = true := by simp [ScannerState.inFlow]; omega
  obtain ⟨hPeek, hMore⟩ := peek_of_chars_cons land ']' tail land.col hSource
  let ready := saveSimpleKey land
  have hReadyFlow : ready.inFlow = true := saveSimpleKey_preserves_inFlow land |>.trans hLandFlow
  have hPre : scanNextToken_preprocess s = .ok (some (ready, ']')) := by
    have hHas : land.hasMore = true := by unfold ScannerState.hasMore; exact decide_eq_true hMore
    unfold scanNextToken_preprocess
    rw [hSkip]
    simp only [bind, Except.bind, pure, Except.pure, hHas, hLandFlow, Bool.not_true,
      Bool.false_eq_true, Bool.false_and, ite_false, Nat.lt_irrefl, decide_false,
      closeStaleExplicitKey_of_inFlow _ hReadyFlow, saveSimpleKey_preserves_peek, hPeek, ready]
  have hReadySource : ScannerSurfCorr ready ⟨']' :: tail, land.col⟩ :=
    L4YAML.Proofs.StructureCoupling.saveSimpleKey_corr _ _ hSource
  have hReadyPeek := peekAt_zero_corr ready _ hReadySource ']' tail rfl
  have hReadyIndent : ready.currentIndent < (ready.col : Int) := by
    simpa only [ready, ScannerState.currentIndent, saveSimpleKey_preserves_indents,
      saveSimpleKey_preserves_col] using hIndent
  have hStructural : scanNextToken_dispatchStructural ready ']' = .ok none := by
    simp [scanNextToken_dispatchStructural, atDocumentStart, atDocumentEnd, hReadyPeek,
      show ¬((ready.col : Int) ≤ ready.currentIndent) from by omega, pure, Except.pure]
  let dispatched := if ready.allowDirectives then
    { ready with allowDirectives := false, documentEverStarted := true } else ready
  have hDispatchedDepth : dispatched.flowLevel = s.flowLevel := by
    simp only [dispatched]; split <;> exact (L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_flowLevel land).trans hLandDepth
  have hDispatchedFlowStack : dispatched.flowStack = s.flowStack := by
    simp only [dispatched]; split <;>
      exact (L4YAML.Proofs.ScannerFlowStack.saveSimpleKey_preserves_flowStack land).trans
        (skipToContent_preserves_flowStack s land hSkip)
  have hDispatchedKind : dispatched.flowStack.back? = some true := by
    rw [hDispatchedFlowStack, hKind]
  have hDispatchedStack : dispatched.simpleKeyStack = s.simpleKeyStack := by
    simp only [dispatched]; split <;>
      exact (saveSimpleKey_preserves_simpleKeyStack land).trans
        (skipToContent_preserves_simpleKeyStack s land hSkip)
  have hDispatchedSource : ScannerSurfCorr dispatched ⟨']' :: tail, land.col⟩ := by
    simp only [dispatched]; split
    · exact ⟨hReadySource.chars_from, hReadySource.col_eq, hReadySource.end_eq,
        hReadySource.input_prefix, hReadySource.indent_cols_nonneg⟩
    · exact hReadySource
  have hDispatchedCol : dispatched.col = land.col := hDispatchedSource.col_eq.symm
  have hScan := scanNextToken_via_flow_dispatch s ready dispatched _ ']' hPre hStructural rfl
    (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ hFlow)
    (dispatchFlowIndicators_close_bracket_nested _ (by omega) hDispatchedKind)
    ((saveSimpleKey_preserves_directivesPresent land).trans hDirectives)
    (scanNextToken_checkBareDocument_ok_of_inFlow _ hReadyFlow)
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ hFlow)
  obtain ⟨hTail, hFinalDepth, _⟩ := scanFlowSequenceEnd_detail dispatched tail
    (hDispatchedCol ▸ hDispatchedSource)
  refine ⟨scanFlowSequenceEnd dispatched, hScan, hDispatchedCol ▸ hTail, ?_,
    (scanFlowSequenceEnd_stack_popped dispatched).trans (congrArg Array.pop hDispatchedStack),
    (scanFlowSequenceEnd_simpleKey_restored dispatched).trans (by rw [hDispatchedStack]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFinalDepth, hDispatchedDepth, ite_eq_left (by omega)]
  · intro i hi
    have hLandTokens := skipToContent_preserves_tokens s land hSkip
    have hDispatchTokens : dispatched.tokens = ready.tokens := by
      simp only [dispatched]; split <;> rfl
    obtain ⟨tok, hAppend⟩ :
        ∃ tok, (scanFlowSequenceEnd dispatched).tokens = dispatched.tokens.push tok :=
      ⟨_, by unfold scanFlowSequenceEnd ScannerState.emit; rw [advance_preserves_tokens]⟩
    have hiLand : i < land.tokens.size := by simpa only [hLandTokens] using hi
    have hiReady : i < ready.tokens.size := by
      have hSize : land.tokens.size ≤ ready.tokens.size := saveSimpleKey_tokens_monotonic land
      omega
    rw [hAppend, hDispatchTokens, Array.getElem?_push,
      ite_eq_right (by omega : i ≠ ready.tokens.size),
      Array.getElem?_eq_getElem hiReady, ← hLandTokens,
      Array.getElem?_eq_getElem hiLand]
    exact congrArg some (saveSimpleKey_preserves_prefix land i hiLand)

  · exact (L4YAML.Proofs.ScannerFlowCollection.scanFlowSequenceEnd_pops dispatched).trans
      (congrArg Array.pop hDispatchedFlowStack)
  · rw [scanFlowSequenceEnd_preserves_indents]
    simp only [dispatched]; split <;>
      exact (saveSimpleKey_preserves_indents land).trans
        (L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s land hSkip)
  · rw [scanFlowSequenceEnd_preserves_dp]
    simp only [dispatched]; split <;>
      exact (saveSimpleKey_preserves_directivesPresent land).trans hDirectives
  · have hTok : (scanFlowSequenceEnd dispatched).tokens =
        dispatched.tokens.push ⟨dispatched.currentPos, .flowSequenceEnd, dispatched.currentPos⟩ := by
      unfold scanFlowSequenceEnd ScannerState.emit
      rw [advance_preserves_tokens]
    have hDispatch : dispatched.tokens = (saveSimpleKey land).tokens := by
      simp only [dispatched]; split <;> rfl
    rw [hTok, filteredValues_push _ _ (by simp), hDispatch, filteredValues_saveSimpleKey,
      skipToContent_preserves_tokens s land hSkip]


private lemma whitespace_id_at_nonwhite (s : ScannerState) (c : Char)
    (hPeek : s.peek? = some c) (hMore : s.offset < s.inputEnd)
    (hWhite : isWhiteSpaceBool c = false) :
    skipToContentWs s = .ok s := by
  have hSpace : c ≠ ' ' := by intro he; subst c; contradiction
  have hTab : c ≠ '\t' := by intro he; subst c; contradiction
  unfold skipToContentWs
  split
  · rw [skipSpaces_of_not_space s c hPeek hSpace]
    dsimp only []
    split
    · rw [hPeek]
      split
      · rename_i he
        exact False.elim (hTab (Option.some.inj he))
      · rfl
    · exact congrArg Except.ok (skipWhitespace_of_not_ws s c hPeek hWhite hMore)
  · exact congrArg Except.ok (skipWhitespace_of_not_ws s c hPeek hWhite hMore)

/-- Source-derived landing for a bare LF followed immediately by the bracket.
The negative indentation floor is the condition for a column-zero close. -/
lemma nested_close_after_lf (s : ScannerState) (tail : List Char)
    (hSource : ScannerSurfCorr s ⟨'\n' :: ']' :: tail, s.col⟩)
    (hDepth : s.flowLevel ≥ 2) (hKind : s.flowStack.back? = some true)
    (hIndent : s.currentIndent < 0) (hDirectives : s.directivesPresent = false) :
    ∃ final, scanNextToken s = .ok (some final) ∧
      ScannerSurfCorr final ⟨tail, 1⟩ ∧ final.flowLevel = s.flowLevel - 1 ∧
      final.simpleKeyStack = s.simpleKeyStack.pop ∧
      final.simpleKey = s.simpleKeyStack.back?.getD {} ∧
      (∀ i, i < s.tokens.size → final.tokens[i]? = s.tokens[i]?) := by
  obtain ⟨hPeek, hMore⟩ := peek_of_chars_cons s '\n' (']' :: tail) s.col hSource
  let land := consumeNewline s
  have hLandEq : land = { s.advance with needIndentCheck := true } := by
    simp [land, consumeNewline, hPeek]
  have hLandSource : ScannerSurfCorr land ⟨']' :: tail, 0⟩ := by
    have hAdvance := advance_newline_corr s (']' :: tail) hSource hMore
    rw [hLandEq]
    exact ⟨hAdvance.chars_from, hAdvance.col_eq, hAdvance.end_eq,
      hAdvance.input_prefix, hAdvance.indent_cols_nonneg⟩
  have hLandFlow : land.inFlow = true := by
    have hEq := L4YAML.Proofs.ScannerCorrectness.consumeNewline_preserves_flowLevel s
    change land.flowLevel = s.flowLevel at hEq
    simp [ScannerState.inFlow, hEq]; omega
  obtain ⟨hLandPeek, hLandMore⟩ := peek_of_chars_cons land ']' tail 0 hLandSource
  have hPark : ∀ fuel, skipToContentLoop land fuel = .ok land := by
    intro fuel
    cases fuel with
    | zero => simp [skipToContentLoop]
    | succ fuel =>
      have hComment : skipToContentComment land = land := by
        simp [skipToContentComment, hLandPeek]
      simp only [skipToContentLoop, whitespace_id_at_nonwhite land ']' hLandPeek hLandMore
        (by decide), hComment, hLandPeek, show isLineBreakBool ']' = false from by decide,
        Bool.false_eq_true, ite_false]
  have hSkip : skipToContent s = .ok land := by
    unfold skipToContent
    have hWhitespace := whitespace_id_at_nonwhite s '\n' hPeek hMore (by decide)
    have hComment : skipToContentComment s = s := by
      simp [skipToContentComment, hPeek]
    simp [skipToContentLoop, hWhitespace, hComment, hPeek,
      show isLineBreakBool '\n' = true from by decide,
      show consumeNewline s = land from rfl, hLandFlow, hPark]
  have hCol : land.col = 0 := hLandSource.col_eq.symm
  have hLandIndent : land.currentIndent < (land.col : Int) := by
    rw [hCol]
    simpa only [Int.ofNat_zero, land, ScannerState.currentIndent,
      L4YAML.Proofs.EmitterScannability.consumeNewline_preserves_indents] using hIndent
  have hLandDirectives : land.directivesPresent = false := by
    rw [hLandEq]
    change s.advance.directivesPresent = false
    unfold ScannerState.advance
    split <;> dsimp only <;> (try split) <;> (try split) <;> exact hDirectives
  obtain ⟨final, hStep, hTail, hDepth, hStack, hKey, hPrefix, _⟩ :=
    nested_close_after_separation s land tail hSkip
      (hCol ▸ hLandSource) hDepth hKind hLandIndent hLandDirectives
  exact ⟨final, hStep, by simpa [hCol] using hTail, hDepth, hStack, hKey, hPrefix⟩

-- Exercise a reachable state in which LF remains after the quoted child.
private def multilineCloseControl : Bool := Id.run do
  let initial := (ScannerState.mk' "[[\"a\"\n], x]").emit .streamStart
  let .ok (some outer) := scanNextToken initial | return false
  let .ok (some inner) := scanNextToken outer | return false
  let .ok (some child) := scanNextToken inner | return false
  let .ok (some closed) := scanNextToken child | return false
  return child.peek? == some '\n' && closed.peek? == some ',' &&
    closed.col == 1 && closed.flowLevel == 1 && closed.line == child.line + 1 &&
    closed.simpleKey.possible &&
    closed.simpleKey.tokenIndex == (child.simpleKeyStack.back?.getD {}).tokenIndex &&
    (List.range child.tokens.size).all fun i =>
      child.tokens[i]?.map (·.val) == closed.tokens[i]?.map (·.val)

#guard multilineCloseControl
#guard (TokenParser.parseYaml "[[\"a\"\n], x]").isOk

#check nested_close_after_separation
#check nested_close_after_lf

open Lean Elab Command in
run_cmd do
  for n in [``nested_close_after_separation, ``nested_close_after_lf] do
    let axs ← collectAxioms n
    unless (axs.filter fun a =>
        !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"FLOW_CLOSE_LANDING_AXIOMS {n}: {axs}"

end MathGraph.WholeSource.FlowCloseLanding
