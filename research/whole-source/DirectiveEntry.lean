module
public import DirectiveStep
public meta import L4YAML.Parser.Composition

/-!
# Actual scanner entry through the first directive and document marker

Capstone path: original source → first two scanNextToken calls → scanLoop
continuation → Group 7.7. No success of the remaining suffix is asserted.
-/
namespace MathGraph.WholeSource.DirectiveEntry
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.EmitterScannability
open MathGraph.WholeSource.DirectiveBridge MathGraph.WholeSource.DirectiveComments
open MathGraph.WholeSource.DirectiveStep

private def twoSteps (input : String) : Bool :=
  match scanNextToken ((ScannerState.mk' input).emit .streamStart) with
  | .ok (some mid) => match scanNextToken mid with
    | .ok (some _) => true
    | _ => false
  | _ => false
#guard twoSteps "%YAML 1.2 # café\n---\nvalue" = true
#guard twoSteps "%YAML 1.2 #\n---\n" = true
#guard twoSteps "%YAML 1.2 #x\nvalue" = false
#guard twoSteps "%YAML 1.2 #x\n---x" = false
#guard twoSteps "%YAML 1.2 #x\n%YAML 1.2\n---\n" = false

/-- Exact initialized preprocessing result, retaining the flag omitted by the
older existential interface. Operational proof follows that interface's
existing reduction, with original-source correspondence supplied directly. -/
lemma initial_percent_preprocess (input : String) (rest : List Char)
    (hsource : input.toList = '%' :: rest) :
    let initial := (ScannerState.mk' input).emit .streamStart
    let ready := saveSimpleKey { initial with needIndentCheck := false }
    scanNextToken_preprocess initial = .ok (some (ready, '%')) ∧
    ScannerSurfCorr ready ⟨'%' :: rest, 0⟩ ∧ ready.flowLevel = 0 ∧
    ready.indents = #[{column := -1, isSequence := false}] ∧
    ready.allowDirectives = true ∧ ready.seenYamlDirective = false := by
  have hc := initial_corr input input.toList (chars_from_zero_toList input)
  rw [hsource] at hc
  let initial := (ScannerState.mk' input).emit .streamStart
  let ready := saveSimpleKey { initial with needIndentCheck := false }
  have hc0 : ScannerSurfCorr initial ⟨'%' :: rest, 0⟩ :=
    ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩
  obtain ⟨hp, hm⟩ := peek_of_corr hc0
  have hskip := skipToContent_of_content_char initial '%' hp (by decide) (by decide) (by decide) hm
  have hcorr : ScannerSurfCorr ready ⟨'%' :: rest, 0⟩ :=
    L4YAML.Proofs.StructureCoupling.saveSimpleKey_corr _ _
      ⟨hc0.chars_from, hc0.col_eq, hc0.end_eq, hc0.input_prefix, hc0.indent_cols_nonneg⟩
  refine ⟨?_, hcorr, rfl, rfl, rfl, rfl⟩
  unfold scanNextToken_preprocess
  rw [hskip]
  simp only [bind, Except.bind, pure, Except.pure]
  have hmore : initial.hasMore = true := by
    unfold ScannerState.hasMore; exact decide_eq_true hm
  simp only [hmore, Bool.not_true, Bool.false_eq_true, ite_false]
  have h_unwind : unwindIndents initial (initial.col : Int) = initial := by
    unfold unwindIndents unwindIndentsLoop; split <;> rfl
  have hflow : initial.inFlow = false := rfl
  have hneed : initial.needIndentCheck = true := rfl
  have hnoshrink : ¬ initial.indents.size < initial.indents.size := by omega
  simp only [h_unwind, hflow, hneed, Bool.not_false, Bool.true_and,
    hnoshrink, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hreadyPeek : ready.peek? = some '%' := (peek_of_corr hcorr).1
  rw [L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_of_ek_none _
    (by rw [L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyLine]; rfl), hreadyPeek]

lemma initial_checks (input : String) (land : ScannerState) :
    let initial := (ScannerState.mk' input).emit .streamStart
    scanNextToken_checkDanglingNode initial land = .ok () ∧
    scanNextToken_checkFlowValueIndent initial land = .ok () := by
  let initial := (ScannerState.mk' input).emit .streamStart
  have hn : trailingNodeRun? initial.tokens = none := by
    exact trailingNodeRun?_push_none #[] _ rfl rfl rfl rfl
  have hd := danglingNodePos?_none_of_no_run initial hn
  have hf := underIndentedFlowValuePos?_none_of_no_run initial hn
  change scanNextToken_checkDanglingNode initial land = .ok () ∧
    scanNextToken_checkFlowValueIndent initial land = .ok ()
  exact ⟨by simp [scanNextToken_checkDanglingNode, hd],
    by simp [scanNextToken_checkFlowValueIndent, hf]⟩

lemma percent_structural (s out : ScannerState) (rest : List Char)
    (hc : ScannerSurfCorr s ⟨'%' :: rest, 0⟩) (hf : s.flowLevel = 0)
    (hok : scanDirective s = .ok out) :
    scanNextToken_dispatchStructural s '%' = .ok (some out) := by
  have hcol : s.col = 0 := hc.col_eq.symm
  have hflow : s.inFlow = false := by simp [ScannerState.inFlow, hf]
  have hp := peekAt_of_corr hc 0
  have hstart : atDocumentStart s = false := by simp [atDocumentStart, hp]
  have hend : atDocumentEnd s = false := by simp [atDocumentEnd, hp]
  simp [scanNextToken_dispatchStructural, hcol, hflow, hstart, hend, hok,
    bind, Except.bind, pure, Except.pure]

/-- Both actual scanner steps from the scanner's initialized source state. -/
lemma original_two_steps (input : String) (major minor comment rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: '-' :: '-' :: '-' :: '\n' :: rest)))) :
    ∃ mid out, scanNextToken ((ScannerState.mk' input).emit .streamStart) = .ok (some mid) ∧
      scanNextToken mid = .ok (some out) ∧ out.directivesPresent = false ∧
      out.allowDirectives = false ∧ out.seenYamlDirective = false := by
  obtain ⟨hpre, hc, hf, hi, ha, hy⟩ := initial_percent_preprocess input _ hsource
  let ready := saveSimpleKey { (ScannerState.mk' input).emit .streamStart with needIndentCheck := false }
  obtain ⟨mid, hdir, hland, ht, _, _⟩ := yaml_comment_dispatch ready
    major minor comment ('-' :: '-' :: '-' :: '\n' :: rest)
    hma hmi hneMa hneMi hcomment hc ha hy
  have hfm : mid.flowLevel = 0 :=
    (L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_flowLevel ready mid hdir).trans hf
  have him : mid.indents = #[{column := -1, isSequence := false}] :=
    (L4YAML.Proofs.IndentStackBase.scanDirective_preserves_indents hdir).trans hi
  obtain ⟨out, hsecond, hd, hal, hseen⟩ := full_step_after_version mid rest _ _ _ _ ready.tokens hland hfm him ht
  have hstruct := percent_structural ready mid _ hc hf hdir
  obtain ⟨hc1, hc2⟩ := initial_checks input ready
  refine ⟨mid, out, ?_, hsecond, hd, hal, hseen⟩
  unfold scanNextToken
  rw [hpre]
  simp only [bind, Except.bind, pure, Except.pure]
  change (do
    scanNextToken_checkDanglingNode ((ScannerState.mk' input).emit .streamStart) ready
    scanNextToken_checkFlowValueIndent ((ScannerState.mk' input).emit .streamStart) ready
    match ← scanNextToken_dispatchStructural ready '%' with
    | some s => pure (some s)
    | none => _) = .ok (some mid)
  rw [hc1]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [hc2]
  simp only []
  rw [hstruct]

/-- Exact residual of the real scanner after two successful steps. This
preserves the production fuel budget and makes no suffix-success assumption. -/
lemma scan_eq_after_two (input : String) (rest : List Char) (mid out : ScannerState)
    (hsource : input.toList = '%' :: rest)
    (hfirst : scanNextToken ((ScannerState.mk' input).emit .streamStart) = .ok (some mid))
    (hsecond : scanNextToken mid = .ok (some out)) :
    scan input = scanLoop out ((input.utf8ByteSize + 1) * 4 - 2) := by
  have hc := initial_corr input input.toList (chars_from_zero_toList input)
  rw [hsource] at hc
  have hc0 : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart) ⟨'%' :: rest, 0⟩ :=
    ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩
  have hp := (peek_of_corr hc0).1
  have hfuel : (input.utf8ByteSize + 1) * 4 =
      ((input.utf8ByteSize + 1) * 4 - 2) + 1 + 1 := by omega
  unfold scan
  rw [hp]
  rw [hfuel, scanLoop, hfirst, scanLoop, hsecond]

lemma original_scan_continuation (input : String) (major minor comment rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: '-' :: '-' :: '-' :: '\n' :: rest)))) :
    ∃ out, scan input = scanLoop out ((input.utf8ByteSize + 1) * 4 - 2) ∧
      out.directivesPresent = false ∧ out.allowDirectives = false ∧
      out.seenYamlDirective = false := by
  obtain ⟨mid, out, hfirst, hsecond, hd, ha, hy⟩ :=
    original_two_steps input major minor comment rest hma hmi hneMa hneMi hcomment hsource
  exact ⟨out, scan_eq_after_two input _ mid out hsource hfirst hsecond, hd, ha, hy⟩

#print axioms initial_percent_preprocess
#print axioms initial_checks
#print axioms percent_structural
#print axioms original_two_steps
#print axioms scan_eq_after_two
#print axioms original_scan_continuation
end
end MathGraph.WholeSource.DirectiveEntry
