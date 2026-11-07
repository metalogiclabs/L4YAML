module
public import DirectiveBoundary
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public import L4YAML.Proofs.Scanner.ScanStrictCoupling
public import L4YAML.Proofs.Scanner.IndentStackBase
public meta import L4YAML.Parser.Composition

/-!
# A full scanner step after a source-derived directive

Capstone path: original directive → actual preprocessing and checks → full
scanNextToken → stream composition → Group 7.7. The suffix remains unparsed.
-/
namespace MathGraph.WholeSource.DirectiveStep
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.EmitterScannability
open MathGraph.WholeSource.DirectiveBridge MathGraph.WholeSource.DirectiveComments
open MathGraph.WholeSource.DirectiveBoundary

private def nextAfterDirective (s : String) : Bool :=
  match scanDirective (ScannerState.mk' s) with
  | .error _ => false
  | .ok out => match scanNextToken out with
    | .ok (some _) => true
    | _ => false
#guard nextAfterDirective "%YAML 1.2 # café\n---\nvalue" = true
#guard nextAfterDirective "%YAML 1.2 #\n---\n" = true
#guard nextAfterDirective "%YAML 1.2 #x\nvalue" = false
#guard nextAfterDirective "%YAML 1.2 #x\n---x" = false
#guard nextAfterDirective "%YAML 1.2 #x\n ---\n" = false

/- Adversarial landing tests: an explicit document marker must leave the
   trailing LF unread, with no flow collection or pending directives. -/
private def landedAtFinalLf (input : String) : Bool :=
  match scanNextToken ((ScannerState.mk' input).emit .streamStart) with
  | .ok (some mid) =>
    match scanNextToken mid with
    | .ok (some out) =>
      out.peek? == some '\n' && out.flowLevel == 0 &&
      out.indents == #[{column := -1, isSequence := false}] &&
      !out.directivesPresent && !out.allowDirectives && !out.seenYamlDirective
    | _ => false
  | _ => false
#guard landedAtFinalLf "%YAML 1.2 #\n---\n" = true
#guard landedAtFinalLf "%YAML 1.2 # café\n---\n" = true
#guard landedAtFinalLf "%YAML 1.2 #x\n---x" = false
#guard landedAtFinalLf "%YAML 1.2 #x\nvalue" = false
#guard landedAtFinalLf "%YAML 1.2 #x\n ---\n" = false

lemma version_token_checks (s land : ScannerState) (major minor : Nat) (pos : YamlPos)
    (priorTokens : Array (Positioned YamlToken))
    (ht : s.tokens = priorTokens.push {pos := pos, val := .versionDirective major minor}) :
    scanNextToken_checkDanglingNode s land = .ok () ∧
    scanNextToken_checkFlowValueIndent s land = .ok () := by
  have hn : trailingNodeRun? s.tokens = none := by
    rw [ht]
    exact trailingNodeRun?_push_none priorTokens _ rfl rfl rfl rfl
  have hd := danglingNodePos?_none_of_no_run s hn
  have hf := underIndentedFlowValuePos?_none_of_no_run s hn
  constructor
  · simp [scanNextToken_checkDanglingNode, hd]
  · simp [scanNextToken_checkFlowValueIndent, hf]

lemma ws_noop_nonwhite (s : ScannerState) (c : Char)
    (hp : s.peek? = some c) (hw : isWhiteSpaceBool c = false)
    (ht : c ≠ '\t') (hs : c ≠ ' ') (hm : s.offset < s.inputEnd) :
    skipToContentWs s = .ok s := by
  have hsp := skipSpaces_of_not_space s c hp hs
  have hws := skipWhitespace_of_not_ws s c hp hw hm
  unfold skipToContentWs
  split
  · rw [hsp]
    dsimp only
    split
    · split
      · rename_i he; exact False.elim (ht (Option.some.inj (hp.symm.trans he)))
      · rfl
    · exact congrArg Except.ok hws
  · exact congrArg Except.ok hws

lemma content_loop_noop (s : ScannerState) (fuel : Nat)
    (hp : s.peek? = some '-') (hm : s.offset < s.inputEnd) :
    skipToContentLoop s fuel = .ok s := by
  cases fuel with
  | zero => simp [skipToContentLoop]
  | succ n =>
    have hw := ws_noop_nonwhite s '-' hp (by decide) (by decide) (by decide) hm
    simp [skipToContentLoop, hw, skipToContentComment, hp,
      isLineBreakBool, isLineFeedBool, isCarriageReturnBool]

lemma lf_content (s : ScannerState) (rest : List Char) (col : Nat)
    (hc : ScannerSurfCorr s ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: rest, col⟩)
    (hf : s.flowLevel = 0) :
    let land := { consumeNewline s with simpleKeyAllowed := true }
    skipToContent s = .ok land ∧
    ScannerSurfCorr land ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ ∧
    land.flowLevel = 0 ∧ land.indents = s.indents ∧ land.needIndentCheck = true := by
  obtain ⟨hp, hm⟩ := peek_of_corr hc
  obtain ⟨hn, hk⟩ := consumeNewline_accepts s (.lf _ col) hc
  have hfl : (consumeNewline s).flowLevel = 0 := by
    rw [L4YAML.Proofs.ScannerCorrectness.consumeNewline_preserves_flowLevel, hf]
  let land := { consumeNewline s with simpleKeyAllowed := true }
  have hland : ScannerSurfCorr land ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ :=
    ⟨hn.chars_from, hn.col_eq, hn.end_eq, hn.input_prefix, hn.indent_cols_nonneg⟩
  obtain ⟨hpLand, hmLand⟩ := peek_of_corr hland
  have hws := ws_noop_nonwhite s '\n' hp (by decide) (by decide) (by decide) hm
  refine ⟨?_, hland, hfl, hk.2.2, ?_⟩
  · have hcomment : skipToContentComment s = s := by simp [skipToContentComment, hp]
    have hflow : (consumeNewline s).inFlow = false := by simp [ScannerState.inFlow, hfl]
    unfold skipToContent
    rw [skipToContentLoop]
    simpa [hws, hcomment, hp, hflow, isLineBreakBool, isLineFeedBool, isCarriageReturnBool]
      using content_loop_noop land (s.inputEnd - s.offset) hpLand hmLand
  · simp [consumeNewline, hp]

lemma preprocess_marker (s : ScannerState) (rest : List Char)
    (hc : ScannerSurfCorr s ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩)
    (hf : s.flowLevel = 0)
    (hi : s.indents = #[{column := -1, isSequence := false}])
    (hneed : s.needIndentCheck = true) :
    ∃ land, scanNextToken_preprocess s = .ok (some (land, '-')) ∧
      ScannerSurfCorr land ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ ∧
      land.flowLevel = 0 ∧
      land.indents = #[{column := -1, isSequence := false}] := by
  obtain ⟨hp, hm⟩ := peek_of_corr hc
  have hskip := skipToContent_of_content_char s '-' hp (by decide) (by decide) (by decide) hm
  have hflow : s.inFlow = false := by simp [ScannerState.inFlow, hf]
  have hunwind : unwindIndents s s.col = s := by
    simp [unwindIndents, hi, unwindIndentsLoop]
  let ready := { s with needIndentCheck := false }
  let land := closeStaleExplicitKey (saveSimpleKey ready)
  have hr : ScannerSurfCorr ready ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ :=
    ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩
  have hl := L4YAML.Proofs.ScanStrictCoupling.closeStaleExplicitKey_corr _ _
    (L4YAML.Proofs.StructureCoupling.saveSimpleKey_corr _ _ hr)
  refine ⟨land, ?_, hl, ?_, ?_⟩
  · unfold scanNextToken_preprocess
    simp [hskip, bind, pure, Except.bind, Except.pure, ScannerState.hasMore, hm, hflow, hneed, hunwind, ready, land, saveSimpleKey_preserves_peek]
    change (match ready.peek? with
      | none => Except.ok none
      | some c => Except.ok (some (land, c))) = Except.ok (some (land, '-'))
    rw [(peek_of_corr hr).1]
  · simp [land, ready, L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_flowLevel, hf]
  · change (closeStaleExplicitKey (saveSimpleKey ready)).indents = _
    rw [L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_indents,
      L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents]
    exact hi

/-- Retain the *actual* post-preprocessing landing witness, rather than only
its three directive flags. This is the source-correspondence handoff needed
for the terminal `scanLoop` checks in the bounded empty-document capstone. -/
lemma full_step_after_version_landing (s : ScannerState) (rest : List Char)
    (col major minor : Nat)
    (pos : YamlPos) (priorTokens : Array (Positioned YamlToken))
    (hc : ScannerSurfCorr s ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: rest, col⟩)
    (hf : s.flowLevel = 0)
    (hi : s.indents = #[{column := -1, isSequence := false}])
    (ht : s.tokens = priorTokens.push {pos := pos, val := .versionDirective major minor}) :
    ∃ land, scanNextToken s = .ok (some (scanDocumentStart land)) ∧
      ScannerSurfCorr land ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ ∧
      land.flowLevel = 0 ∧
      land.indents = #[{column := -1, isSequence := false}] := by
  obtain ⟨hskip, hcLand, hfLand, hiLand, hnLand⟩ := lf_content s rest col hc hf
  let content := { consumeNewline s with simpleKeyAllowed := true }
  obtain ⟨land, hpre, hcorr, hflow, hinds⟩ := preprocess_marker content rest hcLand hfLand
    (hiLand.trans hi) hnLand
  have hpreS : scanNextToken_preprocess s = .ok (some (land, '-')) := by
    obtain ⟨hp, hm⟩ := peek_of_corr hcLand
    have hnoop := skipToContent_of_content_char content '-' hp (by decide) (by decide) (by decide) hm
    unfold scanNextToken_preprocess at hpre ⊢
    rw [hnoop] at hpre
    rw [hskip]
    exact hpre
  obtain ⟨hd, hv⟩ := version_token_checks s land major minor pos priorTokens ht
  have hstruct := structural_document_start land rest hcorr hflow
  refine ⟨land, ?_, hcorr, hflow, hinds⟩
  simp [scanNextToken, hpreS, hd, hv, hstruct, bind, pure, Except.bind, Except.pure]

/-- The `---` production consumes exactly its three marker characters. The
remaining LF and the entire source suffix stay connected to the *same* state
returned by the original `scanNextToken` call. -/
lemma document_start_landing_source (land : ScannerState) (rest : List Char)
    (hc : ScannerSurfCorr land ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩)
    (hi : land.indents = #[{column := -1, isSequence := false}]) :
    ScannerSurfCorr (scanDocumentStart land) ⟨'\n' :: rest, 3⟩ := by
  have hunwind : unwindIndents land (-1) = land := by
    simp [unwindIndents, hi, unwindIndentsLoop]
  let marked := ({ land with simpleKey := { possible := false } }).emit .documentStart
  have hc₀ : ScannerSurfCorr marked ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ :=
    ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩
  have hcol₀ : marked.col = 0 := hc₀.col_eq.symm
  have hc₀' : ScannerSurfCorr marked ⟨'-' :: '-' :: '-' :: '\n' :: rest, marked.col⟩ := by
    simpa [hcol₀] using hc₀
  have hc₁ := advance_non_newline_corr marked '-' ('-' :: '-' :: '\n' :: rest)
    hc₀' (peek_of_corr hc₀).2 (by decide) (by decide)
  have hcol₁ : marked.advance.col = marked.col + 1 := hc₁.col_eq.symm
  have hc₁' : ScannerSurfCorr marked.advance
      ⟨'-' :: '-' :: '\n' :: rest, marked.advance.col⟩ := by
    simpa [hcol₁] using hc₁
  have hc₂ := advance_non_newline_corr marked.advance '-' ('-' :: '\n' :: rest)
    hc₁' (peek_of_corr hc₁).2 (by decide) (by decide)
  have hcol₂ : marked.advance.advance.col = marked.advance.col + 1 := hc₂.col_eq.symm
  have hc₂' : ScannerSurfCorr marked.advance.advance
      ⟨'-' :: '\n' :: rest, marked.advance.advance.col⟩ := by
    simpa [hcol₂] using hc₂
  have hc₃ := advance_non_newline_corr marked.advance.advance '-' ('\n' :: rest)
    hc₂' (peek_of_corr hc₂).2 (by decide) (by decide)
  have hcol₃ : marked.advance.advance.col + 1 = 3 := by omega
  have hc₃' : ScannerSurfCorr marked.advance.advance.advance ⟨'\n' :: rest, 3⟩ := by
    simpa [hcol₃] using hc₃
  simpa [scanDocumentStart, hunwind, ScannerState.advanceN,
    ScannerState.advanceNLoop, marked] using hc₃'

/-- At the post-marker landing, the terminal guards see the original sentinel
indentation, an empty flow stack, and an exact document-start token suffix. -/
lemma document_start_landing_state (land : ScannerState)
    (hf : land.flowLevel = 0)
    (hi : land.indents = #[{column := -1, isSequence := false}]) :
    (scanDocumentStart land).flowLevel = 0 ∧
    (scanDocumentStart land).indents = #[{column := -1, isSequence := false}] ∧
    (scanDocumentStart land).tokens =
      land.tokens.push {pos := land.currentPos, val := .documentStart} := by
  have hunwind : unwindIndents land (-1) = land := by
    simp [unwindIndents, hi, unwindIndentsLoop]
  refine ⟨?_, ?_, ?_⟩
  · exact (L4YAML.Proofs.ScannerCorrectness.scanDocumentStart_preserves_flowLevel land).trans hf
  · simp [scanDocumentStart, hunwind,
      L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents, ScannerState.emit, hi]
  · simp [scanDocumentStart, hunwind,
      L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_tokens, ScannerState.emit,
      ScannerState.currentPos]

/-- State-preserving successor of the independent source directive family.
Unlike a flag-only witness, this hands the exact remaining source and terminal
state to the EOF and token proof obligations. -/
lemma full_step_after_version_state (s : ScannerState) (rest : List Char)
    (col major minor : Nat) (pos : YamlPos)
    (priorTokens : Array (Positioned YamlToken))
    (hc : ScannerSurfCorr s ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: rest, col⟩)
    (hf : s.flowLevel = 0)
    (hi : s.indents = #[{column := -1, isSequence := false}])
    (ht : s.tokens = priorTokens.push {pos := pos, val := .versionDirective major minor}) :
    ∃ out, scanNextToken s = .ok (some out) ∧
      ScannerSurfCorr out ⟨'\n' :: rest, 3⟩ ∧
      out.flowLevel = 0 ∧
      out.indents = #[{column := -1, isSequence := false}] ∧
      out.directivesPresent = false ∧ out.allowDirectives = false ∧
      out.seenYamlDirective = false := by
  obtain ⟨land, hstep, hcLand, hfLand, hiLand⟩ :=
    full_step_after_version_landing s rest col major minor pos priorTokens hc hf hi ht
  obtain ⟨hfl, hind, _⟩ := document_start_landing_state land hfLand hiLand
  refine ⟨scanDocumentStart land, hstep,
    document_start_landing_source land rest hcLand hiLand,
    hfl, hind, ?_, ?_, ?_⟩
  all_goals simp [scanDocumentStart]

/-- Compatibility projection: the previous independently qualified interface
remains available to all existing consumers. -/
lemma full_step_after_version (s : ScannerState) (rest : List Char) (col major minor : Nat)
    (pos : YamlPos) (priorTokens : Array (Positioned YamlToken))
    (hc : ScannerSurfCorr s ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: rest, col⟩)
    (hf : s.flowLevel = 0)
    (hi : s.indents = #[{column := -1, isSequence := false}])
    (ht : s.tokens = priorTokens.push {pos := pos, val := .versionDirective major minor}) :
    ∃ out, scanNextToken s = .ok (some out) ∧ out.directivesPresent = false ∧
      out.allowDirectives = false ∧ out.seenYamlDirective = false := by
  obtain ⟨land, hstep, _, _, _⟩ :=
    full_step_after_version_landing s rest col major minor pos priorTokens hc hf hi ht
  refine ⟨scanDocumentStart land, hstep, ?_, ?_, ?_⟩
  all_goals simp [scanDocumentStart]

/-- Original-source consumer of the full next step; the rest of the document
is not parsed and whole-stream completeness is not claimed. -/
lemma original_comment_full_step (input : String) (major minor comment rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: '-' :: '-' :: '-' :: '\n' :: rest)))) :
    ∃ directiveOut out, scanDirective (ScannerState.mk' input) = .ok directiveOut ∧
      scanNextToken directiveOut = .ok (some out) ∧ out.directivesPresent = false ∧
      out.allowDirectives = false ∧ out.seenYamlDirective = false := by
  have hc := initial_corr input input.toList (chars_from_zero_toList input)
  rw [hsource] at hc
  obtain ⟨mid, hok, hland, ht, _, _⟩ := yaml_comment_dispatch (ScannerState.mk' input)
    major minor comment ('-' :: '-' :: '-' :: '\n' :: rest)
    hma hmi hneMa hneMi hcomment hc rfl rfl
  have hf : mid.flowLevel = 0 :=
    L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_flowLevel _ _ hok
  have hi : mid.indents = #[{column := -1, isSequence := false}] :=
    L4YAML.Proofs.IndentStackBase.scanDirective_preserves_indents hok
  have ht' : mid.tokens = #[{pos := (ScannerState.mk' input).currentPos, val := .versionDirective (String.ofList major).toNat! (String.ofList minor).toNat!}] := by
    simpa [ScannerState.mk'] using ht
  obtain ⟨out, hs, hd, ha, hy⟩ := full_step_after_version mid rest _ _ _ _ #[] hland hf hi ht'
  exact ⟨mid, out, hok, hs, hd, ha, hy⟩

/-- Compatibility with the actual scanner's streamStart token priorTokens. This
still starts by explicitly invoking scanDirective; the first scanNextToken
and the remainder of scanLoop are separate obligations. -/
lemma original_streamstart_comment_full_step (input : String) (major minor comment rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: '-' :: '-' :: '-' :: '\n' :: rest)))) :
    ∃ directiveOut out, scanDirective ((ScannerState.mk' input).emit .streamStart) = .ok directiveOut ∧
      scanNextToken directiveOut = .ok (some out) ∧ out.directivesPresent = false ∧
      out.allowDirectives = false ∧ out.seenYamlDirective = false := by
  have hc := initial_corr input input.toList (chars_from_zero_toList input)
  have hc' : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart) ⟨input.toList, 0⟩ :=
    ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩
  rw [hsource] at hc' 
  obtain ⟨mid, hok, hland, ht, _, _⟩ := yaml_comment_dispatch ((ScannerState.mk' input).emit .streamStart)
    major minor comment ('-' :: '-' :: '-' :: '\n' :: rest)
    hma hmi hneMa hneMi hcomment hc' rfl rfl
  have hf : mid.flowLevel = 0 :=
    L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_flowLevel _ _ hok
  have hi : mid.indents = #[{column := -1, isSequence := false}] :=
    L4YAML.Proofs.IndentStackBase.scanDirective_preserves_indents hok
  obtain ⟨out, hs, hd, ha, hy⟩ := full_step_after_version mid rest _ _ _ _
    ((ScannerState.mk' input).emit .streamStart).tokens hland hf hi ht
  exact ⟨mid, out, hok, hs, hd, ha, hy⟩

#print axioms original_streamstart_comment_full_step
#print axioms full_step_after_version
#print axioms full_step_after_version_landing
#print axioms document_start_landing_source
#print axioms document_start_landing_state
#print axioms full_step_after_version_state
#print axioms original_comment_full_step
#print axioms version_token_checks
#print axioms lf_content
#print axioms preprocess_marker
end
end MathGraph.WholeSource.DirectiveStep
