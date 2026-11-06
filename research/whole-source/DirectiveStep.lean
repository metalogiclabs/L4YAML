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
      ScannerSurfCorr land ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ ∧ land.flowLevel = 0 := by
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
  refine ⟨land, ?_, hl, ?_⟩
  · unfold scanNextToken_preprocess
    simp [hskip, bind, pure, Except.bind, Except.pure, ScannerState.hasMore, hm, hflow, hneed, hunwind, ready, land, saveSimpleKey_preserves_peek]
    change (match ready.peek? with
      | none => Except.ok none
      | some c => Except.ok (some (land, c))) = Except.ok (some (land, '-'))
    rw [(peek_of_corr hr).1]
  · simp [land, ready, L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_flowLevel, hf]

/-- Full scanNextToken, including the actual newline preprocessing and both
intervening validators. No successful step/preprocessing premise is assumed. -/
lemma full_step_after_version (s : ScannerState) (rest : List Char) (col major minor : Nat)
    (pos : YamlPos) (priorTokens : Array (Positioned YamlToken))
    (hc : ScannerSurfCorr s ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: rest, col⟩)
    (hf : s.flowLevel = 0)
    (hi : s.indents = #[{column := -1, isSequence := false}])
    (ht : s.tokens = priorTokens.push {pos := pos, val := .versionDirective major minor}) :
    ∃ out, scanNextToken s = .ok (some out) ∧ out.directivesPresent = false ∧
      out.allowDirectives = false ∧ out.seenYamlDirective = false := by
  obtain ⟨hskip, hcLand, hfLand, hiLand, hnLand⟩ := lf_content s rest col hc hf
  let content := { consumeNewline s with simpleKeyAllowed := true }
  obtain ⟨land, hpre, hcorr, hflow⟩ := preprocess_marker content rest hcLand hfLand
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
  refine ⟨scanDocumentStart land, ?_, ?_, ?_, ?_⟩
  · simp [scanNextToken, hpreS, hd, hv, hstruct, bind, pure, Except.bind, Except.pure]
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
#print axioms original_comment_full_step
#print axioms version_token_checks
#print axioms lf_content
#print axioms preprocess_marker
end
end MathGraph.WholeSource.DirectiveStep
