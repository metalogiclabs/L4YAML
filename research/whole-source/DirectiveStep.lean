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
  | .ok out => (scanNextToken out).toOption.flatten.isSome
#guard nextAfterDirective "%YAML 1.2 # café\n---\nvalue" = true
#guard nextAfterDirective "%YAML 1.2 #\n---\n" = true
#guard nextAfterDirective "%YAML 1.2 #x\nvalue" = false
#guard nextAfterDirective "%YAML 1.2 #x\n---x" = false
#guard nextAfterDirective "%YAML 1.2 #x\n ---\n" = false

lemma version_token_checks (s land : ScannerState) (major minor : Nat) (pos : YamlPos)
    (ht : s.tokens = #[{pos := pos, val := .versionDirective major minor}]) :
    scanNextToken_checkDanglingNode s land = .ok () ∧
    scanNextToken_checkFlowValueIndent s land = .ok () := by
  have hn : trailingNodeRun? s.tokens = none := by
    rw [ht]
    simp [trailingNodeRun?, prevRealIdx?, YamlToken.isNodeProperty,
      YamlToken.isNodeBody, YamlToken.isFlowClose]
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
  · unfold skipToContent
    rw [skipToContentLoop]
    simp only [hws, skipToContentComment, hp]
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool]
    simp only [ScannerState.inFlow, hfl]
    exact content_loop_noop land _ hpLand hmLand
  · simp [land, consumeNewline, hp]

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
  have hpk := (peek_of_corr hl).1
  refine ⟨land, ?_, hl, ?_⟩
  · unfold scanNextToken_preprocess
    simp [hskip, ScannerState.hasMore, hm, hflow, hneed, hunwind, hi, ready, land, hpk]
  · simp [land, ready, L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_flowLevel, hf]

#print axioms version_token_checks
#print axioms lf_content
#print axioms preprocess_marker
end
end MathGraph.WholeSource.DirectiveStep
