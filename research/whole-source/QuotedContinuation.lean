module
public import TagDocument
public import QuotedPublic
public meta import Lean
@[expose] public section
namespace MathGraph.WholeSource.QuotedContinuation
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.EmitterScannability L4YAML.Proofs.FlowAdjacency
open L4YAML.Research.AcceptedSource
open MathGraph.WholeSource.DirectiveStep
open MathGraph.WholeSource.DirectiveEntry
open MathGraph.WholeSource.DirectiveRecordBridge
open MathGraph.WholeSource.DirectiveBridge

/-! A source-connected quoted step after a real document marker. The quoted
syntax is independent; preprocessing and safety checks are derived, not assumed.
The prefix may contain arbitrary earlier tokens. -/
lemma quote_loop_noop (s : ScannerState) (fuel : Nat)
    (hp : s.peek? = some '"') (hm : s.offset < s.inputEnd) :
    skipToContentLoop s fuel = .ok s := by
  cases fuel with
  | zero => simp [skipToContentLoop]
  | succ n =>
    have hw := ws_noop_nonwhite s '"' hp (by decide) (by decide) (by decide) hm
    simp [skipToContentLoop, hw, skipToContentComment, hp,
      isLineBreakBool, isLineFeedBool, isCarriageReturnBool]

lemma lf_quote_content (s : ScannerState) (rest : List Char) (col : Nat)
    (hc : ScannerSurfCorr s ⟨'\n' :: '"' :: rest, col⟩)
    (hf : s.flowLevel = 0) :
    let land := { consumeNewline s with simpleKeyAllowed := true }
    skipToContent s = .ok land ∧
    ScannerSurfCorr land ⟨'"' :: rest, 0⟩ ∧
    land.flowLevel = 0 ∧ land.indents = s.indents ∧ land.needIndentCheck = true ∧
    land.tokens = s.tokens := by
  obtain ⟨hp, hm⟩ := peek_of_corr hc
  obtain ⟨hn, hk⟩ := consumeNewline_accepts s (.lf _ col) hc
  have hfl : (consumeNewline s).flowLevel = 0 := by
    rw [L4YAML.Proofs.ScannerCorrectness.consumeNewline_preserves_flowLevel, hf]
  let land := { consumeNewline s with simpleKeyAllowed := true }
  have hland : ScannerSurfCorr land ⟨'"' :: rest, 0⟩ :=
    ⟨hn.chars_from, hn.col_eq, hn.end_eq, hn.input_prefix, hn.indent_cols_nonneg⟩
  obtain ⟨hpLand, hmLand⟩ := peek_of_corr hland
  have hws := ws_noop_nonwhite s '\n' hp (by decide) (by decide) (by decide) hm
  refine ⟨?_, hland, hfl, hk.2.2, ?_, hk.1⟩
  · have hcomment : skipToContentComment s = s := by simp [skipToContentComment, hp]
    have hflow : (consumeNewline s).inFlow = false := by simp [ScannerState.inFlow, hfl]
    unfold skipToContent
    rw [skipToContentLoop]
    simpa [hws, hcomment, hp, hflow, isLineBreakBool, isLineFeedBool, isCarriageReturnBool]
      using quote_loop_noop land (s.inputEnd - s.offset) hpLand hmLand
  · simp [consumeNewline, hp]

lemma preprocess_quote (s : ScannerState) (rest : List Char)
    (hc : ScannerSurfCorr s ⟨'"' :: rest, 0⟩)
    (hf : s.flowLevel = 0)
    (hi : s.indents = #[{column := -1, isSequence := false}])
    (hneed : s.needIndentCheck = true) :
    ∃ land, scanNextToken_preprocess s = .ok (some (land, '"')) ∧
      ScannerSurfCorr land ⟨'"' :: rest, 0⟩ ∧
      land = closeStaleExplicitKey (saveSimpleKey {s with needIndentCheck := false}) ∧
      land.flowLevel = 0 ∧
      land.indents = #[{column := -1, isSequence := false}] ∧
      land.tokens.filter (fun t => t.val != .placeholder) =
        s.tokens.filter (fun t => t.val != .placeholder) := by
  obtain ⟨hp, hm⟩ := peek_of_corr hc
  have hskip := skipToContent_of_content_char s '"' hp (by decide) (by decide) (by decide) hm
  have hflow : s.inFlow = false := by simp [ScannerState.inFlow, hf]
  have hunwind : unwindIndents s s.col = s := by
    simp [unwindIndents, hi, unwindIndentsLoop]
  let ready := { s with needIndentCheck := false }
  let land := closeStaleExplicitKey (saveSimpleKey ready)
  have hr : ScannerSurfCorr ready ⟨'"' :: rest, 0⟩ :=
    ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩
  have hl := L4YAML.Proofs.ScanStrictCoupling.closeStaleExplicitKey_corr _ _
    (L4YAML.Proofs.StructureCoupling.saveSimpleKey_corr _ _ hr)
  refine ⟨land, ?_, hl, rfl, ?_, ?_, ?_⟩
  · unfold scanNextToken_preprocess
    simp [hskip, bind, pure, Except.bind, Except.pure, ScannerState.hasMore, hm, hflow, hneed, hunwind, ready, land, saveSimpleKey_preserves_peek]
    change (match ready.peek? with
      | none => Except.ok none
      | some c => Except.ok (some (land, c))) = Except.ok (some (land, '"'))
    rw [(peek_of_corr hr).1]
  · simp [land, ready, L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_flowLevel, hf]
  · change (closeStaleExplicitKey (saveSimpleKey ready)).indents = _
    rw [L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_indents,
      L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents]
    exact hi
  · calc
      land.tokens.filter (fun t => t.val != .placeholder) =
          (saveSimpleKey ready).tokens.filter (fun t => t.val != .placeholder) := by
            simp [land]
      _ = ready.tokens.filter (fun t => t.val != .placeholder) :=
        saveSimpleKey_filter_placeholder ready
      _ = s.tokens.filter (fun t => t.val != .placeholder) := rfl

lemma quoted_after_marker (s : ScannerState) (chars : List Char) (col endCol : Nat)
    (prior : Array (Positioned YamlToken)) (pos : YamlPos)
    (hc : ScannerSurfCorr s ⟨'\n' :: chars, col⟩)
    (hf : s.flowLevel = 0)
    (hi : s.indents = #[{column := -1, isSequence := false}])
    (hd : s.directivesPresent = false)
    (ht : s.tokens = prior.push {pos := pos, val := .documentStart})
    (hq : SCDoubleQuotedOk ⟨chars, 0⟩ ⟨[], endCol⟩) :
    ∃ out value, scanNextToken s = .ok (some out) ∧
      out.peek? = none ∧ out.flowLevel = 0 ∧ out.directivesPresent = false ∧
      out.indents = #[{column := -1, isSequence := false}] ∧
      (out.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        ((s.tokens.filter (fun t => t.val != .placeholder)).map (·.val)).push
          (.scalar value .doubleQuoted) := by
  obtain ⟨rest, hchars⟩ := source_quoted_opening hq
  change chars = '"' :: rest at hchars
  subst chars
  obtain ⟨hskip, hcLand, hfLand, hiLand, hnLand, htLand⟩ := lf_quote_content s rest col hc hf
  let content := { consumeNewline s with simpleKeyAllowed := true }
  have hct : content.tokens = s.tokens := htLand
  obtain ⟨pp, hpre, hcorr, hpp, hflow, hinds, htFiltered⟩ :=
    preprocess_quote content rest hcLand hfLand (hiLand.trans hi) hnLand
  have hpreS : scanNextToken_preprocess s = .ok (some (pp, '"')) := by
    obtain ⟨hp, hm⟩ := peek_of_corr hcLand
    have hnoop := skipToContent_of_content_char content '"' hp (by decide) (by decide) (by decide) hm
    unfold scanNextToken_preprocess at hpre ⊢
    rw [hnoop] at hpre
    rw [hskip]
    exact hpre
  have hn : trailingNodeRun? s.tokens = none := by
    rw [ht]
    exact trailingNodeRun?_push_none prior _ rfl rfl rfl rfl
  obtain ⟨hdang, hfv⟩ := clean_token_checks s pp hn
  have hdp : pp.directivesPresent = false := by
    rw [hpp, L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_directivesPresent,
      saveSimpleKey_preserves_directivesPresent]
    exact (consumeNewline_preserves_dp s).trans hd
  have hreal : LastTokenReal ({content with needIndentCheck := false} : ScannerState).tokens := by
    change LastTokenReal content.tokens
    rw [htLand, ht]
    exact lastTokenReal_push (by simp)
  have hlast : lastRealTokenVal? pp.tokens = some .documentStart := by
    rw [hpp, L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_tokens,
      saveSimpleKey_preserves_lastRealTokenVal _ hreal]
    change lastRealTokenVal? content.tokens = _
    rw [htLand, ht]
    exact lastRealTokenVal_push (by simp)
  have hbare : scanNextToken_checkBareDocument pp = .ok () := by
    apply scanNextToken_checkBareDocument_ok_of_last
    intro t he
    rw [hlast] at he
    cases he
    rfl
  have hp := (peek_of_corr hcorr).1
  have hpat : pp.peekAt? 0 = pp.peek? := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop ScannerState.peek?
    rfl
  have hds : atDocumentStart pp = false := by
    unfold atDocumentStart
    rw [hpat, hp]
    simp
  have hde : atDocumentEnd pp = false := by
    unfold atDocumentEnd
    rw [hpat, hp]
    simp
  obtain ⟨hstruct, _, _⟩ := dispatchContent_quote pp '"' rfl hflow hds hde
  let ad := if pp.allowDirectives then
    { pp with allowDirectives := false, documentEverStarted := true } else pp
  have haf : ad.flowLevel = 0 := by
    dsimp [ad]; split <;> exact hflow
  have had : ad.directivesPresent = false := by
    dsimp [ad]; split <;> exact hdp
  have hai : ad.indents = pp.indents := by
    dsimp [ad]; split <;> rfl
  have hat : ad.tokens = pp.tokens := by
    dsimp [ad]; split <;> rfl
  have hac : ScannerSurfCorr ad ⟨'"' :: rest, 0⟩ := by
    dsimp [ad]; split <;>
      exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hads : atDocumentStart ad = false := by
    dsimp [ad]; split <;> exact hds
  have hade : atDocumentEnd ad = false := by
    dsimp [ad]; split <;> exact hde
  obtain ⟨_, hflowDispatch, hblockDispatch⟩ := dispatchContent_quote ad '"' rfl haf hads hade
  obtain ⟨dq, value, hscan, hcdq, htdq⟩ :=
    scanDoubleQuoted_accepts ad hac hq (Or.inr (by trivial : TrailingOk ([] : List Char)))
  have hpeek := peek_none_of_empty_surf dq endCol hcdq
  have hfdq := (L4YAML.Proofs.ScannerPlainScalarValid.scanDoubleQuoted_preserves_flowLevel ad dq hscan).trans haf
  have hddq := (scanDoubleQuoted_preserves_dp ad dq hscan).trans had
  have hidq := (scanDoubleQuoted_preserves_indents ad dq hscan).trans (hai.trans hinds)
  have hfilter : (dq.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
      ((s.tokens.filter (fun t => t.val != .placeholder)).map (·.val)).push
        (.scalar value .doubleQuoted) := by
    rw [htdq]
    simp only [Array.filter_push, show (YamlToken.scalar value .doubleQuoted != .placeholder) = true from rfl,
      ite_true, Array.map_push, hat, htFiltered, hct]
  have hdispatch : ∃ out, scanNextToken_dispatchContent ad '"' = .ok out ∧
      out.peek? = none ∧ out.flowLevel = 0 ∧ out.directivesPresent = false ∧
      out.indents = #[{column := -1, isSequence := false}] ∧
      (out.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        ((s.tokens.filter (fun t => t.val != .placeholder)).map (·.val)).push
          (.scalar value .doubleQuoted) := by
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, hscan]
    exact ⟨_, rfl, dq.simpleKey.possible.rec hpeek hpeek,
      dq.simpleKey.possible.rec hfdq hfdq, dq.simpleKey.possible.rec hddq hddq,
      dq.simpleKey.possible.rec hidq hidq, dq.simpleKey.possible.rec hfilter hfilter⟩
  obtain ⟨out, hdispatch, hpout, hfout, hdout, hiout, htout⟩ := hdispatch
  refine ⟨out, value, ?_, hpout, hfout, hdout, hiout, htout⟩
  exact scanNextToken_via_content_dispatch s pp ad out '"' hpreS hstruct rfl hfv
    hflowDispatch hblockDispatch (scanNextToken_checkAdjacentValue_ok_of_ne_colon _ (by decide))
    hdispatch hdp hbare hdang

/-- Original-source scanner completion for independently specified TAG,
explicit marker, and arbitrary valid double-quoted syntax. -/
lemma tag_quoted_scans (input : String) (handle pfx body : List Char) (col endCol : Nat)
    (htag : TagDirective handle pfx ⟨input.toList, 0⟩
      ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: body, col⟩)
    (hbody : SCDoubleQuotedOk ⟨body, 0⟩ ⟨[], endCol⟩) :
    ∃ ts value, Scanner.scanFiltered input = .ok ts ∧
      ts.map (·.val) = #[.streamStart,
        .tagDirective (String.ofList handle) (String.ofList pfx), .documentStart,
        .scalar value .doubleQuoted, .streamEnd] := by
  let ready := saveSimpleKey { (ScannerState.mk' input).emit .streamStart with needIndentCheck := false }
  obtain ⟨mid, hfirst, hc, _he, ht, hf, hi⟩ := original_dispatch_record_agreement input htag
  have hn : trailingNodeRun? mid.tokens = none := by
    rw [ht]
    exact trailingNodeRun?_push_none ready.tokens _ rfl rfl rfl rfl
  obtain ⟨land, hsecond, hcl, hfl, hil, htl⟩ :=
    full_step_after_clean_landing mid body col hc hf hi hn
  obtain ⟨hfm, him, htm⟩ := document_start_landing_state land hfl hil
  have hcm := document_start_landing_source land body hcl hil
  have hdm : (scanDocumentStart land).directivesPresent = false := by simp [scanDocumentStart]
  obtain ⟨out, value, hthird, hpeek, hfo, hdo, hio, hto⟩ :=
    quoted_after_marker (scanDocumentStart land) body 3 endCol land.tokens land.currentPos
      hcm hfm him hdm htm hbody
  have hmidValues : (mid.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
      #[.streamStart, .tagDirective (String.ofList handle) (String.ofList pfx)] := by
    rw [ht, Array.filter_push]
    simp [saveSimpleKey_filter_placeholder, ScannerState.emit, ScannerState.mk']
  have hmarkValues : ((scanDocumentStart land).tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
      #[.streamStart, .tagDirective (String.ofList handle) (String.ofList pfx), .documentStart] := by
    rw [htm, Array.filter_push]
    simp only [show (YamlToken.documentStart != .placeholder) = true from rfl,
      ite_true, Array.map_push, htl, hmidValues]
    rfl
  rw [hmarkValues] at hto
  have hscan := scan_eq_after_two input _ mid (scanDocumentStart land)
    (percent_source htag.percent) hfirst hsecond
  have hdn : scanLoop_checkDanglingNode out = .ok () :=
    scanLoop_checkDanglingNode_ok_of_sentinel_stack _ hio
      (crossedPropsExcessIdx?_none_of_no_props (no_props_of_filtered_pin hto
        (by intro v hv; simp [Array.mem_def] at hv; rcases hv with rfl | rfl | rfl | rfl <;> rfl)))
  have hfv := scanLoop_checkFlowValueIndent_ok_of_sentinel_stack out hio
  have hfuel : (input.utf8ByteSize + 1) * 4 - 3 ≥ 1 := by omega
  have heof := scanLoop_eof_eq hfuel (scanNextToken_eof out hpeek) hfo hdo hdn hfv
  have hraw : Scanner.scan input = .ok ((unwindIndents out (-1)).emit .streamEnd).tokens := by
    rw [hscan]
    have hnum : (input.utf8ByteSize + 1) * 4 - 2 = ((input.utf8ByteSize + 1) * 4 - 3) + 1 := by omega
    rw [hnum]
    exact scanLoop_step_eq hthird heof
  have hu : unwindIndents out (-1) = out := by simp [unwindIndents, hio, unwindIndentsLoop]
  refine ⟨((unwindIndents out (-1)).emit .streamEnd).tokens.filter
    (fun t => t.val != .placeholder), value, ?_, ?_⟩
  · simp [Scanner.scanFiltered, hraw]
  · rw [hu]
    simp [ScannerState.emit, Array.map_push, hto]

#check quoted_after_marker
#check tag_quoted_scans
open Lean Elab Command in
run_cmd do
  for n in [``quoted_after_marker, ``tag_quoted_scans] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"QUOTED_CONTINUATION_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.QuotedContinuation
