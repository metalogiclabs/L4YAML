module

public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Proofs.Output.EmitterScannability.FilteredTracking
public import L4YAML.Proofs.Parser.StreamCompleteness
public import L4YAML.Proofs.Composition
-- The trace producer seals its executable bodies; inspect the actual trace.
import all L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section

/-! Original-source quoted acceptance through the actual public parser.

Dependency path: independent `SCDoubleQuotedOk` on the entire original input →
actual filtered tokens → token grammar/state → `parseStream_accepts` →
`Composition.parseYaml_pipeline`, feeding Blueprint group 7.7 acceptance closure.
This fragment has no emitter-image or scanner-success premise. It claims
acceptance, not decoded-value fidelity or full YAML grammar completeness.
-/

set_option autoImplicit false

namespace L4YAML.Research.AcceptedSource

open L4YAML Surface Scanner CharPredicates Grammar
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.Acceptance
open L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.TokenGrammar

/-- Read the opening source character without executing any scanner. -/
lemma source_quoted_opening {sp sp' : SurfPos} (h : SCDoubleQuotedOk sp sp') :
    ∃ rest, sp.chars = '"' :: rest := by
  rcases h with ⟨a, b, d, hopen, hbody, hclose⟩
  cases hopen
  exact ⟨_, rfl⟩

/-- The actual initial dispatcher consumes any independently grammatical quoted
source, retaining the actual filtered prefix and the EOF/state obligations. -/
lemma source_quoted_scanNextToken_init (input : String) (col : Nat)
    (h : SCDoubleQuotedOk ⟨input.toList, 0⟩ ⟨[], col⟩) :
    ∃ s₁ content,
      scanNextToken ((ScannerState.mk' input).emit .streamStart) = .ok (some s₁) ∧
      s₁.peek? = none ∧ s₁.flowLevel = 0 ∧ s₁.directivesPresent = false ∧
      s₁.indents = #[{column := -1, isSequence := false}] ∧
      (s₁.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        #[.streamStart, .scalar content .doubleQuoted] := by
  obtain ⟨rest, hstart⟩ := source_quoted_opening h
  change input.toList = '"' :: rest at hstart
  have hcorr₀ := initial_corr input input.toList (chars_from_zero_toList input)
  obtain ⟨s_pp, h_pp, h_fl, h_if, h_ci, h_col, h_ad, h_dp, h_ids,
      h_inp, h_off, h_ie, h_ek, h_line, h_atol, h_bd, h_filter⟩ :=
    scanNextToken_preprocess_init_state input '"' rest hstart
      (by decide) (by decide) (by decide)
  have h_filt_pp :
      (s_pp.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        #[.streamStart] := by
    rw [h_filter]
    simp [ScannerState.emit, ScannerState.mk']
  have hcorr_pp : ScannerSurfCorr s_pp ⟨input.toList, 0⟩ :=
    ScannerSurfCorr_transfer hcorr₀ h_inp h_off h_ie h_col h_ids
  have hcorr_cons : ScannerSurfCorr s_pp ⟨'"' :: rest, 0⟩ := by
    rw [← hstart]
    exact hcorr_pp
  have h_pk := (peek_of_corr hcorr_cons).1
  have h_pat0 : s_pp.peekAt? 0 = s_pp.peek? := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop ScannerState.peek?
    rfl
  have h_ds : atDocumentStart s_pp = false := by
    unfold atDocumentStart
    rw [h_pat0, h_pk]
    simp only [show (some '"' == some '-') = false from by decide,
      Bool.and_false, Bool.false_and]
  have h_de : atDocumentEnd s_pp = false := by
    unfold atDocumentEnd
    rw [h_pat0, h_pk]
    simp only [show (some '"' == some '.') = false from by decide,
      Bool.and_false, Bool.false_and]
  have ⟨h_disp_s, _, _⟩ := dispatchContent_quote s_pp '"' rfl h_fl h_ds h_de
  let s_ad : ScannerState :=
    { s_pp with allowDirectives := false, documentEverStarted := true }
  have ⟨_, h_dfi, h_dbi⟩ := dispatchContent_quote s_ad '"' rfl h_fl h_ds h_de
  have hcorr_ad : ScannerSurfCorr s_ad ⟨input.toList, 0⟩ :=
    ScannerSurfCorr_transfer hcorr_pp rfl rfl rfl rfl rfl
  obtain ⟨s_dq, content, h_dq, hc_dq, h_tok_dq⟩ :=
    scanDoubleQuoted_accepts s_ad hcorr_ad h
      (Or.inr (by trivial : TrailingOk ([] : List Char)))
  have h_pk_dq : s_dq.peek? = none := peek_none_of_empty_surf s_dq col hc_dq
  have h_fl_dq : s_dq.flowLevel = 0 :=
    (L4YAML.Proofs.ScannerPlainScalarValid.scanDoubleQuoted_preserves_flowLevel
      s_ad s_dq h_dq).trans h_fl
  have h_dp_dq : s_dq.directivesPresent = false :=
    (scanDoubleQuoted_preserves_dp s_ad s_dq h_dq).trans h_dp
  have h_ids_dq : s_dq.indents = s_ad.indents :=
    scanDoubleQuoted_preserves_indents s_ad s_dq h_dq
  have h_filt_dq :
      (s_dq.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        #[.streamStart, .scalar content .doubleQuoted] := by
    rw [h_tok_dq]
    simp only [Array.filter_push,
      show (YamlToken.scalar content .doubleQuoted != .placeholder) = true from rfl,
      ite_true, Array.map_push,
      show s_ad.tokens = s_pp.tokens from rfl, h_filt_pp]
    rfl
  have h_dc : ∃ s_final, scanNextToken_dispatchContent s_ad '"' = .ok s_final ∧
      s_final.peek? = none ∧ s_final.flowLevel = 0 ∧
      s_final.directivesPresent = false ∧ s_final.indents = s_ad.indents ∧
      (s_final.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        #[.streamStart, .scalar content .doubleQuoted] := by
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, h_dq]
    exact ⟨_, rfl,
      s_dq.simpleKey.possible.rec h_pk_dq h_pk_dq,
      s_dq.simpleKey.possible.rec h_fl_dq h_fl_dq,
      s_dq.simpleKey.possible.rec h_dp_dq h_dp_dq,
      s_dq.simpleKey.possible.rec h_ids_dq h_ids_dq,
      s_dq.simpleKey.possible.rec h_filt_dq h_filt_dq⟩
  obtain ⟨s_final, h_dc, h_pkf, h_flf, h_dpf, h_idsf, h_filtf⟩ := h_dc
  refine ⟨s_final, content, ?_, h_pkf, h_flf, h_dpf, h_idsf.trans h_ids, h_filtf⟩
  unfold scanNextToken
  simp only [bind, Except.bind, h_pp, h_disp_s]
  simp only [scanNextToken_checkDanglingNode_ok_of_sentinel_stack _ _
    (init_indents_sentinel _) (crossedPropsExcessIdx?_init _)]
  simp only [scanNextToken_checkFlowValueIndent_ok_of_sentinel_stack _ _
    (init_indents_sentinel _)]
  simp only [scanNextToken_checkNoPendingDirectives_ok _ h_dp, h_bd, h_ad, ite_true]
  simp only [scanNextToken_checkAdjacentValue_ok_of_ne_colon _
    (show ('"' : Char) ≠ ':' by decide)]
  exact h_dfi ▸ h_dbi ▸ h_dc ▸ rfl

/-- Whole-input provenance: the exact actual scanner output has precisely the
stream delimiters and the one double-quoted scalar token. -/
lemma source_quoted_scan_tokens (input : String)
    (h : ∃ col, SCDoubleQuotedOk ⟨input.toList, 0⟩ ⟨[], col⟩) :
    ∃ ts content, Scanner.scanFiltered input = .ok ts ∧
      ts.toList.map (·.val) = [.streamStart, .scalar content .doubleQuoted, .streamEnd] := by
  obtain ⟨col, h⟩ := h
  obtain ⟨s₁, content, h_step, h_peek, h_flow, h_dp, h_ids, h_filt⟩ :=
    source_quoted_scanNextToken_init input col h
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have hc := initial_corr input input.toList (chars_from_zero_toList input)
    obtain ⟨rest, hstart⟩ := source_quoted_opening h
    change input.toList = '"' :: rest at hstart
    rw [hstart] at hc
    have hp := (peek_of_corr hc).1
    rw [hp]
    decide
  have h_eof : scanNextToken s₁ = .ok none := scanNextToken_eof s₁ h_peek
  have h_chain : ScanChain ((ScannerState.mk' input).emit .streamStart) 1 s₁ :=
    ScanChain.single h_step
  have h_dn : scanLoop_checkDanglingNode s₁ = .ok () :=
    scanLoop_checkDanglingNode_ok_of_sentinel_stack _ h_ids
      (crossedPropsExcessIdx?_none_of_no_props (no_props_of_filtered_pin h_filt
        (by intro v hv; simp [Array.mem_def] at hv; rcases hv with rfl | rfl <;> rfl)))
  have h_fv : scanLoop_checkFlowValueIndent s₁ = .ok () :=
    scanLoop_checkFlowValueIndent_ok_of_sentinel_stack _ h_ids
  have h_scan := scanFiltered_tokens_eq_of_chain_short_stack input _ s₁ 1 rfl
    h_no_bom h_chain h_eof h_flow h_dp h_dn h_fv (by omega)
    (by rw [h_ids]; decide)
  refine ⟨(s₁.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder),
    content, h_scan, ?_⟩
  have h_final_filter : (s₁.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) =
      (s₁.tokens.filter (fun t => t.val != .placeholder)).push
        { pos := s₁.currentPos, val := .streamEnd } := by
    rw [show (s₁.emit .streamEnd).tokens =
      s₁.tokens.push { pos := s₁.currentPos, val := .streamEnd } from rfl,
      Array.filter_push]
    rfl
  rw [h_final_filter, ← Array.toList_map, Array.map_push, h_filt]
  rfl

/-- The exact token values suffice for both independent parser premises;
positions remain those of the actual scanner output. -/
lemma source_quoted_token_conditions (ts : Array (Positioned YamlToken)) (content : String)
    (hvals : ts.toList.map (·.val) =
      [.streamStart, .scalar content .doubleQuoted, .streamEnd]) :
    TokenGrammar ts ∧ TokenStateOk ts := by
  have ht (i : Nat) : tok ts i =
      ([.streamStart, .scalar content .doubleQuoted, .streamEnd] : List YamlToken)[i]? := by
    unfold tok
    rw [← hvals, List.getElem?_map, ← Array.getElem?_toList]
  have h0 : tok ts 0 = some .streamStart := ht 0
  have h1 : tok ts 1 = some (.scalar content .doubleQuoted) := ht 1
  have h2 : tok ts 2 = some .streamEnd := ht 2
  have hsize : ts.size = 3 := by
    have hs := congrArg List.length hvals
    simpa using hs
  constructor
  · have hn : TG ts .node 1 2 := by
      refine TG.node (m := 1) (TG.props_none ?_) ?_ (TG.content_scalar h1)
      · simp [h1, isProp]
      · intro hlt
        omega
    have hd : TG ts .document 1 2 :=
      TG.document (TG.directives_nil (by simp [h1, isDirective]))
        (Or.inr ⟨by simp [h1], rfl, rfl⟩) hn
    refine ⟨h0, 2, ?_, by omega⟩
    exact TG.stream_doc h1 (by simp) (by simp) rfl hd (by omega)
      (by simp [h2]) (TG.stream_end (Or.inl h2))
  · unfold TokenStateOk L4YAML.Proofs.Serialization.TokenEvents.tokenEvents
    generalize hx : ts.toList = xs
    have hv := hvals
    rw [hx] at hv
    cases xs with
    | nil => simp at hv
    | cons a xs =>
      cases xs with
      | nil => simp at hv
      | cons b xs =>
        cases xs with
        | nil => simp at hv
        | cons c xs =>
          cases xs with
          | cons d xs => simp at hv
          | nil =>
            simp_all [L4YAML.Proofs.Serialization.TokenEvents.go,
              L4YAML.Proofs.Serialization.TokenEvents.tokenEvent,
              L4YAML.Proofs.Serialization.SerializationWellFormed.SerializationWellFormed,
              L4YAML.Proofs.Serialization.SerializationWellFormed.WellFormedFrom]

/-- Independent original-source grammar entails success of the public parser on
that same input, without assuming either scanning or parsing success. -/
lemma source_quoted_public_accepts (input : String)
    (h : ∃ col, SCDoubleQuotedOk ⟨input.toList, 0⟩ ⟨[], col⟩) :
    ∃ docs, TokenParser.parseYaml input = .ok docs := by
  obtain ⟨ts, content, hscan, hvals⟩ := source_quoted_scan_tokens input h
  obtain ⟨hgrammar, hstate⟩ := source_quoted_token_conditions ts content hvals
  obtain ⟨docs, hparse⟩ := parseStream_accepts ts hgrammar hstate
  exact ⟨docs.map YamlDocument.compose,
    L4YAML.Proofs.Composition.parseYaml_pipeline input ts docs hscan hparse⟩

/-- Independent empty-body constructor witness. -/
lemma source_quoted_empty_grammar :
    SCDoubleQuotedOk ⟨("\"\"" : String).toList, 0⟩ ⟨[], 2⟩ := by
  change SCDoubleQuotedOk ⟨['"', '"'], 0⟩ ⟨[], 2⟩
  exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk ['"'] 0)
    (GStar.nil ⟨['"'], 1⟩) (GLit.mk [] 1)

/-- Independent multibyte raw-source constructor witness. -/
lemma source_quoted_multibyte_grammar :
    SCDoubleQuotedOk ⟨("\"é\"" : String).toList, 0⟩ ⟨[], 3⟩ := by
  change SCDoubleQuotedOk ⟨['"', 'é', '"'], 0⟩ ⟨[], 3⟩
  exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk ['é', '"'] 0)
    (GStar.cons _ _ _ (DQCharOk.plain 'é' ['"'] 1 (by decide) (by decide) (by decide))
      (GStar.nil ⟨['"'], 2⟩)) (GLit.mk [] 2)

/-- Noncanonical hex spelling is admitted directly by source constructors. -/
lemma source_quoted_hex_grammar :
    SCDoubleQuotedOk ⟨("\"\\x41\"" : String).toList, 0⟩ ⟨[], 6⟩ := by
  change SCDoubleQuotedOk ⟨['"', '\\', 'x', '4', '1', '"'], 0⟩ ⟨[], 6⟩
  exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk ['\\', 'x', '4', '1', '"'] 0)
    (GStar.cons _ _ _ (DQCharOk.hexEscape2 ['"'] 1 '4' '1'
      (by unfold isNsHexDigit; decide) (by unfold isNsHexDigit; decide) (by decide))
      (GStar.nil ⟨['"'], 5⟩)) (GLit.mk [] 5)

lemma source_quoted_empty_public_accepts :
    ∃ docs, TokenParser.parseYaml "\"\"" = .ok docs :=
  source_quoted_public_accepts _ ⟨2, source_quoted_empty_grammar⟩

lemma source_quoted_multibyte_public_accepts :
    ∃ docs, TokenParser.parseYaml "\"é\"" = .ok docs :=
  source_quoted_public_accepts _ ⟨3, source_quoted_multibyte_grammar⟩

lemma source_quoted_hex_public_accepts :
    ∃ docs, TokenParser.parseYaml "\"\\x41\"" = .ok docs :=
  source_quoted_public_accepts _ ⟨6, source_quoted_hex_grammar⟩

#print axioms source_quoted_opening
#print axioms source_quoted_scanNextToken_init
#print axioms source_quoted_scan_tokens
#print axioms source_quoted_token_conditions
#print axioms source_quoted_public_accepts
#print axioms source_quoted_empty_grammar
#print axioms source_quoted_multibyte_grammar
#print axioms source_quoted_hex_grammar
#print axioms source_quoted_empty_public_accepts
#print axioms source_quoted_multibyte_public_accepts
#print axioms source_quoted_hex_public_accepts

end L4YAML.Research.AcceptedSource
