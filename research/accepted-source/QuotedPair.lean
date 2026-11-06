module

public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Parser.Composition
public import QuotedPublic
public import L4YAML.Proofs.Output.EmitterScannability.FlowStackChain
import all L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section

/-! Original-source pair acceptance, supporting Blueprint group 7.7 closure:
independent five-piece grammar → one-line leaf/flow scanner chain → actual
filtered tokens → parser premises → Composition.parseYaml_pipeline (group 1.1).
No emitter normalization, parser-success premise, or value-fidelity claim.
-/

namespace L4YAML.Research.AcceptedSource

open L4YAML Surface Grammar
open L4YAML.Proofs.Acceptance
open L4YAML Scanner CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.TokenGrammar

set_option autoImplicit false

/-- Five independent source productions. No optional separator whitespace is
    included in this family, and neither scanner nor parser execution defines it. -/
inductive QuotedPair : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s₃ s₄ s' : SurfPos) :
      GLit '[' s s₁ → SCDoubleQuotedOk s₁ s₂ → GLit ',' s₂ s₃ →
      SCDoubleQuotedOk s₃ s₄ → GLit ']' s₄ s' → QuotedPair s s'

/-- One `DQCharOk` step is one iteration of `collectDoubleQuotedLoop`. -/
lemma source_dq_loop_step (sc : ScannerState) {sp sp' : SurfPos}
    (hstep : DQCharOk sp sp') (hcorr : ScannerSurfCorr sc sp)
    (content : String) (fuel' : Nat) (startPos : YamlPos) (inFlow : Bool)
    (ind : Int) (iend : Nat) (pl : Nat) :
    ∃ ch sc' pl',
      collectDoubleQuotedLoop sc content (fuel' + 1) startPos inFlow ind iend pl =
        collectDoubleQuotedLoop sc' (content.push ch) fuel' startPos inFlow ind iend pl' ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧ sc'.line = sc.line := by
  cases hstep with
  | plain c rest col hJ hBs hDq =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (isNbJson_ne_lf hJ) (isNbJson_ne_cr hJ)
    refine ⟨c, sc.advance, if c == ' ' || c == '\t' then pl else (content.push c).length, ?_, hadv, keeps_advance sc,
      advance_line_of_peek sc c (peek_of_corr hcorr).2 hpeek
        (isNbJson_ne_lf hJ) (isNbJson_ne_cr hJ)⟩
    simp only [collectDoubleQuotedLoop, hpeek, isNbJson_not_lineBreak hJ, (isNbJson_iff c).2 hJ,
      Bool.not_true, Bool.false_eq_true, ite_false]
  | escape ec rest col hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    obtain ⟨ch, s', hproc, hc', hk⟩ := processEscape_accepts_named sc.advance ec rest (col + 1) hV hadv
    refine ⟨ch, s', (content.push ch).length, ?_, ?_, (keeps_advance sc).trans hk,
      (L4YAML.Proofs.ScalarProduction.processEscape_line hproc).trans
        (advance_line_of_peek sc '\\' (peek_of_corr hcorr).2 hpeek (by decide) (by decide))⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, namedEscape_not_lineBreak hV, hproc,
        Bool.false_eq_true, ite_false, bind, Except.bind]
    · have : col + 1 + 1 = col + 2 := rfl
      rw [← this]; exact hc'
  | hexEscape2 rest col h1 h2 x1 x2 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'x' [h1, h2] rest (col + 1) 2
      (Or.inl ⟨rfl, rfl⟩) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2]), s', (content.push (Char.ofNat (hexVal [h1, h2]))).length, ?_, ?_,
      (keeps_advance sc).trans hk,
      (L4YAML.Proofs.ScalarProduction.processEscape_line hproc).trans
        (advance_line_of_peek sc '\\' (peek_of_corr hcorr).2 hpeek (by decide) (by decide))⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'x' = false)]
    · have : col + 1 + 1 + 2 = col + 4 := rfl
      rw [← this]; exact hc'
  | hexEscape4 rest col h1 h2 h3 h4 x1 x2 x3 x4 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2, h3, h4] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'u' [h1, h2, h3, h4] rest (col + 1) 4
      (Or.inr (Or.inl ⟨rfl, rfl⟩)) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2, h3, h4]), s', (content.push (Char.ofNat (hexVal [h1, h2, h3, h4]))).length, ?_, ?_,
      (keeps_advance sc).trans hk,
      (L4YAML.Proofs.ScalarProduction.processEscape_line hproc).trans
        (advance_line_of_peek sc '\\' (peek_of_corr hcorr).2 hpeek (by decide) (by decide))⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'u' = false)]
    · have : col + 1 + 1 + 4 = col + 6 := rfl
      rw [← this]; exact hc'
  | hexEscape8 rest col h1 h2 h3 h4 h5 h6 h7 h8 x1 x2 x3 x4 x5 x6 x7 x8 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2, h3, h4, h5, h6, h7, h8] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'U' [h1, h2, h3, h4, h5, h6, h7, h8] rest (col + 1) 8
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2, h3, h4, h5, h6, h7, h8]), s', (content.push (Char.ofNat (hexVal [h1, h2, h3, h4, h5, h6, h7, h8]))).length, ?_, ?_,
      (keeps_advance sc).trans hk,
      (L4YAML.Proofs.ScalarProduction.processEscape_line hproc).trans
        (advance_line_of_peek sc '\\' (peek_of_corr hcorr).2 hpeek (by decide) (by decide))⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'U' = false)]
    · have : col + 1 + 1 + 8 = col + 10 := rfl
      rw [← this]; exact hc'

lemma source_dq_loop_accepts {sp sp' : SurfPos} (hder : GStar DQCharOk sp sp') :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend pl : Nat) (rest : List Char),
      ScannerSurfCorr sc sp → sp.chars.length < fuel → sp'.chars = '"' :: rest →
      ∃ content' sc',
        collectDoubleQuotedLoop sc content fuel startPos inFlow ind iend pl = .ok (content', sc') ∧
        ScannerSurfCorr sc' ⟨rest, sp'.col + 1⟩ ∧ Keeps sc sc' ∧ sc'.line = sc.line := by
  induction hder with
  | nil s =>
    intro sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend
    obtain ⟨chars, col⟩ := s
    simp only at hend hfuel ⊢
    subst hend
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      have hpeek := (peek_of_corr hcorr).1
      refine ⟨content, sc.advance, ?_, advance_corr hcorr (by decide) (by decide), keeps_advance sc,
        advance_line_of_peek sc '"' (peek_of_corr hcorr).2 hpeek (by decide) (by decide)⟩
      simp only [collectDoubleQuotedLoop, hpeek]
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      obtain ⟨ch, sc', pl', heq, hcorr', hk, hl⟩ :=
        source_dq_loop_step sc hstep hcorr content fuel' startPos inFlow ind iend pl
      have hlt := hstep.length_lt
      obtain ⟨content', sc'', hok, hc'', hk', hl'⟩ :=
        ih sc' (content.push ch) fuel' startPos inFlow ind iend pl' rest hcorr' (by omega) hend
      exact ⟨content', sc'', heq.trans hok, hc'', hk.trans hk', hl'.trans hl⟩

/-- The independent one-line source derivation carries the line invariant that
    the generic acceptance helper intentionally omits. Its token retains the
    original scanner position, and its column is the grammar endpoint. -/
lemma source_dq_flow_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : SCDoubleQuotedOk sp sp')
    (hflow : sc.inFlow = true) :
    ∃ s' content, scanDoubleQuoted sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .doubleQuoted } ∧
      s'.line = sc.line ∧ s'.col > 0 ∧ s'.simpleKeyAllowed = false := by
  rcases hder with ⟨a, b, d, h1, hstar, h2⟩
  cases h1 with | mk rest₁ col =>
  cases h2 with | mk rest col₂ =>
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by decide) (by decide)
  have hfuel := fuel_of_corr hadv
  simp only at hfuel
  rw [(keeps_advance sc).2.1] at hfuel
  obtain ⟨content, sc₂, hloop, hc₂, hk, hl⟩ := source_dq_loop_accepts hstar sc.advance ""
    _ sc.currentPos sc.inFlow sc.currentIndent sc.inputEnd 0 rest hadv hfuel rfl
  have hk' := (keeps_advance sc).trans hk
  refine ⟨{ sc₂.emitAt sc.currentPos (.scalar content .doubleQuoted) with
      simpleKeyAllowed := false, needIndentCheck := false }, content, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₂),
    ?_, ?_, ?_, rfl⟩
  · unfold scanDoubleQuoted
    simp only [hloop, bind, Except.bind]
    simp only [hflow, Bool.not_true, Bool.false_eq_true, ite_false]
  · simp [ScannerState.emitAt, hk'.1]
  · exact hl.trans (advance_line_of_peek sc '"' (peek_of_corr hcorr).2 hpeek (by decide) (by decide))
  · have hcol := hc₂.col_eq
    change col₂ + 1 = sc₂.col at hcol
    change sc₂.col > 0
    omega

lemma source_dq_flow_dispatch (s : ScannerState)
    (rest : List Char) (sp' : SurfPos)
    (hcorr : ScannerSurfCorr s ⟨'"' :: rest, s.col⟩)
    (hder : SCDoubleQuotedOk ⟨'"' :: rest, s.col⟩ sp')
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_dp : s.directivesPresent = false)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ s' content, scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' sp'
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        ((s.tokens.filter (fun t => t.val != .placeholder)).map (·.val)).push
          (.scalar content .doubleQuoted) := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' rest s.col
      hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_tokens : s_ad.tokens = (saveSimpleKey s).tokens := by
    simp only [s_ad]; split <;> rfl
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (checkFlowAdjacency_ok_of_notCompletes (fun t ht =>
        saveSimpleKey_preserves_completesFalse s h_last t (h_ad_tokens ▸ ht)))
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'"' :: rest, s.col⟩ := by
    have h_ad_input : s_ad.input = s.input := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s
    have h_ad_offset : s_ad.offset = s.offset := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s
    have h_ad_inputEnd : s_ad.inputEnd = s.inputEnd := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s
    have h_ad_indents : s_ad.indents = s.indents := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
    exact ScannerSurfCorr_transfer hcorr h_ad_input h_ad_offset h_ad_inputEnd h_ad_col h_ad_indents
  have h_ad_flow_bool : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).flowLevel = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  obtain ⟨s_dq, content, h_dq, h_dq_corr, h_dq_raw, h_dq_line, h_dq_col, h_dq_ska⟩ :=
    source_dq_flow_accepts s_ad h_ad_corr hder h_ad_flow_bool
  have h_dq_fl := L4YAML.Proofs.ScannerPlainScalarValid.scanDoubleQuoted_preserves_flowLevel s_ad s_dq h_dq
  have h_dq_dp := scanDoubleQuoted_preserves_dp s_ad s_dq h_dq
  have h_dq_ids := scanDoubleQuoted_preserves_indents s_ad s_dq h_dq
  have h_dq_ek := scanDoubleQuoted_preserves_ek s_ad s_dq h_dq
  have h_dq_tokens : lastRealTokenVal? s_dq.tokens = some (.scalar content .doubleQuoted) := by
    rw [h_dq_raw]
    exact lastRealTokenVal_push_non_ph' s_ad.tokens _ nofun
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    rw [h_ad_tokens, saveSimpleKey_filter_placeholder]
  have h_dq_filter : (s_dq.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
      ((s.tokens.filter (fun t => t.val != .placeholder)).map (·.val)).push
        (.scalar content .doubleQuoted) := by
    rw [h_dq_raw, Array.filter_push]
    simp only [show (YamlToken.scalar content .doubleQuoted != .placeholder) = true from rfl,
      ite_true, Array.map_push, h_ad_filter]
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have h_content : ∃ s_final, scanNextToken_dispatchContent s_ad '"' = .ok s_final
      ∧ ScannerSurfCorr s_final sp'
      ∧ s_final.flowLevel = s.flowLevel
      ∧ s_final.directivesPresent = s.directivesPresent
      ∧ s_final.indents = s.indents
      ∧ s_final.explicitKeyLine = s.explicitKeyLine
      ∧ s_final.col > 0
      ∧ lastRealTokenVal? s_final.tokens = some (.scalar content .doubleQuoted)
      ∧ s_final.simpleKeyAllowed = false
      ∧ s_final.line = s.line
      ∧ AllTokensOnLine s_final s.line
      ∧ EndLineOnLine s_final
      ∧ s_final.simpleKeyStack = s.simpleKeyStack
      ∧ (s_final.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        ((s.tokens.filter (fun t => t.val != .placeholder)).map (·.val)).push
          (.scalar content .doubleQuoted) := by
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, Except.pure, h_dq]
    have h_atol_ad : AllTokensOnLine s_ad s.line :=
      AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)
    have h_atol_dq : AllTokensOnLine s_dq s.line :=
      AllTokensOnLine_scanDoubleQuoted s_ad s_dq h_dq h_ad_flow_bool
        s.line h_atol_ad h_ad_line
    have h_sk_dq : s_dq.simpleKey = s_ad.simpleKey :=
      scanDoubleQuoted_preserves_simpleKey s_ad s_dq h_dq
    have h_dq_stack : s_dq.simpleKeyStack = s_ad.simpleKeyStack :=
      ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s_ad s_dq h_dq
    have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    cases h_skp : s_dq.simpleKey.possible
    · -- simpleKey.possible = false: s' = s_dq
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, h_dq_corr,
        h_dq_fl.trans h_ad_fl, h_dq_dp.trans h_ad_dp, h_dq_ids.trans h_ad_ids,
        h_dq_ek.trans h_ad_ek, h_dq_col, h_dq_tokens, h_dq_ska,
        h_dq_line.trans h_ad_line, h_atol_dq, ?_, h_dq_stack.trans h_ad_stack, h_dq_filter⟩
      · intro h_poss; rw [h_skp] at h_poss; exact absurd h_poss (by decide)
    · -- simpleKey.possible = true: s' = { s_dq with simpleKey endLine update }
      simp only [↓reduceIte]
      refine ⟨_, rfl,
        ⟨h_dq_corr.chars_from, h_dq_corr.col_eq, h_dq_corr.end_eq,
         h_dq_corr.input_prefix, h_dq_corr.indent_cols_nonneg⟩,
        h_dq_fl.trans h_ad_fl, h_dq_dp.trans h_ad_dp, h_dq_ids.trans h_ad_ids,
        h_dq_ek.trans h_ad_ek, h_dq_col, h_dq_tokens, h_dq_ska,
        h_dq_line.trans h_ad_line, h_atol_dq, ?_, h_dq_stack.trans h_ad_stack, h_dq_filter⟩
      · -- EndLineOnLine: endLine just set to s_dq.line, pos from saveSimpleKey
        intro _
        constructor
        · rfl
        · show s_dq.simpleKey.pos.line = s_dq.line
          rw [h_sk_dq]
          have h_ad_sk : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
            simp only [s_ad]; split <;> rfl
          rw [h_ad_sk]
          have h_eol_sk := EndLineOnLine_saveSimpleKey_flow s h_endline
          have h_sk_poss : (saveSimpleKey s).simpleKey.possible = true := by
            rw [← h_ad_sk, ← h_sk_dq]; exact h_skp
          exact (h_eol_sk h_sk_poss).2 |>.trans (saveSimpleKey_preserves_line s)
            |>.trans (h_dq_line.trans h_ad_line).symm
  obtain ⟨s_final, h_dc_eq, h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_ek_f, h_col_f, h_tok_f, h_ska_f, h_line_f, h_atol_f, h_endline_f, h_stack_f, h_filter_f⟩ := h_content
  exact ⟨s_final, content, scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow)
    h_flow_none h_block_none
    (scanNextToken_checkAdjacentValue_ok_of_ne_colon _ (by decide)) h_dc_eq
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow),
    h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_ek_f, h_col_f,
    fun t ht => by rw [h_tok_f] at ht; injection ht with ht; subst ht; exact ⟨nofun, nofun, nofun⟩,
    h_ska_f, h_line_f, (by rw [h_line_f]; exact h_atol_f), h_endline_f, h_stack_f, h_filter_f⟩

/-- Level-preserving actual steps also preserve the actual flow-kind stack. -/
lemma source_flow_stack_of_level {s s' : ScannerState}
    (hstep : scanNextToken s = .ok (some s')) (hlevel : s'.flowLevel = s.flowLevel) :
    s'.flowStack = s.flowStack := by
  rcases scanNextToken_flowStack_step hstep with h | h | h | h
  · exact h.2
  · omega
  · omega
  · omega

#print axioms source_dq_loop_step
/-- Reading only the five source constructors exposes the three delimiters. -/
lemma source_pair_parts {sp sp' : SurfPos} (h : QuotedPair sp sp') :
    ∃ left right tail ca cb,
      sp.chars = '[' :: left ∧ sp'.chars = tail ∧
      SCDoubleQuotedOk ⟨left, sp.col + 1⟩ ⟨',' :: right, ca⟩ ∧
      SCDoubleQuotedOk ⟨right, ca + 1⟩ ⟨']' :: tail, cb⟩ := by
  rcases h with ⟨s₁, s₂, s₃, s₄, e, ho, ha, hc, hb, hz⟩
  cases ho
  cases hc
  cases hz
  exact ⟨_, _, _, _, _, rfl, rfl, ha, hb⟩

/-- Exact seven-token provenance for the original five-piece source grammar. -/
lemma source_quoted_pair_scan_tokens (input : String)
    (h : ∃ col, QuotedPair ⟨input.toList, 0⟩ ⟨[], col⟩) :
    ∃ ts a b, Scanner.scanFiltered input = .ok ts ∧
      ts.toList.map (·.val) = [.streamStart, .flowSequenceStart,
        .scalar a .doubleQuoted, .flowEntry, .scalar b .doubleQuoted,
        .flowSequenceEnd, .streamEnd] := by
  obtain ⟨col, h⟩ := h
  obtain ⟨left, right, tail, ca, cb, hstart, htail, ha, hb⟩ := source_pair_parts h
  change input.toList = '[' :: left at hstart
  change [] = tail at htail
  subst tail
  obtain ⟨s₁, h₁, hc₁, hf₁, hd₁, hi₁, hcol₁, hflow₁, hind₁, hek₁,
    hl₁, hat₁, hel₁, hkey₁, ht₁, hks₁, hska₁, hvalid₁, hlast₁, hkind₁⟩ :=
    scanNextToken_flow_open_init input left hstart
  obtain ⟨leftBody, hleft⟩ := source_quoted_opening ha
  change left = '"' :: leftBody at hleft
  subst left
  have ha₁ : SCDoubleQuotedOk ⟨'"' :: leftBody, s₁.col⟩ ⟨',' :: right, ca⟩ := by
    rw [hcol₁]
    exact ha
  obtain ⟨s₂, a, h₂, hc₂, hf₂, hd₂, hi₂, hek₂, hcol₂, hlast₂, hska₂,
    hl₂, hat₂, hel₂, hks₂, ht₂⟩ :=
    source_dq_flow_dispatch s₁ leftBody _ hc₁ ha₁ hflow₁ hind₁ (by omega)
      (by rw [hl₁]; exact hat₁) hel₁ hd₁ hlast₁
  have hflow₂ : s₂.inFlow = true := by simp [ScannerState.inFlow, hf₂, hf₁]
  have hind₂ : s₂.currentIndent < 0 := by
    unfold ScannerState.currentIndent at *
    rw [hi₂]
    exact hind₁
  have hcorr₂ : ScannerSurfCorr s₂ ⟨',' :: right, s₂.col⟩ := by
    rw [← hc₂.col_eq]
    exact hc₂
  obtain ⟨s₃, h₃, hc₃, hf₃, hd₃, hi₃, hek₃, hcol₃, hl₃, hat₃, hel₃, hks₃, hlast₃⟩ :=
    scanNextToken_flow_comma s₂ right hcorr₂ hflow₂ hind₂ hcol₂ hlast₂ hat₂ hel₂
      (hek₂.trans hek₁) (hd₂.trans hd₁)
  obtain ⟨comma, hcomma, ht₃⟩ :=
    scanNextToken_flow_comma_filtered_push s₂ right hcorr₂ hflow₂ hind₂ hcol₂ hlast₂ h₃
  have hflow₃ : s₃.inFlow = true := by simp [ScannerState.inFlow, hf₃, hf₂, hf₁]
  have hind₃ : s₃.currentIndent < 0 := by
    unfold ScannerState.currentIndent at *
    rw [hi₃]
    exact hind₂
  obtain ⟨rightBody, hright⟩ := source_quoted_opening hb
  change right = '"' :: rightBody at hright
  subst right
  have hb₃ : SCDoubleQuotedOk ⟨'"' :: rightBody, s₃.col⟩ ⟨[']'], cb⟩ := by
    have hca : ca = s₂.col := hc₂.col_eq
    rw [hcol₃, ← hca]
    exact hb
  obtain ⟨s₄, b, h₄, hc₄, hf₄, hd₄, hi₄, hek₄, hcol₄, hlast₄, hska₄,
    hl₄, hat₄, hel₄, hks₄, ht₄⟩ :=
    source_dq_flow_dispatch s₃ rightBody _ hc₃ hb₃ hflow₃ hind₃ (by omega)
      hat₃ hel₃ (hd₃.trans (hd₂.trans hd₁)) hlast₃
  have hflow₄ : s₄.inFlow = true := by simp [ScannerState.inFlow, hf₄, hf₃, hf₂, hf₁]
  have hind₄ : s₄.currentIndent < 0 := by
    unfold ScannerState.currentIndent at *
    rw [hi₄]
    exact hind₃
  have hcorr₄ : ScannerSurfCorr s₄ ⟨[']'], s₄.col⟩ := by
    rw [← hc₄.col_eq]
    exact hc₄
  have hlevel₄ : s₄.flowLevel = 1 := hf₄.trans (hf₃.trans (hf₂.trans hf₁))
  have hdp₄ : s₄.directivesPresent = false := hd₄.trans (hd₃.trans (hd₂.trans hd₁))
  have hkind₄ : s₄.flowStack.back? = some true := by
    rw [source_flow_stack_of_level h₄ hf₄, source_flow_stack_of_level h₃ hf₃,
      source_flow_stack_of_level h₂ hf₂]
    exact hkind₁
  have hids₄ : s₄.indents = #[{column := -1, isSequence := false}] := by
    rw [hi₄, hi₃, hi₂, hi₁]
    rfl
  have hvals₄ : (s₄.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
      #[.streamStart, .flowSequenceStart, .scalar a .doubleQuoted, .flowEntry,
        .scalar b .doubleQuoted] := by
    rw [ht₄, ht₃, Array.map_push, hcomma, ht₂, ht₁]
    rfl
  obtain ⟨s₅, h₅, hf₅, hd₅, hp₅, hi₅, close, hclose, ht₅⟩ :=
    scanNextToken_flow_close_seq_outermost_ext s₄ hcorr₄ hflow₄ hind₄ hcol₄ hlevel₄ hdp₄ hkind₄
  obtain ⟨s₅', h₅', _, _, _, hdn, hfv⟩ :=
    scanNextToken_flow_close_seq_outermost s₄ hcorr₄ hflow₄ hind₄ hcol₄ hlevel₄ hdp₄ hkind₄ hids₄
      (no_props_of_filtered_pin hvals₄ (by
        intro v hv
        simp [Array.mem_def] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl <;> rfl))
  have heq : s₅' = s₅ := Option.some.inj (Except.ok.inj (h₅'.symm.trans h₅))
  subst s₅'
  have heof : scanNextToken s₅ = .ok none := scanNextToken_eof s₅ hp₅
  have hchain : ScanChain ((ScannerState.mk' input).emit .streamStart) 5 s₅ :=
    .step h₁ (.step h₂ (.step h₃ (.step h₄ (.single h₅))))
  have hnobom : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have hc := initial_corr input input.toList (chars_from_zero_toList input)
    rw [hstart] at hc
    rw [(peek_of_corr hc).1]
    decide
  have hscan := scanFiltered_tokens_eq_of_chain_short_stack input _ s₅ 5 rfl hnobom hchain
    heof hf₅ hd₅ hdn hfv (ScanChain.fuel_bound _ _ _ _ rfl hchain heof)
    (by rw [hi₅, hids₄]; decide)
  refine ⟨(s₅.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder), a, b, hscan, ?_⟩
  have hlast : (s₅.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) =
      (s₅.tokens.filter (fun t => t.val != .placeholder)).push
        {pos := s₅.currentPos, val := .streamEnd} := by
    rw [show (s₅.emit .streamEnd).tokens =
      s₅.tokens.push {pos := s₅.currentPos, val := .streamEnd} from rfl, Array.filter_push]
    rfl
  rw [hlast, ← Array.toList_map, Array.map_push, ht₅, Array.map_push, hclose, hvals₄]
  rfl

/-- Token grammar and serialization obligations on the actual scanner output;
    scalar/flow tokens impose no positional property side conditions. -/
lemma source_quoted_pair_token_conditions (ts : Array (Positioned YamlToken)) (a b : String)
    (hvals : ts.toList.map (·.val) = [.streamStart, .flowSequenceStart,
      .scalar a .doubleQuoted, .flowEntry, .scalar b .doubleQuoted,
      .flowSequenceEnd, .streamEnd]) :
    L4YAML.Proofs.TokenGrammar.TokenGrammar ts ∧ L4YAML.Proofs.TokenGrammar.TokenStateOk ts := by
  have ht (i : Nat) : tok ts i =
      ([.streamStart, .flowSequenceStart, .scalar a .doubleQuoted, .flowEntry,
        .scalar b .doubleQuoted, .flowSequenceEnd, .streamEnd] : List YamlToken)[i]? := by
    unfold tok
    rw [← hvals, List.getElem?_map, ← Array.getElem?_toList]
  have hsize : ts.size = 7 := by
    have hs := congrArg List.length hvals
    simpa using hs
  constructor
  · have h0 : tok ts 0 = some .streamStart := ht 0
    have h1 : tok ts 1 = some .flowSequenceStart := ht 1
    have h2 : tok ts 2 = some (.scalar a .doubleQuoted) := ht 2
    have h3 : tok ts 3 = some .flowEntry := ht 3
    have h4 : tok ts 4 = some (.scalar b .doubleQuoted) := ht 4
    have h5 : tok ts 5 = some .flowSequenceEnd := ht 5
    have h6 : tok ts 6 = some .streamEnd := ht 6
    have hn2 : TG ts .node 2 3 := by
      refine TG.node (m := 2) (TG.props_none ?_) ?_ (TG.content_scalar h2)
      · simp [h2, isProp]
      · intro hlt; omega
    have hn4 : TG ts .node 4 5 := by
      refine TG.node (m := 4) (TG.props_none ?_) ?_ (TG.content_scalar h4)
      · simp [h4, isProp]
      · intro hlt; omega
    have hitems3 : TG ts (.flowSeqItems false) 3 5 :=
      TG.flowSeqItems_node (by simp [h3]) (Or.inr ⟨rfl, h3, rfl⟩)
        (by simp [h4]) (by simp [h4]) hn4 (TG.flowSeqItems_end h5)
    have hitems2 : TG ts (.flowSeqItems true) 2 5 :=
      TG.flowSeqItems_node (by simp [h2]) (Or.inl ⟨rfl, rfl⟩)
        (by simp [h2]) (by simp [h2]) hn2 hitems3
    have hn : TG ts .node 1 6 := by
      refine TG.node (m := 1) (TG.props_none ?_) ?_
        (TG.content_flowSeq (TG.flowSeq h1 hitems2 h5))
      · simp [h1, isProp]
      · intro hlt; omega
    have hd : TG ts .document 1 6 :=
      TG.document (TG.directives_nil (by simp [h1, isDirective]))
        (Or.inr ⟨by simp [h1], rfl, rfl⟩) hn
    refine ⟨h0, 6, ?_, by omega⟩
    exact TG.stream_doc h1 (by simp) (by simp) rfl hd (by omega)
      (by simp [h6]) (TG.stream_end (Or.inl h6))
  · unfold L4YAML.Proofs.TokenGrammar.TokenStateOk
      L4YAML.Proofs.Serialization.TokenEvents.tokenEvents
    generalize hx : ts.toList = xs
    have hv := hvals
    rw [hx] at hv
    cases xs with
    | nil => simp at hv
    | cons t0 xs =>
      cases xs with
      | nil => simp at hv
      | cons t1 xs =>
        cases xs with
        | nil => simp at hv
        | cons t2 xs =>
          cases xs with
          | nil => simp at hv
          | cons t3 xs =>
            cases xs with
            | nil => simp at hv
            | cons t4 xs =>
              cases xs with
              | nil => simp at hv
              | cons t5 xs =>
                cases xs with
                | nil => simp at hv
                | cons t6 xs =>
                  cases xs with
                  | cons t7 xs => simp at hv
                  | nil =>
                    simp_all [L4YAML.Proofs.Serialization.TokenEvents.go,
                      L4YAML.Proofs.Serialization.TokenEvents.tokenEvent,
                      L4YAML.Proofs.Serialization.SerializationWellFormed.SerializationWellFormed,
                      L4YAML.Proofs.Serialization.SerializationWellFormed.WellFormedFrom]

/-- Independent original five-piece source grammar entails actual public parse success. -/
lemma source_quoted_pair_public_accepts (input : String)
    (h : ∃ col, QuotedPair ⟨input.toList, 0⟩ ⟨[], col⟩) :
    ∃ docs, TokenParser.parseYaml input = .ok docs := by
  obtain ⟨ts, a, b, hscan, hvals⟩ := source_quoted_pair_scan_tokens input h
  obtain ⟨hgrammar, hstate⟩ := source_quoted_pair_token_conditions ts a b hvals
  obtain ⟨docs, hparse⟩ := L4YAML.Proofs.TokenGrammar.parseStream_accepts ts hgrammar hstate
  exact ⟨docs.map YamlDocument.compose,
    L4YAML.Proofs.Composition.parseYaml_pipeline input ts docs hscan hparse⟩

/-- Both leaves may have empty bodies; this is a constructor witness, not a run. -/
lemma source_quoted_pair_empty_grammar :
    QuotedPair ⟨("[\"\",\"\"]" : String).toList, 0⟩ ⟨[], 7⟩ := by
  change QuotedPair ⟨['[', '"', '"', ',', '"', '"', ']'], 0⟩ ⟨[], 7⟩
  refine QuotedPair.mk _ _ _ _ _ _ (GLit.mk _ 0) ?_ (GLit.mk _ 3) ?_ (GLit.mk [] 6)
  · exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk _ 1)
      (GStar.nil ⟨['"', ',', '"', '"', ']'], 2⟩) (GLit.mk _ 2)
  · exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk _ 4)
      (GStar.nil ⟨['"', ']'], 5⟩) (GLit.mk _ 5)

/-- Raw multibyte source in both leaves, with character columns distinct from bytes. -/
lemma source_quoted_pair_multibyte_grammar :
    QuotedPair ⟨("[\"é\",\"𝄞\"]" : String).toList, 0⟩ ⟨[], 9⟩ := by
  change QuotedPair ⟨['[', '"', 'é', '"', ',', '"', '𝄞', '"', ']'], 0⟩ ⟨[], 9⟩
  refine QuotedPair.mk _ _ _ _ _ _ (GLit.mk _ 0) ?_ (GLit.mk _ 4) ?_ (GLit.mk [] 8)
  · exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk _ 1)
      (GStar.cons _ _ _
        (DQCharOk.plain 'é' ['"', ',', '"', '𝄞', '"', ']'] 2 (by decide) (by decide) (by decide))
        (GStar.nil ⟨['"', ',', '"', '𝄞', '"', ']'], 3⟩)) (GLit.mk _ 3)
  · exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk _ 5)
      (GStar.cons _ _ _
        (DQCharOk.plain '𝄞' ['"', ']'] 6 (by decide) (by decide) (by decide))
        (GStar.nil ⟨['"', ']'], 7⟩)) (GLit.mk _ 7)

/-- Noncanonical original hexadecimal spellings are independently grammatical. -/
lemma source_quoted_pair_hex_grammar :
    QuotedPair ⟨("[\"\\x41\",\"\\u0042\"]" : String).toList, 0⟩ ⟨[], 17⟩ := by
  change QuotedPair ⟨['[', '"', '\\', 'x', '4', '1', '"', ',', '"', '\\', 'u',
    '0', '0', '4', '2', '"', ']'], 0⟩ ⟨[], 17⟩
  refine QuotedPair.mk _ _ _ _ _ _ (GLit.mk _ 0) ?_ (GLit.mk _ 7) ?_ (GLit.mk [] 16)
  · exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk _ 1)
      (GStar.cons _ _ _
        (DQCharOk.hexEscape2 ['"', ',', '"', '\\', 'u', '0', '0', '4', '2', '"', ']'] 2 '4' '1'
          (by unfold isNsHexDigit; decide) (by unfold isNsHexDigit; decide) (by decide))
        (GStar.nil ⟨['"', ',', '"', '\\', 'u', '0', '0', '4', '2', '"', ']'], 6⟩)) (GLit.mk _ 6)
  · exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk _ 8)
      (GStar.cons _ _ _
        (DQCharOk.hexEscape4 ['"', ']'] 9 '0' '0' '4' '2'
          (by unfold isNsHexDigit; decide) (by unfold isNsHexDigit; decide)
          (by unfold isNsHexDigit; decide) (by unfold isNsHexDigit; decide) (by decide))
        (GStar.nil ⟨['"', ']'], 15⟩)) (GLit.mk _ 15)

lemma source_quoted_pair_empty_public_accepts :
    ∃ docs, TokenParser.parseYaml "[\"\",\"\"]" = .ok docs :=
  source_quoted_pair_public_accepts _ ⟨7, source_quoted_pair_empty_grammar⟩

lemma source_quoted_pair_multibyte_public_accepts :
    ∃ docs, TokenParser.parseYaml "[\"é\",\"𝄞\"]" = .ok docs :=
  source_quoted_pair_public_accepts _ ⟨9, source_quoted_pair_multibyte_grammar⟩

lemma source_quoted_pair_hex_public_accepts :
    ∃ docs, TokenParser.parseYaml "[\"\\x41\",\"\\u0042\"]" = .ok docs :=
  source_quoted_pair_public_accepts _ ⟨17, source_quoted_pair_hex_grammar⟩

#print axioms source_quoted_pair_empty_grammar
#print axioms source_quoted_pair_multibyte_grammar
#print axioms source_quoted_pair_hex_grammar
#print axioms source_quoted_pair_empty_public_accepts
#print axioms source_quoted_pair_multibyte_public_accepts
#print axioms source_quoted_pair_hex_public_accepts
#print axioms source_quoted_pair_token_conditions
#print axioms source_quoted_pair_public_accepts
#print axioms source_pair_parts
#print axioms source_quoted_pair_scan_tokens
#print axioms source_dq_loop_accepts
#print axioms source_dq_flow_accepts
#print axioms source_dq_flow_dispatch
#print axioms source_flow_stack_of_level

end L4YAML.Research.AcceptedSource
