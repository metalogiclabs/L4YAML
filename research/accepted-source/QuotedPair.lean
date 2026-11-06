module

public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Parser.Composition
public import QuotedPublic

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
    simp only [hloop, bind, Except.bind, hflow, Bool.not_true, Bool.false_eq_true, ite_false]
  · simp [ScannerState.emitAt, hk'.1]
  · exact hl.trans (advance_line_of_peek sc '"' (peek_of_corr hcorr).2 hpeek (by decide) (by decide))
  · have hcol := hc₂.col_eq
    change col₂ + 1 = sc₂.col at hcol
    change sc₂.col > 0
    omega

#print axioms source_dq_loop_step
#print axioms source_dq_loop_accepts
#print axioms source_dq_flow_accepts

end L4YAML.Research.AcceptedSource
