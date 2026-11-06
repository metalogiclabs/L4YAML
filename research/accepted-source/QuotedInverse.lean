module

public import L4YAML.Proofs.Production.Acceptance.Quoted

@[expose] public section

/-! # Source-connected one-line double-quoted inverse

Research dependency path: successful original-source quoted scan →
`SCDoubleQuotedOk` source reconstruction → no-drop accepted-source fragment →
Blueprint group 7.7 `parse_iff_grammar` converse / revised biconditional.
This is a leaf scanner result, not public parser or flow-collection closure.
The one-line premise restricts raw source, not decoded contents: every named
escape and every valid Unicode hex escape remains in the grammar.
No decoded-content fidelity is asserted.
-/

set_option autoImplicit false

namespace L4YAML.Research.AcceptedSource

open L4YAML Surface Scanner CharPredicates Grammar
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Proofs.Acceptance

/-- Retain the Unicode validity guard discarded by the broad production lemma. -/
lemma parseHexEscape_prod_valid (sc : ScannerState) (chars : List Char) (col n : Nat)
    {ch : Char} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc ⟨chars, col⟩)
    (hok : parseHexEscape sc n = .ok (ch, s')) :
    ∃ ds rest, chars = ds ++ rest ∧ ds.length = n ∧
      (∀ c, c ∈ ds → isNsHexDigit c) ∧ (hexVal ds).isValidChar ∧
      ScannerSurfCorr s' ⟨rest, col + n⟩ := by
  obtain ⟨ds, rest, hchars, hlen, hhex, hc'⟩ :=
    parseHexEscape_prod sc chars col n hcorr hok
  have hc : ScannerSurfCorr sc ⟨ds ++ rest, col⟩ := by rw [← hchars]; exact hcorr
  obtain ⟨hcollected, _, _⟩ := collectHexDigitsLoop_accepts ds sc "" rest col hhex hc
  rw [hlen] at hcollected
  have hfold : (collectHexDigitsLoop sc "" n).1.foldl
      (fun acc c => acc * 16 + if c.isDigit then c.toNat - '0'.toNat
        else if c >= 'a' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10) 0
      = hexVal ds := by
    rw [String.foldl_eq_foldl_toList, hcollected]; rfl
  refine ⟨ds, rest, hchars, hlen, hhex, ?_, hc'⟩
  unfold parseHexEscape at hok
  dsimp only [] at hok
  split at hok
  · simp at hok
  · rw [hfold] at hok
    split at hok
    · assumption
    · simp at hok

/-- A successful escape reconstructs the same admissible character relation. -/
lemma processEscape_prod_ok (sc_bs : ScannerState) (rest : List Char) (col : Nat)
    {ch : Char} {s' : ScannerState}
    (hcorr_bs : ScannerSurfCorr sc_bs ⟨rest, col + 1⟩)
    (hproc : processEscape sc_bs = .ok (ch, s')) :
    ∃ sp', DQCharOk ⟨'\\' :: rest, col⟩ sp' ∧ ScannerSurfCorr s' sp' := by
  unfold processEscape at hproc
  split at hproc
  · simp at hproc
  · rename_i c_esc hpeek
    obtain ⟨rest_tail, hsp_eq⟩ := peek_some_sp hcorr_bs hpeek
    injection hsp_eq with h_rest h_col
    subst h_rest
    have h_col_eq : sc_bs.col = col + 1 := h_col.symm
    have hcorr_sc : ScannerSurfCorr sc_bs ⟨c_esc :: rest_tail, sc_bs.col⟩ := by
      rw [h_col_eq]; exact hcorr_bs
    have hmore := peek_some_has_more hpeek
    dsimp only [] at hproc
    split at hproc <;> (first
      | (obtain ⟨-, rfl⟩ := hproc; try subst_vars
         have ha := advance_non_newline_corr sc_bs _ rest_tail hcorr_sc hmore (by decide) (by decide)
         rw [h_col_eq] at ha
         exact ⟨⟨rest_tail, col + 2⟩, DQCharOk.escape _ rest_tail col (by decide), ha⟩)
      | skip)
    · try subst_vars
      have ha := advance_non_newline_corr sc_bs 'x' rest_tail hcorr_sc hmore (by decide) (by decide)
      rw [h_col_eq] at ha
      obtain ⟨consumed, rest_hex, hchars_hex, hlen_c, hhex_all, hval, hcorr_hex⟩ :=
        parseHexEscape_prod_valid sc_bs.advance rest_tail (col + 2) 2 ha hproc
      obtain ⟨h1, tl1, rfl, htl1⟩ := list_eq_cons hlen_c
      obtain ⟨h2, tl2, rfl, htl2⟩ := list_eq_cons htl1
      cases tl2 with | cons => simp at htl2 | nil =>
      simp only [List.cons_append, List.nil_append] at hchars_hex
      subst hchars_hex
      exact ⟨⟨rest_hex, col + 4⟩,
        DQCharOk.hexEscape2 rest_hex col h1 h2
          (hhex_all h1 (by simp)) (hhex_all h2 (by simp)) hval, hcorr_hex⟩
    · try subst_vars
      have ha := advance_non_newline_corr sc_bs 'u' rest_tail hcorr_sc hmore (by decide) (by decide)
      rw [h_col_eq] at ha
      obtain ⟨consumed, rest_hex, hchars_hex, hlen_c, hhex_all, hval, hcorr_hex⟩ :=
        parseHexEscape_prod_valid sc_bs.advance rest_tail (col + 2) 4 ha hproc
      obtain ⟨h1, tl4, rfl, htl4⟩ := list_eq_cons hlen_c
      obtain ⟨h2, tl3, rfl, htl3⟩ := list_eq_cons htl4
      obtain ⟨h3, tl2, rfl, htl2⟩ := list_eq_cons htl3
      obtain ⟨h4, tl1, rfl, htl1⟩ := list_eq_cons htl2
      cases tl1 with | cons => simp at htl1 | nil =>
      simp only [List.cons_append, List.nil_append] at hchars_hex
      subst hchars_hex
      exact ⟨⟨rest_hex, col + 6⟩,
        DQCharOk.hexEscape4 rest_hex col h1 h2 h3 h4
          (hhex_all h1 (by simp)) (hhex_all h2 (by simp))
          (hhex_all h3 (by simp)) (hhex_all h4 (by simp)) hval, hcorr_hex⟩
    · try subst_vars
      have ha := advance_non_newline_corr sc_bs 'U' rest_tail hcorr_sc hmore (by decide) (by decide)
      rw [h_col_eq] at ha
      obtain ⟨consumed, rest_hex, hchars_hex, hlen_c, hhex_all, hval, hcorr_hex⟩ :=
        parseHexEscape_prod_valid sc_bs.advance rest_tail (col + 2) 8 ha hproc
      obtain ⟨h1, tl8, rfl, htl8⟩ := list_eq_cons hlen_c
      obtain ⟨h2, tl7, rfl, htl7⟩ := list_eq_cons htl8
      obtain ⟨h3, tl6, rfl, htl6⟩ := list_eq_cons htl7
      obtain ⟨h4, tl5, rfl, htl5⟩ := list_eq_cons htl6
      obtain ⟨h5, tl4, rfl, htl4⟩ := list_eq_cons htl5
      obtain ⟨h6, tl3, rfl, htl3⟩ := list_eq_cons htl4
      obtain ⟨h7, tl2, rfl, htl2⟩ := list_eq_cons htl3
      obtain ⟨h8, tl1, rfl, htl1⟩ := list_eq_cons htl2
      cases tl1 with | cons => simp at htl1 | nil =>
      simp only [List.cons_append, List.nil_append] at hchars_hex
      subst hchars_hex
      exact ⟨⟨rest_hex, col + 10⟩,
        DQCharOk.hexEscape8 rest_hex col h1 h2 h3 h4 h5 h6 h7 h8
          (hhex_all h1 (by simp)) (hhex_all h2 (by simp))
          (hhex_all h3 (by simp)) (hhex_all h4 (by simp))
          (hhex_all h5 (by simp)) (hhex_all h6 (by simp))
          (hhex_all h7 (by simp)) (hhex_all h8 (by simp)) hval, hcorr_hex⟩
    · simp at hproc

/-- Source membership, not decoded character membership, propagates one-line scope. -/
lemma dqCharOk_source_mem {sp sp' : SurfPos} (h : DQCharOk sp sp')
    {c : Char} (hc : c ∈ sp'.chars) : c ∈ sp.chars := by
  cases h <;> simp only [List.mem_cons] <;> simp_all

/-- Loop reconstruction with the raw-source one-line premise. -/
lemma collectDoubleQuotedLoop_prod_ok_oneLine (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd p : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hline : ∀ c ∈ sp.chars, c ≠ '\n' ∧ c ≠ '\r')
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd p
      = .ok (result_content, s')) :
    ∃ sp_body sp_close, GStar DQCharOk sp sp_body ∧
      GLit '"' sp_body sp_close ∧ ScannerSurfCorr s' sp_close := by
  induction fuel generalizing sc sp content p with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      exact ⟨⟨'"' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩, GStar.nil _, GLit.mk rest sc.col,
        advance_non_newline_corr sc '"' rest hcorr
          (peek_some_has_more hpeek) (by decide) (by decide)⟩
    · rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv := advance_non_newline_corr sc '\\' rest hcorr
        (peek_some_has_more hpeek) (by decide) (by decide)
      dsimp only [] at hok
      split at hok
      · rename_i c2 hpeek2
        split at hok
        · rename_i hlb2
          obtain ⟨tail, heq⟩ := peek_some_sp hcorr_adv hpeek2
          have hr : rest = c2 :: tail := congrArg SurfPos.chars heq
          have hn := hline c2 (by simp [hr])
          rcases (isLineBreak_iff c2).1 hlb2 with hl | hr
          · exact False.elim (hn.1 (by simpa [isLineFeedProp] using hl))
          · exact False.elim (hn.2 (by simpa [isCarriageReturnProp] using hr))
        · simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i esc_result hproc
            obtain ⟨sp_esc, hchar, hc_esc⟩ := processEscape_prod_ok sc.advance rest sc.col hcorr_adv hproc
            have hl_esc : ∀ c ∈ sp_esc.chars, c ≠ '\n' ∧ c ≠ '\r' :=
              fun c hc => hline c (dqCharOk_source_mem hchar hc)
            obtain ⟨sp_body, sp_close, hb, hg, hc⟩ := ih _ _ _ _ hc_esc hl_esc hok
            exact ⟨sp_body, sp_close, GStar.cons _ _ _ hchar hb, hg, hc⟩
      · exact absurd hok (by simp)
    · rename_i _opt c hne_dq hne_bs hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hn := hline c (by simp)
      split at hok
      · rename_i hlb
        rcases (isLineBreak_iff c).1 hlb with hl | hr
        · exact False.elim (hn.1 (by simpa [isLineFeedProp] using hl))
        · exact False.elim (hn.2 (by simpa [isCarriageReturnProp] using hr))
      · split at hok
        · simp at hok
        · rename_i hne_lb hne_ctrl
          have hjson : isNbJsonProp c := (isNbJson_iff c).1 (by simpa using hne_ctrl)
          have hc_adv := advance_non_newline_corr sc c rest hcorr (peek_some_has_more hpeek) hn.1 hn.2
          have hl_adv : ∀ d ∈ rest, d ≠ '\n' ∧ d ≠ '\r' :=
            fun d hd => hline d (List.mem_cons_of_mem c hd)
          obtain ⟨sp_body, sp_close, hb, hg, hc⟩ := ih _ _ _ _ hc_adv hl_adv hok
          exact ⟨sp_body, sp_close,
            GStar.cons _ _ _ (DQCharOk.plain c rest sc.col hjson hne_bs hne_dq) hb, hg, hc⟩

/-- Successful scanning reconstructs the admissible grammar on the original source. -/
lemma scanDoubleQuoted_prod_ok_oneLine (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '"')
    (hline : ∀ c ∈ sp.chars, c ≠ '\n' ∧ c ≠ '\r')
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', SCDoubleQuotedOk sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hc_adv := advance_non_newline_corr sc '"' rest hcorr
    (peek_some_has_more hpeek) (by decide) (by decide)
  have hl_adv : ∀ c ∈ rest, c ≠ '\n' ∧ c ≠ '\r' :=
    fun c hc => hline c (List.mem_cons_of_mem '"' hc)
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    obtain ⟨sp_body, sp_close, hb, hg, hc⟩ :=
      collectDoubleQuotedLoop_prod_ok_oneLine sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _ 0
        hc_adv hl_adv hloop
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close, SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk rest sc.col) hb hg,
          corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc)⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨sp_close, SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk rest sc.col) hb hg,
        corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc)⟩

/-- Full-input leaf scanning iff the same grammar consumes all raw remaining source.
EOF supplies the acceptance direction's trailing-content condition. -/
lemma scanDoubleQuoted_full_iff_oneLine (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '"')
    (hline : ∀ c ∈ sp.chars, c ≠ '\n' ∧ c ≠ '\r') :
    (∃ s', scanDoubleQuoted sc = .ok s' ∧ ¬ s'.offset < s'.inputEnd) ↔
      ∃ col, SCDoubleQuotedOk sp ⟨[], col⟩ := by
  constructor
  · rintro ⟨s', hok, heof⟩
    obtain ⟨sp', hd, hc⟩ := scanDoubleQuoted_prod_ok_oneLine sc sp hcorr hpeek hline hok
    have hempty := eof_corr s' sp' hc heof
    obtain ⟨chars, col⟩ := sp'
    simp only at hempty
    subst chars
    exact ⟨col, hd⟩
  · rintro ⟨col, hd⟩
    obtain ⟨s', content, hok, hc, _⟩ := scanDoubleQuoted_accepts sc hcorr hd
      (Or.inr (by trivial : TrailingOk ([] : List Char)))
    refine ⟨s', hok, ?_⟩
    intro hmore
    obtain ⟨c, rest, heq, _⟩ := peek_corr s' ⟨[], col⟩ hc hmore
    simp at heq

/-- info: 'L4YAML.Research.AcceptedSource.parseHexEscape_prod_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parseHexEscape_prod_valid

/-- info: 'L4YAML.Research.AcceptedSource.processEscape_prod_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms processEscape_prod_ok

/-- info: 'L4YAML.Research.AcceptedSource.dqCharOk_source_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms dqCharOk_source_mem

/-- info: 'L4YAML.Research.AcceptedSource.collectDoubleQuotedLoop_prod_ok_oneLine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms collectDoubleQuotedLoop_prod_ok_oneLine

/-- info: 'L4YAML.Research.AcceptedSource.scanDoubleQuoted_prod_ok_oneLine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanDoubleQuoted_prod_ok_oneLine

/-- info: 'L4YAML.Research.AcceptedSource.scanDoubleQuoted_full_iff_oneLine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanDoubleQuoted_full_iff_oneLine

/-! ## Original-string consumer and independent constructor witnesses

The consumer supplies only raw opening-quote and one-line facts about `input`.
Initial correspondence and the scanner peek are derived, not assumed. The
examples below construct the SAME grammar before invoking the generic result;
none evaluates the scanner. These remain leaf results without decoded-value,
public-parser, or flow-collection claims.
-/

/-- Actual original-string scanning reaches exact EOF iff the same independent
grammar consumes that original string completely. -/
lemma scanDoubleQuoted_source_full_iff_oneLine (input : String)
    (hstart : ∃ rest, input.toList = '"' :: rest)
    (hline : ∀ c ∈ input.toList, c ≠ '\n' ∧ c ≠ '\r') :
    (∃ s', scanDoubleQuoted (ScannerState.mk' input) = .ok s' ∧
      s'.offset = s'.inputEnd) ↔
      ∃ col, SCDoubleQuotedOk ⟨input.toList, 0⟩ ⟨[], col⟩ := by
  have hcorr := initial_corr input input.toList (chars_from_zero_toList input)
  obtain ⟨rest, hstart⟩ := hstart
  have hcorr_cons : ScannerSurfCorr (ScannerState.mk' input) ⟨'"' :: rest, 0⟩ := by
    rw [← hstart]
    exact hcorr
  have hpeek := (peek_of_corr hcorr_cons).1
  constructor
  · rintro ⟨s', hok, heof⟩
    exact (scanDoubleQuoted_full_iff_oneLine (ScannerState.mk' input)
      ⟨input.toList, 0⟩ hcorr hpeek hline).1 ⟨s', hok, by omega⟩
  · rintro ⟨col, hd⟩
    obtain ⟨s', content, hok, hc, _⟩ :=
      scanDoubleQuoted_accepts (ScannerState.mk' input) hcorr hd
        (Or.inr (by trivial : TrailingOk ([] : List Char)))
    refine ⟨s', hok, ?_⟩
    obtain ⟨pre, hin, hpre⟩ := hc.input_prefix
    simp only [List.append_nil] at hin
    rw [hc.end_eq, utf8ByteSize_eq_listByteSize, hin]
    exact hpre.symm

/-- Empty quoted input: two quote constructors and an empty body. -/
lemma quoted_empty_grammar :
    SCDoubleQuotedOk ⟨("\"\"" : String).toList, 0⟩ ⟨[], 2⟩ := by
  change SCDoubleQuotedOk ⟨['"', '"'], 0⟩ ⟨[], 2⟩
  exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk ['"'] 0)
    (GStar.nil ⟨['"'], 1⟩) (GLit.mk [] 1)

/-- The multibyte source has three surface columns (and four UTF-8 bytes). -/
lemma quoted_multibyte_grammar :
    SCDoubleQuotedOk ⟨("\"é\"" : String).toList, 0⟩ ⟨[], 3⟩ := by
  change SCDoubleQuotedOk ⟨['"', 'é', '"'], 0⟩ ⟨[], 3⟩
  exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk ['é', '"'] 0)
    (GStar.cons _ _ _ (DQCharOk.plain 'é' ['"'] 1 (by decide) (by decide) (by decide))
      (GStar.nil ⟨['"'], 2⟩)) (GLit.mk [] 2)

/-- Named escaped newline: four raw characters, with no physical line break. -/
lemma quoted_escaped_newline_grammar :
    SCDoubleQuotedOk ⟨("\"\\n\"" : String).toList, 0⟩ ⟨[], 4⟩ := by
  change SCDoubleQuotedOk ⟨['"', '\\', 'n', '"'], 0⟩ ⟨[], 4⟩
  exact SCDoubleQuotedOk.mk _ _ _ _ (GLit.mk ['\\', 'n', '"'] 0)
    (GStar.cons _ _ _ (DQCharOk.escape 'n' ['"'] 1 (by decide))
      (GStar.nil ⟨['"'], 3⟩)) (GLit.mk [] 3)

/-- Empty-source leaf success/EOF follows from its constructor witness. -/
lemma quoted_empty_scan_full :
    ∃ s', scanDoubleQuoted (ScannerState.mk' "\"\"") = .ok s' ∧
      s'.offset = s'.inputEnd := by
  refine (scanDoubleQuoted_source_full_iff_oneLine "\"\"" ⟨['"'], rfl⟩ ?_).2
    ⟨2, quoted_empty_grammar⟩
  intro c hc
  change c ∈ ['"', '"'] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

/-- Multibyte-source leaf success/EOF follows from its constructor witness. -/
lemma quoted_multibyte_scan_full :
    ∃ s', scanDoubleQuoted (ScannerState.mk' "\"é\"") = .ok s' ∧
      s'.offset = s'.inputEnd := by
  refine (scanDoubleQuoted_source_full_iff_oneLine "\"é\"" ⟨['é', '"'], rfl⟩ ?_).2
    ⟨3, quoted_multibyte_grammar⟩
  intro c hc
  change c ∈ ['"', 'é', '"'] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> decide

/-- Escaped-newline leaf success/EOF follows from its constructor witness. -/
lemma quoted_escaped_newline_scan_full :
    ∃ s', scanDoubleQuoted (ScannerState.mk' "\"\\n\"") = .ok s' ∧
      s'.offset = s'.inputEnd := by
  refine (scanDoubleQuoted_source_full_iff_oneLine "\"\\n\"" ⟨['\\', 'n', '"'], rfl⟩ ?_).2
    ⟨4, quoted_escaped_newline_grammar⟩
  intro c hc
  change c ∈ ['"', '\\', 'n', '"'] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

/-- info: 'L4YAML.Research.AcceptedSource.scanDoubleQuoted_source_full_iff_oneLine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanDoubleQuoted_source_full_iff_oneLine

/-- info: 'L4YAML.Research.AcceptedSource.quoted_empty_grammar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quoted_empty_grammar

/-- info: 'L4YAML.Research.AcceptedSource.quoted_multibyte_grammar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quoted_multibyte_grammar

/-- info: 'L4YAML.Research.AcceptedSource.quoted_escaped_newline_grammar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms quoted_escaped_newline_grammar

/-- info: 'L4YAML.Research.AcceptedSource.quoted_empty_scan_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quoted_empty_scan_full

/-- info: 'L4YAML.Research.AcceptedSource.quoted_multibyte_scan_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quoted_multibyte_scan_full

/-- info: 'L4YAML.Research.AcceptedSource.quoted_escaped_newline_scan_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms quoted_escaped_newline_scan_full

end L4YAML.Research.AcceptedSource
