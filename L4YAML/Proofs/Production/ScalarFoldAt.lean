/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Production.ScalarProduction
import L4YAML.Proofs.Production.FlowIndexLift
import L4YAML.Proofs.Scanner.PreprocessIndentStable
import L4YAML.Proofs.Output.EmitterScannability.ScanSteps

/-! # Quoted-scalar readings at the pending's own index (DOCS item 53)

    `ScalarProduction` builds every quoted reading at index 0; the
    `FlowIndexLift` lifts (item 45) carry the single-line readings to any
    index and return the multi-line ones as `*Crossed` witnesses.  This file
    pays the multi-line readings themselves: the scanner's fold guards — the
    §6.1 tab gate, the document-marker check and the §8.1 under-indent check,
    which item 53's runtime edit extended to the escaped-break landing —
    guarantee every CONTENT landing clears `s-indent(n)` whenever
    `n ≤ currentIndent + 1`, so the same loop inductions that build the
    0-readings build the readings at `n`.

    What stays behind (each arm returns `∨ True`, cost as domain):
    * a blank interior line whose run has fewer than `n` spaces and then a
      TAB — the one shape `[70] l-empty(n)` has no arm for (the scanner
      accepts it; a future runtime check refuses it);
    * a blank line directly after an ESCAPED break — `[112]`'s `l-empty*`
      slot, which the loop attributes to the next fold instead;
    * the vacuous tab-gate-true branch (no accepted input reaches it). -/

set_option autoImplicit false

namespace L4YAML.Proofs.ScalarFoldAt

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Proofs.FlowIndexLift
open L4YAML.Proofs.PreprocessIndentStable

/-! ## §0 Local plumbing -/

/-- `[63]`'s column arithmetic (local copy — the shared one lives above this
    file in the import graph). -/
private lemma SIndent_col' {k : Nat} {sp sp' : SurfPos} (h : SIndent k sp sp') :
    sp'.col = sp.col + k := by
  induction h with
  | zero => rfl
  | succ n rest col s' _ ih => simpa [ih] using by omega

/-- `consumeNewline` never writes the indent stack. -/
private lemma consumeNewline_indents (s : ScannerState) :
    (consumeNewline s).indents = s.indents := by
  unfold consumeNewline
  split
  · exact advance_indents s
  · dsimp only []
    split
    · exact advance_indents s
    · exact advance_indents s
  · rfl

/-- Neither does the blank-line loop. -/
private lemma foldLoop_indents (s : ScannerState) (cnt fuel : Nat) :
    (foldQuotedNewlinesLoop s cnt fuel).1.indents = s.indents := by
  induction fuel generalizing s cnt with
  | zero => rfl
  | succ f ih =>
    unfold foldQuotedNewlinesLoop; dsimp only []
    split
    · split
      · rw [ih, consumeNewline_indents, skipWhitespace_preserves_indents]
      · rfl
    · rfl

/-! ## §1 `l-empty(n)` from a skipped blank line -/

/-- Every `[30] b-break` lands at column 0. -/
lemma SBBreak_col0 {sp sp' : SurfPos} (h : SBBreak sp sp') : sp'.col = 0 := by
  cases h <;> rfl

/-- A skipped blank line reads at `n`: its run splits as
    `s-flow-line-prefix(n)` when it clears the indent, as `s-indent(<n)`
    when it is a short pure-space run, and only the short-run-then-TAB
    shape has no `[70]` arm. -/
lemma slEmpty_flowIn_at (n : Nat) {sp sp₁ sp' : SurfPos}
    (hws : GStar SSWhite sp sp₁) (hbrk : SBBreak sp₁ sp') :
    SLEmpty n .flowIn sp sp' ∨ True := by
  rcases gstar_white_take_sIndent n hws with ⟨sx, hind, hrest⟩ | ⟨j, sx, hj, hind, hrest, hend⟩
  · exact Or.inl (SLEmpty.flow n sp sp₁ sp' .flowIn (Or.inr rfl)
      (GOpt.some sp sp₁ (SFlowLinePrefix.mk n sp sx sp₁ hind
        (gstar_sswhite_to_gopt_sep hrest))) hbrk)
  · rcases hend with hend | _
    · subst hend
      -- the whole run is `j < n` spaces: `s-indent(<n)`… once the residual
      -- star is nil.  It is: `sx = sp₁` says the run ended at the split.
      cases hrest with
      | nil => exact Or.inl (SLEmpty.flowLt n sp sx sp' .flowIn (Or.inr rfl)
          ⟨j, hj, hind⟩ hbrk)
      | cons _ _ _ hw hr =>
        -- a residual white AT the run's end would step past sp₁ — but the
        -- break starts there, and a break head is not a white.  Refute from
        -- the characters.
        cases hw with
        | space rest col => cases hbrk <;> simp_all
        | tab rest col => cases hbrk <;> simp_all
    · exact Or.inr trivial

/-! ## §2 The blank-line loop at `n` -/

/-- `foldQuotedNewlinesLoop` at `n`: every skipped line is `SLEmpty n`, or
    some line is the tab residue.  The column fact rides along: a loop
    entered at a line start leaves at one. -/
lemma foldQuotedNewlinesLoop_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (cnt fuel : Nat) (hcorr : ScannerSurfCorr sc sp) :
    (∃ sp', GStar (SLEmpty n .flowIn) sp sp' ∧
       ScannerSurfCorr (foldQuotedNewlinesLoop sc cnt fuel).1 sp' ∧
       (sp.col = 0 → sp'.col = 0)) ∨ True := by
  induction fuel generalizing sc sp cnt with
  | zero =>
    simp only [foldQuotedNewlinesLoop]
    exact Or.inl ⟨sp, GStar.nil _, hcorr, fun h => h⟩
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop; dsimp only []
    obtain ⟨sp_ws, h_gstar, hcorr_ws⟩ := skipWhitespace_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
          consumeNewline_sbreak_corr (skipWhitespace sc) sp_ws c hcorr_ws hpeek hlb
        rcases slEmpty_flowIn_at n h_gstar h_sbreak with h_lempty | _
        · rcases ih (consumeNewline (skipWhitespace sc)) sp_cn (cnt + 1) hcorr_cn with
            ⟨sp_rest, h_gr, hc, hcol⟩ | _
          · exact Or.inl ⟨sp_rest, GStar.cons sp sp_cn sp_rest h_lempty h_gr, hc,
              fun _ => hcol (SBBreak_col0 h_sbreak)⟩
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inl ⟨sp, GStar.nil _, hcorr, fun h => h⟩
    · exact Or.inl ⟨sp, GStar.nil _, hcorr, fun h => h⟩

/-! ## §3 The fold at `n` -/

/-- **The fold reads at `n`** whenever `n ≤ currentIndent + 1` and the
    caller's §8.1 guard passed (the landing's final column clears the
    indent): the guards make the landing's space run at least `n` long, so
    `s-flow-line-prefix(n)` splits off the run item 45 style.  The `∨ True`
    side carries the tab-blank interior line and the vacuous gate-true
    branch. -/
lemma foldQuotedNewlines_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (c : Char)
    {content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true)
    (hfold : foldQuotedNewlines sc = .ok (content, s'))
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    (∃ sp₁ sp₂ sp'',
      SBBreak sp sp₁ ∧
      GStar (SLEmpty n .flowIn) sp₁ sp₂ ∧
      SFlowLinePrefix n sp₂ sp'' ∧
      ScannerSurfCorr s' sp'') ∨ True := by
  obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
    consumeNewline_sbreak_corr sc sp c hcorr hpeek hlb
  rcases foldQuotedNewlinesLoop_prod_at n (consumeNewline sc) sp_cn 0 _ hcorr_cn with
    ⟨sp_loop, h_gstar_empty, hcorr_loop, hcol_loop⟩ | _
  · obtain ⟨n_sk2, sp_sk2, h_indent2, hcorr_sk2⟩ :=
      skipSpaces_corr (loopResult sc).1 sp_loop hcorr_loop
    unfold foldQuotedNewlines at hfold; dsimp only [] at hfold
    split at hfold
    · -- the gate-true branch: no accepted input reaches it (the final
      -- column would be at or below the indent), so the domain costs
      -- nothing.
      exact Or.inr trivial
    · -- gate-false: the landing's space run clears the indent, so it is at
      -- least `n` long and the prefix splits off it.
      rename_i h_gate
      obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
        skipWhitespace_corr _ sp_sk2 hcorr_sk2
      -- the run length: the loop lands at column 0, the spaces land at
      -- `n_sk2`, and the gate says that clears the indent.
      have hcol0 : sp_loop.col = 0 :=
        hcol_loop (SBBreak_col0 h_sbreak)
      have hcol_sk2 : sp_sk2.col = n_sk2 := by
        have := SIndent_col' h_indent2; omega
      have h_gate' : ¬ ((skipSpaces (loopResult sc).1).col : Int)
          ≤ (skipSpaces (loopResult sc).1).currentIndent := by
        simpa using h_gate
      have h_ci_sk : (skipSpaces (loopResult sc).1).currentIndent
          = sc.currentIndent := by
        refine currentIndent_of_indents_eq ?_
        rw [skipSpaces_preserves_indents]
        show (loopResult sc).1.indents = sc.indents
        rw [show (loopResult sc).1.indents = (consumeNewline sc).indents from
              foldLoop_indents (consumeNewline sc) 0 _,
            consumeNewline_indents]
      have h_col_state : ((skipSpaces (loopResult sc).1).col : Int) = (n_sk2 : Int) := by
        rw [hcorr_sk2.col_eq] at hcol_sk2
        exact_mod_cast hcol_sk2
      have hn_le : n ≤ n_sk2 := by
        rw [h_ci_sk] at h_gate'
        omega
      -- split the space run at `n`: indent + residual spaces, the residual
      -- and the trailing whites feeding the separation slot.
      have h_eq : n_sk2 = n + (n_sk2 - n) := by omega
      rw [h_eq] at h_indent2
      obtain ⟨sp_mid, h_ind_n, h_ind_rest⟩ := sindent_split h_indent2
      have h_seps : GStar SSWhite sp_mid sp_ws :=
        gstar_sswhite_append (sindent_to_gstar_sswhite h_ind_rest) h_gstar_ws
      have h_flp : SFlowLinePrefix n sp_loop sp_ws :=
        SFlowLinePrefix.mk n sp_loop sp_mid sp_ws h_ind_n
          (gstar_sswhite_to_gopt_sep h_seps)
      split at hfold
      · have hinj := Except.ok.inj hfold
        obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
        exact Or.inl ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty, h_flp, hcorr_ws⟩
      · have hinj := Except.ok.inj hfold
        obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
        exact Or.inl ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty, h_flp, hcorr_ws⟩
  · exact Or.inr trivial

/-! ## §4 The double-quoted body at `n` -/

/-- The prepend at `n` (the 0-version's proof, index-generic). -/
private lemma SNbDoubleMultiLine_prepend_at (n : Nat) (s s₁ s_end : SurfPos)
    (hchar : SNbDoubleChar s s₁)
    (hrest : SNbDoubleMultiLine n s₁ s_end) :
    SNbDoubleMultiLine n s s_end := by
  cases hrest with
  | single _ _ hline =>
    exact SNbDoubleMultiLine.single n s s_end (GStar.cons s s₁ s_end hchar hline)
  | multi _ s₁' s₂ s₃ _ hline hbreak hcont =>
    exact SNbDoubleMultiLine.multi n s s₁' s₂ s₃ s_end
      (GStar.cons s s₁ s₁' hchar hline) hbreak hcont

/-- **The double-quoted body reads at `n`** whenever `n ≤ currentIndent + 1`:
    the loop's own guards clear every content landing (the fold's since item
    50's neighbourhood, the escaped break's since item 53's runtime edit).
    The `∨ True` side carries §3's residues. -/
lemma collectDoubleQuotedLoop_prod_at (n : Nat) (sc0 : ScannerState) (sp0 : SurfPos)
    (content0 : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr0 : ScannerSurfCorr sc0 sp0)
    (hok0 : collectDoubleQuotedLoop sc0 content0 fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s'))
    (hci0 : sc0.currentIndent = currentIndent)
    (hn : (n : Int) ≤ max 0 (currentIndent + 1)) :
    (∃ sp_body sp_close,
      SNbDoubleMultiLine n sp0 sp_body ∧
      GLit '"' sp_body sp_close ∧
      ScannerSurfCorr s' sp_close) ∨ True := by
  suffices H : ∀ (p : Nat) (sc : ScannerState) (sp : SurfPos) (content : String),
      ScannerSurfCorr sc sp →
      collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd p
        = .ok (result_content, s') →
      sc.currentIndent = currentIndent →
      ((∃ sp_body sp_close,
        SNbDoubleMultiLine n sp sp_body ∧
        GLit '"' sp_body sp_close ∧
        ScannerSurfCorr s' sp_close) ∨ True) by
    exact H 0 sc0 sp0 content0 hcorr0 hok0 hci0
  clear hok0 hcorr0 hci0
  intro p sc sp content hcorr hok hci
  induction fuel generalizing sc sp content p with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- closing quote: the one-line reading is index-free.
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      exact Or.inl ⟨⟨'"' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
             SNbDoubleMultiLine.single n _ _ (GStar.nil _),
             GLit.mk rest sc.col,
             advance_non_newline_corr sc '"' rest hcorr
               (peek_some_has_more hpeek) (by decide) (by decide)⟩
    · -- backslash: escape sequence
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv :=
        advance_non_newline_corr sc '\\' rest hcorr
          (peek_some_has_more hpeek) (by decide) (by decide)
      dsimp only [] at hok
      split at hok
      · rename_i c2 hpeek2
        split at hok
        · -- escaped break: item 53's landing structure.  A CONTENT landing
          -- passed the under-indent check, so its space run clears `n` and
          -- becomes the escape's own `s-flow-line-prefix(n)`; a BLANK
          -- landing keeps the deferral (`[112]`'s `l-empty*` slot, which the
          -- loop attributes to the next fold).
          rename_i hlb2
          obtain ⟨sp_cn, h_break_nl, hcorr_cn⟩ :=
            consumeNewline_sbreak_corr sc.advance ⟨rest, sc.col + 1⟩ c2 hcorr_adv hpeek2 hlb2
          obtain ⟨n_sp, sp_sp, h_ind_sp, hcorr_sp⟩ :=
            skipSpaces_corr (consumeNewline sc.advance) sp_cn hcorr_cn
          obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
            skipWhitespace_corr (skipSpaces (consumeNewline sc.advance)) sp_sp hcorr_sp
          have hci' : (skipWhitespace (skipSpaces (consumeNewline sc.advance))).currentIndent
              = currentIndent := by
            refine (currentIndent_of_indents_eq ?_).trans hci
            rw [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
                consumeNewline_indents, advance_indents]
          simp only [bind, Except.bind] at hok
          repeat' split at hok
          all_goals first
            | contradiction
            | -- the CONTENT landing: the last check's negation is in scope.
              (rename_i hgt
               rcases ih _ _ sp_ws content hcorr_ws hok hci' with
                 ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ | _
               · refine Or.inl ⟨sp_body, sp_close, ?_, h_glit, h_corr⟩
                 have hcol_cn : sp_cn.col = 0 := SBBreak_col0 h_break_nl
                 have hcol_sp : sp_sp.col = n_sp := by
                   have := SIndent_col' h_ind_sp; omega
                 have hcol_state : (skipSpaces (consumeNewline sc.advance)).col = n_sp := by
                   rw [← hcorr_sp.col_eq]; exact hcol_sp
                 have hn_le : n ≤ n_sp := by
                   rw [hcol_state] at hgt; omega
                 have h_ind_sp' : SIndent (n + (n_sp - n)) sp_cn sp_sp := by
                   rw [show n + (n_sp - n) = n_sp from by omega]; exact h_ind_sp
                 obtain ⟨sp_mid, h_ind_n, h_ind_rest⟩ := sindent_split h_ind_sp'
                 have h_flp : SFlowLinePrefix n sp_cn sp_ws :=
                   SFlowLinePrefix.mk n sp_cn sp_mid sp_ws h_ind_n
                     (gstar_sswhite_to_gopt_sep
                       (gstar_sswhite_append (sindent_to_gstar_sswhite h_ind_rest) h_gstar_ws))
                 exact SNbDoubleMultiLine.multi n
                   ⟨'\\' :: rest, sc.col⟩ ⟨'\\' :: rest, sc.col⟩ sp_ws ⟨[], 0⟩ sp_body
                   (GStar.nil _)
                   (SSDoubleBreak.escaped n _ _
                     (SSDoubleEscaped.mk n
                       ⟨'\\' :: rest, sc.col⟩ ⟨'\\' :: rest, sc.col⟩
                       ⟨rest, sc.col + 1⟩ sp_cn sp_cn sp_ws
                       (GStar.nil _) (GLit.mk rest sc.col) h_break_nl
                       (GStar.nil sp_cn) h_flp))
                   h_body
               · exact Or.inr trivial)
            | -- the BLANK landing: keep the deferral.
              exact Or.inr trivial
        · -- ordinary escape: index-free prepend.
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i esc_result hproc
            obtain ⟨sp_esc, h_dq_char, hcorr_esc⟩ :=
              processEscape_prod sc.advance rest sc.col hcorr_adv hproc
            have hci' : esc_result.2.currentIndent = currentIndent := by
              refine (currentIndent_of_indents_eq ?_).trans hci
              rw [L4YAML.Proofs.EmitterScannability.processEscape_preserves_indents
                    sc.advance esc_result hproc,
                  advance_indents]
            rcases ih _ _ sp_esc _ hcorr_esc hok hci' with
              ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ | _
            · exact Or.inl ⟨sp_body, sp_close,
                SNbDoubleMultiLine_prepend_at n _ _ _ h_dq_char h_body, h_glit, h_corr⟩
            · exact Or.inr trivial
      · exact absurd hok (by simp)
    · -- regular character or fold
      rename_i _opt c hne_dq hne_bs hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      split at hok
      · -- fold: the reading at `n` (§3), then the loop's own guards.
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_result hfold
          have hn_sc : (n : Int) ≤ max 0 (sc.currentIndent + 1) := by rw [hci]; exact hn
          rcases foldQuotedNewlines_prod_at n sc ⟨c :: rest, sc.col⟩ c hcorr hpeek hlb
              hfold hn_sc with ⟨sp_cn, sp_loop, sp_fold, h_sbreak, h_gstar_empty, h_flp,
                hcorr_fold⟩ | _
          · have hci' : fold_result.2.currentIndent = currentIndent := by
              refine (currentIndent_of_indents_eq ?_).trans hci
              exact L4YAML.Proofs.EmitterScannability.foldQuotedNewlines_preserves_indents
                sc fold_result hfold
            split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · split at hok <;>
                  first
                    | (rcases ih _ _ sp_fold _ hcorr_fold hok hci' with
                         ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ | _
                       · exact Or.inl ⟨sp_body, sp_close,
                           SNbDoubleMultiLine.multi n
                             ⟨c :: rest, sc.col⟩ ⟨c :: rest, sc.col⟩
                             sp_fold ⟨[], 0⟩ _
                             (GStar.nil _)
                             (SSDoubleBreak.flowFold n _ sp_cn sp_loop _
                               h_sbreak h_gstar_empty h_flp)
                             h_body,
                           h_glit, h_corr⟩
                       · exact Or.inr trivial)
                    | simp at hok
          · exact Or.inr trivial
      · -- regular character: index-free prepend.
        split at hok
        · simp at hok
        · rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
          have hci' : sc.advance.currentIndent = currentIndent := by
            refine (currentIndent_of_indents_eq ?_).trans hci
            exact advance_indents sc
          rcases ih _ sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv hok hci' with
            ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ | _
          · exact Or.inl ⟨sp_body, sp_close,
              SNbDoubleMultiLine_prepend_at n _ _ _
                (SNbDoubleChar.plain c rest sc.col
                  (not_lineBreak_bool_to_prop hne_lb) hne_bs hne_dq) h_body,
              h_glit, h_corr⟩
          · exact Or.inr trivial

/-! ## §5 The single-quoted body at `n` -/

private lemma SNbSingleMultiLine_prepend_at (n : Nat) (s s₁ s_end : SurfPos)
    (hchar : SNbSingleChar s s₁)
    (hrest : SNbSingleMultiLine n s₁ s_end) :
    SNbSingleMultiLine n s s_end := by
  cases hrest with
  | single _ _ hline =>
    exact SNbSingleMultiLine.single n s s_end (GStar.cons s s₁ s_end hchar hline)
  | multi _ s₁' s₂ s₃ s₄ _ hline hbreak hgstar hflp hcont =>
    exact SNbSingleMultiLine.multi n s s₁' s₂ s₃ s₄ s_end
      (GStar.cons s s₁ s₁' hchar hline) hbreak hgstar hflp hcont

/-- The single-quoted twin of `collectDoubleQuotedLoop_prod_at` — no escaped
    break, so the fold is the only landing. -/
lemma collectSingleQuotedLoop_prod_at (n : Nat) (sc0 : ScannerState) (sp0 : SurfPos)
    (content0 : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr0 : ScannerSurfCorr sc0 sp0)
    (hok0 : collectSingleQuotedLoop sc0 content0 fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s'))
    (hci0 : sc0.currentIndent = currentIndent)
    (hn : (n : Int) ≤ max 0 (currentIndent + 1)) :
    (∃ sp_body sp_close,
      SNbSingleMultiLine n sp0 sp_body ∧
      GLit '\'' sp_body sp_close ∧
      ScannerSurfCorr s' sp_close) ∨ True := by
  induction fuel generalizing sc0 sp0 content0 with
  | zero => simp [collectSingleQuotedLoop] at hok0
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok0
    split at hok0
    · exact absurd hok0 (by simp)
    · rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr0 hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      dsimp only [] at hok0
      split at hok0
      · -- escaped quote ''
        rename_i hpeek2
        have hcorr_adv :=
          advance_non_newline_corr sc0 '\'' rest hcorr0 hmore (by decide) (by decide)
        obtain ⟨rest2, hsp_adv⟩ := peek_some_sp hcorr_adv hpeek2
        injection hsp_adv with h_rest2 h_col2
        subst h_rest2
        rw [h_col2] at hcorr_adv
        have hmore2 := peek_some_has_more hpeek2
        have hcorr_adv2 :=
          advance_non_newline_corr sc0.advance '\'' rest2 hcorr_adv hmore2 (by decide) (by decide)
        rw [show sc0.advance.col + 1 = sc0.col + 2 from by omega] at hcorr_adv2
        have hci' : sc0.advance.advance.currentIndent = currentIndent := by
          refine (currentIndent_of_indents_eq ?_).trans hci0
          rw [advance_indents, advance_indents]
        rcases ih sc0.advance.advance ⟨rest2, sc0.col + 2⟩ _ hcorr_adv2 hok0 hci' with
          ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ | _
        · exact Or.inl ⟨sp_body, sp_close,
            SNbSingleMultiLine_prepend_at n _ _ _
              (SNbSingleChar.escapedQuote rest2 sc0.col) h_body, h_glit, h_corr⟩
        · exact Or.inr trivial
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok0
        obtain ⟨-, rfl⟩ := hok0
        exact Or.inl ⟨⟨'\'' :: rest, sc0.col⟩, ⟨rest, sc0.col + 1⟩,
               SNbSingleMultiLine.single n _ _ (GStar.nil _),
               GLit.mk rest sc0.col,
               advance_non_newline_corr sc0 '\'' rest hcorr0 hmore (by decide) (by decide)⟩
    · rename_i c hne_sq hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr0 hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      split at hok0
      · -- fold at `n`
        rename_i hlb
        simp only [bind, Except.bind] at hok0
        split at hok0
        · exact absurd hok0 (by simp)
        · rename_i fold_result hfold
          have hn_sc : (n : Int) ≤ max 0 (sc0.currentIndent + 1) := by rw [hci0]; exact hn
          rcases foldQuotedNewlines_prod_at n sc0 ⟨c :: rest, sc0.col⟩ c hcorr0 hpeek hlb
              hfold hn_sc with ⟨sp_cn, sp_loop, sp_fold, h_sbreak, h_gstar_empty, h_flp,
                hcorr_fold⟩ | _
          · have hci' : fold_result.2.currentIndent = currentIndent := by
              refine (currentIndent_of_indents_eq ?_).trans hci0
              exact L4YAML.Proofs.EmitterScannability.foldQuotedNewlines_preserves_indents
                sc0 fold_result hfold
            split at hok0
            · simp at hok0
            · split at hok0
              · simp at hok0
              · rcases ih _ sp_fold _ hcorr_fold hok0 hci' with
                  ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ | _
                · exact Or.inl ⟨sp_body, sp_close,
                    SNbSingleMultiLine.multi n
                      ⟨c :: rest, sc0.col⟩ ⟨c :: rest, sc0.col⟩
                      sp_cn sp_loop sp_fold _
                      (GStar.nil _)
                      h_sbreak h_gstar_empty h_flp
                      h_body,
                    h_glit, h_corr⟩
                · exact Or.inr trivial
          · exact Or.inr trivial
      · split at hok0
        · simp at hok0
        · rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc0 c rest hcorr0 hmore h_not_nl h_not_cr
          have hci' : sc0.advance.currentIndent = currentIndent := by
            refine (currentIndent_of_indents_eq ?_).trans hci0
            exact advance_indents sc0
          rcases ih sc0.advance ⟨rest, sc0.col + 1⟩ _ hcorr_adv hok0 hci' with
            ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ | _
          · exact Or.inl ⟨sp_body, sp_close,
              SNbSingleMultiLine_prepend_at n _ _ _
                (SNbSingleChar.plain c rest sc0.col
                  (not_lineBreak_bool_to_prop hne_lb) hne_sq) h_body,
              h_glit, h_corr⟩
          · exact Or.inr trivial

/-! ## §6 The scan-level wrappers -/

/-- **`scanDoubleQuoted` reads at `n`** whenever `n ≤ currentIndent + 1`, in
    the block-node contexts (`SNbDoubleText` at `.blockIn`/`.blockOut`/
    `.flowIn`/`.flowOut` is the multi-line body). -/
lemma scanDoubleQuoted_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (hok : scanDoubleQuoted sc = .ok s')
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    (∃ sp', SCDoubleQuoted n .blockIn sp sp' ∧ ScannerSurfCorr s' sp') ∨ True := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek_dq
  subst hsp_eq
  have hmore := peek_some_has_more hpeek_dq
  have hcorr_adv :=
    advance_non_newline_corr sc '"' rest hcorr hmore (by decide) (by decide)
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    have hci_adv : sc.advance.currentIndent = sc.currentIndent :=
      currentIndent_of_indents_eq (advance_indents sc)
    rcases collectDoubleQuotedLoop_prod_at n sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _
        hcorr_adv hloop hci_adv hn with
      ⟨sp_body, sp_close, h_body, h_glit_close, hcorr_close⟩ | _
    · split at hok
      · split at hok
        · simp at hok
        · have h := Except.ok.inj hok; subst h
          exact Or.inl ⟨_,
                 SCDoubleQuoted.mk n .blockIn _ _ _ _
                   (GLit.mk rest sc.col) h_body h_glit_close,
                 corr_of_simpleKeyAllowed_needIndentCheck_update false false
                   (corr_of_emitAt _ _ hcorr_close)⟩
      · have h := Except.ok.inj hok; subst h
        exact Or.inl ⟨_,
               SCDoubleQuoted.mk n .blockIn _ _ _ _
                 (GLit.mk rest sc.col) h_body h_glit_close,
               corr_of_simpleKeyAllowed_needIndentCheck_update false false
                 (corr_of_emitAt _ _ hcorr_close)⟩
    · exact Or.inr trivial

/-- The single-quoted wrapper (see `scanDoubleQuoted_prod_at`). -/
lemma scanSingleQuoted_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (hok : scanSingleQuoted sc = .ok s')
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    (∃ sp', SCSingleQuoted n .blockIn sp sp' ∧ ScannerSurfCorr s' sp') ∨ True := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek_sq
  subst hsp_eq
  have hmore := peek_some_has_more hpeek_sq
  have hcorr_adv :=
    advance_non_newline_corr sc '\'' rest hcorr hmore (by decide) (by decide)
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    have hci_adv : sc.advance.currentIndent = sc.currentIndent :=
      currentIndent_of_indents_eq (advance_indents sc)
    rcases collectSingleQuotedLoop_prod_at n sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _
        hcorr_adv hloop hci_adv hn with
      ⟨sp_body, sp_close, h_body, h_glit_close, hcorr_close⟩ | _
    · split at hok
      · split at hok
        · simp at hok
        · have h := Except.ok.inj hok; subst h
          exact Or.inl ⟨_,
                 SCSingleQuoted.mk n .blockIn _ _ _ _
                   (GLit.mk rest sc.col) h_body h_glit_close,
                 corr_of_simpleKeyAllowed_needIndentCheck_update false false
                   (corr_of_emitAt _ _ hcorr_close)⟩
      · have h := Except.ok.inj hok; subst h
        exact Or.inl ⟨_,
               SCSingleQuoted.mk n .blockIn _ _ _ _
                 (GLit.mk rest sc.col) h_body h_glit_close,
               corr_of_simpleKeyAllowed_needIndentCheck_update false false
                 (corr_of_emitAt _ _ hcorr_close)⟩
    · exact Or.inr trivial

/-! ## §7 Context conversion (the quoted body is context-free off the keys) -/

/-- `nb-double-text` is the same multi-line body at all four non-key
    contexts, so the reading converts freely among them. -/
lemma SCDoubleQuoted_multiCtx {n : Nat} {s s' : SurfPos} (c' : L4YAML.YamlContext)
    (hc' : c' = .flowOut ∨ c' = .flowIn ∨ c' = .blockOut ∨ c' = .blockIn)
    (h : SCDoubleQuoted n .blockIn s s') : SCDoubleQuoted n c' s s' := by
  cases h with
  | mk _ _ _ hq1 hbody hq2 =>
    rcases hc' with rfl | rfl | rfl | rfl <;>
      exact SCDoubleQuoted.mk n _ _ _ _ _ hq1 hbody hq2

/-- The single-quoted twin. -/
lemma SCSingleQuoted_multiCtx {n : Nat} {s s' : SurfPos} (c' : L4YAML.YamlContext)
    (hc' : c' = .flowOut ∨ c' = .flowIn ∨ c' = .blockOut ∨ c' = .blockIn)
    (h : SCSingleQuoted n .blockIn s s') : SCSingleQuoted n c' s s' := by
  cases h with
  | mk _ _ _ hq1 hbody hq2 =>
    rcases hc' with rfl | rfl | rfl | rfl <;>
      exact SCSingleQuoted.mk n _ _ _ _ _ hq1 hbody hq2

/-! ## §8 The plain scalar at `n` (block context) -/

/-- `skipBlankLinesLoop` at `n` — the plain walk's blank-line skipper. -/
lemma skipBlankLinesLoop_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (cnt fuel inputEnd : Nat) (hcorr : ScannerSurfCorr sc sp) :
    (∃ sp', GStar (SLEmpty n .flowIn) sp sp' ∧
       ScannerSurfCorr (skipBlankLinesLoop sc cnt fuel inputEnd).2 sp' ∧
       (sp.col = 0 → sp'.col = 0)) ∨ True := by
  induction fuel generalizing sc sp cnt with
  | zero =>
    simp only [skipBlankLinesLoop]
    exact Or.inl ⟨sp, GStar.nil _, hcorr, fun h => h⟩
  | succ fuel' ih =>
    unfold skipBlankLinesLoop; dsimp only []
    obtain ⟨sp_ws, h_gstar, hcorr_sk⟩ := skipWhitespace_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
          consumeNewline_sbreak_corr (skipWhitespace sc) sp_ws c hcorr_sk hpeek hlb
        rcases slEmpty_flowIn_at n h_gstar h_sbreak with h_lempty | _
        · rcases ih (consumeNewline (skipWhitespace sc)) sp_cn (cnt + 1) hcorr_cn with
            ⟨sp_rest, h_gr, hc, hcol⟩ | _
          · exact Or.inl ⟨sp_rest, GStar.cons sp sp_cn sp_rest h_lempty h_gr, hc,
              fun _ => hcol (SBBreak_col0 h_sbreak)⟩
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inl ⟨sp, GStar.nil _, hcorr, fun h => h⟩
    · exact Or.inl ⟨sp, GStar.nil _, hcorr, fun h => h⟩

/-- The BLOCK line-break handler at `n`: a `some` return passed the
    under-indent guard, so the landing's space run clears `n ≤ contentIndent`
    and reads as `s-flow-line-prefix(n)`. -/
lemma handleBlockLineBreak_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos) (c : Char)
    (content : String) (contentIndent inputEnd : Nat)
    {content' : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true)
    (hblk : collectPlainScalar_handleBlockLineBreak sc content contentIndent inputEnd
            = some (content', s'))
    (hn : n ≤ contentIndent) :
    (∃ sp₁ sp₂ sp',
      SBBreak sp sp₁ ∧
      GStar (SLEmpty n .flowIn) sp₁ sp₂ ∧
      SFlowLinePrefix n sp₂ sp' ∧
      ScannerSurfCorr s' sp') ∨ True := by
  obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
    consumeNewline_sbreak_corr sc sp c hcorr hpeek hlb
  rcases skipBlankLinesLoop_prod_at n (consumeNewline sc) sp_cn 0 _ inputEnd hcorr_cn with
    ⟨sp_loop, h_gstar_empty, hcorr_loop, hcol_loop⟩ | _
  · obtain ⟨n_sk, sp_sk, h_indent, hcorr_sk⟩ :=
      skipSpaces_corr
        (skipBlankLinesLoop (consumeNewline sc) 0
          (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2
        sp_loop hcorr_loop
    obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
      skipWhitespace_corr
        (skipSpaces (skipBlankLinesLoop (consumeNewline sc) 0
          (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2)
        sp_sk hcorr_sk
    unfold collectPlainScalar_handleBlockLineBreak at hblk
    dsimp only [] at hblk
    split at hblk
    · exact absurd hblk (by simp)
    · rename_i h_guard
      split at hblk
      · exact absurd hblk (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at hblk
        obtain ⟨-, rfl⟩ := hblk
        -- the guard's negation: the landing's space run clears the floor.
        have hcol0 : sp_loop.col = 0 := hcol_loop (SBBreak_col0 h_sbreak)
        have hcol_sk : sp_sk.col = n_sk := by
          have := SIndent_col' h_indent; omega
        have h_state_col : (skipSpaces (skipBlankLinesLoop (consumeNewline sc) 0
            (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2).col = n_sk := by
          rw [← hcorr_sk.col_eq]; exact hcol_sk
        have hn_le : n ≤ n_sk := by
          rw [h_state_col] at h_guard
          omega
        have h_ind' : SIndent (n + (n_sk - n)) sp_loop sp_sk := by
          rw [show n + (n_sk - n) = n_sk from by omega]; exact h_indent
        obtain ⟨sp_mid, h_ind_n, h_ind_rest⟩ := sindent_split h_ind'
        exact Or.inl ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty,
          SFlowLinePrefix.mk n sp_loop sp_mid sp_ws h_ind_n
            (gstar_sswhite_to_gopt_sep
              (gstar_sswhite_append (sindent_to_gstar_sswhite h_ind_rest) h_gstar_ws)),
          hcorr_ws⟩
  · exact Or.inr trivial

/-- The plain collect loop at `n` (BLOCK context; the flow break keeps the
    deferral — the flow share's own item consumes it). -/
lemma collectPlainScalarLoop_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (content spaces : String) (fuel : Nat)
    (contentIndent inputEnd : Nat)
    (sp_ent : SurfPos) (inFlow : Bool)
    (hcorr : ScannerSurfCorr sc sp)
    (h_ws : GStar SSWhite sp_ent sp)
    (h_hash_col : sc.peek? = some '#' → spaces.length = 0 → sc.col > 0)
    {result : PlainScalarResult}
    (hok : collectPlainScalarLoop sc content spaces fuel inFlow contentIndent inputEnd
           = .ok result)
    (hn : n ≤ contentIndent) :
    (∃ sp_entries sp_next sp_trail,
      GStar (SNbNsPlainInLineEntry (ctxOfInFlow inFlow)) sp_ent sp_entries ∧
      GStar (SSNsPlainNextLine n (ctxOfInFlow inFlow)) sp_entries sp_next ∧
      GStar SSWhite sp_next sp_trail ∧
      ScannerSurfCorr result.state sp_trail) ∨ True := by
  induction fuel generalizing sc sp content spaces sp_ent with
  | zero =>
    simp [collectPlainScalarLoop] at hok; subst hok
    exact Or.inl ⟨sp_ent, sp_ent, sp, GStar.nil _, GStar.nil _, h_ws, hcorr⟩
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at hok
    split at hok
    · have h := Except.ok.inj hok; subst h
      exact Or.inl ⟨sp_ent, sp_ent, sp, GStar.nil _, GStar.nil _, h_ws, hcorr⟩
    · rename_i c hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      have hmore := peek_some_has_more hpeek
      subst hsp_eq
      split at hok
      · rename_i r_term h_term
        have h := Except.ok.inj hok; subst h
        rw [terminates_state_eq c sc content spaces inFlow r_term h_term]
        exact Or.inl ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
          h_ws, hcorr⟩
      · rename_i h_term_none
        split at hok
        · -- line break
          split at hok
          · -- inFlow = true: the flow share's own item consumes this.
            exact Or.inr trivial
          · -- inFlow = false: block line break at `n`
            split at hok
            · have h := Except.ok.inj hok; subst h
              exact Or.inl ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                h_ws, hcorr⟩
            · rename_i content' s' hblk
              split at hok
              · have h := Except.ok.inj hok; subst h
                exact Or.inl ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                  h_ws, hcorr⟩
              · rename_i hblkpeek
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow
                  contentIndent inputEnd = cont_result at hok
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at hok
                  split at hok
                  · have h := Except.ok.inj hok; subst h
                    exact Or.inl ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _,
                      GStar.nil _, h_ws, hcorr⟩
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    have hlb : isLineBreakBool c = true := by assumption
                    rcases handleBlockLineBreak_prod_at n sc ⟨c :: rest, sc.col⟩ c content
                        contentIndent inputEnd hcorr hpeek hlb hblk hn with
                      ⟨sp₁, sp₂, sp_fold, h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩ | _
                    · rcases ih s' sp_fold content' "" sp_fold hcorr_fold (GStar.nil _)
                          (fun hpk _ => absurd hpk hblkpeek) h_loop with
                        ⟨sp_entries_ih, sp_next_ih, sp_trail_ih,
                         h_entries_ih, h_next_ih, h_ws_ih, hcorr_ih⟩ | _
                      · exact Or.inl ⟨sp_ent, sp_next_ih, sp_trail_ih,
                          GStar.nil _,
                          GStar.cons sp_ent sp_entries_ih sp_next_ih
                            (SSNsPlainNextLine.mk n (ctxOfInFlow inFlow)
                              sp_ent ⟨c :: rest, sc.col⟩ sp₁ sp₂ sp_fold sp_entries_ih
                              h_ws h_sbreak h_gstar_empty h_flp h_entries_ih)
                            h_next_ih,
                          h_ws_ih, hcorr_ih⟩
                      · exact Or.inr trivial
                    · exact Or.inr trivial
                | error e => simp at hok
        · split at hok
          · -- whitespace
            have hws_char : isWhiteSpaceBool c = true := by assumption
            have hnl := isWhiteSpace_not_newline c hws_char
            have hcr := isWhiteSpace_not_cr c hws_char
            have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
            have hw : SSWhite ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ := by
              simp [isWhiteSpaceBool, isSpaceBool, isTabBool, Bool.or_eq_true,
                beq_iff_eq] at hws_char
              rcases hws_char with rfl | rfl
              · exact SSWhite.space rest sc.col
              · exact SSWhite.tab rest sc.col
            exact ih sc.advance ⟨rest, sc.col + 1⟩ content (spaces.push c) sp_ent
              hcorr_adv (gstar_sswhite_append h_ws (GStar.cons _ _ _ hw (GStar.nil _)))
              (fun _ hlen => by simp [String.length_push] at hlen)
              hok
          · split at hok
            · have h := Except.ok.inj hok; subst h
              exact Or.inl ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                h_ws, hcorr⟩
            · -- content char: the 0-lemma's own construction, verbatim.
              have h_safe : isPlainSafeBool c inFlow = true := by
                cases hb : isPlainSafeBool c inFlow <;> simp_all
              have hnl := (isPlainSafe_not_newline h_safe).1
              have hcr := (isPlainSafe_not_newline h_safe).2
              have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
              have hchar : SNsPlainChar (ctxOfInFlow inFlow) ⟨c :: rest, sc.col⟩
                  ⟨rest, sc.col + 1⟩ := by
                by_cases hcolon : c = ':'
                · subst hcolon
                  obtain ⟨m, hpn, hnb, hfi, hprn, hbomn⟩ :=
                    colon_not_terminated_next sc content spaces inFlow h_term_none
                  unfold ScannerState.peekAt? at hpn
                  obtain ⟨pre, rest', hcs, hlen⟩ :=
                    peekAtLoop_some_chars hcorr.end_eq hpn (':' :: rest) hcorr.chars_from
                  have ⟨a, ha⟩ : ∃ a, pre = [a] := by
                    cases pre with
                    | nil => simp at hlen
                    | cons a as => cases as with
                      | nil => exact ⟨a, rfl⟩
                      | cons => simp at hlen
                  subst ha; simp at hcs
                  obtain ⟨ha', hrst⟩ := hcs; subst ha'; subst hrst
                  have h_ns_safe : isNsPlainSafe (ctxOfInFlow inFlow) m := by
                    cases inFlow with
                    | false => exact not_blank_to_nsChar hnb hprn hbomn
                    | true =>
                      exact ⟨not_blank_to_nsChar hnb hprn hbomn, fun hfp => by
                        have h1 := hfi rfl
                        have h2 := (isFlowIndicator_iff m).mpr hfp
                        simp [h1] at h2⟩
                  exact SNsPlainChar.colonSafe (ctxOfInFlow inFlow) '_' m rest' sc.col
                    h_ns_safe
                · by_cases hhash : c = '#'
                  · subst hhash
                    have h_sp_zero : spaces.length = 0 := by
                      suffices ¬(spaces.length > 0) by omega
                      intro h_pos
                      have h_dec : decide (spaces.length > 0) = true :=
                        decide_eq_true_eq.mpr h_pos
                      unfold collectPlainScalar_terminates? at h_term_none
                      simp [h_dec] at h_term_none
                    have h_col_pos : sc.col > 0 := h_hash_col hpeek h_sp_zero
                    exact SNsPlainChar.hashAfterNs (ctxOfInFlow inFlow) rest sc.col h_col_pos
                  · exact SNsPlainChar.safe (ctxOfInFlow inFlow) c rest sc.col
                      (isPlainSafe_to_nsPlainSafe h_safe) hcolon hhash
              rcases ih sc.advance ⟨rest, sc.col + 1⟩ _ "" ⟨rest, sc.col + 1⟩
                  hcorr_adv (GStar.nil _)
                  (fun _ _ => by
                    have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq
                    omega)
                  hok with
                ⟨sp_entries, sp_next, sp_trail, h_ent_rest, h_next_rest,
                 h_ws_rest, hcorr_rest⟩ | _
              · exact Or.inl ⟨sp_entries, sp_next, sp_trail,
                  GStar.cons sp_ent ⟨rest, sc.col + 1⟩ sp_entries
                    (SNbNsPlainInLineEntry.mk (ctxOfInFlow inFlow) sp_ent ⟨c :: rest, sc.col⟩
                      ⟨rest, sc.col + 1⟩ h_ws hchar)
                    h_ent_rest,
                  h_next_rest, h_ws_rest, hcorr_rest⟩
              · exact Or.inr trivial

/-- **`scanPlainScalar` reads at `n`** in BLOCK context whenever
    `n ≤ minContentIndentOf` — the loop's own under-indent guard clears every
    continuation landing.  The flow share keeps the deferral. -/
lemma scanPlainScalar_to_flowNode_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s')
    (hinflow : sc.inFlow = false)
    (hn : n ≤ minContentIndentOf sc) :
    (∃ sp_gram sp', SFlowNode n .flowOut sp sp_gram ∧
                    GStar SSWhite sp_gram sp' ∧
                    ScannerSurfCorr s' sp') ∨ True := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  have hrest_head : ∀ m, sc.peekAt? 1 = some m → ∃ rest', rest = m :: rest' := by
    intro m hm; unfold ScannerState.peekAt? at hm
    have hcorr' := hsp_eq ▸ hcorr
    obtain ⟨pre, rest', hcs, hlen⟩ :=
      peekAtLoop_some_chars hcorr'.end_eq hm (c :: rest) hcorr'.chars_from
    have ⟨a, ha⟩ : ∃ a, pre = [a] := by
      cases pre with
      | nil => simp at hlen
      | cons a as => cases as with
        | nil => exact ⟨a, rfl⟩
        | cons => simp at hlen
    subst ha; simp at hcs; obtain ⟨_, rfl⟩ := hcs; exact ⟨rest', rfl⟩
  rw [hsp_eq]; rw [hsp_eq] at hcorr
  have h_first : SNsPlainFirst (ctxOfInFlow sc.inFlow) ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
    canStartPlainScalar_to_SNsPlainFirst c rest sc.col (sc.peekAt? 1) sc.inFlow hstart hrest_head
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i result hloop
    simp only [Except.ok.injEq] at hok; subst hok
    have h_term_none := canStartPlain_first_not_terminates c sc sc.inFlow hstart h_not_doc
    have h_safe := canStartPlain_implies_safe hstart
    have h_nws := canStartPlainScalar_not_ws hstart
    have h_nlb := canStartPlain_not_linebreak hstart
    have h_has_more := peek_some_has_more hpeek
    obtain ⟨fuel', h_fuel_eq⟩ : ∃ m, (sc.inputEnd - sc.offset + 1) * 2 = m + 1 :=
      ⟨(sc.inputEnd - sc.offset + 1) * 2 - 1, by omega⟩
    rw [h_fuel_eq] at hloop
    have hloop' := collectPlainScalarLoop_content_first_step
      hpeek h_term_none h_nlb h_nws h_safe hloop
    have hcorr_adv := advance_non_newline_corr sc c rest hcorr h_has_more
      (isPlainSafe_not_newline h_safe).1 (isPlainSafe_not_newline h_safe).2
    have hci_eq : (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat)
        = minContentIndentOf sc := by
      rw [hinflow]; rfl
    rw [hci_eq] at hloop'
    rcases collectPlainScalarLoop_prod_at n sc.advance ⟨rest, sc.col + 1⟩ _ "" _ _ _
        ⟨rest, sc.col + 1⟩ sc.inFlow hcorr_adv (GStar.nil _)
        (fun _ _ => by
          have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq
          omega)
        hloop' hn with
      ⟨sp_entries, sp_next, sp_trail, h_entries, h_next_lines, h_trail, hcorr_result⟩ | _
    · exact Or.inl ⟨sp_next, sp_trail,
        SFlowNode.content n .flowOut _ _
          (SFlowContent.plain n .flowOut _ _
            (SNsPlainMultiLine_ctxOfInFlow_to_flowOut
              (SNsPlainMultiLine.mk n (ctxOfInFlow sc.inFlow) _ _ sp_next
                (SNsPlainOneLine.mk (ctxOfInFlow sc.inFlow) _ ⟨rest, sc.col + 1⟩ sp_entries
                  h_first h_entries)
                h_next_lines))),
        h_trail,
        corr_of_simpleKeyAllowed_needIndentCheck_update false false
          (corr_of_emitAt _ _ hcorr_result)⟩
    · exact Or.inr trivial

end L4YAML.Proofs.ScalarFoldAt
