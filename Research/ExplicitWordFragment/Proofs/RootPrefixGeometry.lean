module
public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Proofs.Foundation.SurfaceSpanSupply
public import L4YAML.Proofs.Scanner.ScanStrictCoupling
public section
set_option autoImplicit false
namespace L4YAML.Proofs.RootPrefixGeometry
open L4YAML L4YAML.Surface L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.StructureCoupling L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScanStrictCoupling L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.PreprocessProduction L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.TabIndentBridge L4YAML.Proofs.SurfaceSpan

/-- Unwind bookkeeping changes the stack and tokens, not the source position.
    Retain the *same* surface rather than weakening to an existential. -/
lemma unwindLoop_same_surface (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) (fuel : Nat) :
    ScannerSurfCorr (unwindIndentsLoop sc col fuel) sp := by
  induction fuel generalizing sc with
  | zero => simpa only [unwindIndentsLoop] using hcorr
  | succ fuel' ih =>
    unfold unwindIndentsLoop; split
    · have hcorr_emit := corr_of_emit .blockEnd hcorr
      exact ih { (sc.emit .blockEnd) with indents := _, pendingKeys := _ }
        ⟨hcorr_emit.chars_from, hcorr_emit.col_eq, hcorr_emit.end_eq, hcorr_emit.input_prefix,
         fun i hi h0 => by
           simp only [ScannerState.emit] at hi ⊢
           rw [Array.getElem_pop]
           exact hcorr.indent_cols_nonneg i (by simp [Array.size_pop] at hi; omega) h0⟩
    · exact hcorr

lemma unwind_same_surface (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) :
    ScannerSurfCorr (unwindIndents sc col) sp := by
  unfold unwindIndents
  exact unwindLoop_same_surface sc sp hcorr col _

/-- Actual nonterminal preprocessing retains the skip-to-content cursor's
    surface correspondence and establishes that the skip did not reach EOF. -/
lemma preprocess_retains_skip (sc s' : ScannerState) (c : Char)
    (hok : scanNextToken_preprocess sc = .ok (some (s', c))) :
    ∃ s_content : ScannerState, skipToContent sc = .ok s_content ∧
      s_content.offset < s_content.inputEnd ∧
      (∀ sp, ScannerSurfCorr s_content sp → ScannerSurfCorr s' sp) := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    split at hok
    · simp at hok
    · rename_i h_more
      have hm : s_content.offset < s_content.inputEnd := by
        simp [ScannerState.hasMore] at h_more
        omega
      refine ⟨s_content, by first | exact h_skip | rfl, hm, ?_⟩
      intro sp1 hcorr1
      split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            have hcorr2 := unwind_same_surface s_content sp1 hcorr1 (↑s_content.col)
            have hcorr3 : ScannerSurfCorr
                { (unwindIndents s_content ↑s_content.col) with
                  needIndentCheck := false } sp1 :=
              ⟨hcorr2.chars_from, hcorr2.col_eq, hcorr2.end_eq, hcorr2.input_prefix, hcorr2.indent_cols_nonneg⟩
            exact closeStaleExplicitKey_corr _ sp1 (saveSimpleKey_corr _ sp1 hcorr3)
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            exact closeStaleExplicitKey_corr _ sp1 (saveSimpleKey_corr _ sp1 hcorr1)

/-- Produce the grammar prefix and exact indentation at a successful explicit
    key landing. The tab alternative is excluded by the actual scanKey result,
    not by a supplied grammar assumption. The start is a correlated column-0
    surface (e.g. the initial no-BOM cursor). -/
theorem explicit_key_prefix_geometry
    {sc prep q out : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hzero : sp.col = 0)
    (hpre : scanNextToken_preprocess sc = .ok (some (prep, '?')))
    (had : q = if prep.allowDirectives then
        { prep with allowDirectives := false, documentEverStarted := true } else prep)
    (hflow : q.inFlow = false) (hkey : scanKey q = .ok out) :
    ∃ sp_root sp_q, GStar SLDocumentPrefix sp sp_root ∧
      SSLComments sp_root sp_root ∧ SIndent q.col sp_root sp_q ∧
      ScannerSurfCorr q sp_q := by
  obtain ⟨s_content, hskip, hm, htransport⟩ := preprocess_retains_skip sc prep '?' hpre
  obtain ⟨sp_root, sp_ws, sp_q, hp, hz, hws, _, hc, hpk⟩ :=
    skipToContent_documentPrefix_prod sc sp s_content hcorr hzero hskip
  have heq : sp_q = sp_ws := by
    rcases hpk with h | h
    · exact h
    · obtain ⟨c, rest, hchars, hpeek⟩ := peek_corr s_content sp_q hc hm
      rw [hpeek] at h
      cases h
  rw [← heq] at hws
  have hprep : ScannerSurfCorr prep sp_q := htransport _ hc
  have hq : ScannerSurfCorr q sp_q := by
    rw [had]
    exact L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update hprep
  have hin : prep.input = sc.input := preprocess_input hpre
  have hqin : q.input = sc.input := by
    rw [had]
    split <;> exact hin
  rcases L4YAML.Proofs.StreamAccum.gstar_white_sIndent_or_tab hws with ⟨k, hk⟩ | htab
  · have hcol := L4YAML.Proofs.StreamAccum.SIndent_col hk
    have hqc := hq.col_eq
    have hkq : k = q.col := by omega
    rw [hkq] at hk
    refine ⟨sp_root, sp_q, .cons _ _ _ hp (.nil _), ?_, hk, hq⟩
    cases sp_root with
    | mk cs col =>
      simp only [] at hz
      subst col
      exact start_of_line_gives_SSLComments cs
  · have hsuf : sp_root.chars <:+ q.input.toList := by
      rw [hqin]
      exact (slDocumentPrefix_suffix hp).trans (corr_chars_suffix hcorr)
    have ht := tabIndent_scans_of_located hq hsuf hz hws htab
    exact False.elim (scanKey_tab_ne hflow ht.1 hkey)

/-- No-BOM initialization specialization: consumes the actual first preprocessing
    equation and key dispatch, without free source geometry witnesses. -/
theorem initial_no_bom_key_geometry
    {input : String} {prep q out : ScannerState}
    (hpre : scanNextToken_preprocess ((ScannerState.mk' input).emit .streamStart) =
      .ok (some (prep, '?')))
    (had : q = if prep.allowDirectives then
        { prep with allowDirectives := false, documentEverStarted := true } else prep)
    (hflow : q.inFlow = false) (hkey : scanKey q = .ok out) :
    ∃ sp_root sp_q, GStar SLDocumentPrefix ⟨input.toList, 0⟩ sp_root ∧
      SSLComments sp_root sp_root ∧ SIndent q.col sp_root sp_q ∧
      ScannerSurfCorr q sp_q := by
  have hinit := initial_corr input input.toList
    (L4YAML.Proofs.ScanStrictCoupling.chars_from_zero_toList input)
  have hc : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart) ⟨input.toList, 0⟩ :=
    ⟨hinit.chars_from, hinit.col_eq, hinit.end_eq, hinit.input_prefix, hinit.indent_cols_nonneg⟩
  exact explicit_key_prefix_geometry hc rfl hpre had hflow hkey

#print axioms unwind_same_surface
#print axioms preprocess_retains_skip
#print axioms explicit_key_prefix_geometry
#print axioms initial_no_bom_key_geometry
end L4YAML.Proofs.RootPrefixGeometry
