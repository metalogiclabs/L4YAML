module
public import Tests.Guards.Proofs.RootEventEOF
public import Tests.Guards.Proofs.ReachableEOF
public section
namespace L4YAML.Tests.Guards.RootComposedTrace
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.StructureProduction
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.PreprocessProduction L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.StreamAccum (ContentArm NextIsSep SlotGateAt)
open L4YAML.Tests.Guards.ScalarKeyProducer L4YAML.Tests.Guards.RootEventEOF

lemma scan_four_steps_to_terminal
    {input : String} {sc k out sv' : ScannerState} {filtered : Array (Positioned YamlToken)}
    (h1 : scanNextToken (initial input) = .ok (some sc))
    (h2 : scanNextToken sc = .ok (some k))
    (h3 : scanNextToken k = .ok (some out))
    (h4 : scanNextToken out = .ok (some sv'))
    (hf : scanFiltered input = .ok filtered) :
    ∃ fuel ts, scanLoop sv' (fuel + 1) = .ok ts ∧
      filtered = ts.filter (fun t => t.val != .placeholder) := by
  have hsize : (input.utf8ByteSize + 1) * 4 = input.utf8ByteSize * 4 + 4 := by omega
  have hprefix (n : Nat) : scanLoop (initial input) (n + 4) = scanLoop sv' n := by
    calc
      scanLoop (initial input) (n + 4) = scanLoop sc (n + 3) := by rw [scanLoop, h1]
      _ = scanLoop k (n + 2) := by rw [scanLoop, h2]
      _ = scanLoop out (n + 1) := by rw [scanLoop, h3]
      _ = scanLoop sv' n := by rw [scanLoop, h4]
  cases hs : scan input with
  | error e => simp [scanFiltered, hs] at hf
  | ok raw =>
    have hloop := scan_success_initial_loop input raw hs
    rw [hsize, hprefix] at hloop
    have he : raw.filter (fun t => t.val != .placeholder) = filtered := by
      simpa [scanFiltered, hs] using hf
    cases hn : input.utf8ByteSize * 4 with
    | zero => simp [scanLoop, hn] at hloop
    | succ fuel =>
      refine ⟨fuel, raw, ?_, he.symm⟩
      first | exact hloop | simpa [hn] using hloop


/-- Conditional restricted actual-prefix-to-filtered-trace theorem.  The key's
    preprocessed state and dispatched state are distinct, and the value route
    consumes the very same leaf's retained comment gate. All non-root roles
    and dedents remain explicit outcomes. No arbitrary final closing function,
    assumed event invariant, or final grammar comment premise. -/
lemma scalar_root_actual_filtered_trace
    {input : String} {q_prep s_q sc s_prep s_ad s' sc_colon sc_afterColon sv_prep sv_ad sv' : ScannerState} {filtered : Array (Positioned YamlToken)}
    {c vc : Char}
    {sp_root sp_line sp_q sp_prep sp_a sp_colon sp_vstart sp_vprep sp_va : SurfPos}
    (hinit : scanNextToken_preprocess (initial input) = .ok (some (q_prep, '?')))
    (hq_ad : s_q = if q_prep.allowDirectives then
      { q_prep with allowDirectives := false, documentEverStarted := true } else q_prep)
    (hstepQ : scanNextToken (initial input) = .ok (some sc))
    (hstepK : scanNextToken sc = .ok (some s'))
    (hstepColon : scanNextToken s' = .ok (some sc_afterColon))
    (hstepV : scanNextToken sc_afterColon = .ok (some sv'))
    (hfiltered : scanFiltered input = .ok filtered)
    (hq_corr : ScannerSurfCorr s_q sp_q) (hq_peek : s_q.peek? = some '?')
    (hq_scan : scanKey s_q = .ok sc) (hq_flow : s_q.inFlow = false)
    (hq_nic : s_q.needIndentCheck = false)
    (h_next : NextIsSep sc)
    (h_ad : s_ad = if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true } else s_prep)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr' : ScannerSurfCorr s' sp_a)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (h_depth : s_ad.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_amp : c ≠ '&') (h_star : c ≠ '*') (h_bang : c ≠ '!')
    (h_pipe : c ≠ '|') (h_gt : c ≠ '>')
    (h_src : SlotGateAt s_prep)
    (h_deeper : s_q.col < sp_a.col)
    (h_colon_flow : sc_colon.inFlow = false)
    (hpre_colon : scanNextToken_preprocess s' = .ok (some (sc_colon, ':')))
    (hcorr_colon : ScannerSurfCorr sc_colon sp_colon)
    (hcolon : scanValue sc_colon = .ok sc_afterColon)
    (hprefix : GStar SLDocumentPrefix ⟨input.toList, 0⟩ sp_root)
    (hcomments : SSLComments sp_root sp_line)
    (hindent : SIndent s_q.col sp_line sp_q)
    (hcorr_vstart : ScannerSurfCorr sc_afterColon sp_vstart)
    (h_vnic : sc_colon.needIndentCheck = false)
    (h_vfresh : sc_colon.simpleKey.possible = true → sc_colon.simpleKey.pos.col = sc_colon.col)
    (h_vnext : NextIsSep sc_afterColon)
    (h_vad : sv_ad = if sv_prep.allowDirectives then
      { sv_prep with allowDirectives := false, documentEverStarted := true } else sv_prep)
    (h_vpreprocess : scanNextToken_preprocess sc_afterColon = .ok (some (sv_prep, vc)))
    (hcorr_vprep : ScannerSurfCorr sv_prep sp_vprep)
    (hcorr_va : ScannerSurfCorr sv' sp_va)
    (arm_v : ContentArm sv_ad sv' vc sp_vprep sp_va)
    (h_vdepth : sv_ad.flowLevel = 0)
    (h_vdispatch : scanNextToken_dispatchContent sv_ad vc = .ok sv')
    (h_vnotdoc : sv_ad.col = 0 → atDocumentBoundary sv_ad = false)
    (h_vsrc : SlotGateAt sv_prep)
    (h_vamp : vc ≠ '&') (h_vstar : vc ≠ '*') (h_vbang : vc ≠ '!')
    (h_vpipe : vc ≠ '|') (h_vgt : vc ≠ '>')
    (hterminal : scanNextToken sv' = .ok none) :
    TraceOf input (tokenEvents filtered) ∨
    (∃ sp_afterQ, L4YAML.Proofs.FlowIndexLift.DedentLanding (s_q.col + 1) sp_afterQ sp_prep) ∨
    L4YAML.Proofs.FlowIndexLift.DedentLanding (s_q.col + 1) sp_vstart sp_vprep ∨
    sc_afterColon.implicitValueLine = some sc_afterColon.line ∨
    L4YAML.Tests.Guards.ColonRolePartition.StaleAt sc s_prep ∨
    L4YAML.Tests.Guards.ColonRolePartition.StaleAt s' sc_colon := by
  have hp := L4YAML.Proofs.StreamAccum.preprocess_some_peek hpre_colon
  rcases L4YAML.Tests.Guards.ColonRolePartition.scalar_colon_role_partition
    hq_scan h_preprocess h_ad h_dispatch hpre_colon hcolon h_colon_flow hp with hm | hs | hs1 | hs2
  · by_cases hstamp : sc_afterColon.implicitValueLine = some sc_afterColon.line
    · exact Or.inr (Or.inr (Or.inr (Or.inl hstamp)))
    have hcc : sp_colon.col = s_q.col := hcorr_colon.col_eq.trans hm
    have route : ∀ sp ev, TBlockMapEntry s_q.col sp_q sp ev →
        TLYamlStream ⟨input.toList, 0⟩ sp ([] ++ [] ++ ev) := by
      intro sp ev he
      simpa using root_single_map_route hprefix hcomments hindent sp ev he
    obtain ⟨sp_afterQ, _, _, h⟩ :=
      scalar_key_actual_landing_to_value_route
        hq_corr hq_peek hq_scan hq_flow hq_nic h_next h_ad hcorr_prep hcorr'
        h_preprocess arm h_depth h_dispatch h_not_doc h_amp h_star h_bang h_pipe h_gt
        h_src h_deeper hcc h_colon_flow hpre_colon hcorr_colon hcolon route
    rcases h with ⟨sp_afterColon, hcorr_after, _, hroute⟩ | hded
    · have h_after_eq : sp_afterColon = sp_vstart := ScannerSurfCorr_unique hcorr_after hcorr_vstart
      rw [h_after_eq] at hroute
      obtain ⟨sp_tmp, hgl, hcorr_tmp⟩ :=
        scanValue_prod sc_colon sp_colon hcorr_colon hp sc_afterColon hcolon
      have h_tmp_eq : sp_tmp = sp_vstart := ScannerSurfCorr_unique hcorr_tmp hcorr_vstart
      rw [h_tmp_eq] at hgl
      have h_vcol : s_q.col + 1 ≤ sp_vstart.col := by
        cases hgl
        simp_all
      have h_vcol0 : 0 < sp_vstart.col := by omega
      have h_vfloor : IndentFloor sc_afterColon (s_q.col + 1) :=
        IndentFloor.succ_of_int_le ((scanValue_needIndentCheck hcolon).trans h_vnic)
          (by rw [← hm]; exact scanValue_col_le_currentIndent h_colon_flow h_vfresh hcolon)
      have hflow : sv_ad.inFlow = false := by
        unfold ScannerState.inFlow
        rw [h_vdepth]
        rfl
      rcases TPendingNode.content_sep_of_preprocess h_vad h_vfloor h_vcol h_vcol0
          h_vnext hcorr_vstart hcorr_vprep hcorr_va h_vpreprocess h_vnotdoc
          hflow h_vdispatch h_vsrc with ⟨hsep, hfl⟩ | hd
      · have hcorr_ad : ScannerSurfCorr s_ad sp_prep := by
          rw [h_ad]
          exact L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update hcorr_prep
        have hpeek_ad : s_ad.peek? = some c := by
          rw [h_ad]
          have := L4YAML.Proofs.StreamAccum.preprocess_some_peek h_preprocess
          split <;> exact this
        have hqtok : s_q.tokens = q_prep.tokens := by
          rw [hq_ad]
          split <;> rfl
        have hS := root_event_from_steps_retained hinit hqtok hq_scan h_preprocess
          h_ad hcorr_ad hpeek_ad arm h_depth h_dispatch h_amp h_bang h_star
          hpre_colon hcolon h_colon_flow hp hstamp h_vpreprocess h_vad
        have hcorr_vad : ScannerSurfCorr sv_ad sp_vprep := by
          rw [h_vad]
          exact L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update hcorr_vprep
        have hpeek_vad : sv_ad.peek? = some vc := by
          rw [h_vad]
          have := L4YAML.Proofs.StreamAccum.preprocess_some_peek h_vpreprocess
          split <;> exact this
        obtain ⟨sp_gram, sp_scan, hT, hws, hgate, hc⟩ :=
          L4YAML.Tests.Guards.OwnerExplicitKeyPark.content_leaf_at_retained (s_q.col + 1) hcorr_vad hpeek_vad hflow h_vnotdoc
            h_vamp h_vstar h_vbang h_vpipe h_vgt h_vdispatch hfl
        have hevents : tokenEvents sv'.tokens = [] := by
          rw [tokenEvents_eq_goOut,
            scalar_dispatch_silent arm_v hcorr_vad hpeek_vad h_vdepth h_vdispatch
              h_vamp h_vbang h_vstar [], hS.events]
          simp
        have hclose : ∀ sp_end, SSLComments sp_gram sp_end →
            TLYamlStream ⟨input.toList, 0⟩ sp_end (tokenEvents sv'.tokens) := by
          intro sp_end hssl
          rw [hevents]
          simpa using hroute sp_end []
            (.flowInBlock (s_q.col + 1) .blockOut sp_vstart sp_vprep sp_gram sp_end []
              hsep (.content _ _ _ _ _ hT) hssl)
        obtain ⟨fuel, raw, hloop, heq⟩ :=
          scan_four_steps_to_terminal hstepQ hstepK hstepColon hstepV hfiltered
        left
        rw [heq]
        obtain ⟨s_result, p_eof, hskip, _, heof, _⟩ :=
          L4YAML.Proofs.ReachableEOF.next_none_reachable_eof sv' sp_scan hc hterminal
        exact eof_from_retained_park hc hws hgate hskip heof hloop hclose
      · exact Or.inr (Or.inr (Or.inl hd))
    · exact Or.inr (Or.inl ⟨sp_afterQ, hded⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs2))))


#print axioms scan_four_steps_to_terminal
#print axioms root_event_from_steps_retained
#print axioms scalar_key_actual_landing_to_value_route
#print axioms scalar_root_actual_filtered_trace
end L4YAML.Tests.Guards.RootComposedTrace
end
