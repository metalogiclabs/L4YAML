/- Bounded conditional producer: scalar (plain/quoted) explicit keys only.
No whole-stream route is assumed for the first lemma.  The second lemma
consumes the retained key with the actual colon scanner production.
Actual reachability of SlotGateAt, NextIsSep and the enclosing mapping
route, and property/alias/block/flow keys, are separate obligations. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.StreamBridge
public import Tests.Guards.Proofs.ColonRolePartition
public import Tests.Guards.Proofs.OwnerExplicitKeyPark
public section
namespace L4YAML.Tests.Guards.ScalarKeyProducer
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.StructureProduction
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.PreprocessProduction
open L4YAML.Proofs.ScannerWhitespace L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.TabIndentBridge
open L4YAML.Proofs.StreamAccum (ContentArm NextIsSep SlotGateAt white_prepend_SSLComments)
lemma scalar_key_prefix_retained_from_scan
    {s_q sc s_prep s_ad s' : ScannerState} {c : Char}
    {sp_q sp_prep sp_a : SurfPos}
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
    (h_src : SlotGateAt s_prep) :
    ∃ sp_afterQ, GLit '?' sp_q sp_afterQ ∧ ScannerSurfCorr sc sp_afterQ ∧
      (((∃ sp_gram, GStar SSWhite sp_gram sp_a ∧
          (sp_gram = sp_a → s'.col ≠ 0 →
            ¬ (CommentOk s' ∧ s'.peek? = some '#')) ∧
          ∀ sp_key, SSLComments sp_gram sp_key →
          TBlockIndented s_q.col .blockOut sp_afterQ sp_key []) ∧
        PushesTrace s_ad.tokens s'.tokens []) ∨
        L4YAML.Proofs.FlowIndexLift.DedentLanding (s_q.col + 1) sp_afterQ sp_prep) := by
  obtain ⟨sp_afterQ, hq, h_corr⟩ := scanKey_prod s_q sp_q hq_corr hq_peek sc hq_scan
  refine ⟨sp_afterQ, hq, h_corr, ?_⟩
  have h_floor : IndentFloor sc (s_q.col + 1) :=
    IndentFloor.succ_of_int_le ((scanKey_needIndentCheck hq_flow hq_scan).trans hq_nic)
      (scanKey_col_le_currentIndent hq_flow hq_scan)
  have h_col : s_q.col + 1 ≤ sp_afterQ.col := by
    have hqc := hq_corr.col_eq
    cases hq
    simp_all
  have h_col0 : 0 < sp_afterQ.col := by omega
  have hflow : s_ad.inFlow = false := by unfold ScannerState.inFlow; rw [h_depth]; rfl
  have hcorr_ad : ScannerSurfCorr s_ad sp_prep := by
    rw [h_ad]
    exact L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update hcorr_prep
  have hpeek : s_ad.peek? = some c := by
    rw [h_ad]
    have := L4YAML.Proofs.StreamAccum.preprocess_some_peek h_preprocess
    split <;> exact this
  rcases TPendingNode.content_sep_of_preprocess h_ad h_floor h_col h_col0 h_next h_corr
      hcorr_prep hcorr' h_preprocess h_not_doc hflow h_dispatch h_src with
    ⟨h_sep, h_fl⟩ | h_ded
  · obtain ⟨sp_gram, sp_res, hT, hws, hgate, hcorr_res⟩ :=
      L4YAML.Tests.Guards.OwnerExplicitKeyPark.content_leaf_at_retained (s_q.col + 1) hcorr_ad hpeek hflow h_not_doc
        h_amp h_star h_bang h_pipe h_gt h_dispatch h_fl
    obtain rfl : sp_res = sp_a := ScannerSurfCorr_unique hcorr_res hcorr'
    obtain ⟨ev_n, hpt, hdisj⟩ := accum_step_content_trace_out arm hcorr_ad hpeek h_depth h_dispatch
    have hev : ev_n = [] := by
      rcases hdisj with ⟨hev, -⟩ | ⟨hev, -⟩ | ⟨hev, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hev
      · exact hev
      · exact hev
      · exact absurd hc h_amp
      · exact absurd hc h_bang
      · exact absurd hc h_star
    subst ev_n
    refine Or.inl ⟨⟨sp_gram, hws, hgate, ?_⟩, hpt⟩
    intro sp_key hssl
    exact .node _ .blockOut _ _ []
      (.flowInBlock _ .blockOut _ _ _ _ [] h_sep (.content _ _ _ _ _ hT)
        hssl)
  · exact Or.inr h_ded

/-- Consume the same retained key at the actual colon scan, supplying
precisely the mapValue park that content_step_park already consumes.
The map indentation and enclosing route remain explicit premises. -/
lemma scalar_key_to_value_route
    {n : Nat} {sp_start sp_q sp_afterQ sp_key sp_colon : SurfPos}
    {sc sc' : ScannerState} {ev_c ev_o : List Event}
    (hq : GLit '?' sp_q sp_afterQ)
    (hk : TBlockIndented n .blockOut sp_afterQ sp_key [])
    (hi : SIndent n sp_key sp_colon)
    (hcorr : ScannerSurfCorr sc sp_colon)
    (hpeek : sc.peek? = some ':') (hok : scanValue sc = .ok sc')
    (route : ∀ sp ev, TBlockMapEntry n sp_q sp ev →
      TLYamlStream sp_start sp (ev_c ++ ev_o ++ ev)) :
    ∃ sp_afterColon, ScannerSurfCorr sc' sp_afterColon ∧
      (∀ sp_mid ev_v, TBlockNode (n + 1) .blockOut sp_afterColon sp_mid ev_v →
        TLYamlStream sp_start sp_mid (ev_c ++ ev_o ++ ev_v)) := by
  obtain ⟨sp_afterColon, hc, hcorr'⟩ := scanValue_prod sc sp_colon hcorr hpeek sc' hok
  refine ⟨sp_afterColon, hcorr', ?_⟩
  intro sp_mid ev_v hv
  have he : TBlockMapEntry n sp_q sp_mid ([] ++ ev_v) :=
    .explicit n sp_q sp_afterQ sp_key sp_colon sp_afterColon sp_mid [] ev_v hq hk hi hc
      (.node n .blockOut _ _ _ hv)
  simpa using route sp_mid ([] ++ ev_v) he

lemma scalar_key_to_value_park
    {n : Nat} {sp_start sp_q sp_afterQ sp_key sp_colon : SurfPos}
    {sc sc' : ScannerState} {c : Char} {ev_c ev_o : List Event}
    (hq : GLit '?' sp_q sp_afterQ)
    (hk : TBlockIndented n .blockOut sp_afterQ sp_key [])
    (hi : SIndent n sp_key sp_colon)
    (hcorr : ScannerSurfCorr sc sp_colon)
    (hpeek : sc.peek? = some ':') (hok : scanValue sc = .ok sc')
    (route : ∀ sp ev, TBlockMapEntry n sp_q sp ev →
      TLYamlStream sp_start sp (ev_c ++ ev_o ++ ev)) :
    ∃ sp_afterColon, ScannerSurfCorr sc' sp_afterColon ∧
      TPendingNode.ContentPark sp_start sp_afterColon c ev_c (n + 1) ev_o := by
  obtain ⟨sp_afterColon, hc, hr⟩ := scalar_key_to_value_route hq hk hi hcorr hpeek hok route
  exact ⟨sp_afterColon, hc, .mapValue n ev_o hr⟩
/-- Compose the previously checked producer and colon consumer at the same
actual scanner continuation. No independent key certificate may be assumed.
The closing comment and indentation witnesses and enclosing route remain explicit. -/
lemma scalar_key_actual_landing_to_value_route
    {s_q sc s_prep s_ad s' sc_colon sc_afterColon : ScannerState} {c : Char}
    {sp_start sp_q sp_prep sp_a sp_colon : SurfPos} {ev_c ev_o : List Event}
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
    (h_colon_col : sp_colon.col = s_q.col)
    (h_colon_flow : sc_colon.inFlow = false)
    (hpre_colon : scanNextToken_preprocess s' = .ok (some (sc_colon, ':')))
    (hcorr_colon : ScannerSurfCorr sc_colon sp_colon)
    (hcolon : scanValue sc_colon = .ok sc_afterColon)
    (route : ∀ sp ev, TBlockMapEntry s_q.col sp_q sp ev →
      TLYamlStream sp_start sp (ev_c ++ ev_o ++ ev)) :
    ∃ sp_afterQ, GLit '?' sp_q sp_afterQ ∧ ScannerSurfCorr sc sp_afterQ ∧
      ((∃ sp_afterColon, ScannerSurfCorr sc_afterColon sp_afterColon ∧
        PushesTrace s_ad.tokens s'.tokens [] ∧
        (∀ sp_mid ev_v, TBlockNode (s_q.col + 1) .blockOut sp_afterColon sp_mid ev_v →
          TLYamlStream sp_start sp_mid (ev_c ++ ev_o ++ ev_v))) ∨
        L4YAML.Proofs.FlowIndexLift.DedentLanding (s_q.col + 1) sp_afterQ sp_prep) := by
  obtain ⟨sp_afterQ, hq, hcorrQ, h⟩ :=
    scalar_key_prefix_retained_from_scan hq_corr hq_peek hq_scan hq_flow hq_nic
      h_next h_ad hcorr_prep hcorr' h_preprocess arm h_depth h_dispatch
      h_not_doc h_amp h_star h_bang h_pipe h_gt h_src
  refine ⟨sp_afterQ, hq, hcorrQ, ?_⟩
  rcases h with ⟨⟨sp_gram, hrun, hg, hkey⟩, hpush⟩ | hd
  · classical
    obtain ⟨sp_mid, sp_ws, sp_prep2, hland, hws, _, hcorr2, hpk, hsuf⟩ :=
      L4YAML.Proofs.StreamAccum.preprocess_some_ssl_comments_landing
        s' sp_a sc_colon ':' hcorr' hpre_colon hrun hg
    have hp := L4YAML.Proofs.StreamAccum.preprocess_some_peek hpre_colon
    have h_eq : sp_prep2 = sp_ws := by
      rcases hpk with h | h
      · exact h
      · rw [hp] at h
        cases h
    have h_pe : sp_colon = sp_ws :=
      (ScannerSurfCorr_unique hcorr_colon hcorr2).trans h_eq
    rw [← h_pe] at hws
    rcases hland with hland | hflat
    · have hi : SIndent s_q.col sp_mid sp_colon := by
        rcases L4YAML.Proofs.StreamAccum.gstar_white_sIndent_or_tab hws with
          ⟨k, hk⟩ | htab
        · have hw := L4YAML.Proofs.StreamAccum.SIndent_col hk
          have hz := hland.2.1
          have he : k = s_q.col := by omega
          simpa [he] using hk
        · have hsuf' : sp_mid.chars <:+ sc_colon.input.toList := by
            rw [preprocess_input hpre_colon]
            exact hsuf.trans (corr_chars_suffix hcorr')
          have ht := tabIndent_scans_of_located hcorr_colon hsuf' hland.2.1 hws htab
          exact False.elim (scanValue_tab_ne h_colon_flow ht.2 hcolon)
      obtain ⟨sp_afterColon, hc, hpark⟩ :=
        scalar_key_to_value_route hq (hkey sp_mid hland.1) hi
          hcorr_colon hp hcolon route
      exact Or.inl ⟨sp_afterColon, hc, hpush, hpark⟩
    · obtain ⟨ws, _, _, hcolrun⟩ := gstar_sswhite_run hws
      have hmid := hflat.1
      rw [hmid] at hcolrun
      exfalso
      omega
  · exact Or.inr hd


lemma scalar_key_actual_landing_to_value_park
    {s_q sc s_prep s_ad s' sc_colon sc_afterColon : ScannerState} {c vc : Char}
    {sp_start sp_q sp_prep sp_a sp_colon : SurfPos} {ev_c ev_o : List Event}
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
    (h_colon_col : sp_colon.col = s_q.col)
    (h_colon_flow : sc_colon.inFlow = false)
    (hpre_colon : scanNextToken_preprocess s' = .ok (some (sc_colon, ':')))
    (hcorr_colon : ScannerSurfCorr sc_colon sp_colon)
    (hcolon : scanValue sc_colon = .ok sc_afterColon)
    (route : ∀ sp ev, TBlockMapEntry s_q.col sp_q sp ev →
      TLYamlStream sp_start sp (ev_c ++ ev_o ++ ev)) :
    ∃ sp_afterQ, GLit '?' sp_q sp_afterQ ∧ ScannerSurfCorr sc sp_afterQ ∧
      ((∃ sp_afterColon, ScannerSurfCorr sc_afterColon sp_afterColon ∧
        PushesTrace s_ad.tokens s'.tokens [] ∧
        TPendingNode.ContentPark sp_start sp_afterColon vc ev_c (s_q.col + 1) ev_o) ∨
        L4YAML.Proofs.FlowIndexLift.DedentLanding (s_q.col + 1) sp_afterQ sp_prep) := by
  obtain ⟨sp_afterQ, hq, hc, h⟩ :=
    scalar_key_actual_landing_to_value_route hq_corr hq_peek hq_scan hq_flow hq_nic
      h_next h_ad hcorr_prep hcorr' h_preprocess arm h_depth h_dispatch h_not_doc
      h_amp h_star h_bang h_pipe h_gt h_src h_deeper h_colon_col h_colon_flow
      hpre_colon hcorr_colon hcolon route
  refine ⟨sp_afterQ, hq, hc, ?_⟩
  rcases h with ⟨sp_afterColon, hcorr, hpush, hr⟩ | hd
  · exact Or.inl ⟨sp_afterColon, hcorr, hpush, .mapValue s_q.col ev_o hr⟩
  · exact Or.inr hd

/-- The actual grammar supplies the enclosing root route; no arbitrary
    map-to-stream function is passed by the caller. The root prefix,
    comment boundary and indentation still have to be produced by the fold. -/
lemma root_single_map_route
    {sp_start sp_root sp_line sp_q : SurfPos} {n : Nat}
    (hprefix : GStar SLDocumentPrefix sp_start sp_root)
    (hcomments : SSLComments sp_root sp_line)
    (hindent : SIndent n sp_line sp_q) :
    ∀ sp ev, TBlockMapEntry n sp_q sp ev → TLYamlStream sp_start sp ev := by
  intro sp ev hentry
  have he : TBlockMapEntries n sp_line sp ev :=
    .single n sp_line sp_q sp ev hindent hentry
  have hn : TBlockNode 0 .blockIn sp_root sp ev := by
    simpa using (TBlockNode.blockMap 0 .blockIn n sp_root sp_root sp_line sp [] ev
      (TOpt.none _) hcomments (by simpa using he))
  exact TLYamlStream.bareRoute hprefix sp ev hn

/-- Consume the retained key using the certified colon partition, then spend
    the produced mapValue park in the actual item-534 content_step_park and
    total consumers. No assumed colon equality or abstract root map route.
    This is a one-entry bare-root slice; the nonmatching colon and both
    dedent branches remain alternatives, not contradictions. -/
lemma scalar_root_key_value_fold_to_stream
    {s_q sc s_prep s_ad s' sc_colon sc_afterColon sv_prep sv_ad sv' : ScannerState}
    {c vc : Char}
    {sp_start sp_root sp_line sp_q sp_prep sp_a sp_colon sp_vstart sp_vprep sp_va sp_block sp_end : SurfPos}
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
    (hprefix : GStar SLDocumentPrefix sp_start sp_root)
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
    (hS : TSLYamlStream sp_start sv_ad sp_block [] [] [])
    (h_end : SSLComments sp_va sp_end) :
    TLYamlStream sp_start sp_end (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents sv'.tokens) ∨
    (∃ sp_afterQ, L4YAML.Proofs.FlowIndexLift.DedentLanding (s_q.col + 1) sp_afterQ sp_prep) ∨
    L4YAML.Proofs.FlowIndexLift.DedentLanding (s_q.col + 1) sp_vstart sp_vprep ∨
    sc_afterColon.implicitValueLine = some sc_afterColon.line ∨
    L4YAML.Tests.Guards.ColonRolePartition.StaleAt sc s_prep ∨
    L4YAML.Tests.Guards.ColonRolePartition.StaleAt s' sc_colon := by
  have hp := L4YAML.Proofs.StreamAccum.preprocess_some_peek hpre_colon
  rcases L4YAML.Tests.Guards.ColonRolePartition.scalar_colon_role_partition
    hq_scan h_preprocess h_ad h_dispatch hpre_colon hcolon h_colon_flow hp with hm | hs | hs1 | hs2
  · have hcc : sp_colon.col = s_q.col := hcorr_colon.col_eq.trans hm
    have route : ∀ sp ev, TBlockMapEntry s_q.col sp_q sp ev →
        TLYamlStream sp_start sp ([] ++ [] ++ ev) := by
      intro sp ev he
      simpa using root_single_map_route hprefix hcomments hindent sp ev he
    obtain ⟨sp_afterQ, _, _, h⟩ :=
      scalar_key_actual_landing_to_value_park (vc := vc)
        hq_corr hq_peek hq_scan hq_flow hq_nic h_next h_ad hcorr_prep hcorr'
        h_preprocess arm h_depth h_dispatch h_not_doc h_amp h_star h_bang h_pipe h_gt
        h_src h_deeper hcc h_colon_flow hpre_colon hcorr_colon hcolon route
    rcases h with ⟨sp_afterColon, hcorr_after, _, hpark⟩ | hded
    · have h_after_eq : sp_afterColon = sp_vstart := ScannerSurfCorr_unique hcorr_after hcorr_vstart
      rw [h_after_eq] at hpark
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
      rcases TPendingNode.content_step_park hS hpark h_vad h_vfloor h_vcol h_vcol0
          h_vnext hcorr_vstart hcorr_vprep hcorr_va h_vpreprocess arm_v h_vdepth
          h_vdispatch h_vnotdoc h_vsrc with ⟨ev_n, hS', hP⟩ | hd
      · exact Or.inl (TPendingNode.total hS' hP h_end)
      · exact Or.inr (Or.inr (Or.inl hd))
    · exact Or.inr (Or.inl ⟨sp_afterQ, hded⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs2))))

#print axioms root_single_map_route
#print axioms scalar_root_key_value_fold_to_stream

#print axioms L4YAML.Tests.Guards.OwnerExplicitKeyPark.content_leaf_at_retained
#print axioms scalar_key_prefix_retained_from_scan
#print axioms scalar_key_to_value_park
#print axioms scalar_key_actual_landing_to_value_park
end L4YAML.Tests.Guards.ScalarKeyProducer
end
