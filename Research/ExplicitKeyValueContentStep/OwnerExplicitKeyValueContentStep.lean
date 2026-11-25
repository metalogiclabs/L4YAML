module
public import Tests.Guards.Proofs.OwnerExplicitKeyFreshTransport
import all Tests.Guards.Proofs.OwnerExplicitKeyTransport
public import L4YAML.Proofs.Scanner.PropsRunLineCoupling
public section
set_option maxHeartbeats 4000000
namespace L4YAML.Tests.Guards.OwnerExplicitKeyValueContentStep
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Tests.Guards.OwnerExplicitKeyPark
open L4YAML.Tests.Guards.OwnerExplicitKeyTransport
open L4YAML.Tests.Guards.OwnerExplicitKeyFreshTransport
open L4YAML.Proofs.StreamAccum (ContentArm NextIsSep SlotGateAt)

-- Blueprint 7.7 chain: native colon readiness → owner content_step_park
-- → explicit-key depth-zero fold → scan_trace (the complete fold remains open).
private lemma preprocess_col_drop_saved_col {s p : ScannerState}
    (hf : s.inFlow = false) (hfp : p.inFlow = false)
    (hpre : scanNextToken_preprocess s = .ok (some (p, ':')))
    (hdrop : p.col < s.col) : p.simpleKey.pos.col = p.col := by
  obtain ⟨u, w, hskip, hsave, hcases⟩ :=
    L4YAML.Proofs.EntryBoundaryLayout.preprocess_save_elim hpre
  have huc : u.col = w.col := by
    rcases hcases with h | h
    · rw [h]
    · rw [h]
      exact unwindIndents_col w _
  have hpc : p.col = w.col := by
    rw [hsave, closeStaleExplicitKey_col, L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col, huc]
  have ha := skip_col_drop_allowed hskip hf (by omega)
  exact (L4YAML.Proofs.StreamAccum.preprocess_saved_key_col_of_walk hskip ha hfp hpre).2

/-- Native preprocessing and actual colon dispatch supply the post-colon
    indentation floor and separator needed by the owner's content fold. -/
private lemma native_colon_floor_and_next {s p a : ScannerState}
    (hf : s.inFlow = false) (hfp : p.inFlow = false)
    (hpre : scanNextToken_preprocess s = .ok (some (p, ':')))
    (hdrop : p.col < s.col)
    (hd : scanNextToken_dispatchBlockIndicators p ':' = .ok (some a)) :
    IndentFloor a (p.col + 1) ∧ NextIsSep a := by
  have hv := L4YAML.Proofs.StreamAccum.dispatchBlock_colon_scanValue hd
  have hn := L4YAML.Proofs.PropsRunLineCoupling.preprocess_some_needIndentCheck_false hf hpre
  have hk := preprocess_col_drop_saved_col hf hfp hpre hdrop
  exact ⟨IndentFloor.succ_of_int_le ((scanValue_needIndentCheck hv).trans hn)
      (scanValue_col_le_currentIndent hfp (fun _ => hk) hv),
    L4YAML.Proofs.StreamAccum.dispatchBlock_colon_next hfp
      (L4YAML.Proofs.StreamAccum.preprocess_some_peek hpre) hd⟩

/-- The matched colon returns the owner's pending node together with every
    post-colon reading required by its actual content_step_park consumer. -/
lemma matched_colon_owner_content_ready
    {start q after scan sp_colon sp_block : SurfPos} {n : Nat}
    {s sc_colon sc_after : ScannerState} {vc : Char} {ec eo ek : List Event}
    (hS : TSLYamlStream start s sp_block ec (eo ++ ek) [])
    (park : KeyReady start q after scan n s ec eo ek)
    (h_deeper : n < scan.col) (h_colon_col : sp_colon.col = n)
    (h_flow : sc_colon.inFlow = false)
    (hpre : scanNextToken_preprocess s = .ok (some (sc_colon, ':')))
    (hcorr_colon : ScannerSurfCorr sc_colon sp_colon)
    (hdispatch : scanNextToken_dispatchBlockIndicators sc_colon ':' = .ok (some sc_after)) :
    ∃ sp_after, ScannerSurfCorr sc_after sp_after ∧
      TSLYamlStream start sc_after sp_block ec (eo ++ ek) [] ∧
      TPendingNode start false sp_block sp_after ec (eo ++ ek) [] ∧
      TPendingNode.ContentPark start sp_after vc ec (n + 1) (eo ++ ek) ∧
      IndentFloor sc_after (n + 1) ∧ sp_after.col = n + 1 ∧ NextIsSep sc_after := by
  have hv := L4YAML.Proofs.StreamAccum.dispatchBlock_colon_scanValue hdispatch
  have hf : s.inFlow = false := by
    unfold ScannerState.inFlow at h_flow ⊢
    rw [← L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel s sc_colon ':' hpre]
    exact h_flow
  have hdrop : sc_colon.col < s.col := by
    cases park with
    | ready gram hq hc =>
      have h1 := hc.col_eq
      have h2 := hcorr_colon.col_eq
      omega
  obtain ⟨sp_after, hc, hs, hp, hpark⟩ :=
    matched_colon_owner_fold_from_transitions (vc := vc) hS park h_deeper h_colon_col
      h_flow hpre hcorr_colon hv
  obtain ⟨hfloor, hnext⟩ := native_colon_floor_and_next hf h_flow hpre hdrop hdispatch
  have hnc : sc_colon.col = n := by have := hcorr_colon.col_eq; omega
  rw [hnc] at hfloor
  have hcol : sp_after.col = n + 1 := by
    obtain ⟨sp_next, hlit, hcnext⟩ := L4YAML.Proofs.StructureProduction.scanValue_prod sc_colon sp_colon hcorr_colon
      (L4YAML.Proofs.StreamAccum.preprocess_some_peek hpre) sc_after hv
    have heq := ScannerSurfCorr_unique hcnext hc
    rw [heq] at hlit
    cases hlit
    simp_all
  exact ⟨sp_after, hc, hs, hp, hpark, hfloor, hcol, hnext⟩

/-- Consume the returned map-value park with the owner's actual content fold.
    Its floor, column, follower and incoming event coupling are all derived
    from the two native preprocessing passes and the colon dispatch. -/
lemma matched_colon_then_owner_content_step
    {start q after scan sp_colon sp_block sp_prep sp_a : SurfPos} {n : Nat}
    {s sc_colon sc_after s_prep s_ad s' : ScannerState} {vc : Char} {ec eo ek : List Event}
    (hS : TSLYamlStream start s sp_block ec (eo ++ ek) [])
    (park : KeyReady start q after scan n s ec eo ek)
    (h_deeper : n < scan.col) (h_colon_col : sp_colon.col = n)
    (h_flow : sc_colon.inFlow = false)
    (hpre : scanNextToken_preprocess s = .ok (some (sc_colon, ':')))
    (hcorr_colon : ScannerSurfCorr sc_colon sp_colon)
    (hcolon : scanNextToken_dispatchBlockIndicators sc_colon ':' = .ok (some sc_after))
    (h_ad : s_ad = if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true } else s_prep)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpre_value : scanNextToken_preprocess sc_after = .ok (some (s_prep, vc)))
    (arm : ContentArm s_ad s' vc sp_prep sp_a)
    (h_depth : s_ad.flowLevel = 0)
    (hdispatch : scanNextToken_dispatchContent s_ad vc = .ok s')
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_src : SlotGateAt s_prep) :
    (∃ ev_n, TSLYamlStream start s' sp_block ec ((eo ++ ek) ++ ev_n) [] ∧
      TPendingNode start false sp_block sp_a ec ((eo ++ ek) ++ ev_n) []) ∨
    (∃ sp_after, ScannerSurfCorr sc_after sp_after ∧
      L4YAML.Proofs.FlowIndexLift.DedentLanding (n + 1) sp_after sp_prep) := by
  obtain ⟨sp_after, hc, hs, _, hpark, hfloor, hcol, hnext⟩ :=
    matched_colon_owner_content_ready (vc := vc) hS park h_deeper h_colon_col
      h_flow hpre hcorr_colon hcolon
  have htokens : s_ad.tokens = s_prep.tokens := by rw [h_ad]; split <;> rfl
  have hs_ad : TSLYamlStream start s_ad sp_block ec (eo ++ ek) [] :=
    ⟨hs.stream, by rw [htokens, (preprocess_silent hpre_value) [], hs.events]⟩
  rcases TPendingNode.content_step_park hs_ad hpark h_ad hfloor (by omega) (by omega)
      hnext hc hcorr_prep hcorr' hpre_value arm h_depth hdispatch h_not_doc h_src with h | h
  · exact Or.inl h
  · exact Or.inr ⟨sp_after, hc, h⟩

#print axioms matched_colon_owner_content_ready
#print axioms matched_colon_then_owner_content_step
run_meta do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let ready ← Lean.collectAxioms ``matched_colon_owner_content_ready
  unless ready.all allowed.contains do throwError "native colon readiness gained nonstandard axioms: {ready}"
  let actual ← Lean.collectAxioms ``matched_colon_then_owner_content_step
  let owner ← Lean.collectAxioms ``TPendingNode.content_step_park
  unless actual.all owner.contains && owner.all actual.contains do
    throwError "value consumer axiom closure differs from actual owner content fold"
  let raw := actual.filter fun a => !allowed.contains a
  unless raw.size == 45 do throwError "owner content native census changed: {raw.size}"
  Lean.logInfo m!"OWNER_VALUE_CONTENT_AXIOM_IDENTITY raw={raw.size} readiness_standard_only=true"
end L4YAML.Tests.Guards.OwnerExplicitKeyValueContentStep
