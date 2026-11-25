module
public import Tests.Guards.Proofs.OwnerExplicitKeyTransport
import all Tests.Guards.Proofs.OwnerExplicitKeyTransport
public import Tests.Guards.Proofs.OwnerExplicitKeyFreshTransport
import all Tests.Guards.Proofs.OwnerExplicitKeyFreshTransport
public import L4YAML.Proofs.Scanner.PropsRunLineCoupling
public section
namespace L4YAML.Tests.Guards.OwnerExplicitKeyConsume
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.StructureProduction
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.StreamAccum
open L4YAML.Tests.Guards.OwnerExplicitKeyPark
open L4YAML.Tests.Guards.OwnerExplicitKeyTransport
set_option maxHeartbeats 4000000

-- Blueprint 7.7: these producers feed colon_then_content_step, which consumes
-- the actual owner's content_step_park. Full scan_trace is still open.
private lemma value_dispatch_candidate {s s' : ScannerState}
    (h : scanNextToken_dispatchBlockIndicators s ':' = .ok (some s')) :
    isValueCandidate s = true := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  simp at h
  split at h
  · assumption
  · simp at h

private lemma value_floor_from_col_drop {s p s' : ScannerState}
    (hflow : p.inFlow = false)
    (hpre : scanNextToken_preprocess s = .ok (some (p, ':')))
    (hdrop : p.col < s.col) (hscan : scanValue p = .ok s') :
    IndentFloor s' (p.col + 1) := by
  have hf : s.inFlow = false := by
    unfold ScannerState.inFlow at hflow ⊢
    rw [← preprocess_preserves_flowLevel s p ':' hpre]
    exact hflow
  obtain ⟨u, w, hskip, hsave, hcases⟩ :=
    L4YAML.Proofs.EntryBoundaryLayout.preprocess_save_elim hpre
  have hucol : u.col = w.col := by
    rcases hcases with rfl | rfl
    · rfl
    · exact unwindIndents_col w _
  have hpcol : p.col = w.col := by
    rw [hsave, L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_col,
      L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col, hucol]
  have ha := L4YAML.Tests.Guards.OwnerExplicitKeyFreshTransport.skip_col_drop_allowed
    hskip hf (by omega)
  have hkeycol := (preprocess_saved_key_col_of_walk hskip ha hflow hpre).2
  have hcurr := scanValue_col_le_currentIndent hflow (fun _ => hkeycol) hscan
  have hnic := L4YAML.Proofs.PropsRunLineCoupling.preprocess_some_needIndentCheck_false hf hpre
  exact IndentFloor.succ_of_int_le ((scanValue_needIndentCheck hscan).trans hnic) hcurr

/-- Consume a retained key, its matched colon, and the following content dispatch
through the actual owner fold. The colon produces its floor, column and separator;
preprocessing supplies event transport. Dedent remains an explicit outcome.
The enclosing key route and source coupling remain caller obligations; no full reachability or scan_trace claim is made. -/
lemma colon_then_content_step
    {start q after scan sp_colon sp_block sp_prep sp_a : SurfPos} {n : Nat}
    {s sc_colon sc_after s_prep s_ad s' : ScannerState} {c : Char} {ec eo ek : List Event}
    (hS : TSLYamlStream start s sp_block ec (eo ++ ek) [])
    (park : KeyReady start q after scan n s ec eo ek)
    (h_deeper : n < scan.col) (h_colon_col : sp_colon.col = n)
    (h_flow : sc_colon.inFlow = false)
    (hpre_colon : scanNextToken_preprocess s = .ok (some (sc_colon, ':')))
    (hcorr_colon : ScannerSurfCorr sc_colon sp_colon)
    (hcolon_dispatch : scanNextToken_dispatchBlockIndicators sc_colon ':' = .ok (some sc_after))
    (h_ad : s_ad = if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true } else s_prep)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpre_value : scanNextToken_preprocess sc_after = .ok (some (s_prep, c)))
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (h_depth : s_ad.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_src : SlotGateAt s_prep) :
    ∃ sp_after, ScannerSurfCorr sc_after sp_after ∧
      ((∃ ev_n, TSLYamlStream start s' sp_block ec ((eo ++ ek) ++ ev_n) [] ∧
        TPendingNode start false sp_block sp_a ec ((eo ++ ek) ++ ev_n) []) ∨
      L4YAML.Proofs.FlowIndexLift.DedentLanding (n + 1) sp_after sp_prep) := by
  have hcolon := dispatchBlockIndicators_value_scan hcolon_dispatch
  have hpeek := preprocess_some_peek hpre_colon
  have hdrop : sc_colon.col < s.col := by
    cases park with
    | ready gram hq hc =>
      have hs := hc.col_eq
      have hp := hcorr_colon.col_eq
      omega
  obtain ⟨sp_after, hcorr, hstate, _, hpark⟩ :=
    L4YAML.Tests.Guards.OwnerExplicitKeyFreshTransport.matched_colon_owner_fold_from_transitions (vc := c) hS park h_deeper h_colon_col
      h_flow hpre_colon hcorr_colon hcolon
  obtain ⟨sp_after', hglit, hcorr'colon⟩ :=
    scanValue_prod sc_colon sp_colon hcorr_colon hpeek sc_after hcolon
  have heq := ScannerSurfCorr_unique hcorr'colon hcorr
  subst sp_after'
  have hcol : sp_after.col = n + 1 := by
    cases hglit
    simp_all
  have hfloor : IndentFloor sc_after (n + 1) := by
    have hf := value_floor_from_col_drop h_flow hpre_colon hdrop hcolon
    have hc := hcorr_colon.col_eq
    rw [← hc, h_colon_col] at hf
    exact hf
  have hnext := nextIsSep_of_scanValue h_flow hpeek
    (value_dispatch_candidate hcolon_dispatch) hcolon
  have hS_ad : TSLYamlStream start s_ad sp_block ec (eo ++ ek) [] := by
    refine ⟨hstate.stream, ?_⟩
    have ht := preprocess_silent hpre_value []
    have htok : s_ad.tokens = s_prep.tokens := by rw [h_ad]; split <;> rfl
    rw [htok, ht, hstate.events]
  exact ⟨sp_after, hcorr, TPendingNode.content_step_park hS_ad hpark h_ad hfloor
    (by omega) (by omega) hnext hcorr hcorr_prep hcorr' hpre_value arm h_depth
    h_dispatch h_not_doc h_src⟩

#print axioms colon_then_content_step
end L4YAML.Tests.Guards.OwnerExplicitKeyConsume
