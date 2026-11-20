/-
S3 / Group 7.7: content producer for an already open document.
The native document-start consumer below supplies the route it spends.
This module does not assert a global scan_trace theorem.
The inherited scalar/property axiom ceiling and the closed native consumer
are checked in Tests.Guards.Proofs.RightWallContentAxioms; the existing
strict serialization headline sweep remains unchanged.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.RightWallBoundary

@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.RightWallContent

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.StreamAccum (ContentArm dispatchContent_blockScalar_prod)
open L4YAML.Proofs.NodeProduction (SCDoubleQuoted_ctx_lift SCSingleQuoted_ctx_lift)

/-- The same native leaf construction as content_step_noPending, with a
possibly nonempty open-event prefix. The closed source boundary and the
start of the current node are kept distinct. -/
lemma content_step_routed0
    {sp_start block node sp_prep sp_a : SurfPos} {s_prep s' : ScannerState} {c : Char}
    {ev_c ev_o : List Event}
    (hS : TSLYamlStream sp_start s_prep block ev_c ev_o [])
    (h_sep : SSeparateLines 0 node sp_prep)
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c) (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s')
    (h_route : ∀ sp_m ev_n, TBlockNode 0 .blockIn node sp_m ev_n →
      TLYamlStream sp_start sp_m (ev_c ++ ev_o ++ ev_n)) :
    ∃ ev_n, TSLYamlStream sp_start s' block ev_c (ev_o ++ ev_n) [] ∧
      TPendingNode sp_start false block sp_a ev_c (ev_o ++ ev_n) [] := by
  obtain ⟨ev_n, hpt, hdisj⟩ := accum_step_content_trace_out arm hcorr hpeek h_depth h_dispatch
  refine ⟨ev_n, ⟨hS.stream, by rw [hpt.goOut_at [], hS.events]; simp [List.append_assoc]⟩, ?_⟩
  rcases hdisj with ⟨hev, sp_gram, hT, hws, -⟩ | ⟨hev, hc, -⟩ | ⟨hev, hc, -⟩ | ⟨-, ha, -⟩ | ⟨-, ht, -⟩ | ⟨-, hal⟩
  · subst hev
    simp only [List.append_nil]
    exact .pendingContent block sp_a sp_gram ev_c ev_o
      (fun sp_mid h_ssl => by simpa using h_route sp_mid [] (.flowInBlock 0 .blockIn node sp_prep sp_gram sp_mid [] h_sep hT h_ssl))
      hws
  · subst hev
    simp only [List.append_nil]
    have hFlow : TFlowNode 0 .flowOut sp_prep sp_a [] := by
      cases arm with
      | doubleQuoted _ _ hq _ _ =>
        exact .content _ _ _ _ _ (.doubleQ _ _ _ _ (SCDoubleQuoted_ctx_lift hq (by decide) (by decide)))
      | singleQuoted _ _ hq _ _ =>
        exact .content _ _ _ _ _ (.singleQ _ _ _ _ (SCSingleQuoted_ctx_lift hq (by decide) (by decide)))
      | plainIn _ _ hd _ _ => omega
      | plain _ _ h_c _ _ _ _ _ => rcases hc with h | h <;> simp_all
      | blockScalar _ h_c _ _ => rcases hc with h | h <;> rcases h_c with h' | h' <;> simp_all
      | anchor _ h_c _ _ _ => rcases hc with h | h <;> simp_all
      | tag _ h_c _ _ _ => rcases hc with h | h <;> simp_all
      | alias _ h_c _ _ => rcases hc with h | h <;> simp_all
    exact .pendingContent block sp_a sp_a ev_c ev_o
      (fun sp_mid h_ssl => by
        simpa using (h_route sp_mid []
          (TBlockNode.flowInBlock 0 .blockIn node sp_prep sp_a sp_mid [] h_sep hFlow h_ssl)))
      (GStar.nil _)
  · subst hev
    obtain ⟨sp_bs, -, hcorr_bs, h_absorb⟩ := dispatchContent_blockScalar_prod s_prep sp_prep hcorr hpeek hc h_dispatch
    have heq := ScannerSurfCorr_unique hcorr_bs hcorr'
    rw [heq] at h_absorb
    simp only [List.append_nil]
    exact .pendingContent block sp_a sp_a ev_c ev_o
      (fun sp_mid h_ssl => by simpa using h_route sp_mid [] ((h_absorb sp_mid h_ssl).elim
        (fun hl => .blockLiteral 0 .blockIn node sp_prep sp_prep sp_mid [] h_sep (TOpt.none _) hl)
        (fun hf => .blockFolded 0 .blockIn node sp_prep sp_prep sp_mid [] h_sep (TOpt.none _) hf)))
      (GStar.nil _)
  · exact .pendingProps block sp_a node sp_prep 0 ev_c ev_o ev_n h_sep
      (by simpa using TCNsProperties.anchorFirst sp_prep sp_a sp_a ev_n [] ha (TOpt.none _))
      (fun sp_m ev h => by simpa using h_route sp_m ev h)
  · exact .pendingProps block sp_a node sp_prep 0 ev_c ev_o ev_n h_sep
      (by simpa using TCNsProperties.tagFirst sp_prep sp_a sp_a ev_n [] ht (TOpt.none _))
      (fun sp_m ev h => by simpa using h_route sp_m ev h)
  · exact .pendingContent block sp_a sp_a ev_c (ev_o ++ ev_n)
      (fun sp_mid h_ssl => by simpa [List.append_assoc] using
        (h_route sp_mid ev_n (TBlockNode.flowInBlock 0 .blockIn node sp_prep sp_a sp_mid ev_n
          h_sep (TFlowNode.alias 0 .flowOut sp_prep sp_a ev_n hal) h_ssl)))
      (GStar.nil _)

/-- Content after an actual document-start marker. The route is derived
from the pre-marker trace and the real source marker, not assumed. -/
lemma content_after_docStart
    {start block marker node prepPos landing : SurfPos}
    {sc prep after : ScannerState} {c : Char} {ev_c : List Event}
    (hS : TSLYamlStream start sc block ev_c [] [])
    (hBlockCol : block.col = 0) (hComments : SSLComments block marker)
    (hCorrMarker : ScannerSurfCorr sc marker)
    (rest : List Char) (hChars : marker.chars = '-' :: '-' :: '-' :: rest)
    (hCol : marker.col = 0) (hMark : SCDirectivesEnd marker node)
    (hPre : scanNextToken_preprocess (scanDocumentStart sc) = .ok (some (prep, c)))
    (hSep : SSeparateLines 0 node prepPos)
    (arm : ContentArm prep after c prepPos landing)
    (hCorr : ScannerSurfCorr prep prepPos) (hCorrAfter : ScannerSurfCorr after landing)
    (hPeek : prep.peek? = some c) (hDepth : prep.flowLevel = 0)
    (hScan : scanNextToken_dispatchContent prep c = .ok after) :
    ∃ ev_n, TSLYamlStream start after block ev_c (.beginDocument :: ev_n) [] ∧
      TPendingNode start false block landing ev_c (.beginDocument :: ev_n) [] := by
  obtain ⟨node', hMarker, hCorrNode, hStarted⟩ :=
    hS.docStart marker hCorrMarker rest hChars hCol
  have heq : node' = node := by
    cases hMark
    cases hMarker
    rfl
  subst node'
  have hPrep : TSLYamlStream start prep block ev_c [.beginDocument] [] :=
    ⟨hS.stream, by
      rw [TPendingNode.preprocess_goOut hPre []]
      simpa using hStarted.events⟩
  obtain ⟨ev_n, hTrace, hPending⟩ := content_step_routed0 hPrep hSep arm
    hCorr hCorrAfter hPeek hDepth hScan (fun finish en hNode => by
      simpa using TLYamlStream.explicitRoute hS.stream
        (TPendingNode.SSLComments_to_GStar_prefix hBlockCol hComments)
        hMark (TAlt.left _ _ _ (TLBareDocument.mk _ _ _ hNode)))
  exact ⟨ev_n, by simpa using hTrace, by simpa using hPending⟩

/-- The actual consumer of a matched content park: preprocess, close the
document, scan `...`, preprocess again, and spend the resulting lawful route
at `directive_step_noPending`. The old-event prefix is a conclusion of the
native event fold. Neither an hRoute nor a closed predecessor is a premise. -/
lemma directive_after_pending_document
    {start block scan endLanding dirLanding : SurfPos}
    {sc endPrep ended dirPrep directed : ScannerState} {c : Char}
    {ev_c ev_o : List Event}
    (hS : TSLYamlStream start sc block ev_c ev_o [])
    (hP : TPendingNode start false block scan ev_c ev_o [])
    (hEndPre : scanNextToken_preprocess sc = .ok (some (endPrep, c)))
    (hEndComments : SSLComments scan endLanding)
    (hEndCorr : ScannerSurfCorr endPrep endLanding)
    (endRest : List Char)
    (hEndChars : endLanding.chars = '.' :: '.' :: '.' :: endRest)
    (hEndCol : endLanding.col = 0)
    (hEndScan : scanDocumentEnd endPrep = .ok ended)
    (hDirPre : scanNextToken_preprocess ended = .ok (some (dirPrep, '%')))
    (hDirComments : SSLComments ⟨endRest, 3⟩ dirLanding)
    (hDirCol : dirLanding.col = 0)
    (hDirCorr : ScannerSurfCorr dirPrep dirLanding)
    (hDirPeek : dirPrep.peek? = some '%')
    (hDirScan : scanDirective dirPrep = .ok directed) :
    ∃ stop, ScannerSurfCorr directed stop ∧
      TSLYamlStream start directed dirLanding (ev_c ++ ev_o ++ [.endDocument]) []
        (L4YAML.Proofs.Serialization.EventsOf.declaredHandle (span dirLanding stop)).toList ∧
      TPendingNode start true dirLanding stop (ev_c ++ ev_o ++ [.endDocument]) []
        (L4YAML.Proofs.Serialization.EventsOf.declaredHandle (span dirLanding stop)).toList := by
  have hClosed : TSLYamlStream start endPrep endLanding (ev_c ++ ev_o) [] [] :=
    ⟨hP.close_with_ssl hS hEndComments, by
      rw [TPendingNode.preprocess_goOut hEndPre []]
      simpa using hS.events⟩
  obtain ⟨stop, hMarker, hCorr, hEnded⟩ :=
    hClosed.docEnd endLanding hEndCorr endRest hEndChars hEndCol ended hEndScan
  have hStop : stop = (⟨endRest, 3⟩ : SurfPos) := by
    cases hMarker
    simp_all
  subst stop
  have hDirTrace : TSLYamlStream start dirPrep endLanding (ev_c ++ ev_o) [.endDocument] [] :=
    ⟨hEnded.stream, by
      rw [TPendingNode.preprocess_goOut hDirPre []]
      exact hEnded.events⟩
  exact RightWallBoundary.next_directive_after_document_end hDirTrace hMarker
    hDirComments hDirCol
    (L4YAML.Proofs.StreamAccum.sslComments_refl_of_col0 hDirCol)
    hDirCorr hDirPeek hDirScan

end L4YAML.Proofs.Serialization.TraceOf.RightWallContent
end Blanket
