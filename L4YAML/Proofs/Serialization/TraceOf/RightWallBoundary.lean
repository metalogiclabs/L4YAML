/-
Copyright (c) 2026. MathGraph bounded research experiment.
Two event/source-synchronized route consumers, without a free hRoute premise.
This file establishes the directive transitions only, not global scan_trace.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed

@[expose] public section Blanket

namespace L4YAML.Proofs.Serialization.TraceOf.RightWallBoundary

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge (ScannerSurfCorr)
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge (TPendingNode)
open L4YAML.Proofs.Serialization.TraceOf.RightWallRoute (DirectiveRoute)
open L4YAML.Proofs.Serialization.EventsOf (declaredHandle)

/-- At a real `...` boundary, the already certified previous trace and the
    scanned source marker create BOTH the new closed trace and its future
    directive-origin certificate. The event equality comes from the existing
    `TSLYamlStream` token-to-event coupling, not a caller-provided hRoute. -/
theorem after_document_end_rebases_both
    {start before markerEnd here : SurfPos} {sc : ScannerState}
    {ev : List Event}
    (hClosed : TSLYamlStream start sc before ev [.endDocument] [])
    (hMarker : SCDocumentEnd before markerEnd)
    (hComments : SSLComments markerEnd here) :
    TSLYamlStream start sc here (ev ++ [.endDocument]) [] [] ∧
      DirectiveRoute start here (ev ++ [.endDocument]) := by
  refine ⟨⟨TLYamlStream.closeSuffix hClosed.stream hMarker hComments, ?_⟩,
    L4YAML.Proofs.Serialization.TraceOf.RightWallRoute.afterDocumentEnd
      hClosed.stream hMarker hComments⟩
  simpa using hClosed.events

/-- The first directive consumes the actual initial/source prefix rather
    than an unqualified stream continuation.  The caller has to produce
    `hPrefix` from the real source-level noPending park. -/
theorem first_directive_from_prefix
    {start park landing : SurfPos} {s_prep s' : ScannerState}
    (hClosed : TSLYamlStream start s_prep park [] [] [])
    (hPrefix : GStar SLDocumentPrefix start park)
    (hcol : park.col = 0)
    (hpre : SSLComments park landing)
    (hcorr : ScannerSurfCorr s_prep landing)
    (hpeek : s_prep.peek? = some '%')
    (hok : scanDirective s_prep = .ok s') :
    ∃ stop, ScannerSurfCorr s' stop ∧
      TSLYamlStream start s' landing [] [] (declaredHandle (span landing stop)).toList ∧
      TPendingNode start true landing stop [] []
        (declaredHandle (span landing stop)).toList := by
  exact TPendingNode.directive_step_noPending hClosed
    (Or.inl ⟨rfl, hPrefix⟩) hcol hpre hcorr hpeek hok

/-- A later directive can start only after a source-proven document suffix.
    No input to this theorem is named or typed as an unconstrained hRoute. -/
theorem next_directive_after_document_end
    {start before markerEnd park landing : SurfPos} {s_prep s' : ScannerState}
    {ev : List Event}
    (hClosed : TSLYamlStream start s_prep before ev [.endDocument] [])
    (hMarker : SCDocumentEnd before markerEnd)
    (hComments : SSLComments markerEnd park)
    (hcol : park.col = 0)
    (hpre : SSLComments park landing)
    (hcorr : ScannerSurfCorr s_prep landing)
    (hpeek : s_prep.peek? = some '%')
    (hok : scanDirective s_prep = .ok s') :
    ∃ stop, ScannerSurfCorr s' stop ∧
      TSLYamlStream start s' landing (ev ++ [.endDocument]) []
        (declaredHandle (span landing stop)).toList ∧
      TPendingNode start true landing stop (ev ++ [.endDocument]) []
        (declaredHandle (span landing stop)).toList := by
  obtain ⟨hStream, hRoute⟩ :=
    after_document_end_rebases_both hClosed hMarker hComments
  exact TPendingNode.directive_step_noPending hStream hRoute
    hcol hpre hcorr hpeek hok

/-- Once a directive run exists, the previous pending node itself supplies
    the legally-originated route and exact accumulated events. -/
theorem next_directive_in_existing_run
    {start park scanned landing : SurfPos} {s_prep s' : ScannerState}
    {ev : List Event} {handles : List String}
    (hClosed : TSLYamlStream start s_prep park ev [] handles)
    (hPending : TPendingNode start true park scanned ev [] handles)
    (hpre : SSLComments scanned landing)
    (hcorr : ScannerSurfCorr s_prep landing)
    (hpeek : s_prep.peek? = some '%')
    (hok : scanDirective s_prep = .ok s') :
    ∃ stop, ScannerSurfCorr s' stop ∧
      TSLYamlStream start s' park ev []
        ((declaredHandle (span landing stop)).toList ++ handles) ∧
      TPendingNode start true park stop ev []
        ((declaredHandle (span landing stop)).toList ++ handles) := by
  cases hPending with
  | pendingDirective _ _ _ _ hOrigin hAccumulator =>
    exact TPendingNode.directive_step_run hClosed hOrigin hAccumulator
      hpre hcorr hpeek hok

#print axioms after_document_end_rebases_both
#print axioms first_directive_from_prefix
#print axioms next_directive_after_document_end
#print axioms next_directive_in_existing_run

end L4YAML.Proofs.Serialization.TraceOf.RightWallBoundary
end Blanket
