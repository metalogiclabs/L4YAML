/-
MathGraph Right-Wall proof-route carrier experiment.
Parent: Devin PR #359 source 57721b243c6f1bdd33e8d49c9aedd4f15e552c58
and source-corrected diagnostic head d6ff3d1de0d02e1edbb4eb9b88fa3478ca76684d.
No production repair and no claim of complete scan_trace.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.StreamBridge

@[expose] public section Blanket

namespace L4YAML.Proofs.Serialization.TraceOf.RightWallRoute

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.EventsOf (declaredHandle)

/-!
Proof-carrying directive provenance. Exactly two legal origins for the
next directive document: before any document, or after an explicit ...
suffix. A final prefix may carry comments/blank lines. This is NOT
equivalent to the scanner's allowDirectives Boolean on arbitrary states.
-/
def DirectiveRoute (start here : SurfPos) (ev : List Event) : Prop :=
  (ev = [] ∧ GStar SLDocumentPrefix start here) ∨
  ∃ before : SurfPos, ∃ after : SurfPos, ∃ earlier : List Event,
    ∃ suffixEvents : List Event,
    TLYamlStream start before earlier ∧
    TPlus TLDocumentSuffix before after suffixEvents ∧
    GStar SLDocumentPrefix after here ∧
    ev = earlier ++ suffixEvents

/-- Empty initial stream seeds the *first document* route. -/
lemma initial (start : SurfPos) : DirectiveRoute start start [] :=
  Or.inl ⟨rfl, GStar.nil _⟩

/-- Star composition, proved here rather than assuming an external transport. -/
private lemma star_compose {P : SurfPos → SurfPos → Prop}
    {a b c : SurfPos} (left : GStar P a b) (right : GStar P b c) :
    GStar P a c := by
  induction left generalizing c with
  | nil _ => simpa using right
  | cons s₁ s₂ s₃ h_one h_tail ih =>
    exact .cons s₁ s₂ c h_one (ih right)

/-- A separator/comment prefix does not lose the route's provenance. -/
lemma throughComments {start here next : SurfPos} {ev : List Event}
    (hRoute : DirectiveRoute start here ev) (hcol : here.col = 0)
    (hComments : SSLComments here next) : DirectiveRoute start next ev := by
  have hPrefix : GStar SLDocumentPrefix here next :=
    TPendingNode.SSLComments_to_GStar_prefix hcol hComments
  rcases hRoute with ⟨he, hFirst⟩ | ⟨before, after, earlier, suffEv, hPrev, hSuffix, hp, he⟩
  · exact Or.inl ⟨he, star_compose hFirst hPrefix⟩
  · exact Or.inr ⟨before, after, earlier, suffEv, hPrev, hSuffix,
      star_compose hp hPrefix, he⟩

/-- A genuine parsed end marker + its suffix comments seeds the SECOND route. -/
lemma afterDocumentEnd {start before markerEnd here : SurfPos} {earlier : List Event}
    (hPrev : TLYamlStream start before earlier)
    (hMarker : SCDocumentEnd before markerEnd)
    (hComments : SSLComments markerEnd here) :
    DirectiveRoute start here (earlier ++ [.endDocument]) := by
  have hSuffix : TPlus TLDocumentSuffix before here [.endDocument] :=
    TPlus.mk _ _ _ _ [] (TLDocumentSuffix.mk before markerEnd here hMarker hComments)
      (TStar.nil _)
  exact Or.inr ⟨before, here, earlier, [.endDocument],
    hPrev, hSuffix, GStar.nil _, rfl⟩

/-- A directive document can be closed under the corrected [211] grammar
    only when the caller carries one of the lawful route certificates. -/
lemma closeDirective {start here directiveEnd markerEnd finish : SurfPos}
    {ev ed eb : List Event}
    (hRoute : DirectiveRoute start here ev)
    (hDir : TPlus TLDirective here directiveEnd ed)
    (hMark : SCDirectivesEnd directiveEnd markerEnd)
    (hBody : TLExplicitBody markerEnd finish eb) :
    TLYamlStream start finish (ev ++ (.beginDocument :: ed ++ eb)) := by
  rcases hRoute with ⟨he, hFirst⟩ |
      ⟨before, after, earlier, suffixEvents, hPrev, hSuffix, hPrefix, he⟩
  · subst ev
    simpa using TLYamlStream.directiveFirstRoute hFirst hDir hMark hBody
  · rw [he]
    simpa [List.append_assoc] using
      TLYamlStream.directiveAfterSuffixRoute hPrev hSuffix hPrefix hDir hMark hBody

/-- The old docStart_step_run consumer, now with a *necessary* extra premise.
    This version has no silent use of an arbitrary-previous-stream route.
    The source-to-DirectiveRoute invariant is the remaining global obligation. -/
lemma docStart_step_run_withRoute
    {sp_start sp_block sp_scan sp_prep : SurfPos} {s_prep : ScannerState}
    {ev_c : List Event} {p : List String}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c [] p)
    (hRoute : DirectiveRoute sp_start sp_block ev_c)
    (h_acc : ∀ sp_mid, SSLComments sp_scan sp_mid →
      TPlus TLDirective sp_block sp_mid (p.reverse.map .declareTag))
    (h_pre : SSLComments sp_scan sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep)
    (rest : List Char) (hchars : sp_prep.chars = '-' :: '-' :: '-' :: rest)
    (hcol : sp_prep.col = 0) :
    ∃ sp', ScannerSurfCorr (scanDocumentStart s_prep) sp' ∧
      TSLYamlStream sp_start (scanDocumentStart s_prep) sp_block ev_c
        (.beginDocument :: p.reverse.map .declareTag) [] ∧
      TPendingNode sp_start false sp_block sp' ev_c
        (.beginDocument :: p.reverse.map .declareTag) [] := by
  obtain ⟨sp', hde, hcorr', hS'⟩ := hS.docStart sp_prep hcorr rest hchars hcol
  refine ⟨sp', hcorr', by simpa using hS', ?_⟩
  exact TPendingNode.pendingDocStart _ _ _ _ fun sp_end eb hb => by
    simpa using closeDirective hRoute (h_acc sp_prep h_pre) hde hb

/-! ## Native transition correspondence (conditional at the entry state) -/

/-- The actual scanDocumentEnd transition supplies a lawful post-suffix
    route certificate once its trailing comments have been read. -/
lemma scanDocumentEnd_producesRoute
    {start before : SurfPos} {sc sc' : ScannerState} {closed : List Event}
    (hS : TSLYamlStream start sc before closed [] [])
    (hcorr : ScannerSurfCorr sc before)
    (rest : List Char) (hchars : before.chars = '.' :: '.' :: '.' :: rest)
    (hcol : before.col = 0) (hok : scanDocumentEnd sc = .ok sc') :
    ∃ markerEnd, ScannerSurfCorr sc' markerEnd ∧
      ∀ next, SSLComments markerEnd next →
        DirectiveRoute start next (closed ++ [.endDocument]) := by
  obtain ⟨markerEnd, hMarker, hcorr', _⟩ :=
    hS.docEnd before hcorr rest hchars hcol sc' hok
  exact ⟨markerEnd, hcorr', fun next hComments =>
    afterDocumentEnd hS.stream hMarker hComments⟩

/-- The first "%" of a directive run preserves its lawful route
    while opening the annotated pending-directive park. -/
lemma directive_step_noPending_preservesRoute
    {start sp sp_prep : SurfPos} {sc sc' : ScannerState}
    {closed : List Event}
    (hS : TSLYamlStream start sc sp closed [] [])
    (hRoute : DirectiveRoute start sp closed) (hcol : sp.col = 0)
    (hpre : SSLComments sp sp_prep)
    (hcorr : ScannerSurfCorr sc sp_prep) (hpeek : sc.peek? = some '%')
    (hok : scanDirective sc = .ok sc') :
    ∃ sp', ScannerSurfCorr sc' sp' ∧
      TSLYamlStream start sc' sp_prep closed []
        (declaredHandle (span sp_prep sp')).toList ∧
      DirectiveRoute start sp_prep closed ∧
      TPendingNode start true sp_prep sp' closed []
        (declaredHandle (span sp_prep sp')).toList := by
  obtain ⟨sp', hcorr', hS', hPending⟩ :=
    TPendingNode.directive_step_noPending hS hcol hpre hcorr hpeek hok
  exact ⟨sp', hcorr', hS', throughComments hRoute hcol hpre, hPending⟩

/-- Further directives extend the run but leave the closed-stream route
    unchanged. No new first/suffix assumption is invented by the step. -/
lemma directive_step_run_preservesRoute
    {start block scan prep : SurfPos} {sc sc' : ScannerState}
    {closed : List Event} {p : List String}
    (hS : TSLYamlStream start sc block closed [] p)
    (hRoute : DirectiveRoute start block closed)
    (h_acc : ∀ middle, SSLComments scan middle →
      TPlus TLDirective block middle (p.reverse.map .declareTag))
    (hpre : SSLComments scan prep)
    (hcorr : ScannerSurfCorr sc prep) (hpeek : sc.peek? = some '%')
    (hok : scanDirective sc = .ok sc') :
    ∃ sp', ScannerSurfCorr sc' sp' ∧
      TSLYamlStream start sc' block closed []
        ((declaredHandle (span prep sp')).toList ++ p) ∧
      DirectiveRoute start block closed ∧
      TPendingNode start true block sp' closed []
        ((declaredHandle (span prep sp')).toList ++ p) := by
  obtain ⟨sp', hcorr', hS', hPending⟩ :=
    TPendingNode.directive_step_run hS h_acc hpre hcorr hpeek hok
  exact ⟨sp', hcorr', hS', hRoute, hPending⟩

#print axioms scanDocumentEnd_producesRoute
#print axioms directive_step_noPending_preservesRoute
#print axioms directive_step_run_preservesRoute

#print axioms initial
#print axioms throughComments
#print axioms afterDocumentEnd
#print axioms closeDirective
#print axioms docStart_step_run_withRoute

end L4YAML.Proofs.Serialization.TraceOf.RightWallRoute

end Blanket
