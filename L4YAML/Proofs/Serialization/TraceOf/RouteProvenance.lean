/-
Copyright (c) 2026. MathGraph bounded research experiment.
YAML 1.2.2 [211] requires a *lawful document origin*, not just
the scanner's allowDirectives flag.
Exact parent source: Devin PR #359 at 57721b243c6f1bdd33e8d49c9aedd4f15e552c58,
with corrected trace grammar and conditional route helpers at d6ff3d1de.
This is experimental proof code; the global scan-loop induction is not closed.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.DocBridge
public import L4YAML.Proofs.Production.PreprocessProduction

@[expose] public section Blanket

namespace L4YAML.Proofs.Serialization.TraceOf.RightWallRoute

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.PreprocessProduction (SSLComments_to_GStar)

/-- Evidence for exactly the two lawful origins of a new directive
document in YAML [211], with its original source-to-event relation.
A mere `allowDirectives=true` does not supply this evidence. -/
def DirectiveRoute (start here : SurfPos) (ev : List Event) : Prop :=
  (ev = [] ∧ GStar SLDocumentPrefix start here) ∨
  ∃ before : SurfPos, ∃ after : SurfPos, ∃ earlier : List Event,
    ∃ suffixEvents : List Event,
    TLYamlStream start before earlier ∧
    TPlus TLDocumentSuffix before after suffixEvents ∧
    GStar SLDocumentPrefix after here ∧
    ev = earlier ++ suffixEvents

lemma initial (start : SurfPos) : DirectiveRoute start start [] :=
  Or.inl ⟨rfl, GStar.nil _⟩

private lemma star_compose {P : SurfPos → SurfPos → Prop}
    {a b c : SurfPos} (left : GStar P a b) (right : GStar P b c) :
    GStar P a c := by
  induction left generalizing c with
  | nil _ => simpa using right
  | cons s₁ s₂ s₃ h_one h_tail ih =>
    exact .cons s₁ s₂ c h_one (ih right)

/-- Source comments preserve the actual first/suffix route certificate. -/
lemma throughComments {start here next : SurfPos} {ev : List Event}
    (hRoute : DirectiveRoute start here ev) (hcol : here.col = 0)
    (hComments : SSLComments here next) : DirectiveRoute start next ev := by
  have hPrefix : GStar SLDocumentPrefix here next :=
    GStar.cons here next next
      (SLDocumentPrefix.comments here next
        (SSLComments_to_GStar here next hComments hcol))
      (GStar.nil _)
  rcases hRoute with ⟨he, hFirst⟩ | ⟨before, after, earlier, suffEv, hPrev, hSuffix, hp, he⟩
  · exact Or.inl ⟨he, star_compose hFirst hPrefix⟩
  · exact Or.inr ⟨before, after, earlier, suffEv, hPrev, hSuffix,
      star_compose hp hPrefix, he⟩

/-- A genuine document-end production plus comments seeds the second route. -/
lemma afterDocumentEnd {start before markerEnd here : SurfPos} {earlier : List Event}
    (hPrev : TLYamlStream start before earlier)
    (hMarker : SCDocumentEnd before markerEnd)
    (hComments : SSLComments markerEnd here) :
    DirectiveRoute start here (earlier ++ [.endDocument]) := by
  have hSuffix : TPlus TLDocumentSuffix before here [.endDocument] :=
    TPlus.mk _ _ _ _ [] (TLDocumentSuffix.mk before markerEnd here hMarker hComments)
      (TStar.nil _)
  exact Or.inr ⟨before, here, earlier, [.endDocument], hPrev, hSuffix,
    GStar.nil _, rfl⟩

/-- Correct annotated-stream constructor: consume only a lawful origin. -/
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

#print axioms L4YAML.Proofs.Serialization.TraceOf.RightWallRoute.initial
#print axioms L4YAML.Proofs.Serialization.TraceOf.RightWallRoute.throughComments
#print axioms L4YAML.Proofs.Serialization.TraceOf.RightWallRoute.afterDocumentEnd
#print axioms L4YAML.Proofs.Serialization.TraceOf.RightWallRoute.closeDirective

end L4YAML.Proofs.Serialization.TraceOf.RightWallRoute
end Blanket
