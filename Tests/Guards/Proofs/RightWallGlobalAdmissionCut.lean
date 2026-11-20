/-
MathGraph Right-Wall: S/T global admissibility cut.
Source: correct document-stream continuation on Devin PR #359 lineage,
exact parent ba12de17ff1339b6711fddd15f27b183d3ab7509.
Scope: a *conditional* source-to-event bridge, never a claim that the
whole scanner loop satisfies its premises.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.StreamBridge

@[expose] public section Blanket

namespace L4YAML.Proofs.Serialization.TraceOf.RightWallRoute

open L4YAML L4YAML.Surface L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge

/-!
This is the original S-side admission distinction, now exposed as
the source *shape* needed by the T-side DirectiveRoute. Proof is
independent of scanner tokenEvents; it cannot establish event equality.
-/
lemma source_eligible_origin
    {sc : ScannerState} {start block scan : SurfPos}
    (hP : PendingNode sc false start block scan)
    (hNoFlow : sc.inFlow = false)
    (hAllow : sc.allowDirectives = true) :
    GStar SLDocumentPrefix start block ∨ SCDocumentEnd block scan := by
  cases hP with
  | noPending _ _ h_col _ h_nodoc =>
    exact Or.inl (h_nodoc hNoFlow)
  | pendingDocEnd _ _ _ _ h_marker _ _ =>
    exact Or.inr h_marker
  | pendingContent =>
    exact absurd hAllow (by simp [show sc.allowDirectives = false from by assumption])
  | pendingProps =>
    exact absurd hAllow (by simp [show sc.allowDirectives = false from by assumption])
  | pendingDocStart =>
    exact absurd hAllow (by simp [show sc.allowDirectives = false from by assumption])
  | pendingFlow =>
    exact absurd hAllow (by simp [show sc.allowDirectives = false from by assumption])
  | pendingBlockContent =>
    exact absurd hAllow (by simp [show sc.allowDirectives = false from by assumption])
  | pendingBlock =>
    exact absurd hAllow (by simp [show sc.allowDirectives = false from by assumption])
  | pendingMapValue =>
    exact absurd hAllow (by simp [show sc.allowDirectives = false from by assumption])

/-!
An exact S→T bridge for a *paired* source park and trace accumulator.

The two additional hypotheses expose the unproved correspondence:
* a source-only first-doc prefix has no accumulated event list;
* a successful document-end source park has exactly the pending end event.

Neither is a trivial consequence of allowDirectives: they must be
established by the global paired-scanner induction, not assumed in the
final 7.7 theorem.
-/
lemma source_and_trace_yield_directive_route
    {sc : ScannerState} {start block scan : SurfPos}
    {closed openEvents : List Event} {handles : List String}
    (hP : PendingNode sc false start block scan)
    (hT : TSLYamlStream start sc block closed openEvents handles)
    (hNoFlow : sc.inFlow = false)
    (hAllow : sc.allowDirectives = true)
    (hFirstEvents : GStar SLDocumentPrefix start block →
      closed ++ openEvents = [])
    (hSuffixEvents : SCDocumentEnd block scan →
      openEvents = [.endDocument]) :
    ∀ next, SSLComments scan next →
      DirectiveRoute start next (closed ++ openEvents) := by
  cases hP with
  | noPending _ _ h_col _ h_nodoc =>
    intro next hComments
    have hPrefix := h_nodoc hNoFlow
    have hCol0 : block.col = 0 :=
      h_col.resolve_right (by simp [hNoFlow])
    exact throughComments (Or.inl ⟨hFirstEvents hPrefix, hPrefix⟩) hCol0 hComments
  | pendingDocEnd _ _ _ _ h_marker _ _ =>
    intro next hComments
    have hEnd := hSuffixEvents h_marker
    simpa [hEnd] using afterDocumentEnd hT.stream h_marker hComments
  | pendingContent =>
    exact False.elim (absurd hAllow (by simp [show sc.allowDirectives = false from by assumption]))
  | pendingProps =>
    exact False.elim (absurd hAllow (by simp [show sc.allowDirectives = false from by assumption]))
  | pendingDocStart =>
    exact False.elim (absurd hAllow (by simp [show sc.allowDirectives = false from by assumption]))
  | pendingFlow =>
    exact False.elim (absurd hAllow (by simp [show sc.allowDirectives = false from by assumption]))
  | pendingBlockContent =>
    exact False.elim (absurd hAllow (by simp [show sc.allowDirectives = false from by assumption]))
  | pendingBlock =>
    exact False.elim (absurd hAllow (by simp [show sc.allowDirectives = false from by assumption]))
  | pendingMapValue =>
    exact False.elim (absurd hAllow (by simp [show sc.allowDirectives = false from by assumption]))

#print axioms source_eligible_origin
#print axioms source_and_trace_yield_directive_route

end L4YAML.Proofs.Serialization.TraceOf.RightWallRoute
end Blanket
