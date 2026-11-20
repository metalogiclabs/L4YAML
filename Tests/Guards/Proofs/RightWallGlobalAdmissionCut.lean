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

/-!
## Source-prefix event hygiene: close the first-event obligation under
an independently checkable scanner-token restriction.

Before a YAML document has started, only streamStart, placeholders and
directive tokens may have been emitted. Named %TAG handles can be pending,
but they do not become events until a following documentStart.

This is a genuine theorem over goOut, not a one-input example. The global
loop must still prove the token restriction on its first-document branch.
-/

def PreDocumentToken (v : YamlToken) : Prop :=
  v = .streamStart ∨ v = .placeholder ∨
  (∃ a b : Nat, v = .versionDirective a b) ∨
  (∃ h p : String, v = .tagDirective h p)

lemma preDoc_tokens_emit_no_events
    (ts : List (Positioned YamlToken)) :
    ∀ (pending : List String),
      (∀ t ∈ ts, PreDocumentToken t.val) →
      (L4YAML.Proofs.Serialization.TokenEvents.goOut ts pending).1 = [] := by
  induction ts with
  | nil =>
    intro pending _
    rfl
  | cons t ts ih =>
    intro pending hall
    have ht : PreDocumentToken t.val := hall t (by simp)
    have hrest : ∀ u ∈ ts, PreDocumentToken u.val :=
      fun u hu => hall u (by simp [hu])
    rcases ht with hStart | hPh | hVersion | hTag
    · rw [L4YAML.Proofs.Serialization.TokenEvents.goOut_silent t
        (by rw [hStart]; rfl)
        (by rw [hStart]; simp)
        (by intro _ _; rw [hStart]; simp) ts pending]
      exact ih pending hrest
    · rw [L4YAML.Proofs.Serialization.TokenEvents.goOut_silent t
        (by rw [hPh]; rfl)
        (by rw [hPh]; simp)
        (by intro _ _; rw [hPh]; simp) ts pending]
      exact ih pending hrest
    · obtain ⟨major, minor, hv⟩ := hVersion
      rw [L4YAML.Proofs.Serialization.TokenEvents.goOut_silent t
        (by rw [hv]; rfl)
        (by rw [hv]; simp)
        (by intro _ _; rw [hv]; simp) ts pending]
      exact ih pending hrest
    · obtain ⟨handle, prefix, hv⟩ := hTag
      rw [L4YAML.Proofs.Serialization.TokenEvents.goOut_tagDirective
        t handle prefix hv ts pending]
      exact ih _ hrest

/-- The trace accumulator's missing first-event equation follows from
the concrete no-content-token invariant, regardless of pending handles. -/
lemma first_event_shape_of_token_history
    {sc : ScannerState} {start block : SurfPos}
    {closed openEvents : List Event} {handles : List String}
    (hT : TSLYamlStream start sc block closed openEvents handles)
    (hNoDocumentTokens :
      ∀ t ∈ sc.tokens.toList, PreDocumentToken t.val) :
    closed ++ openEvents = [] := by
  calc
    closed ++ openEvents =
      (L4YAML.Proofs.Serialization.TokenEvents.goOut sc.tokens.toList []).1 :=
        (congrArg Prod.fst hT.events).symm
    _ = [] := preDoc_tokens_emit_no_events _ _ hNoDocumentTokens

#print axioms preDoc_tokens_emit_no_events
#print axioms first_event_shape_of_token_history

#print axioms source_eligible_origin
#print axioms source_and_trace_yield_directive_route

end L4YAML.Proofs.Serialization.TraceOf.RightWallRoute
end Blanket
