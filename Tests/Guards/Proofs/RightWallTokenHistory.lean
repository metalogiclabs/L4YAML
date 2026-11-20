/-
MathGraph Right-Wall: universal token-history bridge (bounded scope).
Pinned to exact verified global admission cut c311255f960d715da5dcbef0a3fc7bb8c6cc7f58,
originating from Devin PR #359 source plus YAML [211] corrected grammar.
Not a global scanLoop proof; the source invariant connecting scanner state to
NonEmitting tokens and the prefix-event alignment remain explicit.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.StreamBridge

@[expose] public section Blanket

namespace L4YAML.Proofs.Serialization.TraceOf.RightWallHistory

open L4YAML
open L4YAML.Scanner
open L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge

/-- Token classes whose processing cannot directly emit a serialization
    event. A %TAG directive is allowed here: its handles are held pending,
    not emitted before the following documentStart. -/
def NonEmitting (v : YamlToken) : Prop :=
  tokenEvent v = none ∧ v ≠ .documentStart

/-- All token lists built exclusively from non-emitting tokens have
    no emitted events, regardless of the pending named-tag handles.
    This is a genuine universally quantified algebraic fact about goOut. -/
lemma no_events_of_nonemitting
    (ts : List (Positioned YamlToken)) (p : List String)
    (h : ∀ t ∈ ts, NonEmitting t.val) :
    (goOut ts p).1 = [] := by
  induction ts generalizing p with
  | nil => rfl
  | cons t rest ih =>
    have ht : NonEmitting t.val := h t (by simp)
    have hRest : ∀ u ∈ rest, NonEmitting u.val := by
      intro u hu
      exact h u (by simp [hu])
    by_cases hDir : ∃ handle prefix, t.val = .tagDirective handle prefix
    · rcases hDir with ⟨handle, prefix, hTag⟩
      have hTail := ih (if isNamedHandle handle then handle :: p else p) hRest
      simp [goOut, hTag, hTail]
    · have hNoDir : ∀ handle prefix, t.val ≠ .tagDirective handle prefix := by
        intro handle prefix hTag
        exact hDir ⟨handle, prefix, hTag⟩
      rw [goOut_silent t ht.1 ht.2 hNoDir rest p]
      exact ih p hRest

/-- A real documentEnd followed only by non-emitting tokens produces
    exactly one final endDocument event after the preceding event stream.
    This is independent of scanner sampling and holds for arbitrary lengths. -/
lemma end_marker_final_event
    (pre post : List (Positioned YamlToken)) (marker : Positioned YamlToken)
    (p : List String)
    (hMarker : marker.val = .documentEnd)
    (hPost : ∀ t ∈ post, NonEmitting t.val) :
    (goOut (pre ++ marker :: post) p).1 =
      (goOut pre p).1 ++ [.endDocument] := by
  have hEnd : (goOut (marker :: post) (goOut pre p).2).1 = [.endDocument] := by
    rw [goOut_documentEnd marker hMarker]
    simp [no_events_of_nonemitting post (goOut pre p).2 hPost]
  rw [goOut_append]
  simp only [Prod.fst]
  rw [hEnd]

/-- First document: if the scanner-token history is non-emitting,
    then any TSLYamlStream that identifies its closed events with goOut
    and has no open events or handles must have an empty closed trace.
    This *discharges* the first-event shape condition in the admission cut,
    conditional only on the token-history invariant. -/
lemma first_park_closed_events_empty
    {start block : SurfPos} {sc : ScannerState} {closed : List Event}
    (hT : TSLYamlStream start sc block closed [] [])
    (hNoEvents : ∀ t ∈ sc.tokens.toList, NonEmitting t.val) :
    closed = [] := by
  have hNone := no_events_of_nonemitting sc.tokens.toList [] hNoEvents
  have hEq : (goOut sc.tokens.toList []).1 = closed := by
    simpa using congrArg Prod.fst hT.events
  exact hEq.symm.trans hNone

/-- The corresponding post-suffix shape, once a previous-token prefix
    has already been related to the closed trace. This exposes the exact
    single remaining correspondence obligation at this source boundary. -/
lemma post_suffix_open_events
    {start block : SurfPos} {sc : ScannerState}
    {closed openEvents : List Event}
    (hT : TSLYamlStream start sc block closed openEvents [])
    (pre post : List (Positioned YamlToken))
    (marker : Positioned YamlToken)
    (hTokens : sc.tokens.toList = pre ++ marker :: post)
    (hMarker : marker.val = .documentEnd)
    (hPost : ∀ t ∈ post, NonEmitting t.val)
    (hPrefix : (goOut pre []).1 = closed) :
    openEvents = [.endDocument] := by
  have hEq : (goOut sc.tokens.toList []).1 = closed ++ openEvents := by
    simpa using congrArg Prod.fst hT.events
  rw [hTokens, end_marker_final_event pre post marker [] hMarker hPost, hPrefix] at hEq
  exact List.append_cancel_left hEq.symm

#print axioms no_events_of_nonemitting
#print axioms end_marker_final_event
#print axioms first_park_closed_events_empty
#print axioms post_suffix_open_events

end L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
end Blanket
