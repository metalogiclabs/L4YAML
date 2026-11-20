module
public import L4YAML.Proofs.Serialization.TokenEvents
@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
open L4YAML
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
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
    by_cases hDir : ∃ handle pfx, t.val = .tagDirective handle pfx
    · rcases hDir with ⟨handle, pfx, hTag⟩
      have hTail := ih (if isNamedHandle handle then handle :: p else p) hRest
      simp [goOut, hTag, hTail]
    · have hNoDir : ∀ handle pfx, t.val ≠ .tagDirective handle pfx := by
        intro handle pfx hTag
        exact hDir ⟨handle, pfx, hTag⟩
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


#print axioms no_events_of_nonemitting
#print axioms end_marker_final_event
end L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
end Blanket
