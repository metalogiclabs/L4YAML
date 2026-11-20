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


/-! A single proposition for the scanner-reachability induction:
either no event-producing token has appeared, or the last real document
marker is documentEnd and every subsequent token is non-emitting.
This is a TOKEN-HISTORY condition, not full source grammar conformance.
-/
def EligibleHistory (ts : List (Positioned YamlToken)) : Prop :=
  (∀ t ∈ ts, NonEmitting t.val) ∨
  ∃ pre : List (Positioned YamlToken),
    ∃ post : List (Positioned YamlToken),
    ∃ marker : Positioned YamlToken,
      ts = pre ++ marker :: post ∧
      marker.val = .documentEnd ∧
      ∀ t ∈ post, NonEmitting t.val

/-- Eligible token histories satisfy the universally checked observation
    that P139 sampled at actual scanner states. -/
lemma eligibleHistory_event_shape (ts : List (Positioned YamlToken))
    (h : EligibleHistory ts) :
    (goOut ts []).1 = [] ∨
    ∃ pre : List (Positioned YamlToken),
      (goOut ts []).1 = (goOut pre []).1 ++ [.endDocument] := by
  rcases h with hNo | ⟨pre, post, marker, hEq, hMarker, hPost⟩
  · exact Or.inl (no_events_of_nonemitting ts [] hNo)
  · right
    refine ⟨pre, ?_⟩
    rw [hEq]
    exact end_marker_final_event pre post marker [] hMarker hPost

/-- Scanning a directive (or a semantically silent token) cannot destroy
    the previously established first-document/post-suffix origin. -/
lemma eligibleHistory_append_nonemitting
    (ts : List (Positioned YamlToken)) (t : Positioned YamlToken)
    (h : EligibleHistory ts) (ht : NonEmitting t.val) :
    EligibleHistory (ts ++ [t]) := by
  rcases h with hNo | ⟨pre, post, marker, hEq, hMark, hPost⟩
  · left
    intro u hu
    rcases List.mem_append.mp hu with ha | hb
    · exact hNo u ha
    · have heq : u = t := by simpa using hb
      subst u
      exact ht
  · right
    refine ⟨pre, post ++ [t], marker, ?_, hMark, ?_⟩
    · rw [hEq]
      simp [List.append_assoc]
    · intro u hu
      rcases List.mem_append.mp hu with ha | hb
      · exact hPost u ha
      · have heq : u = t := by simpa using hb
        subst u
        exact ht

/-- Successful scanning of a literal document-end marker establishes
    the post-suffix branch, independently of all earlier token events. -/
lemma eligibleHistory_append_docEnd
    (ts : List (Positioned YamlToken)) (marker : Positioned YamlToken)
    (h : marker.val = .documentEnd) :
    EligibleHistory (ts ++ [marker]) := by
  exact Or.inr ⟨ts, [], marker, by simp, h, by simp⟩

#print axioms eligibleHistory_event_shape
#print axioms eligibleHistory_append_nonemitting
#print axioms eligibleHistory_append_docEnd

#print axioms no_events_of_nonemitting
#print axioms end_marker_final_event
end L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
end Blanket
