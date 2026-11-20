/- Capstone 7.7 / S3: actual key reservations and the native colon event
fold. Reuse the scanner's verified placeholder invariant on every reachable
prefix; do not assume an event-prefix equality at the mapping producer. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.Reachability
public import L4YAML.Proofs.Production.ScannerPlainScalarValid
import all L4YAML.Proofs.Serialization.TokenEvents
@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.KeyEvents
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
open L4YAML.Proofs.Serialization.SerializationWellFormed

/-- The existing reservation preservation lemmas, folded through the
actual successful scanner step without importing unrelated scalar validity. -/
lemma placeholder_step {s after : ScannerState} (h : AllKeysPlaceholderInv s)
    (edge : scanNextToken s = .ok (some after)) : AllKeysPlaceholderInv after := by
  unfold scanNextToken at edge
  simp only [bind, Except.bind, pure, Except.pure] at edge
  split at edge <;> (try (simp at edge; done))
  split at edge <;> (try (simp at edge; done))
  rename_i prep ch pre
  have hp := preprocess_preserves_AllKeysPlaceholderInv s prep ch pre h
  split at edge <;> (try (simp at edge; done))
  split at edge <;> (try (simp at edge; done))
  split at edge <;> (try (simp at edge; done))
  split at edge
  · simp only [Except.ok.injEq, Option.some.injEq] at edge
    subst edge
    exact dispatchStructural_preserves_AllKeysPlaceholderInv prep ch hp _ (by assumption)
  · have had : AllKeysPlaceholderInv (if prep.allowDirectives then
        { prep with allowDirectives := false, documentEverStarted := true } else prep) := by
      split <;> exact hp
    split at edge <;> (try (simp at edge; done))
    split at edge <;> (try (simp at edge; done))
    split at edge <;> (try (simp at edge; done))
    split at edge
    · simp only [Except.ok.injEq, Option.some.injEq] at edge
      subst edge
      exact dispatchFlowIndicators_preserves_AllKeysPlaceholderInv _ ch had _ (by assumption)
    · split at edge <;> (try (simp at edge; done))
      split at edge
      · simp only [Except.ok.injEq, Option.some.injEq] at edge
        subst edge
        exact dispatchBlockIndicators_preserves_AllKeysPlaceholderInv _ ch had _ (by assumption)
      · split at edge <;> (try (simp at edge; done))
        split at edge <;> (try (simp at edge; done))
        simp only [Except.ok.injEq, Option.some.injEq] at edge
        subst edge
        exact dispatchContent_preserves_AllKeysPlaceholderInv _ ch had _ (by assumption)

lemma reachable_key_reservations {input : String} {s : ScannerState}
    (reach : ScannerReachable input s) : AllKeysPlaceholderInv s := by
  induction reach with
  | seed =>
    have hp : (scanSeed input).simpleKey.possible = false := by
      unfold scanSeed
      dsimp only
      split
      · rw [consumeBOM_preserves_simpleKey]; rfl
      · rfl
    have hs : (scanSeed input).simpleKeyStack.size = 0 := by
      unfold scanSeed
      dsimp only
      split
      · rw [consumeBOM_preserves_simpleKeyStack]; rfl
      · rfl
    exact ⟨fun h => Bool.noConfusion (hp.symm.trans h),
      fun j hj => by rw [hs] at hj; omega,
      fun h => Bool.noConfusion (hp.symm.trans h),
      fun j hj => by rw [hs] at hj; omega⟩
  | step _ edge ih => exact placeholder_step ih edge

def Silent (v : YamlToken) : Prop := tokenEvent v = none ∧
  v ≠ .documentStart ∧ ∀ h pfx, v ≠ .tagDirective h pfx

lemma goOut_set_silent {ts : List (Positioned YamlToken)} {i : Nat}
    {new : Positioned YamlToken} (hn : Silent new.val)
    (ho : ∀ old, ts[i]? = some old → Silent old.val) :
    ∀ p, goOut (ts.set i new) p = goOut ts p := by
  induction ts generalizing i with
  | nil => intro p; simp
  | cons t rest ih =>
    cases i with
    | zero =>
      intro p
      have ht := ho t rfl
      simp only [List.set_cons_zero]
      rw [goOut_silent new hn.1 hn.2.1 hn.2.2,
        goOut_silent t ht.1 ht.2.1 ht.2.2]
    | succ i =>
      have hr := ih (i := i) (fun old h => ho old (by simpa using h))
      intro p
      obtain ⟨pos, val, stop⟩ := t
      cases val <;> simp_all [goOut]
      all_goals split <;> simp_all

lemma array_set_silent {ts : Array (Positioned YamlToken)} {i : Nat}
    {new : Positioned YamlToken} (hn : Silent new.val)
    (ho : ∀ old, ts[i]? = some old → Silent old.val) (p : List String) :
    goOut (ts.setIfInBounds i new).toList p = goOut ts.toList p := by
  rw [Array.toList_setIfInBounds]
  exact goOut_set_silent hn (by simpa using ho) p

lemma placeholder_slot_silent {ts : Array (Positioned YamlToken)} {i : Nat}
    (h : ∀ hi : i < ts.size, (ts[i]'hi).val = .placeholder) :
    ∀ old, ts[i]? = some old → Silent old.val := by
  intro old hold
  by_cases hi : i < ts.size
  · rw [Array.getElem?_eq_getElem hi] at hold
    cases Option.some.inj hold
    simp [Silent, h hi, tokenEvent]
  · have hx : ts[i]? = none := Array.getElem?_eq_none (by omega)
    rw [hx] at hold
    cases hold

lemma goOut_push_silent (ts : Array (Positioned YamlToken)) (new : Positioned YamlToken)
    (hn : Silent new.val) (p : List String) :
    goOut (ts.push new).toList p = goOut ts.toList p := by
  rw [Array.toList_push, goOut_append,
    goOut_silent new hn.1 hn.2.1 hn.2.2, goOut_nil]
  simp

lemma pushMappingIndent_goOut (s : ScannerState) (col : Int) (p : List String) :
    goOut (pushMappingIndent s col).tokens.toList p = goOut s.tokens.toList p := by
  unfold pushMappingIndent
  split
  · exact goOut_push_silent _ _ (by simp [Silent, tokenEvent]) p
  · rfl

lemma scanValuePrepare_goOut {s : ScannerState} (h : SimpleKeyPlaceholderInv s)
    (p : List String) :
    goOut (scanValuePrepare s).tokens.toList p = goOut s.tokens.toList p := by
  unfold scanValuePrepare
  split
  · rename_i hp
    obtain ⟨_, _, hfirst, hsecond⟩ := h hp
    have h1 := placeholder_slot_silent hfirst
    have h2 := placeholder_slot_silent hsecond
    split
    · split
      · change goOut ((s.tokens.setIfInBounds s.simpleKey.tokenIndex _).setIfInBounds
          (s.simpleKey.tokenIndex + 1) _).toList p = _
        rw [array_set_silent (by simp [Silent, tokenEvent]) (by
          intro old hold
          rw [Array.getElem?_setIfInBounds_ne (by omega)] at hold
          exact h2 old hold) p,
          array_set_silent (by simp [Silent, tokenEvent]) h1 p]
      · exact array_set_silent (by simp [Silent, tokenEvent]) h2 p
    · exact array_set_silent (by simp [Silent, tokenEvent]) h2 p
  · split
    · rfl
    · split
      · exact pushMappingIndent_goOut _ _ p
      · rfl

lemma scanValue_tokens {s after : ScannerState} (edge : scanValue s = .ok after) :
    after.tokens = (scanValuePrepare (scanValueClearKey s)).tokens.push
      ⟨(scanValuePrepare (scanValueClearKey s)).currentPos, .value,
        (scanValuePrepare (scanValueClearKey s)).currentPos⟩ := by
  unfold scanValue at edge
  simp only [bind, Except.bind] at edge
  split at edge <;> (try (simp at edge; done))
  split at edge <;> (try (simp at edge; done))
  split at edge <;> (try (simp at edge; done))
  simp only [Except.ok.injEq] at edge
  subst edge
  rw [advance_preserves_tokens]
  rfl

lemma scanValue_goOut {s after : ScannerState} (h : SimpleKeyPlaceholderInv s)
    (edge : scanValue s = .ok after) (p : List String) :
    goOut after.tokens.toList p = goOut s.tokens.toList p := by
  have ht : (scanValueClearKey s).tokens = s.tokens :=
    (L4YAML.Proofs.StreamAccum.scanValueClearKey_fields s).2.2.2.2.2.2.2.1
  have hc : SimpleKeyPlaceholderInv (scanValueClearKey s) := by
    intro hp
    have hk := L4YAML.Proofs.StreamAccum.scanValueClearKey_keeps s hp
    have hp0 : s.simpleKey.possible = true := by rw [← hk]; exact hp
    simpa [hk, ht] using h hp0
  rw [scanValue_tokens edge,
    goOut_push_silent _ _ (by simp [Silent, tokenEvent]), scanValuePrepare_goOut hc, ht]

/-- The actual block-colon branch from every native-reachable predecessor.
The placeholder premise is derived by the real scanner induction, and full
(event, pending-handle) equality is a conclusion of native token rewriting. -/
lemma reachable_colon_goOut {input : String} {s prep after : ScannerState}
    (reach : ScannerReachable input s)
    (pre : scanNextToken_preprocess s = .ok (some (prep, ':')))
    (edge : scanNextToken_dispatchBlockIndicators
      (if prep.allowDirectives then
        { prep with allowDirectives := false, documentEverStarted := true } else prep)
      ':' = .ok (some after)) (p : List String) :
    goOut after.tokens.toList p = goOut s.tokens.toList p := by
  have h := reachable_key_reservations reach
  have hp := preprocess_preserves_AllKeysPlaceholderInv s prep ':' pre h
  have had : SimpleKeyPlaceholderInv (if prep.allowDirectives then
      { prep with allowDirectives := false, documentEverStarted := true } else prep) := by
    split <;> exact hp.1
  have hs := scanValue_goOut had (L4YAML.Proofs.StreamAccum.dispatchBlock_colon_scanValue edge) p
  have htok : (if prep.allowDirectives then
      { prep with allowDirectives := false, documentEverStarted := true } else prep).tokens = prep.tokens := by
    split <;> rfl
  rw [htok] at hs
  exact hs.trans (L4YAML.Proofs.Serialization.TraceOf.StreamBridge.TPendingNode.preprocess_goOut pre p)

end L4YAML.Proofs.Serialization.TraceOf.KeyEvents
end Blanket
