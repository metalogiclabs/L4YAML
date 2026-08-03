/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.Scanner

/-!
# Flow-adjacency check: proof helpers (Fix A, step a) — legacy scanner

The scanner rejects separator-less adjacent flow entries via
`scanNextToken_checkFlowAdjacency`, folded into the entry of
`scanNextToken_dispatchFlowIndicators`.  This module provides the two
reusable helpers every downstream (legacy) proof needs:

* **`peel_flowAdj`** — for *inversion* sites (given a successful
  `dispatchFlowIndicators` result, derive facts): strip the folded check
  off the front, restoring the pre-fold body so the existing dispatch
  proof proceeds unchanged.

* **`checkFlowAdjacency_ok_of_notInFlow` / `_notCompletes` / `_sepChar`**
  — for *construction* sites (prove `dispatchFlowIndicators s c = .ok …`):
  discharge the check to `.ok ()` from the local scanner invariant.

The indexed twins live in `FlowAdjacencyIx.lean` (kept separate so the
legacy proofs, which `L4YAML.Scanner.IndexedDispatch` transitively
depends on, do not form an import cycle). -/

namespace L4YAML.Proofs.FlowAdjacency

open L4YAML L4YAML.Scanner

/-! ## Inversion helpers (peel the folded check) -/

/-- Peel the folded flow-adjacency check off the front of
    `scanNextToken_dispatchFlowIndicators`.  After
    `unfold scanNextToken_dispatchFlowIndicators`, the body is
    `scanNextToken_checkFlowAdjacency s c >>= k`; on a successful (`.ok`)
    result the check must itself have succeeded, so the continuation
    `k ()` carries the whole `.ok` equation. -/
theorem peel_flowAdj {α : Type} {s : ScannerState} {c : Char}
    {k : Unit → Except ScanError α} {r : α}
    (h : (scanNextToken_checkFlowAdjacency s c >>= k) = .ok r) : k () = .ok r := by
  cases hc : scanNextToken_checkFlowAdjacency s c with
  | ok u => rw [hc] at h; simp only [bind, Except.bind] at h; exact h
  | error e => rw [hc] at h; simp [bind, Except.bind] at h

/-! ## Construction helpers (discharge the check to `.ok ()`) -/

/-- Outside a flow collection the adjacency check is vacuously `.ok ()`. -/
theorem checkFlowAdjacency_ok_of_notInFlow {s : ScannerState} {c : Char}
    (h : s.inFlow = false) : scanNextToken_checkFlowAdjacency s c = .ok () := by
  unfold scanNextToken_checkFlowAdjacency
  simp [h]

/-- If the previous real token does not complete a flow value, the
    adjacency check is `.ok ()` regardless of `c`. -/
theorem checkFlowAdjacency_ok_of_notCompletes {s : ScannerState} {c : Char}
    (h : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    scanNextToken_checkFlowAdjacency s c = .ok () := by
  unfold scanNextToken_checkFlowAdjacency
  split
  · split
    · rename_i hlast; rw [h _ hlast]; simp
    · rfl
  · rfl

/-- If `c` is a valid post-value character (`,` `:` `]` `}`), the
    adjacency check is `.ok ()` regardless of the previous token. -/
theorem checkFlowAdjacency_ok_of_sepChar {s : ScannerState} {c : Char}
    (h : c = ',' ∨ c = ':' ∨ c = ']' ∨ c = '}') :
    scanNextToken_checkFlowAdjacency s c = .ok () := by
  unfold scanNextToken_checkFlowAdjacency
  split
  · split
    · rcases h with rfl | rfl | rfl | rfl <;> simp
    · rfl
  · rfl

/-! ## Last-token preservation through `saveSimpleKey`

Used to thread the `checkFlowAdjacency_ok_of_notCompletes` discharge from a
scanner state into its `saveSimpleKey`-preprocessed successor (the emit→scan
towers scan each flow entry from a `saveSimpleKey`-advanced state). -/

/-- Pushing two `.placeholder` slots does not change the last *real* token
    (it is skipped), so `lastRealTokenVal?` is either unchanged or the
    placeholder itself. -/
theorem lastRealTokenVal_push_two_ph
    (tokens : Array (Positioned YamlToken))
    (ph1 ph2 : Positioned YamlToken) (h1 : ph1.val = .placeholder) (h2 : ph2.val = .placeholder)
    (t : YamlToken)
    (ht : lastRealTokenVal? ((tokens.push ph1).push ph2) = some t) :
    lastRealTokenVal? tokens = some t ∨ t = .placeholder := by
  unfold lastRealTokenVal? at ht
  dsimp only [] at ht
  simp only [Array.size_push] at ht
  simp only [show tokens.size + 2 > 0 from by omega, ↓reduceIte,
    show tokens.size + 2 - 1 = tokens.size + 1 from by omega] at ht
  have h_elem1 : ((tokens.push ph1).push ph2)[tokens.size + 1]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.getElem_push, Array.size_push, h2]
  simp only [h_elem1, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
    Bool.true_and, show tokens.size + 1 > 0 from by omega,
    show tokens.size + 1 - 1 = tokens.size from by omega] at ht
  have h_elem2 : ((tokens.push ph1).push ph2)[tokens.size]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega)]
    simp [Array.getElem_push, Array.size_push, h1]
  by_cases h_gt : tokens.size > 0
  · have h_elem3 : ((tokens.push ph1).push ph2)[tokens.size - 1]!.val =
        tokens[tokens.size - 1]!.val := by
      rw [getElem!_pos _ _ (by simp [Array.size_push]; omega),
          getElem!_pos _ _ (by omega)]
      simp only [Array.getElem_push,
        show tokens.size - 1 < (tokens.push ph1).size from by simp [Array.size_push]; omega,
        show tokens.size - 1 < tokens.size from by omega, dite_true]
    simp only [h_elem2, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show tokens.size + 1 > 1 from by omega, ↓reduceIte,
      show tokens.size + 1 - 2 = tokens.size - 1 from by omega,
      h_elem3, decide_true] at ht
    injection ht with ht_val
    by_cases h_ne : t = .placeholder
    · exact .inr h_ne
    · left; unfold lastRealTokenVal?; dsimp only []
      simp [h_gt, ht_val,
        show (t == YamlToken.placeholder) = false from beq_eq_false_iff_ne.mpr h_ne]
  · simp only [h_elem2, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show ¬(tokens.size + 1 > 1) from by omega, ↓reduceIte,
      decide_true, decide_false] at ht
    injection ht with ht_val; exact .inr ht_val.symm

/-- If the final array slot holds a non-placeholder token, `lastRealTokenVal?`
    returns exactly that token's value (no placeholder-skipping needed).  Used to
    read off the last real token from the `scanNextToken_flow_value` `.value`-push
    exposure (which is stated as an index fact, not a `.push` shape). -/
theorem lastRealTokenVal_of_last_nonph
    (tokens : Array (Positioned YamlToken)) (N : Nat) (tok : Positioned YamlToken)
    (h_size : tokens.size = N + 1) (h_get : tokens[N]? = some tok)
    (h_np : tok.val ≠ .placeholder) :
    lastRealTokenVal? tokens = some tok.val := by
  have hN : N < tokens.size := by omega
  have h_eq : tokens[N] = tok := by
    rw [Array.getElem?_eq_getElem hN] at h_get; exact Option.some.inj h_get
  have h_bang : tokens[tokens.size - 1]!.val = tok.val := by
    rw [show tokens.size - 1 = N from by omega, getElem!_pos tokens N hN, h_eq]
  have h_np' : (tok.val == YamlToken.placeholder) = false := beq_eq_false_iff_ne.mpr h_np
  unfold lastRealTokenVal?
  simp only [show tokens.size > 0 from by omega, ↓reduceIte, h_bang, h_np',
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- `saveSimpleKey` preserves "last real token does not complete a flow
    value" (the placeholders it may push are not value-completers). -/
theorem saveSimpleKey_preserves_completesFalse (s : ScannerState)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false)
    (t : YamlToken)
    (ht : lastRealTokenVal? (saveSimpleKey s).tokens = some t) :
    t.completesFlowValue = false := by
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
      (saveSimpleKey s).tokens = ((s.tokens.push ⟨s.currentPos, .placeholder, s.currentPos⟩).push
        ⟨s.currentPos, .placeholder, s.currentPos⟩) := by
    unfold saveSimpleKey
    split
    · exact .inl rfl
    · split
      · right; dsimp only []
      · exact .inl rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq] at ht; exact h_last t ht
  · rw [h_eq] at ht
    have h_or := lastRealTokenVal_push_two_ph s.tokens
      ⟨s.currentPos, .placeholder, s.currentPos⟩
      ⟨s.currentPos, .placeholder, s.currentPos⟩ rfl rfl t ht
    cases h_or with
    | inl h => exact h_last t h
    | inr h => subst h; rfl

end L4YAML.Proofs.FlowAdjacency
