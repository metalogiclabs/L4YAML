/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.IndexedDispatch

/-!
# Flow-adjacency check: proof helpers (Fix A, step a) — indexed scanner

Indexed twins of the helpers in `FlowAdjacency.lean`, for
`scanNextTokenIx_dispatchFlowIndicators`.  Kept in a separate module
(importing `L4YAML.Scanner.IndexedDispatch`) so the legacy helpers, which
that scanner module transitively depends on, do not form an import cycle.
-/

namespace L4YAML.Proofs.FlowAdjacencyIx

open L4YAML L4YAML.Scanner L4YAML.Scanner.Indexed L4YAML.Scanner.Indexed.ScannerStateIx

/-- Peel the folded flow-adjacency check off the front of
    `scanNextTokenIx_dispatchFlowIndicators` (inversion sites). -/
theorem peel_flowAdjIx {input : String} {α : Type}
    {s : ScannerStateIx input} {c : Char}
    {k : Unit → Except ScanError α} {r : α}
    (h : (scanNextTokenIx_checkFlowAdjacency s c >>= k) = .ok r) : k () = .ok r := by
  cases hc : scanNextTokenIx_checkFlowAdjacency s c with
  | ok u => rw [hc] at h; simp only [bind, Except.bind] at h; exact h
  | error e => rw [hc] at h; simp [bind, Except.bind] at h

/-- Outside a flow collection the adjacency check is vacuously `.ok ()`. -/
theorem checkFlowAdjacencyIx_ok_of_notInFlow {input : String}
    {s : ScannerStateIx input} {c : Char}
    (h : s.inFlow = false) : scanNextTokenIx_checkFlowAdjacency s c = .ok () := by
  unfold scanNextTokenIx_checkFlowAdjacency
  simp [h]

/-- If the previous real token does not complete a flow value, the
    adjacency check is `.ok ()` regardless of `c`. -/
theorem checkFlowAdjacencyIx_ok_of_notCompletes {input : String}
    {s : ScannerStateIx input} {c : Char}
    (h : ∀ t, lastRealTokenValIx? s.tokens = some t → t.completesFlowValue = false) :
    scanNextTokenIx_checkFlowAdjacency s c = .ok () := by
  unfold scanNextTokenIx_checkFlowAdjacency
  split
  · split
    · rename_i hlast; rw [h _ hlast]; simp
    · rfl
  · rfl

/-- If `c` is a valid post-value character (`,` `:` `]` `}`), the
    adjacency check is `.ok ()` regardless of the previous token. -/
theorem checkFlowAdjacencyIx_ok_of_sepChar {input : String}
    {s : ScannerStateIx input} {c : Char}
    (h : c = ',' ∨ c = ':' ∨ c = ']' ∨ c = '}') :
    scanNextTokenIx_checkFlowAdjacency s c = .ok () := by
  unfold scanNextTokenIx_checkFlowAdjacency
  split
  · split
    · rcases h with rfl | rfl | rfl | rfl <;> simp
    · rfl
  · rfl

end L4YAML.Proofs.FlowAdjacencyIx
