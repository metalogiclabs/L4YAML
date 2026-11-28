import Research.R2JointFrames.State
import L4YAML.Proofs.Scanner.ColFloor

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Proofs
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.IndentStackBase L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.CloseStaleExplicitKey

namespace R2JointFrames

lemma MarkedMaps.of_eq {s t : ScannerState} (h : MarkedMaps s)
    (keys : t.pendingKeys = s.pendingKeys) (indents : t.indents = s.indents) :
    MarkedMaps t := by
  intro i l key
  obtain ⟨entry, atEntry, kind⟩ := h i l (keys ▸ key)
  exact ⟨entry, by rw [indents]; exact atEntry, kind⟩

lemma MarkedMaps.push_none {s t : ScannerState} (h : MarkedMaps s) (entry : IndentEntry)
    (keys : t.pendingKeys = s.pendingKeys.push none)
    (indents : t.indents = s.indents.push entry) : MarkedMaps t := by
  intro i l key
  rw [keys] at key
  by_cases lt : i < s.pendingKeys.size
  · rw [Array.getElem?_push_lt lt, ← Array.getElem?_eq_getElem lt] at key
    obtain ⟨old, atOld, kind⟩ := h i l key
    have oldLt := (Array.getElem?_eq_some_iff.mp atOld).1
    exact ⟨old, by rw [indents, Array.getElem?_push_lt oldLt,
      ← Array.getElem?_eq_getElem oldLt]; exact atOld, kind⟩
  · by_cases eq : i = s.pendingKeys.size
    · subst i; rw [Array.getElem?_push_size] at key; cases key
    · rw [Array.getElem?_eq_none (by simp; omega)] at key; cases key

lemma MarkedMaps.pop {s t : ScannerState} (h : MarkedMaps s)
    (size : s.pendingKeys.size = s.indents.size)
    (keys : t.pendingKeys = s.pendingKeys.pop) (indents : t.indents = s.indents.pop) :
    MarkedMaps t := by
  intro i l key
  rw [keys, Array.getElem?_pop] at key
  split at key
  · obtain ⟨entry, atEntry, kind⟩ := h i l key
    exact ⟨entry, by rw [indents, Array.getElem?_pop, ite_eq_left (by omega)]; exact atEntry, kind⟩
  · cases key

lemma MarkedMaps.erase {s t : ScannerState} (h : MarkedMaps s)
    (indents : t.indents = s.indents)
    (back : ∀ (i l : Nat), t.pendingKeys[i]? = some (some l) → s.pendingKeys[i]? = some (some l)) :
    MarkedMaps t := by
  intro i l key
  obtain ⟨entry, atEntry, kind⟩ := h i l (back i l key)
  exact ⟨entry, by rw [indents]; exact atEntry, kind⟩

lemma marked_pushMapping (s : ScannerState) (col : Int) (h : MarkedMaps s) :
    MarkedMaps (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · exact h.push_none _ rfl rfl
  · exact h

lemma marked_pushSequence (s : ScannerState) (col : Int) (h : MarkedMaps s) :
    MarkedMaps (pushSequenceIndent s col) := by
  unfold pushSequenceIndent
  split
  · exact h.push_none _ rfl rfl
  · exact h

lemma marked_unwindLoop (s : ScannerState) (col : Int) (fuel : Nat)
    (h : MarkedMaps s) (slots : SlotsOk s) : MarkedMaps (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => simpa [unwindIndentsLoop] using h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · exact ih _ (h.pop slots.1 rfl rfl) (slots.pop rfl rfl)
    · exact h

lemma marked_unwind (s : ScannerState) (col : Int) (h : MarkedMaps s) (slots : SlotsOk s) :
    MarkedMaps (unwindIndents s col) := marked_unwindLoop s col _ h slots

lemma marked_clear (s : ScannerState) (col : Int) (h : MarkedMaps s) :
    MarkedMaps (s.clearPendingKeyAt col) :=
  h.erase rfl (fun i l key => (closeAt_marked _ _ _ i l key).1)

lemma marked_staleAt (s : ScannerState) (c : Char) (h : MarkedMaps s) :
    MarkedMaps (s.closeStaleAt c) :=
  h.erase rfl (fun i l key => closeStale_marked _ _ _ _ _ i l key)

lemma marked_stale (s : ScannerState) (h : MarkedMaps s) :
    MarkedMaps (closeStaleExplicitKey s) := by
  rcases closeStaleExplicitKey_cases s with eq | ⟨c, _, eq⟩ <;> rw [eq]
  · exact h
  · exact (marked_staleAt s c h).of_eq rfl rfl

lemma marked_key {s t : ScannerState} (ok : scanKey s = .ok t)
    (h : MarkedMaps s) (base : SentinelBase s)
    (floor : s.inFlow = false → s.currentIndent ≤ (s.col : Int)) : MarkedMaps t := by
  by_cases flow : s.inFlow = true
  · exact h.of_eq (scanKey_pendingKeys_of_inFlow flow ok)
      (L4YAML.Proofs.FlowIndentStable.scanKey_indents_of_inFlow flow ok)
  · have nf : s.inFlow = false := by simpa using flow
    let pushed := pushMappingIndent s (s.col : Int)
    have pm : MarkedMaps pushed := marked_pushMapping s _ h
    have topMap : ∃ entry, pushed.indents[pushed.indents.size-1]? = some entry ∧
        entry.isSequence = false := by
      by_cases new : s.currentIndent < (s.col : Int)
      · refine ⟨{ column := (s.col : Int), isSequence := false }, ?_, rfl⟩
        simp [pushed, pushMappingIndent, new]
      · have eq : (s.col : Int) = s.currentIndent := by have := floor nf; omega
        have pos := base.size_pos
        let entry := s.indents[s.indents.size-1]'(by omega)
        have back : s.indents.back? = some entry := by
          rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
        have atCol : (s.col : Int) = entry.column := by
          rw [eq, IndentStackMono.currentIndent_eq_last pos]
        refine ⟨entry, ?_, scanKey_top_not_sequence ok nf back atCol⟩
        simpa [pushed, pushMappingIndent, new] using
          (show s.indents[s.indents.size-1]? = some entry by
            rw [Array.getElem?_eq_getElem (by omega)])
    intro i l key
    have tk := scanKey_pendingKeys nf ok
    have ti := scanKey_indents nf ok
    change t.pendingKeys = pushed.pendingKeys.set! (pushed.indents.size-1) (some s.line) at tk
    change t.indents = pushed.indents at ti
    rw [tk, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at key
    split at key
    · rename_i eq
      rw [← eq]
      obtain ⟨entry, atEntry, kind⟩ := topMap
      exact ⟨entry, by rw [ti]; exact atEntry, kind⟩
    · obtain ⟨entry, atEntry, kind⟩ := pm i l key
      exact ⟨entry, by rw [ti]; exact atEntry, kind⟩

lemma marked_valuePrepare (s : ScannerState) (h : MarkedMaps s) :
    MarkedMaps (scanValuePrepare s) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · exact h.push_none _ rfl rfl
      · exact h.of_eq rfl rfl
    · exact h.of_eq rfl rfl
  · split
    · exact h.of_eq rfl rfl
    · split
      · exact marked_pushMapping s _ h
      · exact h

lemma marked_value {s t : ScannerState} (ok : scanValue s = .ok t)
    (h : MarkedMaps s) : MarkedMaps t := by
  unfold scanValue at ok
  simp only [bind, Except.bind] at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  simp only [Except.ok.injEq] at ok; subst ok
  obtain ⟨ci, ck, _⟩ := scanValueClearKey_core s
  have cleared : MarkedMaps (scanValueClearKey s) := h.of_eq ck ci
  have prepared := marked_valuePrepare _ cleared
  have advanced : MarkedMaps (((scanValuePrepare (scanValueClearKey s)).emit .value).advance) :=
    prepared.of_eq (by rw [advance_preserves_pendingKeys]; rfl)
      (by rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]; rfl)
  split
  · exact advanced.of_eq rfl rfl
  · split
    · exact advanced.of_eq rfl rfl
    · exact advanced.erase rfl (fun i l key => (closeAt_marked _ _ _ i l key).1)

lemma marked_block {s t : ScannerState} (ok : scanBlockEntry s = .ok t)
    (nf : s.inFlow = false) (h : MarkedMaps s) : MarkedMaps t :=
  (marked_pushSequence s _ h).of_eq (scanBlockEntry_pendingKeys nf ok)
    (scanBlockEntry_indents nf ok)

#print axioms marked_key
#print axioms marked_value

end R2JointFrames
