module
public import Research.R2ScannerMapOwnership.Controls

@[expose] public section MapOwnershipScanner

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs
open L4YAML.Proofs.PendingKeysStable L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.IndentStackMono (Mono)

namespace R2MapOwnership

lemma Maps.of_eq {s t : ScannerState} (h : Maps s)
    (keys : t.pendingKeys = s.pendingKeys) (indents : t.indents = s.indents) : Maps t := by
  intro i l marked
  obtain ⟨entry, atEntry, kind⟩ := h i l (keys ▸ marked)
  exact ⟨entry, indents ▸ atEntry, kind⟩

lemma Maps.push_none {s t : ScannerState} (h : Maps s) (entry : IndentEntry)
    (keys : t.pendingKeys = s.pendingKeys.push none)
    (indents : t.indents = s.indents.push entry) : Maps t := by
  intro i l marked
  rw [keys] at marked
  by_cases before : i < s.pendingKeys.size
  · rw [Array.getElem?_push_lt before] at marked
    obtain ⟨old, atOld, kind⟩ := h i l (by rw [Array.getElem?_eq_getElem before]; exact marked)
    refine ⟨old, ?_, kind⟩
    rw [indents, Array.getElem?_push_lt (Array.getElem?_eq_some_iff.mp atOld).1]
    rw [Array.getElem?_eq_getElem (Array.getElem?_eq_some_iff.mp atOld).1] at atOld
    exact atOld
  · by_cases last : i = s.pendingKeys.size
    · subst i
      rw [Array.getElem?_push_size] at marked
      cases marked
    · rw [Array.getElem?_eq_none (by simp [Array.size_push]; omega)] at marked
      cases marked

lemma Maps.push_mapping (s : ScannerState) (col : Int) (h : Maps s) :
    Maps (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · exact h.push_none _ rfl rfl
  · exact h

lemma Maps.push_sequence (s : ScannerState) (col : Int) (h : Maps s) :
    Maps (pushSequenceIndent s col) := by
  unfold pushSequenceIndent
  split
  · exact h.push_none _ rfl rfl
  · exact h

lemma Maps.pop {s t : ScannerState} (h : Maps s) (slots : SlotsOk s)
    (keys : t.pendingKeys = s.pendingKeys.pop)
    (indents : t.indents = s.indents.pop) : Maps t := by
  intro i l marked
  rw [keys, Array.getElem?_pop] at marked
  split at marked
  · rename_i bound
    obtain ⟨entry, atEntry, kind⟩ := h i l marked
    exact ⟨entry, by rw [indents, Array.getElem?_pop, ite_eq_left (by have := slots.1; omega)]; exact atEntry, kind⟩
  · cases marked

lemma Maps.clear_at {s : ScannerState} (h : Maps s) (col : Int) :
    Maps (s.clearPendingKeyAt col) := by
  intro i l marked
  exact h i l (closeAt_marked _ _ _ _ _ marked).1

lemma Maps.close_stale_at {s : ScannerState} (h : Maps s) (c : Char) : Maps (s.closeStaleAt c) := by
  intro i l marked
  exact h i l (closeStale_marked _ _ _ _ _ _ _ marked)

lemma Maps.close_stale {s : ScannerState} (h : Maps s) : Maps (closeStaleExplicitKey s) := by
  rcases L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_cases s with eq | ⟨_, _, eq⟩
  · rw [eq]; exact h
  · rw [eq]
    exact h.close_stale_at _

lemma Maps.unwind_loop (s : ScannerState) (col : Int) (fuel : Nat)
    (h : Maps s) (slots : SlotsOk s) : Maps (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => simpa [unwindIndentsLoop] using h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · obtain ⟨indents, keys, _⟩ := unwindPop_fields s
      exact ih _ (h.pop slots keys indents) (slots.pop indents keys)
    · exact h

lemma Maps.unwind (s : ScannerState) (col : Int) (h : Maps s) (slots : SlotsOk s) :
    Maps (unwindIndents s col) := by
  unfold unwindIndents
  exact h.unwind_loop _ _ _ slots

lemma Maps.scan_key {s t : ScannerState} (h : Maps s)
    (base : SentinelBase s) (floor : s.inFlow = false → s.currentIndent ≤ (s.col : Int))
    (step : scanKey s = .ok t) : Maps t := by
  by_cases flow : s.inFlow = true
  · exact h.of_eq (scanKey_pendingKeys_of_inFlow flow step)
      (L4YAML.Proofs.FlowIndentStable.scanKey_indents_of_inFlow flow step)
  · have noflow : s.inFlow = false := by simpa using flow
    let pushed := pushMappingIndent s (s.col : Int)
    have keys := scanKey_pendingKeys noflow step
    have indents := scanKey_indents noflow step
    have kept : Maps pushed := h.push_mapping s _
    have top : ∃ entry : IndentEntry,
        pushed.indents[pushed.indents.size - 1]? = some entry ∧ entry.isSequence = false := by
      dsimp only [pushed]
      unfold pushMappingIndent
      split
      · exact ⟨{column := s.col, isSequence := false}, by simp [ScannerState.emit], rfl⟩
      · have positive := base.size_pos
        let entry := s.indents[s.indents.size-1]'(by omega)
        have atEntry : s.indents.back? = some entry := by
          rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
        have column : (s.col : Int) = entry.column := by
          have upper := floor noflow
          have current := L4YAML.Proofs.IndentStackMono.currentIndent_eq_last positive
          dsimp only [entry]
          omega
        exact ⟨entry, by rw [Array.getElem?_eq_getElem (by omega)],
          scanKey_top_not_sequence step noflow atEntry column⟩
    intro i l marked
    rw [keys, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at marked
    split at marked
    · rename_i equal
      subst i
      obtain ⟨entry, atEntry, kind⟩ := top
      exact ⟨entry, indents ▸ atEntry, kind⟩
    · obtain ⟨entry, atEntry, kind⟩ := kept i l marked
      exact ⟨entry, indents ▸ atEntry, kind⟩

lemma Maps.value_prepare (s : ScannerState) (h : Maps s) : Maps (scanValuePrepare s) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · exact h.push_none _ rfl rfl
      · exact h
    · exact h
  · split
    · exact h
    · split
      · exact h.push_mapping s _
      · exact h

lemma Maps.scan_value {s t : ScannerState} (h : Maps s)
    (step : scanValue s = .ok t) : Maps t := by
  have clear := scanValueClearKey_core s
  have cleared : Maps (scanValueClearKey s) := h.of_eq clear.2.1 clear.1
  have prepared := cleared.value_prepare _
  have advanced : Maps (((scanValuePrepare (scanValueClearKey s)).emit .value).advance) :=
    prepared.of_eq (by rw [advance_preserves_pendingKeys, emit_pendingKeys])
      (by rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]; rfl)
  unfold scanValue at step
  simp only [bind, Except.bind] at step
  split at step <;> try contradiction
  split at step <;> try contradiction
  split at step <;> try contradiction
  simp only [Except.ok.injEq] at step
  subst t
  split
  · exact advanced
  · split
    · exact advanced
    · exact advanced.clear_at _

lemma Maps.scan_block_entry {s t : ScannerState} (h : Maps s)
    (noflow : s.inFlow = false) (step : scanBlockEntry s = .ok t) : Maps t :=
  (h.push_sequence s _).of_eq (scanBlockEntry_pendingKeys noflow step)
    (scanBlockEntry_indents noflow step)

lemma Maps.document_start (s : ScannerState) (h : Maps s) (slots : SlotsOk s) :
    Maps (scanDocumentStart s) := by
  apply (h.unwind s (-1) slots).of_eq
  · unfold scanDocumentStart
    simp [advanceN_preserves_pendingKeys, emit_pendingKeys]
  · unfold scanDocumentStart
    simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents]

lemma Maps.document_end {s t : ScannerState} (h : Maps s) (slots : SlotsOk s)
    (step : scanDocumentEnd s = .ok t) : Maps t := by
  unfold scanDocumentEnd at step
  simp only [bind, Except.bind] at step
  repeat (any_goals (split at step))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at step; subst t)
  all_goals apply (h.unwind s (-1) slots).of_eq
  all_goals simp [advanceN_preserves_pendingKeys, emit_pendingKeys,
    L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents]

lemma Maps.preprocess {s t : ScannerState} {c : Char} (h : Maps s) (slots : SlotsOk s)
    (step : scanNextToken_preprocess s = .ok (some (t,c))) : Maps t := by
  unfold scanNextToken_preprocess at step
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at step
  split at step
  · contradiction
  · rename_i skipped skip
    have indents := skipToContent_preserves_indents s skipped skip
    have keys := skipToContent_preserves_pendingKeys s skipped skip
    have kept : Maps skipped := h.of_eq keys indents
    have keptSlots : SlotsOk skipped := slots.of_eq keys indents
    split at step
    · simp at step
    · split at step
      · split at step
        · contradiction
        · split at step
          · simp at step
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl,rfl⟩ := step
            apply Maps.close_stale
            exact (kept.unwind _ _ keptSlots).of_eq (saveSimpleKey_preserves_pendingKeys _)
              (saveSimpleKey_preserves_indents _)
      · split at step
        · contradiction
        · split at step
          · simp at step
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl,rfl⟩ := step
            apply Maps.close_stale
            exact kept.of_eq (saveSimpleKey_preserves_pendingKeys _)
              (saveSimpleKey_preserves_indents _)

lemma Maps.dispatch_structural {s t : ScannerState} {c : Char} (h : Maps s) (slots : SlotsOk s)
    (step : scanNextToken_dispatchStructural s c = .ok (some t)) : Maps t := by
  unfold scanNextToken_dispatchStructural at step
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at step
  repeat (any_goals (split at step))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact h.document_start s slots
    | exact h.document_end slots (by assumption)
    | exact h.of_eq (scanDirective_preserves_pendingKeys (by assumption))
        (L4YAML.Proofs.IndentStackBase.scanDirective_preserves_indents (by assumption))

lemma Maps.dispatch_flow {s t : ScannerState} {c : Char} (h : Maps s)
    (step : scanNextToken_dispatchFlowIndicators s c = .ok (some t)) : Maps t :=
  h.of_eq (dispatchFlowIndicators_preserves_pendingKeys step)
    (L4YAML.Proofs.FlowIndentStable.dispatchFlowIndicators_preserves_indents step)

lemma Maps.dispatch_block {s t : ScannerState} {c : Char} (h : Maps s)
    (base : SentinelBase s) (floor : s.inFlow = false → s.currentIndent ≤ (s.col : Int))
    (step : scanNextToken_dispatchBlockIndicators s c = .ok (some t)) : Maps t := by
  by_cases flow : s.inFlow = true
  · exact h.of_eq (dispatchBlockIndicators_preserves_pendingKeys flow step)
      (L4YAML.Proofs.FlowIndentStable.dispatchBlockIndicators_preserves_indents flow step)
  · have noflow : s.inFlow = false := by simpa using flow
    unfold scanNextToken_dispatchBlockIndicators at step
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at step
    repeat (any_goals (split at step))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    all_goals first
      | exact h.scan_block_entry noflow (by assumption)
      | exact h.scan_key base floor (by assumption)
      | exact h.scan_value (by assumption)

lemma Maps.dispatch_content {s t : ScannerState} {c : Char} (h : Maps s)
    (step : scanNextToken_dispatchContent s c = .ok t) : Maps t :=
  h.of_eq (dispatchContent_pendingKeys step)
    (L4YAML.Proofs.IndentStackBase.dispatchContent_preserves_indents step)

lemma Maps.initial (input : String) : Maps (ScannerState.mk' input) := by
  intro i l marked
  cases i <;> simp [ScannerState.mk'] at marked

#print axioms Maps.scan_key
#print axioms Maps.preprocess
#print axioms Maps.dispatch_structural
#print axioms Maps.dispatch_block

end R2MapOwnership

end MapOwnershipScanner
