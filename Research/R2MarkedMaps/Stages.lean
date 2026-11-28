import Research.R2MarkedMaps.Writers

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Proofs
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.IndentStackBase L4YAML.Proofs.PreprocessIndentStable

namespace R2JointFrames

lemma marked_documentStart (s : ScannerState) (h : MarkedMaps s) (slots : SlotsOk s) :
    MarkedMaps (scanDocumentStart s) := by
  apply (marked_unwind s (-1) h slots).of_eq
  · unfold scanDocumentStart; simp [advanceN_preserves_pendingKeys, emit_pendingKeys]
  · unfold scanDocumentStart; simp [advanceN_preserves_indents]

lemma marked_documentEnd {s t : ScannerState} (ok : scanDocumentEnd s = .ok t)
    (h : MarkedMaps s) (slots : SlotsOk s) : MarkedMaps t := by
  unfold scanDocumentEnd at ok
  simp only [bind, Except.bind] at ok
  repeat (any_goals (split at ok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at ok; subst ok)
  all_goals apply (marked_unwind s (-1) h slots).of_eq
  all_goals (try simp [advanceN_preserves_pendingKeys, emit_pendingKeys])
  all_goals simp [advanceN_preserves_indents]

lemma marked_preprocess {s t : ScannerState} {c : Char}
    (ok : scanNextToken_preprocess s = .ok (some (t,c)))
    (h : MarkedMaps s) (slots : SlotsOk s) : MarkedMaps t := by
  unfold scanNextToken_preprocess at ok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at ok
  split at ok
  · contradiction
  · rename_i skipped skip
    have keys := skipToContent_preserves_pendingKeys s skipped skip
    have indents := skipToContent_preserves_indents s skipped skip
    have maps := h.of_eq keys indents
    have sslots := slots.of_eq keys indents
    split at ok
    · simp at ok
    · split at ok
      · split at ok
        · contradiction
        · split at ok
          · simp at ok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ok
            obtain ⟨rfl, rfl⟩ := ok
            apply marked_stale
            exact (marked_unwind skipped _ maps sslots).of_eq
              (by rw [saveSimpleKey_preserves_pendingKeys])
              (by rw [saveSimpleKey_preserves_indents])
      · split at ok
        · contradiction
        · split at ok
          · simp at ok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ok
            obtain ⟨rfl, rfl⟩ := ok
            exact marked_stale _ (maps.of_eq (saveSimpleKey_preserves_pendingKeys _)
              (saveSimpleKey_preserves_indents _))

lemma marked_structural {s t : ScannerState} {c : Char}
    (ok : scanNextToken_dispatchStructural s c = .ok (some t))
    (h : MarkedMaps s) (slots : SlotsOk s) : MarkedMaps t := by
  unfold scanNextToken_dispatchStructural at ok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at ok
  repeat (any_goals (split at ok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact marked_documentStart s h slots
    | exact marked_documentEnd (by assumption) h slots
    | exact h.of_eq (scanDirective_preserves_pendingKeys (by assumption))
        (scanDirective_preserves_indents (by assumption))

lemma marked_flow {s t : ScannerState} {c : Char}
    (ok : scanNextToken_dispatchFlowIndicators s c = .ok (some t))
    (h : MarkedMaps s) : MarkedMaps t :=
  h.of_eq (dispatchFlowIndicators_preserves_pendingKeys ok)
    (L4YAML.Proofs.FlowIndentStable.dispatchFlowIndicators_preserves_indents ok)

lemma marked_blockDispatch {s t : ScannerState} {c : Char}
    (ok : scanNextToken_dispatchBlockIndicators s c = .ok (some t))
    (h : MarkedMaps s) (base : SentinelBase s)
    (floor : s.inFlow = false → s.currentIndent ≤ (s.col : Int)) : MarkedMaps t := by
  by_cases flow : s.inFlow = true
  · exact h.of_eq (dispatchBlockIndicators_preserves_pendingKeys flow ok)
      (L4YAML.Proofs.FlowIndentStable.dispatchBlockIndicators_preserves_indents flow ok)
  · have nf : s.inFlow = false := by simpa using flow
    unfold scanNextToken_dispatchBlockIndicators at ok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at ok
    repeat (any_goals (split at ok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    all_goals first
      | exact marked_block (by assumption) nf h
      | exact marked_key (by assumption) h base floor
      | exact marked_value (by assumption) h

lemma marked_content {s t : ScannerState} {c : Char}
    (ok : scanNextToken_dispatchContent s c = .ok t) (h : MarkedMaps s) :
    MarkedMaps t :=
  h.of_eq (dispatchContent_pendingKeys ok) (dispatchContent_preserves_indents ok)

#print axioms marked_preprocess
#print axioms marked_structural
#print axioms marked_blockDispatch

end R2JointFrames
