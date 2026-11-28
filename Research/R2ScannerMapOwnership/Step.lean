module
public import Research.R2ScannerMapOwnership.Scanner

@[expose] public section MapOwnershipStep

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs
open L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.IndentStackMono (Mono)

namespace R2MapOwnership

lemma Maps.next {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : Maps s)
    (sound : Sound s) (hm : Mono s) (hbase : SentinelBase s)
    (hfloor : PreprocessFloor s) : Maps s' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp at hok
    · rename_i sp c h_pre
      have h_ps : Sound sp := preprocess_sound h_pre sound hm
      have h_pb : SentinelBase sp := L4YAML.Proofs.IndentStackBase.preprocess_base h_pre hbase
      have h_maps : Maps sp := h.preprocess sound.slots h_pre
      have h_pc : sp.inFlow = false → sp.currentIndent ≤ (sp.col : Int) := hfloor sp c h_pre
      split at hok
      · cases hok
      split at hok
      · cases hok
      split at hok
      · cases hok
      · split at hok
        · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
          exact h_maps.dispatch_structural h_ps.slots ‹_›
        · split at hok
          · cases hok
          split at hok
          · cases hok
          · rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at hok
            · generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact h_maps.dispatch_flow h_fi
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact h_maps.dispatch_block h_pb h_pc h_bi
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact h_maps.dispatch_content h_dc
            · generalize h_sp2 :
                (({ sp with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at hok
              have h_ps2 : Sound sp2 := by
                rw [← h_sp2]; exact Sound.of_eq h_ps rfl rfl rfl rfl rfl rfl
              have h_maps2 : Maps sp2 := by
                rw [← h_sp2]; exact h_maps.of_eq rfl rfl
              have h_pb2 : SentinelBase sp2 := by rw [← h_sp2]; exact h_pb
              have h_pc2 : sp2.inFlow = false → sp2.currentIndent ≤ (sp2.col : Int) := by
                rw [← h_sp2]; exact h_pc
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact h_maps2.dispatch_flow h_fi
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact h_maps2.dispatch_block h_pb2 h_pc2 h_bi
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp2 c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp2 c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact h_maps2.dispatch_content h_dc

#print axioms Maps.next

end R2MapOwnership

end MapOwnershipStep
