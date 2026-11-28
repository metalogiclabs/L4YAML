module
public import Research.R2ScannerMapOwnership.Scanner

@[expose] public section MapOwnershipCountermodel
set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Proofs
open L4YAML.Proofs.PendingKeySound

namespace R2MapOwnership

-- A malformed proof-input state, not a scanner-reachability witness.
-- Its register agrees with its marked sequence slot, so existing Sound
-- holds. The scanner's actual mark writer rejects precisely that kind.
def counterfeit : ScannerState := { bad with explicitKeyLine := some 0, explicitKeyCol := 0 }

lemma counterfeit_sound : Sound counterfeit where
  slots := by
    refine ⟨by decide +kernel, ?_⟩
    intro i l marked
    cases i with
    | zero => simp [counterfeit, bad] at marked
    | succ i =>
      cases i with
      | zero => exact ⟨0, by decide +kernel, by decide⟩
      | succ i =>
        rw [Array.getElem?_eq_none (by simp [counterfeit, bad])] at marked
        cases marked
  reg := fun _ => by
    rw [innermostPendingKey_eq, innermost_eq_go]
    simp [go, counterfeit, bad, ScannerState.indentColumns]
  base := by
    intro pos
    have zero : counterfeit.flowLevel = 0 := rfl
    exact (Nat.not_lt_zero _ (zero ▸ pos)).elim
  stack := rfl

lemma counterfeit_not_maps : ¬Maps counterfeit := by
  intro maps
  obtain ⟨entry, atEntry, kind⟩ := maps 1 0 (by rfl)
  have eq : entry = {column := 0, isSequence := true} := by
    simpa [counterfeit, bad] using atEntry.symm
  rw [eq] at kind
  cases kind

lemma sound_does_not_imply_maps : ¬(∀ s, Sound s → Maps s) :=
  fun implication => counterfeit_not_maps (implication counterfeit counterfeit_sound)

#print axioms sound_does_not_imply_maps

end R2MapOwnership
end MapOwnershipCountermodel
