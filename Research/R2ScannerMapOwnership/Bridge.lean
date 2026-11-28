import Research.R2ScannerMapOwnership.Reachable
import Research.R2ScannerMapOwnership.Countermodel
import Research.R2JointFrames.State

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.R2ConsumptionClosure

namespace R2MapOwnership

-- The joint projection's ownership and ordering prerequisites are now paid
-- for every initialized successful token prefix, not supplied externally.
lemma initialized_joint_entries (input : String) (n : Nat) (s : ScannerState)
    (reached : prefixes input n = some s) {P : SurfPos → Prop} {e : SurfPos}
    (context : R2JointFrames.Context s P e) : EntryValues s P e := by
  obtain ⟨sound, mono, _base, _floor, maps⟩ := initialized_facts input n s reached
  exact context.entries mono sound.slots maps

lemma counterfeit_not_initialized (input : String) (n : Nat) :
    prefixes input n ≠ some counterfeit :=
  fun reached => counterfeit_not_maps (initialized_maps input n counterfeit reached)

#print axioms initialized_joint_entries
#print axioms counterfeit_not_initialized

end R2MapOwnership
