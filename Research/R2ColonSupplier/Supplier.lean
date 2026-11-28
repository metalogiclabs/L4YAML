import Research.R2CompactSlot.SlotValues
import Research.R2ColonSupplier.LiveOwner

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.R2CompactSlot

namespace R2ColonSupplier

-- The caller retains the whole entry family, then preprocessing restricts
-- its scanner domain. The owner is taken from the actual live state.
lemma entry_step_at_landing {before prep : ScannerState} {start e : SurfPos}
    {own : Nat} {c : Char} (family : EntryValues before (SLYamlStream start) e)
    (marked : own ∈ RegisterWitness.markedCols before)
    (preprocess : scanNextToken_preprocess before = .ok (some (prep,c))) :
    EntryStep (ValuesBelow prep (SLYamlStream start) own) own e := by
  have step := family.at marked (marked_lt_ceiling marked)
  exact step.map (fun z lower => ValuesBelow.restrict lower (fun x _ hx =>
    (RegisterWitness.preprocess_markedCols preprocess
      (RegisterWitness.MarkedColsIn.self before)).mem hx))

#print axioms entry_step_at_landing

end R2ColonSupplier
