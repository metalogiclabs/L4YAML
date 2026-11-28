import Research.R2SequenceContext.SequenceValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2CompactSlot
open L4YAML.Proofs.R2SequenceContext

namespace L4YAML.Proofs.R2LandedContinuation

-- The slot's domain is the whole landed collection, including its current
-- sequence tail. Restrict only to the actual post-step marked projection.
lemma SlotValues.landed_sequence {before after : ScannerState}
    {start slot land dash next : SurfPos} {nv k : Nat}
    (payload : SlotValues before start nv .blockOut slot) (bound : nv ≤ k)
    (comments : SSLComments slot land) (indent : SIndent k land dash)
    (literal : GLit '-' dash next) (notNs : GNot SNsChar next)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    SequenceValues after start k next := by
  intro e node z tail
  exact EntryValues.restrict_state (payload z
    (slotLandedSeq bound comments
      (SBlockSeqEntries_of_compactTail indent literal notNs node tail))) back

#print axioms SlotValues.landed_sequence

end L4YAML.Proofs.R2LandedContinuation
