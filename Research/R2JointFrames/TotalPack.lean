import Research.R2SequenceContext.SequenceValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.R2SequenceContext

namespace R2JointFrames

-- Once the mandatory entry proof retains the family, this value-line face
-- is total. There is no second supplier and no alternative to select.
lemma total_sequence_pack {sc : ScannerState} {start slot : SurfPos} {n : Nat}
    (family : SequenceValues sc start n slot) :
    ∀ own ∈ RegisterWitness.markedCols sc,
      ∀ e, SBlockIndented n .blockIn slot e →
      ∀ z, SCompactSeqTail n e z → ExplValueLine start own z :=
  fun _own marked e node z tail =>
    (family e node z tail).valueLine marked (marked_lt_ceiling marked)

#print axioms total_sequence_pack

end R2JointFrames
