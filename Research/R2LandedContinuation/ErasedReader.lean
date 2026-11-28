import Research.R2LandedContinuation.LandedValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.R2SequenceContext L4YAML.Proofs.R2LandedContinuation

namespace R2LandedErasure

-- Negative control: change only the funded slot to the old stream-only
-- interface. No alternative premise or substitute family is introduced.
lemma erased_reader {before after : ScannerState}
    {start slot land dash next : SurfPos} {nv k : Nat}
    (payload : ∀ e, SBlockIndented nv .blockOut slot e → SLYamlStream start e)
    (bound : nv ≤ k) (comments : SSLComments slot land) (indent : SIndent k land dash)
    (literal : GLit '-' dash next) (notNs : GNot SNsChar next)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    SequenceValues after start k next := by
  exact SlotValues.landed_sequence payload bound comments indent literal notNs back

end R2LandedErasure
