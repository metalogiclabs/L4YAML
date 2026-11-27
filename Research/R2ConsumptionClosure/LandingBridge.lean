import Research.R2ConsumptionClosure.EntryValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure

namespace R2LandingBridge

-- The actual colon boundary already supplies these scanner facts in the
-- strict-domain experiment. Reuse them to preserve the entire continuation,
-- rather than only its single-value projection.
lemma consume_at_landing {before after : ScannerState} {P : SurfPos → Prop}
    {e i c v : SurfPos} {own : Nat}
    (entries : EntryValues before P e)
    (ownMark : own ∈ RegisterWitness.markedCols before)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (mono : IndentStackMono.Mono after) (top : after.currentIndent ≤ (own : Int))
    (consumed : own ∉ RegisterWitness.markedCols after)
    (indent : SIndent own e i) (colon : GLit ':' i c)
    (value : SBlockIndented own .blockOut c v) : EntryValues after P v := by
  apply EntryValues.consume entries ownMark back ?_ indent colon value
  intro x hx
  have le := markedCols_le_of_top mono top x hx
  have ne : x ≠ own := fun h => consumed (h ▸ hx)
  omega

#print axioms consume_at_landing

end R2LandingBridge
