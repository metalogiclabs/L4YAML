import Research.R2CompactSlot.SlotValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2CompactSlot

namespace L4YAML.Proofs.R2SequenceContext

def SequenceValues (sc : ScannerState) (start : SurfPos) (n : Nat) (slot : SurfPos) : Prop :=
  ∀ e, SBlockIndented n .blockIn slot e →
    ∀ z, SCompactSeqTail n e z → EntryValues sc (SLYamlStream start) z

lemma EntryValues.restrict_state {before after : ScannerState} {P : SurfPos → Prop}
    {e : SurfPos} (h : EntryValues before P e)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    EntryValues after P e :=
  ValuesBelow.restrict (EntryValues.below h (columnCeiling after)) (fun x _ => back x)

lemma SequenceValues.slot {sc : ScannerState} {start slot : SurfPos} {n : Nat}
    (payload : SequenceValues sc start n slot) : SlotValues sc start n .blockIn slot :=
  fun e node => payload e node e (SCompactSeqTail.nil n e)

lemma SlotValues.compact_sequence {before after : ScannerState}
    {start slot dash next : SurfPos} {n m : Nat} {ctx : YamlContext}
    (payload : SlotValues before start n ctx slot)
    (indent : SIndent m slot dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    SequenceValues after start (n + 1 + m) next := by
  intro e node z tail
  exact EntryValues.restrict_state (payload z
    (SBlockIndented.compactSeq n ctx m slot dash z indent
      (SCompactSeq.mk (n + 1 + m) dash next e z literal notNs node tail))) back

lemma SequenceValues.sibling {before after : ScannerState}
    {start slot land dash next : SurfPos} {n : Nat}
    (payload : SequenceValues before start n slot)
    (completed : SBlockIndented n .blockIn slot land)
    (indent : SIndent n land dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    SequenceValues after start n next := by
  intro e node z tail
  exact EntryValues.restrict_state (payload land completed z
    (SCompactSeqTail.cons n land dash next e z indent literal notNs node tail)) back

lemma SequenceValues.nested {before after : ScannerState}
    {start slot land dash next : SurfPos} {n k : Nat}
    (payload : SequenceValues before start n slot) (lt : n < k)
    (comments : SSLComments slot land) (indent : SIndent k land dash)
    (literal : GLit '-' dash next) (notNs : GNot SNsChar next)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    SequenceValues after start k next := by
  intro e node z tail
  exact EntryValues.restrict_state (payload z
    (SBlockIndented.node n .blockIn slot z
      (nestedBlockSeq lt comments (SBlockSeqEntries_of_compactTail indent literal notNs node tail)))
    z (SCompactSeqTail.nil n z)) back

lemma SequenceValues.compact {before after : ScannerState}
    {start slot dash next : SurfPos} {n m : Nat}
    (payload : SequenceValues before start n slot)
    (indent : SIndent m slot dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    SequenceValues after start (n + 1 + m) next :=
  SlotValues.compact_sequence (SequenceValues.slot payload) indent literal notNs back

#print axioms SequenceValues.sibling
#print axioms SequenceValues.nested
#print axioms SequenceValues.compact
#print axioms SlotValues.compact_sequence

end L4YAML.Proofs.R2SequenceContext
