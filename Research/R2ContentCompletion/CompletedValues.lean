import Research.R2SequenceContext.SequenceValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.R2CompactSlot L4YAML.Proofs.R2SequenceContext

namespace L4YAML.Proofs.R2ContentCompletion

def CompletedValues (sc : ScannerState) (start : SurfPos) (n : Nat) (gram : SurfPos) : Prop :=
  ∀ e, SSLComments gram e →
    ∀ z, SCompactSeqTail n e z → EntryValues sc (SLYamlStream start) z

def NodeSequenceValues (sc : ScannerState) (start : SurfPos) (n : Nat) (slot : SurfPos) : Prop :=
  ∀ e, SBlockNode (n + 1) .blockIn slot e →
    ∀ z, SCompactSeqTail n e z → EntryValues sc (SLYamlStream start) z

lemma SequenceValues.complete {before after : ScannerState}
    {start slot gram : SurfPos} {n : Nat} (payload : SequenceValues before start n slot)
    (reader : ∀ e, SSLComments gram e → SBlockIndented n .blockIn slot e)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    CompletedValues after start n gram :=
  fun e comments z tail => EntryValues.restrict_state (payload e (reader e comments) z tail) back

lemma NodeSequenceValues.complete {before after : ScannerState}
    {start slot gram : SurfPos} {n : Nat} (payload : NodeSequenceValues before start n slot)
    (reader : ∀ e, SSLComments gram e → SBlockNode (n + 1) .blockIn slot e)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    CompletedValues after start n gram :=
  fun e comments z tail => EntryValues.restrict_state (payload e (reader e comments) z tail) back

lemma NodeSequenceValues.restrict_state {before after : ScannerState}
    {start slot : SurfPos} {n : Nat} (payload : NodeSequenceValues before start n slot)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    NodeSequenceValues after start n slot :=
  fun e node z tail => EntryValues.restrict_state (payload e node z tail) back

lemma SequenceValues.nodes {before after : ScannerState}
    {start slot : SurfPos} {n : Nat} (payload : SequenceValues before start n slot)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    NodeSequenceValues after start n slot := by
  intro e node z tail
  exact EntryValues.restrict_state
    (payload e (SBlockIndented.node n .blockIn slot e node) z tail) back

lemma CompletedValues.sibling {before after : ScannerState}
    {start gram land dash slot : SurfPos} {n : Nat}
    (payload : CompletedValues before start n gram) (comments : SSLComments gram land)
    (indent : SIndent n land dash) (literal : GLit '-' dash slot) (notNs : GNot SNsChar slot)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    SequenceValues after start n slot := by
  intro e node z tail
  exact EntryValues.restrict_state (payload land comments z
    (SCompactSeqTail.cons n land dash slot e z indent literal notNs node tail)) back

#print axioms SequenceValues.complete
#print axioms NodeSequenceValues.complete
#print axioms NodeSequenceValues.restrict_state
#print axioms SequenceValues.nodes
#print axioms CompletedValues.sibling

end L4YAML.Proofs.R2ContentCompletion
