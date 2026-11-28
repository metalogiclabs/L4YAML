import Research.R2ColonSupplier.ConsumedSibling
import Research.R2CloseValueFamily.PairRoute

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.CharPredicates
open R2ConcreteSuppliers R2CompactControls R2ConsumedSibling

namespace R2CloseConcrete

-- The source is initialized in the retained independent supplier experiment.
-- Build this value directly from its entry family, not its finished proof.
lemma initialized_whole_value :
    R2UnmarkedOwner.AncestorValue (afterFirstColon source) q0 2 endB := by
  apply R2UnmarkedOwner.AncestorValue.of_entries
    (initialized_slot endA (plainAKey 2 3 endA.chars))
    (by simp [innerMarks])
    (by intro x hx; simp only [remainingMarks, innerMarks, List.mem_singleton,
      List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega)
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero indB)))
    (GLit.mk _ 2 : GLit ':' indB valueB)
  exact SBlockIndented.node 2 .blockOut valueB endB
    (SBlockNode_blockIn_to_blockOut
      (letterNode 3 3 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

lemma sibling_tail : SCompactMapTail 2 endB endC :=
  SCompactMapTail.cons 2 endB indC endC endC
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero indC)))
    consumed_owner_sibling (SCompactMapTail.nil _ _)

-- A non-nil mapping sibling is consumed while column 2 is unmarked. The
-- retained family supplies column 0, which then consumes its value to EOF.
lemma initialized_sibling_then_ancestor : SLYamlStream q0 ⟨[],0⟩ := by
  have retained := initialized_whole_value.2 endC sibling_tail
  have root := retained.at (own := 0) (by simp [remainingMarks]) (by decide)
  exact root.2 endC valueD (SIndent.zero _) (GLit.mk _ 0) ⟨[],0⟩
    (SBlockIndented.node 0 .blockOut valueD ⟨[],0⟩
      (SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'd' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide))))
    ⟨[],0⟩ (SCompactMapTail.nil _ _)

#print axioms initialized_whole_value
#print axioms initialized_sibling_then_ancestor

end R2CloseConcrete
