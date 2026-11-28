import Research.R2ContinuationContract.TwoAncestors
import Research.R2UnmarkedOwner.AncestorValue

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.CharPredicates
open R2ConcreteSuppliers R2ContinuationControls R2ContinuationTwoAncestors

namespace R2UnmarkedOwner

-- Reuse the independently initialized parent construction through an actual
-- non-nil sequence sibling. Here column 2 is consumed and absent, but column
-- 0 and the consumed column's arbitrary mapping tail are both retained.
lemma initialized_unmarked_value : AncestorValue afterInner q0 2 endC := by
  apply AncestorValue.of_entries sibling_key (by simp [siblingMarks])
    (fun x hx => by simp only [innerConsumedMarks, List.mem_singleton] at hx; subst x; simp [siblingMarks])
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero colon2)))
    (GLit.mk _ 2 : GLit ':' colon2 value2)
  exact SBlockIndented.node 2 .blockOut value2 endC
    (SBlockNode_blockIn_to_blockOut
      (letterNode 3 3 'c' endC.chars (by unfold isNsPlainSafe isNsChar; decide)
        (by decide)))

example : 2 ∉ RegisterWitness.markedCols afterInner ∧
    0 ∈ RegisterWitness.markedCols afterInner := by simp [innerConsumedMarks]

lemma initialized_unmarked_then_ancestor : SLYamlStream q0 ⟨[],0⟩ := by
  have ancestor := initialized_unmarked_value.pair (ancestor := 0)
    (by simp [innerConsumedMarks]) (by decide)
  exact (ancestor endC value0 (SIndent.zero endC)
    (GLit.mk _ 0 : GLit ':' endC value0) ⟨[],0⟩
    (SBlockIndented.node 0 .blockOut value0 ⟨[],0⟩
      (SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'd' [] (by unfold isNsPlainSafe isNsChar; decide)
          (by decide))))).close

#print axioms initialized_unmarked_value
#print axioms initialized_unmarked_then_ancestor

end R2UnmarkedOwner
