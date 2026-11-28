import Research.R2ScannerMapOwnership.JointFixture
import Research.R2SequenceContext.ConcreteContexts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.CharPredicates R2ConcreteSuppliers R2CompactControls
open R2SequenceControls R2ConcreteSequences

namespace R2ActualJointWitness
open R2JointFrames R2ActualJointStep

lemma actual_inner_key : Context stateA (SLYamlStream q0) endA :=
  context_transport inner_key (by decide +kernel) (by decide +kernel)

lemma actual_inner_value_slot : Slot stateValue4 (SLYamlStream q0) 4 .blockOut value4 := by
  have payload := initialized_explicit_colon source 4
    (s := stateA) (prep := prepA) (t := stateValue4) (line := 0)
    (start := q0) (e := endA) (i := colon4) (c := value4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) actual_inner_key
    (by rw [prepA_column]; exact SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _
      (SIndent.succ 1 _ 2 _ (SIndent.succ 0 _ 3 _ (SIndent.zero colon4)))))
    (GLit.mk _ 4)
  simpa only [prepA_column] using payload.1

lemma actual_inner_value : Context stateB (SLYamlStream q0) endB := by
  have value : SBlockIndented 4 .blockOut value4 endB :=
    SBlockIndented.node 4 .blockOut value4 endB
      (SBlockNode_blockIn_to_blockOut
        (letterNode 5 5 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  exact context_transport (actual_inner_value_slot endB value)
    (by decide +kernel) (by decide +kernel)

lemma sibling_content : SBlockIndented 2 .blockIn nextSlot endC :=
  SBlockIndented.node 2 .blockIn nextSlot endC
    (letterNode 3 3 'c' endC.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide))

lemma actual_sibling_slot : Slot stateSibling (SLYamlStream q0) 2 .blockIn nextSlot := by
  exact landed_sequence_context (s := stateB) (prep := prepB) (t := stateSibling)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) actual_inner_value
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero nextDash)))
    (GLit.mk _ 2) (space_not_ns _ _)

lemma actual_landed_family :
    L4YAML.Proofs.R2SequenceContext.SequenceValues stateSibling q0 2 nextSlot := by
  exact initialized_landed_sequence source 6 (s := stateB) (prep := prepB) (t := stateSibling)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    actual_inner_value
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero nextDash)))
    (GLit.mk _ 2) (space_not_ns _ _)

lemma actual_sibling : Context stateC (SLYamlStream q0) endC :=
  context_transport (actual_sibling_slot endC sibling_content)
    (by decide +kernel) (by decide +kernel)

lemma actual_root_value_slot : Slot stateValue0 (SLYamlStream q0) 0 .blockOut value0 := by
  have payload := initialized_explicit_colon source 8
    (s := stateC) (prep := prepC) (t := stateValue0) (line := 0)
    (start := q0) (e := endC) (i := endC) (c := value0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) actual_sibling
    (by rw [prepC_column]; exact SIndent.zero endC)
    (GLit.mk _ 0)
  simpa only [prepC_column] using payload.1

lemma initialized_complete : SLYamlStream q0 ⟨[],0⟩ := by
  have value : SBlockIndented 0 .blockOut value0 ⟨[],0⟩ :=
    SBlockIndented.node 0 .blockOut value0 ⟨[],0⟩
      (SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'd' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  exact (actual_root_value_slot ⟨[],0⟩ value).close

#print axioms initialized_complete
#print axioms actual_landed_family

end R2ActualJointWitness
