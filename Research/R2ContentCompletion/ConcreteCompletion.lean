import Research.R2ContentCompletion.Controls
import Research.R2ContentCompletion.CompletedValues
import Research.R2SequenceContext.ConcreteContexts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2CompactSlot
open L4YAML.Proofs.R2SequenceContext L4YAML.Proofs.R2ContentCompletion
open L4YAML.CharPredicates R2CompletionControls R2SequenceControls
open R2ConcreteSuppliers R2ConcreteSequences

namespace R2ConcreteCompletion

def gramA : SurfPos := ⟨['\n',' ',' ','-',' ','b','\n',':',' ','c','\n'],5⟩

example : plain = siblings := rfl
example : (scalarState plain).input.toList.drop (scalarState plain).offset = gramA.chars := by decide +kernel
example : (scalarState plain).col = gramA.col := by decide +kernel

-- Same actual plain-node grammar reader as the content producer, with its
-- future comments supplied by the completed-content continuation.
lemma actual_content_reader (e : SurfPos) (comments : SSLComments gramA e) :
    SBlockIndented 2 .blockIn Sibling.slot e := by
  refine SBlockIndented.node 2 .blockIn _ _
    (SBlockNode.flowInBlock 3 .blockIn Sibling.slot
      ⟨'a' :: gramA.chars,4⟩ gramA e ?_ ?_ comments)
  · exact SSeparateLines.inline _ _ _
      (SSeparateInLine.whites _ _ (GPlus.mk _ _ _ (SSWhite.space _ 3) (GStar.nil _)))
  · exact SFlowNode.content _ _ _ _ (SFlowContent.plain _ _ _ _
      (SNsPlainMultiLine.mk _ _ _ _ _
        (SNsPlainOneLine.mk _ _ _ _
          (SNsPlainFirst.nonIndicator _ 'a' _ 4
            (by unfold isNsPlainSafe isNsChar; decide) (by decide))
          (GStar.nil _)) (GStar.nil _)))

lemma initialized_completed_family : CompletedValues (scalarState plain) Sibling.q0 2 gramA := by
  apply SequenceValues.complete Sibling.initial_context actual_content_reader
  intro x hx
  simpa [plainMarks, siblingsMarks] using hx

lemma actual_sibling_family :
    SequenceValues (dashState siblings 1) Sibling.q0 2 Sibling.nextSlot := by
  apply CompletedValues.sibling initialized_completed_family
    (SSLComments.withComment gramA Sibling.endA Sibling.endA
      (SSBComment.noSep _ _ (SBComment.break _ _ (SBBreak.lf Sibling.endA.chars 5)))
      (GStar.nil _))
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero Sibling.nextDash)))
    (GLit.mk _ 2 : GLit '-' Sibling.nextDash Sibling.nextSlot) (space_not_ns _ _)
  intro x hx
  simpa [Sibling.nextMarks, plainMarks] using hx

-- End-to-end grammar from the initialized completed scalar, through an actual
-- sequence sibling, then the pending root value. No free root route is used.
lemma actual_completed_sibling_ancestor : SLYamlStream Sibling.q0 ⟨[],0⟩ := by
  have family := actual_sibling_family Sibling.endB
    (SBlockIndented.node 2 .blockIn Sibling.nextSlot Sibling.endB
      (letterNode 3 3 'b' Sibling.endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
    Sibling.endB (SCompactSeqTail.nil _ _)
  have outer := family.at (own := 0) (by simp [Sibling.nextMarks])
    (marked_lt_ceiling (by simp [Sibling.nextMarks] : 0 ∈ RegisterWitness.markedCols (dashState siblings 1)))
  exact outer.2 Sibling.endB Sibling.value0 (SIndent.zero _) (GLit.mk _ 0) ⟨[],0⟩
    (SBlockIndented.node 0 .blockOut Sibling.value0 ⟨[],0⟩
      (SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'c' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide))))
    ⟨[],0⟩ (SCompactMapTail.nil _ _)

#print axioms initialized_completed_family
#print axioms actual_completed_sibling_ancestor

end R2ConcreteCompletion
