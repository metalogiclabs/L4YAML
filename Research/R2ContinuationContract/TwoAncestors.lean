import Research.R2ContinuationContract.Controls
import Research.R2ContentCompletion.CompletedValues
import Research.R2SequenceContext.ConcreteContexts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2CompactSlot
open L4YAML.Proofs.R2SequenceContext L4YAML.Proofs.R2ContentCompletion
open L4YAML.CharPredicates R2CompletionControls R2SequenceControls R2CompactControls
open R2ConcreteSuppliers R2ConcreteSequences R2ContinuationControls

namespace R2ContinuationTwoAncestors

def q0 : SurfPos := ⟨source.toList,0⟩
def k0 : SurfPos := ⟨source.toList.drop 1,1⟩
def q2 : SurfPos := ⟨source.toList.drop 2,2⟩
def k2 : SurfPos := ⟨source.toList.drop 3,3⟩
def dash : SurfPos := ⟨source.toList.drop 4,4⟩
def slot : SurfPos := ⟨source.toList.drop 5,5⟩
def gramA : SurfPos := ⟨['\n',' ',' ',' ',' ','-',' ','b','\n',' ',' ',':',' ','c','\n',':',' ','d','\n'],7⟩
def endA : SurfPos := ⟨[' ',' ',' ',' ','-',' ','b','\n',' ',' ',':',' ','c','\n',':',' ','d','\n'],0⟩
def nextDash : SurfPos := ⟨['-',' ','b','\n',' ',' ',':',' ','c','\n',':',' ','d','\n'],4⟩
def nextSlot : SurfPos := ⟨[' ','b','\n',' ',' ',':',' ','c','\n',':',' ','d','\n'],5⟩
def endB : SurfPos := ⟨[' ',' ',':',' ','c','\n',':',' ','d','\n'],0⟩
def colon2 : SurfPos := ⟨[':',' ','c','\n',':',' ','d','\n'],2⟩
def value2 : SurfPos := ⟨[' ','c','\n',':',' ','d','\n'],3⟩
def endC : SurfPos := ⟨[':',' ','d','\n'],0⟩
def value0 : SurfPos := ⟨[' ','d','\n'],1⟩

example : (scalarState source).input.toList.drop (scalarState source).offset = gramA.chars := by decide +kernel
example : (dashState source 1).input.toList.drop (dashState source 1).offset = nextSlot.chars := by decide +kernel
example : afterInner.input.toList.drop afterInner.offset = value2.chars := by decide +kernel
example : afterOuter.input.toList.drop afterOuter.offset = value0.chars := by decide +kernel

-- The root route is constructed at the initialized source, never supplied as
-- a free enclosing-route premise or borrowed from a whole-source theorem.
lemma root_slot : SlotValues (questionState source 0) q0 0 .blockOut k0 := by
  apply SlotValues.of_question (GLit.mk _ 0 : GLit '?' q0 k0)
  · intro v entry z tail
    exact (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q0) (SIndent.zero q0)
      v entry z tail).close
  · intro x hx
    simpa [rootMarks] using hx

lemma inner_slot : SlotValues (questionState source 1) q0 2 .blockOut k2 := by
  exact (SlotValues.compact_question root_slot
    (SIndent.succ 0 _ 1 q2 (SIndent.zero q2) : SIndent 1 k0 q2)
    (GLit.mk _ 2 : GLit '?' q2 k2)
    (by intro x hx; simp only [innerMarks, rootMarks, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega)
    (by intro x hx; simp only [rootMarks, List.mem_singleton] at hx; omega)).1

lemma sequence_initial : SequenceValues (dashState source 0) q0 4 slot := by
  apply SlotValues.compact_sequence inner_slot
    (SIndent.succ 0 _ 3 dash (SIndent.zero dash) : SIndent 1 k2 dash)
    (GLit.mk _ 4 : GLit '-' dash slot) (space_not_ns _ _)
  intro x hx
  simpa [firstDashMarks, innerMarks] using hx

lemma content_reader (e : SurfPos) (comments : SSLComments gramA e) :
    SBlockIndented 4 .blockIn slot e := by
  refine SBlockIndented.node 4 .blockIn _ _
    (SBlockNode.flowInBlock 5 .blockIn slot ⟨'a' :: gramA.chars,6⟩ gramA e ?_ ?_ comments)
  · exact SSeparateLines.inline _ _ _
      (SSeparateInLine.whites _ _ (GPlus.mk _ _ _ (SSWhite.space _ 5) (GStar.nil _)))
  · exact SFlowNode.content _ _ _ _ (SFlowContent.plain _ _ _ _
      (SNsPlainMultiLine.mk _ _ _ _ _
        (SNsPlainOneLine.mk _ _ _ _
          (SNsPlainFirst.nonIndicator _ 'a' _ 6
            (by unfold isNsPlainSafe isNsChar; decide) (by decide))
          (GStar.nil _)) (GStar.nil _)))

lemma completed_family : CompletedValues (scalarState source) q0 4 gramA := by
  apply SequenceValues.complete sequence_initial content_reader
  intro x hx
  simpa [completedMarks, firstDashMarks] using hx

lemma sibling_family : SequenceValues (dashState source 1) q0 4 nextSlot := by
  apply CompletedValues.sibling completed_family
    (SSLComments.withComment gramA endA endA
      (SSBComment.noSep _ _ (SBComment.break _ _ (SBBreak.lf endA.chars 7)))
      (GStar.nil _))
    (SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _
      (SIndent.succ 1 _ 2 _ (SIndent.succ 0 _ 3 _ (SIndent.zero nextDash)))))
    (GLit.mk _ 4 : GLit '-' nextDash nextSlot) (space_not_ns _ _)
  intro x hx
  simpa [siblingMarks, completedMarks] using hx

lemma sibling_key : EntryValues (dashState source 1) (SLYamlStream q0) endB :=
  sibling_family endB
    (SBlockIndented.node 4 .blockIn nextSlot endB
      (letterNode 5 5 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
    endB (SCompactSeqTail.nil _ _)

lemma inner_consumed : EntryValues afterInner (SLYamlStream q0) endC := by
  apply EntryValues.consume sibling_key (own := 2) (by simp [siblingMarks])
    (by intro x hx; simp only [innerConsumedMarks, siblingMarks, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega)
    (by intro x hx; simp only [innerConsumedMarks, List.mem_singleton] at hx; omega)
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero colon2)))
    (GLit.mk _ 2 : GLit ':' colon2 value2)
  exact SBlockIndented.node 2 .blockOut value2 endC
    (SBlockNode_blockIn_to_blockOut
      (letterNode 3 3 'c' endC.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

lemma actual_completed_sibling_two_ancestor_values : SLYamlStream q0 ⟨[],0⟩ := by
  have done : EntryValues afterOuter (SLYamlStream q0) ⟨[],0⟩ := by
    apply EntryValues.consume inner_consumed (own := 0) (by simp [innerConsumedMarks])
      (by intro x hx; simp [outerConsumedMarks] at hx)
      (by intro x hx; simp [outerConsumedMarks] at hx)
      (SIndent.zero endC) (GLit.mk _ 0 : GLit ':' endC value0)
    exact SBlockIndented.node 0 .blockOut value0 ⟨[],0⟩
      (SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'd' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  exact done.close

#print axioms completed_family
#print axioms actual_completed_sibling_two_ancestor_values

end R2ContinuationTwoAncestors
