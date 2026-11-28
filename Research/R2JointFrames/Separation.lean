import Research.R2JointFrames.Slots
import Research.R2SequenceContext.ConcreteContexts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2InvariantPayload
open L4YAML.CharPredicates R2ConcreteSuppliers R2SequenceControls R2ConcreteSequences

namespace R2JointSeparation
open R2JointFrames

def source : String := "- a\n- b\n"
def state : ScannerState := dashState source 0
def afterA : SurfPos := ⟨['-',' ','b','\n'],0⟩
def next : SurfPos := ⟨[' ','b','\n'],1⟩
def afterB : SurfPos := ⟨[],0⟩
def P (e : SurfPos) : Prop := e = afterA

lemma marks : RegisterWitness.markedCols state = [] := by decide +kernel
lemma frames : levels state = [FrameLevel.seq 0] := by decide +kernel
example : (nthDash source 0).isSome = true := by decide +kernel

lemma sibling : SCompactSeqTail 0 afterA afterB :=
  SCompactSeqTail.cons 0 afterA afterA next afterB afterB (SIndent.zero afterA)
    (GLit.mk _ 0 : GLit '-' afterA next) (space_not_ns _ _)
    (SBlockIndented.node 0 .blockIn next afterB
      (letterNode 1 1 'b' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
    (SCompactSeqTail.nil _ _)

-- This is an actual scanner stack and actual grammar sibling, with a
-- result-parametric predicate that exposes exactly the discarded tail.
lemma flat_without_joint : EntryValues state P afterA ∧ ¬Context state P afterA := by
  constructor
  · exact EntryValues.of_no_marks marks rfl
  · intro context
    change Joint state P (levels state) afterA at context
    rw [frames] at context
    have impossible : afterB ≠ afterA := by
      intro eq
      have chars := congrArg SurfPos.chars eq
      cases chars
    exact impossible (context afterB sibling)

lemma no_uniform_reconstruction :
    ¬(∀ (sc : ScannerState) (R : SurfPos → Prop) (e : SurfPos),
      EntryValues sc R e → Context sc R e) := by
  intro rebuild
  exact flat_without_joint.2 (rebuild state P afterA flat_without_joint.1)

#print axioms flat_without_joint
#print axioms no_uniform_reconstruction

end R2JointSeparation
