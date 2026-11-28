import Research.R2ColonSupplier.Controls
import Research.R2ColonComposition.ColonValues

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2InvariantPayload
open L4YAML.Proofs.R2CompactSlot L4YAML.CharPredicates
open R2ConcreteSuppliers R2CompactControls

namespace R2ConsumedSibling

def source : String := "? ? a\n  : b\n  : c\n: d\n"
def q0 : SurfPos := ⟨source.toList,0⟩
def k0 : SurfPos := ⟨source.toList.drop 1,1⟩
def q2 : SurfPos := ⟨source.toList.drop 2,2⟩
def k2 : SurfPos := ⟨source.toList.drop 3,3⟩
def endA : SurfPos := ⟨[' ',' ',':',' ','b','\n',' ',' ',':',' ','c','\n',':',' ','d','\n'],0⟩
def indB : SurfPos := ⟨endA.chars.drop 2,2⟩
def valueB : SurfPos := ⟨endA.chars.drop 3,3⟩
def endB : SurfPos := ⟨[' ',' ',':',' ','c','\n',':',' ','d','\n'],0⟩
def indC : SurfPos := ⟨endB.chars.drop 2,2⟩
def valueC : SurfPos := ⟨endB.chars.drop 3,3⟩
def endC : SurfPos := ⟨[':',' ','d','\n'],0⟩
def valueD : SurfPos := ⟨[' ','d','\n'],1⟩

lemma rootMarks : RegisterWitness.markedCols (questionState source 0) = [0] := by decide +kernel
lemma innerMarks : RegisterWitness.markedCols (questionState source 1) = [0,2] := by decide +kernel
lemma remainingMarks : RegisterWitness.markedCols (afterFirstColon source) = [0] := by decide +kernel
example : (firstColon source).isSome = true := by decide +kernel
example : (nthColon source 1).isSome = true := by decide +kernel

-- A real over-approximating domain names column 2 even after it was consumed.
-- Coverage cannot be used in the reverse direction to infer ownership.
lemma cover_does_not_imply_owner :
    RegisterWitness.MarkedColsIn (afterFirstColon source) [0,2] ∧
      2 ∈ ([0,2] : List Nat) ∧ 2 ∉ RegisterWitness.markedCols (afterFirstColon source) := by
  refine ⟨(RegisterWitness.MarkedColsIn.self _).mono ?_, by decide, ?_⟩
  · intro x hx
    simp only [remainingMarks, List.mem_singleton] at hx
    simp [hx]
  · simp [remainingMarks]

lemma initialized_slot : SlotValues (questionState source 1) q0 2 .blockOut k2 := by
  have root : SlotValues (questionState source 0) q0 0 .blockOut k0 := by
    apply SlotValues.of_question (GLit.mk _ 0 : GLit '?' q0 k0)
    · intro v entry z tail
      exact (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q0) (SIndent.zero q0)
        v entry z tail).close
    · intro x hx
      simpa [rootMarks] using hx
  exact (SlotValues.compact_question root
    (SIndent.succ 0 _ 1 q2 (SIndent.zero q2) : SIndent 1 k0 q2)
    (GLit.mk _ 2 : GLit '?' q2 k2)
    (by intro x hx; simp only [rootMarks,innerMarks,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; omega)
    (by intro x hx; simp only [rootMarks,List.mem_singleton] at hx; omega)).1

lemma first_value_payload :
    SlotValues (afterFirstColon source) q0 2 .blockOut valueB ∧
      NodeValues (afterFirstColon source) q0 2 valueB := by
  apply R2ColonComposition.colon_payload
    (initialized_slot endA (plainAKey 2 3 endA.chars))
    (by simp [innerMarks])
    (by intro x hx; simp only [innerMarks,remainingMarks,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; omega)
    (by intro x hx; simp only [remainingMarks,List.mem_singleton] at hx; omega)
  · exact SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero indB))
  · exact GLit.mk _ 2

-- Column 2 is no longer an explicit-entry owner. Its next colon is an
-- actual empty-key sibling in the still-open mapping.
lemma consumed_owner_sibling : SBlockMapEntry 2 indC endC :=
  SBlockMapEntry.emptyKeyNode 2 indC valueC endC (GLit.mk _ 2)
    (SBlockNode_blockIn_to_blockOut
      (letterNode 3 3 'c' endC.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

lemma actual_consumed_sibling_then_ancestor : SLYamlStream q0 ⟨[],0⟩ := by
  have node : SBlockNode 3 .blockIn valueB endB :=
    letterNode 3 3 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)
  have frame := (first_value_payload.2 endB node).2 (by simp [remainingMarks])
  have tail : SCompactMapTail 2 endB endC :=
    SCompactMapTail.cons 2 endB indC endC endC
      (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero indC)))
      consumed_owner_sibling (SCompactMapTail.nil _ _)
  cases frame with
  | level _ _ _ _ cont =>
    have values := (cont endC tail).close
    have root := values.at (own := 0) (by simp [remainingMarks]) (by decide +kernel)
    exact root.2 endC valueD (SIndent.zero _) (GLit.mk _ 0) ⟨[],0⟩
      (SBlockIndented.node 0 .blockOut valueD ⟨[],0⟩
        (SBlockNode_blockIn_to_blockOut
          (letterNode 1 1 'd' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide))))
      ⟨[],0⟩ (SCompactMapTail.nil _ _)

#print axioms cover_does_not_imply_owner
#print axioms actual_consumed_sibling_then_ancestor

end R2ConsumedSibling
