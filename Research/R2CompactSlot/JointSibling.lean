import Research.R2CompactSlot.ConcreteSlots

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.R2InvariantPayload L4YAML.Proofs.R2CompactSlot
open L4YAML.CharPredicates R2CompactControls R2ConcreteSuppliers

namespace R2JointSibling

-- Already exercised by the pre-proof public-parser control in Controls.lean.
def source : String := "? ? a\n  : b\n  ? c\n  : d\n: e\n"
def q0 : SurfPos := ⟨source.toList, 0⟩
def k0 : SurfPos := ⟨source.toList.drop 1, 1⟩
def q2 : SurfPos := ⟨source.toList.drop 2, 2⟩
def k2 : SurfPos := ⟨source.toList.drop 3, 3⟩
def endA : SurfPos := ⟨[' ', ' ', ':', ' ', 'b', '\n', ' ', ' ', '?', ' ', 'c', '\n',
  ' ', ' ', ':', ' ', 'd', '\n', ':', ' ', 'e', '\n'], 0⟩
def indB : SurfPos := ⟨endA.chars.drop 2, 2⟩
def valueB : SurfPos := ⟨endA.chars.drop 3, 3⟩
def endB : SurfPos := ⟨[' ', ' ', '?', ' ', 'c', '\n', ' ', ' ', ':', ' ', 'd', '\n',
  ':', ' ', 'e', '\n'], 0⟩
def siblingQ : SurfPos := ⟨endB.chars.drop 2, 2⟩
def siblingKey : SurfPos := ⟨endB.chars.drop 3, 3⟩
def endC : SurfPos := ⟨[' ', ' ', ':', ' ', 'd', '\n', ':', ' ', 'e', '\n'], 0⟩
def indD : SurfPos := ⟨endC.chars.drop 2, 2⟩
def valueD : SurfPos := ⟨endC.chars.drop 3, 3⟩
def endD : SurfPos := ⟨[':', ' ', 'e', '\n'], 0⟩
def valueE : SurfPos := ⟨[' ', 'e', '\n'], 1⟩

lemma rootMarks : RegisterWitness.markedCols (questionState source 0) = [0] := by decide +kernel
lemma innerMarks : RegisterWitness.markedCols (questionState source 1) = [0,2] := by decide +kernel
example : (nthQuestion source 1).isSome = true := by decide +kernel
example : (questionState source 1).offset = 3 ∧ (questionState source 1).col = 3 := by decide +kernel
example : RegisterWitness.markedCols (afterFirstColon source) = [0] := by decide +kernel

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
    (by intro x hx; simp only [rootMarks, innerMarks, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega)
    (by intro x hx; simp only [rootMarks, List.mem_singleton] at hx; omega)).1

lemma sibling_entry : SBlockMapEntry 2 siblingQ endD := by
  apply SBlockMapEntry.explicit 2 siblingQ siblingKey endC indD valueD endD
  · exact GLit.mk _ 2
  · exact SBlockIndented.node 2 .blockOut _ _
      (NodeProduction.SBlockNode_blockIn_to_blockOut
        (letterNode 3 3 'c' endC.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  · exact SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero indD))
  · exact GLit.mk _ 2
  · exact SBlockIndented.node 2 .blockOut _ _
      (NodeProduction.SBlockNode_blockIn_to_blockOut
        (letterNode 3 3 'd' endD.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

-- A non-nil inner sibling tail and a later ancestor value are both spent in
-- the same source-to-EOF proof, from the initialized wide slot.
lemma actual_sibling_then_ancestor : SLYamlStream q0 ⟨[], 0⟩ := by
  have key := initialized_slot endA (plainAKey 2 3 endA.chars)
  have inner := key.at (own := 2) (by simp [innerMarks])
    (marked_lt_ceiling (by simp [innerMarks] : 2 ∈ RegisterWitness.markedCols (questionState source 1)))
  have tail : SCompactMapTail 2 endB endD :=
    SCompactMapTail.cons 2 endB siblingQ endD endD
      (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero siblingQ)))
      sibling_entry (SCompactMapTail.nil _ _)
  have afterD := inner.2 indB valueB
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero indB)))
    (GLit.mk _ 2 : GLit ':' indB valueB) endB
    (SBlockIndented.node 2 .blockOut valueB endB
      (NodeProduction.SBlockNode_blockIn_to_blockOut
        (letterNode 3 3 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide))))
    endD tail
  have outer := afterD.at (own := 0) (by simp [innerMarks]) (by decide)
  exact outer.2 endD valueE (SIndent.zero _) (GLit.mk _ 0) ⟨[], 0⟩
    (SBlockIndented.node 0 .blockOut valueE ⟨[], 0⟩
      (NodeProduction.SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'e' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide))))
    ⟨[], 0⟩ (SCompactMapTail.nil _ _)

#print axioms actual_sibling_then_ancestor

end R2JointSibling
