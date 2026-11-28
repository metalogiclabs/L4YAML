import Research.R2CloseValueFamily.PairRoute
import Research.R2ContinuationContract.Controls
import Research.R2SequenceContext.ConcreteContexts
import Research.R2ContentCompletion.CompletedValues

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2CompactSlot
open L4YAML.Proofs.R2SequenceContext
open L4YAML.CharPredicates R2ConcreteSuppliers R2CompactControls R2CompletionControls

namespace R2CloseConcrete

def source : String := "? ? a\n  : b\n  ? c\n  : d\n: e\n"
def q0 : SurfPos := ⟨source.toList, 0⟩
def k0 : SurfPos := ⟨source.toList.drop 1, 1⟩
def q2 : SurfPos := ⟨source.toList.drop 2, 2⟩
def k2 : SurfPos := ⟨source.toList.drop 3, 3⟩
def gram : SurfPos := ⟨source.toList.drop 5, 5⟩
def endKey : SurfPos := ⟨source.toList.drop 6, 0⟩
def colon2 : SurfPos := ⟨source.toList.drop 8, 2⟩
def value2 : SurfPos := ⟨source.toList.drop 9, 3⟩
def endB : SurfPos := ⟨source.toList.drop 12, 0⟩
def siblingQ : SurfPos := ⟨source.toList.drop 14, 2⟩
def siblingKey : SurfPos := ⟨source.toList.drop 15, 3⟩
def siblingKeyEnd : SurfPos := ⟨source.toList.drop 18, 0⟩
def siblingColon : SurfPos := ⟨source.toList.drop 20, 2⟩
def siblingValue : SurfPos := ⟨source.toList.drop 21, 3⟩
def siblingEnd : SurfPos := ⟨source.toList.drop 24, 0⟩
def rootValue : SurfPos := ⟨source.toList.drop 25, 1⟩

lemma rootMarks : RegisterWitness.markedCols (questionState source 0) = [0] := by decide +kernel
lemma innerMarks : RegisterWitness.markedCols (questionState source 1) = [0, 2] := by decide +kernel
lemma scalarMarks : RegisterWitness.markedCols (scalarState source) = [0, 2] := by decide +kernel
example : (scalarState source).input.toList.drop (scalarState source).offset = gram.chars := by decide +kernel
example : (scalarState source).offset = 5 := by decide +kernel
example : (afterFirstColon source).input.toList.drop (afterFirstColon source).offset = value2.chars := by decide +kernel
example : RegisterWitness.markedCols (afterFirstColon source) = [0] := by decide +kernel
#guard (L4YAML.TokenParser.parseYaml source).isOk

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

lemma node_reader (e : SurfPos) (comments : SSLComments gram e) :
    SBlockNode 3 .blockIn k2 e := by
  refine SBlockNode.flowInBlock 3 .blockIn k2 ⟨'a' :: gram.chars, 4⟩ gram e ?_ ?_ comments
  · exact SSeparateLines.inline _ _ _
      (SSeparateInLine.whites _ _ (GPlus.mk _ _ _ (SSWhite.space _ 3) (GStar.nil _)))
  · exact SFlowNode.content _ _ _ _ (SFlowContent.plain _ _ _ _
      (SNsPlainMultiLine.mk _ _ _ _ _
        (SNsPlainOneLine.mk _ _ _ _
          (SNsPlainFirst.nonIndicator _ 'a' _ 4
            (by unfold isNsPlainSafe isNsChar; decide) (by decide))
          (GStar.nil _)) (GStar.nil _)))

lemma initialized_pack :
    ∃ ns : List Nat, RegisterWitness.MarkedColsIn (scalarState source) ns ∧
      (∀ own ∈ ns, ∀ m i c, SSLComments gram m → SIndent own m i → GLit ':' i c →
        ∀ v, SBlockIndented own .blockOut c v →
          R2UnmarkedOwner.AncestorValue (scalarState source) q0 own v) ∧
      (∀ own ∈ ns, ∀ a ∈ RegisterWitness.markedCols (scalarState source), a < own →
        ∀ m i c, SSLComments gram m → SIndent own m i → GLit ':' i c →
        ∀ v, SBlockIndented own .blockOut c v → ExplValueLine q0 a v) := by
  apply R2CloseValueFamily.wholePack
  intro own marked m i c comments indent literal v value
  have family : EntryValues (scalarState source) (SLYamlStream q0) m := EntryValues.restrict_state
    (inner_slot m (SBlockIndented.node 2 .blockOut k2 m
      (SBlockNode_blockIn_to_blockOut (node_reader m comments))))
    (fun x hx => by simpa [innerMarks, scalarMarks] using hx)
  exact R2UnmarkedOwner.AncestorValue.of_entries family marked (fun _ h => h) indent literal value

lemma actual_map_sibling : SCompactMapTail 2 endB siblingEnd := by
  refine SCompactMapTail.cons 2 endB siblingQ siblingEnd siblingEnd ?_ ?_ (SCompactMapTail.nil _ _)
  · exact SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero siblingQ))
  · refine SBlockMapEntry.explicit 2 siblingQ siblingKey siblingKeyEnd siblingColon siblingValue siblingEnd
      (GLit.mk _ 2) ?_ ?_ (GLit.mk _ 2) ?_
    · exact SBlockIndented.node 2 .blockOut _ _
        (SBlockNode_blockIn_to_blockOut
          (letterNode 3 3 'c' siblingKeyEnd.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
    · exact SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero siblingColon))
    · exact SBlockIndented.node 2 .blockOut _ _
        (SBlockNode_blockIn_to_blockOut
          (letterNode 3 3 'd' siblingEnd.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

-- The very pack retained by the actual content/flow interfaces is spent
-- across a non-nil consumed mapping tail, then the surviving ancestor.
lemma actual_pack_sibling_then_ancestor : SLYamlStream q0 ⟨[], 0⟩ := by
  obtain ⟨ns, domain, routes, _pairs⟩ := initialized_pack
  have retained := routes 2 (domain.mem (by simp [scalarMarks])) endKey colon2 value2
    (SSLComments.withComment gram endKey endKey
      (SSBComment.noSep _ _ (SBComment.break _ _ (SBBreak.lf endKey.chars 5))) (GStar.nil _))
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero colon2)))
    (GLit.mk _ 2 : GLit ':' colon2 value2) endB
    (SBlockIndented.node 2 .blockOut value2 endB
      (SBlockNode_blockIn_to_blockOut
        (letterNode 3 3 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide))))
  have lower := retained.2 siblingEnd actual_map_sibling
  have ancestor := lower.valueLine (own := 0) (by simp [scalarMarks]) (by decide)
  exact (ancestor siblingEnd rootValue (SIndent.zero _) (GLit.mk _ 0) ⟨[], 0⟩
    (SBlockIndented.node 0 .blockOut _ _
      (SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'e' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide))))).close

#print axioms actual_pack_sibling_then_ancestor

end R2CloseConcrete
