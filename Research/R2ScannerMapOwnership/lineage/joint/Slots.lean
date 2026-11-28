import Research.R2JointFrames.State

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2InvariantPayload
open L4YAML.Proofs.IndentStackMono

namespace R2JointFrames

def Slot (sc : ScannerState) (P : SurfPos → Prop) (n : Nat)
    (ctx : YamlContext) (slot : SurfPos) : Prop :=
  ∀ e, SBlockIndented n ctx slot e → Context sc P e

lemma Slot.compact_sequence {before after : ScannerState} {P : SurfPos → Prop}
    {slot dash next : SurfPos} {n m : Nat} {ctx : YamlContext}
    (payload : Slot before P n ctx slot)
    (shape : levels after = FrameLevel.seq (n+1+m) :: levels before)
    (back : ∀ f ∈ levels before, f.width ∈ RegisterWitness.markedCols after →
      f.width ∈ RegisterWitness.markedCols before)
    (indent : SIndent m slot dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    Slot after P (n+1+m) .blockIn next := by
  intro e node
  change Joint after P (levels after) e
  rw [shape]
  intro z tail
  exact (payload z (SBlockIndented.compactSeq n ctx m slot dash z indent
    (SCompactSeq.mk (n+1+m) dash next e z literal notNs node tail))).restrict_on back

lemma Slot.compact_question {before after : ScannerState} {P : SurfPos → Prop}
    {slot q next : SurfPos} {n m : Nat} {ctx : YamlContext}
    (payload : Slot before P n ctx slot)
    (shape : levels after = FrameLevel.map (n+1+m) :: levels before)
    (marked : n+1+m ∈ RegisterWitness.markedCols after)
    (back : ∀ f ∈ levels before, f.width ∈ RegisterWitness.markedCols after →
      f.width ∈ RegisterWitness.markedCols before)
    (indent : SIndent m slot q) (literal : GLit '?' q next) :
    Slot after P (n+1+m) .blockOut next := by
  intro e key
  change Joint after P (levels after) e
  rw [shape]
  apply Joint.question marked literal ?_ key
  intro v entry z tail
  exact (payload z (SBlockIndented.compactMap n ctx m slot q z indent
    (SCompactMap.mk (n+1+m) q v z entry tail))).restrict_on back

lemma Slot.nodes {sc : ScannerState} {start slot : SurfPos} {own : Nat}
    {rest : List FrameLevel} (payload : Slot sc (SLYamlStream start) own .blockOut slot)
    (shape : levels sc = FrameLevel.map own :: rest)
    (mono : Mono sc) (slots : PendingKeySound.SlotsOk sc) (maps : MarkedMaps sc) :
    NodeValues sc start own slot := by
  intro e node
  have context := payload e (SBlockIndented.node own .blockOut slot e
    (SBlockNode_blockIn_to_blockOut node))
  refine ⟨context.entries mono slots maps, ?_⟩
  intro consumed
  have order := levels_ordered mono
  rw [shape] at order
  have cover := levels_cover_marks slots maps
  rw [shape] at cover
  change Joint sc (SLYamlStream start) (levels sc) e at context
  rw [shape] at context
  simp only [Joint, ite_eq_right consumed] at context
  apply KeyFrames.mapLevel own [] e (by simp)
  intro z tail
  apply KeyFrames.bottom
  apply (context z tail).entries order.2
  intro x marked
  rcases List.mem_cons.mp (cover x marked) with eq | mem
  · have width := congrArg FrameLevel.width eq
    change x = own at width
    exact (consumed (width ▸ marked)).elim
  · exact mem

lemma Joint.sequence_tail {sc : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {k : Nat} {e z : SurfPos}
    (h : Joint sc P (FrameLevel.seq k :: rest) e) (tail : SCompactSeqTail k e z) :
    Joint sc P (FrameLevel.seq k :: rest) z := by
  intro endPos future
  exact h endPos (SCompactSeqTail_append tail future)

lemma Context.resume_sequence {before after : ScannerState} {P : SurfPos → Prop}
    {pre rest : List FrameLevel} {k : Nat} {land dash next e : SurfPos}
    (context : Context before P land)
    (oldShape : levels before = pre ++ FrameLevel.seq k :: rest)
    (newShape : levels after = FrameLevel.seq k :: rest)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (indent : SIndent k land dash) (literal : GLit '-' dash next)
    (notNs : GNot SNsChar next) (node : SBlockIndented k .blockIn next e) :
    Context after P e := by
  change Joint before P (levels before) land at context
  rw [oldShape] at context
  change Joint after P (levels after) e
  rw [newShape]
  exact context.drop.sibling_sequence back indent literal notNs node

-- The actual sequence-tail family now comes from one common mixed stack,
-- including a landing left of the most recent explicit-key slot.
lemma Context.landed_sequence {before after : ScannerState} {start : SurfPos}
    {pre rest : List FrameLevel} {k : Nat} {land dash next : SurfPos}
    (context : Context before (SLYamlStream start) land)
    (oldShape : levels before = pre ++ FrameLevel.seq k :: rest)
    (newShape : levels after = FrameLevel.seq k :: rest)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (mono : Mono after) (slots : PendingKeySound.SlotsOk after) (maps : MarkedMaps after)
    (indent : SIndent k land dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    L4YAML.Proofs.R2SequenceContext.SequenceValues after start k next := by
  intro e node z tail
  have resumed := context.resume_sequence oldShape newShape back indent literal notNs node
  have joint : Joint after (SLYamlStream start) (FrameLevel.seq k :: rest) e := by
    simpa only [Context, newShape] using resumed
  have ended := joint.sequence_tail tail
  have afterContext : Context after (SLYamlStream start) z := by
    simpa only [Context, newShape] using ended
  exact afterContext.entries mono slots maps

#print axioms Slot.compact_sequence
#print axioms Slot.compact_question
#print axioms Slot.nodes
#print axioms Context.landed_sequence

end R2JointFrames
