import Research.R2MandatoryContext.Controls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2InvariantPayload
open R2JointFrames R2ActualJointStep

namespace R2MandatoryContext

-- These are the mandatory node and entry completion functions themselves.
-- They store no extra position, frame list, snapshot or alternative.
def Node (s : ScannerState) (P : SurfPos → Prop) (n : Nat) (slot : SurfPos) : Prop :=
  ∀ e, SBlockNode n .blockIn slot e → Context s P e

def Sequence (s : ScannerState) (P : SurfPos → Prop) (n : Nat) (slot : SurfPos) : Prop :=
  ∀ e, SBlockIndented n .blockIn slot e →
    ∀ z, SCompactSeqTail n e z → Context s P z

lemma sequence_push {s t : ScannerState} (step : scanBlockEntry s = .ok t)
    (flow : s.inFlow = false) (pushed : s.currentIndent < (s.col : Int)) :
    levels t = FrameLevel.seq s.col :: levels s := by
  have shape := scanBlockEntry_indents flow step
  rw [pushSequenceIndent, if_pos pushed] at shape
  have result := levels_push shape
  simpa [frame, show ¬(s.col : Int) < 0 by omega] using result

lemma actual_compact_sequence {s t : ScannerState} {P : SurfPos → Prop}
    {slot dash next : SurfPos} {n m : Nat} {ctx : YamlContext}
    (step : scanBlockEntry s = .ok t) (flow : s.inFlow = false)
    (slots : SlotsOk s) (column : s.col = n+1+m)
    (pushed : s.currentIndent < (s.col : Int))
    (payload : Slot s P n ctx slot)
    (indent : SIndent m slot dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    Sequence t P (n+1+m) next := by
  have shape := sequence_push step flow pushed
  rw [column] at shape
  have back := RegisterWitness.scanBlockEntry_markedCols flow step
    (RegisterWitness.MarkedColsIn.self s) slots
  have opened := payload.compact_sequence shape (fun _ _ h => back.mem h) indent literal notNs
  intro e node z tail
  have joint := opened e node
  change Joint t P (levels t) e at joint
  rw [shape] at joint
  exact (show Context t P z from by
    change Joint t P (levels t) z
    rw [shape]
    exact joint.sequence_tail tail)

-- A new question at the current map width is a sibling even when the old
-- explicit value was omitted. It is not the compact-push case.
lemma same_map_question {s t : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {land q next : SurfPos} {own : Nat}
    (context : Context s P land)
    (oldShape : levels s = FrameLevel.map own :: rest)
    (newShape : levels t = FrameLevel.map own :: rest)
    (marked : own ∈ RegisterWitness.markedCols t)
    (back : ∀ f ∈ rest, f.width ∈ RegisterWitness.markedCols t →
      f.width ∈ RegisterWitness.markedCols s)
    (indent : SIndent own land q) (literal : GLit '?' q next) :
    Slot t P own .blockOut next := by
  have before : Joint s P (FrameLevel.map own :: rest) land := by
    simpa only [Context, oldShape] using context
  have tailRoute : ∀ z, SCompactMapTail own land z → Joint s P rest z := by
    by_cases oldMarked : own ∈ RegisterWitness.markedCols s
    · exact (show EntryStep (Joint s P rest) own land from by
        simpa only [Joint, if_pos oldMarked] using before).1
    · exact (show ∀ z, SCompactMapTail own land z → Joint s P rest z from by
        simpa only [Joint, if_neg oldMarked] using before)
  intro e key
  change Joint t P (levels t) e
  rw [newShape]
  apply Joint.question marked literal ?_ key
  intro v entry z tail
  exact (tailRoute z (SCompactMapTail.cons own land q v z indent entry tail)).restrict_on back

-- First-document births use existing grammar evidence at the actual virgin
-- park. There is no incoming semantic Context premise.
lemma first_question {s : ScannerState} {start land q next : SurfPos} {own : Nat}
    (shape : levels s = [FrameLevel.map own])
    (marked : own ∈ RegisterWitness.markedCols s)
    (lineStart : land.col = 0) (prefix : GStar SLDocumentPrefix start land)
    (indent : SIndent own land q) (literal : GLit '?' q next) :
    Slot s (SLYamlStream start) own .blockOut next := by
  intro e key
  change Joint s (SLYamlStream start) (levels s) e
  rw [shape]
  apply Joint.question marked literal ?_ key
  intro v entry z tail
  exact (nodocMapRouteF lineStart prefix indent v entry z tail).close

lemma first_value {s : ScannerState} {start land q next : SurfPos} {own : Nat}
    (shape : levels s = [FrameLevel.map own])
    (unmarked : own ∉ RegisterWitness.markedCols s)
    (lineStart : land.col = 0) (prefix : GStar SLDocumentPrefix start land)
    (indent : SIndent own land q)
    (entry : ∀ e, SBlockNode (own+1) .blockIn next e → SBlockMapEntry own q e) :
    Node s (SLYamlStream start) (own+1) next := by
  intro e node
  change Joint s (SLYamlStream start) (levels s) e
  rw [shape]
  simp only [Joint, if_neg unmarked]
  intro z tail
  exact (nodocMapRouteF lineStart prefix indent e (entry e node) z tail).close

-- All three colon births have the same mandatory node context. The grammar
-- constructor distinguishes keyless, implicit and decorated entry heads.
lemma first_keyless {s : ScannerState} {start land colon next : SurfPos} {own : Nat}
    (shape : levels s = [FrameLevel.map own])
    (unmarked : own ∉ RegisterWitness.markedCols s)
    (lineStart : land.col = 0) (prefix : GStar SLDocumentPrefix start land)
    (indent : SIndent own land colon) (literal : GLit ':' colon next) :
    Node s (SLYamlStream start) (own+1) next :=
  first_value shape unmarked lineStart prefix indent
    (fun e node => SBlockMapEntry.emptyKeyNode own colon next e literal
      (SBlockNode_blockIn_to_blockOut node))

lemma first_implicit {s : ScannerState} {start land key keyEnd colon next : SurfPos} {own : Nat}
    (shape : levels s = [FrameLevel.map own])
    (unmarked : own ∉ RegisterWitness.markedCols s)
    (lineStart : land.col = 0) (prefix : GStar SLDocumentPrefix start land)
    (indent : SIndent own land key) (head : ImplicitKeyHead key keyEnd)
    (white : GStar SSWhite keyEnd colon) (literal : GLit ':' colon next) :
    Node s (SLYamlStream start) (own+1) next :=
  first_value shape unmarked lineStart prefix indent
    (fun e node => SBlockMapEntry.implicitKeyNode own key colon next e
      (SImplicitYamlKey.oneLine key keyEnd colon head white) literal
      (SBlockNode_blockIn_to_blockOut node))

#print axioms actual_compact_sequence
#print axioms same_map_question
#print axioms first_question
#print axioms first_keyless
#print axioms first_implicit

end R2MandatoryContext
