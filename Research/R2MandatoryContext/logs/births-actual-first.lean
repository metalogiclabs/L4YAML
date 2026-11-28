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
  rw [pushSequenceIndent, ite_eq_left pushed] at shape
  change t.indents = s.indents.push {column := (s.col : Int), isSequence := true} at shape
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
        simpa only [Joint, ite_eq_left oldMarked] using before).1
    · exact (show ∀ z, SCompactMapTail own land z → Joint s P rest z from by
        simpa only [Joint, ite_eq_right oldMarked] using before)
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
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land q) (literal : GLit '?' q next) :
    Slot s (SLYamlStream start) own .blockOut next := by
  intro e key
  change Joint s (SLYamlStream start) (levels s) e
  rw [shape]
  apply Joint.question marked literal ?_ key
  intro v entry z tail
  exact (nodocMapRouteF lineStart prefixes indent v entry z tail).close

lemma first_value {s : ScannerState} {start land q next : SurfPos} {own : Nat}
    (shape : levels s = [FrameLevel.map own])
    (unmarked : own ∉ RegisterWitness.markedCols s)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land q)
    (entry : ∀ e, SBlockNode (own+1) .blockIn next e → SBlockMapEntry own q e) :
    Node s (SLYamlStream start) (own+1) next := by
  intro e node
  change Joint s (SLYamlStream start) (levels s) e
  rw [shape]
  simp only [Joint, ite_eq_right unmarked]
  intro z tail
  exact (nodocMapRouteF lineStart prefixes indent e (entry e node) z tail).close

-- All three colon births have the same mandatory node context. The grammar
-- constructor distinguishes keyless, implicit and decorated entry heads.
lemma first_keyless {s : ScannerState} {start land colon next : SurfPos} {own : Nat}
    (shape : levels s = [FrameLevel.map own])
    (unmarked : own ∉ RegisterWitness.markedCols s)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land colon) (literal : GLit ':' colon next) :
    Node s (SLYamlStream start) (own+1) next :=
  first_value shape unmarked lineStart prefixes indent
    (fun e node => SBlockMapEntry.emptyKeyNode own colon next e literal
      (SBlockNode_blockIn_to_blockOut node))

lemma first_implicit {s : ScannerState} {start land key keyEnd colon next : SurfPos} {own : Nat}
    (shape : levels s = [FrameLevel.map own])
    (unmarked : own ∉ RegisterWitness.markedCols s)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land key) (head : ImplicitKeyHead key keyEnd)
    (white : GStar SSWhite keyEnd colon) (literal : GLit ':' colon next) :
    Node s (SLYamlStream start) (own+1) next :=
  first_value shape unmarked lineStart prefixes indent
    (fun e node => SBlockMapEntry.implicitKeyNode own key colon next e
      (implicitKeyHead_to_SImplicitKey head white) literal
      (SBlockNode_blockIn_to_blockOut node))

lemma first_properties {s : ScannerState} {start land key keyEnd colon next : SurfPos} {own : Nat}
    (shape : levels s = [FrameLevel.map own])
    (unmarked : own ∉ RegisterWitness.markedCols s)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land key) (props : SCNsProperties 0 .blockKey key keyEnd)
    (white : GStar SSWhite keyEnd colon) (literal : GLit ':' colon next) :
    Node s (SLYamlStream start) (own+1) next :=
  first_value shape unmarked lineStart prefixes indent
    (fun e node => SBlockMapEntry.implicitKeyNode own key colon next e
      (SImplicitKey.jsonKey key keyEnd colon (SFlowNode.propsEmpty 0 .blockKey key keyEnd props)
        (ScalarProduction.gstar_sswhite_to_gopt_sep white)) literal
      (SBlockNode_blockIn_to_blockOut node))

lemma actual_same_question {s t : ScannerState} {P : SurfPos → Prop}
    {land q next : SurfPos}
    (step : scanKey s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (same : s.currentIndent = (s.col : Int))
    (context : Context s P land)
    (indent : SIndent s.col land q) (literal : GLit '?' q next) :
    Slot t P s.col .blockOut next := by
  have nonempty := base.size_pos
  let top := s.indents[s.indents.size-1]'(by omega)
  have atTop : s.indents.back? = some top := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  have colTop : top.column = (s.col : Int) := by
    have current := IndentStackMono.currentIndent_eq_last nonempty
    dsimp only [top]
    omega
  have kind : top.isSequence = false := scanKey_top_not_sequence step flow atTop colTop.symm
  obtain ⟨array, arrayEq⟩ := Array.back?_eq_some_iff.mp atTop
  let previous : ScannerState := {s with indents := array}
  have oldShape : levels s = FrameLevel.map s.col :: levels previous := by
    have shape := levels_push (s := previous) arrayEq
    simpa [frame, colTop, kind, show ¬(s.col : Int) < 0 by omega] using shape
  have noPush : ¬(s.col : Int) > s.currentIndent := by omega
  have indents : t.indents = s.indents := by
    rw [scanKey_indents flow step, pushMappingIndent, ite_eq_right noPush]
  have keys : t.pendingKeys = s.pendingKeys.set! (s.indents.size-1) (some s.line) := by
    rw [scanKey_pendingKeys flow step, pushMappingIndent, ite_eq_right noPush]
  have key : t.pendingKeys[s.indents.size-1]? = some (some s.line) := by
    rw [keys, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
    simp [sound.slots.1, show s.indents.size-1 < s.indents.size by omega]
  have column : t.indentColumns[s.indents.size-1]? = some (s.col : Int) := by
    rw [ScannerState.indentColumns, indents, Array.getElem?_map,
      Array.getElem?_eq_getElem (by omega)]
    exact congrArg some colTop
  have marked : s.col ∈ RegisterWitness.markedCols t :=
    RegisterWitness.markedCols_mem.mpr ⟨s.indents.size-1,s.line,(s.col : Int),key,column,by simp⟩
  have domain := RegisterWitness.scanKey_markedCols flow step sound.slots base (by omega)
    (RegisterWitness.MarkedColsIn.self s)
  have order := levels_ordered mono
  rw [oldShape] at order
  apply same_map_question context oldShape ((levels_indents indents).trans oldShape) marked
    ?_ indent literal
  intro f mem newMark
  rcases List.mem_cons.mp (domain.mem newMark) with equal | old
  · have smaller := order.1 f mem
    change f.width < s.col at smaller
    omega
  · exact old

lemma levels_empty {s : ScannerState} (mono : IndentStackMono.Mono s)
    (negative : s.currentIndent < 0) : levels s = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro entry mem
  have before := mono.le_currentIndent entry
    (by simpa only [List.mem_reverse, Array.mem_toList] using mem)
  have less : entry.column < 0 := by omega
  simp only [ite_eq_left less]

lemma actual_first_question {s t : ScannerState} {start land q next : SurfPos}
    (step : scanKey s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s) (negative : s.currentIndent < 0)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent s.col land q) (literal : GLit '?' q next) :
    Slot t (SLYamlStream start) s.col .blockOut next := by
  have pushed : (s.col : Int) > s.currentIndent := by omega
  have indents := scanKey_indents flow step
  rw [pushMappingIndent, ite_eq_left pushed] at indents
  change t.indents = s.indents.push {column := s.col, isSequence := false} at indents
  have shape : levels t = [FrameLevel.map s.col] := by
    have shape := levels_push indents
    simpa [frame, levels_empty mono negative, show ¬(s.col : Int) < 0 by omega] using shape
  have keys := scanKey_pendingKeys flow step
  rw [pushMappingIndent, ite_eq_left pushed] at keys
  dsimp only [ScannerState.emit] at keys
  have key : t.pendingKeys[s.indents.size]? = some (some s.line) := by
    rw [keys]
    simp [sound.slots.1]
  have column : t.indentColumns[s.indents.size]? = some (s.col : Int) := by
    rw [indentColumns_getElem?, indents, Array.getElem?_push_size]
    rfl
  exact first_question shape
    (RegisterWitness.markedCols_mem.mpr ⟨s.indents.size,s.line,(s.col : Int),key,column,by simp⟩)
    lineStart prefixes indent literal

#print axioms actual_compact_sequence
#print axioms same_map_question
#print axioms first_question
#print axioms first_keyless
#print axioms first_implicit
#print axioms first_properties
#print axioms actual_same_question
#print axioms actual_first_question

end R2MandatoryContext
