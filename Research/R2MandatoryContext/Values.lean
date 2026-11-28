import Research.R2MandatoryContext.Completion

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.PreprocessIndentStable
open R2JointFrames R2ActualJointStep

namespace R2MandatoryContext

lemma value_indents {s t : ScannerState} (step : scanValue s = .ok t) :
    t.indents = (scanValuePrepare (scanValueClearKey s)).indents := by
  unfold scanValue at step
  simp only [bind, Except.bind] at step
  split at step <;> try contradiction
  split at step <;> try contradiction
  split at step <;> try contradiction
  simp only [Except.ok.injEq] at step
  subst t
  change (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents = _
  rw [L4YAML.Proofs.ScannerLoopInvariant.advance_indents]
  rfl

-- The key may begin earlier than the colon. Its actual saved column, rather
-- than the cursor column, is what the scanner uses to create this map.
lemma value_push {s t : ScannerState} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (pushed : s.currentIndent < (own : Int)) :
    t.indents = s.indents.push {column := (own : Int), isSequence := false} := by
  rw [value_indents step]
  have fields := PreprocessIndentStable.scanValueClearKey_fields s
  have clearedFlow : (scanValueClearKey s).inFlow = false := fields.2.2.1.trans flow
  have clearedIndent : (scanValueClearKey s).currentIndent = s.currentIndent :=
    currentIndent_of_indents_eq fields.2.1
  simp [scanValuePrepare, possible, clearedFlow, column, clearedIndent, pushed, fields.2.1]

lemma compact_value_node {s t : ScannerState} {P : SurfPos → Prop}
    {slot key next : SurfPos} {n m : Nat} {ctx : YamlContext}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s) (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = n+1+m)
    (pushed : s.currentIndent < ((n+1+m : Nat) : Int))
    (payload : Slot s P n ctx slot) (indent : SIndent m slot key)
    (entry : ∀ e, SBlockNode (n+1+m+1) .blockIn next e → SBlockMapEntry (n+1+m) key e) :
    Node t P (n+1+m+1) next := by
  have indents := value_push step flow possible column pushed
  have shape : levels t = FrameLevel.map (n+1+m) :: levels s := by
    have shape := levels_push indents
    have fm : frame {column := ((n+1+m : Nat) : Int), isSequence := false} =
        some (FrameLevel.map (n+1+m)) := by
      simp only [frame, ite_eq_right (show ¬((n+1+m : Nat) : Int) < 0 by omega)]
      rfl
    simpa only [fm, Option.toList_some, List.singleton_append] using shape
  have top : t.currentIndent ≤ ((n+1+m : Nat) : Int) := by
    simp [ScannerState.currentIndent, indents]
  have newMono := IndentStackMono.scanValue_mono step mono base
  have consumed := R2ValueOwnership.scanValue_own_unmarked step sound flow newMono top
  have back := RegisterWitness.scanValue_markedCols step (RegisterWitness.MarkedColsIn.self s) sound.slots
  intro e node
  change Joint t P (levels t) e
  rw [shape]
  simp only [Joint, ite_eq_right consumed]
  intro z tail
  exact (payload z (SBlockIndented.compactMap n ctx m slot key z indent
    (SCompactMap.mk (n+1+m) key e z (entry e node) tail))).restrict_marks (fun _ h => back.mem h)

lemma compact_keyless {s t : ScannerState} {P : SurfPos → Prop}
    {slot colon next : SurfPos} {n m : Nat} {ctx : YamlContext}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s) (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = n+1+m)
    (pushed : s.currentIndent < ((n+1+m : Nat) : Int))
    (payload : Slot s P n ctx slot) (indent : SIndent m slot colon) (literal : GLit ':' colon next) :
    Node t P (n+1+m+1) next :=
  compact_value_node step flow sound mono base possible column pushed payload indent
    (fun e node => SBlockMapEntry.emptyKeyNode (n+1+m) colon next e literal
      (SBlockNode_blockIn_to_blockOut node))

lemma compact_implicit {s t : ScannerState} {P : SurfPos → Prop}
    {slot key colon next : SurfPos} {n m : Nat} {ctx : YamlContext}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s) (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = n+1+m)
    (pushed : s.currentIndent < ((n+1+m : Nat) : Int))
    (payload : Slot s P n ctx slot) (indent : SIndent m slot key)
    (head : SImplicitKey key colon) (literal : GLit ':' colon next) :
    Node t P (n+1+m+1) next :=
  compact_value_node step flow sound mono base possible column pushed payload indent
    (fun e node => SBlockMapEntry.implicitKeyNode (n+1+m) key colon next e head literal
      (SBlockNode_blockIn_to_blockOut node))

-- The old own mark may be present or absent. Either way, an actual sibling
-- entry is folded into the old map tail before the outer context is spent.
lemma same_map_value {s t : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {land key next : SurfPos} {own : Nat}
    (context : Context s P land)
    (oldShape : levels s = FrameLevel.map own :: rest)
    (newShape : levels t = FrameLevel.map own :: rest)
    (consumed : own ∉ RegisterWitness.markedCols t)
    (back : ∀ f ∈ rest, f.width ∈ RegisterWitness.markedCols t →
      f.width ∈ RegisterWitness.markedCols s)
    (indent : SIndent own land key)
    (entry : ∀ e, SBlockNode (own+1) .blockIn next e → SBlockMapEntry own key e) :
    Node t P (own+1) next := by
  have before : Joint s P (FrameLevel.map own :: rest) land := by
    simpa only [Context, oldShape] using context
  have route : ∀ z, SCompactMapTail own land z → Joint s P rest z := by
    by_cases oldMarked : own ∈ RegisterWitness.markedCols s
    · exact (show L4YAML.Proofs.R2ConsumptionClosure.EntryStep (Joint s P rest) own land from by
        simpa only [Joint, ite_eq_left oldMarked] using before).1
    · exact (show ∀ z, SCompactMapTail own land z → Joint s P rest z from by
        simpa only [Joint, ite_eq_right oldMarked] using before)
  intro e node
  change Joint t P (levels t) e
  rw [newShape]
  simp only [Joint, ite_eq_right consumed]
  intro z tail
  exact (route z (SCompactMapTail.cons own land key e z indent (entry e node) tail)).restrict_on back

#print axioms compact_value_node
#print axioms compact_keyless
#print axioms compact_implicit
#print axioms same_map_value

end R2MandatoryContext
