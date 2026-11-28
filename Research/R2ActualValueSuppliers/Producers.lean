import Research.R2ActualValueSuppliers.Controls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.PreprocessIndentStable
open R2JointFrames R2ActualJointStep R2MandatoryContext

namespace R2ActualValueSuppliers

-- The saved key's column is independent of the colon cursor. The actual
-- validator, rather than an assumed map shape, excludes a sequence top.
lemma implicit_value_layout {s t : ScannerState} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (same : s.currentIndent = (own : Int)) :
    t.indents = s.indents ∧
    ∃ rest, levels s = FrameLevel.map own :: rest ∧
      levels t = FrameLevel.map own :: rest := by
  have fields := PreprocessIndentStable.scanValueClearKey_fields s
  have clearFlow : (scanValueClearKey s).inFlow = false := fields.2.2.1.trans flow
  have clearIndent : (scanValueClearKey s).currentIndent = s.currentIndent :=
    currentIndent_of_indents_eq fields.2.1
  have indents : t.indents = s.indents := by
    rw [value_indents step]
    simp [scanValuePrepare, possible, clearFlow, column, clearIndent, same, fields.2.1]
  have nonempty := base.size_pos
  let top := s.indents[s.indents.size-1]'(by omega)
  have atTop : s.indents.back? = some top := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  have topColumn : top.column = (own : Int) := by
    have current := IndentStackMono.currentIndent_eq_last nonempty
    dsimp only [top]
    omega
  have kind : top.isSequence = false :=
    scanValue_top_not_sequence (EntryBoundaryLayout.scanValue_ok_validate_ok step) possible
      clearFlow (by rw [fields.2.1]; exact atTop)
      (by rw [column, topColumn]) (by rw [column, clearIndent, same]; omega)
  obtain ⟨array, arrayEq⟩ := Array.back?_eq_some_iff.mp atTop
  let previous : ScannerState := {s with indents := array}
  have shape : levels s = FrameLevel.map own :: levels previous := by
    have shape := levels_push (s := previous) arrayEq
    simpa [frame, topColumn, kind, show ¬(own : Int) < 0 by omega] using shape
  exact ⟨indents, levels previous, shape, (levels_indents indents).trans shape⟩

lemma actual_same_value {s t : ScannerState} {P : SurfPos → Prop}
    {land key next : SurfPos} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (same : s.currentIndent = (own : Int))
    (context : Context s P land) (indent : SIndent own land key)
    (entry : ∀ e, SBlockNode (own+1) .blockIn next e → SBlockMapEntry own key e) :
    Node t P (own+1) next := by
  obtain ⟨indents, rest, oldShape, newShape⟩ :=
    implicit_value_layout step flow base possible column same
  have newMono := mono.of_indents_eq indents
  have consumed := R2ValueOwnership.scanValue_own_unmarked (own := own)
    step sound flow newMono (by rw [currentIndent_of_indents_eq indents, same]; omega)
  have back := RegisterWitness.scanValue_markedCols step
    (RegisterWitness.MarkedColsIn.self s) sound.slots
  exact same_map_value context oldShape newShape consumed (fun _ _ h => back.mem h) indent entry

-- These are actual grammar writers, rather than a caller-supplied completed
-- entry. The ancestor Context is retained; no ancestor-domain emptiness is used.
lemma actual_same_keyless {s t : ScannerState} {P : SurfPos → Prop}
    {land colon next : SurfPos} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (same : s.currentIndent = (own : Int))
    (context : Context s P land) (indent : SIndent own land colon) (literal : GLit ':' colon next) :
    Node t P (own+1) next :=
  actual_same_value step flow sound mono base possible column same context indent
    (fun e node => SBlockMapEntry.emptyKeyNode own colon next e literal
      (SBlockNode_blockIn_to_blockOut node))

lemma actual_same_implicit {s t : ScannerState} {P : SurfPos → Prop}
    {land key keyEnd colon next : SurfPos} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (same : s.currentIndent = (own : Int))
    (context : Context s P land) (indent : SIndent own land key)
    (head : ImplicitKeyHead key keyEnd) (white : GStar SSWhite keyEnd colon)
    (literal : GLit ':' colon next) : Node t P (own+1) next :=
  actual_same_value step flow sound mono base possible column same context indent
    (fun e node => SBlockMapEntry.implicitKeyNode own key colon next e
      (implicitKeyHead_to_SImplicitKey head white) literal
      (SBlockNode_blockIn_to_blockOut node))

lemma actual_same_properties {s t : ScannerState} {P : SurfPos → Prop}
    {land key keyEnd colon next : SurfPos} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (same : s.currentIndent = (own : Int))
    (context : Context s P land) (indent : SIndent own land key)
    (props : SCNsProperties 0 .blockKey key keyEnd) (white : GStar SSWhite keyEnd colon)
    (literal : GLit ':' colon next) : Node t P (own+1) next :=
  actual_same_value step flow sound mono base possible column same context indent
    (fun e node => SBlockMapEntry.implicitKeyNode own key colon next e
      (SImplicitKey.jsonKey key keyEnd colon (SFlowNode.propsEmpty 0 .blockKey key keyEnd props)
        (ScalarProduction.gstar_sswhite_to_gopt_sep white)) literal
      (SBlockNode_blockIn_to_blockOut node))

lemma first_value_layout {s t : ScannerState} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (negative : s.currentIndent < 0) :
    levels t = [FrameLevel.map own] ∧ own ∉ RegisterWitness.markedCols t := by
  have indents := value_push step flow possible column (by omega)
  have shape : levels t = [FrameLevel.map own] := by
    have shape := levels_push indents
    simpa [frame, levels_empty mono negative, show ¬(own : Int) < 0 by omega] using shape
  have newMono := IndentStackMono.scanValue_mono step mono base
  have top : t.currentIndent ≤ (own : Int) := by
    simp [ScannerState.currentIndent, indents]
  exact ⟨shape, R2ValueOwnership.scanValue_own_unmarked step sound flow newMono top⟩

lemma actual_first_value {s t : ScannerState} {start land key next : SurfPos} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (negative : s.currentIndent < 0)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land key)
    (entry : ∀ e, SBlockNode (own+1) .blockIn next e → SBlockMapEntry own key e) :
    Node t (SLYamlStream start) (own+1) next := by
  obtain ⟨shape, unmarked⟩ := first_value_layout step flow sound mono base possible column negative
  exact first_value shape unmarked lineStart prefixes indent entry

#print axioms implicit_value_layout
#print axioms actual_same_value
#print axioms actual_same_keyless
#print axioms actual_same_implicit
#print axioms actual_same_properties
#print axioms first_value_layout
#print axioms actual_first_value

end R2ActualValueSuppliers
