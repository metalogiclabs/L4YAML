import Research.R2ActualValueSuppliers.First

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.PreprocessIndentStable
open R2JointFrames R2ActualJointStep R2MandatoryContext

namespace R2ActualValueSuppliers

def unsavedSource := "? - a: b\n    : c\n  - d\n: e\n"

def checkUnsaved (s t : ScannerState) : Bool :=
  if !s.inFlow && !(scanValueClearKey s).simpleKey.possible &&
      s.currentIndent == (s.col : Int) && !atSequenceIndent s then
    t.indents == s.indents && !(RegisterWitness.markedCols t).contains s.col &&
      (RegisterWitness.markedCols t).all (RegisterWitness.markedCols s).contains
  else true

def unsavedSweep : Nat → ScannerState → Bool × Nat
  | 0, _ => (true,0)
  | fuel+1, s =>
    let here := match scanNextToken_preprocess s with
      | .ok (some (prep, ':')) =>
          let dis := dispatchState prep
          match scanValue dis with
          | .ok t => (checkUnsaved dis t,
              if !dis.inFlow && !(scanValueClearKey dis).simpleKey.possible &&
                  dis.currentIndent == (dis.col : Int) && !atSequenceIndent dis &&
                  (dis.col : Int) != dis.explicitKeyCol then 1 else 0)
          | _ => (true,0)
      | _ => (true,0)
    match scanNextToken s with
    | .ok (some t) =>
        let later := unsavedSweep fuel t
        (here.1 && later.1,here.2+later.2)
    | _ => here

#guard (unsavedSource :: sources).all fun input =>
  (unsavedSweep 0 ((ScannerState.mk' input).emit .streamStart)).1
#guard (unsavedSource :: sources).all fun input =>
  (unsavedSweep 1 ((ScannerState.mk' input).emit .streamStart)).1
#guard (unsavedSource :: sources).all fun input =>
  (unsavedSweep 2 ((ScannerState.mk' input).emit .streamStart)).1
#guard (unsavedSource :: sources).all fun input =>
  (unsavedSweep 128 ((ScannerState.mk' input).emit .streamStart)).1
#guard (unsavedSweep 128 ((ScannerState.mk' unsavedSource).emit .streamStart)).2 > 0
#guard (L4YAML.TokenParser.parseYaml unsavedSource).isOk
#eval (unsavedSweep 128 ((ScannerState.mk' unsavedSource).emit .streamStart)).2

-- When preprocessing cleared a phantom key, scanValuePrepare may use its
-- explicit-register branch instead. At this same column both branches keep
-- the stack. A mapping kind is a stated fact about the real top, checked by
-- the existing atSequenceIndent predicate; it is not inferred from the
-- saved-key validator, whose guard did not run in this case.
lemma unsaved_value_layout {s t : ScannerState}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (base : IndentStackBase.SentinelBase s)
    (cleared : (scanValueClearKey s).simpleKey.possible = false)
    (same : s.currentIndent = (s.col : Int)) (notSequence : atSequenceIndent s = false) :
    t.indents = s.indents ∧
    ∃ rest, levels s = FrameLevel.map s.col :: rest ∧
      levels t = FrameLevel.map s.col :: rest := by
  have fields := PreprocessIndentStable.scanValueClearKey_fields s
  have clearFlow : (scanValueClearKey s).inFlow = false := fields.2.2.1.trans flow
  have clearIndent : (scanValueClearKey s).currentIndent = s.currentIndent :=
    currentIndent_of_indents_eq fields.2.1
  have indents : t.indents = s.indents := by
    rw [value_indents step]
    unfold scanValuePrepare
    simp only [cleared, Bool.false_eq_true, ite_false]
    split
    · exact fields.2.1
    · simp [clearFlow, pushMappingIndent, fields.1, clearIndent, same, fields.2.1]
  have nonempty := base.size_pos
  let top := s.indents[s.indents.size-1]'(by omega)
  have atTop : s.indents.back? = some top := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  have topColumn : top.column = (s.col : Int) := by
    have current := IndentStackMono.currentIndent_eq_last nonempty
    dsimp only [top]
    omega
  have kind : top.isSequence = false := by
    simpa [atSequenceIndent, atTop, topColumn] using notSequence
  obtain ⟨array, arrayEq⟩ := Array.back?_eq_some_iff.mp atTop
  let previous : ScannerState := {s with indents := array}
  have shape : levels s = FrameLevel.map s.col :: levels previous := by
    have shape := levels_push (s := previous) arrayEq
    simpa [frame, topColumn, kind, show ¬(s.col : Int) < 0 by omega] using shape
  exact ⟨indents, levels previous, shape, (levels_indents indents).trans shape⟩

lemma actual_unsaved_value {s t : ScannerState} {P : SurfPos → Prop}
    {land key next : SurfPos}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (cleared : (scanValueClearKey s).simpleKey.possible = false)
    (same : s.currentIndent = (s.col : Int)) (notSequence : atSequenceIndent s = false)
    (context : Context s P land) (indent : SIndent s.col land key)
    (entry : ∀ e, SBlockNode (s.col+1) .blockIn next e → SBlockMapEntry s.col key e) :
    Node t P (s.col+1) next := by
  obtain ⟨indents, rest, oldShape, newShape⟩ := unsaved_value_layout step flow base cleared same notSequence
  have newMono := mono.of_indents_eq indents
  have consumed := R2ValueOwnership.scanValue_own_unmarked (own := s.col)
    step sound flow newMono (by rw [currentIndent_of_indents_eq indents, same]; omega)
  have back := RegisterWitness.scanValue_markedCols step
    (RegisterWitness.MarkedColsIn.self s) sound.slots
  exact same_map_value context oldShape newShape consumed (fun _ _ h => back.mem h) indent entry

lemma actual_unsaved_keyless {s t : ScannerState} {P : SurfPos → Prop}
    {land colon next : SurfPos}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (cleared : (scanValueClearKey s).simpleKey.possible = false)
    (same : s.currentIndent = (s.col : Int)) (notSequence : atSequenceIndent s = false)
    (context : Context s P land) (indent : SIndent s.col land colon)
    (literal : GLit ':' colon next) : Node t P (s.col+1) next :=
  actual_unsaved_value step flow sound mono base cleared same notSequence context indent
    (fun e node => SBlockMapEntry.emptyKeyNode s.col colon next e literal
      (SBlockNode_blockIn_to_blockOut node))

#print axioms unsaved_value_layout
#print axioms actual_unsaved_value
#print axioms actual_unsaved_keyless

end R2ActualValueSuppliers
