import Research.R2JointFrames.Slots
import Research.R2ValueOwnership.Ownership

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Proofs L4YAML.Surface
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.IndentStackBase L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.R2ConsumptionClosure

namespace R2JointFrames

lemma Context.of_eq {s t : ScannerState} {P : SurfPos → Prop} {e : SurfPos}
    (context : Context s P e) (keys : t.pendingKeys = s.pendingKeys)
    (indents : t.indents = s.indents) : Context t P e := by
  have shape : levels t = levels s := by simp [levels, indents]
  have marks : RegisterWitness.markedCols t = RegisterWitness.markedCols s := by
    simp [RegisterWitness.markedCols, ScannerState.indentColumns, keys, indents]
  change Joint t P (levels t) e
  rw [shape]
  exact context.restrict_marks (fun _ h => marks ▸ h)

lemma Slot.of_eq {s t : ScannerState} {P : SurfPos → Prop} {slot : SurfPos}
    {n : Nat} {ctx : YamlContext} (payload : Slot s P n ctx slot)
    (keys : t.pendingKeys = s.pendingKeys) (indents : t.indents = s.indents) :
    Slot t P n ctx slot := fun e node => (payload e node).of_eq keys indents

lemma levels_push_map {s t : ScannerState} {own : Nat}
    (indents : t.indents = s.indents.push { column := (own : Int), isSequence := false }) :
    levels t = FrameLevel.map own :: levels s := by
  simp [levels, indents, List.reverse_append]

-- Actual scanner key producer. Its shape, new mark and surviving-mark domain
-- are conclusions of scanKey, not new semantic route assumptions.
lemma Slot.actual_question {s t : ScannerState} {P : SurfPos → Prop}
    {slot q next : SurfPos} {n m : Nat} {ctx : YamlContext}
    (ok : scanKey s = .ok t) (nf : s.inFlow = false)
    (slots : SlotsOk s) (mono : IndentStackMono.Mono s) (base : SentinelBase s)
    (column : s.col = n+1+m) (pushed : s.currentIndent < (s.col : Int))
    (payload : Slot s P n ctx slot) (indent : SIndent m slot q) (literal : GLit '?' q next) :
    Slot t P (n+1+m) .blockOut next := by
  have ti := scanKey_indents nf ok
  have tk := scanKey_pendingKeys nf ok
  rw [pushMappingIndent, ite_eq_left pushed] at ti tk
  dsimp only [ScannerState.emit] at ti tk
  have inds : t.indents = s.indents.push { column := ((n+1+m : Nat) : Int), isSequence := false } := by
    simpa only [column] using ti
  have shape := levels_push_map inds
  have key : t.pendingKeys[s.indents.size]? = some (some s.line) := by
    rw [tk]
    simp only [Array.size_push, Nat.add_sub_cancel, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self]
    simp [slots.1]
  have col : t.indentColumns[s.indents.size]? = some ((n+1+m : Nat) : Int) := by
    rw [indentColumns_getElem?, inds, Array.getElem?_push_size]
    rfl
  have marked : n+1+m ∈ RegisterWitness.markedCols t :=
    RegisterWitness.markedCols_mem.mpr ⟨s.indents.size, s.line, ((n+1+m : Nat) : Int),
      key, col, Int.toNat_natCast _⟩
  have all := RegisterWitness.scanKey_markedCols nf ok slots base (Int.le_of_lt pushed)
    (RegisterWitness.MarkedColsIn.self s)
  change RegisterWitness.MarkedColsIn t (s.col :: RegisterWitness.markedCols s) at all
  have ordered := levels_ordered (IndentStackMono.scanKey_mono nf ok mono base)
  rw [shape] at ordered
  apply payload.compact_question shape marked ?_ indent literal
  intro f mem markedF
  have lower := ordered.1 f mem
  change f.width < n+1+m at lower
  have domain := all.mem markedF
  simp only [column, List.mem_cons] at domain
  rcases domain with own | old
  · omega
  · exact old

lemma explicit_value_indents {s t : ScannerState} {line : Nat}
    (ok : scanValue s = .ok t) (live : s.explicitKeyLine = some line)
    (noSimple : (scanValueClearKey s).simpleKey.possible = false) : t.indents = s.indents := by
  have ck := scanValueClearKey_core s
  have prep : (scanValuePrepare (scanValueClearKey s)).indents = s.indents := by
    simp [scanValuePrepare, noSimple, ck.2.2.2.1, live, ck.1]
  unfold scanValue at ok
  simp only [bind, Except.bind] at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  simp only [Except.ok.injEq] at ok; subst ok
  repeat (any_goals split)
  all_goals change (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents = s.indents
  all_goals rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]
  all_goals exact prep

-- Actual explicit colon producer. Ownership supplies absence of its consumed
-- mark while Joint.consume retains arbitrary map/sequence siblings below it.
lemma Context.actual_colon {s t : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {own line : Nat} {e i c v : SurfPos}
    (ok : scanValue s = .ok t) (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : SentinelBase s) (nf : s.inFlow = false)
    (live : s.explicitKeyLine = some line)
    (noSimple : (scanValueClearKey s).simpleKey.possible = false)
    (top : s.currentIndent ≤ (own : Int))
    (shape : levels s = FrameLevel.map own :: rest)
    (marked : own ∈ RegisterWitness.markedCols s)
    (context : Context s P e) (indent : SIndent own e i) (literal : GLit ':' i c)
    (value : SBlockIndented own .blockOut c v) : Context t P v := by
  have indents := explicit_value_indents ok live noSimple
  have same : levels t = levels s := by simp [levels, indents]
  have monoNext := IndentStackMono.scanValue_mono ok mono base
  have topNext : t.currentIndent ≤ (own : Int) := by
    rw [currentIndent_of_indents_eq indents]; exact top
  have consumed := R2ValueOwnership.scanValue_own_unmarked ok sound nf monoNext topNext
  have back := RegisterWitness.scanValue_markedCols ok (RegisterWitness.MarkedColsIn.self s) sound.slots
  change Joint s P (levels s) e at context
  rw [shape] at context
  change Joint t P (levels t) v
  rw [same, shape]
  exact context.consume marked consumed (fun _ h => back.mem h) indent literal value

#print axioms Slot.actual_question
#print axioms Context.actual_colon

end R2JointFrames
