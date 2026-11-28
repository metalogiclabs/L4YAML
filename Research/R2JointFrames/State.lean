import Research.R2JointFrames.Joint

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.IndentStackMono
open L4YAML.Proofs.R2ConsumptionClosure

namespace R2JointFrames

lemma Ordered.of_pairwise {fs : List FrameLevel}
    (h : fs.Pairwise (fun a b => b.width < a.width)) : Ordered fs := by
  induction fs with
  | nil => trivial
  | cons f rest ih =>
    have parts := List.pairwise_cons.mp h
    exact ⟨parts.1, ih parts.2⟩

lemma levels_ordered {sc : ScannerState} (mono : Mono sc) : Ordered (levels sc) := by
  have increasing : sc.indents.toList.Pairwise (fun a b => a.column < b.column) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [Array.length_toList] at hi hj
    have jm : j - 1 < sc.indents.size := by omega
    have last : j - 1 + 1 = j := by omega
    have le := mono.le_last (j - 1) jm i hi (by omega)
    have lt := mono (j - 1) (by omega)
    have lt' : sc.indents[j - 1].column < sc.indents[j].column := by
      simpa only [last] using lt
    simpa only [Array.getElem_toList] using Int.lt_of_le_of_lt le lt'
  have decreasing : sc.indents.toList.reverse.Pairwise (fun a b => b.column < a.column) :=
    List.pairwise_reverse.mpr increasing
  apply Ordered.of_pairwise
  apply decreasing.filterMap (fun e =>
    if e.column < 0 then none
    else some (if e.isSequence then FrameLevel.seq e.column.toNat else FrameLevel.map e.column.toNat))
  intro a b lt x hx y hy
  split at hx
  · contradiction
  · rename_i nonnegativeA
    split at hy
    · contradiction
    · rename_i nonnegativeB
      have ax : x.width = a.column.toNat := by
        split at hx <;> cases hx <;> rfl
      have byy : y.width = b.column.toNat := by
        split at hy <;> cases hy <;> rfl
      rw [ax, byy]
      omega

-- Kind ownership is explicit. The existing Sound.slots predicate supplies
-- size and nonnegative columns, but does not itself say marked levels are maps.
def MarkedMaps (sc : ScannerState) : Prop :=
  ∀ (i l : Nat), sc.pendingKeys[i]? = some (some l) →
    ∃ entry : IndentEntry, sc.indents[i]? = some entry ∧ entry.isSequence = false

lemma levels_cover_marks {sc : ScannerState} (slots : PendingKeySound.SlotsOk sc)
    (maps : MarkedMaps sc) :
    ∀ x ∈ RegisterWitness.markedCols sc, FrameLevel.map x ∈ levels sc := by
  intro x marked
  obtain ⟨i, l, c, key, column, rfl⟩ := RegisterWitness.markedCols_mem.mp marked
  obtain ⟨entry, atEntry, kind⟩ := maps i l key
  obtain ⟨c', atColumn, nonnegative⟩ := slots.2 i l key
  have eq : c' = c := Option.some.inj (atColumn.symm.trans column)
  subst c'
  have entryCol : entry.column = c := by
    simpa [ScannerState.indentColumns, atEntry] using column
  apply List.mem_filterMap.mpr
  have mem : entry ∈ sc.indents.toList := by simpa using Array.mem_of_getElem? atEntry
  refine ⟨entry, List.mem_reverse.mpr mem, ?_⟩
  simp [entryCol, kind, show ¬c < 0 by omega]

lemma Context.entries {sc : ScannerState} {P : SurfPos → Prop} {e : SurfPos}
    (h : Context sc P e) (mono : Mono sc)
    (slots : PendingKeySound.SlotsOk sc) (maps : MarkedMaps sc) : EntryValues sc P e :=
  Joint.entries h (levels_ordered mono) (levels_cover_marks slots maps)

def SlotCheck (sc : ScannerState) : Prop :=
  sc.pendingKeys.size = sc.indents.size ∧
  ∀ i : Fin sc.pendingKeys.size, sc.pendingKeys[i].isSome = true →
    (sc.indents[i.val]?).any (fun entry => decide (0 ≤ entry.column) && !entry.isSequence) = true

lemma SlotCheck.sound {sc : ScannerState} (check : SlotCheck sc) :
    PendingKeySound.SlotsOk sc ∧ MarkedMaps sc := by
  have entries : ∀ (i l : Nat), sc.pendingKeys[i]? = some (some l) →
      ∃ entry : IndentEntry, sc.indents[i]? = some entry ∧
        0 ≤ entry.column ∧ entry.isSequence = false := by
    intro i l key
    obtain ⟨hi, atKey⟩ := Array.getElem?_eq_some_iff.mp key
    have live : (sc.pendingKeys[i]'hi).isSome = true := by rw [atKey]; rfl
    have checked := check.2 ⟨i,hi⟩ live
    cases atEntry : sc.indents[i]? with
    | none => simp [atEntry] at checked
    | some entry =>
      have parts : 0 ≤ entry.column ∧ entry.isSequence = false := by
        simpa [atEntry] using checked
      exact ⟨entry, rfl, parts⟩
  constructor
  · refine ⟨check.1, ?_⟩
    intro i l key
    obtain ⟨entry, atEntry, nonnegative, _⟩ := entries i l key
    exact ⟨entry.column, by simp [ScannerState.indentColumns, atEntry], nonnegative⟩
  · intro i l key
    obtain ⟨entry, atEntry, _, kind⟩ := entries i l key
    exact ⟨entry, atEntry, kind⟩

def MonoCheck (sc : ScannerState) : Prop :=
  ∀ i : Fin sc.indents.size,
    (if h : i.val+1 < sc.indents.size then
      decide ((sc.indents[i.val]'i.isLt).column < (sc.indents[i.val+1]'h).column)
     else true) = true

lemma MonoCheck.sound {sc : ScannerState} (check : MonoCheck sc) : Mono sc := by
  intro i hi
  have checked := check ⟨i,by omega⟩
  simp only [dif_pos hi] at checked
  exact of_decide_eq_true checked

#print axioms levels_ordered
#print axioms Context.entries

end R2JointFrames
