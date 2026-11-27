import L4YAML.Proofs.Production.StreamAccum

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.NodeProduction

namespace L4YAML.Proofs.R2ConsumptionClosure

-- Both ways of completing this actual entry retain its mapping's own tail.
-- The result can itself await every enclosing entry.
def EntryStep (P : SurfPos → Prop) (own : Nat) (e : SurfPos) : Prop :=
  (∀ z, SCompactMapTail own e z → P z) ∧
  (∀ i c, SIndent own e i → GLit ':' i c →
    ∀ v, SBlockIndented own .blockOut c v →
      ∀ z, SCompactMapTail own v z → P z)

-- Recursion is over grammar columns; membership is read from the real state.
-- No independent list, snapshot or fourth-kind index is carried.
def ValuesBelow (sc : ScannerState) (P : SurfPos → Prop) : Nat → SurfPos → Prop
  | 0, e => P e
  | n + 1, e =>
    if n ∈ RegisterWitness.markedCols sc then EntryStep (ValuesBelow sc P n) n e
    else ValuesBelow sc P n e

def columnCeiling (sc : ScannerState) : Nat :=
  (RegisterWitness.markedCols sc).foldr (fun x n => max (x + 1) n) 0

def EntryValues (sc : ScannerState) (P : SurfPos → Prop) (e : SurfPos) : Prop :=
  ValuesBelow sc P (columnCeiling sc) e

lemma marked_lt_ceiling {sc : ScannerState} {own : Nat}
    (h : own ∈ RegisterWitness.markedCols sc) : own < columnCeiling sc := by
  have bound : ∀ xs : List Nat, ∀ x ∈ xs,
      x + 1 ≤ xs.foldr (fun x n => max (x + 1) n) 0 := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)
  exact Nat.lt_of_succ_le (bound _ own h)

lemma ceiling_le_of_marks_lt {sc : ScannerState} {upper : Nat}
    (h : ∀ x ∈ RegisterWitness.markedCols sc, x < upper) : columnCeiling sc ≤ upper := by
  have bound : ∀ xs : List Nat, (∀ x ∈ xs, x < upper) →
      xs.foldr (fun x n => max (x + 1) n) 0 ≤ upper := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
      intro hs
      exact Nat.max_le.mpr ⟨hs a (by simp), ih (fun x hx => hs x (by simp [hx]))⟩
  exact bound _ h

lemma EntryStep.map {P Q : SurfPos → Prop} {own : Nat} {e : SurfPos}
    (step : EntryStep P own e) (f : ∀ z, P z → Q z) : EntryStep Q own e :=
  ⟨fun z tail => f z (step.1 z tail),
   fun i c indent colon v value z tail => f z (step.2 i c indent colon v value z tail)⟩

lemma ValuesBelow.close {sc : ScannerState} {P : SurfPos → Prop} {upper : Nat}
    {e : SurfPos} (h : ValuesBelow sc P upper e) : P e := by
  induction upper with
  | zero => exact h
  | succ n ih =>
    unfold ValuesBelow at h
    split at h
    · exact ih (h.1 e (SCompactMapTail.nil n e))
    · exact ih h

lemma ValuesBelow.at {sc : ScannerState} {P : SurfPos → Prop} {upper own : Nat}
    {e : SurfPos} (h : ValuesBelow sc P upper e)
    (marked : own ∈ RegisterWitness.markedCols sc) (lt : own < upper) :
    EntryStep (ValuesBelow sc P own) own e := by
  induction upper with
  | zero => omega
  | succ n ih =>
    by_cases eq : own = n
    · subst own
      simpa only [ValuesBelow, if_pos marked] using h
    · have below : own < n := by omega
      unfold ValuesBelow at h
      split at h
      · exact ih (h.1 e (SCompactMapTail.nil n e)) below
      · exact ih h below

lemma ValuesBelow.truncate {sc : ScannerState} {P : SurfPos → Prop} {upper lower : Nat}
    {e : SurfPos} (h : ValuesBelow sc P upper e) (le : lower ≤ upper) :
    ValuesBelow sc P lower e := by
  induction upper with
  | zero =>
    have : lower = 0 := by omega
    subst lower
    exact h
  | succ n ih =>
    by_cases eq : lower = n + 1
    · subst lower; exact h
    · have le' : lower ≤ n := by omega
      unfold ValuesBelow at h
      split at h
      · exact ih (h.1 e (SCompactMapTail.nil n e)) le'
      · exact ih h le'

lemma ValuesBelow.narrow {before after : ScannerState} {P : SurfPos → Prop} {upper : Nat}
    {e : SurfPos} (h : ValuesBelow before P upper e)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    ValuesBelow after P upper e := by
  induction upper generalizing e with
  | zero => exact h
  | succ n ih =>
    by_cases hm : n ∈ RegisterWitness.markedCols after
    · have old := back n hm
      simp only [ValuesBelow, if_pos old] at h
      simp only [ValuesBelow, if_pos hm]
      exact h.map (fun z hz => ih hz)
    · simp only [ValuesBelow, if_neg hm]
      unfold ValuesBelow at h
      split at h
      · exact ih (h.1 e (SCompactMapTail.nil n e))
      · exact ih h

lemma EntryValues.consume {before after : ScannerState} {P : SurfPos → Prop}
    {e i c v : SurfPos} {own : Nat} (h : EntryValues before P e)
    (ownMark : own ∈ RegisterWitness.markedCols before)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (smaller : ∀ x ∈ RegisterWitness.markedCols after, x < own)
    (indent : SIndent own e i) (colon : GLit ':' i c)
    (value : SBlockIndented own .blockOut c v) : EntryValues after P v := by
  have step := ValuesBelow.at h ownMark (marked_lt_ceiling ownMark)
  have rest := step.2 i c indent colon v value v (SCompactMapTail.nil own v)
  exact rest.narrow back |>.truncate (ceiling_le_of_marks_lt smaller)

lemma ValuesBelow.valueLine {sc : ScannerState} {start e : SurfPos} {upper own : Nat}
    (h : ValuesBelow sc (SLYamlStream start) upper e)
    (marked : own ∈ RegisterWitness.markedCols sc) (lt : own < upper) :
    ExplValueLine start own e := by
  intro i c indent colon v value
  have step := h.at marked lt
  exact ResumeFrames.level own [] v (by simp)
    (fun z tail => ResumeFrames.bottom z (step.2 i c indent colon v value z tail).close)

-- Consuming any marked owner leaves a continuation for every smaller owner.
-- Taking a nil tail here closes only the consumed mapping, not outer entries.
lemma EntryValues.pair {sc : ScannerState} {start e i c v : SurfPos} {own a : Nat}
    (h : EntryValues sc (SLYamlStream start) e)
    (ownMark : own ∈ RegisterWitness.markedCols sc)
    (aMark : a ∈ RegisterWitness.markedCols sc) (lt : a < own)
    (indent : SIndent own e i) (colon : GLit ':' i c)
    (value : SBlockIndented own .blockOut c v) : ExplValueLine start a v := by
  have step := ValuesBelow.at h ownMark (marked_lt_ceiling ownMark)
  exact (step.2 i c indent colon v value v (SCompactMapTail.nil own v)).valueLine aMark lt

-- A real question and whole entry route construct both branches. In
-- particular, omission uses explicitEmpty only after its actual key ends.
lemma entryStep_of_question {P : SurfPos → Prop} {n : Nat} {q key e : SurfPos}
    (question : GLit '?' q key)
    (route : ∀ v, SBlockMapEntry n q v →
      ∀ z, SCompactMapTail n v z → P z)
    (content : SBlockIndented n .blockOut key e) : EntryStep P n e := by
  constructor
  · exact route e (SBlockMapEntry.explicitEmpty n q key e question content)
  · intro i c indent colon v value
    exact route v (SBlockMapEntry.explicit n q key e i c v question content indent colon value)

-- This is the exact colon → value-node boundary. The retained result remains
-- open; the consumed value's block node is supplied by the actual scanner arm.
lemma colon_value_domain {P : SurfPos → Prop} {n : Nat} {keyEnd i colon : SurfPos}
    (step : EntryStep P n keyEnd) (indent : SIndent n keyEnd i)
    (literal : GLit ':' i colon) :
    ∀ e, SBlockNode (n + 1) .blockIn colon e → P e := by
  intro e node
  exact step.2 i colon indent literal e
    (SBlockIndented.node n .blockOut colon e (SBlockNode_blockIn_to_blockOut node))
    e (SCompactMapTail.nil n e)

#print axioms EntryValues.pair
#print axioms EntryValues.consume
#print axioms entryStep_of_question
#print axioms colon_value_domain

end L4YAML.Proofs.R2ConsumptionClosure
