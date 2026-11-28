import Research.R2JointFrames.Controls
import Research.R2SequenceContext.SequenceValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.R2InvariantPayload L4YAML.Proofs.R2CompactSlot
open L4YAML.Proofs.IndentStackCover (FrameLevel)

namespace R2JointFrames

-- Marked maps await both an omitted and an explicit value. Unmarked maps
-- and sequences await their own sibling tails. These layers stay interleaved.
def Joint (sc : ScannerState) (P : SurfPos → Prop) : List FrameLevel → SurfPos → Prop
  | [], e => P e
  | ⟨k, true⟩ :: rest, e => ∀ z, SCompactSeqTail k e z → Joint sc P rest z
  | ⟨k, false⟩ :: rest, e =>
      if k ∈ RegisterWitness.markedCols sc then EntryStep (Joint sc P rest) k e
      else ∀ z, SCompactMapTail k e z → Joint sc P rest z

def Context (sc : ScannerState) (P : SurfPos → Prop) (e : SurfPos) : Prop :=
  Joint sc P (levels sc) e

def Ordered : List FrameLevel → Prop
  | [] => True
  | f :: rest => (∀ g ∈ rest, g.width < f.width) ∧ Ordered rest

lemma Joint.pop {sc : ScannerState} {P : SurfPos → Prop} {f : FrameLevel}
    {rest : List FrameLevel} {e : SurfPos} (h : Joint sc P (f :: rest) e) :
    Joint sc P rest e := by
  rcases f with ⟨k, kind⟩
  cases kind with
  | true => exact h e (SCompactSeqTail.nil k e)
  | false =>
    by_cases marked : k ∈ RegisterWitness.markedCols sc
    · exact (show EntryStep (Joint sc P rest) k e from by simpa [Joint, marked] using h).1 e
        (SCompactMapTail.nil k e)
    · exact (show ∀ z, SCompactMapTail k e z → Joint sc P rest z from by simpa [Joint, marked] using h)
        e (SCompactMapTail.nil k e)

lemma Joint.close {sc : ScannerState} {P : SurfPos → Prop} {fs : List FrameLevel}
    {e : SurfPos} (h : Joint sc P fs e) : P e := by
  induction fs with
  | nil => exact h
  | cons f rest ih => exact ih h.pop

lemma Joint.drop {sc : ScannerState} {P : SurfPos → Prop} {pre rest : List FrameLevel}
    {e : SurfPos} (h : Joint sc P (pre ++ rest) e) : Joint sc P rest e := by
  induction pre with
  | nil => exact h
  | cons f pre ih => exact ih h.pop

lemma Joint.map {sc : ScannerState} {P Q : SurfPos → Prop} {fs : List FrameLevel}
    {e : SurfPos} (h : Joint sc P fs e) (f : ∀ z, P z → Q z) : Joint sc Q fs e := by
  induction fs generalizing e with
  | nil => exact f e h
  | cons top rest ih =>
    rcases top with ⟨k, kind⟩
    cases kind with
    | true => exact fun z tail => ih (h z tail)
    | false =>
      by_cases marked : k ∈ RegisterWitness.markedCols sc
      · simp only [Joint, ite_eq_left marked] at h ⊢
        exact h.map (fun z hz => ih hz)
      · simp only [Joint, ite_eq_right marked] at h ⊢
        exact fun z tail => ih (h z tail)

lemma Joint.restrict_marks {before after : ScannerState} {P : SurfPos → Prop}
    {fs : List FrameLevel} {e : SurfPos} (h : Joint before P fs e)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    Joint after P fs e := by
  induction fs generalizing e with
  | nil => exact h
  | cons top rest ih =>
    rcases top with ⟨k, kind⟩
    cases kind with
    | true => exact fun z tail => ih (h z tail)
    | false =>
      by_cases marked : k ∈ RegisterWitness.markedCols after
      · have old := back k marked
        simp only [Joint, ite_eq_left marked, ite_eq_left old] at h ⊢
        exact h.map (fun z hz => ih hz)
      · simp only [Joint, ite_eq_right marked]
        by_cases old : k ∈ RegisterWitness.markedCols before
        · simp only [Joint, ite_eq_left old] at h
          exact fun z tail => ih (h.1 z tail)
        · simp only [Joint, ite_eq_right old] at h
          exact fun z tail => ih (h z tail)

lemma Joint.restrict_on {before after : ScannerState} {P : SurfPos → Prop}
    {fs : List FrameLevel} {e : SurfPos} (h : Joint before P fs e)
    (back : ∀ f ∈ fs, f.width ∈ RegisterWitness.markedCols after →
      f.width ∈ RegisterWitness.markedCols before) : Joint after P fs e := by
  induction fs generalizing e with
  | nil => exact h
  | cons top rest ih =>
    have lower := fun f hf => back f (List.mem_cons_of_mem top hf)
    rcases top with ⟨k, kind⟩
    cases kind with
    | true => exact fun z tail => ih (h z tail) lower
    | false =>
      by_cases marked : k ∈ RegisterWitness.markedCols after
      · have old := back _ List.mem_cons_self marked
        simp only [Joint, ite_eq_left marked, ite_eq_left old] at h ⊢
        exact h.map (fun z hz => ih hz lower)
      · simp only [Joint, ite_eq_right marked]
        by_cases old : k ∈ RegisterWitness.markedCols before
        · simp only [Joint, ite_eq_left old] at h
          exact fun z tail => ih (h.1 z tail) lower
        · simp only [Joint, ite_eq_right old] at h
          exact fun z tail => ih (h z tail) lower

lemma Joint.question {sc : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {own : Nat} {q slot e : SurfPos}
    (marked : own ∈ RegisterWitness.markedCols sc) (literal : GLit '?' q slot)
    (route : ∀ v, SBlockMapEntry own q v →
      ∀ z, SCompactMapTail own v z → Joint sc P rest z)
    (key : SBlockIndented own .blockOut slot e) :
    Joint sc P (FrameLevel.map own :: rest) e := by
  simp only [Joint, ite_eq_left marked]
  exact entryStep_of_question literal route key

lemma Joint.consume {before after : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {own : Nat} {e i c v : SurfPos}
    (h : Joint before P (FrameLevel.map own :: rest) e)
    (marked : own ∈ RegisterWitness.markedCols before)
    (consumed : own ∉ RegisterWitness.markedCols after)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (indent : SIndent own e i) (colon : GLit ':' i c)
    (value : SBlockIndented own .blockOut c v) :
    Joint after P (FrameLevel.map own :: rest) v := by
  simp only [Joint, ite_eq_left marked] at h
  simp only [Joint, ite_eq_right consumed]
  exact fun z tail => (h.2 i c indent colon v value z tail).restrict_marks back

lemma Joint.sibling_sequence {before after : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {k : Nat} {land dash next e : SurfPos}
    (h : Joint before P (FrameLevel.seq k :: rest) land)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (indent : SIndent k land dash) (literal : GLit '-' dash next)
    (notNs : GNot SNsChar next) (node : SBlockIndented k .blockIn next e) :
    Joint after P (FrameLevel.seq k :: rest) e := by
  intro z tail
  exact (h z (SCompactSeqTail.cons k land dash next e z indent literal notNs node tail)).restrict_marks back

lemma ValuesBelow.from_bounded_step {sc : ScannerState} {P : SurfPos → Prop}
    {own upper : Nat} {e : SurfPos}
    (bound : ∀ x < upper, x ∈ RegisterWitness.markedCols sc → x ≤ own)
    (step : EntryStep (ValuesBelow sc P own) own e) : ValuesBelow sc P upper e := by
  induction upper with
  | zero => exact (step.1 e (SCompactMapTail.nil own e)).truncate (Nat.zero_le _)
  | succ n ih =>
    by_cases lt : n < own
    · exact (step.1 e (SCompactMapTail.nil own e)).truncate (by omega)
    · by_cases eq : n = own
      · subst n
        by_cases marked : own ∈ RegisterWitness.markedCols sc
        · simpa only [ValuesBelow, ite_eq_left marked] using step
        · simpa only [ValuesBelow, ite_eq_right marked] using step.1 e (SCompactMapTail.nil own e)
      · have absent : n ∉ RegisterWitness.markedCols sc := by
          intro marked
          have := bound n (by omega) marked
          omega
        simp only [ValuesBelow, ite_eq_right absent]
        exact ih (fun x hx => bound x (by omega))

-- This direction closes unmarked collection tails only as a projection.
-- The joint context itself continues to retain every such tail.
lemma Joint.values_below {sc : ScannerState} {P : SurfPos → Prop}
    {fs : List FrameLevel} {upper : Nat} {e : SurfPos}
    (h : Joint sc P fs e) (ordered : Ordered fs)
    (covered : ∀ x < upper, x ∈ RegisterWitness.markedCols sc → FrameLevel.map x ∈ fs) :
    ValuesBelow sc P upper e := by
  induction fs generalizing upper e with
  | nil =>
    exact ValuesBelow.of_no_lower_marks (fun x hx marked => by
      simpa using covered x hx marked) h
  | cons top rest ih =>
    rcases top with ⟨k, kind⟩
    change (∀ g ∈ rest, g.width < k) ∧ Ordered rest at ordered
    cases kind with
    | true =>
      apply ih h.pop ordered.2
      intro x hx marked
      rcases List.mem_cons.mp (covered x hx marked) with eq | mem
      · have bad := congrArg FrameLevel.isSeq eq
        contradiction
      · exact mem
    | false =>
      by_cases marked : k ∈ RegisterWitness.markedCols sc
      · by_cases lt : k < upper
        · simp only [Joint, ite_eq_left marked] at h
          apply ValuesBelow.from_bounded_step (own := k)
          · intro x hx mark
            rcases List.mem_cons.mp (covered x hx mark) with eq | mem
            · have width := congrArg FrameLevel.width eq
              exact Nat.le_of_eq width
            · exact Nat.le_of_lt (ordered.1 _ mem)
          · exact h.map (fun z hz => ih (upper := k) hz ordered.2 (by
              intro x hx mark
              rcases List.mem_cons.mp (covered x (by omega) mark) with eq | mem
              · have width := congrArg FrameLevel.width eq
                change x = k at width
                omega
              · exact mem))
        · apply ih h.pop ordered.2
          intro x hx mark
          rcases List.mem_cons.mp (covered x hx mark) with eq | mem
          · have width := congrArg FrameLevel.width eq
            change x = k at width
            omega
          · exact mem
      · apply ih h.pop ordered.2
        intro x hx mark
        rcases List.mem_cons.mp (covered x hx mark) with eq | mem
        · have width := congrArg FrameLevel.width eq
          change x = k at width
          exact (marked (width ▸ mark)).elim
        · exact mem

lemma Joint.entries {sc : ScannerState} {P : SurfPos → Prop}
    {fs : List FrameLevel} {e : SurfPos} (h : Joint sc P fs e)
    (ordered : Ordered fs)
    (covered : ∀ x ∈ RegisterWitness.markedCols sc, FrameLevel.map x ∈ fs) :
    EntryValues sc P e :=
  h.values_below ordered (fun x _ => covered x)

#print axioms Joint.consume
#print axioms Joint.sibling_sequence
#print axioms Joint.entries

end R2JointFrames
