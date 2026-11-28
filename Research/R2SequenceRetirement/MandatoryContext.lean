/-
Copyright (c) 2026 Heath Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Production.StreamAccum
public import Research.R2ScannerMapOwnership.Reachable

@[expose] public section R2SequenceRetirement
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.PreprocessIndentStable
namespace R2SequenceRetirement

/-! Mandatory completion → real stack context → marked-value projection.
    Capstone dependency: Blueprint 7.3 accumulation → 7.2 stream grammar.
    This module proves the contract algebra and the root sequence supplier.
    It does not assert that the complete PendingNode migration accepts. -/


def EntryStep (P : SurfPos → Prop) (own : Nat) (e : SurfPos) : Prop :=
  (∀ z, SCompactMapTail own e z → P z) ∧
  (∀ i c, SIndent own e i → GLit ':' i c →
    ∀ v, SBlockIndented own .blockOut c v → ∀ z, SCompactMapTail own v z → P z)

def levels (sc : ScannerState) : List FrameLevel :=
  sc.indents.toList.reverse.filterMap fun e =>
    if e.column < 0 then none
    else some (if e.isSequence then FrameLevel.seq e.column.toNat else FrameLevel.map e.column.toNat)

lemma EntryStep.map {P Q : SurfPos → Prop} {own : Nat} {e : SurfPos}
    (step : EntryStep P own e) (f : ∀ z, P z → Q z) : EntryStep Q own e :=
  ⟨fun z tail => f z (step.1 z tail),
   fun i c indent colon v value z tail => f z (step.2 i c indent colon v value z tail)⟩

lemma entryStep_of_question {P : SurfPos → Prop} {n : Nat} {q key e : SurfPos}
    (question : GLit '?' q key)
    (route : ∀ v, SBlockMapEntry n q v →
      ∀ z, SCompactMapTail n v z → P z)
    (content : SBlockIndented n .blockOut key e) : EntryStep P n e := by
  constructor
  · exact route e (SBlockMapEntry.explicitEmpty n q key e question content)
  · intro i c indent colon v value
    exact route v (SBlockMapEntry.explicit n q key e i c v question content indent colon value)


def Core (marks : List Nat) (P : SurfPos → Prop) : List FrameLevel → SurfPos → Prop
  | [], e => P e
  | ⟨k, true⟩ :: rest, e => ∀ z, SCompactSeqTail k e z → Core marks P rest z
  | ⟨k, false⟩ :: rest, e =>
      if k ∈ marks then EntryStep (Core marks P rest) k e
      else ∀ z, SCompactMapTail k e z → Core marks P rest z

abbrev Joint (sc : ScannerState) (P : SurfPos → Prop) (fs : List FrameLevel) (e : SurfPos) : Prop := Core (RegisterWitness.markedCols sc) P fs e

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
    · exact (show EntryStep (Joint sc P rest) k e from by simpa [Joint, Core, marked] using h).1 e
        (SCompactMapTail.nil k e)
    · exact (show ∀ z, SCompactMapTail k e z → Joint sc P rest z from by simpa [Joint, Core, marked] using h)
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
      · simp only [Joint, Core, ite_eq_left marked] at h ⊢
        exact EntryStep.map h (fun z hz => ih hz)
      · simp only [Joint, Core, ite_eq_right marked] at h ⊢
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
        simp only [Joint, Core, ite_eq_left marked, ite_eq_left old] at h ⊢
        exact EntryStep.map h (fun z hz => ih hz)
      · simp only [Joint, Core, ite_eq_right marked]
        by_cases old : k ∈ RegisterWitness.markedCols before
        · simp only [Joint, Core, ite_eq_left old] at h
          exact fun z tail => ih (h.1 z tail)
        · simp only [Joint, Core, ite_eq_right old] at h
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
        simp only [Joint, Core, ite_eq_left marked, ite_eq_left old] at h ⊢
        exact EntryStep.map h (fun z hz => ih hz lower)
      · simp only [Joint, Core, ite_eq_right marked]
        by_cases old : k ∈ RegisterWitness.markedCols before
        · simp only [Joint, Core, ite_eq_left old] at h
          exact fun z tail => ih (h.1 z tail) lower
        · simp only [Joint, Core, ite_eq_right old] at h
          exact fun z tail => ih (h z tail) lower

lemma Joint.question {sc : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {own : Nat} {q slot e : SurfPos}
    (marked : own ∈ RegisterWitness.markedCols sc) (literal : GLit '?' q slot)
    (route : ∀ v, SBlockMapEntry own q v →
      ∀ z, SCompactMapTail own v z → Joint sc P rest z)
    (key : SBlockIndented own .blockOut slot e) :
    Joint sc P (FrameLevel.map own :: rest) e := by
  simp only [Joint, Core, ite_eq_left marked]
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
  simp only [Joint, Core, ite_eq_left marked] at h
  simp only [Joint, Core, ite_eq_right consumed]
  exact fun z tail => Joint.restrict_marks (before := before) (after := after) (h.2 i c indent colon v value z tail) back

lemma Joint.sibling_sequence {before after : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {k : Nat} {land dash next e : SurfPos}
    (h : Joint before P (FrameLevel.seq k :: rest) land)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (indent : SIndent k land dash) (literal : GLit '-' dash next)
    (notNs : GNot SNsChar next) (node : SBlockIndented k .blockIn next e) :
    Joint after P (FrameLevel.seq k :: rest) e := by
  intro z tail
  exact Joint.restrict_marks (before := before) (after := after) (h z (SCompactSeqTail.cons k land dash next e z indent literal notNs node tail)) back


def Full (sc : ScannerState) (start e : SurfPos) : Prop := Context sc (SLYamlStream start) e

def frame (e : IndentEntry) : Option FrameLevel :=
  if e.column < 0 then none
  else some (if e.isSequence then FrameLevel.seq e.column.toNat else FrameLevel.map e.column.toNat)

lemma levels_indents {s t : ScannerState} (h : t.indents = s.indents) : levels t = levels s := by
  unfold levels
  rw [h]

lemma levels_push {s t : ScannerState} {e : IndentEntry}
    (h : t.indents = s.indents.push e) : levels t = (frame e).toList ++ levels s := by
  change t.indents.toList.reverse.filterMap frame =
    (frame e).toList ++ s.indents.toList.reverse.filterMap frame
  rw [h, Array.toList_push, List.reverse_append, List.filterMap_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.filterMap_cons, List.filterMap_nil]
  cases hf : frame e <;> rfl

-- Actual unwinding deletes an initial segment of the mixed top-first levels.
-- This is stronger than membership preservation and costs no scanner invariant.
lemma unwind_prefix (s : ScannerState) (col : Int) (fuel : Nat) :
    ∃ pre, levels s = pre ++ levels (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => exact ⟨[], by simp [unwindIndentsLoop]⟩
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · rename_i guard
      have parts : s.currentIndent > col ∧ s.indents.size > 1 := by simpa using guard
      have gt := parts.2
      let popped : ScannerState := { s.emit .blockEnd with
        indents := (s.emit .blockEnd).indents.pop,
        pendingKeys := (s.emit .blockEnd).pendingKeys.pop }
      obtain ⟨pre, old⟩ := ih popped
      have pushed : s.indents = popped.indents.push s.indents.back! :=
        Array.eq_push_pop_back!_of_size_ne_zero (by omega)
      have shape := levels_push pushed
      refine ⟨(frame s.indents.back!).toList ++ pre, ?_⟩
      rw [shape, old, List.append_assoc]
    · exact ⟨[], rfl⟩

lemma stale_indents (s : ScannerState) : (closeStaleExplicitKey s).indents = s.indents := by
  rcases L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_cases s with eq | ⟨_, _, eq⟩
  · rw [eq]
  · rw [eq]; rfl

lemma preprocess_prefix {s t : ScannerState} {c : Char}
    (step : scanNextToken_preprocess s = .ok (some (t,c))) :
    ∃ pre, levels s = pre ++ levels t := by
  unfold scanNextToken_preprocess at step
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at step
  split at step
  · contradiction
  · rename_i skipped skip
    have same : levels skipped = levels s :=
      levels_indents (skipToContent_preserves_indents s skipped skip)
    split at step
    · simp at step
    · split at step
      · split at step
        · contradiction
        · split at step
          · simp at step
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl,rfl⟩ := step
            obtain ⟨pre, shape⟩ := unwind_prefix skipped (skipped.col : Int) skipped.indents.size
            refine ⟨pre, ?_⟩
            rw [← same, shape]
            congr 1
            apply levels_indents
            rw [stale_indents, saveSimpleKey_preserves_indents]
            rfl
      · split at step
        · contradiction
        · split at step
          · simp at step
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl,rfl⟩ := step
            refine ⟨[], ?_⟩
            simp only [List.nil_append]
            rw [← same]
            symm
            apply levels_indents
            rw [stale_indents, saveSimpleKey_preserves_indents]

lemma context_preprocess {s t : ScannerState} {c : Char} {P : SurfPos → Prop} {e : SurfPos}
    (step : scanNextToken_preprocess s = .ok (some (t,c)))
    (context : Context s P e) : Context t P e := by
  obtain ⟨pre, shape⟩ := preprocess_prefix step
  change Joint s P (levels s) e at context
  rw [shape] at context
  exact Joint.restrict_marks (Joint.drop context)
    (fun _ marked => (RegisterWitness.preprocess_markedCols step
      (RegisterWitness.MarkedColsIn.self s)).mem marked)

lemma context_transport {s t : ScannerState} {P : SurfPos → Prop} {e : SurfPos}
    (context : Context s P e) (keys : t.pendingKeys = s.pendingKeys)
    (indents : t.indents = s.indents) : Context t P e := by
  change Joint t P (levels t) e
  rw [levels_indents indents]
  exact context.restrict_marks
    (fun _ marked => ((RegisterWitness.MarkedColsIn.self s).transport keys indents).mem marked)

-- This is the scanner's existing flag update between preprocessing and block
-- dispatch. It introduces no new state or independently stored snapshot.
def dispatchState (prep : ScannerState) : ScannerState :=
  if prep.allowDirectives then {prep with allowDirectives := false, documentEverStarted := true}
  else prep

lemma context_dispatch {s : ScannerState} {P : SurfPos → Prop} {e : SurfPos}
    (context : Context s P e) : Context (dispatchState s) P e := by
  unfold dispatchState
  split
  · exact context_transport context rfl rfl
  · exact context



lemma Full.close {s : ScannerState} {start e : SurfPos} (h : Full s start e) : SLYamlStream start e := Joint.close h

lemma Full.of_eq {s t : ScannerState} {start e : SurfPos} (h : Full s start e)
    (keys : t.pendingKeys = s.pendingKeys) (indents : t.indents = s.indents) : Full t start e :=
  context_transport h keys indents

lemma Full.preprocess {s t : ScannerState} {start e : SurfPos} {c : Char}
    (h : Full s start e) (step : scanNextToken_preprocess s = .ok (some (t,c))) : Full t start e :=
  context_preprocess step h

lemma Full.content {s prep t : ScannerState} {start e : SurfPos} {c : Char}
    (h : Full s start e) (preprocess : scanNextToken_preprocess s = .ok (some (prep,c)))
    (step : scanNextToken_dispatchContent (dispatchState prep) c = .ok t) : Full t start e := by
  have atDispatch : Full (dispatchState prep) start e := context_dispatch (h.preprocess preprocess)
  exact atDispatch.of_eq (L4YAML.Proofs.PendingKeySound.dispatchContent_pendingKeys step)
    (IndentStackBase.dispatchContent_preserves_indents step)


/-- Retain an arbitrary second sibling suffix rather than closing the first
    completion with nil. This is the required pending-entry answer. -/
lemma seqTail_append {n : Nat} :
    ∀ {a b c : SurfPos}, SCompactSeqTail n a b → SCompactSeqTail n b c → SCompactSeqTail n a c
  | _, _, _, .nil _ _, second => second
  | _, _, _, .cons _ a i next e _ indent dash notNs node tail, second =>
      SCompactSeqTail.cons n a i next e _ indent dash notNs node (seqTail_append tail second)

lemma Full.sequence {sc : ScannerState} {start e : SurfPos} {k : Nat}
    (shape : levels sc = [FrameLevel.seq k])
    (route : ∀ z, SCompactSeqTail k e z → SLYamlStream start z) : Full sc start e := by
  change Core (RegisterWitness.markedCols sc) (SLYamlStream start) (levels sc) e
  rw [shape]
  exact route

lemma Full.sequence_after {sc : ScannerState} {start e z : SurfPos} {k : Nat}
    (shape : levels sc = [FrameLevel.seq k])
    (route : ∀ y, SCompactSeqTail k e y → SLYamlStream start y)
    (tail : SCompactSeqTail k e z) : Full sc start z :=
  Full.sequence shape (fun y later => route y (seqTail_append tail later))

lemma levels_of_negative {sc : ScannerState} (mono : IndentStackMono.Mono sc)
    (negative : sc.currentIndent < 0) : levels sc = [] := by
  change sc.indents.toList.reverse.filterMap frame = []
  apply List.filterMap_eq_nil_iff.mpr
  intro entry member
  have inside : entry ∈ sc.indents := by simpa using member
  have le := mono.le_currentIndent entry inside
  simp [frame, show entry.column < 0 by omega]

lemma scan_sequence_at_base {s t : ScannerState}
    (mono : IndentStackMono.Mono s) (negative : s.currentIndent < 0)
    (flow : s.inFlow = false) (step : scanBlockEntry s = .ok t) :
    levels t = [FrameLevel.seq s.col] := by
  have pushed : t.indents = s.indents.push { column := (s.col : Int), isSequence := true } := by
    rw [L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents flow step]
    unfold pushSequenceIndent
    simp [show s.currentIndent < (s.col : Int) by omega]
  rw [levels_push pushed, levels_of_negative mono negative]
  simp [frame]

lemma Full.at_base {sc : ScannerState} {start e : SurfPos}
    (mono : IndentStackMono.Mono sc) (negative : sc.currentIndent < 0)
    (stream : SLYamlStream start e) : Full sc start e := by
  change Core (RegisterWitness.markedCols sc) (SLYamlStream start) (levels sc) e
  rw [levels_of_negative mono negative]
  exact stream

/-- Transport the existing complete entry domain through the real dash.
    Both scanner branches are covered: a new sequence level is pushed, or
    an indentless sequence keeps the existing mapping level. No sequence-top
    premise or new saved state/index is required. -/
lemma Full.sequence_step {sc prep after : ScannerState}
    {start e z : SurfPos} {k : Nat}
    (route : ∀ y, SCompactSeqTail k e y → Full sc start y)
    (preprocess : scanNextToken_preprocess sc = .ok (some (prep, '-')))
    (flow : (dispatchState prep).inFlow = false)
    (step : scanBlockEntry (dispatchState prep) = .ok after)
    (slots : PendingKeySound.SlotsOk (dispatchState prep))
    (column : (dispatchState prep).col = k)
    (tail : SCompactSeqTail k e z) : Full after start z := by
  have atDispatch : ∀ y, SCompactSeqTail k e y → Full (dispatchState prep) start y :=
    fun y future => context_dispatch ((route y future).preprocess preprocess)
  by_cases pushed : (dispatchState prep).currentIndent < ((dispatchState prep).col : Int)
  · have indents : after.indents = (dispatchState prep).indents.push
        { column := ((dispatchState prep).col : Int), isSequence := true } := by
      rw [L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents flow step]
      unfold pushSequenceIndent
      simp [pushed]
    have shape : levels after = FrameLevel.seq k :: levels (dispatchState prep) := by
      simpa [frame, column, show ¬(k : Int) < 0 by omega] using levels_push indents
    have back : ∀ x ∈ RegisterWitness.markedCols after,
        x ∈ RegisterWitness.markedCols (dispatchState prep) :=
      fun _ marked => (RegisterWitness.scanBlockEntry_markedCols flow step
        (RegisterWitness.MarkedColsIn.self (dispatchState prep)) slots).mem marked
    change Joint after (SLYamlStream start) (levels after) z
    rw [shape]
    intro y future
    exact Joint.restrict_marks (atDispatch y (seqTail_append tail future)) back
  · have indents : after.indents = (dispatchState prep).indents := by
      rw [L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents flow step]
      unfold pushSequenceIndent
      simp [pushed]
    have keys : after.pendingKeys = (dispatchState prep).pendingKeys := by
      rw [PendingKeySound.scanBlockEntry_pendingKeys flow step]
      unfold pushSequenceIndent
      simp [pushed]
    exact (atDispatch z tail).of_eq keys indents

/-- A marked mapping's value line is a projection of the whole context.
    Every inner collection is closed by its nil tail only in this view;
    the original context remains available to sibling readers. -/
lemma Joint.value_line {sc : ScannerState} {P : SurfPos → Prop}
    {fs : List FrameLevel} {e : SurfPos} {nv : Nat}
    (h : Joint sc P fs e) (marked : nv ∈ RegisterWitness.markedCols sc)
    (member : FrameLevel.map nv ∈ fs) :
    ∀ i c, SIndent nv e i → GLit ':' i c →
    ∀ v, SBlockIndented nv .blockOut c v →
    ∀ z, SCompactMapTail nv v z → P z := by
  induction fs generalizing e with
  | nil => cases member
  | cons top rest ih =>
    rcases List.mem_cons.mp member with same | lower
    · subst top
      have entry : EntryStep (Joint sc P rest) nv e := by
        simpa [Joint, Core, marked] using h
      intro i c indent colon v value z tail
      exact Joint.close (entry.2 i c indent colon v value z tail)
    · exact ih (Joint.pop h) lower

lemma levels_cover_marks {sc : ScannerState} (slots : PendingKeySound.SlotsOk sc)
    (maps : R2MapOwnership.Maps sc) :
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

lemma Full.value_line {sc : ScannerState} {start e : SurfPos}
    (h : Full sc start e) (slots : PendingKeySound.SlotsOk sc)
    (maps : R2MapOwnership.Maps sc) :
    ∀ nv ∈ RegisterWitness.markedCols sc, ExplValueLine start nv e := by
  intro nv marked i c indent colon v value
  exact ResumeFrames.one (fun z tail =>
    Joint.value_line h marked (levels_cover_marks slots maps nv marked)
      i c indent colon v value z tail)


/-- The real root dash supplies the mandatory continuation for every entry
    body, first sibling suffix, and further suffix. No root context is assumed.
    Its prefix is the existing virgin PendingNode's document-prefix field. -/
lemma root_sequence_supplier {sc prep after : ScannerState}
    {start before land dash next : SurfPos} {k : Nat}
    (mono : IndentStackMono.Mono sc) (base : IndentStackBase.SentinelBase sc)
    (negative : sc.currentIndent < 0)
    (documentPrefix : GStar SLDocumentPrefix start before)
    (preprocess : scanNextToken_preprocess sc = .ok (some (prep, '-')))
    (flow : (dispatchState prep).inFlow = false)
    (step : scanBlockEntry (dispatchState prep) = .ok after)
    (corr : ScannerSurfCorr prep dash)
    (comments : SSLComments before land) (landing : land.col = 0)
    (indent : SIndent k land dash)
    (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    ∀ e, SBlockIndented k .blockIn next e →
    ∀ z, SCompactSeqTail k e z → Full after start z := by
  have small := size_le_one_of_currentIndent_neg base mono negative
  have indents := preprocess_indents_of_size_le_one small preprocess
  have monoPrep := IndentStackMono.preprocess_mono preprocess mono
  have dispatchIndents : (dispatchState prep).indents = prep.indents := by
    unfold dispatchState; split <;> rfl
  have monoDispatch := monoPrep.of_indents_eq dispatchIndents
  have negativePrep : prep.currentIndent < 0 := by
    simpa only [ScannerState.currentIndent, indents] using negative
  have negativeDispatch : (dispatchState prep).currentIndent < 0 := by
    unfold dispatchState; split <;> exact negativePrep
  have column : (dispatchState prep).col = k := by
    have measure := SIndent_col indent
    have agree := corr.col_eq
    unfold dispatchState; split <;> change prep.col = k <;> omega
  have shape := scan_sequence_at_base monoDispatch negativeDispatch flow step
  rw [column] at shape
  intro e node z tail
  apply Full.sequence_after shape (tail := tail)
  intro y siblings
  exact SLYamlStream.single start before y y documentPrefix
    (GOpt.some before y (SLAnyDocument.bare before y
      (SLBareDocument.mk before y (rootBlockSeq k comments
        (SBlockSeqEntries_of_compactTail indent literal notNs node siblings)))))
    (GStar.nil y)

/-- The pending sequence's critical pack is an answer of its existing
    mandatory completion, once that completion retains the whole context. -/
lemma sequence_value_pack {sc : ScannerState} {start slot : SurfPos} {n : Nat}
    (complete : ∀ e, SBlockIndented n .blockIn slot e →
      ∀ z, SCompactSeqTail n e z → Full sc start z)
    (sound : PendingKeySound.Sound sc) (maps : R2MapOwnership.Maps sc) :
    ∀ nv ∈ RegisterWitness.markedCols sc,
    ∀ e, SBlockIndented n .blockIn slot e →
    ∀ z, SCompactSeqTail n e z → ExplValueLine start nv z := by
  intro nv marked e node z tail
  exact (complete e node z tail).value_line sound.slots maps nv marked

/-- The completed sequence has the same projection, with its SSLComments
    completion domain. This pays the field and forwarding parameter together. -/
lemma completed_sequence_value_pack {sc : ScannerState} {start gram : SurfPos} {n : Nat}
    (complete : ∀ e, SSLComments gram e →
      ∀ z, SCompactSeqTail n e z → Full sc start z)
    (sound : PendingKeySound.Sound sc) (maps : R2MapOwnership.Maps sc) :
    ∀ nv ∈ RegisterWitness.markedCols sc,
    ∀ e, SSLComments gram e →
    ∀ z, SCompactSeqTail n e z → ExplValueLine start nv z := by
  intro nv marked e comments z tail
  exact (complete e comments z tail).value_line sound.slots maps nv marked

/-- The content pack's three old locations read this same projection.
    The scanner's existing gates remain the completion's real domain. -/
lemma content_value_pack {sc : ScannerState} {start gram : SurfPos}
    (complete : danglingNodePos? sc = none → underIndentedFlowValuePos? sc = none →
      ∀ e, SSLComments gram e → Full sc start e)
    (sound : PendingKeySound.Sound sc) (maps : R2MapOwnership.Maps sc)
    (noDangling : danglingNodePos? sc = none)
    (noUnderIndent : underIndentedFlowValuePos? sc = none) :
    ∀ nv ∈ RegisterWitness.markedCols sc,
    ∀ e, SSLComments gram e → ExplValueLine start nv e := by
  intro nv marked e comments
  exact (complete noDangling noUnderIndent e comments).value_line sound.slots maps nv marked

#print axioms Full.content
#print axioms Full.sequence_step
#print axioms root_sequence_supplier
#print axioms sequence_value_pack
#print axioms completed_sequence_value_pack
#print axioms content_value_pack

end R2SequenceRetirement
end R2SequenceRetirement
