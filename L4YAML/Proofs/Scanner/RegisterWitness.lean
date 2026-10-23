/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Scanner.PendingKeySound

@[expose] public section Blanket

/-!
# The register witness, stated and seeded (DOCS item 342)

Item 340 built the flip (`PackAlt sc := ExplicitValueRefused sc`) to a fixpoint
and found 72 consumer sites STARVED: a park whose register is LIVE owes the
informative side of its pack — the `?` the register names and that `?`'s route
to the stream — and nothing in the scanner state said which `?` that was.
Item 338's `Sound` ties the register to the innermost marked slot of
`pendingKeys`; this module ties each marked slot to a surface `?`:

* `AtCol input c sp` — `sp` is a suffix of `input` standing at column `c`.
  Item 341 named this relation `AtLineCol`; the LINE half is not stated.  No
  fact in the tree relates `sc.line` to the input (`ScannerSurfCorr` carries
  `col_eq` and `input_prefix`, nothing about newlines), so a line component
  would have no cursor bridge and the seed could not pay it.  No consumer reads
  the register's line (item 338 deleted the hook's `line != ekLine` guard), so
  the column and the suffix are the whole of what the witness must say.
* `QuestionEntry input sp_start c sp_q` — the informative side of the
  `?`-entry pack, keyed by the `?`'s column: `sp_q` stands at `c`, reads `?`,
  and every `[186]` entry it opens closes the stream.
* `SlotWitness input sc sp_start i` — a marked slot `pendingKeys[i] = some l` at
  column `indentColumns[i] = c` has a `QuestionEntry` at `c` in `input` — the
  stream's constant, taken as a parameter rather than read off `sc.input` so no
  writer owes an input-preservation lemma (item 343).
* `RegWitness sc sp_start` — outside flow, a live register `(some l, c)` has a
  `QuestionEntry` at `c`; `regWitness_of_slots` derives it from `RegOk` and
  the slot witnesses (`innermost_some_mem`), so the writers carry the slots.
* `scanKey_witness` — the seed: the `?` just scanned is `sp_q`, its route is
  the premise `question_open_map` already holds (`h_expl`'s informative side).

The writer lemmas through `scanNextToken` are item 343's; the flip that reads
`inl`/`inr` off the register is item 344's.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.RegisterWitness

open L4YAML.Scanner
open L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.CloseStaleExplicitKey

/-! ## §1  The relations -/

/-- `sp` is the suffix of `input` standing at column `c`. -/
def AtCol (input : String) (c : Nat) (sp : SurfPos) : Prop :=
  sp.col = c ∧ ∃ pre : List Char, input.toList = pre ++ sp.chars

/-- The cursor bridge: the scanner's own surface position stands at its column. -/
lemma AtCol.of_corr {sc : ScannerState} {sp : SurfPos} (h : ScannerSurfCorr sc sp) :
    AtCol sc.input sc.col sp :=
  ⟨h.col_eq, let ⟨pre, hpre, _⟩ := h.input_prefix; ⟨pre, hpre⟩⟩

/-- The informative side of the `?`-entry pack, keyed by the `?`'s column `c`. -/
def QuestionEntry (input : String) (sp_start : SurfPos) (c : Nat) (sp_q : SurfPos) : Prop :=
  AtCol input c sp_q ∧ (∃ sp_q' : SurfPos, GLit '?' sp_q sp_q') ∧
  ∀ sp_v : SurfPos, SBlockMapEntry c sp_q sp_v → SLYamlStream sp_start sp_v

/-- A marked slot names a `?` at its level's column. -/
def SlotWitness (input : String) (sc : ScannerState) (sp_start : SurfPos) (i : Nat) : Prop :=
  ∀ l : Nat, sc.pendingKeys[i]? = some (some l) →
    ∃ (c : Nat) (sp_q : SurfPos), sc.indentColumns[i]? = some (c : Int) ∧
      QuestionEntry input sp_start c sp_q

/-- Every marked slot names a `?`. -/
def SlotsWitness (input : String) (sc : ScannerState) (sp_start : SurfPos) : Prop :=
  ∀ i : Nat, SlotWitness input sc sp_start i

/-- Outside flow, a live register names a `?` at its column. -/
def RegWitness (input : String) (sc : ScannerState) (sp_start : SurfPos) : Prop :=
  sc.flowLevel = 0 → ∀ (l : Nat) (c : Int),
    sc.explicitKeyLine = some l → sc.explicitKeyCol = c →
    ∃ (cn : Nat) (sp_q : SurfPos), c = (cn : Int) ∧ QuestionEntry input sp_start cn sp_q

/-- The register's witness is the innermost marked slot's (`RegOk`). -/
lemma regWitness_of_slots {input : String} {sc : ScannerState} {sp_start : SurfPos}
    (hreg : RegOk sc) (hw : SlotsWitness input sc sp_start) : RegWitness input sc sp_start := by
  intro h0 l c hl hc
  have hinn : PendingKeys.innermost sc.indentColumns sc.pendingKeys = (some l, c) := by
    rw [← innermostPendingKey_eq, ← hreg h0, hl, hc]
  obtain ⟨i, _, hi, hci⟩ := innermost_some_mem _ _ _ _ hinn
  obtain ⟨cn, sp_q, hcol, hq⟩ := hw i l hi
  refine ⟨cn, sp_q, ?_, hq⟩
  rw [hcol] at hci
  simpa using hci.symm

/-- Transport along a step that moves neither field the witness reads.  (The input is the
    stream's constant — a parameter, not a field — so no step has to preserve it.) -/
lemma SlotsWitness.transport {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents) :
    SlotsWitness input s' sp_start := by
  intro i l hi
  rw [hpk] at hi
  obtain ⟨c, sp_q, hc, hq⟩ := h i l hi
  exact ⟨c, sp_q, by rw [ScannerState.indentColumns, hind]; exact hc, hq⟩

/-! ## §2  The seed -/

lemma scanKey_input {s s' : ScannerState} (hok : scanKey s = .ok s') : s'.input = s.input := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       show (ScannerState.advance (ScannerState.emit _ _)).input = _
       rw [advance_input]
       simp [ScannerState.emit, L4YAML.Proofs.ScannerProgress.pushMappingIndent_input])
    | simp_all

/-- Below the top, `pushMappingIndent` moves neither a slot nor a column. -/
lemma pushMappingIndent_getElem?_of_lt (s : ScannerState) (col : Int) (i : Nat)
    (hi : i < s.indents.size) (hsz : s.pendingKeys.size = s.indents.size) :
    (pushMappingIndent s col).pendingKeys[i]? = s.pendingKeys[i]? ∧
    (pushMappingIndent s col).indentColumns[i]? = s.indentColumns[i]? := by
  unfold pushMappingIndent
  split
  · simp only [ScannerState.indentColumns, ScannerState.emit]
    constructor
    · rw [Array.getElem?_push, if_neg (by omega)]
    · rw [Array.map_push, Array.getElem?_push, if_neg (by simpa using Nat.ne_of_lt hi)]
  · exact ⟨rfl, rfl⟩

/-- **The seed.**  A `?` scanned outside flow marks the level at its own column, and
    the `?` itself is the witness: the surface position the cursor stood on reads `?`
    (`peek_corr`), stands at the register's column (`AtCol.of_corr`), and its
    `[186]` route is the premise the `?` producer holds. -/
lemma scanKey_witness {s s' : ScannerState} {sp sp_start : SurfPos}
    (hcorr : ScannerSurfCorr s sp) (h_noflow : s.inFlow = false)
    (hok : scanKey s = .ok s') (hs : SlotsOk s) (hbase : SentinelBase s)
    (hcol : s.currentIndent ≤ (s.col : Int)) (hpeek : s.peek? = some '?')
    (h_route : ∀ sp_v : SurfPos, SBlockMapEntry s.col sp sp_v → SLYamlStream sp_start sp_v)
    (hw : SlotsWitness s.input s sp_start) : SlotsWitness s.input s' sp_start := by
  have hind := L4YAML.Proofs.PreprocessIndentStable.scanKey_indents h_noflow hok
  have hpk := scanKey_pendingKeys h_noflow hok
  obtain ⟨pm, hpm⟩ : ∃ pm, pm = pushMappingIndent s (s.col : Int) := ⟨_, rfl⟩
  rw [← hpm] at hind hpk
  have hsl : SlotsOk pm := hpm ▸ pushMappingIndent_slots s _ hs
  have hsz := hsl.1
  have hpos : 0 < pm.indents.size :=
    hpm ▸ (L4YAML.Proofs.IndentStackBase.pushMappingIndent_base s _ hbase).size_pos
  have htop_ci : pm.currentIndent = (s.col : Int) := by
    rw [hpm]
    exact Int.le_antisymm (L4YAML.Proofs.IndentStackCover.pushMappingIndent_top_le hcol)
      (L4YAML.Proofs.PreprocessIndentStable.pushMappingIndent_le s _)
  have htop : pm.indentColumns[pm.indents.size - 1]? = some (s.col : Int) := by
    rw [indentColumns_getElem?, Array.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some]
    rw [← L4YAML.Proofs.IndentStackMono.currentIndent_eq_last hpos, htop_ci]
  have hcols' : s'.indentColumns = pm.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  -- the `?` the cursor stands on
  have hmore : s.offset < s.inputEnd := by
    by_cases hne : s.offset < s.inputEnd
    · exact hne
    · simp [ScannerState.peek?, hne] at hpeek
  obtain ⟨c, rest, hchars, hpc⟩ := peek_corr s sp hcorr hmore
  rw [hpeek] at hpc
  have hc : c = '?' := (Option.some.inj hpc).symm
  subst hc
  have hq : QuestionEntry s.input sp_start s.col sp := by
    refine ⟨AtCol.of_corr hcorr, ⟨⟨rest, sp.col + 1⟩, ?_⟩, h_route⟩
    have : sp = ⟨'?' :: rest, sp.col⟩ := by cases sp; simp_all
    rw [this]; exact GLit.mk rest sp.col
  intro i l hi
  rw [hcols']
  rw [hpk, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hi
  split at hi
  · rename_i heq
    subst heq
    exact ⟨s.col, sp, htop, hq⟩
  · rename_i hne
    have hi' : i < pm.indents.size := by
      obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.1 hi
      omega
    by_cases hlt : i < s.indents.size
    · obtain ⟨hpk_i, hcol_i⟩ := hpm ▸ pushMappingIndent_getElem?_of_lt s (s.col : Int) i hlt hs.1
      rw [hpk_i] at hi
      obtain ⟨c, sp_q, hc, hq'⟩ := hw i l hi
      exact ⟨c, sp_q, by rw [hcol_i]; exact hc, hq'⟩
    · -- `i` is the pushed level's slot, which is empty
      exfalso
      rw [hpm] at hi
      unfold pushMappingIndent at hi
      have hsz0 := hs.1
      split at hi
      · simp only [ScannerState.emit] at hi
        rw [Array.getElem?_push] at hi
        split at hi
        · simp at hi
        · obtain ⟨hlt', _⟩ := Array.getElem?_eq_some_iff.1 hi
          omega
      · obtain ⟨hlt', _⟩ := Array.getElem?_eq_some_iff.1 hi
        omega


/-! ## §3  The writers (DOCS item 343)

`SlotsWitness` reads `pendingKeys`, `indents` and `input` only, so a writer is one of
three shapes: a PUSH (one empty slot on top, the slots below untouched), a POP (the
top slot goes, the slots below untouched), or a CLOSE (`PendingKeys.closeAt`: a slot
is kept or emptied, never re-marked).  Everything else is `SlotsWitness.transport`. -/

/-- A pushed level's own slot is `none`; the slots below are the pre-state's. -/
lemma SlotsWitness.push {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start)
    (e : IndentEntry) (hind : s'.indents = s.indents.push e)
    (hpk : s'.pendingKeys = s.pendingKeys.push none)
    (hsz : s.pendingKeys.size = s.indents.size) : SlotsWitness input s' sp_start := by
  intro i l hi
  rw [hpk, Array.getElem?_push] at hi
  split at hi
  · simp at hi
  · obtain ⟨c, sp_q, hc, hq⟩ := h i l hi
    refine ⟨c, sp_q, ?_, hq⟩
    rw [indentColumns_getElem?] at hc
    have hlt : i < s.indents.size := by
      rcases hx : s.indents[i]? with _ | e
      · simp [hx] at hc
      · exact (Array.getElem?_eq_some_iff.1 hx).1
    rw [indentColumns_getElem?, hind, Array.getElem?_push, if_neg (by omega)]
    exact hc

/-- Popping the top level keeps every remaining slot's witness. -/
lemma SlotsWitness.pop {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start)
    (hind : s'.indents = s.indents.pop) (hpk : s'.pendingKeys = s.pendingKeys.pop)
    (hsz : s.pendingKeys.size = s.indents.size) :
    SlotsWitness input s' sp_start := by
  intro i l hi
  rw [hpk, Array.getElem?_pop] at hi
  split at hi
  · obtain ⟨c, sp_q, hc, hq⟩ := h i l hi
    refine ⟨c, sp_q, ?_, hq⟩
    rw [indentColumns_getElem?, hind, Array.getElem?_pop, if_pos (by omega)]
    rw [indentColumns_getElem?] at hc; exact hc
  · cases hi

/-- `closeAt` empties slots and re-marks none, so every slot still marked keeps its witness. -/
lemma SlotsWitness.close {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (col : Int) :
    SlotsWitness input (s.clearPendingKeyAt col) sp_start := by
  intro i l hi
  simp only [ScannerState.clearPendingKeyAt] at hi
  exact h i l (closeAt_marked _ _ _ _ _ hi).1

lemma pushMappingIndent_witness {input : String} {s : ScannerState} {sp_start : SurfPos} (col : Int)
    (h : SlotsWitness input s sp_start) (hsz : s.pendingKeys.size = s.indents.size) :
    SlotsWitness input (pushMappingIndent s col) sp_start := by
  unfold pushMappingIndent
  split
  · exact h.push { column := col, isSequence := false } (by simp [ScannerState.emit])
      (by simp [ScannerState.emit]) hsz
  · exact h

lemma pushSequenceIndent_witness {input : String} {s : ScannerState} {sp_start : SurfPos} (col : Int)
    (h : SlotsWitness input s sp_start) (hsz : s.pendingKeys.size = s.indents.size) :
    SlotsWitness input (pushSequenceIndent s col) sp_start := by
  unfold pushSequenceIndent
  split
  · exact h.push { column := col, isSequence := true } (by simp [ScannerState.emit])
      (by simp [ScannerState.emit]) hsz
  · exact h

/-- The re-read writes the register only. -/
lemma readPendingKey_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input s.readPendingKey sp_start := h

/-- The stale-key hook: the identity, or a close followed by the re-read. -/
lemma closeStaleExplicitKey_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input (closeStaleExplicitKey s) sp_start := by
  rcases closeStaleExplicitKey_cases s with heq | heq <;> rw [heq]
  · exact h
  · exact readPendingKey_witness (h.close _)

lemma unwindIndentsLoop_witness {input : String} (s : ScannerState) (col : Int) (fuel : Nat)
    {sp_start : SurfPos} (h : SlotsWitness input s sp_start) (hs : SlotsOk s) :
    SlotsWitness input (unwindIndentsLoop s col fuel) sp_start := by
  induction fuel generalizing s with
  | zero => simpa [unwindIndentsLoop] using h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · obtain ⟨h1, h2, -⟩ := unwindPop_fields s
      exact ih _ (h.pop h1 h2 hs.1) (hs.pop h1 h2)
    · exact h

lemma unwindIndents_witness {input : String} (s : ScannerState) (col : Int) {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (hs : SlotsOk s) :
    SlotsWitness input (unwindIndents s col) sp_start :=
  unwindIndentsLoop_witness s col _ h hs

end L4YAML.Proofs.RegisterWitness

end Blanket
