/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Coupling.StructureCoupling
public import L4YAML.Proofs.Scanner.FlowAdjacency
public import L4YAML.Proofs.Scanner.BlockScalarFlowGuard
public import L4YAML.Proofs.Scanner.AliasTrailingContent
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

public meta import L4YAML.CapstoneAttr
@[expose] public section Blanket

/-!
# Scan-Strict Coupling: Full-Consumption Infrastructure

Phase A of v0.4.4. Composes the 80+ leaf coupling theorems from
CouplingBridge, ScannerCoupling, ScalarCoupling, and StructureCoupling
into top-level theorems showing that `scan` consumes all input characters.

## Main Results

- `scanNextToken_corr`: each scanNextToken step preserves ScannerSurfCorr
- `scanNextToken_none_consumed`: when scanNextToken returns none, input is consumed
- `scanLoop_full_consumption`: after scanLoop succeeds, all characters consumed
- `scan_full_consumption`: successful scan provides its reachable EOF state, exact fuel and returned tokens

## Architecture

```
chars_from_zero_toList          -- String ↔ CharsFromOffset bridge
    ↓
scanNextToken_preprocess_corr   -- skipToContent + unwind + saveKey
    ↓
scanNextToken_dispatch*_corr    -- 4 dispatch couplings composing leaf theorems
    ↓
scanNextToken_corr              -- full token step
    ↓
scanLoop_full_consumption       -- fuel induction
    ↓
scan_full_consumption           -- initial state + BOM + loop
```
-/

set_option autoImplicit false

namespace L4YAML.Proofs.ScanStrictCoupling

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.BlockScalarFlowGuard
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.StructureCoupling
open L4YAML.Proofs.FlowAdjacency

/-! ## §1 CharsFromOffset–toList Bridge -/

-- The initial character list matches input.toList.
-- CharsFromOffset iterates byte positions using get/next, while
-- String.toList iterates using String.Internal.toArray.
-- Both traverse valid UTF-8 and produce identical character sequences.
lemma chars_from_zero_toList (input : String) :
    CharsFromOffset input 0 input.toList :=
  CouplingBridge.chars_from_zero_toList input

/-! ## §1.5 Preservation Lemmas

Field-preservation lemmas for unwindIndentsLoop and saveSimpleKey:
offset, inputEnd, and input are unchanged by these bookkeeping operations. -/

lemma unwindIndentsLoop_offset (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).offset = s.offset := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

lemma unwindIndentsLoop_inputEnd (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).inputEnd = s.inputEnd := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

lemma unwindIndentsLoop_input (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).input = s.input := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

lemma saveSimpleKey_offset (s : ScannerState) :
    (saveSimpleKey s).offset = s.offset := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

lemma saveSimpleKey_inputEnd (s : ScannerState) :
    (saveSimpleKey s).inputEnd = s.inputEnd := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

lemma saveSimpleKey_input (s : ScannerState) :
    (saveSimpleKey s).input = s.input := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

lemma saveSimpleKey_peek (s : ScannerState) :
    (saveSimpleKey s).peek? = s.peek? := by
  unfold ScannerState.peek?
  simp only [saveSimpleKey_offset, saveSimpleKey_inputEnd, saveSimpleKey_input]

/-! ## §2 Dispatch Couplings

Each dispatch function processes one category of YAML tokens.
These theorems compose the leaf _corr theorems from StructureCoupling
and ScalarCoupling. -/

-- Structural dispatch: document markers and directives.
lemma scanNextToken_dispatchStructural_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchStructural sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- item 50: the floor refuses outright (the `]`/`}` exemption is gone)
    simp at hok
  · split at hok
    · simp at hok
    · split at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanDocumentStart_corr sc sp hcorr
      · split at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h; subst h
            exact scanDocumentEnd_corr sc sp hcorr _ ‹_›
        · split at hok
          · split at hok
            · simp at hok
            · have h := Except.ok.inj hok; injection h with h; subst h
              exact scanDirective_corr sc sp hcorr _ ‹_›
          · simp at hok

-- Flow indicator dispatch: [ ] { } ,
lemma scanNextToken_dispatchFlowIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchFlowIndicators sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  replace hok := peel_flowAdj hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · have h := Except.ok.inj hok; injection h with h; subst h
    exact scanFlowSequenceStart_corr sc sp hcorr
  · split at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h; subst h
            exact scanFlowSequenceEnd_corr sc sp hcorr
    · split at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanFlowMappingStart_corr sc sp hcorr
      · split at hok
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · have h := Except.ok.inj hok; injection h with h; subst h
                exact scanFlowMappingEnd_corr sc sp hcorr
        · split at hok
          · split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · have h := Except.ok.inj hok; injection h with h; subst h
                exact scanFlowEntry_corr sc sp hcorr _ ‹_›
          · simp at hok

-- Block indicator dispatch: - ? :
lemma scanNextToken_dispatchBlockIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchBlockIndicators sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · split at hok
    · simp at hok
    · have h := Except.ok.inj hok; injection h with h; subst h
      exact scanBlockEntry_corr sc sp hcorr _ ‹_›
  · split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanKey_corr sc sp hcorr _ ‹_›
    · split at hok
      · split at hok
        · simp at hok
        · have h := Except.ok.inj hok; injection h with h; subst h
          exact scanValue_corr sc sp hcorr _ ‹_›
      · simp at hok

-- Content dispatch: & * ! | > " ' plain scalars.
lemma scanNextToken_dispatchContent_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- '&': item-9e property-run guard, then the scanAnchorOrAlias bind
    split at hok
    · simp at hok
    generalize h_anch : scanAnchorOrAlias sc true = result at hok
    cases result with
    | error e => simp at hok
    | ok s_a =>
      have h := Except.ok.inj hok; subst h
      obtain ⟨sp', hcorr'⟩ := scanAnchorOrAlias_corr sc sp hcorr true s_a h_anch
      exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  · split at hok
    · split at hok   -- item 9e: the property-run guard
      · simp at hok
      split at hok
      · simp at hok
      · -- '*': item 9h peels `validateAliasClose`, then the alias bind.
        exact scanAnchorOrAlias_corr sc sp hcorr false _ (aliasArm_scan_ok hok)
    · split at hok
      · -- '!': item-9e property-run guard, then the scanTag bind
        split at hok
        · simp at hok
        generalize h_tag : scanTag sc = result at hok
        cases result with
        | error e => simp at hok
        | ok s_t =>
          have h := Except.ok.inj hok; subst h
          exact scanTag_corr sc sp hcorr s_t h_tag
      · split at hok
        · -- '|' or '>': scanBlockScalar returns directly, under the item-9c
          -- `!inFlow` guard (peeled: `.error` cannot equal `.ok`)
          exact scanBlockScalar_corr sc sp hcorr (peel_blockScalarGuard hok)
        · split at hok
          · split at hok
            · simp at hok
            · have h := Except.ok.inj hok; subst h
              obtain ⟨sp', hcorr'⟩ := scanDoubleQuoted_corr sc sp hcorr ‹_›
              split
              · exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
              · exact ⟨sp', hcorr'⟩
          · split at hok
            · split at hok
              · simp at hok
              · have h := Except.ok.inj hok; subst h
                obtain ⟨sp', hcorr'⟩ := scanSingleQuoted_corr sc sp hcorr ‹_›
                split
                · exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
                · exact ⟨sp', hcorr'⟩
            · split at hok
              · -- canStartPlainScalar: scanPlainScalar returns directly
                exact scanPlainScalar_corr sc sp hcorr hok
              · simp at hok

/-! ## §3 Preprocess Coupling -/

-- scanNextToken_preprocess preserves ScannerSurfCorr on the .ok (some _) path.
/-- Item 333: the stale-register reset moves no surface datum. -/
lemma closeStaleExplicitKey_corr (s : ScannerState) (sp : SurfPos)
    (h : ScannerSurfCorr s sp) : ScannerSurfCorr (closeStaleExplicitKey s) sp := by
  rcases closeStaleExplicitKey_cases s with h_eq | ⟨_, _, h_eq⟩ <;> rw [h_eq] <;>
    exact ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩

lemma scanNextToken_preprocess_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState) (c : Char)
    (hok : scanNextToken_preprocess sc = .ok (some (s', c))) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    obtain ⟨sp1, hcorr1⟩ := skipToContentLoop_ok_corr sc sp _ s_content hcorr
        (Nat.le_refl _) h_skip
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            obtain ⟨sp2, hcorr2⟩ := unwindIndents_corr s_content sp1 hcorr1 (↑s_content.col)
            have hcorr3 : ScannerSurfCorr
                { (unwindIndents s_content ↑s_content.col) with
                  needIndentCheck := false } sp2 :=
              ⟨hcorr2.chars_from, hcorr2.col_eq, hcorr2.end_eq, hcorr2.input_prefix, hcorr2.indent_cols_nonneg⟩
            exact ⟨sp2, closeStaleExplicitKey_corr _ sp2 (saveSimpleKey_corr _ sp2 hcorr3)⟩
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            exact ⟨sp1, closeStaleExplicitKey_corr _ sp1 (saveSimpleKey_corr _ sp1 hcorr1)⟩

/-- Preserve the actual EOF state and the correspondence used by the original
    proof, instead of discarding both at existential introduction. -/
lemma preprocess_none_reachable_eof (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok none) :
    ∃ (e : ScannerState) (p : SurfPos), skipToContent sc = .ok e ∧
      ScannerSurfCorr e p ∧ ¬ e.hasMore ∧ p.chars = [] := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · cases hok
  · rename_i s_content h_skip
    split at hok
    · rename_i h_hasMore
      obtain ⟨sp_c, hcorr_c⟩ := skipToContentLoop_ok_corr sc sp _ s_content hcorr
        (Nat.le_refl _) h_skip
      have h_not_lt : ¬ s_content.offset < s_content.inputEnd := by
        simp [ScannerState.hasMore] at h_hasMore; omega
      refine ⟨s_content, sp_c, h_skip, hcorr_c, ?_, eof_corr s_content sp_c hcorr_c h_not_lt⟩
      simpa [ScannerState.hasMore] using h_not_lt
    · rename_i h_hasMore
      split at hok
      · split at hok
        · cases hok
        · split at hok
          · rename_i h_indent h_no_trailing h_peek_none
            exfalso; rw [closeStaleExplicitKey_peek, saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none; dsimp only [] at h_peek_none
            unfold unwindIndents at h_peek_none
            simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd,
              unwindIndentsLoop_input] at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt; simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok
      · split at hok
        · cases hok
        · split at hok
          · rename_i h_no_indent h_no_trailing h_peek_none
            exfalso; rw [closeStaleExplicitKey_peek, saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt; simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok

-- Compatibility projection; the meaningful witness is retained above.
lemma scanNextToken_preprocess_none_consumed (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final : SurfPos, sp_final.chars = [] := by
  obtain ⟨_, p, _, _, _, hp⟩ := preprocess_none_reachable_eof sc sp hcorr hok
  exact ⟨p, hp⟩

/-! ## §4 scanNextToken Coupling -/

-- When scanNextToken returns .ok (some s'), ScannerSurfCorr is preserved.
lemma scanNextToken_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken sc = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · split at hok
    · exact absurd (Except.ok.inj hok) nofun
    · rename_i s_pre c_pre h_pre
      obtain ⟨sp_pre, hcorr_pre⟩ := scanNextToken_preprocess_corr sc sp hcorr s_pre c_pre h_pre
      -- §9.2 dangling-node check (item 133)
      split at hok
      · simp at hok
      -- §8.1 flow-value floor (item 172)
      split at hok
      · simp at hok
      split at hok
      · simp at hok
      · split at hok
        · rename_i s_str h_str
          have h := Except.ok.inj hok; injection h with h; subst h
          exact scanNextToken_dispatchStructural_corr s_pre sp_pre c_pre hcorr_pre s_str h_str
        · split at hok
          · simp at hok
          · -- pending-directives check (Fix B)
            split at hok
            · simp at hok
            -- §9.2 bare-document check (item 132)
            split at hok
            · simp at hok
            · have hcorr_ad : ScannerSurfCorr
                  (if s_pre.allowDirectives then
                    { s_pre with allowDirectives := false, documentEverStarted := true }
                  else s_pre) sp_pre := by
                split
                · exact ⟨hcorr_pre.chars_from, hcorr_pre.col_eq, hcorr_pre.end_eq, hcorr_pre.input_prefix, hcorr_pre.indent_cols_nonneg⟩
                · exact hcorr_pre
              split at hok
              · rename_i s_flow h_flow
                have h := Except.ok.inj hok; injection h with h; subst h
                exact scanNextToken_dispatchFlowIndicators_corr _ sp_pre c_pre hcorr_ad s_flow h_flow
              · split at hok
                · simp at hok
                · split at hok
                  · rename_i s_blk h_blk
                    have h := Except.ok.inj hok; injection h with h; subst h
                    exact scanNextToken_dispatchBlockIndicators_corr _ sp_pre c_pre hcorr_ad s_blk h_blk
                  · -- adjacent-value check (item 47)
                    split at hok
                    · simp at hok
                    · split at hok
                      · simp at hok
                      · rename_i s_cnt h_cnt
                        have h := Except.ok.inj hok; injection h with h; subst h
                        exact scanNextToken_dispatchContent_corr _ sp_pre c_pre hcorr_ad s_cnt h_cnt

lemma next_none_reachable_eof (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken sc = .ok none) :
    ∃ (e : ScannerState) (p : SurfPos), skipToContent sc = .ok e ∧
      ScannerSurfCorr e p ∧ ¬ e.hasMore ∧ p.chars = [] := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · split at hok
    · rename_i h_pre
      exact preprocess_none_reachable_eof sc sp hcorr h_pre
    · -- §9.2 dangling-node check (item 133)
      split at hok
      · simp at hok
      -- §8.1 flow-value floor (item 172)
      split at hok
      · simp at hok
      split at hok
      · simp at hok
      · split at hok
        · exact absurd (Except.ok.inj hok) nofun
        · -- pending-directives check (Fix B)
          split at hok
          · simp at hok
          -- §9.2 bare-document check (item 132)
          split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · split at hok
              · exact absurd (Except.ok.inj hok) nofun
              · split at hok
                · simp at hok
                · split at hok
                  · exact absurd (Except.ok.inj hok) nofun
                  · -- adjacent-value check (item 47)
                    split at hok
                    · simp at hok
                    · split at hok
                      · simp at hok
                      · exact absurd (Except.ok.inj hok) nofun

-- Compatibility projection.
lemma scanNextToken_none_consumed (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken sc = .ok none) :
    ∃ sp_final : SurfPos, sp_final.chars = [] := by
  obtain ⟨_, p, _, _, _, hp⟩ := next_none_reachable_eof sc sp hcorr hok
  exact ⟨p, hp⟩

/-! ## §5 scanLoop Full Consumption -/

/-- The exact finite prefix of native successful scanner transitions.
    The count is the number of consumed scanner-loop fuel units. -/
inductive ScanPrefix : Nat → ScannerState → ScannerState → Prop where
  | zero (s : ScannerState) : ScanPrefix 0 s s
  | step {n : Nat} {s t u : ScannerState} :
      scanNextToken s = .ok (some t) → ScanPrefix n t u →
      ScanPrefix (n + 1) s u

/-- A successful run supplies its own reachable terminal cursor, the actual
    EOF preprocessing result, a related empty surface, and the very same
    returned token array, with the exact fuel accounting. -/
lemma loop_reachable_eof (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
    (tokens : Array (Positioned YamlToken))
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanLoop sc fuel = .ok tokens) :
    ∃ (n rest : Nat) (t e : ScannerState) (p : SurfPos),
      fuel = n + (rest + 1) ∧ ScanPrefix n sc t ∧
      scanNextToken t = .ok none ∧ skipToContent t = .ok e ∧
      ScannerSurfCorr e p ∧ ¬ e.hasMore ∧ p.chars = [] ∧
      scanLoop t (rest + 1) = .ok tokens := by
  induction fuel generalizing sc sp tokens with
  | zero => simp [scanLoop] at hok
  | succ fuel' ih =>
    cases hn : scanNextToken sc with
    | error err => simp [scanLoop, hn] at hok
    | ok v =>
      cases v with
      | none =>
        obtain ⟨e, p, hs, hc, he, hp⟩ := next_none_reachable_eof sc sp hcorr hn
        exact ⟨0, fuel', sc, e, p, by omega, .zero _, hn, hs, hc, he, hp, hok⟩
      | some t =>
        obtain ⟨sp', hc⟩ := scanNextToken_corr sc sp hcorr t hn
        have ht : scanLoop t fuel' = .ok tokens := by
          simpa only [scanLoop, hn] using hok
        obtain ⟨n, rest, u, e, p, hfuel, hpath, hnone, hs, hcorr', he, hp, hl⟩ :=
          ih t sp' tokens hc ht
        exact ⟨n + 1, rest, u, e, p, by omega, .step hn hpath, hnone, hs, hcorr', he, hp, hl⟩

-- Compatibility projection.
lemma scanLoop_full_consumption (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
    (tokens : Array (Positioned YamlToken))
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanLoop sc fuel = .ok tokens) :
    ∃ sp_final : SurfPos, sp_final.chars = [] := by
  obtain ⟨_, _, _, _, p, _, _, _, _, _, _, hp, _⟩ :=
    loop_reachable_eof sc sp fuel tokens hcorr hok
  exact ⟨p, hp⟩

/-! ## §6 scan Full Consumption -/

/-- Use the actual production initialization including BOM. -/
def scanInitial (input : String) : ScannerState :=
  let s := (ScannerState.mk' input).emit .streamStart
  match s.peek? with
  | some '\uFEFF' => s.consumeBOM
  | _ => s

/-- Successful production scan reaches a source-correlated EOF via its own native
    steps, with the same returned tokens and exact fuel accounting. -/
@[capstone]
theorem scan_full_consumption (input : String)
    (tokens : Array (Positioned YamlToken)) (h : scan input = .ok tokens) :
    ∃ (n rest : Nat) (t e : ScannerState) (p : SurfPos),
      (input.utf8ByteSize + 1) * 4 = n + (rest + 1) ∧
      ScanPrefix n (scanInitial input) t ∧
      scanNextToken t = .ok none ∧ skipToContent t = .ok e ∧
      ScannerSurfCorr e p ∧ ¬ e.hasMore ∧ p.chars = [] ∧
      scanLoop t (rest + 1) = .ok tokens := by
  have hloop : scanLoop (scanInitial input) ((input.utf8ByteSize + 1) * 4) = .ok tokens := h
  have h_chars := L4YAML.Proofs.ScanStrictCoupling.chars_from_zero_toList input
  have h_init := initial_corr input input.toList h_chars
  have h_emit : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart)
      ⟨input.toList, 0⟩ :=
    ⟨h_init.chars_from, h_init.col_eq, h_init.end_eq, h_init.input_prefix, h_init.indent_cols_nonneg⟩
  have h_bom : ∃ sp, ScannerSurfCorr (scanInitial input) sp := by
    unfold scanInitial
    dsimp only []
    split
    · exact (consumeBOM_corr _ _ h_emit).imp fun _ h => h.1
    · exact ⟨_, h_emit⟩
  obtain ⟨sp, hc⟩ := h_bom
  exact loop_reachable_eof _ sp _ tokens hc hloop

/-! ## §6 Fix-B helpers: `directivesPresent` tracking (grammar-completeness Phase 1)

The pendingDirective↔scanner coupling in `StreamAccum` needs to know how
`directivesPresent` flows through the scan pipeline:
- preprocessing preserves it (`preprocess_some_directivesPresent`);
- `scanDirective` always sets it (`scanDirective_directivesPresent`);
- a successful `scanDocumentEnd` implies it was clear
  (`scanDocumentEnd_ok_directivesPresent`) and clears it in the result;
- `scanDocumentStart` clears it.

Mirrors the `_preserves_flowLevel` family in `ScannerCorrectness`. -/

lemma emit_dp (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).directivesPresent = s.directivesPresent := by
  unfold ScannerState.emit; rfl

lemma consumeNewline_dp (s : ScannerState) :
    (consumeNewline s).directivesPresent = s.directivesPresent := by
  unfold consumeNewline
  split
  · exact advance_dp s
  · dsimp only []
    split
    · exact advance_dp s
    · exact advance_dp s
  · rfl

lemma skipSpaces_dp (s : ScannerState) :
    (skipSpaces s).directivesPresent = s.directivesPresent := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_dp]
    · rfl

lemma skipWhitespace_dp (s : ScannerState) :
    (skipWhitespace s).directivesPresent = s.directivesPresent := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_dp]
      · rfl
    · rfl

lemma collectCommentTextLoop_dp (s : ScannerState) (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_dp]
    · rfl

lemma skipToEndOfLineLoop_dp (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ fuel' IH =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · rw [IH, advance_dp]
    · rfl

lemma skipToEndOfLine_dp (s : ScannerState) :
    (skipToEndOfLine s).directivesPresent = s.directivesPresent := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_dp s _

lemma unwindIndentsLoop_dp (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · rw [ih]; exact emit_dp s .blockEnd
    · rfl

lemma unwindIndents_dp (s : ScannerState) (col : Int) :
    (unwindIndents s col).directivesPresent = s.directivesPresent := by
  unfold unwindIndents
  exact unwindIndentsLoop_dp s col s.indents.size

lemma saveSimpleKey_dp (s : ScannerState) :
    (saveSimpleKey s).directivesPresent = s.directivesPresent := by
  unfold saveSimpleKey
  split <;> (try rfl)
  split <;> rfl

lemma skipToContentWs_dp (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
        · split at h
          · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
          · split at h
            · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
      · simp at h; rw [← h, skipSpaces_dp]
    · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
  · simp at h; rw [← h, skipWhitespace_dp]

lemma skipToContentComment_dp (s : ScannerState) :
    (skipToContentComment s).directivesPresent = s.directivesPresent := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_dp, advance_dp]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_dp, advance_dp]
      · rfl
  · rfl

lemma skipToContentLoop_dp (s : ScannerState) (s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' IH =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · rename_i c hpeek
        split at h
        · split at h
          · have ih := IH _ h
            rw [ih, consumeNewline_dp, skipToContentComment_dp]
            exact skipToContentWs_dp s s1 hws
          · have ih := IH _ h
            rw [ih, consumeNewline_dp, skipToContentComment_dp]
            exact skipToContentWs_dp s s1 hws
        · simp at h; rw [← h, skipToContentComment_dp]
          exact skipToContentWs_dp s s1 hws
      · simp at h; rw [← h, skipToContentComment_dp]
        exact skipToContentWs_dp s s1 hws

lemma skipToContent_dp (s : ScannerState) (s' : ScannerState)
    (h : skipToContent s = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold skipToContent at h
  exact skipToContentLoop_dp s s' _ h

/-- Preprocessing preserves `directivesPresent`. -/
lemma preprocess_some_directivesPresent {sc s_prep : ScannerState} {c : Char}
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.directivesPresent = sc.directivesPresent := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i s1 hskip
    split at h
    · simp at h
    · split at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, _⟩ := h
            rw [← h1, closeStaleExplicitKey_directivesPresent, saveSimpleKey_dp, unwindIndents_dp]
            exact skipToContent_dp sc s1 hskip
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, _⟩ := h
            rw [← h1, closeStaleExplicitKey_directivesPresent, saveSimpleKey_dp]
            exact skipToContent_dp sc s1 hskip

/-- `scanYamlDirective` always sets `directivesPresent`. -/
lemma scanYamlDirective_directivesPresent {s s_ws s' : ScannerState} {sp : YamlPos}
    (h : scanYamlDirective s s_ws sp = .ok s') : s'.directivesPresent = true := by
  unfold scanYamlDirective at h
  simp only [bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; rfl)
    | simp at h

/-- `scanTagDirective` always sets `directivesPresent`. -/
lemma scanTagDirective_directivesPresent {s s_ws s' : ScannerState} {sp : YamlPos}
    (h : scanTagDirective s s_ws sp = .ok s') : s'.directivesPresent = true := by
  unfold scanTagDirective at h
  simp only [bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; rfl)
    | simp at h

/-- `scanDirective` always sets `directivesPresent` (Fix B: including the
    reserved-directive branch). -/
lemma scanDirective_directivesPresent {s s' : ScannerState}
    (h : scanDirective s = .ok s') : s'.directivesPresent = true := by
  unfold scanDirective at h
  split at h
  · simp at h
  · dsimp only [] at h
    split at h
    · -- YAML
      split at h
      · rename_i s_y h_y
        simp only [Except.ok.injEq] at h; subst h
        show (skipToEndOfLine s_y).directivesPresent = true
        rw [skipToEndOfLine_dp]
        exact scanYamlDirective_directivesPresent h_y
      · simp at h
    · split at h
      · -- TAG
        split at h
        · rename_i s_t h_t
          simp only [Except.ok.injEq] at h; subst h
          show (skipToEndOfLine s_t).directivesPresent = true
          rw [skipToEndOfLine_dp]
          exact scanTagDirective_directivesPresent h_t
        · simp at h
      · -- reserved: the record update sets the flag directly
        simp only [Except.ok.injEq] at h; subst h
        rfl

/-- A successful `scanDocumentEnd` implies no directives were pending
    (Fix B: the guard is a bare `directivesPresent` check). -/
lemma scanDocumentEnd_ok_directivesPresent {s s' : ScannerState}
    (h : scanDocumentEnd s = .ok s') : s.directivesPresent = false := by
  cases hdp : s.directivesPresent with
  | false => rfl
  | true =>
    exfalso
    unfold scanDocumentEnd at h
    rw [hdp] at h
    simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- `scanDocumentEnd` clears `directivesPresent` in its result. -/
lemma scanDocumentEnd_result_dp {s s' : ScannerState}
    (h : scanDocumentEnd s = .ok s') : s'.directivesPresent = false := by
  unfold scanDocumentEnd at h
  simp only [bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; rfl)
    | simp at h

/-- `scanDocumentStart` clears `directivesPresent`. -/
lemma scanDocumentStart_dp (s : ScannerState) :
    (scanDocumentStart s).directivesPresent = false := by
  unfold scanDocumentStart; rfl

/-- Snoc a final element onto a `GPlus` chain. -/
lemma GPlus_snoc {P : SurfPos → SurfPos → Prop} {a b c : SurfPos}
    (h : GPlus P a b) (hlast : P b c) : GPlus P a c := by
  cases h with
  | mk m _ hfirst hrest =>
    exact GPlus.mk a m c hfirst
      (GStar_trans hrest (GStar.cons _ _ _ hlast (GStar.nil _)))

end L4YAML.Proofs.ScanStrictCoupling

end Blanket
