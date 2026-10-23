/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Proofs.Scanner.ScannerPlainContent

@[expose] public section Blanket

/-!
# Acceptance — plain scalars, one line (Stream E)

Scanner converses of `scanPlainScalar_prod`: a narrowed `[133] ns-plain-one-line`
derivation at the scanner's position makes `scanPlainScalar` succeed and land at the
end of the derivation's trailing white run, emitting the trimmed `.plain` token.

The unnarrowed converse is false (probes in `Tests/Guards/Proofs/AcceptanceProbes.lean`):
* `a #b` — `[130]`'s `hashAfterNs` only asks `col > 0`, so `#` after a space is a
  plain char; the scanner reads ` #` as a comment and stops at `a` (→ `PlainCharOk.hash`
  only with no pending white).
* `--- x` / `---` — `[126]`'s `dashSafe` derives `---` at column 0; the scanner sees a
  document marker and emits an empty scalar without moving (→ `hdoc`).
* `a  ` — `[133]` ends at `a`; the scanner buffers the trailing whites and lands after
  them (→ the landing is `sp''`, the end of the `GStar SSWhite` run).
-/

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Grammar

/-- One plain content char the scanner keeps: `isPlainSafeBool` (printable, no BOM, in
    flow no indicator); `:` only before another safe char; `#` only with no white before
    it (`[130]` lets `#` follow a space, which the scanner reads as a comment). -/
inductive PlainCharOk (inFlow : Bool) : (afterWhite : Bool) → SurfPos → SurfPos → Prop where
  | safe (aw : Bool) (ch : Char) (rest : List Char) (col : Nat)
      (hSafe : isPlainSafeBool ch inFlow = true) (hNotColon : ch ≠ ':') (hNotHash : ch ≠ '#') :
      PlainCharOk inFlow aw ⟨ch :: rest, col⟩ ⟨rest, col + 1⟩
  | colonSafe (aw : Bool) (next : Char) (rest : List Char) (col : Nat)
      (hSafe : isPlainSafeBool next inFlow = true) :
      PlainCharOk inFlow aw ⟨':' :: next :: rest, col⟩ ⟨next :: rest, col + 1⟩
  | hash (rest : List Char) (col : Nat) (hColGt : col > 0) :
      PlainCharOk inFlow false ⟨'#' :: rest, col⟩ ⟨rest, col + 1⟩

/-- `[132]` entry: a white run then a char; `#` is admitted only when the run is empty. -/
inductive PlainEntryOk (inFlow : Bool) : SurfPos → SurfPos → Prop where
  | noWhite (s s' : SurfPos) : PlainCharOk inFlow false s s' → PlainEntryOk inFlow s s'
  | white (s s₁ s' : SurfPos) : GPlus SSWhite s s₁ → PlainCharOk inFlow true s₁ s' →
      PlainEntryOk inFlow s s'

/-- `[126]` narrowed to the scanner's Boolean predicates (`canStartPlainScalarBool`). -/
inductive PlainFirstOk (inFlow : Bool) : SurfPos → SurfPos → Prop where
  | nonIndicator (ch : Char) (rest : List Char) (col : Nat)
      (hSafe : isPlainSafeBool ch inFlow = true) (hInd : isIndicatorBool ch = false) :
      PlainFirstOk inFlow ⟨ch :: rest, col⟩ ⟨rest, col + 1⟩
  | indicator (ch next : Char) (rest : List Char) (col : Nat)
      (hInd : ch = '-' ∨ ch = '?' ∨ ch = ':') (hSafe : isPlainSafeBool next inFlow = true) :
      PlainFirstOk inFlow ⟨ch :: next :: rest, col⟩ ⟨next :: rest, col + 1⟩

lemma PlainFirstOk.toSNsPlainFirst {inFlow : Bool} {s s' : SurfPos}
    (h : PlainFirstOk inFlow s s') : SNsPlainFirst (ctxOfInFlow inFlow) s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hInd =>
    exact SNsPlainFirst.nonIndicator _ ch rest col (isPlainSafe_to_nsPlainSafe hSafe)
      (fun hi => by rw [← isIndicator_iff] at hi; simp_all)
  | indicator ch next rest col hInd hSafe =>
    rcases hInd with rfl | rfl | rfl
    · exact SNsPlainFirst.dashSafe _ next rest col (isPlainSafe_to_nsPlainSafe hSafe)
    · exact SNsPlainFirst.questionSafe _ next rest col (isPlainSafe_to_nsPlainSafe hSafe)
    · exact SNsPlainFirst.colonSafe _ next rest col (isPlainSafe_to_nsPlainSafe hSafe)

/-- `[133]` narrowed: the scanner's `canStartPlainScalarBool` first char, then entries. -/
inductive PlainOneLineOk (inFlow : Bool) : SurfPos → SurfPos → Prop where
  | mk (s s₁ s' : SurfPos) : PlainFirstOk inFlow s s₁ →
      GStar (PlainEntryOk inFlow) s₁ s' → PlainOneLineOk inFlow s s'

/-- What the scanner must see after the derivation's maximal trailing whites to stop
    there on the same line: EOF, a comment `#` (after at least one white), `:` before a
    blank / EOF / (flow) indicator, a flow indicator in flow, or any plain-unsafe char.
    Line breaks are not stops here: continuation is the multi-line relation's business. -/
def PlainStopOk (inFlow : Bool) (hadWhite : Bool) (chars : List Char) : Prop :=
  match chars with
  | [] => True
  | c :: rest =>
      (c = '#' ∧ hadWhite = true) ∨
      (c = ':' ∧ (match rest.head? with
        | none => True
        | some n => isBlankBool n = true ∨ (inFlow = true ∧ isFlowIndicatorBool n = true))) ∨
      (inFlow = true ∧ isFlowIndicatorBool c = true) ∨
      (isPlainSafeBool c inFlow = false ∧ isWhiteSpaceBool c = false ∧ isLineBreakBool c = false)

lemma PlainCharOk.toSNsPlainChar {inFlow aw : Bool} {s s' : SurfPos}
    (h : PlainCharOk inFlow aw s s') : SNsPlainChar (ctxOfInFlow inFlow) s s' := by
  cases h with
  | safe aw ch rest col hSafe hc hh => exact isPlainSafe_to_plainChar_basic ch rest col inFlow hSafe hc hh
  | colonSafe aw next rest col hSafe =>
    exact SNsPlainChar.colonSafe _ ':' next rest col (isPlainSafe_to_nsPlainSafe hSafe)
  | hash rest col hcol => exact SNsPlainChar.hashAfterNs _ rest col hcol

lemma GPlus.toGStar {P : SurfPos → SurfPos → Prop} {s s' : SurfPos}
    (h : GPlus P s s') : GStar P s s' :=
  match s, s', h with
  | _, _, .mk s₁ s₂ s₃ h₁ hs => GStar.cons s₁ s₂ s₃ h₁ hs

lemma GStar.imp' {P Q : SurfPos → SurfPos → Prop} (f : ∀ a b, P a b → Q a b) :
    ∀ {s s' : SurfPos}, GStar P s s' → GStar Q s s'
  | _, _, .nil s => .nil s
  | _, _, .cons s₁ s₂ s₃ h hs => .cons s₁ s₂ s₃ (f _ _ h) (GStar.imp' f hs)

lemma PlainEntryOk.toEntry {inFlow : Bool} {s s' : SurfPos}
    (h : PlainEntryOk inFlow s s') : SNbNsPlainInLineEntry (ctxOfInFlow inFlow) s s' :=
  match s, s', h with
  | _, _, .noWhite s s' hc => SNbNsPlainInLineEntry.mk _ s s s' (GStar.nil s) hc.toSNsPlainChar
  | _, _, .white s s₁ s' hw hc => SNbNsPlainInLineEntry.mk _ s s₁ s' (GPlus.toGStar hw) hc.toSNsPlainChar

lemma PlainOneLineOk.toSNsPlainOneLine {inFlow : Bool} {s s' : SurfPos}
    (h : PlainOneLineOk inFlow s s') : SNsPlainOneLine (ctxOfInFlow inFlow) s s' :=
  match s, s', h with
  | _, _, .mk s s₁ s' hf hstar =>
    SNsPlainOneLine.mk _ s s₁ s' hf.toSNsPlainFirst (GStar.imp' (fun _ _ he => he.toEntry) hstar)

/-- `collectPlainScalar_terminates?` either falls through or stops where it stands. -/
lemma terminates_none_or_stop (c : Char) (sc : ScannerState) (content spaces : String)
    (inFlow : Bool) :
    collectPlainScalar_terminates? c sc content spaces inFlow = none ∨
    collectPlainScalar_terminates? c sc content spaces inFlow =
      some { content, spaces, state := sc, terminated := true } := by
  unfold collectPlainScalar_terminates?
  repeat' split
  all_goals simp

lemma flowIndicator_not_plain {c : Char} (h : isFlowIndicatorBool c = true) :
    isLineBreakBool c = false ∧ isWhiteSpaceBool c = false ∧ isPlainSafeBool c true = false := by
  simp only [isFlowIndicatorBool, decide_eq_true_eq, List.mem_cons,
    List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- At a `PlainStopOk` position the loop stops where it stands (`terminated := true`). -/
lemma collectPlainScalarLoop_stops (sc : ScannerState) {sp : SurfPos} {hadWhite : Bool}
    (content spaces : String) (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat)
    (hcorr : ScannerSurfCorr sc sp)
    (hstop : PlainStopOk inFlow hadWhite sp.chars)
    (hsp : hadWhite = true → spaces.length > 0) :
    collectPlainScalarLoop sc content spaces (fuel + 1) inFlow contentIndent inputEnd =
      .ok { content, spaces, state := sc, terminated := true } := by
  obtain ⟨chars, col⟩ := sp
  cases chars with
  | nil =>
    have hp := peek_none_of_corr hcorr
    simp [collectPlainScalarLoop, hp]
  | cons c rest =>
    have ⟨hp, _⟩ := peek_of_corr hcorr
    simp only [PlainStopOk] at hstop
    rw [collectPlainScalarLoop]
    simp only [hp]
    rcases hstop with ⟨rfl, hw⟩ | ⟨rfl, hnext⟩ | ⟨hf, hind⟩ | ⟨hunsafe, hnw, hnb⟩
    · have hl := hsp hw
      simp [collectPlainScalar_terminates?, hl]
    · have hadv := advance_corr hcorr (by decide) (by decide)
      have hpk : sc.peekAt? 1 = rest.head? := by
        rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one sc ':' hp]
        cases rest with
        | nil => exact peek_none_of_corr hadv
        | cons n r => exact (peek_of_corr hadv).1
      cases rest with
      | nil => simp [collectPlainScalar_terminates?, hpk]
      | cons n r =>
        simp only [List.head?] at hnext hpk
        rcases hnext with hb | ⟨hfl, hfi⟩
        · simp [collectPlainScalar_terminates?, hpk, hb]
        · subst hfl
          simp [collectPlainScalar_terminates?, hpk, hfi]
    · subst hf
      obtain ⟨hnb, hnw, hns⟩ := flowIndicator_not_plain hind
      rcases terminates_none_or_stop c sc content spaces true with ht | ht <;> simp [ht, hnb, hnw, hns]
    · rcases terminates_none_or_stop c sc content spaces inFlow with ht | ht <;>
        simp [ht, hnb, hnw, hunsafe]

lemma isPlainSafe_facts {c : Char} {inFlow : Bool} (h : isPlainSafeBool c inFlow = true) :
    isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧
    (inFlow && isFlowIndicatorBool c) = false ∧ isPrintableBool c = true ∧ (c == '﻿') = false := by
  unfold isPlainSafeBool at h
  cases inFlow <;> simp_all

/-- One `PlainCharOk` char: the loop takes it as content (with the pending whites) and advances. -/
lemma collectPlainScalarLoop_char_step (sc : ScannerState) {inFlow aw : Bool} {sp sp' : SurfPos}
    (content spaces : String) (contentIndent inputEnd : Nat)
    (hstep : PlainCharOk inFlow aw sp sp') (hcorr : ScannerSurfCorr sc sp) (hcol : sp.col > 0)
    (hsp : aw = false → spaces = "") :
    ∃ c, (∀ fuel, collectPlainScalarLoop sc content spaces (fuel + 1) inFlow contentIndent inputEnd =
        collectPlainScalarLoop sc.advance (content ++ spaces ++ String.singleton c) "" fuel
          inFlow contentIndent inputEnd) ∧
      ScannerSurfCorr sc.advance sp' ∧ Keeps sc sc.advance := by
  have hcol' : sp.col = sc.col := hcorr.col_eq
  cases hstep with
  | safe aw ch rest col hSafe hc hh =>
    obtain ⟨hnw, hnb, hfi, _, _⟩ := isPlainSafe_facts hSafe
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by intro h; subst h; exact absurd hnb (by decide))
      (by intro h; subst h; exact absurd hnb (by decide))
    have hc0 : (sc.col == 0) = false := by
      have h1 : col = sc.col := hcol'
      have h2 : 0 < col := hcol
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    refine ⟨ch, fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, collectPlainScalar_terminates?, hh, hc, hfi, hc0, hnb, hnw, hSafe]
  | colonSafe aw next rest col hSafe =>
    obtain ⟨hnw, hnb, hfi, hpr, hbom⟩ := isPlainSafe_facts hSafe
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpk : sc.peekAt? 1 = some next := by
      rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one sc ':' hp]
      exact (peek_of_corr hadv).1
    have hblank : isBlankBool next = false := by simp [isBlankBool, hnw, hnb]
    have hc0 : (sc.col == 0) = false := by
      have h1 : col = sc.col := hcol'
      have h2 : 0 < col := hcol
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    refine ⟨':', fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    have hs : isPlainSafeBool ':' inFlow = true := by cases inFlow <;> decide
    obtain ⟨hw2, hb2, hf2, hp2, _⟩ := isPlainSafe_facts hs
    simp [hp, collectPlainScalar_terminates?, hpk, hblank, hfi, hpr, hbom, hs, hw2, hb2]
  | hash rest col hcolgt =>
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hc0 : (sc.col == 0) = false := by
      have h1 : col = sc.col := hcol'
      have h2 : 0 < col := hcol
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hsp' := hsp rfl
    subst hsp'
    refine ⟨'#', fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    have hs : isPlainSafeBool '#' inFlow = true := by cases inFlow <;> decide
    obtain ⟨hw2, hb2, hf2, hp2, _⟩ := isPlainSafe_facts hs
    simp [hp, collectPlainScalar_terminates?, hc0, hs, hw2, hb2, hf2]

/-- One white char: the loop buffers it into `spaces` and advances. -/
lemma collectPlainScalarLoop_white_step (sc : ScannerState) {sp sp' : SurfPos}
    (content spaces : String) (inFlow : Bool) (contentIndent inputEnd : Nat)
    (hw : SSWhite sp sp') (hcorr : ScannerSurfCorr sc sp) (hcol : sp.col > 0) :
    ∃ c, (∀ fuel, collectPlainScalarLoop sc content spaces (fuel + 1) inFlow contentIndent inputEnd =
        collectPlainScalarLoop sc.advance content (spaces.push c) fuel inFlow contentIndent inputEnd) ∧
      ScannerSurfCorr sc.advance sp' ∧ Keeps sc sc.advance := by
  have hcol' : sp.col = sc.col := hcorr.col_eq
  cases hw with
  | space rest col =>
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hc0 : (sc.col == 0) = false := by
      have h1 : col = sc.col := hcol'
      have h2 : 0 < col := hcol
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    refine ⟨' ', fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, collectPlainScalar_terminates?, hc0, (by decide : isWhiteSpaceBool ' ' = true),
      (by decide : isLineBreakBool ' ' = false), (by decide : isFlowIndicatorBool ' ' = false)]
  | tab rest col =>
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hc0 : (sc.col == 0) = false := by
      have h1 : col = sc.col := hcol'
      have h2 : 0 < col := hcol
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    refine ⟨'\t', fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, collectPlainScalar_terminates?, hc0, (by decide : isWhiteSpaceBool '\t' = true),
      (by decide : isLineBreakBool '\t' = false), (by decide : isFlowIndicatorBool '\t' = false)]

/-- A white run: the loop buffers every white into `spaces` (`k` steps of fuel). -/
lemma collectPlainScalarLoop_whites {sp sp' : SurfPos} (hw : GStar SSWhite sp sp') :
    ∀ (sc : ScannerState) (content spaces : String) (inFlow : Bool) (contentIndent inputEnd : Nat),
      ScannerSurfCorr sc sp → sp.col > 0 →
      ∃ sc' spaces' k,
        (∀ fuel, collectPlainScalarLoop sc content spaces (fuel + k) inFlow contentIndent inputEnd =
          collectPlainScalarLoop sc' content spaces' fuel inFlow contentIndent inputEnd) ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧
        sp.chars.length = sp'.chars.length + k ∧ spaces'.length = spaces.length + k := by
  induction hw with
  | nil s =>
    intro sc content spaces inFlow ci ie hcorr _
    exact ⟨sc, spaces, 0, fun _ => rfl, hcorr, Keeps.refl sc, rfl, rfl⟩
  | cons s₁ s₂ s₃ h1 _ ih =>
    intro sc content spaces inFlow ci ie hcorr hcol
    obtain ⟨c, heq, hadv, hk⟩ :=
      collectPlainScalarLoop_white_step sc content spaces inFlow ci ie h1 hcorr hcol
    have hcol2 : s₂.col > 0 := by cases h1 <;> exact Nat.succ_pos _
    obtain ⟨sc', spaces', k, heq', hcorr', hk', hl1, hl2⟩ :=
      ih sc.advance content (spaces.push c) inFlow ci ie hadv hcol2
    have hl0 : s₁.chars.length = s₂.chars.length + 1 := by cases h1 <;> rfl
    refine ⟨sc', spaces', k + 1, fun fuel => ?_, hcorr', hk.trans hk', by omega, ?_⟩
    · rw [show fuel + (k + 1) = (fuel + k) + 1 by omega, heq, heq']
    · simp [String.length_push] at hl2; omega

/-- The first char (`PlainFirstOk`): the loop takes it as content; at column 0 the state must
not sit on a document marker (`hdoc`). -/
lemma collectPlainScalarLoop_first_step (sc : ScannerState) {inFlow : Bool} {sp sp' : SurfPos}
    (contentIndent inputEnd : Nat)
    (hf : PlainFirstOk inFlow sp sp') (hcorr : ScannerSurfCorr sc sp)
    (hdoc : sc.col = 0 → atDocumentBoundary sc = false) :
    ∃ c, (∀ fuel, collectPlainScalarLoop sc "" "" (fuel + 1) inFlow contentIndent inputEnd =
        collectPlainScalarLoop sc.advance (String.singleton c) "" fuel inFlow contentIndent inputEnd) ∧
      ScannerSurfCorr sc.advance sp' ∧ Keeps sc sc.advance := by
  cases hf with
  | nonIndicator ch rest col hSafe hInd =>
    obtain ⟨hnw, hnb, hfi, hpr, hbom⟩ := isPlainSafe_facts hSafe
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by intro h; subst h; exact absurd hnb (by decide))
      (by intro h; subst h; exact absurd hnb (by decide))
    have hnd : ¬(ch = '-' ∨ ch = '?' ∨ ch = ':') := by
      rintro (rfl | rfl | rfl) <;> exact absurd hInd (by decide)
    have hstart : canStartPlainScalarBool ch (sc.peekAt? 1) inFlow = true := by
      simp [canStartPlainScalarBool, hnd, hInd, hnw, hnb, hpr, bne, hbom]
    have hterm := canStartPlain_first_not_terminates ch sc inFlow hstart hdoc
    refine ⟨ch, fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, hterm, hnb, hnw, hSafe]
  | indicator ch next rest col hInd hSafe =>
    obtain ⟨hnw, hnb, hfi, hpr, hbom⟩ := isPlainSafe_facts hSafe
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by rcases hInd with rfl | rfl | rfl <;> decide)
      (by rcases hInd with rfl | rfl | rfl <;> decide)
    have hpk : sc.peekAt? 1 = some next := by
      rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one sc ch hp]
      exact (peek_of_corr hadv).1
    have hstart : canStartPlainScalarBool ch (sc.peekAt? 1) inFlow = true := by
      simp [canStartPlainScalarBool, hInd, hpk, hnw, hnb, hfi, hpr, bne, hbom]
    have hterm := canStartPlain_first_not_terminates ch sc inFlow hstart hdoc
    have hs : isPlainSafeBool ch inFlow = true := by
      rcases hInd with rfl | rfl | rfl <;> cases inFlow <;> decide
    obtain ⟨hw2, hb2, _, _, _⟩ := isPlainSafe_facts hs
    refine ⟨ch, fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, hterm, hb2, hw2, hs]

lemma PlainCharOk.len_col {inFlow aw : Bool} {s s' : SurfPos} (h : PlainCharOk inFlow aw s s') :
    s.chars.length = s'.chars.length + 1 ∧ s'.col = s.col + 1 :=
  match s, s', h with
  | _, _, .safe _ _ _ _ _ _ _ => ⟨rfl, rfl⟩
  | _, _, .colonSafe _ _ _ _ _ => ⟨rfl, rfl⟩
  | _, _, .hash _ _ _ => ⟨rfl, rfl⟩

/-- One in-line entry (optional white run, then a content char): content grows, `spaces` resets. -/
lemma collectPlainScalarLoop_entry_step (sc : ScannerState) {inFlow : Bool} {sp sp' : SurfPos}
    (content : String) (contentIndent inputEnd : Nat)
    (he : PlainEntryOk inFlow sp sp') (hcorr : ScannerSurfCorr sc sp) (hcol : sp.col > 0) :
    ∃ sc' content' k,
      (∀ fuel, collectPlainScalarLoop sc content "" (fuel + k) inFlow contentIndent inputEnd =
        collectPlainScalarLoop sc' content' "" fuel inFlow contentIndent inputEnd) ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧ sp.chars.length = sp'.chars.length + k ∧
      sp.col < sp'.col :=
  match sp, sp', he with
  | _, _, .noWhite s s' hc => by
    obtain ⟨c, heq, hadv, hk⟩ :=
      collectPlainScalarLoop_char_step sc content "" contentIndent inputEnd hc hcorr hcol
        (fun _ => rfl)
    obtain ⟨hl, hc'⟩ := hc.len_col
    exact ⟨sc.advance, content ++ "" ++ String.singleton c, 1, heq, hadv, hk, hl, by omega⟩
  | _, _, .white s s₁ s' hw hc => by
    have hws := GPlus.toGStar hw
    obtain ⟨scw, spaces', kw, heqw, hcorrw, hkw, hl1, _⟩ :=
      collectPlainScalarLoop_whites hws sc content "" inFlow contentIndent inputEnd hcorr hcol
    have hcolw : s₁.col > 0 := Nat.lt_of_lt_of_le hcol (GStar_SSWhite_col hws)
    obtain ⟨c, heq, hadv, hk⟩ :=
      collectPlainScalarLoop_char_step scw content spaces' contentIndent inputEnd hc hcorrw hcolw
        (fun h => Bool.noConfusion h)
    obtain ⟨hl, hc'⟩ := hc.len_col
    refine ⟨scw.advance, content ++ spaces' ++ String.singleton c, kw + 1, fun fuel => ?_, hadv,
      hkw.trans hk, by omega, by have := GStar_SSWhite_col hws; omega⟩
    rw [show fuel + (kw + 1) = (fuel + 1) + kw by omega, heqw, heq]

/-- The in-line entries `[133]`: iterate `collectPlainScalarLoop_entry_step`. -/
lemma collectPlainScalarLoop_entries {inFlow : Bool} {sp sp' : SurfPos}
    (hs : GStar (PlainEntryOk inFlow) sp sp') :
    ∀ (sc : ScannerState) (content : String) (contentIndent inputEnd : Nat),
      ScannerSurfCorr sc sp → sp.col > 0 →
      ∃ sc' content' k,
        (∀ fuel, collectPlainScalarLoop sc content "" (fuel + k) inFlow contentIndent inputEnd =
          collectPlainScalarLoop sc' content' "" fuel inFlow contentIndent inputEnd) ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧ sp.chars.length = sp'.chars.length + k ∧
        sp.col ≤ sp'.col := by
  induction hs with
  | nil s =>
    intro sc content ci ie hcorr _
    exact ⟨sc, content, 0, fun _ => rfl, hcorr, Keeps.refl sc, rfl, Nat.le_refl _⟩
  | cons s₁ s₂ s₃ h1 _ ih =>
    intro sc content ci ie hcorr hcol
    obtain ⟨sc₂, content₂, k₁, heq₁, hcorr₂, hk₁, hl₁, hcol₁⟩ :=
      collectPlainScalarLoop_entry_step sc content ci ie h1 hcorr hcol
    obtain ⟨sc', content', k, heq', hcorr', hk', hl, hcl⟩ :=
      ih sc₂ content₂ ci ie hcorr₂ (Nat.lt_trans hcol hcol₁)
    refine ⟨sc', content', k + k₁, fun fuel => ?_, hcorr', hk₁.trans hk', by omega, by omega⟩
    rw [show fuel + (k + k₁) = (fuel + k) + k₁ by omega, heq₁, heq']

lemma PlainFirstOk.len_col {inFlow : Bool} {s s' : SurfPos} (h : PlainFirstOk inFlow s s') :
    s.chars.length = s'.chars.length + 1 ∧ s'.col = s.col + 1 :=
  match s, s', h with
  | _, _, .nonIndicator _ _ _ _ _ => ⟨rfl, rfl⟩
  | _, _, .indicator _ _ _ _ _ _ => ⟨rfl, rfl⟩

/-- One-line plain-scalar converse of `scanPlainScalar_prod`: a `PlainOneLineOk` derivation
`sp → sp'` followed by the trailing white run `sp' → sp''` that the scanner also consumes, and
a `PlainStopOk` stop at `sp''`, is accepted; the scanner lands at `sp''` (not `sp'`: `"a  "`
lands at 3) with the `.plain` token. `hdoc`: at column 0 the scanner refuses a document
marker (`"--- x"` refutes the converse without it). -/
lemma scanPlainScalar_accepts (sc : ScannerState) {sp sp' sp'' : SurfPos} {hadWhite : Bool}
    (hcorr : ScannerSurfCorr sc sp)
    (hder : PlainOneLineOk sc.inFlow sp sp')
    (hwhite : GStar SSWhite sp' sp'')
    (hstop : PlainStopOk sc.inFlow hadWhite sp''.chars)
    (hhw : hadWhite = true → sp''.chars.length < sp'.chars.length)
    (hdoc : sc.col = 0 → atDocumentBoundary sc = false) :
    ∃ s' content, scanPlainScalar sc = .ok s' ∧ ScannerSurfCorr s' sp'' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .plain } := by
  have ⟨s₁, hf, hstar⟩ : ∃ s₁, PlainFirstOk sc.inFlow sp s₁ ∧
      GStar (PlainEntryOk sc.inFlow) s₁ sp' :=
    match sp, sp', hder with
    | _, _, .mk _ s₁ _ hf hstar => ⟨s₁, hf, hstar⟩
  have hfuel := fuel_of_corr hcorr
  obtain ⟨hl₁, hcol₁⟩ := hf.len_col
  obtain ⟨c, heq₁, hc₁, hk₁⟩ :=
    collectPlainScalarLoop_first_step sc (inFlow := sc.inFlow) (sp := sp) (sp' := s₁)
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd hf hcorr hdoc
  obtain ⟨sc₂, content₂, k₂, heq₂, hc₂, hk₂, hl₂, hcl₂⟩ :=
    collectPlainScalarLoop_entries hstar sc.advance (String.singleton c)
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd hc₁
      (by omega)
  obtain ⟨sc₃, spaces₃, k₃, heq₃, hc₃, hk₃, hl₃, hs₃⟩ :=
    collectPlainScalarLoop_whites hwhite sc₂ content₂ "" sc.inFlow
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd hc₂ (by omega)
  have hsp : hadWhite = true → spaces₃.length > 0 := fun h => by
    have := hhw h; simp at hs₃; omega
  have hk := hk₁.trans (hk₂.trans hk₃)
  obtain ⟨f, hF⟩ : ∃ f, (sc.inputEnd - sc.offset + 1) * 2 = (((f + 1) + k₃) + k₂) + 1 :=
    ⟨(sc.inputEnd - sc.offset + 1) * 2 - (k₂ + k₃ + 2), by omega⟩
  have hloop : collectPlainScalarLoop sc "" "" ((sc.inputEnd - sc.offset + 1) * 2)
      sc.inFlow (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd =
      .ok { content := content₂, spaces := spaces₃, state := sc₃, terminated := true } := by
    rw [hF, heq₁, heq₂, heq₃]
    exact collectPlainScalarLoop_stops sc₃ content₂ spaces₃ f sc.inFlow _ sc.inputEnd hc₃ hstop hsp
  refine ⟨{ sc₃.emitAt sc.currentPos (.scalar (trimTrailingWS content₂) .plain) with
      simpleKeyAllowed := false, needIndentCheck := false }, trimTrailingWS content₂, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₃), ?_⟩
  · unfold scanPlainScalar
    simp only [hloop, bind, Except.bind]
  · simp [ScannerState.emitAt, hk.1]

end L4YAML.Proofs.Acceptance

end Blanket
