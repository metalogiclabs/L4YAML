/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.ScalarProduction

@[expose] public section Blanket

/-! # Acceptance (scanner converse) for quoted scalars

    The inverse of `scanDoubleQuoted_prod` / `scanSingleQuoted_prod`, one-line
    case: a surface derivation at the scanner's position makes the scanner
    succeed and land at the derivation's end.

    The surface relations are STRICTLY wider than the scanner, so the converse
    holds only under narrowed character relations (`DQCharOk`, `SQCharOk`) and
    a trailing hypothesis.  Refuting inputs for the unnarrowed converse:
    * `"\x01"` / `'\x01'` — `[107]`/`[118]` admit any non-break char, the
      scanner refuses C0 controls (`invalidControlChar`, `[2] nb-json`).
    * `"\uD800"`, `"\UFFFFFFFF"` — `[60]`/`[61]` constrain digits only, the
      scanner refuses non-scalar values (`unicodeOutOfRange`).
    * `"a"b` in block context — `[109]` ends at the closing quote, the scanner
      refuses the trailing content (`trailingContent`, §7.3).
    * `''''` — `[120]` derives `''` with two quotes left, but the scanner reads
      the pair as `[117] c-quoted-quote`, lands after all four (`'''''` runs to
      `unterminatedScalar`); hence `hq` on the char after the closing quote.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Grammar

/-! ## §1 State bookkeeping the loop preserves -/

/-- Fields the collect loops never touch, read back at the token emission. -/
def Keeps (sc sc' : ScannerState) : Prop :=
  sc'.tokens = sc.tokens ∧ sc'.inputEnd = sc.inputEnd

lemma Keeps.refl (sc : ScannerState) : Keeps sc sc := ⟨rfl, rfl⟩

lemma Keeps.trans {a b c : ScannerState} (h₁ : Keeps a b) (h₂ : Keeps b c) : Keeps a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

lemma keeps_advance (sc : ScannerState) : Keeps sc sc.advance := by
  unfold Keeps ScannerState.advance
  by_cases h : sc.offset < sc.inputEnd
  · simp only [h, ite_true]
    split <;> (try split) <;> exact ⟨rfl, rfl⟩
  · simp only [h, ite_false, and_self]

/-! ## §2 Position facts read off `ScannerSurfCorr` -/

lemma peek_of_corr {sc : ScannerState} {c : Char} {rest : List Char} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩) :
    sc.peek? = some c ∧ sc.offset < sc.inputEnd := by
  have hmore : sc.offset < sc.inputEnd := by
    cases Nat.lt_or_ge sc.offset sc.inputEnd with
    | inl h => exact h
    | inr h =>
      have := eof_corr sc _ hcorr (Nat.not_lt.mpr h)
      simp at this
  obtain ⟨c', rest', hchars, hpeek⟩ := peek_corr sc _ hcorr hmore
  simp only [List.cons.injEq] at hchars
  obtain ⟨rfl, rfl⟩ := hchars
  exact ⟨hpeek, hmore⟩

lemma peek_none_of_corr {sc : ScannerState} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨[], col⟩) : sc.peek? = none := by
  cases h : sc.peek? with
  | none => rfl
  | some c =>
    obtain ⟨rest, hsp⟩ := peek_some_sp hcorr h
    simp at hsp

lemma length_le_listByteSize (l : List Char) : l.length ≤ listByteSize l := by
  induction l with
  | nil => simp [listByteSize]
  | cons c rest ih =>
    simp only [List.length_cons, listByteSize]
    have := Char.utf8Size_pos c
    omega

/-- The scanner's fuel `inputEnd - offset + 1` covers every remaining char. -/
lemma fuel_of_corr {sc : ScannerState} {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp) :
    sp.chars.length < sc.inputEnd - sc.offset + 1 := by
  obtain ⟨pre, hin, hpre⟩ := hcorr.input_prefix
  have hend := hcorr.end_eq
  rw [utf8ByteSize_eq_listByteSize, hin, listByteSize_append] at hend
  have := length_le_listByteSize sp.chars
  omega

/-- `advance_non_newline_corr` with the column read off the correspondence. -/
lemma advance_corr {sc : ScannerState} {c : Char} {rest : List Char} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩)
    (hnl : c ≠ '\n') (hcr : c ≠ '\r') :
    ScannerSurfCorr sc.advance ⟨rest, col + 1⟩ := by
  have hcol := hcorr.col_eq
  simp only at hcol
  subst hcol
  exact advance_non_newline_corr sc c rest hcorr (peek_of_corr hcorr).2 hnl hcr

/-! ## §3 Character facts -/

lemma isNbJson_ne_lf {c : Char} (hJ : isNbJsonProp c) : c ≠ '\n' := by
  intro h; subst h; exact absurd hJ (by decide)

lemma isNbJson_ne_cr {c : Char} (hJ : isNbJsonProp c) : c ≠ '\r' := by
  intro h; subst h; exact absurd hJ (by decide)

lemma isNbJson_not_lineBreak {c : Char} (hJ : isNbJsonProp c) : isLineBreakBool c = false := by
  cases h : isLineBreakBool c
  · rfl
  · exfalso
    rcases (isLineBreak_iff c).1 h with h' | h'
    · exact isNbJson_ne_lf hJ (by simpa [isLineFeedProp] using h')
    · exact isNbJson_ne_cr hJ (by simpa [isCarriageReturnProp] using h')

lemma hex_bool_of_isNsHexDigit {c : Char} (h : isNsHexDigit c) :
    (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true := by
  unfold isNsHexDigit at h
  unfold Char.isDigit
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Or.inl ⟨h1, h2⟩)
  · exact Or.inl (Or.inr ⟨h1, h2⟩)
  · exact Or.inr ⟨h1, h2⟩

lemma isNsHexDigit_ne_lf {c : Char} (h : isNsHexDigit c) : c ≠ '\n' := by
  intro hc; subst hc; unfold isNsHexDigit at h; simp at h

lemma isNsHexDigit_ne_cr {c : Char} (h : isNsHexDigit c) : c ≠ '\r' := by
  intro hc; subst hc; unfold isNsHexDigit at h; simp at h

lemma namedEscape_ne_lf {c : Char} (h : isNamedEscapeChar c) : c ≠ '\n' := by
  intro hc; subst hc; exact h rfl

lemma namedEscape_ne_cr {c : Char} (h : isNamedEscapeChar c) : c ≠ '\r' := by
  intro hc; subst hc; exact h rfl

lemma namedEscape_not_lineBreak {c : Char} (h : isNamedEscapeChar c) : isLineBreakBool c = false := by
  cases hb : isLineBreakBool c
  · rfl
  · exfalso
    rcases (isLineBreak_iff c).1 hb with h' | h'
    · exact namedEscape_ne_lf h (by simpa [isLineFeedProp] using h')
    · exact namedEscape_ne_cr h (by simpa [isCarriageReturnProp] using h')

/-! ## §4 Hex escapes -/

/-- Digit value as `parseHexEscape` computes it. -/
def hexDigitVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if c >= 'a' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Value of a digit run, most significant first (`[59]`–`[61]`). -/
def hexVal (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 16 + hexDigitVal c) 0

lemma collectHexDigitsLoop_accepts (ds : List Char) :
    ∀ (sc : ScannerState) (hex : String) (rest : List Char) (col : Nat),
      (∀ c, c ∈ ds → isNsHexDigit c) →
      ScannerSurfCorr sc ⟨ds ++ rest, col⟩ →
      (collectHexDigitsLoop sc hex ds.length).1.toList = hex.toList ++ ds ∧
      ScannerSurfCorr (collectHexDigitsLoop sc hex ds.length).2 ⟨rest, col + ds.length⟩ ∧
      Keeps sc (collectHexDigitsLoop sc hex ds.length).2 := by
  induction ds with
  | nil =>
    intro sc hex rest col _ hcorr
    simp only [List.length_nil, collectHexDigitsLoop, List.append_nil, Nat.add_zero]
    exact ⟨trivial, hcorr, Keeps.refl sc⟩
  | cons d ds ih =>
    intro sc hex rest col hhex hcorr
    have hd := hhex d (List.mem_cons_self ..)
    have hds : ∀ c, c ∈ ds → isNsHexDigit c := fun c hc => hhex c (List.mem_cons_of_mem d hc)
    simp only [List.cons_append] at hcorr
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (isNsHexDigit_ne_lf hd) (isNsHexDigit_ne_cr hd)
    obtain ⟨h1, h2, h3⟩ := ih sc.advance (hex.push d) rest (col + 1) hds hadv
    simp only [List.length_cons, collectHexDigitsLoop, hpeek, hex_bool_of_isNsHexDigit hd, ite_true]
    refine ⟨?_, ?_, (keeps_advance sc).trans h3⟩
    · rw [h1]; simp
    · have : col + 1 + ds.length = col + (ds.length + 1) := by omega
      rw [← this]; exact h2

lemma parseHexEscape_accepts (ds rest : List Char) (sc : ScannerState) (col n : Nat)
    (hn : ds.length = n)
    (hhex : ∀ c, c ∈ ds → isNsHexDigit c)
    (hval : (hexVal ds).isValidChar)
    (hcorr : ScannerSurfCorr sc ⟨ds ++ rest, col⟩) :
    ∃ s', parseHexEscape sc n = .ok (Char.ofNat (hexVal ds), s') ∧
      ScannerSurfCorr s' ⟨rest, col + n⟩ ∧ Keeps sc s' := by
  subst hn
  obtain ⟨h1, h2, h3⟩ := collectHexDigitsLoop_accepts ds sc "" rest col hhex hcorr
  refine ⟨(collectHexDigitsLoop sc "" ds.length).2, ?_, h2, h3⟩
  unfold parseHexEscape
  have hlen : (collectHexDigitsLoop sc "" ds.length).1.length = ds.length := by
    rw [← String.length_toList, h1]; simp
  have hfold : (collectHexDigitsLoop sc "" ds.length).1.foldl
      (fun acc c => acc * 16 + if c.isDigit then c.toNat - '0'.toNat
        else if c >= 'a' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10) 0
      = hexVal ds := by
    rw [String.foldl_eq_foldl_toList, h1]; rfl
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ite_false, hfold, hval, ite_true]

/-! ## §5 Named escapes -/

lemma processEscape_accepts_named (sc : ScannerState) (ec : Char) (rest : List Char) (col : Nat)
    (hValid : isNamedEscapeChar ec)
    (hcorr : ScannerSurfCorr sc ⟨ec :: rest, col⟩) :
    ∃ ch s', processEscape sc = .ok (ch, s') ∧
      ScannerSurfCorr s' ⟨rest, col + 1⟩ ∧ Keeps sc s' := by
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (namedEscape_ne_lf hValid) (namedEscape_ne_cr hValid)
  unfold isNamedEscapeChar resolveNamedEscape at hValid
  split at hValid <;> first
    | exact absurd rfl hValid
    | exact ⟨_, sc.advance, by unfold processEscape; rw [hpeek]; rfl, hadv, keeps_advance sc⟩

/-! ## §6 Double-quoted one-line content, narrowed to what the scanner accepts -/

/-- `[107] nb-double-char` narrowed by `[2] nb-json` on plain chars and by
    Unicode scalar-value validity on hex escapes (see the module docstring). -/
inductive DQCharOk : SurfPos → SurfPos → Prop where
  | plain (c : Char) (rest : List Char) (col : Nat)
      (hJson : isNbJsonProp c) (hNotBs : c ≠ '\\') (hNotDq : c ≠ '"') :
      DQCharOk ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
  | escape (ec : Char) (rest : List Char) (col : Nat)
      (hValid : isNamedEscapeChar ec) :
      DQCharOk ⟨'\\' :: ec :: rest, col⟩ ⟨rest, col + 2⟩
  | hexEscape2 (rest : List Char) (col : Nat) (h1 h2 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hVal : (hexVal [h1, h2]).isValidChar) :
      DQCharOk ⟨'\\' :: 'x' :: h1 :: h2 :: rest, col⟩ ⟨rest, col + 4⟩
  | hexEscape4 (rest : List Char) (col : Nat) (h1 h2 h3 h4 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hHex3 : isNsHexDigit h3) (hHex4 : isNsHexDigit h4)
      (hVal : (hexVal [h1, h2, h3, h4]).isValidChar) :
      DQCharOk ⟨'\\' :: 'u' :: h1 :: h2 :: h3 :: h4 :: rest, col⟩ ⟨rest, col + 6⟩
  | hexEscape8 (rest : List Char) (col : Nat) (h1 h2 h3 h4 h5 h6 h7 h8 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hHex3 : isNsHexDigit h3) (hHex4 : isNsHexDigit h4)
      (hHex5 : isNsHexDigit h5) (hHex6 : isNsHexDigit h6)
      (hHex7 : isNsHexDigit h7) (hHex8 : isNsHexDigit h8)
      (hVal : (hexVal [h1, h2, h3, h4, h5, h6, h7, h8]).isValidChar) :
      DQCharOk ⟨'\\' :: 'U' :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: h8 :: rest, col⟩
        ⟨rest, col + 10⟩

lemma DQCharOk.toSNbDoubleChar {s s' : SurfPos} (h : DQCharOk s s') : SNbDoubleChar s s' := by
  cases h with
  | plain c rest col hJ hBs hDq =>
    exact .plain c rest col (fun hb => by
      rcases hb with hb | hb
      · exact isNbJson_ne_lf hJ (by simpa [isLineFeedProp] using hb)
      · exact isNbJson_ne_cr hJ (by simpa [isCarriageReturnProp] using hb)) hBs hDq
  | escape ec rest col hV => exact .escape ec rest col hV
  | hexEscape2 rest col h1 h2 x1 x2 _ => exact .hexEscape2 rest col h1 h2 x1 x2
  | hexEscape4 rest col h1 h2 h3 h4 x1 x2 x3 x4 _ => exact .hexEscape4 rest col h1 h2 h3 h4 x1 x2 x3 x4
  | hexEscape8 rest col h1 h2 h3 h4 h5 h6 h7 h8 x1 x2 x3 x4 x5 x6 x7 x8 _ =>
    exact .hexEscape8 rest col h1 h2 h3 h4 h5 h6 h7 h8 x1 x2 x3 x4 x5 x6 x7 x8

lemma DQCharOk.length_lt {s s' : SurfPos} (h : DQCharOk s s') : s'.chars.length < s.chars.length := by
  cases h <;> simp only [List.length_cons] <;> omega

/-- Hex-escape arm of `processEscape` shared by the three widths. -/
lemma processEscape_accepts_hex (sc : ScannerState) (tag : Char) (ds rest : List Char) (col n : Nat)
    (htag : tag = 'x' ∧ n = 2 ∨ tag = 'u' ∧ n = 4 ∨ tag = 'U' ∧ n = 8)
    (hn : ds.length = n)
    (hhex : ∀ c, c ∈ ds → isNsHexDigit c)
    (hval : (hexVal ds).isValidChar)
    (hcorr : ScannerSurfCorr sc ⟨tag :: (ds ++ rest), col⟩) :
    ∃ s', processEscape sc = .ok (Char.ofNat (hexVal ds), s') ∧
      ScannerSurfCorr s' ⟨rest, col + 1 + n⟩ ∧ Keeps sc s' := by
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by rcases htag with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> decide)
    (by rcases htag with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> decide)
  obtain ⟨s', hpar, hc', hk⟩ := parseHexEscape_accepts ds rest sc.advance (col + 1) n hn hhex hval hadv
  refine ⟨s', ?_, hc', (keeps_advance sc).trans hk⟩
  rcases htag with ⟨h, hn'⟩ | ⟨h, hn'⟩ | ⟨h, hn'⟩ <;> subst h <;> subst hn' <;>
    (unfold processEscape; rw [hpeek]; exact hpar)

/-- One `DQCharOk` step is one iteration of `collectDoubleQuotedLoop`. -/
lemma collectDoubleQuotedLoop_step (sc : ScannerState) {sp sp' : SurfPos}
    (hstep : DQCharOk sp sp') (hcorr : ScannerSurfCorr sc sp)
    (content : String) (fuel' : Nat) (startPos : YamlPos) (inFlow : Bool)
    (ind : Int) (iend : Nat) (pl : Nat) :
    ∃ ch sc' pl',
      collectDoubleQuotedLoop sc content (fuel' + 1) startPos inFlow ind iend pl =
        collectDoubleQuotedLoop sc' (content.push ch) fuel' startPos inFlow ind iend pl' ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  cases hstep with
  | plain c rest col hJ hBs hDq =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (isNbJson_ne_lf hJ) (isNbJson_ne_cr hJ)
    refine ⟨c, sc.advance, if c == ' ' || c == '\t' then pl else (content.push c).length, ?_, hadv, keeps_advance sc⟩
    simp only [collectDoubleQuotedLoop, hpeek, isNbJson_not_lineBreak hJ, (isNbJson_iff c).2 hJ,
      Bool.not_true, Bool.false_eq_true, ite_false]
  | escape ec rest col hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    obtain ⟨ch, s', hproc, hc', hk⟩ := processEscape_accepts_named sc.advance ec rest (col + 1) hV hadv
    refine ⟨ch, s', (content.push ch).length, ?_, ?_, (keeps_advance sc).trans hk⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, namedEscape_not_lineBreak hV, hproc,
        Bool.false_eq_true, ite_false, bind, Except.bind]
    · have : col + 1 + 1 = col + 2 := rfl
      rw [← this]; exact hc'
  | hexEscape2 rest col h1 h2 x1 x2 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'x' [h1, h2] rest (col + 1) 2
      (Or.inl ⟨rfl, rfl⟩) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2]), s', (content.push (Char.ofNat (hexVal [h1, h2]))).length, ?_, ?_,
      (keeps_advance sc).trans hk⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'x' = false)]
    · have : col + 1 + 1 + 2 = col + 4 := rfl
      rw [← this]; exact hc'
  | hexEscape4 rest col h1 h2 h3 h4 x1 x2 x3 x4 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2, h3, h4] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'u' [h1, h2, h3, h4] rest (col + 1) 4
      (Or.inr (Or.inl ⟨rfl, rfl⟩)) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2, h3, h4]), s', (content.push (Char.ofNat (hexVal [h1, h2, h3, h4]))).length, ?_, ?_,
      (keeps_advance sc).trans hk⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'u' = false)]
    · have : col + 1 + 1 + 4 = col + 6 := rfl
      rw [← this]; exact hc'
  | hexEscape8 rest col h1 h2 h3 h4 h5 h6 h7 h8 x1 x2 x3 x4 x5 x6 x7 x8 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2, h3, h4, h5, h6, h7, h8] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'U' [h1, h2, h3, h4, h5, h6, h7, h8] rest (col + 1) 8
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2, h3, h4, h5, h6, h7, h8]), s', (content.push (Char.ofNat (hexVal [h1, h2, h3, h4, h5, h6, h7, h8]))).length, ?_, ?_,
      (keeps_advance sc).trans hk⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'U' = false)]
    · have : col + 1 + 1 + 8 = col + 10 := rfl
      rw [← this]; exact hc'

lemma collectDoubleQuotedLoop_accepts {sp sp' : SurfPos} (hder : GStar DQCharOk sp sp') :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend pl : Nat) (rest : List Char),
      ScannerSurfCorr sc sp → sp.chars.length < fuel → sp'.chars = '"' :: rest →
      ∃ content' sc',
        collectDoubleQuotedLoop sc content fuel startPos inFlow ind iend pl = .ok (content', sc') ∧
        ScannerSurfCorr sc' ⟨rest, sp'.col + 1⟩ ∧ Keeps sc sc' := by
  induction hder with
  | nil s =>
    intro sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend
    obtain ⟨chars, col⟩ := s
    simp only at hend hfuel ⊢
    subst hend
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      have hpeek := (peek_of_corr hcorr).1
      refine ⟨content, sc.advance, ?_, advance_corr hcorr (by decide) (by decide), keeps_advance sc⟩
      simp only [collectDoubleQuotedLoop, hpeek]
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      obtain ⟨ch, sc', pl', heq, hcorr', hk⟩ :=
        collectDoubleQuotedLoop_step sc hstep hcorr content fuel' startPos inFlow ind iend pl
      have hlt := hstep.length_lt
      obtain ⟨content', sc'', hok, hc'', hk'⟩ :=
        ih sc' (content.push ch) fuel' startPos inFlow ind iend pl' rest hcorr' (by omega) hend
      exact ⟨content', sc'', heq.trans hok, hc'', hk.trans hk'⟩

/-! ## §7 Trailing content after the closing quote (block context, §7.3) -/

/-- What may follow the closing quote in block context: white, then end, break, `#` or `:`. -/
def TrailingOk (rest : List Char) : Prop :=
  match rest.dropWhile (fun c => c == ' ' || c == '\t') with
  | [] => True
  | c :: _ => isLineBreakProp c ∨ c = '#' ∨ c = ':'

instance (rest : List Char) : Decidable (TrailingOk rest) := by
  unfold TrailingOk; split <;> exact inferInstance

lemma skipTrailingSpaces_corr (rest : List Char) :
    ∀ (sc : ScannerState) (col fuel : Nat),
      ScannerSurfCorr sc ⟨rest, col⟩ → rest.length < fuel →
      ∃ k, ScannerSurfCorr (skipTrailingSpaces sc fuel)
        ⟨rest.dropWhile (fun c => c == ' ' || c == '\t'), col + k⟩ := by
  induction rest with
  | nil =>
    intro sc col fuel hcorr hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      refine ⟨0, ?_⟩
      simp only [skipTrailingSpaces, peek_none_of_corr hcorr, List.dropWhile_nil, Nat.add_zero]
      exact hcorr
  | cons c rest ih =>
    intro sc col fuel hcorr hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      have hpeek := (peek_of_corr hcorr).1
      by_cases hw : (c == ' ' || c == '\t') = true
      · have hc : c = ' ' ∨ c = '\t' := by simpa using hw
        have hadv := advance_corr hcorr (by rcases hc with rfl | rfl <;> decide)
          (by rcases hc with rfl | rfl <;> decide)
        obtain ⟨k, hk⟩ := ih sc.advance (col + 1) fuel' hadv (by simp at hfuel; omega)
        refine ⟨k + 1, ?_⟩
        simp only [skipTrailingSpaces, hpeek, hw, ite_true, List.dropWhile_cons]
        have : col + 1 + k = col + (k + 1) := by omega
        rw [← this]; exact hk
      · refine ⟨0, ?_⟩
        simp only [skipTrailingSpaces, hpeek, hw, Bool.false_eq_true, ite_false, List.dropWhile_cons,
          Nat.add_zero]
        exact hcorr

lemma validateTrailingContent_accepts (sc : ScannerState) (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨rest, col⟩) (hok : TrailingOk rest) :
    validateTrailingContent sc sc.inputEnd = .ok () := by
  have hfuel := fuel_of_corr hcorr
  simp only at hfuel
  obtain ⟨k, hk⟩ := skipTrailingSpaces_corr rest sc col _ hcorr hfuel
  unfold validateTrailingContent
  unfold TrailingOk at hok
  split at hok
  · rename_i hdrop
    rw [hdrop] at hk
    simp only [peek_none_of_corr hk]
    rfl
  · rename_i c tl hdrop
    rw [hdrop] at hk
    have hpeek := (peek_of_corr hk).1
    simp only [hpeek]
    rcases hok with h | h | h
    · simp [(isLineBreak_iff c).2 h]; rfl
    · subst h; simp; rfl
    · subst h; simp; rfl

/-! ## §8 The double-quoted converse -/

/-- `[109] c-double-quoted` with its one-line content narrowed to `DQCharOk`. -/
inductive SCDoubleQuotedOk : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s' : SurfPos) :
      GLit '"' s s₁ → GStar DQCharOk s₁ s₂ → GLit '"' s₂ s' → SCDoubleQuotedOk s s'

lemma GStar_mono {P Q : SurfPos → SurfPos → Prop} (h : ∀ s s', P s s' → Q s s')
    {s s' : SurfPos} (hd : GStar P s s') : GStar Q s s' := by
  induction hd with
  | nil s => exact .nil s
  | cons s₁ s₂ s₃ h₁ _ ih => exact .cons s₁ s₂ s₃ (h _ _ h₁) ih

/-- The narrowed relation is a sub-relation of `[109]` at every `n` and `c`. -/
lemma SCDoubleQuotedOk.toSCDoubleQuoted (n : Nat) (c : L4YAML.YamlContext) {s s' : SurfPos}
    (h : SCDoubleQuotedOk s s') : SCDoubleQuoted n c s s' := by
  rcases h with ⟨a, b, d, h1, hstar, h2⟩
  have hone := GStar_mono (fun _ _ => DQCharOk.toSNbDoubleChar) hstar
  refine .mk n c _ _ _ _ h1 ?_ h2
  cases c <;> first | exact hone | exact .single n _ _ hone

/-- Converse of `scanDoubleQuoted_prod` (one-line): a `SCDoubleQuotedOk` derivation at the
    scanner's position is accepted, landing at its end with the `.doubleQuoted` token.
    `htrail` is the block-context §7.3 trailing check (`"a"b` refutes the converse without it). -/
lemma scanDoubleQuoted_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : SCDoubleQuotedOk sp sp')
    (htrail : sc.inFlow = true ∨ TrailingOk sp'.chars) :
    ∃ s' content, scanDoubleQuoted sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .doubleQuoted } := by
  rcases hder with ⟨a, b, d, h1, hstar, h2⟩
  cases h1 with | mk rest₁ col =>
  cases h2 with | mk rest col₂ =>
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by decide) (by decide)
  have hfuel := fuel_of_corr hadv
  simp only at hfuel
  rw [(keeps_advance sc).2] at hfuel
  obtain ⟨content, sc₂, hloop, hc₂, hk⟩ := collectDoubleQuotedLoop_accepts hstar sc.advance ""
    _ sc.currentPos sc.inFlow sc.currentIndent sc.inputEnd 0 rest hadv hfuel rfl
  simp only at hc₂ htrail
  have hk' := (keeps_advance sc).trans hk
  refine ⟨{ sc₂.emitAt sc.currentPos (.scalar content .doubleQuoted) with
      simpleKeyAllowed := false, needIndentCheck := false }, content, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₂), ?_⟩
  · unfold scanDoubleQuoted
    simp only [hloop, bind, Except.bind]
    rcases htrail with hf | ht
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
    · have hv := validateTrailingContent_accepts sc₂ rest (col₂ + 1) hc₂ ht
      rw [hk'.2] at hv
      cases hf : sc.inFlow
      · simp only [Bool.not_false, ite_true, hv]
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  · simp [ScannerState.emitAt, hk'.1]

/-! ## §9 The single-quoted converse -/

/-- `[118] nb-single-char` narrowed by `[2] nb-json` on plain chars. -/
inductive SQCharOk : SurfPos → SurfPos → Prop where
  | plain (c : Char) (rest : List Char) (col : Nat)
      (hJson : isNbJsonProp c) (hNotSq : c ≠ '\'') :
      SQCharOk ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
  | escapedQuote (rest : List Char) (col : Nat) :
      SQCharOk ⟨'\'' :: '\'' :: rest, col⟩ ⟨rest, col + 2⟩

lemma SQCharOk.toSNbSingleChar {s s' : SurfPos} (h : SQCharOk s s') : SNbSingleChar s s' := by
  cases h with
  | plain c rest col hJ hSq =>
    exact .plain c rest col (fun hb => by
      rcases hb with hb | hb
      · exact isNbJson_ne_lf hJ (by simpa [isLineFeedProp] using hb)
      · exact isNbJson_ne_cr hJ (by simpa [isCarriageReturnProp] using hb)) hSq
  | escapedQuote rest col => exact .escapedQuote rest col

lemma SQCharOk.length_lt {s s' : SurfPos} (h : SQCharOk s s') : s'.chars.length < s.chars.length := by
  cases h <;> simp only [List.length_cons] <;> omega

/-- One `SQCharOk` step is one iteration of `collectSingleQuotedLoop`. -/
lemma collectSingleQuotedLoop_step (sc : ScannerState) {sp sp' : SurfPos}
    (hstep : SQCharOk sp sp') (hcorr : ScannerSurfCorr sc sp)
    (content : String) (fuel' : Nat) (startPos : YamlPos) (inFlow : Bool) (ind : Int) (iend : Nat) :
    ∃ ch sc',
      collectSingleQuotedLoop sc content (fuel' + 1) startPos inFlow ind iend =
        collectSingleQuotedLoop sc' (content.push ch) fuel' startPos inFlow ind iend ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  cases hstep with
  | plain c rest col hJ hSq =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (isNbJson_ne_lf hJ) (isNbJson_ne_cr hJ)
    refine ⟨c, sc.advance, ?_, hadv, keeps_advance sc⟩
    simp only [collectSingleQuotedLoop, hpeek, isNbJson_not_lineBreak hJ, (isNbJson_iff c).2 hJ,
      Bool.not_true, Bool.false_eq_true, ite_false]
  | escapedQuote rest col =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hadv2 := advance_corr hadv (by decide) (by decide)
    refine ⟨'\'', sc.advance.advance, ?_, hadv2, (keeps_advance sc).trans (keeps_advance _)⟩
    simp only [collectSingleQuotedLoop, hpeek, hpeek2]

lemma collectSingleQuotedLoop_accepts {sp sp' : SurfPos} (hder : GStar SQCharOk sp sp') :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend : Nat) (rest : List Char),
      ScannerSurfCorr sc sp → sp.chars.length < fuel → sp'.chars = '\'' :: rest →
      rest.head? ≠ some '\'' →
      ∃ content' sc',
        collectSingleQuotedLoop sc content fuel startPos inFlow ind iend = .ok (content', sc') ∧
        ScannerSurfCorr sc' ⟨rest, sp'.col + 1⟩ ∧ Keeps sc sc' := by
  induction hder with
  | nil s =>
    intro sc content fuel startPos inFlow ind iend rest hcorr hfuel hend hq
    obtain ⟨chars, col⟩ := s
    simp only at hend hfuel ⊢
    subst hend
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      have hpeek := (peek_of_corr hcorr).1
      have hadv := advance_corr hcorr (by decide) (by decide)
      refine ⟨content, sc.advance, ?_, hadv, keeps_advance sc⟩
      cases rest with
      | nil => simp only [collectSingleQuotedLoop, hpeek, peek_none_of_corr hadv]
      | cons c tl =>
        have hpeek2 := (peek_of_corr hadv).1
        have hc : c ≠ '\'' := fun h => hq (by simp [h])
        simp only [collectSingleQuotedLoop, hpeek, hpeek2]
        split
        · rename_i heq; exact absurd (Option.some.inj heq) hc
        · rfl
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel startPos inFlow ind iend rest hcorr hfuel hend hq
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      obtain ⟨ch, sc', heq, hcorr', hk⟩ :=
        collectSingleQuotedLoop_step sc hstep hcorr content fuel' startPos inFlow ind iend
      have hlt := hstep.length_lt
      obtain ⟨content', sc'', hok, hc'', hk'⟩ :=
        ih sc' (content.push ch) fuel' startPos inFlow ind iend rest hcorr' (by omega) hend hq
      exact ⟨content', sc'', heq.trans hok, hc'', hk.trans hk'⟩

/-- `[120] c-single-quoted` with its one-line content narrowed to `SQCharOk`. -/
inductive SCSingleQuotedOk : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s' : SurfPos) :
      GLit '\'' s s₁ → GStar SQCharOk s₁ s₂ → GLit '\'' s₂ s' → SCSingleQuotedOk s s'

/-- The narrowed relation is a sub-relation of `[120]` at every `n` and `c`. -/
lemma SCSingleQuotedOk.toSCSingleQuoted (n : Nat) (c : L4YAML.YamlContext) {s s' : SurfPos}
    (h : SCSingleQuotedOk s s') : SCSingleQuoted n c s s' := by
  rcases h with ⟨a, b, d, h1, hstar, h2⟩
  have hone := GStar_mono (fun _ _ => SQCharOk.toSNbSingleChar) hstar
  refine .mk n c _ _ _ _ h1 ?_ h2
  cases c <;> first | exact hone | exact .single n _ _ hone

/-- Converse of `scanSingleQuoted_prod` (one-line).  `hq`: the char after the closing quote is
    not `'` (else the scanner reads `[117] c-quoted-quote`: `''''` lands after all four quotes);
    `htrail` is the block-context §7.3 trailing check. -/
lemma scanSingleQuoted_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : SCSingleQuotedOk sp sp')
    (hq : sp'.chars.head? ≠ some '\'')
    (htrail : sc.inFlow = true ∨ TrailingOk sp'.chars) :
    ∃ s' content, scanSingleQuoted sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .singleQuoted } := by
  rcases hder with ⟨a, b, d, h1, hstar, h2⟩
  cases h1 with | mk rest₁ col =>
  cases h2 with | mk rest col₂ =>
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by decide) (by decide)
  have hfuel := fuel_of_corr hadv
  simp only at hfuel hq htrail
  rw [(keeps_advance sc).2] at hfuel
  obtain ⟨content, sc₂, hloop, hc₂, hk⟩ := collectSingleQuotedLoop_accepts hstar sc.advance ""
    _ sc.currentPos sc.inFlow sc.currentIndent sc.inputEnd rest hadv hfuel rfl hq
  simp only at hc₂
  have hk' := (keeps_advance sc).trans hk
  refine ⟨{ sc₂.emitAt sc.currentPos (.scalar content .singleQuoted) with
      simpleKeyAllowed := false, needIndentCheck := false }, content, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₂), ?_⟩
  · unfold scanSingleQuoted
    simp only [hloop, bind, Except.bind]
    rcases htrail with hf | ht
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
    · have hv := validateTrailingContent_accepts sc₂ rest (col₂ + 1) hc₂ ht
      rw [hk'.2] at hv
      cases hf : sc.inFlow
      · simp only [Bool.not_false, ite_true, hv]
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  · simp [ScannerState.emitAt, hk'.1]

end L4YAML.Proofs.Acceptance
