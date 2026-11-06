module

public import L4YAML.Proofs.Production.Acceptance.Properties

/-!
# Independent TAG lexical grammar and scanner bridge

Research dependency path: independent directive syntax → scanner acceptance →
`parse_iff_grammar` (the open grammar-completeness capstone). This module changes
no production grammar or runtime. Qualification requires exact-source CI and
axiom inspection; source text alone makes no passing claim.
-/

namespace MathGraph.WholeSource.DirectiveBridge

@[expose] public section

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.StructureProduction

/-- Independent [89]–[92] spelling: named handles have a nonempty word body. -/
inductive TagHandle : List Char → Prop where
  | primary : TagHandle ['!']
  | secondary : TagHandle ['!', '!']
  | named (c : Char) (cs : List Char) (hc : isWordCharProp c)
      (hcs : ∀ d ∈ cs, isWordCharProp d) : TagHandle ('!' :: (c :: cs) ++ ['!'])

/-- Scanner-independent maximal-run boundary. -/
def Stops (p : Char → Prop) (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c → ¬ p c

/-- An instrument used only to share the three collector proofs. -/
def collectRun (test : Char → Bool) (sc : ScannerState) (acc : String) :
    Nat → String × ScannerState
  | 0 => (acc, sc)
  | n + 1 => match sc.peek? with
    | none => (acc, sc)
    | some c => if test c then collectRun test sc.advance (acc.push c) n else (acc, sc)

/-- A maximal independent character run determines the exact returned spelling
and original-input landing, for every scanner state corresponding to its start. -/
lemma collectRun_accepts (p : Char → Prop) (test : Char → Bool)
    (htest : ∀ c, test c = true ↔ p c)
    (hbreak : ∀ c, p c → c ≠ '\n' ∧ c ≠ '\r')
    (cs : List Char) (hcs : ∀ c ∈ cs, p c)
    (rest : List Char) (hstop : Stops p rest) :
    ∀ (sc : ScannerState) (acc : String) (col fuel : Nat),
      ScannerSurfCorr sc ⟨cs ++ rest, col⟩ → cs.length ≤ fuel →
      ∃ out sc', collectRun test sc acc fuel = (out, sc') ∧
        out.toList = acc.toList ++ cs ∧
        ScannerSurfCorr sc' ⟨rest, col + cs.length⟩ ∧ Keeps sc sc' := by
  induction cs with
  | nil =>
    intro sc acc col fuel hcorr _
    refine ⟨acc, sc, ?_, by simp, by simpa using hcorr, Keeps.refl sc⟩
    cases fuel with
    | zero => rfl
    | succ n =>
      cases rest with
      | nil => simp [collectRun, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        have hc : test c = false := by
          cases hb : test c
          · rfl
          · exact False.elim ((hstop c rfl) ((htest c).mp hb))
        simp [collectRun, hpk, hc]
  | cons c cs ih =>
    intro sc acc col fuel hcorr hfuel
    have hc := hcs c (by simp)
    have ht : ∀ d ∈ cs, p d := fun d hd => hcs d (by simp [hd])
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hpk := (peek_of_corr hcorr).1
      have hadv := advance_corr hcorr (hbreak c hc).1 (hbreak c hc).2
      obtain ⟨out, sc', heq, hout, hcorr', hk⟩ :=
        ih ht sc.advance (acc.push c) (col + 1) n hadv (by simp at hfuel; omega)
      refine ⟨out, sc', ?_, ?_, ?_, (keeps_advance sc).trans hk⟩
      · simp [collectRun, hpk, (htest c).mpr hc, heq]
      · simpa [String.toList_push, List.append_assoc] using hout
      · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcorr'

lemma handleLoop_eq_collectRun (sc : ScannerState) (acc : String) (fuel : Nat) :
    collectTagHandleDirectiveLoop sc acc fuel =
      collectRun (fun c => isWordCharBool c || c == '!') sc acc fuel := by
  induction fuel generalizing sc acc with
  | zero => rfl
  | succ n ih =>
    cases hp : sc.peek? with
    | none => simp only [collectTagHandleDirectiveLoop, collectRun, hp]
    | some c =>
      simp only [collectTagHandleDirectiveLoop, collectRun, hp]
      split <;> simp_all only [ih]

lemma handleChar_not_break (c : Char) (h : isWordCharProp c ∨ c = '!') :
    c ≠ '\n' ∧ c ≠ '\r' := by
  rcases h with hw | rfl
  · exact wordChar_not_break hw
  · decide

lemma TagHandle.chars {cs : List Char} (h : TagHandle cs) :
    ∀ c ∈ cs, isWordCharProp c ∨ c = '!' := by
  cases h with
  | primary => simp
  | secondary => simp
  | named c cs hc hcs =>
    intro d hd
    simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hd
    rcases hd with (rfl | rfl | hd) | rfl
    · exact Or.inr rfl
    · exact Or.inl hc
    · exact Or.inl (hcs d hd)
    · exact Or.inr rfl

/-- The runtime validator accepts every independently generated handle. -/
lemma TagHandle.validated {cs : List Char} (h : TagHandle cs) :
    isTagHandleShaped (String.ofList cs) = true := by
  cases h with
  | primary => decide
  | secondary => decide
  | named c cs hc hcs =>
    have hw : (c :: cs).all isWordCharBool = true := by
      simp only [List.all_eq_true]
      intro d hd
      apply (isWordChar_iff d).mpr
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hc
      · exact hcs d hd
    unfold isTagHandleShaped
    apply Bool.or_eq_true.mpr
    right
    simp only [String.toList_ofList, List.cons_append]
    change (decide (((c :: cs) ++ ['!']).length ≥ 2) &&
      (((c :: cs) ++ ['!']).getLast? == some '!') &&
      (((c :: cs) ++ ['!']).dropLast.all isWordCharBool)) = true
    simp [hw]

/-- Stable public collector signature. It covers arbitrary primary, secondary,
and named handles, arbitrary UTF-8 suffixes, scanner context and accumulator. -/
lemma collectTagHandleDirectiveLoop_accepts {cs rest : List Char}
    (h : TagHandle cs) (hstop : Stops (fun c => isWordCharProp c ∨ c = '!') rest)
    (sc : ScannerState) (acc : String) (col fuel : Nat)
    (hcorr : ScannerSurfCorr sc ⟨cs ++ rest, col⟩) (hfuel : cs.length ≤ fuel) :
    ∃ out sc', collectTagHandleDirectiveLoop sc acc fuel = (out, sc') ∧
      out.toList = acc.toList ++ cs ∧
      ScannerSurfCorr sc' ⟨rest, col + cs.length⟩ ∧ Keeps sc sc' := by
  rw [handleLoop_eq_collectRun]
  exact collectRun_accepts _ _ isTagHandleChar_iff_bool handleChar_not_break
    cs h.chars rest hstop sc acc col fuel hcorr hfuel

lemma TagHandle.ends_bang {cs : List Char} (h : TagHandle cs) :
    cs.getLast? = some '!' := by
  cases h <;> simp [List.getLast?_append]

lemma handle_empty_excluded : ¬ TagHandle [] := by
  intro h
  have hh := h.ends_bang
  simp at hh

/-- Every nonempty unclosed word body is excluded, independently of its
length. This is stronger than the concrete `!a` boundary probe below. -/
lemma handle_unclosed_words_excluded (body : List Char) (hne : body ≠ [])
    (hw : ∀ c ∈ body, isWordCharProp c) : ¬ TagHandle ('!' :: body) := by
  intro h
  cases body with
  | nil => exact hne rfl
  | cons c cs =>
    have hh : (c :: cs).getLast? = some '!' := by simpa using h.ends_bang
    exact (by decide : ¬ isWordCharProp '!') (hw '!' (List.mem_of_getLast? hh))

lemma handle_unclosed_excluded : ¬ TagHandle ['!', 'a'] :=
  handle_unclosed_words_excluded ['a'] (by decide) (by
    intro c hc; simp only [List.mem_singleton] at hc; subst c; decide)

-- Constructive reachability of all three grammar arms.
lemma primary_witness : TagHandle ['!'] := .primary
lemma secondary_witness : TagHandle ['!', '!'] := .secondary
lemma named_witness : TagHandle ['!', 'a', '!'] :=
  .named 'a' [] (by decide) (by simp)

/-- Exact source span and maximal lexical boundary, independent of scanner
execution. Both endpoints are positions in the same original source. -/
structure LexRun (p : Char → Prop) (cs : List Char) (s t : SurfPos) : Prop where
  source : s.chars = cs ++ t.chars
  column : t.col = s.col + cs.length
  chars : ∀ c ∈ cs, p c
  stop : Stops p t.chars

lemma surfPos_eta (s : SurfPos) : s = ⟨s.chars, s.col⟩ := by cases s; rfl

lemma LexRun.start_eq {p : Char → Prop} {cs : List Char} {s t : SurfPos}
    (h : LexRun p cs s t) : s = ⟨cs ++ t.chars, s.col⟩ :=
  (surfPos_eta s).trans (by rw [h.source])

lemma LexRun.end_eq {p : Char → Prop} {cs : List Char} {s t : SurfPos}
    (h : LexRun p cs s t) : t = ⟨t.chars, s.col + cs.length⟩ :=
  (surfPos_eta t).trans (by rw [h.column])

lemma prefixLoop_eq_collectRun (sc : ScannerState) (acc : String) (fuel : Nat) :
    collectTagPrefixLoop sc acc fuel = collectRun isUriCharBool sc acc fuel := by
  induction fuel generalizing sc acc with
  | zero => rfl
  | succ n ih =>
    cases hp : sc.peek? with
    | none => simp only [collectTagPrefixLoop, collectRun, hp]
    | some c =>
      simp only [collectTagPrefixLoop, collectRun, hp]
      split <;> simp_all only [ih]

lemma uri_not_break (c : Char) (h : isUriCharProp c) : c ≠ '\n' ∧ c ≠ '\r' := by
  have hb := isUriChar_not_isLineBreak c ((isUriChar_iff c).mpr h)
  exact ⟨by intro he; subst he; exact hb rfl, by intro he; subst he; exact hb rfl⟩

lemma collectTagPrefixLoop_accepts {cs : List Char} {s t : SurfPos}
    (h : LexRun isUriCharProp cs s t) (sc : ScannerState)
    (hcorr : ScannerSurfCorr sc s) (fuel : Nat) (hfuel : s.chars.length ≤ fuel) :
    ∃ out sc', collectTagPrefixLoop sc "" fuel = (out, sc') ∧
      out = String.ofList cs ∧ ScannerSurfCorr sc' t ∧ Keeps sc sc' := by
  have hc : ScannerSurfCorr sc ⟨cs ++ t.chars, s.col⟩ := by
    rw [← h.start_eq]; exact hcorr
  obtain ⟨out, sc', heq, hout, hc', hk⟩ := collectRun_accepts _ _ isUriChar_iff
    uri_not_break cs h.chars t.chars h.stop sc "" s.col fuel hc
      (by have hs := h.source; simp only [hs, List.length_append] at hfuel; omega)
  refine ⟨out, sc', ?_, ?_, ?_, hk⟩
  · simpa only [prefixLoop_eq_collectRun] using heq
  · rw [← String.toList_inj, String.toList_ofList]
    simpa using hout
  · rw [h.end_eq]; exact hc'

lemma whites_span (cs : List Char) (rest : List Char) (col : Nat)
    (h : ∀ c ∈ cs, isWhiteSpaceProp c) :
    GStar SSWhite ⟨cs ++ rest, col⟩ ⟨rest, col + cs.length⟩ := by
  induction cs generalizing col with
  | nil => simpa using GStar.nil (⟨rest, col⟩ : SurfPos)
  | cons c cs ih =>
    have hc : isWhiteSpaceBool c = true := (isWhiteSpace_iff c).mpr (h c (by simp))
    have ht := ih (col + 1) (fun d hd => h d (by simp [hd]))
    have hh := isWhiteSpace_gives_SSWhite c (cs ++ rest) col hc
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      GStar.cons _ _ _ hh ht

lemma whitespace_accepts {cs : List Char} {s t : SurfPos}
    (h : LexRun isWhiteSpaceProp cs s t) (sc : ScannerState)
    (hcorr : ScannerSurfCorr sc s) :
    ScannerSurfCorr (skipWhitespace sc) t ∧ Keeps sc (skipWhitespace sc) := by
  have hs := h.start_eq
  have ht := h.end_eq
  have hw : GStar SSWhite s t := by rw [hs, ht]; exact whites_span cs _ _ h.chars
  apply skipWhitespace_accepts sc hw hcorr
  · intro he; exact h.stop ' ' he (by decide)
  · intro he; exact h.stop '\t' he (by decide)

/-- A TAG body with explicit source spans. Separators and URI pfxChars are
nonempty. This first bridge stops before LF/CR/EOF; comment handling is a
separate extension. No scanner or parser success occurs in this grammar. -/
structure TagBody (handle pfxChars : List Char) (s t : SurfPos) where
  afterHandle : SurfPos
  afterSeparator : SurfPos
  afterPrefix : SurfPos
  separator : List Char
  trailing : List Char
  handleShape : TagHandle handle
  handleRun : LexRun (fun c => isWordCharProp c ∨ c = '!') handle s afterHandle
  separatorRun : LexRun isWhiteSpaceProp separator afterHandle afterSeparator
  separatorNonempty : separator ≠ []
  prefixRun : LexRun isUriCharProp pfxChars afterSeparator afterPrefix
  prefixNonempty : pfxChars ≠ []
  trailingRun : LexRun isWhiteSpaceProp trailing afterPrefix t
  ending : t.chars.head? = none ∨ t.chars.head? = some '\n' ∨ t.chars.head? = some '\r'

lemma ending_peek {sc : ScannerState} {t : SurfPos} (hcorr : ScannerSurfCorr sc t)
    (he : t.chars.head? = none ∨ t.chars.head? = some '\n' ∨ t.chars.head? = some '\r') :
    sc.peek? = none ∨ sc.peek? = some '\n' ∨ sc.peek? = some '\r' := by
  cases t with
  | mk chars col =>
    cases chars with
    | nil => exact Or.inl (peek_none_of_corr hcorr)
    | cons c cs =>
      have hp := (peek_of_corr hcorr).1
      simp only [List.head?_cons, Option.some.injEq, reduceCtorEq, false_or] at he
      rcases he with rfl | rfl
      · exact Or.inr (Or.inl hp)
      · exact Or.inr (Or.inr hp)

/-- General TAG directive-body bridge. The original scanner supplies the fuel
limit and token start; the source-related body scanner supplies the position.
All preexisting tokens are preserved and exactly one tag directive is appended. -/
lemma scanTagDirective_accepts (origin sc : ScannerState) {handle pfxChars : List Char}
    {s t : SurfPos} (h : TagBody handle pfxChars s t)
    (hcorr : ScannerSurfCorr sc s) (hlimit : origin.inputEnd = sc.inputEnd) :
    ∃ out, scanTagDirective origin sc origin.currentPos = .ok out ∧
      ScannerSurfCorr out t ∧
      out.tokens = sc.tokens.push { pos := origin.currentPos,
        val := .tagDirective (String.ofList handle) (String.ofList pfxChars) } ∧
      out.directivesPresent = true := by
  have hc : ScannerSurfCorr sc ⟨handle ++ h.afterHandle.chars, s.col⟩ := by
    rw [← h.handleRun.start_eq]; exact hcorr
  have hfuel := fuel_of_corr hcorr
  obtain ⟨hand, sc₁, hloop, hhand, hc₁, hk₁⟩ := collectTagHandleDirectiveLoop_accepts
    h.handleShape h.handleRun.stop sc "" s.col (origin.inputEnd - sc.offset) hc
      (by rw [hlimit]; have hs := h.handleRun.source; simp only [hs, List.length_append] at hfuel; omega)
  have hhandEq : hand = String.ofList handle := by
    rw [← String.toList_inj, String.toList_ofList]; simpa using hhand
  subst hand
  have ht₁ := h.handleRun.end_eq
  have hc₁' : ScannerSurfCorr sc₁ h.afterHandle := by rw [ht₁]; exact hc₁
  obtain ⟨hc₂, hk₂⟩ := whitespace_accepts h.separatorRun sc₁ hc₁'
  have hi₂ : (skipWhitespace sc₁).inputEnd = origin.inputEnd := by
    rw [hk₂.2.1, hk₁.2.1, hlimit]
  have hf₂ := fuel_of_corr hc₂
  obtain ⟨pfx, sc₃, hpfx, hpfxEq, hc₃, hk₃⟩ := collectTagPrefixLoop_accepts h.prefixRun
    (skipWhitespace sc₁) hc₂ (origin.inputEnd - (skipWhitespace sc₁).offset) (by omega)
  subst pfx
  obtain ⟨hc₄, hk₄⟩ := whitespace_accepts h.trailingRun sc₃ hc₃
  let final := { (skipWhitespace sc₃).emitAt origin.currentPos
      (.tagDirective (String.ofList handle) (String.ofList pfxChars)) with directivesPresent := true }
  have hfinal : ScannerSurfCorr final t := by
    have he := L4YAML.Proofs.ScalarCoupling.corr_of_emitAt origin.currentPos
      (.tagDirective (String.ofList handle) (String.ofList pfxChars)) hc₄
    exact ⟨he.chars_from, he.col_eq, he.end_eq, he.input_prefix, he.indent_cols_nonneg⟩
  refine ⟨final, ?_, hfinal, ?_, rfl⟩
  · unfold scanTagDirective
    simp only [hloop, h.handleShape.validated, Bool.not_true, Bool.false_eq_true, ite_false]
    simp only [hpfx]
    rcases ending_peek hc₄ h.ending with he | he | he <;>
      simp [he, isLineBreakBool, pure, Except.pure, bind, Except.bind, final]
  · simp only [final, ScannerState.emitAt]
    rw [hk₄.1, hk₃.1, hk₂.1, hk₁.1]

lemma nameLoop_eq_collectRun (sc : ScannerState) (acc : String) (fuel : Nat) :
    collectDirectiveNameLoop sc acc fuel = collectRun
      (fun c => !isWhiteSpaceBool c && !isLineBreakBool c && isPrintableBool c && c != '﻿')
      sc acc fuel := by
  induction fuel generalizing sc acc with
  | zero => rfl
  | succ n ih =>
    cases hp : sc.peek? with
    | none => simp only [collectDirectiveNameLoop, collectRun, hp]
    | some c =>
      simp only [collectDirectiveNameLoop, collectRun, hp]
      split <;> simp_all only [ih]

lemma ns_not_break (c : Char) (h : isNsChar c) : c ≠ '\n' ∧ c ≠ '\r' := by
  exact ⟨by intro he; subst he; exact h.1 (by decide),
    by intro he; subst he; exact h.1 (by decide)⟩

lemma collectDirectiveNameLoop_accepts {cs : List Char} {s t : SurfPos}
    (h : LexRun isNsChar cs s t) (sc : ScannerState)
    (hcorr : ScannerSurfCorr sc s) (fuel : Nat) (hfuel : s.chars.length ≤ fuel) :
    ∃ out sc', collectDirectiveNameLoop sc "" fuel = (out, sc') ∧
      out = String.ofList cs ∧ ScannerSurfCorr sc' t ∧ Keeps sc sc' := by
  have hc : ScannerSurfCorr sc ⟨cs ++ t.chars, s.col⟩ := by
    rw [← h.start_eq]; exact hcorr
  obtain ⟨out, sc', heq, hout, hc', hk⟩ := collectRun_accepts _ _
    (fun c => (isNsChar_iff_bool c).symm) ns_not_break cs h.chars t.chars h.stop
    sc "" s.col fuel hc
      (by have hs := h.source; simp only [hs, List.length_append] at hfuel; omega)
  refine ⟨out, sc', ?_, ?_, ?_, hk⟩
  · simpa only [nameLoop_eq_collectRun] using heq
  · rw [← String.toList_inj, String.toList_ofList]; simpa using hout
  · rw [h.end_eq]; exact hc'

/-- A full independent `%TAG` directive through the same original-source
positions as its body. Column-zero is the production dispatch context. -/
structure TagDirective (handle pfxChars : List Char) (s t : SurfPos) where
  afterPercent : SurfPos
  afterName : SurfPos
  bodyStart : SurfPos
  separator : List Char
  columnZero : s.col = 0
  percent : GLit '%' s afterPercent
  name : LexRun isNsChar ['T', 'A', 'G'] afterPercent afterName
  separatorRun : LexRun isWhiteSpaceProp separator afterName bodyStart
  separatorNonempty : separator ≠ []
  body : TagBody handle pfxChars bodyStart t

lemma skipToEndOfLine_of_ending {sc : ScannerState} {t : SurfPos}
    (hcorr : ScannerSurfCorr sc t)
    (he : t.chars.head? = none ∨ t.chars.head? = some '\n' ∨ t.chars.head? = some '\r') :
    skipToEndOfLine sc = sc := by
  have hp := ending_peek hcorr he
  unfold skipToEndOfLine
  cases (sc.inputEnd - sc.offset) with
  | zero => rfl
  | succ n => rcases hp with hp | hp | hp <;> simp [skipToEndOfLineLoop, hp, isLineBreakBool]

/-- Full TAG source/scanner bridge: independent original source syntax and the
scanner's permission flag derive success, the precise token at the `%` source
position, and the next scanner/source correspondence. -/
lemma scanDirective_accepts (sc : ScannerState) {handle pfxChars : List Char}
    {s t : SurfPos} (h : TagDirective handle pfxChars s t)
    (hcorr : ScannerSurfCorr sc s) (hallow : sc.allowDirectives = true) :
    ∃ out, scanDirective sc = .ok out ∧ ScannerSurfCorr out t ∧
      out.tokens = sc.tokens.push { pos := sc.currentPos,
        val := .tagDirective (String.ofList handle) (String.ofList pfxChars) } ∧
      out.directivesPresent = true := by
  have hcadv : ScannerSurfCorr sc.advance h.afterPercent := by
    cases h.percent
    exact advance_corr hcorr (by decide) (by decide)
  have hfuel := fuel_of_corr hcadv
  have hiadv := (keeps_advance sc).2.1
  obtain ⟨name, sc₁, hname, hn, hc₁, hk₁⟩ := collectDirectiveNameLoop_accepts
    h.name sc.advance hcadv (sc.inputEnd - sc.advance.offset) (by omega)
  have hn' : name = "TAG" := by simpa using hn
  subst name
  obtain ⟨hc₂, hk₂⟩ := whitespace_accepts h.separatorRun sc₁ hc₁
  have hlim : sc.inputEnd = (skipWhitespace sc₁).inputEnd := by
    rw [hk₂.2.1, hk₁.2.1, hiadv]
  obtain ⟨out, hok, hco, htok, hdp⟩ := scanTagDirective_accepts sc
    (skipWhitespace sc₁) h.body hc₂ hlim
  refine ⟨out, ?_, hco, ?_, hdp⟩
  · unfold scanDirective
    simp only [hallow, Bool.not_true, Bool.false_eq_true, ite_false, hname]
    simp only [show ("TAG" == "YAML") = false from rfl, Bool.false_eq_true, ite_false,
      show ("TAG" == "TAG") = true from rfl, ite_true, hok]
    rw [skipToEndOfLine_of_ending hco h.body.ending]
  · rw [htok, hk₂.1, hk₁.1, (keeps_advance sc).1]

lemma uri_not_white {c : Char} (hu : isUriCharProp c) : ¬ isWhiteSpaceProp c := by
  intro hw
  simp only [isWhiteSpaceProp, isSpaceProp, isTabProp, beq_iff_eq] at hw
  rcases hw with rfl | rfl <;>
    simp [isUriCharProp, isWordCharProp, isAsciiLetterProp] at hu

/-- Constructive arbitrary-length family, with unrestricted original-source
suffix and starting column. This reaches every handle arm and every nonempty
URI pfxChars, rather than proving only a finite set of literal examples. -/
def tagBody_before_lf (handle pfxChars rest : List Char) (col : Nat)
    (hh : TagHandle handle) (hp : ∀ c ∈ pfxChars, isUriCharProp c) (hne : pfxChars ≠ []) :
    TagBody handle pfxChars
      ⟨handle ++ ' ' :: (pfxChars ++ '\n' :: rest), col⟩
      ⟨'\n' :: rest, col + handle.length + 1 + pfxChars.length⟩ := by
  refine {
    afterHandle := ⟨' ' :: (pfxChars ++ '\n' :: rest), col + handle.length⟩
    afterSeparator := ⟨pfxChars ++ '\n' :: rest, col + handle.length + 1⟩
    afterPrefix := ⟨'\n' :: rest, col + handle.length + 1 + pfxChars.length⟩
    separator := [' ']
    trailing := []
    handleShape := hh
    handleRun := ?_
    separatorRun := ?_
    separatorNonempty := by decide
    prefixRun := ?_
    prefixNonempty := hne
    trailingRun := ?_
    ending := Or.inr (Or.inl rfl) }
  · refine ⟨rfl, rfl, hh.chars, ?_⟩
    intro c hc
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst c
    decide
  · refine ⟨rfl, by simp, ?_, ?_⟩
    · intro c hc; simp only [List.mem_singleton] at hc; subst c; decide
    · cases pfxChars with
      | nil => exact False.elim (hne rfl)
      | cons c cs =>
        intro d hd
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hd
        subst d
        exact uri_not_white (hp c (by simp))
  · refine ⟨rfl, rfl, hp, ?_⟩
    intro c hc
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst c
    decide
  · refine ⟨rfl, by simp, by simp, ?_⟩
    intro c hc
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst c
    decide

/-- The constructive family specializes to arbitrary named word bodies. -/
def namedTagBody_before_lf (c : Char) (cs pfxChars rest : List Char) (col : Nat)
    (hc : isWordCharProp c) (hcs : ∀ d ∈ cs, isWordCharProp d)
    (hp : ∀ d ∈ pfxChars, isUriCharProp d) (hne : pfxChars ≠ []) :
    TagBody ('!' :: (c :: cs) ++ ['!']) pfxChars
      ⟨('!' :: (c :: cs) ++ ['!']) ++ ' ' :: (pfxChars ++ '\n' :: rest), col⟩
      ⟨'\n' :: rest, col + ('!' :: (c :: cs) ++ ['!']).length + 1 + pfxChars.length⟩ :=
  tagBody_before_lf _ pfxChars rest col (.named c cs hc hcs) hp hne

/-- Constructive full original-input witness for every valid handle and
nonempty URI pfxChars. The suffix after LF is unrestricted. -/
def tagDirective_before_lf (handle pfxChars rest : List Char)
    (hh : TagHandle handle) (hp : ∀ c ∈ pfxChars, isUriCharProp c) (hne : pfxChars ≠ []) :
    TagDirective handle pfxChars
      ⟨'%' :: 'T' :: 'A' :: 'G' :: ' ' :: (handle ++ ' ' :: (pfxChars ++ '\n' :: rest)), 0⟩
      ⟨'\n' :: rest, 5 + handle.length + 1 + pfxChars.length⟩ := by
  refine {
    afterPercent := ⟨'T' :: 'A' :: 'G' :: ' ' :: (handle ++ ' ' :: (pfxChars ++ '\n' :: rest)), 1⟩
    afterName := ⟨' ' :: (handle ++ ' ' :: (pfxChars ++ '\n' :: rest)), 4⟩
    bodyStart := ⟨handle ++ ' ' :: (pfxChars ++ '\n' :: rest), 5⟩
    separator := [' ']
    columnZero := rfl
    percent := .mk _ 0
    name := ?_
    separatorRun := ?_
    separatorNonempty := by decide
    body := tagBody_before_lf handle pfxChars rest 5 hh hp hne }
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl <;> decide
    · intro c hc
      simp only [List.head?_cons, Option.some.injEq] at hc
      subst c
      decide
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro c hc; simp only [List.mem_singleton] at hc; subst c; decide
    · intro c hc
      cases hh <;> simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hc
      all_goals subst c; decide

#print axioms collectTagHandleDirectiveLoop_accepts
#print axioms TagHandle.validated
#print axioms scanTagDirective_accepts
#print axioms scanDirective_accepts

end
end MathGraph.WholeSource.DirectiveBridge
