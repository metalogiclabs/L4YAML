/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.ScannerCorrectness
import L4YAML.Proofs.Coupling.CouplingBridge
import L4YAML.Proofs.Scanner.BlockScalarFlowGuard

/-! # No inline flow open ahead — the depth-0 refutation fact (item 10, site 5)

`accum_flow_open_depth0`'s no-break arm (`col ≠ 0`, only `s-white` crossed)
must REFUTE the closeable pendings whose construct is already complete: after
a quoted scalar, an alias, a flow close back to block, or a `...`, a `[`/`{`
on the same line is exactly what the scanner's trailing-content family
rejects — `validateTrailingContent` ([109]/[120] via §7.5),
`validateAliasClose` (item 9h), `validateFlowClose` ([137]/[140]),
`scanDocumentEnd`'s suffix check ([204]) — and a plain scalar in block
context ABSORBS a same-line `[` (`ns-plain-safe-out` [128] admits it), while
a block scalar ends at column 0 or end of input.

This file packages that one dispatch's worth of lookahead as a fact about
the REST OF THE LINE, carried by the pending state to the flow-open step:

* **`LineStop P`** — the surface reading, INDEXED by its stop set: optional
  `s-white`, then either end of input or a non-white head in `P`.  Item 10
  wrote one set into the predicate (`NoOpenHead`) and projected every producer
  onto it; items 36/37 name the rungs the producers actually decide —
  `TailSuffix` (`[204]`'s `s-l-comments`), `NodeTail` (§7.5: `s-l-comments`
  plus `[154]`/`[155]`'s `:`), `OffLine` (outside `[1] c-printable`, or the
  BOM), and their union `NodeStop` — with `LineStop.mono` at the CONSUMER.
  `LineNoOpen` is `LineStop NoOpenHead`, and every old consumer is unchanged.
* **`RestNoOpen`** — the scanner-side reading, quantified over
  `CharsFromOffset` so producers never touch `SurfPos`.
* **Producers** — one per family, each reading the guard that ran when the
  pending was built.
* **Consumers** — transport under the preprocessing whites
  (`LineNoOpen.strip`), and the head refutation against a dispatched
  `[`/`{` (`LineNoOpen.not_open_head`).
-/

set_option maxHeartbeats 1000000

namespace L4YAML.Proofs.LineOpenGuard

open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.CouplingBridge
open L4YAML.CharPredicates
open L4YAML.Proofs.ScannerProgress
open L4YAML.Proofs.ScannerCorrectness.ScanHelpers
open L4YAML.Proofs.BlockScalarFlowGuard

/-! ## §1 The predicate and its surface consumers

The predicate is indexed by its STOP SET — the characters the producer's own
validator admitted.  Item 10 wrote one stop set INTO the predicate (`¬(c = '['
∨ c = '{')`) and projected all four validators onto it inside the producers
(`stop_of_allowlist`), because the consumer of the day asked only about a flow
open.  The strength discarded there is exactly what a later consumer needs:
`[204] l-document-suffix`'s tail is `[79] s-l-comments` and admits a break or
a `#` and nothing else, which refutes a same-line `-`/`?`/`:` as flatly as it
refutes a `[`.  So the set rides the predicate and the projection happens at
the CONSUMER (`LineStop.mono`), which costs the old consumers one `mono` and
buys the new ones the difference. -/

/-- The rest of the current line stops in `P`: optional `s-white` [33], then
    end of input or a head that is not white and satisfies `P`. -/
inductive LineStop (P : Char → Prop) : List Char → Prop where
  | nil : LineStop P []
  | stop {c : Char} (rest : List Char)
      (hnw : ¬(c = ' ' ∨ c = '\t'))
      (hst : P c) : LineStop P (c :: rest)
  | white {c : Char} {rest : List Char}
      (hw : c = ' ' ∨ c = '\t')
      (t : LineStop P rest) : LineStop P (c :: rest)

/-- **The projection, moved to the consumer.**  A stop set weakens freely;
    this single step is what every producer used to take on its own behalf. -/
lemma LineStop.mono {P Q : Char → Prop} (hPQ : ∀ c, P c → Q c) :
    ∀ {l : List Char}, LineStop P l → LineStop Q l := by
  intro l h
  induction h with
  | nil => exact .nil
  | stop rest hnw hst => exact .stop rest hnw (hPQ _ hst)
  | white hw _ ih => exact .white hw ih

/-- The head of a stopped line satisfies the stop set, once it is known not
    to be one of the leading whites. -/
lemma LineStop.head_stop {P : Char → Prop} {c : Char} {rest : List Char}
    (h : LineStop P (c :: rest)) (hnw : ¬(c = ' ' ∨ c = '\t')) : P c := by
  cases h with
  | stop _ _ hst => exact hst
  | white hw _ => exact absurd hw hnw

/-- One `s-white` step strips one white char and preserves the fact. -/
lemma LineStop.strip_one {P : Char → Prop} {sp sp' : SurfPos}
    (hw : SSWhite sp sp') (h : LineStop P sp.chars) : LineStop P sp'.chars := by
  cases hw with
  | space rest col =>
    cases h with
    | stop _ hnw _ => exact absurd (Or.inl rfl) hnw
    | white _ t => exact t
  | tab rest col =>
    cases h with
    | stop _ hnw _ => exact absurd (Or.inr rfl) hnw
    | white _ t => exact t

/-- Preprocessing's no-break residue is `s-white*`; the fact survives it. -/
lemma LineStop.strip {P : Char → Prop} {sp sp' : SurfPos}
    (hws : GStar SSWhite sp sp') (h : LineStop P sp.chars) :
    LineStop P sp'.chars := by
  induction hws with
  | nil => exact h
  | cons _ _ _ hstep _ ih => exact ih (h.strip_one hstep)

/-- **The consumer's own read**: the character a no-break step dispatches is
    in the stop set the producing validator admitted.  `hhead` is that
    character read back through the correspondence. -/
lemma LineStop.across_whites {P : Char → Prop} {sp sp' : SurfPos} {c : Char}
    (h : LineStop P sp.chars) (hws : GStar SSWhite sp sp')
    (hhead : sp'.chars.head? = some c) (hnw : ¬(c = ' ' ∨ c = '\t')) : P c := by
  have h' := h.strip hws
  cases hchars : sp'.chars with
  | nil => rw [hchars] at hhead; cases hhead
  | cons c' rest =>
    rw [hchars] at hhead h'
    injection hhead with hce
    subst hce
    exact h'.head_stop hnw

/-! ### §1a The stop sets

Three rungs, weakest last, each named for the production that decides it. -/

/-- `[204] l-document-suffix ::= c-document-end s-l-comments` — the tail of a
    `...`, which admits a break, a `#`, or end of input and NOTHING else: a
    document-end marker is not a node and cannot be a key. -/
def TailSuffix (c : Char) : Prop := isLineBreakBool c = true ∨ c = '#'

/-- Item 10's set: the rest of the line cannot dispatch a flow open.  (A
    break, `#`, `:`, `-`, a non-printable — anything a completed construct's
    trailing validation admits — satisfies it.) -/
def NoOpenHead (c : Char) : Prop := ¬(c = '[' ∨ c = '{')

lemma TailSuffix.toNoOpenHead {c : Char} (h : TailSuffix c) : NoOpenHead c := by
  simp only [TailSuffix, isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
    Bool.or_eq_true, beq_iff_eq] at h
  rintro (rfl | rfl) <;> simp_all

/-- §7.5's own allowlist — the tail of a COMPLETE block-context NODE:
    `[79] s-l-comments`, plus the `:` that `[154] ns-s-implicit-yaml-key` and
    `[155] c-s-implicit-json-key` put after a node on its own line.  This is
    what `validateTrailingContent`, `validateAliasClose` and
    `validateFlowClose` decide, character for character — one rung weaker than
    `[204]`'s, because a node CAN be a key and a `...` cannot. -/
def NodeTail (c : Char) : Prop := TailSuffix c ∨ c = ':'

/-- Outside `[1] c-printable`, or the byte order mark (`[3] c-byte-order-mark`
    is printable, but no production admits it mid-line): where the two scalar
    WALKS stop with no validator consulted at all.  A plain scalar absorbs
    every `ns-plain-safe-out` character it meets, so what it stops at is either
    `NodeTail` or this; a block scalar's line collection is the same walk. -/
def OffLine (c : Char) : Prop := isPrintableBool c = false ∨ c = '﻿'

/-- What a complete block-context node's line may stop at: the two families
    above, and nothing else.  A UNION, not a projection — the `NodeTail`
    producers keep their own sharper conclusion and weaken here (item 37). -/
def NodeStop (c : Char) : Prop := NodeTail c ∨ OffLine c

lemma TailSuffix.toNodeTail {c : Char} (h : TailSuffix c) : NodeTail c := Or.inl h

lemma NodeTail.toNodeStop {c : Char} (h : NodeTail c) : NodeStop c := Or.inl h

lemma OffLine.toNodeStop {c : Char} (h : OffLine c) : NodeStop c := Or.inr h

lemma NodeStop.toNoOpenHead {c : Char} (h : NodeStop c) : NoOpenHead c := by
  rcases h with (hts | rfl) | (hnp | rfl)
  · exact hts.toNoOpenHead
  · rintro (h | h) <;> exact absurd h (by decide)
  · rintro (rfl | rfl) <;> exact absurd hnp (by decide)
  · rintro (h | h) <;> exact absurd h (by decide)

/-- **What §7.5 refuses.**  A `-` and a `?` are printable, are not the BOM, are
    not breaks, and are neither `#` nor `:` — so no rung of the ladder admits
    them.  This is the whole content of item 37 at the character level. -/
lemma NodeStop.not_dash_or_question {c : Char} (h : NodeStop c)
    (hc : c = '-' ∨ c = '?') : False := by
  have hne : c ≠ '-' ∧ c ≠ '?' := by
    rcases h with ((hbr | hh) | hcol) | (hnp | hbom)
    · exact ⟨by rintro rfl; exact absurd hbr (by decide),
             by rintro rfl; exact absurd hbr (by decide)⟩
    · subst hh; exact ⟨by decide, by decide⟩
    · subst hcol; exact ⟨by decide, by decide⟩
    · exact ⟨by rintro rfl; exact absurd hnp (by decide),
             by rintro rfl; exact absurd hnp (by decide)⟩
    · subst hbom; exact ⟨by decide, by decide⟩
  rcases hc with rfl | rfl
  · exact hne.1 rfl
  · exact hne.2 rfl

/-- Item 10's predicate, as the specialization it now is. -/
abbrev LineNoOpen : List Char → Prop := LineStop NoOpenHead

/-- The tail of a `...`: `s-l-comments` and nothing else. -/
abbrev LineTailSuffix : List Char → Prop := LineStop TailSuffix

/-- §7.5's node tail: `s-l-comments` plus `[154]`/`[155]`'s `:`. -/
abbrev LineNodeTail : List Char → Prop := LineStop NodeTail

/-- The union a completed block-context node's park carries. -/
abbrev LineNodeStop : List Char → Prop := LineStop NodeStop

lemma LineTailSuffix.toLineNoOpen {l : List Char}
    (h : LineTailSuffix l) : LineNoOpen l :=
  h.mono (fun _ => TailSuffix.toNoOpenHead)

lemma LineNodeTail.toLineNodeStop {l : List Char}
    (h : LineNodeTail l) : LineNodeStop l :=
  h.mono (fun _ => NodeTail.toNodeStop)

lemma LineNodeStop.toLineNoOpen {l : List Char}
    (h : LineNodeStop l) : LineNoOpen l :=
  h.mono (fun _ => NodeStop.toNoOpenHead)

/-- The head of a `LineNoOpen` line is never a flow open. -/
lemma LineNoOpen.not_open_head {c : Char} {rest : List Char}
    (h : LineNoOpen (c :: rest)) (hc : c = '[' ∨ c = '{') : False := by
  cases h with
  | stop _ _ hno => exact hno hc
  | white hw _ => cases hc <;> cases hw <;> simp_all

/-- The refutation: a `LineNoOpen` position cannot reach a `[`/`{` across
    whites alone.  `hhead` is the dispatched char read back through the
    correspondence. -/
lemma LineNoOpen.no_open_across_whites {sp sp' : SurfPos} {c : Char}
    (h : LineNoOpen sp.chars) (hws : GStar SSWhite sp sp')
    (hhead : sp'.chars.head? = some c) (hc : c = '[' ∨ c = '{') : False :=
  h.across_whites hws hhead (by rintro (rfl | rfl) <;> cases hc <;> simp_all) hc

/-- **The `...` refutation** (item 36): after a document-end marker, a
    same-line step that crossed only `s-white` reaches a break or a `#`.  Any
    other dispatched character — every block indicator, every content head —
    contradicts `[204]`'s own suffix check. -/
lemma LineTailSuffix.no_content_across_whites {sp sp' : SurfPos} {c : Char}
    (h : LineTailSuffix sp.chars) (hws : GStar SSWhite sp sp')
    (hhead : sp'.chars.head? = some c)
    (hnw : ¬(c = ' ' ∨ c = '\t'))
    (hnb : isLineBreakBool c = false) (hnc : c ≠ '#') : False := by
  rcases h.across_whites hws hhead hnw with hbr | hhash
  · rw [hnb] at hbr; cases hbr
  · exact hnc hhash

/-- **The §7.5 refutation** (item 37): after a complete block-context node, a
    same-line step that crossed only `s-white` cannot dispatch a `-` or a `?`.
    The `:` is NOT refuted and must not be: it is `[154]`'s implicit key, the
    one same-line continuation the productions admit. -/
lemma LineNodeStop.no_indicator_across_whites {sp sp' : SurfPos} {c : Char}
    (h : LineNodeStop sp.chars) (hws : GStar SSWhite sp sp')
    (hhead : sp'.chars.head? = some c) (hc : c = '-' ∨ c = '?') : False :=
  NodeStop.not_dash_or_question
    (h.across_whites hws hhead
      (by rcases hc with rfl | rfl <;> rintro (h | h) <;> exact absurd h (by decide)))
    hc

/-! ## §2 The scanner-side reading and its bridges -/

/-- Scanner-side `LineStop`, quantified over the character suffix so
    producers reason with `peek?`/`advance` only. -/
def RestStop (P : Char → Prop) (s : ScannerState) : Prop :=
  ∀ l, CharsFromOffset s.input s.offset l → LineStop P l

abbrev RestNoOpen (s : ScannerState) : Prop := RestStop NoOpenHead s
abbrev RestTailSuffix (s : ScannerState) : Prop := RestStop TailSuffix s
abbrev RestNodeTail (s : ScannerState) : Prop := RestStop NodeTail s
abbrev RestNodeStop (s : ScannerState) : Prop := RestStop NodeStop s

/-- The projection, scanner side. -/
lemma RestStop.mono {P Q : Char → Prop} (hPQ : ∀ c, P c → Q c) {s : ScannerState}
    (h : RestStop P s) : RestStop Q s := fun l hl => (h l hl).mono hPQ

/-- Read the fact through the correspondence. -/
lemma RestStop.to_surface {P : Char → Prop} {s : ScannerState} {sp : SurfPos}
    (h : RestStop P s) (hcorr : ScannerSurfCorr s sp) : LineStop P sp.chars :=
  h _ hcorr.chars_from

/-- The two-disjunct form the pending state carries, read through the
    correspondence. -/
lemma col0_or_lineStop {P : Char → Prop} {s' : ScannerState} {sp : SurfPos}
    (h : s'.col = 0 ∨ RestStop P s') (hcorr : ScannerSurfCorr s' sp) :
    sp.col = 0 ∨ LineStop P sp.chars :=
  h.imp (fun h0 => hcorr.col_eq.trans h0) (fun hr => hr.to_surface hcorr)

lemma col0_or_lineNoOpen {s' : ScannerState} {sp : SurfPos}
    (h : s'.col = 0 ∨ RestNoOpen s') (hcorr : ScannerSurfCorr s' sp) :
    sp.col = 0 ∨ LineNoOpen sp.chars := col0_or_lineStop h hcorr

/-- Token emission and record updates leave the cursor alone. -/
lemma RestStop.congr {P : Char → Prop} {s s' : ScannerState}
    (hi : s'.input = s.input) (ho : s'.offset = s.offset)
    (h : RestStop P s) : RestStop P s' := by
  intro l hl
  rw [hi, ho] at hl
  exact h l hl

/-- A state whose `peek?` is `none` or a non-white head in `P` is
    `RestStop P` with an empty white prefix. -/
lemma restStop_of_peek_stop {P : Char → Prop} {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (h : ∀ c, s.peek? = some c → ¬(c = ' ' ∨ c = '\t') ∧ P c) :
    RestStop P s := by
  intro l hl
  cases hl with
  | at_end _ _ => exact .nil
  | cons p hlt c rest hc hrest =>
    have hpk : s.peek? = some c := by
      unfold ScannerState.peek?
      rw [if_pos (by omega : s.offset < s.inputEnd)]
      exact congrArg some hc
    obtain ⟨h1, h2⟩ := h c hpk
    exact .stop _ h1 h2

lemma restNoOpen_of_peek_stop {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (h : ∀ c, s.peek? = some c → ¬(c = ' ' ∨ c = '\t') ∧ ¬(c = '[' ∨ c = '{')) :
    RestNoOpen s := restStop_of_peek_stop hend h

/-- A state at column 0 or end of input (the block-scalar endings). -/
lemma restStop_of_at_end {P : Char → Prop} {s : ScannerState}
    (h : s.offset ≥ s.inputEnd) (hend : s.inputEnd = s.input.utf8ByteSize) :
    RestStop P s := by
  intro l hl
  cases hl with
  | at_end _ _ => exact .nil
  | cons p hlt _ _ _ _ => omega

lemma restNoOpen_of_at_end {s : ScannerState}
    (h : s.offset ≥ s.inputEnd) (hend : s.inputEnd = s.input.utf8ByteSize) :
    RestNoOpen s := restStop_of_at_end h hend

/-- A peeked char is the surface head. -/
lemma head_of_peek {s : ScannerState} {sp : SurfPos} {c : Char}
    (hcorr : ScannerSurfCorr s sp) (hpk : s.peek? = some c) :
    sp.chars.head? = some c := by
  have hlt : s.offset < s.inputEnd := by
    unfold ScannerState.peek? at hpk
    by_cases h : s.offset < s.inputEnd
    · exact h
    · rw [if_neg h] at hpk; cases hpk
  have hget : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
    unfold ScannerState.peek? at hpk
    rw [if_pos hlt] at hpk
    exact Option.some.inj hpk
  have hcf := hcorr.chars_from
  have hend := hcorr.end_eq
  generalize hch : sp.chars = l at hcf ⊢
  cases hcf with
  | at_end _ h => rw [hend] at hlt; omega
  | cons p h c' rest hc hrest =>
    exact congrArg some (hc.symm.trans hget)

/-! ## §3 The shared white-skip core

`skipTrailingSpaces` (and its clone `skipDocEndWhitespace`) advance through
`s-white` only; if the landing `peek?` is acceptable, the whole window is
`RestNoOpen`.  Fuel adequacy: each step consumes at least one byte. -/

/-- `peek? = some c` exposes the `CharsFromOffset` head. -/
private lemma peek_some_head {s : ScannerState} {c : Char}
    (_hend : s.inputEnd = s.input.utf8ByteSize)
    (hpk : s.peek? = some c) :
    s.offset < s.inputEnd ∧ String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
  unfold ScannerState.peek? at hpk
  by_cases hlt : s.offset < s.inputEnd
  · rw [if_pos hlt] at hpk
    exact ⟨hlt, Option.some.inj hpk⟩
  · rw [if_neg hlt] at hpk
    cases hpk

private lemma skipTrailingSpaces_step_white {s : ScannerState} {c : Char} {fuel' : Nat}
    (hpk : s.peek? = some c) (hw : (c == ' ' || c == '\t') = true) :
    skipTrailingSpaces s (fuel' + 1) = skipTrailingSpaces s.advance fuel' := by
  have hstep : skipTrailingSpaces s (fuel' + 1) =
      (match s.peek? with
        | some c => if c == ' ' || c == '\t' then skipTrailingSpaces s.advance fuel' else s
        | none => s) := rfl
  rw [hstep, hpk]
  exact if_pos hw

private lemma skipTrailingSpaces_step_stop {s : ScannerState} {c : Char} {fuel' : Nat}
    (hpk : s.peek? = some c) (hw : ¬(c == ' ' || c == '\t') = true) :
    skipTrailingSpaces s (fuel' + 1) = s := by
  have hstep : skipTrailingSpaces s (fuel' + 1) =
      (match s.peek? with
        | some c => if c == ' ' || c == '\t' then skipTrailingSpaces s.advance fuel' else s
        | none => s) := rfl
  rw [hstep, hpk]
  exact if_neg hw

private lemma skipDocEndWhitespace_step_white {s : ScannerState} {c : Char} {fuel' : Nat}
    (hpk : s.peek? = some c) (hw : (c == ' ' || c == '\t') = true) :
    skipDocEndWhitespace s (fuel' + 1) = skipDocEndWhitespace s.advance fuel' := by
  have hstep : skipDocEndWhitespace s (fuel' + 1) =
      (match s.peek? with
        | some c => if c == ' ' || c == '\t' then skipDocEndWhitespace s.advance fuel' else s
        | none => s) := rfl
  rw [hstep, hpk]
  exact if_pos hw

private lemma skipDocEndWhitespace_step_stop {s : ScannerState} {c : Char} {fuel' : Nat}
    (hpk : s.peek? = some c) (hw : ¬(c == ' ' || c == '\t') = true) :
    skipDocEndWhitespace s (fuel' + 1) = s := by
  have hstep : skipDocEndWhitespace s (fuel' + 1) =
      (match s.peek? with
        | some c => if c == ' ' || c == '\t' then skipDocEndWhitespace s.advance fuel' else s
        | none => s) := rfl
  rw [hstep, hpk]
  exact if_neg hw

lemma restStop_of_skipTrailingSpaces {P : Char → Prop} (fuel : Nat) :
    ∀ (s : ScannerState),
    s.inputEnd = s.input.utf8ByteSize →
    (∀ c, (skipTrailingSpaces s fuel).peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ P c) →
    RestStop P s := by
  induction fuel with
  | zero => intro s hend hstop; exact restStop_of_peek_stop hend hstop
  | succ fuel' ih =>
    intro s hend hstop
    cases hpk : s.peek? with
    | none =>
      exact restStop_of_peek_stop hend (fun c hc => by rw [hc] at hpk; cases hpk)
    | some c =>
      obtain ⟨hlt, hget⟩ := peek_some_head hend hpk
      by_cases hw : (c == ' ' || c == '\t') = true
      · rw [skipTrailingSpaces_step_white hpk hw] at hstop
        have hadv : RestStop P s.advance := by
          refine ih s.advance ?_ hstop
          rw [advance_inputEnd, advance_input]; exact hend
        intro l hl
        cases hl with
        | at_end _ _ => omega
        | cons p hplt c' rest hc' hrest =>
          have hce : c' = c := by rw [← hget, ← hc']
          subst hce
          refine LineStop.white (by
            simp only [Bool.or_eq_true, beq_iff_eq] at hw
            exact hw) ?_
          refine hadv rest ?_
          rw [advance_input, advance_offset_eq s hlt]
          exact hrest
      · rw [skipTrailingSpaces_step_stop hpk hw] at hstop
        exact restStop_of_peek_stop hend (fun c' hc' => hstop c' hc')

lemma restNoOpen_of_skipTrailingSpaces (fuel : Nat) :
    ∀ (s : ScannerState),
    s.inputEnd = s.input.utf8ByteSize →
    (∀ c, (skipTrailingSpaces s fuel).peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ ¬(c = '[' ∨ c = '{')) →
    RestNoOpen s := restStop_of_skipTrailingSpaces fuel

/-- The `skipDocEndWhitespace` clone of the same walk. -/
lemma restStop_of_skipDocEndWhitespace {P : Char → Prop} (fuel : Nat) :
    ∀ (s : ScannerState),
    s.inputEnd = s.input.utf8ByteSize →
    (∀ c, (skipDocEndWhitespace s fuel).peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ P c) →
    RestStop P s := by
  induction fuel with
  | zero => intro s hend hstop; exact restStop_of_peek_stop hend hstop
  | succ fuel' ih =>
    intro s hend hstop
    cases hpk : s.peek? with
    | none =>
      exact restStop_of_peek_stop hend (fun c hc => by rw [hc] at hpk; cases hpk)
    | some c =>
      obtain ⟨hlt, hget⟩ := peek_some_head hend hpk
      by_cases hw : (c == ' ' || c == '\t') = true
      · rw [skipDocEndWhitespace_step_white hpk hw] at hstop
        have hadv : RestStop P s.advance := by
          refine ih s.advance ?_ hstop
          rw [advance_inputEnd, advance_input]; exact hend
        intro l hl
        cases hl with
        | at_end _ _ => omega
        | cons p hplt c' rest hc' hrest =>
          have hce : c' = c := by rw [← hget, ← hc']
          subst hce
          refine LineStop.white (by
            simp only [Bool.or_eq_true, beq_iff_eq] at hw
            exact hw) ?_
          refine hadv rest ?_
          rw [advance_input, advance_offset_eq s hlt]
          exact hrest
      · rw [skipDocEndWhitespace_step_stop hpk hw] at hstop
        exact restStop_of_peek_stop hend (fun c' hc' => hstop c' hc')

lemma restNoOpen_of_skipDocEndWhitespace (fuel : Nat) :
    ∀ (s : ScannerState),
    s.inputEnd = s.input.utf8ByteSize →
    (∀ c, (skipDocEndWhitespace s fuel).peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ ¬(c = '[' ∨ c = '{')) →
    RestNoOpen s := restStop_of_skipDocEndWhitespace fuel

/-! ## §4 Validator producers -/

/-- **The allowlist IS `NodeTail`** (item 37): `validateTrailingContent`'s
    three-way test is `[79] s-l-comments` plus `[154]`/`[155]`'s `:`, which is
    the set the production names.  Item 10 wrote the projection here — its
    consumer's `¬(c = '[' ∨ c = '{')` — and that is what made the residue's
    `-`/`?` unanswerable four sites later. -/
lemma stop_of_allowlist {c : Char}
    (h : isLineBreakBool c || c == '#' || c == ':') :
    ¬(c = ' ' ∨ c = '\t') ∧ NodeTail c := by
  simp only [Bool.or_eq_true, beq_iff_eq, isLineBreakBool,
    isLineFeedBool, isCarriageReturnBool] at h
  refine ⟨by rintro (rfl | rfl) <;> simp_all, ?_⟩
  rcases h with (hbr | rfl) | rfl
  · exact Or.inl (Or.inl (by rcases hbr with rfl | rfl <;> decide))
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr rfl

/-- §7.5: a passed `validateTrailingContent` leaves the rest of the line at
    `NodeTail` — a break, a `#`, or the `:` of an implicit key. -/
lemma restNodeTail_of_validateTrailingContent {s : ScannerState} {k : Nat}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : validateTrailingContent s k = .ok ()) :
    RestNodeTail s := by
  unfold validateTrailingContent at hok
  simp only [pure, Except.pure] at hok
  refine restStop_of_skipTrailingSpaces (k - s.offset + 1) s hend
    (fun c hc => ?_)
  split at hok
  · rename_i hnone
    rw [hc] at hnone; cases hnone
  · rename_i c' hsome
    rw [hc] at hsome
    injection hsome with hce
    subst hce
    split at hok
    · rename_i hallow
      exact stop_of_allowlist hallow
    · simp at hok

/-- [137]/[140]: a passed `validateFlowClose` at flow level 0 — the same five
    lines of code, and so the same set. -/
lemma restNodeTail_of_validateFlowClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hfl : s.flowLevel = 0)
    (hok : validateFlowClose s = .ok ()) :
    RestNodeTail s := by
  unfold validateFlowClose at hok
  rw [if_pos (by simp [hfl])] at hok
  simp only [pure, Except.pure] at hok
  refine restStop_of_skipTrailingSpaces (s.inputEnd - s.offset + 1) s hend
    (fun c hc => ?_)
  split at hok
  · rename_i hnone
    rw [hc] at hnone; cases hnone
  · rename_i c' hsome
    rw [hc] at hsome
    injection hsome with hce
    subst hce
    split at hok
    · rename_i hallow
      exact stop_of_allowlist hallow
    · simp at hok

/-- [104] (item 9h): a passed `validateAliasClose` in block context — it IS
    `validateTrailingContent`, one `if` down. -/
lemma restNodeTail_of_validateAliasClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hflow : s.inFlow = false)
    (hok : validateAliasClose s = .ok ()) :
    RestNodeTail s := by
  unfold validateAliasClose at hok
  rw [if_neg (by simp [hflow])] at hok
  exact restNodeTail_of_validateTrailingContent hend hok

/-! Item 10's conclusions, each one `mono` off the rung above.  Every consumer
that only ever asked about a flow open is unchanged. -/

lemma restNoOpen_of_validateTrailingContent {s : ScannerState} {k : Nat}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : validateTrailingContent s k = .ok ()) :
    RestNoOpen s :=
  (restNodeTail_of_validateTrailingContent hend hok).mono (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

lemma restNoOpen_of_validateFlowClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hfl : s.flowLevel = 0)
    (hok : validateFlowClose s = .ok ()) :
    RestNoOpen s :=
  (restNodeTail_of_validateFlowClose hend hfl hok).mono (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

lemma restNoOpen_of_validateAliasClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hflow : s.inFlow = false)
    (hok : validateAliasClose s = .ok ()) :
    RestNoOpen s :=
  (restNodeTail_of_validateAliasClose hend hflow hok).mono (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

/-- The flow-close producer at the union the park carries. -/
lemma restNodeStop_of_validateFlowClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hfl : s.flowLevel = 0)
    (hok : validateFlowClose s = .ok ()) :
    RestNodeStop s :=
  (restNodeTail_of_validateFlowClose hend hfl hok).mono (fun _ => NodeTail.toNodeStop)

/-! ## §5 Scan-level producers: the quoted scalars and `...`

No loop analysis is needed: each validator ran on the very state the scan
returns (modulo token emission), and if its white-skip had exhausted fuel
mid-whites the landing peek would be a white — outside every allowlist — so
`.ok` itself rules that out.  The `hend'` inputs come from the call sites'
`ScannerSurfCorr` (its `end_eq` field). -/

lemma scanDoubleQuoted_restNodeTail {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanDoubleQuoted s = .ok s') :
    RestNodeTail s' := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i ev heq_loop
    obtain ⟨content, s_after_close⟩ := ev
    split at hok
    · split at hok
      · cases hok
      · rename_i u hval
        cases u
        injection hok with h_eq
        subst h_eq
        exact (restNodeTail_of_validateTrailingContent (s := s_after_close)
          hend' hval).congr rfl rfl
    · rename_i hnflow
      rw [hflow] at hnflow
      simp at hnflow

lemma scanSingleQuoted_restNodeTail {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanSingleQuoted s = .ok s') :
    RestNodeTail s' := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i ev heq_loop
    obtain ⟨content, s_after_close⟩ := ev
    split at hok
    · split at hok
      · cases hok
      · rename_i u hval
        cases u
        injection hok with h_eq
        subst h_eq
        exact (restNodeTail_of_validateTrailingContent (s := s_after_close)
          hend' hval).congr rfl rfl
    · rename_i hnflow
      rw [hflow] at hnflow
      simp at hnflow

/-! Item 10's two quoted conclusions, each one `mono` off the rung above. -/

lemma scanDoubleQuoted_restNoOpen {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanDoubleQuoted s = .ok s') :
    RestNoOpen s' :=
  (scanDoubleQuoted_restNodeTail hflow hend' hok).mono
    (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

lemma scanSingleQuoted_restNoOpen {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanSingleQuoted s = .ok s') :
    RestNoOpen s' :=
  (scanSingleQuoted_restNodeTail hflow hend' hok).mono
    (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

/-- **[204] `l-document-suffix ::= c-document-end s-l-comments`** — the
    marker's own tail, at its own strength (item 36).  `scanDocumentEnd`'s
    suffix probe validated the returned state's window (the probe starts at
    `result.offset`) and admitted exactly `s-l-comments`: a break, a `#`, or
    end of input.  Nothing about a `[` here — the flow-open reading below is
    one `mono` away, and every OTHER character is refuted too, which is what a
    `...` parked mid-line owes the block dispatch. -/
lemma scanDocumentEnd_restTailSuffix {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanDocumentEnd s = .ok s') :
    RestTailSuffix s' := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · -- the suffix-probe match; each surviving arm pins the landing peek
    split at hok
    · -- peek = none
      rename_i hpk
      have h_eq := Except.ok.inj hok
      rw [h_eq] at hpk
      apply restStop_of_skipDocEndWhitespace _ s' hend'
      intro c hc
      rw [hc] at hpk
      cases hpk
    · -- peek = some '#'
      rename_i hpk
      have h_eq := Except.ok.inj hok
      rw [h_eq] at hpk
      apply restStop_of_skipDocEndWhitespace _ s' hend'
      intro c hc
      rw [hc] at hpk
      injection hpk with hce
      subst hce
      exact ⟨by decide, Or.inr rfl⟩
    · -- peek = some c, break required
      rename_i c₀ hne1 hne2 hpk
      split at hok
      · rename_i hbr
        have h_eq := Except.ok.inj hok
        rw [h_eq] at hpk
        apply restStop_of_skipDocEndWhitespace _ s' hend'
        intro c hc
        rw [hc] at hpk
        injection hpk with hce
        subst hce
        refine ⟨?_, Or.inl hbr⟩
        simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
          Bool.or_eq_true, beq_iff_eq] at hbr
        rintro (rfl | rfl) <;> simp_all
      · cases hok

/-- [204] read at item 10's strength: one `mono`, at the consumer. -/
lemma scanDocumentEnd_restNoOpen {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanDocumentEnd s = .ok s') :
    RestNoOpen s' :=
  (scanDocumentEnd_restTailSuffix hend' hok).mono (fun _ => TailSuffix.toNoOpenHead)


/-! ## §6 Offset/inputEnd walk facts for the two scalar loops -/

private lemma consumeNewline_fields (s : ScannerState) :
    s.offset ≤ (consumeNewline s).offset ∧ (consumeNewline s).inputEnd = s.inputEnd := by
  unfold consumeNewline
  split
  · exact ⟨advance_offset_ge s, advance_inputEnd s⟩
  · dsimp only []
    split
    · refine ⟨?_, advance_inputEnd s⟩
      show s.offset ≤ (String.Pos.Raw.next s.advance.input ⟨s.advance.offset⟩).byteIdx
      have h1 := advance_offset_ge s
      rw [next_byteIdx]
      have := Char.utf8Size_pos (String.Pos.Raw.get s.advance.input ⟨s.advance.offset⟩)
      omega
    · exact ⟨advance_offset_ge s, advance_inputEnd s⟩
  · exact ⟨Nat.le_refl _, rfl⟩

private lemma peek_some_lt {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) : s.offset < s.inputEnd := by
  unfold ScannerState.peek? at hpk
  by_cases h : s.offset < s.inputEnd
  · exact h
  · rw [if_neg h] at hpk; cases hpk

private lemma peek_some_get {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
  unfold ScannerState.peek? at hpk
  rw [if_pos (peek_some_lt hpk)] at hpk
  exact Option.some.inj hpk

private lemma consumeNewline_offset_gt {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true) :
    s.offset < (consumeNewline s).offset := by
  have hlt : s.offset < s.inputEnd := peek_some_lt hpk
  unfold consumeNewline
  rw [hpk]
  split
  · exact advance_offset_lt s hlt
  · dsimp only []
    split
    · show s.offset < (String.Pos.Raw.next s.advance.input ⟨s.advance.offset⟩).byteIdx
      have h1 := advance_offset_lt s hlt
      rw [next_byteIdx]
      have := Char.utf8Size_pos (String.Pos.Raw.get s.advance.input ⟨s.advance.offset⟩)
      omega
    · exact advance_offset_lt s hlt
  · rename_i hne1 hne2
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
      Bool.or_eq_true, beq_iff_eq] at hbr
    rcases hbr with rfl | rfl <;> simp_all

private lemma consumeNewline_col0 {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true) :
    (consumeNewline s).col = 0 := by
  have hlt : s.offset < s.inputEnd := peek_some_lt hpk
  have hget := peek_some_get hpk
  unfold consumeNewline
  rw [hpk]
  split
  · rename_i heq
    injection heq with hc'
    subst hc'
    exact advance_col_newline s hlt (by rw [hget]; rfl)
  · rename_i heq
    injection heq with hc'
    subst hc'
    have hcol0 : s.advance.col = 0 := advance_col_cr s hlt (by rw [hget]; rfl)
    dsimp only []
    split
    all_goals exact hcol0
  · rename_i hne1 hne2
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
      Bool.or_eq_true, beq_iff_eq] at hbr
    rcases hbr with rfl | rfl <;> simp_all

private lemma skipWhitespaceLoop_fields (fuel : Nat) : ∀ (s : ScannerState),
    s.offset ≤ (skipWhitespaceLoop s fuel).offset ∧
    (skipWhitespaceLoop s fuel).inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s; unfold skipWhitespaceLoop; exact ⟨Nat.le_refl _, rfl⟩
  | succ fuel' ih =>
    intro s
    unfold skipWhitespaceLoop
    split
    · split
      · obtain ⟨h1, h2⟩ := ih s.advance
        exact ⟨Nat.le_trans (advance_offset_ge s) h1, h2.trans (advance_inputEnd s)⟩
      · exact ⟨Nat.le_refl _, rfl⟩
    · exact ⟨Nat.le_refl _, rfl⟩

private lemma skipWhitespace_fields (s : ScannerState) :
    s.offset ≤ (skipWhitespace s).offset ∧ (skipWhitespace s).inputEnd = s.inputEnd :=
  skipWhitespaceLoop_fields _ s

private lemma skipSpacesLoop_fields (fuel : Nat) : ∀ (s : ScannerState),
    s.offset ≤ (skipSpacesLoop s fuel).offset ∧
    (skipSpacesLoop s fuel).inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s; unfold skipSpacesLoop; exact ⟨Nat.le_refl _, rfl⟩
  | succ fuel' ih =>
    intro s
    unfold skipSpacesLoop
    split
    · obtain ⟨h1, h2⟩ := ih s.advance
      exact ⟨Nat.le_trans (advance_offset_ge s) h1, h2.trans (advance_inputEnd s)⟩
    · exact ⟨Nat.le_refl _, rfl⟩

private lemma skipSpaces_fields (s : ScannerState) :
    s.offset ≤ (skipSpaces s).offset ∧ (skipSpaces s).inputEnd = s.inputEnd :=
  skipSpacesLoop_fields _ s

private lemma skipBlankLinesLoop_fields (fuel : Nat) : ∀ (s : ScannerState) (cnt inputEnd : Nat),
    s.offset ≤ (skipBlankLinesLoop s cnt fuel inputEnd).2.offset ∧
    (skipBlankLinesLoop s cnt fuel inputEnd).2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s cnt inputEnd; unfold skipBlankLinesLoop; exact ⟨Nat.le_refl _, rfl⟩
  | succ fuel' ih =>
    intro s cnt inputEnd
    unfold skipBlankLinesLoop
    dsimp only []
    split
    · split
      · obtain ⟨h1, h2⟩ := ih (consumeNewline (skipWhitespace s)) (cnt + 1) inputEnd
        obtain ⟨hw1, hw2⟩ := skipWhitespace_fields s
        obtain ⟨hn1, hn2⟩ := consumeNewline_fields (skipWhitespace s)
        exact ⟨Nat.le_trans hw1 (Nat.le_trans hn1 h1),
               h2.trans (hn2.trans hw2)⟩
      · exact ⟨Nat.le_refl _, rfl⟩
    · exact ⟨Nat.le_refl _, rfl⟩

/-- `collectPlainScalar_handleBlockLineBreak` starts with the break's
    `consumeNewline`, so a `some` result strictly advanced the offset. -/
private lemma handleBlockLineBreak_progress {s : ScannerState} {content : String}
    {ci ie : Nat} {content' : String} {s2 : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true)
    (h : collectPlainScalar_handleBlockLineBreak s content ci ie = some (content', s2)) :
    s.offset < s2.offset ∧ s2.inputEnd = s.inputEnd := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  simp only [] at h
  split at h
  · cases h
  · split at h
    · cases h
    · have hpair := Prod.mk.inj (Option.some.inj h)
      obtain ⟨-, h2⟩ := hpair
      subst h2
      have hgt := consumeNewline_offset_gt hpk hbr
      obtain ⟨hb1, hb2⟩ := skipBlankLinesLoop_fields (ie - (consumeNewline s).offset + 1)
        (consumeNewline s) 0 ie
      obtain ⟨hs1, hs2⟩ := skipSpaces_fields
        (skipBlankLinesLoop (consumeNewline s) 0 (ie - (consumeNewline s).offset + 1) ie).2
      obtain ⟨hw1, hw2⟩ := skipWhitespace_fields
        (skipSpaces (skipBlankLinesLoop (consumeNewline s) 0 (ie - (consumeNewline s).offset + 1) ie).2)
      have hn2 := (consumeNewline_fields s).2
      exact ⟨by omega, by omega⟩

/-! ## §7 The plain scalar: fuel adequacy, then the stop shape -/

/-- The `terminates?` probe stops the scan AT its own state, terminated, and
    only at `#`, `:` or a column-0 document boundary (block context). -/
private lemma terminates?_inv {c : Char} {s : ScannerState}
    {content spaces : String} {r : PlainScalarResult}
    (h : collectPlainScalar_terminates? c s content spaces false = some r) :
    r.state = s ∧ r.terminated = true ∧ (c = '#' ∨ c = ':' ∨ s.col = 0) := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · rename_i hcond
    injection h with h; subst h
    refine ⟨rfl, rfl, Or.inl ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.1
  · split at h
    · rename_i hcolon
      simp only [] at h
      split at h <;> split at h <;>
        first
          | (injection h with h; subst h;
             exact ⟨rfl, rfl, Or.inr (Or.inl (by simpa using hcolon))⟩)
          | cases h
    · split at h
      · rename_i hflow
        simp at hflow
      · split at h
        · rename_i hdoc
          injection h with h; subst h
          refine ⟨rfl, rfl, Or.inr (Or.inr ?_)⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hdoc
          simpa using hdoc.1
        · cases h

/-- With more fuel than remaining bytes, the block-context plain-scalar walk
    always TERMINATES (never exits on fuel). -/
private lemma collectPlainScalarLoop_terminated (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    s.inputEnd - s.offset < fuel →
    r.terminated = true := by
  induction fuel with
  | zero => intro s _ _ _ _ r _ hb; omega
  | succ fuel' ih =>
    intro s content spaces ci ie r hok hb
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq; rfl
    · rename_i c hpk
      have hlt : s.offset < s.inputEnd := by
        unfold ScannerState.peek? at hpk
        by_cases h : s.offset < s.inputEnd
        · exact h
        · rw [if_neg h] at hpk; cases hpk
      split at hok
      · rename_i hterm
        injection hok with h_eq; subst h_eq
        exact (terminates?_inv hterm).2.1
      · split at hok
        · -- break, block context
          rename_i hbr
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq; rfl
            · rename_i content' s2 hblk
              obtain ⟨hgt, hend2⟩ := handleBlockLineBreak_progress hpk hbr hblk
              split at hok
              · injection hok with h_eq; subst h_eq; rfl
              · dsimp only [] at hok
                generalize h_loop : collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq; rfl
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exact ih s2 content' "" ci ie _ h_loop (by omega)
                | error e => simp at hok
        · split at hok
          · -- whitespace: advance
            have hadv := advance_offset_lt s hlt
            have hend2 := advance_inputEnd s
            exact ih s.advance content _ ci ie r hok (by omega)
          · split at hok
            · injection hok with h_eq; subst h_eq; rfl
            · -- plain-safe content: advance
              simp only [] at hok
              have hadv := advance_offset_lt s hlt
              have hend2 := advance_inputEnd s
              exact ih s.advance _ "" ci ie r hok (by omega)

/-- `[128] ns-plain-safe-out` is `ns-char`, so what makes the walk stop
    without a validator is a character no production admits at all. -/
private lemma offLine_of_not_plainSafe {c : Char}
    (hnw : ¬(isWhiteSpaceBool c = true)) (hnb : ¬(isLineBreakBool c = true))
    (h : (!isPlainSafeBool c false) = true) : OffLine c := by
  have hw : isWhiteSpaceBool c = false := by simpa using hnw
  have hb : isLineBreakBool c = false := by simpa using hnb
  have hps : isPlainSafeBool c false = false := by simpa using h
  by_cases hbom : c = '﻿'
  · exact Or.inr hbom
  · refine Or.inl ?_
    by_cases hp : isPrintableBool c = true
    · rw [show isPlainSafeBool c false = true from by
        simp [isPlainSafeBool, hw, hb, hp, hbom]] at hps
      cases hps
    · simpa using hp

/-- A terminated block-context plain-scalar walk lands at column 0 or on a
    stop character — and the stop set is `NodeStop` exactly (item 37): the
    walk's own three exits are `#`, `:` and a break (`NodeTail`), plus a
    character outside `ns-plain-safe-out`, which is `OffLine`.  Every `-`, `?`
    and `[` is ABSORBED, which is why none of them can be here. -/
private lemma collectPlainScalarLoop_stop (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    r.terminated = true →
    r.state.col = 0 ∨ (∀ c, r.state.peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ NodeStop c) := by
  induction fuel with
  | zero =>
    intro s _ _ _ _ r hok hterm
    unfold collectPlainScalarLoop at hok
    injection hok with h_eq; subst h_eq
    cases hterm
  | succ fuel' ih =>
    intro s content spaces ci ie r hok hterm
    unfold collectPlainScalarLoop at hok
    split at hok
    · rename_i hpk
      injection hok with h_eq; subst h_eq
      exact Or.inr (fun c hc => by rw [hc] at hpk; cases hpk)
    · rename_i c hpk
      split at hok
      · rename_i hterm'
        obtain ⟨hst, -, hdisj⟩ := terminates?_inv hterm'
        injection hok with h_eq; subst h_eq
        rw [hst]
        rcases hdisj with rfl | rfl | hcol
        · exact Or.inr (fun c' hc' => by
            rw [hpk] at hc'
            injection hc' with hce
            subst hce
            exact ⟨by decide, Or.inl (Or.inl (Or.inr rfl))⟩)
        · exact Or.inr (fun c' hc' => by
            rw [hpk] at hc'
            injection hc' with hce
            subst hce
            exact ⟨by decide, Or.inl (Or.inr rfl)⟩)
        · exact Or.inl hcol
      · -- termination char classes below
        have hstop_break : isLineBreakBool c = true →
            (∀ c', s.peek? = some c' → ¬(c' = ' ' ∨ c' = '\t') ∧ NodeStop c') := by
          intro hbr c' hc'
          rw [hpk] at hc'
          injection hc' with hce
          subst hce
          refine ⟨?_, Or.inl (Or.inl (Or.inl hbr))⟩
          simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
            Bool.or_eq_true, beq_iff_eq] at hbr
          rintro (rfl | rfl) <;> simp_all
        split at hok
        · rename_i hbr
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact Or.inr (hstop_break hbr)
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq
                exact Or.inr (hstop_break hbr)
              · dsimp only [] at hok
                generalize h_loop : collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq
                    exact Or.inr (hstop_break hbr)
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exact ih s2 content' "" ci ie _ h_loop hterm
                | error e => simp at hok
        · split at hok
          · exact ih s.advance content _ ci ie r hok hterm
          · split at hok
            · rename_i hunsafe
              injection hok with h_eq; subst h_eq
              refine Or.inr (fun c' hc' => ?_)
              rw [hpk] at hc'
              injection hc' with hce
              subst hce
              rename_i hnbr hnws
              constructor
              · intro habs
                apply hnws
                simp only [isWhiteSpaceBool, isSpaceBool, isTabBool,
                  Bool.or_eq_true, beq_iff_eq]
                exact habs
              · exact Or.inr (offLine_of_not_plainSafe hnws hnbr hunsafe)
            · exact ih s.advance _ "" ci ie r hok hterm

/-- `scanPlainScalar` in block context: the emitted state sits at column 0 or
    on a `NodeStop` character.  (`hend'` from the caller's corr.) -/
lemma scanPlainScalar_restNodeStop {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanPlainScalar s = .ok s') :
    s'.col = 0 ∨ RestNodeStop s' := by
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  rw [hflow] at hok
  split at hok
  · cases hok
  · rename_i result h_loop
    injection hok with h_eq
    subst h_eq
    have hterm := collectPlainScalarLoop_terminated _ s "" "" _ s.inputEnd result h_loop
      (by omega)
    have hstop := collectPlainScalarLoop_stop _ s "" "" _ s.inputEnd result h_loop hterm
    cases hstop with
    | inl hcol => exact Or.inl hcol
    | inr hpk =>
      refine Or.inr ((restStop_of_peek_stop (s := result.state) hend' ?_).congr rfl rfl)
      exact hpk

lemma scanPlainScalar_restNoOpen {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanPlainScalar s = .ok s') :
    s'.col = 0 ∨ RestNoOpen s' :=
  (scanPlainScalar_restNodeStop hflow hend' hok).imp id
    (RestStop.mono (fun _ => NodeStop.toNoOpenHead))

/-! ## §8 The block scalar: every ending is a column-0 line, EOF, or a
non-printable stop -/

private lemma consumeExactSpaces_fields (count : Nat) : ∀ (s : ScannerState),
    s.offset ≤ (consumeExactSpaces s count).2.offset ∧
    (consumeExactSpaces s count).2.inputEnd = s.inputEnd := by
  induction count with
  | zero => intro s; unfold consumeExactSpaces; exact ⟨Nat.le_refl _, rfl⟩
  | succ count' ih =>
    intro s
    unfold consumeExactSpaces
    split
    · obtain ⟨h1, h2⟩ := ih s.advance
      exact ⟨Nat.le_trans (advance_offset_ge s) h1, h2.trans (advance_inputEnd s)⟩
    · exact ⟨Nat.le_refl _, rfl⟩

private lemma collectLineContentLoop_fields (fuel : Nat) : ∀ (s : ScannerState) (content : String),
    s.offset ≤ (collectLineContentLoop s content fuel).2.offset ∧
    (collectLineContentLoop s content fuel).2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s content; unfold collectLineContentLoop; exact ⟨Nat.le_refl _, rfl⟩
  | succ fuel' ih =>
    intro s content
    unfold collectLineContentLoop
    split
    · split
      · exact ⟨Nat.le_refl _, rfl⟩
      · obtain ⟨h1, h2⟩ := ih s.advance (content.push _)
        exact ⟨Nat.le_trans (advance_offset_ge s) h1, h2.trans (advance_inputEnd s)⟩
    · exact ⟨Nat.le_refl _, rfl⟩

/-- With adequate fuel, `collectLineContentLoop` stops at EOF, a break, a
    non-printable, or the BOM — never on a white or a bracket. -/
private lemma collectLineContentLoop_stop (fuel : Nat) : ∀ (s : ScannerState) (content : String),
    s.inputEnd - s.offset < fuel →
    ∀ c, (collectLineContentLoop s content fuel).2.peek? = some c →
      isLineBreakBool c = true ∨ isPrintableBool c = false ∨ c = '﻿' := by
  induction fuel with
  | zero => intro s _ hb; omega
  | succ fuel' ih =>
    intro s content hb c hc
    unfold collectLineContentLoop at hc
    split at hc
    · rename_i c₀ hpk
      split at hc
      · rename_i hstopc
        rw [hpk] at hc
        injection hc with hce
        subst hce
        exact or_assoc.mp (by simpa using hstopc)
      · rename_i hcont
        have hlt : s.offset < s.inputEnd := by
          unfold ScannerState.peek? at hpk
          by_cases h : s.offset < s.inputEnd
          · exact h
          · rw [if_neg h] at hpk; cases hpk
        have hadv := advance_offset_lt s hlt
        have hend2 := advance_inputEnd s
        exact ih s.advance (content.push _) (by omega) c hc
    · rename_i hpk
      rw [hpk] at hc
      cases hc

/-- The block-scalar body walk: given a column-0-or-EOF entry, every exit is
    column 0, EOF, or an `OffLine` stop — the SAME line collection the plain
    scalar runs, so the same set (item 37).  A mid-line exit is the one arm
    that says anything, and `collectLineContentLoop_stop` already named it. -/
private lemma collectBlockScalarLoop_end (fuel : Nat) :
    ∀ (s : ScannerState) (raw : String) (ci ie : Nat),
    (s.col = 0 ∨ s.peek? = none) →
    s.inputEnd - s.offset < fuel →
    s.inputEnd ≤ ie →
    (collectBlockScalarLoop s raw fuel ci ie).2.col = 0 ∨
    (∀ c, (collectBlockScalarLoop s raw fuel ci ie).2.peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ NodeStop c) := by
  induction fuel with
  | zero => intro s _ _ _ _ hb _; omega
  | succ fuel' ih =>
    intro s raw ci ie hentry hb hie
    unfold collectBlockScalarLoop
    split
    · -- document boundary at col 0
      rename_i hdoc
      simp only [Bool.and_eq_true, beq_iff_eq] at hdoc
      exact Or.inl (by simpa using hdoc.1)
    · -- name the indent-consumption result
      generalize hces : consumeExactSpaces s ci = pr
      obtain ⟨spc, sas⟩ := pr
      have hsas1 : s.offset ≤ sas.offset := by
        have h := (consumeExactSpaces_fields ci s).1; rw [hces] at h; exact h
      have hsas2 : sas.inputEnd = s.inputEnd := by
        have h := (consumeExactSpaces_fields ci s).2; rw [hces] at h; exact h
      try dsimp only []
      split
      · -- EOF after the indent spaces
        rename_i hpk
        exact Or.inr (fun c hc => by rw [hc] at hpk; cases hpk)
      · rename_i c₀ hpk
        have hlt := peek_some_lt hpk
        split
        · -- an empty line: consume its break and recurse at col 0
          rename_i hbr
          try dsimp only []
          have hgt := consumeNewline_offset_gt hpk hbr
          have hn2 := (consumeNewline_fields sas).2
          exact ih (consumeNewline sas) _ ci ie
            (Or.inl (consumeNewline_col0 hpk hbr)) (by omega) (by omega)
        · split
          · -- dedented non-empty line: return the ENTRY state
            cases hentry with
            | inl hcol => exact Or.inl hcol
            | inr hpk0 => exact Or.inr (fun c hc => by rw [hc] at hpk0; cases hpk0)
          · -- content line: name the line-collection result
            try dsimp only []
            generalize hlcl : collectLineContentLoop sas "" (ie - sas.offset + 1) = lr
            obtain ⟨lc, sal⟩ := lr
            have hsal1 : sas.offset ≤ sal.offset := by
              have h := (collectLineContentLoop_fields (ie - sas.offset + 1) sas "").1
              rw [hlcl] at h; exact h
            have hsal2 : sal.inputEnd = sas.inputEnd := by
              have h := (collectLineContentLoop_fields (ie - sas.offset + 1) sas "").2
              rw [hlcl] at h; exact h
            try dsimp only []
            split
            · rename_i c' hpk'
              split
              · -- break after the line: consume and recurse at col 0
                rename_i hbr'
                try dsimp only []
                have hgt := consumeNewline_offset_gt hpk' hbr'
                have hn2 := (consumeNewline_fields sal).2
                exact ih (consumeNewline sal) _ ci ie
                  (Or.inl (consumeNewline_col0 hpk' hbr')) (by omega) (by omega)
              · -- non-break stop mid-line: a non-printable or BOM
                rename_i hnbr
                refine Or.inr (fun c hc => ?_)
                rw [hpk'] at hc
                injection hc with hce
                subst hce
                have hstop := collectLineContentLoop_stop (ie - sas.offset + 1) sas ""
                  (by omega)
                rw [hlcl] at hstop
                rcases hstop c' hpk' with hbr2 | hnp | hbom
                · exact absurd hbr2 (by simpa using hnbr)
                · exact ⟨by rintro (rfl | rfl) <;> exact absurd hnp (by decide),
                         Or.inr (Or.inl hnp)⟩
                · subst hbom
                  exact ⟨by decide, Or.inr (Or.inr rfl)⟩
            · -- EOF after the line
              rename_i hpk'
              exact Or.inr (fun c hc => by rw [hc] at hpk'; cases hpk')

private lemma parseBlockHeaderLoop_inputEnd (fuel : Nat) :
    ∀ (s : ScannerState) (chomp : ChompStyle) (eo : Option Nat),
    (parseBlockHeaderLoop s chomp eo fuel).2.2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s _ _; rfl
  | succ fuel' ih =>
    intro s chomp eo
    unfold parseBlockHeaderLoop
    split
    · exact (ih s.advance _ _).trans (advance_inputEnd s)
    · exact (ih s.advance _ _).trans (advance_inputEnd s)
    · split
      · exact (ih s.advance _ _).trans (advance_inputEnd s)
      · rfl
    · rfl

private lemma collectCommentTextLoop_inputEnd (fuel : Nat) :
    ∀ (s : ScannerState) (text : String),
    (collectCommentTextLoop s text fuel).2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s _; unfold collectCommentTextLoop; rfl
  | succ fuel' ih =>
    intro s text
    unfold collectCommentTextLoop
    split
    · split
      · rfl
      · exact (ih s.advance _).trans (advance_inputEnd s)
    · rfl

private lemma scanBlockScalarSkipComment_inputEnd (s : ScannerState) :
    (scanBlockScalarSkipComment s).inputEnd = s.inputEnd := by
  unfold scanBlockScalarSkipComment
  split
  · dsimp only []
    generalize hp : collectCommentTextLoop s.advance ""
      (s.advance.inputEnd - s.advance.offset) = pr
    obtain ⟨text, s2⟩ := pr
    have hcc := collectCommentTextLoop_inputEnd
      (s.advance.inputEnd - s.advance.offset) s.advance ""
    rw [hp] at hcc
    dsimp only [] at hcc
    try dsimp only []
    split
    · split
      · exact hcc.trans (advance_inputEnd s)
      · rfl
    · rfl
  · rfl

private lemma scanBlockScalarConsumeNewline_inputEnd {s s' : ScannerState}
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.inputEnd = s.inputEnd := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · have he := Except.ok.inj h; subst he
      exact (consumeNewline_fields s).2
    · split at h
      · have he := Except.ok.inj h; subst he; rfl
      · cases h
  · have he := Except.ok.inj h; subst he; rfl

/-- `scanBlockScalarBody`: the emitted state sits at column 0 or at a stop. -/
private lemma scanBlockScalarBody_restNodeStop {s_orig s_after_newline s' : ScannerState}
    {chomp : ChompStyle} {eo : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (hentry : s_after_newline.col = 0 ∨ s_after_newline.peek? = none)
    (hie : s_after_newline.inputEnd ≤ s_orig.inputEnd)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanBlockScalarBody s_orig s_after_newline chomp eo isLit startPos = .ok s') :
    s'.col = 0 ∨ RestNodeStop s' := by
  cases eo with
  | some m =>
    unfold scanBlockScalarBody at hok
    dsimp only [] at hok
    generalize hlr : collectBlockScalarLoop s_after_newline ""
      (s_orig.inputEnd - s_after_newline.offset + 1)
      (max 0 (s_orig.currentIndent + (m : Int))).toNat s_orig.inputEnd = lr at hok
    have hloop := collectBlockScalarLoop_end (s_orig.inputEnd - s_after_newline.offset + 1)
      s_after_newline "" (max 0 (s_orig.currentIndent + (m : Int))).toNat
      s_orig.inputEnd hentry (by omega) hie
    rw [hlr] at hloop
    obtain ⟨raw2, sac⟩ := lr
    dsimp only [] at hok hloop
    injection hok with h_eq
    subst h_eq
    cases hloop with
    | inl h0 => exact Or.inl h0
    | inr hpk => exact Or.inr ((restStop_of_peek_stop (s := sac) hend' hpk).congr rfl rfl)
  | none =>
    unfold scanBlockScalarBody at hok
    dsimp only [] at hok
    generalize hci : autoDetectBlockScalarIndent s_after_newline
      (max 0 (s_orig.currentIndent + 1)).toNat s_orig.inputEnd = cip at hok
    obtain ⟨ci, err⟩ := cip
    dsimp only [] at hok
    cases err with
    | some e => cases hok
    | none =>
      dsimp only [] at hok
      generalize hlr : collectBlockScalarLoop s_after_newline ""
        (s_orig.inputEnd - s_after_newline.offset + 1) ci s_orig.inputEnd = lr at hok
      have hloop := collectBlockScalarLoop_end (s_orig.inputEnd - s_after_newline.offset + 1)
        s_after_newline "" ci s_orig.inputEnd hentry (by omega) hie
      rw [hlr] at hloop
      obtain ⟨raw2, sac⟩ := lr
      dsimp only [] at hok hloop
      injection hok with h_eq
      subst h_eq
      cases hloop with
      | inl h0 => exact Or.inl h0
      | inr hpk => exact Or.inr ((restStop_of_peek_stop (s := sac) hend' hpk).congr rfl rfl)

/-- `scanBlockScalar`: the emitted state sits at column 0, at end of input,
    or on an `OffLine` stop.  (`hend'` from the caller's corr.) -/
lemma scanBlockScalar_restNodeStop {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanBlockScalar s = .ok s') :
    s'.col = 0 ∨ RestNodeStop s' := by
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  split at hok
  · cases hok
  · rename_i s_after_newline hnl
    have hentry : s_after_newline.col = 0 ∨ s_after_newline.peek? = none := by
      unfold scanBlockScalarConsumeNewline at hnl
      split at hnl
      · rename_i c₀ hpk₀
        split at hnl
        · rename_i hbr₀
          have h := Except.ok.inj hnl
          subst h
          exact Or.inl (consumeNewline_col0 hpk₀ hbr₀)
        · split at hnl
          · rename_i hnomore
            have h := Except.ok.inj hnl
            subst h
            refine Or.inr ?_
            unfold ScannerState.peek?
            rw [if_neg]
            simp only [Bool.not_eq_true', ScannerState.hasMore,
              decide_eq_false_iff_not] at hnomore
            exact hnomore
          · cases hnl
      · rename_i hpk₀
        have h := Except.ok.inj hnl
        subst h
        exact Or.inr hpk₀
    have hie : s_after_newline.inputEnd ≤ s.inputEnd := by
      have h1 := scanBlockScalarConsumeNewline_inputEnd hnl
      have h2 := scanBlockScalarSkipComment_inputEnd
        (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)
      have h3 := (skipWhitespace_fields (parseBlockHeaderLoop s.advance .clip none 2).2.2).2
      have h4 := parseBlockHeaderLoop_inputEnd 2 s.advance .clip none
      have h5 := advance_inputEnd s
      omega
    exact scanBlockScalarBody_restNodeStop hentry hie hend' hok

lemma scanBlockScalar_restNoOpen {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanBlockScalar s = .ok s') :
    s'.col = 0 ∨ RestNoOpen s' :=
  (scanBlockScalar_restNodeStop hend' hok).imp id
    (RestStop.mono (fun _ => NodeStop.toNoOpenHead))

/-! ## §9 The dispatch-level producer

For a content dispatch that was NOT a property (`&`/`!`), in block context,
the emitted state sits at column 0 or stops the line where §7.5 says a
complete node's line stops: quoted scalars and aliases by their trailing
validation (`NodeTail` — `s-l-comments` plus `[154]`'s `:`), plain and block
scalars by their walks (`NodeTail` or `OffLine`).  The union is `NodeStop`,
and item 10's flow-open reading is one `mono` below it. -/

lemma dispatchContent_restNodeStop {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hna : c ≠ '&') (hnt : c ≠ '!')
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.col = 0 ∨ RestNodeStop s' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq
    exact absurd (by simpa using h_eq) hna
  · split at hok
    · -- '*': the alias arm keeps its validateAliasClose
      split at hok
      · simp at hok
      split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · rename_i v hv
          split at hok
          · simp at hok
          · rename_i u hval
            cases u
            have hvs : v = s' := Except.ok.inj hok
            subst hvs
            have hfl := ScannerCorrectness.scanAnchorOrAlias_preserves_flowLevel s false v hv
            have hflv : v.inFlow = false := by
              unfold ScannerState.inFlow at hflow ⊢
              rw [hfl]
              exact hflow
            exact Or.inr ((restNodeTail_of_validateAliasClose hend' hflv hval).mono
              (fun _ => NodeTail.toNodeStop))
    · split at hok
      · rename_i h_eq
        exact absurd (by simpa using h_eq) hnt
      · split at hok
        · -- '|' or '>': block scalar under the item-9c guard
          exact scanBlockScalar_restNodeStop hend' (peel_blockScalarGuard hok)
        · split at hok
          · -- '"': double-quoted, then the endLine touch-up
            split at hok
            · simp at hok
            · rename_i s_dq hdq
              have heq : (if s_dq.simpleKey.possible then
                  { s_dq with simpleKey := { s_dq.simpleKey with endLine := s_dq.line } }
                else s_dq) = s' := Except.ok.inj hok
              have hfields : s'.input = s_dq.input ∧ s'.offset = s_dq.offset ∧
                  s'.inputEnd = s_dq.inputEnd := by
                rw [← heq]
                split <;> exact ⟨rfl, rfl, rfl⟩
              have hend_dq : s_dq.inputEnd = s_dq.input.utf8ByteSize := by
                rw [← hfields.2.2, ← hfields.1]
                exact hend'
              exact Or.inr (((scanDoubleQuoted_restNodeTail hflow hend_dq hdq).mono
                (fun _ => NodeTail.toNodeStop)).congr hfields.1 hfields.2.1)
          · split at hok
            · -- '\'': single-quoted
              split at hok
              · simp at hok
              · rename_i s_sq hsq
                have heq : (if s_sq.simpleKey.possible then
                    { s_sq with simpleKey := { s_sq.simpleKey with endLine := s_sq.line } }
                  else s_sq) = s' := Except.ok.inj hok
                have hfields : s'.input = s_sq.input ∧ s'.offset = s_sq.offset ∧
                    s'.inputEnd = s_sq.inputEnd := by
                  rw [← heq]
                  split <;> exact ⟨rfl, rfl, rfl⟩
                have hend_sq : s_sq.inputEnd = s_sq.input.utf8ByteSize := by
                  rw [← hfields.2.2, ← hfields.1]
                  exact hend'
                exact Or.inr (((scanSingleQuoted_restNodeTail hflow hend_sq hsq).mono
                  (fun _ => NodeTail.toNodeStop)).congr hfields.1 hfields.2.1)
            · -- plain scalar (or error)
              split at hok
              · exact scanPlainScalar_restNodeStop hflow hend' hok
              · simp at hok

/-- Item 10's dispatch-level conclusion, one `mono` below §9's own. -/
lemma dispatchContent_restNoOpen {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hna : c ≠ '&') (hnt : c ≠ '!')
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.col = 0 ∨ RestNoOpen s' :=
  (dispatchContent_restNodeStop hflow hna hnt hend' hok).imp id
    (RestStop.mono (fun _ => NodeStop.toNoOpenHead))

end L4YAML.Proofs.LineOpenGuard
