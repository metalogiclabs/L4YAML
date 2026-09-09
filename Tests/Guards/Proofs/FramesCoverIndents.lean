import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Scanner.IndexedDispatch
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The frames cover the indent stack (DOCS item 129)

Item 127 read a popping landing from the SCANNER's side — the column it rests at
is the top entry's own, on an entry the incoming stack already held — and item
128 removed that reading's escape.  `ResumeFrames.resumeAt` asks the SURFACE
question about the same landing: is that width one of the still-open mapping
frames?  The two meet only if every open mapping level of `sc.indents` is a
frame, which is what `IndentStackCover.Covered` says and this item carries
through every scanner step.

**The stack moves in four places and the frames pay at one class of them.**  The
unwind POPS; `[183]`'s `-` opens a SEQUENCE level, which the frames deliberately
do not record; and the three MAPPING pushes are `[187]`'s `?` (at the
indicator's column) and `scanValuePrepare`'s two — the implicit key's column
`[193]`, and the keyless entry's own `:` `[196]`.  So a step is `CoverStep`: the
cover survives, or exactly one mapping level opened, at the top — which is where
item 127 reads the landing from.

**Why the sequence level is exempt, and where that is settled** (§3).  A dedent
landing that rests on a sequence level is `trailing content` when a `:` consumes
it (§8.2.1, `scanValue_top_not_sequence`) and ordinary YAML when a `-` does.
The check lives in the `:`'s own validation, so the refutation is something the
CONSUMER spends, not something the landing carries — item 125's shape.

§1 types the predicate, its transports, its seed and its step.  §2 is the
runtime: the three mapping pushes, each resumed at its own column, and the
sequence level that is not a frame.  §3 is the two ends — the spend and the
refuter — with the discriminating triple.  §4 names the residue this item does
NOT close. -/

namespace L4YAML.Tests.Guards.FramesCoverIndents

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.IndentStackCover L4YAML.Proofs.StreamAccum

/-! ## §1  The predicate, its transports, its seed, and its step -/

/-- The predicate: every mapping level at a non-negative column is a frame. -/
example (ks : List Nat) (s : ScannerState) :
    Covered ks s ↔
      ∀ e ∈ s.indents, e.isSequence = false → 0 ≤ e.column → e.column.toNat ∈ ks :=
  Iff.rfl

/-- The seed: the sentinel alone is covered by any frames, `[]` included. -/
example (input : String) : Covered [] (ScannerState.mk' input) := mk'_cover input []

/-- The step: a `scanNextToken` either keeps the cover, or opens ONE mapping
    level at the top and the frames gain exactly its column. -/
example {ks : List Nat} {s s' : ScannerState} (hok : scanNextToken s = .ok (some s'))
    (h : Covered ks s) :
    Covered ks s' ∨ ∃ c : Nat,
      s'.indents.back? = some { column := (c : Int), isSequence := false } ∧
        Covered (c :: ks) s' :=
  scanNextToken_cover hok h

/-- The four transports: an equal stack, a popped stack, more frames, one more
    frame. -/
example {ks : List Nat} {s s' : ScannerState} (h : Covered ks s)
    (heq : s'.indents = s.indents) : Covered ks s' := h.of_indents_eq heq

example {ks : List Nat} {s s' : ScannerState} (h : Covered ks s)
    (hsub : ∀ e ∈ s'.indents, e ∈ s.indents) : Covered ks s' := h.of_subset hsub

example {ks ks' : List Nat} {s : ScannerState} (h : Covered ks s)
    (hsub : ∀ k ∈ ks, k ∈ ks') : Covered ks' s := h.mono hsub

example {ks : List Nat} {s : ScannerState} (c : Nat) (h : Covered ks s) :
    Covered (c :: ks) s := h.cons c

/-- The writers: the unwind pops, `[183]` is exempt, `[187]` is the payment. -/
example {ks : List Nat} {s : ScannerState} (col : Int) (h : Covered ks s) :
    Covered ks (unwindIndents s col) := unwindIndents_cover col h

example {ks : List Nat} {s : ScannerState} (col : Int) (h : Covered ks s) :
    Covered ks (pushSequenceIndent s col) := pushSequenceIndent_cover col h

example {ks : List Nat} {s : ScannerState} (c : Nat) (h : Covered ks s) :
    Covered (c :: ks) (pushMappingIndent s (c : Int)) := pushMappingIndent_cover c h

/-! ## §2  The three mapping pushes on the runtime -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) && refuses input

/-- Both scanners accept: the input is not the refusal's family. -/
private def scansClean (input : String) : Bool :=
  match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
  | .ok _, .ok _ => true
  | _, _ => false

-- (a) Each mapping push, resumed at its own column by a later sibling: the
-- implicit key `[193]`, the explicit `?` `[187]`, and the keyless `:` `[196]`.
#guard accepts "a:\n  b:\n    x: 1\n  c: 2\n"
#guard accepts "a:\n  ? b\n  : c\n  d: 1\n"
#guard accepts "a:\n  : v\n  b: 1\n"

-- (b) …and the sequence level, which is NOT a frame: the same landing column
-- resumes for a `-` entry and is `trailing content` for a `:`.
#guard accepts "a:\n  - x\n  - y\n"
#guard scannerRefuses "a:\n  - x\n  b: 2\n"

/-! ## §3  The two ends -/

/-- **The spend.**  With the cover on the park's state, item 127's equation
    reads as MEMBERSHIP — which is what `ResumeFrames.resumeAt` asks — unless
    the landing rests on a sequence level. -/
example {sc s_prep : ScannerState} {c : Char} {ks : List Nat}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_pop : s_prep.indents ≠ sc.indents)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_cov : Covered ks sc) :
    s_prep.col ∈ ks ∨
      ∃ e, s_prep.indents.back? = some e ∧ e.isSequence = true ∧
        e.column = (s_prep.col : Int) :=
  preprocess_landing_mem_or_seq hok h_pop h_base h_cov

/-- **The refuter.**  A `:` that validates at the landing's column has a mapping
    level under it, so the landing is a frame outright. -/
example {ks : List Nat} {s : ScannerState} {top : IndentEntry}
    (hok : scanValueValidate s = .ok ())
    (h_poss : s.simpleKey.possible = true) (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.simpleKey.pos.col : Int) = top.column)
    (h_le : (s.simpleKey.pos.col : Int) ≤ s.currentIndent)
    (h_cov : Covered ks s) :
    s.simpleKey.pos.col ∈ ks :=
  landing_mem_of_value hok h_poss h_noflow h_top h_at h_le h_cov

-- The discriminating triple, on ONE landing column, with a POP under it (the
-- spend's own `h_pop`): the popping landing rests on a mapping level and
-- resumes; rests on a sequence level and is refused by the `:`; rests on the
-- same sequence level and resumes for a `-`.
#guard accepts "a:\n  b:\n    x: 1\n  c: 2\n"
#guard scannerRefuses "a:\n  - b:\n      x: 1\n  c: 2\n"
#guard accepts "a:\n  - b:\n      x: 1\n  - c: 2\n"

-- …and the same three at the shallower depth where nothing pops, which is where
-- §8.2.1's check alone carries the refusal.
#guard accepts "- a: 1\n  b: 2\n"
#guard scannerRefuses "a:\n  - x\n  : c\n"
#guard emits "a:\n  - x\n  - y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :x", "=VAL :y", "-SEQ",
   "-MAP", "-DOC", "-STR"]

/-! ## §4  The residue this item does NOT close

`scanValue_top_not_sequence` is stated at the `:`'s own validation, and that is
the only consumer running the check: the `?` reaches `pushMappingIndent` with no
§8.2.1 test in front of it.  So a popping landing that rests on a SEQUENCE level
and is consumed by an EXPLICIT key is accepted by both scanners, and the pair
below isolates what that costs — the same input with the landing on a MAPPING
level emits one document, and on a sequence level the stream closes its document
and opens a second one.  Named here, measured, and left for the item that
threads the cover through the accumulation. -/

#guard scansClean "a:\n  - b:\n      x: 1\n  ? c\n  : 2\n"
#guard emits "a:\n  b:\n    x: 1\n  ? c\n  : 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+MAP", "=VAL :x",
   "=VAL :1", "-MAP", "=VAL :c", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "a:\n  - b:\n      x: 1\n  ? c\n  : 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "+MAP", "=VAL :b", "+MAP",
   "=VAL :x", "=VAL :1", "-MAP", "-MAP", "-SEQ", "=VAL :c", "=VAL :2", "-MAP",
   "-DOC", "+DOC", "=VAL :", "-DOC", "-STR"]

end L4YAML.Tests.Guards.FramesCoverIndents
