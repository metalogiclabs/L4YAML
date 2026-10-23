# `eventsOf` — concept note for Step 5a(iii)

Status: proposal, 2026-10-23; §7 item 1 landed the same day as `EventsOf.lean`
(defaults of §6 taken).  §6 lists the decisions it asks for.  Defaults are stated so that work can start if no
objection is raised.

## 1. The obligation

The corrected capstone 7.7 is

```lean
theorem parse_iff_grammar (input : String) :
    (∃ docs, parseYaml input = .ok docs)
      ↔ ExactSurfaceLanguage input ∧ SerializationWellFormed input
```

`SerializationWellFormed` exists today over a **trace** (`List Event`,
`SerializationWellFormed.lean`), not over the input.  Step 5a(iii) owes the
connection `eventsOf : String → List Event`, so that the capstone's second
conjunct reads `SerializationWellFormed (eventsOf input)`.  Three constraints
on it are already on record:

- **N1, non-circular.**  No call into `Scanner`, `IndexedScanner`,
  `TokenParser` or `compose`.  The right-hand side of the capstone must mean
  something without the left-hand side (package README, "what is not proved").
- **N2, exact.**  `*`, `&`, `!`, `%TAG`, `---` and `...` inside a quoted
  scalar, a comment, a block-scalar body or the interior of a plain scalar are
  not events (DOCS.md, 5a(iii): "the extraction is not independent of the
  surface work").
- **N3, two-way.**  The forward direction must *produce* the trace of an
  accepted input; the converse must *consume* a well-formed trace while
  rebuilding a scanner/parser run from an exact derivation.

## 2. A function over derivations is not available

Every surface relation is `SurfPos → SurfPos → Prop`.  A derivation of
`SLYamlStream sp sp'` lives in `Prop`, so Lean cannot eliminate it into a
`List Event`: "`eventsOf` over the exact surface derivation" cannot be a
function of the derivation.  The honest shapes are:

| | shape | price | what it buys |
|---|---|---|---|
| A | event-annotated grammar `SLYamlStreamE : SurfPos → SurfPos → List Event → Prop`, one twin per production | ~50 productions duplicated, two grammars kept in step forever | nothing B does not |
| B | a **lexical skeleton** relation `Skeleton : String → List Seg → Prop` plus an executable `eventsOfSegs : List Seg → List Event` | one new inductive over *segments*, reusing the existing surface relations as its side conditions | the trace is a function of a witness that is a plain list |
| C | fold the skeleton into `ExactSurfaceLanguage` itself (`∃ segs, ExactDerivation input segs`) | ties 5a(ii) and 5a(iii) into one definition | removes one ∃ at the cost of coupling the two open steps |
| D | an executable **reference lexer** `refLex : String → Option (List Seg)` beside B, with `refLex_sound` / `refLex_complete` against `Skeleton` | ~600 lines of spec-shaped code + two proofs | `eventsOf` becomes the function the plan names, and the capstone's right-hand side becomes **decidable** |

Proposal: **B as the specification, D as its executable twin.**  A is rejected
for its N×N price; C is rejected because 5a(ii) is row 19's work under another
name and must stay separable.

## 3. The skeleton (B)

```lean
inductive Seg where
  | anchor   (name : String)      -- `&name`, SCNsAnchorProperty
  | alias    (name : String)      -- `*name`, SCNsAliasNode
  | tagUse   (handle : String)    -- `!h!suffix`, SCNsTagProperty.named; `!suffix` and `!!suffix` carry the builtin handles
  | tagDecl  (handle : String)    -- `%TAG !h! prefix`, the narrowed SLDirective of 5a(ii)
  | docStart (directives : List Seg.Directive)   -- the directive group and its `---` (SLDirectiveDocument); `[]` for a bare `---`
  | docEnd                        -- `...`, SCDocumentEnd
  | opaque   (chars : List Char)  -- a quoted scalar, a comment, a block-scalar body, a plain-scalar interior
  | other    (chars : List Char)  -- indicators, whitespace, breaks, indentation, everything else

def eventsOfSegs : List Seg → List Event   -- anchor ↦ defineAnchor, alias ↦ useAlias, tagUse ↦ useTag, docEnd ↦ endDocument; opaque/other ↦ nothing
                                           -- docStart ds ↦ beginDocument :: (ds.filterMap tagDecl).map declareTag
```

A `%TAG` directive precedes its document's `---` lexically but belongs to that
document semantically: `WellFormedFrom` resets `Env.tagHandles` on
`beginDocument`, so emitting `declareTag` at the directive's own position would
be wiped before the first `useTag` (`%TAG !h! tag:example.com,2026:⏎--- !h!item
value` must be well-formed).  The directive group is therefore part of the
`docStart` segment and its declarations are emitted **after** `beginDocument`,
matching the order `RuntimeScopes.documentEvents` already fixes and proves
necessary.  `tagDecl` is consequently not a top-level `Seg` constructor.  Probe
set for this corner: two successive directive documents, a bare document after
`...`, a `%TAG` with no `---` (refused by `ExactSurfaceLanguage`, not by the
trace).

`Skeleton input segs` says: the segments concatenate to `input.toList`, no two
`other` segments are adjacent and no `other` segment is empty (so the
partition of non-event text is canonical: maximal runs), each
event segment is derivable by its surface relation **at the column the
concatenation puts it at**, each `opaque` segment is derivable by one of
`SCDoubleQuoted`, `SCSingleQuoted`, `SLComment`/`SCNbCommentText`,
`SCLLiteral`/`SCLFolded`'s body relations or a plain-scalar interior, and no
event lexeme starts inside an `other` segment.  The name/handle carried by an
event segment is the one the source recognisers in `SourceEvents.lean`
already read (`anchorEventAt`, `namedTagUseAt`, `namedTagDeclarationAt`),
whose exactness against the surface relations is proved there
(`alias_use_source_exact`, `named_tag_use_source_exact`, …) — those lemmas
become the side conditions of `Skeleton`'s constructors rather than theorems
about it.

Then

```lean
def SerializationWellFormedInput (input : String) : Prop :=
  ∃ segs, Skeleton input segs ∧ SerializationWellFormed (eventsOfSegs segs)
```

and the capstone's second conjunct is this predicate (renamed to
`SerializationWellFormed input` once the trace-level one is namespaced).

## 4. The uniqueness lemma is on the path whatever the quantifier

Forward direction (`parseYaml ok → ∃ segs, …`): the scanner's own token array
is a skeleton — `skeleton_of_scan : scanFiltered input = .ok ts →
Skeleton input (segsOfTokens ts)` — and its trace is well-formed by the two
guard bridges already proved (`scanner_alias_guard_exact`,
`parser_tag_guard_exact`, `SourceEvents.lean` §"Composition").  No uniqueness
needed.

Converse (`ExactSurfaceLanguage ∧ ∃ segs, … → parseYaml ok`): the converse
proof rebuilds the scanner run from the exact derivation, whose skeleton is
`segs'`; the well-formedness hypothesis is about some `segs`.  Closing the gap
needs

```lean
lemma skeleton_unique :
    Skeleton input segs → Skeleton input segs' → eventsOfSegs segs = eventsOfSegs segs'
```

— stated on the **trace**, which is what the converse consumes, not on the
segment lists: even with canonical `other` runs, two skeletons may still differ
in how they split an `opaque` region (a quoted scalar is one segment, a comment
another, but the grammar does not fix the boundary between a plain scalar's
interior and the whitespace after it), and list equality would then be false
for a reason the trace does not care about.  The content of the lemma is
*the exact surface grammar is lexically unambiguous about where its event
lexemes are* — and it is needed
under `∀` too (then the forward direction needs it instead).  This is a real
theorem about YAML 1.2.2 as narrowed by 5a(ii); it is **false** today for
`InYamlLanguage` (`scannerDrop` derives everything) and becomes provable only
after Row 12 and row 19 land.  D's `refLex_complete` *is* this lemma in
executable clothing, which is the second reason to build D: the uniqueness
proof is a determinism proof about a total function on `List Char`, not an
induction over two derivations.

## 5. Decisions already taken elsewhere that this inherits

- **Anchor timing.**  `AnchorTiming.lean` separates the normative commit (at
  node start, YAML §3.2.2.2) from L4YAML's current commit (at node
  completion).  `eventsOfSegs` emits `defineAnchor` at the `&` lexeme, i.e.
  **normative**; `&x [*x]` is well-formed.  This agrees with 5a(iv)'s runtime
  repair (in progress) and disagrees with the base-branch parser until it
  lands — the forward direction is stated against the repaired parser.
- **Document scope.**  `Env.reset` fires on `beginDocument` and `endDocument`
  only, i.e. on explicit `---` / `...`.  A bare document has no event of its
  own; two bare documents cannot be adjacent without a marker, so no anchor
  leaks between documents without a reset.
- **Scope of `SerializationWellFormed`.**  Exactly the two state-dependent
  rejection families of `ErrorCensus.lean` (`undefinedAlias`,
  `undeclaredTagHandle`).  `duplicateYamlDirective`, `directiveAfterContent`,
  `directiveWithoutDocument`, `directiveTrailingContent`, `invalidBareDocument`
  stay in `ExactSurfaceLanguage` (5a(ii)'s worklist), where they are shape,
  not state.

## 6. Open questions (defaults in bold)

1. Quantifier in `SerializationWellFormedInput`: **`∃ segs`** (forward
   direction free; `skeleton_unique` paid by the converse) or `∀ segs`?
2. Build D (`refLex`) now, beside B? **Yes** — it makes the capstone's
   right-hand side decidable, so the whole statement can be censused against
   the yaml-test-suite and `Tests/` corpora with `#guard` before any proof is
   attempted (Rule 2 at the capstone level), and it carries `skeleton_unique`.
3. `Seg.tagUse` for the builtin handles `!` and `!!`: emit `useTag "!"` /
   `useTag "!!"` (always allowed, `BuiltinTagHandle`) or no event? **Emit** —
   it keeps `eventsOfSegs` a homomorphism and `TagHandleAllowed` already
   admits them.
4. The verbatim tag `!<…>` and the tag suffix/URI characters: `opaque`
   (**default**) or a dedicated segment?
5. Anchor names may contain `*` and `!` (`ns-anchor-char` excludes only flow
   indicators and white space), and plain scalars may contain `&`, `*`, `!`
   after their first character.  Those are N2's hard cases; `Skeleton`'s
   `other`/`opaque` conditions must say that an event lexeme is recognised
   only at a node-property / node-start position.  **Carry a `Ctx` argument
   (block/flow, after-indicator) in the skeleton**, mirroring the scanner's
   dispatch, or reject the input shape?  Default: carry it.
6. Positions: should segments carry a `(line, col)` for later correspondence
   with the parser's error positions?  **No** for 7.7; columns are recomputed
   from the concatenation.
7. Module placement: `L4YAML/Proofs/Serialization/EventsOf.lean` (B) and
   `RefLex.lean` (D), both `module`, both in the serialization package's
   closure, moving the three closure-census pins once each.  **Yes.**

## 7. What lands first

1. `EventsOf.lean`: `Seg`, `Skeleton`, `eventsOfSegs`,
   `SerializationWellFormedInput`, the `Skeleton` constructors' side
   conditions discharged by `SourceEvents.lean`'s exactness lemmas, and ≥ 30
   Rule-2 instantiations (`&x [*x]`, `"&x"`, `# *x`, `a*b`, `&a*b`, `|⏎ *x`,
   `--- &x 1⏎--- *x`, `a: &x 1⏎...⏎b: *x`, `!h!x` with and without `%TAG`).
2. `RefLex.lean`: the lexer, `refLex_sound`, `refLex_canonical` (its output
   satisfies the maximal-run condition), the `#guard` census of
   `(refLex input).map eventsOfSegs` against `parseYaml`'s verdict on the two
   corpora (every disagreement recorded, none papered over).
3. `skeleton_of_scan` (forward half of N3), then `refLex_complete` — stated as
   `Skeleton input segs → ∃ segs', refLex input = some segs' ∧ eventsOfSegs segs' = eventsOfSegs segs`,
   which is `skeleton_unique` in executable clothing — after Row 12 / row 19.

## 8. `refLex_sound` — proof plan (slice 3)

Target: `refLex input = some segs → Skeleton 0 input.toList segs`.  The
decidable side conditions of `SegAt`/`Skeleton` are pinned on a 58-input grid
in `Tests/Guards/Proofs/RefLexShape.lean` (its first run refuted the directive
arm; see that file's header).  What remains is the `Prop` half, arm by arm:

| `Seg` arm | `SegAt` obligation | discharged by |
|---|---|---|
| `anchor`/`alias` | `PendingAnchorWitness`/`AliasEventWitness` + `Maximal` | `SourceEvents` bridge `isAnchorCharBool c = true ↔ isNsAnchorChar c` (`SourceEvents.lean:247`) lifted over `spanWhile`; `Maximal` is the span's stop condition |
| `tagUse` | `SCNsTagProperty` + `handleOf` + `Maximal` | the three `SCNsTagProperty` constructors (verbatim / shorthand / non-specific) over the maximal `isTagCharBool` run |
| `docStart`/`docEnd` | `SCDirectivesEnd`/`SCDocumentEnd` at col 0, `SLDirective` per directive line | constructors are literal; `SLDirective` needs `[79] s-l-comments` for the absorbed blank/comment lines, which `commentLines` consumes exactly |
| `other` | `chars ≠ [] ∧ noEventLexeme` | the arm's own guard; the `flush` discipline gives non-adjacency |
| `opaque` | `OpaqueAt` = full `SCDoubleQuoted`/`SCSingleQuoted`/`SLComment`/`SCLLiteral`/`SCLFolded`/`SNsPlain*` | **open — see below** |

### The `opaque` arm decides the shape of slice 3

`OpaqueAt` demands the real surface scalar relations, not a lexical
approximation.  Proving them for `RefLex`'s private `quoted`/`blockBody`/`plain`
would re-derive the leaf production lemmas that already exist for the scanner's
own functions: `scanDoubleQuoted_prod`, `scanSingleQuoted_prod`,
`scanBlockScalar_prod` (`ScalarProduction.lean`) each conclude
`∃ sp', ⟨relation⟩ sp sp' ∧ ScannerSurfCorr s' sp'` from `ScannerSurfCorr sc sp`
and `scanX sc = .ok s'`.

Decision (default, per §6's rule): **re-base `refLex` on byte offsets over the
original `String` and let the `opaque` arms call the scanner leaf functions on a
positioned `ScannerState`** (`{ ScannerState.mk' input with offset, col }`;
`ScannerSurfCorr` holds by `initial_corr`'s argument shifted to the suffix).
Then `OpaqueAt` is the `*_prod` conclusion and `refLex_sound` reduces to a loop
invariant `ScannerSurfCorr sc ⟨rest, col⟩ → Skeleton col rest (loop …)`.

This does not make the capstone circular: `Skeleton`, `eventsOfSegs` and
`SerializationWellFormedInput` stay independent of `Scanner`; only the executable
witness-finder reuses scanner code, and its soundness is to the independent
relation.  Cost: the `RefLex.lean` rewrite (after #57 lands, not on it) and a
re-run of the two censuses, which must not move.

Rejected: (a) widen `OpaqueAt` to a lexical span — would make
`SerializationWellFormedInput` true on inputs with no surface derivation (the
false-theorem direction); (b) prove `OpaqueAt` for the private lexers — the
double-quoted body alone (`[106]`–`[110]`, escapes, folding) is the largest
single proof in `ScalarProduction.lean`.

Open: the leaf functions read `sc.indents` (block-scalar floor) and `inFlow`;
the positioned state carries the sentinel stack, so `scanBlockScalar` runs at
floor −1.  The census must show this agrees with `parseYaml` on `- |⏎x` and
`a: |⏎  x⏎b: y` before the plan is executed.

Measured (scratch, positioned `ScannerState` with the sentinel stack only):
`scanBlockScalar` on `a: |⏎  x⏎b: y` stops at offset 9 (before `b`) and on
`- |⏎  x⏎- y` at 8 — both as the real scanner does — but on `- |⏎x⏎` it
consumes the whole input (offset 6) while `parseYaml` refuses it: at floor −1
a column-0 line is body, at the real floor 0 it is not.  So slice 3 must give
the positioned state the enclosing block indent (the `-`/`:` column `refLex`
already walks past), not the bare sentinel; `- |⏎x` and `- |⏎*x` go into the
census either way.

## 9. Correction to §8: `refLex` is not on the capstone's path

Writing the §8 rewrite exposed two facts that change the plan.

1. `scanPlainScalar_prod` (and its flow twin `scanPlainScalar_to_flowNode_flowIn`)
   conclude `SNsPlain … sp sp_gram ∧ GStar SSWhite sp_gram sp' ∧ ScannerSurfCorr s' sp'`:
   the scanner consumes trailing white that the grammar span excludes, and
   `sp_gram` is not an executable output.  No executable lexer, private or
   scanner-backed, can emit an `opaque` segment whose text is exactly the
   plain scalar's grammar span.
2. The forward surface capstone already exists: `parse_strict_proof`
   (`DocumentProduction.lean`) gets `InYamlLanguage input` from
   `scanLoop_grammar_prod`, i.e. every successful scan already carries a
   surface derivation per token (`*_prod` lemma per token kind).

Consequence: `SerializationWellFormedInput` is an `∃ segs`, so the capstone's
**forward** serialization conjunct needs a *witness*, not a *decision
procedure* — and the witness can be built in the proof from the `*_prod`
conclusions (using `sp_gram`, which the proof has even though no program does).
The **backward** direction needs trace uniqueness (§4) plus "the parser's
alias/tag checks compute `checkFrom` over the same trace", neither of which
mentions `refLex`.  `refLex` therefore stays what slice 2 made it: the census
instrument that keeps `SerializationWellFormedInput` honest against
`parseYaml`.  The §8 rewrite is dropped; the two divergence rows pinned in
`RefLexCensus.lean` are census debt, not proof debt.

### The path, restated

| # | lemma | file | depends on |
|---|---|---|---|
| S1 | `OpaqueAt` admits trailing white: `R sp sp_mid ∧ GStar SSWhite sp_mid sp'` (trailing white carries no event lexeme) | `EventsOf.lean` | — |
| S2 | `tokenEvents : Array (Positioned YamlToken) → List Event` — `.anchor`/`.alias`/`.tag`/`.documentStart`(+directives)/`.documentEnd` in stream order; executable, no `Prop` | new `TokenEvents.lean` | — |
| S3 | `scan_skeleton : scan input = .ok tokens → ∃ segs, Skeleton 0 input.toList segs ∧ eventsOfSegs segs = tokenEvents tokens` | new module | per-token `*_prod` lemmas; a loop invariant over `scanLoop` |
| S4 | `skeleton_trace_unique : Skeleton 0 cs segs₁ → Skeleton 0 cs segs₂ → eventsOfSegs segs₁ = eventsOfSegs segs₂` | `EventsOf.lean` | `Maximal`, canonical `other` runs, `OpaqueAt` spans determined by their first char |
| S5 | `parse_ok_checkFrom : parseYaml input = .ok docs → checkFrom {} (tokenEvents tokens) = true` and its converse under `InYamlLanguage` | parser proofs | `ParseState.declareAnchor`/`declaredIndex`, `RuntimeScopes.documentEvents` |

Forward conjunct = S3 + S5(→) + `checkFrom` ↔ `WellFormedFrom`.
Backward = S4 + S5(←) + the surface direction.

### Open questions (defaults in bold)

1. S3's loop invariant rides `scanLoop`, whose grammar invariant lives in
   `StreamAccum.lean` (Row 12's file).  **Default: a separate module with its
   own induction over `scanLoop`, importing StreamAccum's per-step `*_prod`
   lemmas and not editing it**; if the per-step lemmas do not expose the token
   just pushed, the alternative is one extra conjunct in Row 12's invariant,
   negotiated with that stream after item 344.
2. Trailing white (S1): relax `OpaqueAt`, **or** let the skeleton emit the
   white as an `other` run.  **Default: relax `OpaqueAt`** — one `GStar SSWhite`
   conjunct, no change to `Skeleton`, no change to the census (white has no
   event lexeme either way).
3. S4 needs `opaque` spans to be determined by their opening character and
   position (a `"` opens exactly one double-quoted span, a `#` one comment,
   …).  Plain scalars break this unless their span is pinned: **default: S4 is
   stated on traces, and the plain disjunct contributes no events whatever its
   span**, so the proof only needs "no event lexeme starts inside any admissible
   plain span", which `noEventLexeme`'s node-start discipline gives.
4. Does `refLex` keep a role?  **Default: census only** (slice 2 as merged plus
   the pinned divergence rows); no `refLex_sound`.

### Order

S1 (small), S2 (small, with a census column `tokenEvents tokens =? eventsOf input`
on the agreeing rows), S4 (the hard pure lemma, independent of everything
else), then S3 and S5 once question 1 is settled.
