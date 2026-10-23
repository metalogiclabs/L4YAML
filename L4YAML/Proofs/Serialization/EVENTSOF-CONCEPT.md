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
