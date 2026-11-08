# Group 7.7 closure contract and critical path

Status: UNKNOWN. This is the execution contract, not a completion certificate.
Source boundary: frozen production 64795a8db28ccfdae85082c93b6453001ae9d3e4.
Governing requirement: Blueprint/04-capstones.md Group 7.7 and
Proofs/Serialization/EVENTSOF-CONCEPT.md sections 1–3. The original unrestricted
converse is REJECTED by CapstoneObstructions.original_converse_refuted.

## Required terminal claims

For the actual TokenParser.parseYaml entry point and a single independently
specified YAML 1.2.2 source language L, prove both:

* L input -> exists docs, parseYaml input = .ok docs.
* (exists docs, parseYaml input = .ok docs) -> L input.

L must incorporate source-connected syntax and serialization validity. It must
not call production scanner/parser acceptance or merely assume token validity.
No unsupported-input restriction may be silently added. Existing output and
round-trip capstones remain protected; this acceptance iff does not establish
exact output semantics. Any output claim requires its own independently stated
relation and theorem, rather than being inferred from this iff.

## Coverage and existing work

source-bridge-map.json now pins every declaration/constructor in the six current
Surface files, and every ScannerState field. coverage-audit.py checks source
identity and the textual census. CoverageInventory.lean independently checks the
82 relation names and 186 constructor names against the compiled environment.
This is exhaustive for that source boundary, NOT a census of normative YAML
requirements. The older DOCS.md count of 77 relations is historical.

Reuse the existing constructor-family map in source-bridge-map.json. Every
listed constructor inherits its family's OPEN full-source correspondence status;
none becomes complete merely because it is enumerated. QuotedSource is a
separately checked restricted instance, not a discharge of every original
quoted constructor. ScannerState fields are implementation inventory, not fields
that should be copied wholesale into an independent specification.

The existing DOCS.md grammar-completeness plan, Blueprint Group 7 dependency
analysis, and Tests/Guards/Proofs/{DropDependents,RepairChoice,ProducerDerivation,
DispatchPrice,ParkGapCensus}.lean already price the scannerDrop repair. Do not
repeat those experiments without source drift. StreamAccum is a forward
accumulator; its existence does not supply the reverse source producer.

## Dependency order and decisive exits

1. **Normative coverage and exact language (OPEN).** Map all source relations,
   character classes, context restrictions and state requirements to governing
   productions. Replace broad leaves, disconnected scannerDrop and invalid
   implicit continuation. Retain directive multiplicity and legal anchor rebinding.
   Exit: an independent full-language definition and audited requirement map.
2. **Source-connected state composition (OPEN).** Reuse EventsOf/TraceOf and
   serialization components where their hypotheses fit the corrected language.
   Preserve source extents, directive records and per-document reset order before
   event erasure. Keep grammar state independent of implementation registers.
   Exit: composition lemmas that derive actual reachable scanner premises.
3. **Producer (OPEN).** Prove SourceBridge.Obligation L by grammar construction,
   including nested collections, key lookahead/indentation, scalar boundaries,
   EOF and the production fuel bound. Existing accepts_of_producer closes the
   parser composition once this is supplied. Exit: unconditional producer for L.
4. **Same-language strictness (OPEN).** Reprove acceptance -> L. Old proofs into
   universal InYamlLanguage cannot transfer. Frozen raw-SOH comment acceptance
   already refutes normative iff. The separate normative-comments candidate has
   passing finite controls but a failing full proof build. Duplicate TAG handling
   also needs reconciliation. Exit: qualified implementation repair plus theorem.
5. **Qualification (OPEN).** Exact theorem-type consumers, transitive axiom gate,
   full unchanged native positive/negative regressions, dependency/source pins,
   source-qualified CI artifact and independent specification audit. Exit: all
   prior claims qualified on the SAME source, with no placeholders or hidden
   assumptions. A green restricted harness does not meet this exit.

## Cornerstone and mandatory work selection

The governing target is ONE source language L and ONE qualified implementation
revision R, with completeness and strictness proved for exactly that pair.
L is a source-only mathematical judgment, not a name for runtime acceptance.
Its accepted inputs must be justified by the governing requirements; narrowing
it to convenient fragments or broadening it to permissive runtime behavior is
not a repair. The original refuted language is not the target. The frozen
production revision cannot satisfy normative strictness; it remains a reusable
historical evidence boundary, not a mandatory final implementation.

The required theorem schema is fixed above. The concrete full definition of L
is NOT yet fixed or qualified. Writing this contract does not fill that gap.
The next mandatory deliverable is L4-EXACT-GRAMMAR: the complete independent
Lean language definition plus a requirement-to-definition map, including all
unresolved scope decisions. No full-language milestone is earned until that
map has no unexplained omissions and the definition is independently audited.
Do not silently choose an implementation limitation as an exclusion from YAML.
Any explicit supported-profile boundary must have governing evidence and appear
in the theorem scope; unresolved boundaries remain UNKNOWN.

The definition must retain original source consumption, lexical/Unicode
constraints, context-sensitive node and document structure, explicit directive
records and document-local multiplicity, anchor/tag scope, and reset order.
Reuse existing definitions only after checking their meaning and hypotheses.
Known separating witnesses for scannerDrop, bare continuation, raw controls,
directive multiplicity, aliases and tag scope are specification audit inputs.
Existing event erasure is insufficient for directive multiplicity. Existing
constructor census is insufficient for normative coverage.

Before each code experiment, record in obligations.json:

1. The exact governing obligation and definition/constructor it will discharge,
   or the competing diagnoses its counterexample will distinguish.
2. The decisive result and its verification boundary.
3. Which terminal claim becomes possible if it succeeds.

Until L4-EXACT-GRAMMAR is discharged, prioritize specification construction and
separating witnesses. Fragment extensions are deferred unless they are needed
to decide a named specification ambiguity; record that dependency first.
Afterwards select only work on the five closure exits above. A new example,
lemma, green run or conditional generic interface earns no full-language
coverage by itself. Preserve reusable fragments without relabeling them as
universal coverage. Do not report a completion percentage from their count.

## Active next experiment and supersession

Construct and audit the full independent language, beginning by reconciling the
governing Group 7.7 requirements and supported-source boundary against the
existing six Surface files and known counterexamples. Produce the concrete
Lean definition and requirement map, not another parameterized acceptance
interface. Missing or disputed productions must be named UNKNOWNs rather than
filled with scannerDrop, acceptance predicates, or unproved coverage claims.

Directive-block induction is DEFERRED_PENDING_EXACT_LANGUAGE. The previously
queued source-record, TAG dispatch, marker and quoted-body work is preserved:
DirectiveRecords proves the event-erasure obstruction; DirectiveRecordBridge,
TagDocument, QuotedContinuation and TagQuotedParse provide qualified components.
The latest fragment proves public acceptance of one TAG directive, an explicit
marker, and an independently grammatical quoted body. None fixes the full L.
Resume induction only when its source relation is part of the audited target,
or when a recorded separating experiment is necessary to settle that target.

## Commands and stop rule

`python3 research/whole-source/coverage-audit.py` checks inventory drift.
`bash research/whole-source/qualify-capstone.sh DIR` checks the bounded proof chain.
`python3 research/whole-source/coverage-audit.py --closure` currently exits 2,
explicitly UNKNOWN. This is a blocking diagnostic, not an implemented final
semantic verifier: it cannot be promoted by setting a status flag. Replace that
diagnostic only with a separately reviewed, typed full-language proof consumer
and complete qualification. A false original theorem closes a diagnosis, not the
project. No current result permits declaring Capstone complete.

## Requirement map checkpoint

The existing source-bridge-map.json now contains requirement_map: an index of
all 211 numbered YAML 1.2.2 productions, 17 candidate definition families and 11
cross-cutting obligations, each with a reuse/repair/missing/rejected action.
The normative Markdown is pinned by Git blob and SHA256; the audit checks exact
production names when supplied that file, family ownership, definition leads,
and local source hashes. These are integrity checks, not semantic adequacy.

Progress: cornerstone fixed; reuse candidates identified; complete numbered
production index built; family semantic audit and concrete exact Lean language
still OPEN. Cell/Lean evidence integration remains NOT STARTED. Existing parser
and fragment receipts retain their original scopes.

LOAD-LAYERS scope resolved below; this does not establish conformance. Next construction
order: exact lexical leaves, then mutually recursive exact nodes, then exact
documents/streams. A repaired stream wrapper around old broad scalar/node
children is already insufficient. The existing lexical Skeleton remains useful
for source/event alignment but is not a replacement for structural syntax.

## Acceptance boundary decision

Group 7 and EVENTSOF-CONCEPT section 1 govern syntax/serialization acceptance,
including aliases, tag-handle availability, directive validity and document
scope. YAML 3.3 separately distinguishes complete representation, tag resolution,
recognized/valid content, key equality and native construction. Those requirements
remain protected separate claims; Group 7.7 must not be advertised as all loading
correctness. No source-syntax fragment has been excluded by this decision.

At the actual API, parseYaml maps total compose over parseYamlRaw success;
Schema.Api.parseAs separately adds type conversion and SchemaError. The qualified
AcceptanceScope theorems state exact acceptance equivalence and the mapped-output
relationship. Controls distinguish accepted invalid integer content/duplicate
plain keys from rejected unavailable aliases/tag handles. Both types and standard-only axiom profiles were inspected at code
ff9e921c66a9e95bfa61e54361072a86595c92f1, run 42437972498, job 128600834976
SUCCESS. All four native controls and retained qualification passed; full production
job was skipped. Artifact 13600835573; SHA256
b4cca1f04e5264f98944778c6a98f5ee8270d471bb58e470cfa901e7fb2dbe41.
Earlier 5fc820b5/run 42437804329 failed control meta visibility despite compiled
theorems; corrected the import without changing claims.

Next construction: independent lexical leaves must distinguish c-printable from
nb-json (YAML 5.1 explicitly permits non-C0 characters in quoted scalars for JSON
compatibility). A blanket printable-only filter would wrongly narrow the language.
Then propagate leaves through mutually recursive nodes and exact streams; preserve
original source records and prove trace coherence. Full language is NOT CONSTRUCTED.

Lexical audit lead: Spec/CharPredicates.isPrintableProp currently omits LF and CR
although annotated as production [1]. This is not yet a runtime defect: Surface
isNbChar removes breaks anyway. An exact [1] definition must include both; prove
reuse at the non-break consumer boundary instead of importing the misleading
whole-production name. DQCharOk/SQCharOk already use nb-json and are candidate
leaves, not automatically full normative scalar grammars.

## Exact character layer

ExactCharacters.lean defines [1] CPrintable, [2] NbJson, [27] NbChar and [34]
NsChar directly from the pinned normative ranges. The intended reuse boundary is
universal equivalence: CPrintable repairs the omitted LF/CR cases, while NbChar
and NsChar equal the existing non-break/non-space predicates. This avoids a
production edit and preserves the correct consumers rather than globally
changing their character class.

Eleven boundary checks cover LF/CR, DEL, C1, NEL, raw SOH, BOM, noncharacters,
Unicode range endpoints and tab. Two formal separating witnesses exercise the
requirements directly: permissive comments admit SOH, whereas a blanket printable
restriction wrongly excludes DEL from quoted nb-json. They qualify the new
character layer, not a fresh discovery of the already-known comment defect.

The complete independent language is still NOT CONSTRUCTED. Next, carry these
classes into exact comment and quoted-character relations, with normative escape
value constraints and doubled-quote handling; then propagate those relations
through recursive nodes. No new bounded parser-acceptance family is needed for
that construction. Do not infer full quoted syntax from nb-json alone.

Qualified code e1e00c3f67d254ba36322a6000b77aa475ce44b7, Actions 42446253551,
job 128625694475 SUCCESS, artifact 13603746574, reported SHA256
c139ec15c5b3081b5c1dca5f9d1f554710df9747c70024c3674af55640fde01d.
Four universal equivalences use standard axioms only; both separating witnesses
are axiom-free. All lexical guards, unchanged native controls, expected RED,
inventory and frozen source guards passed. Full production job skipped.
Failed 49837912/run 42446110859 preserved: proof equivalences compiled, but
control evaluator visibility/Unicode notation/decidability errors caused rejection.
No theorem statement was weakened to repair the candidate.

## Lexical propagation

ExactLexical.lean is a source-only definition module, importing ExactCharacters
and no scanner/parser acceptance module. It supplies CommentText, DoubleChar,
SingleChar and arbitrary DoubleBody/SingleBody runs. Named escapes are an explicit
source alphabet. Hex escapes require their exact digit counts and a Unicode
scalar value, keeping valid escaped controls distinct from invalid raw controls.

ExactLexicalBridge.lean separately proves equivalence of quoted characters and
arbitrary body runs with DQCharOk/SQCharOk. The existing scanner proofs can thereby
be reused at this leaf interface. Strict comments embed into the old comment
relation; a converse is neither claimed nor appropriate. This does NOT yet cover
complete quoted scalars, multiline folding, implicit-key restrictions, indentation,
closing-quote lookahead, or recursive node contexts.

Next: define full context-indexed double/single quoted syntax from normative
productions 108–116 and 119–125 using these leaves, auditing multiline whitespace,
folding and implicit-key restrictions. Do not wrap the old broad node grammar or
infer full scalar coverage from the body equivalences. Keep comment/separation
propagation and runtime comment repair as separately named remaining obligations.

Qualified code 58ea915b2fb85a1c31ffa67eae8d27ba969c00a3, Actions 42451501016,
job 128641493234 SUCCESS; artifact 13606181707, reported SHA256
7072fe8097cd1f3162bda7511f3f5da329160348a9f940cb17024521b1ce9c08.
Eight profiles inspected: standard-only; doubled-quote witness axiom-free.
Six escape guards, retained native controls, expected RED, inventory and frozen
source guards passed. Full production job skipped. Failed cc7e9950/42451130920
(fixed-index induction) and 1408d274/42451311009 (eliminated endpoint name) remain
recorded. Generalized the helper and inferred its endpoint; no statement weakened.
