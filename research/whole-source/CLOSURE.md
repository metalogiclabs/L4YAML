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
