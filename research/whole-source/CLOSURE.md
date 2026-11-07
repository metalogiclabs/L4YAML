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

## Next experiment

Refine the existing EventsOf.Seg.docStart dirs and Skeleton relations rather
than introducing another directive-storage representation. Seg.docStart already
retains every directive source line, and skeleton_text proves full source
reconstruction. Add independent validity and multiplicity conditions on those
retained lines, with the already independent quoted-body fragment. Derive declaration uniqueness,
reset order and agreement with source-connected events. Duplicate-version,
duplicate-handle and two-document reset separators must distinguish discarded
information from scanner/parser behavior. This fragment tests the common state
interface; it does not close the full language or justify further example-only
campaigns. Reconsider this priority if the normative coverage audit reveals an
earlier shared obstruction.

## Commands and stop rule

`python3 research/whole-source/coverage-audit.py` checks inventory drift.
`bash research/whole-source/qualify-capstone.sh DIR` checks the bounded proof chain.
`python3 research/whole-source/coverage-audit.py --closure` currently exits 2,
explicitly UNKNOWN. This is a blocking diagnostic, not an implemented final
semantic verifier: it cannot be promoted by setting a status flag. Replace that
diagnostic only with a separately reviewed, typed full-language proof consumer
and complete qualification. A false original theorem closes a diagnosis, not the
project. No current result permits declaring Capstone complete.
