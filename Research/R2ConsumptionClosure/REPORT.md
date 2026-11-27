# Actual consumed-value contexts constructed; global storage remains open

**WARRANTED, bounded:** Lean 4.36.0 checks real entry-context suppliers for
the initialized 4/0 and 6/2/0 source controls. The complete 6/2/0 grammar proof
consumes the inner value, omits the middle entry, and consumes both outer
values. It constructs the question entries from the actual source prefix and
uses the first-document `single` route. No free enclosing-route premise,
`scannerDrop`, `implicitContinue`, custom axiom or native-decide axiom supplies
these contexts.

**UNKNOWN, global retention:** the real value-completion producer accepts the
new mandatory context, but its generic caller cannot yet supply it. The
changed-contract diagnostic has 14 explicit demands and no additional type
errors. This is 13 retained old demands plus one new supplier demand, not a
measurement of eight proof debts paid. The seven critical positions remain
open on the unchanged accepted production source.

Parent `bd56eb5b5bf4e10a9814f2c05c32ddc1d098ab86`, production source SHA256
`f1eece1acca9f124666aa8fcc8fe5b591c316df35b292b32ed28af491a25772a`;
Lean 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. Published
changes are research evidence only. The existing 186-row native experiment
and #384/item 541 integration qualification are not duplicated.

## The new continuation and why it is different

The fixed pair's terminal result is one `ExplValueLine`. That result does not
itself exhibit a fresh pair after another value is consumed. This experiment
does not prove the old pair impossible. It supplies a different, explicitly
consumption-closed contract.

`EntryStep P own` supports both completing this entry without a value and
consuming its actual colon/value. Both alternatives retain its compact mapping
tail before returning `P`. `EntryValues sc P` nests those steps at the marked
columns read from `sc`. Its recursion ceiling is computed from that same
projection; no separate mark list, snapshot or optional escape is stored.

`EntryValues.consume` proves that consuming a marked owner preserves the whole
continuation for every surviving smaller marked ancestor. The before/after
states, backward marked membership, strict survivor bound, actual indent,
colon and value are explicit premises. `LandingBridge.lean` derives the strict
bound from the already available output-stack monotonicity, top bound and
consumed-own exclusion. `EntryValues.pair` projects the legacy two-value demand
from the new family.

`colon_value_frames` also keeps the consumed mapping's own tail open as
`KeyFrames P [map n]`. It preserves nonempty sibling tails. The simpler
`colon_value_domain` closes that one mapping with a nil tail when the next
operation is an ancestor transition. Two executable sibling controls pass.
The framed form is reusable for the remaining invariant transport; it has
not been installed throughout the production carriers.

## Concrete initialized suppliers, including a complete mixed route

`ConcreteSuppliers.lean` starts from the public scanner's seed and locates its
actual colon states using `scanNextToken` and the public fuel budget. Kernel
reduction checks the source characters, successful first-colon observation,
byte offsets, columns, marked projections and the first value cursor's
remaining characters. These proofs use `decide +kernel`, not native-decide.
The two parser acceptance checks and two sibling controls are executable
guards; they are not kernel reductions of the public parser.

| Source | Checked state after inner colon | Supplied grammar context |
| --- | --- | --- |
| `? ? ? a\n    : b\n: d\n` | offset 13, column 5, marks `[0,2]` | Any actual value node retains both outer entries. |
| `? ? ? ? a\n      : b\n  : d\n: e\n` | offset 17, column 7, marks `[0,2,4]` | Any actual value node retains all three outer entries. |

The suppliers construct the literal question positions, their compact-key
indentation and the plain `a` key. They obtain the root route from
`nodocMapRouteF`, which uses `SLYamlStream.single`. There is no assumed root
route or arbitrary scanner snapshot standing in for the initialized state.

`actual_6_2_0_consumption` then constructs the actual `b` node, omits the entry
at column 4 after that node completes, consumes the actual value at column 2,
and consumes the root value at column 0. Kernel-checked scanner projections
at those later colon states are `[0]` and `[]`, with offsets/columns 23/3 and
27/1. The result is `SLYamlStream` from the exact source prefix to EOF.

An independent environment walk checks transitive type/value dependencies:

| Checked declaration | Reached constants | Required constructors | Forbidden dependencies |
| --- | ---: | ---: | ---: |
| `actual_value_domain4` | 6,134 | 3 present | 0 |
| `actual_value_domain6` | 6,136 | 3 present | 0 |
| `actual_6_2_0_consumption` | 6,168 | 3 present | 0 |

Required: `SLYamlStream.single`, `SBlockMapEntry.explicit`,
`SBlockMapEntry.explicitEmpty`. Forbidden: `SLYamlStream.scannerDrop`,
`SLYamlStream.implicitContinue`, `dropClose`, `sorryAx`. The audit validates
that every required/forbidden name exists before testing its closure.
Each checked supplier and the complete route use only `propext`,
`Classical.choice`, `Quot.sound`. This is a finite source-grounded result,
not a proof of trace uniqueness or universal scanner/grammar correspondence.

## The actual production consumer accepts the contract

The separate diagnostic starts from the preceding strict retention variant,
SHA256 `578f4fb5803a3ac74d6ff40265db3bd78fec577bd5dad7c53b977f758de76500`.
It inserts the checked family and requires its node domain at the real
`accum_content_on_pendingMapValue_indented`. The one-line flow-content arm
(which includes plain scalar values), block-scalar arm and multiline arm all
consume that context using their existing actual node constructors and
backward marked-membership evidence.

The producer declaration elaborates. Its raw, unmangled axiom profile is
byte-identical to the accepted baseline: 48 axioms, including the same
inherited native-decide leaves, SHA256
`2ff7fe79deaca52cf869907334227bbd85475a8a64a3a96bbae2cc78b85da46a`.
No `sorryAx` occurs in this producer's profile. Initial pretty-printed private
aliases differed; raw `Lean.collectAxioms` names resolve that display issue.

The complete diagnostic still fails, exit 1:

| Demand | Old strict contract | New mandatory-context contract |
| --- | ---: | ---: |
| Three key-writer residual classes in three content arms | 9 | Compiled under the new premise |
| Generic caller that must supply the new node domain | Not demanded | 1 |
| Other colon callers / closes / properties / empty values / union | 13 | 13 |
| Additional type errors | 0 | 0 |

The new labelled goal is `R2_VALUE_COMPLETION_ENTRY_VALUES` at
`accum_content_pending`, the actual caller. It needs a domain over the
pending value node that returns `EntryValues` for the scanner's surviving
marks. Existing single-value `h_kslot` evidence does not itself supply that
family. The constructor/invariant must retain it from the real question and
colon producers. The surrounding failed variant is not a qualified capstone
or production repair; no new critical-position measurement is inferred.

The exact final diagnostic source SHA256 is
`08ea2422212322c45f1b27750f30e1ad88598bc61cafc81d40e38daa2db14943`.
`producer-domain.patch` reconstructs it from the preceding strict variant.

## Remaining target and lineage

The finite suppliers and consumption/landing/tail adapters are **REUSABLE**.
Storing this family in the actual `pendingMapValue` invariant and transporting
it through its real producers is **CANDIDATE**. Universal supply and all seven
critical retirements remain **UNKNOWN**. Preserve the framed result when a
consumed mapping may still gain siblings; do not replace it globally by a
closed stream or by another fixed-arity pair.

Next: strengthen the informative value-domain payload at `pendingMapValue`
and fund it at the actual explicit-entry and colon producers, using these
concrete witnesses as regressions. Price every new obligation and retain the
13 unrelated residuals. No new optional alternative is justified by this
experiment.

Earlier elaboration, namespace and output-directory failures are retained.
Attempting to reduce the public parser with kernel `decide` stopped at its
non-reducing entry point; executable guards are used for that observation.
That failure does not refute either grammar supplier. The first changed
producer price and final raw-axiom price both expose the same 14 labels.
The original 22-demand diagnostic and prior negative branches remain in the
parent lineage.

No runtime file, production branch, guard, detector or ceiling was changed.
No hosted workflow, maintainer message, merge or approval attempt was made.

## Reproduction

Use this source's pinned toolchain and manifest. Build the unchanged imports:

```sh
lake build L4YAML.Proofs.Production.DocumentProduction
mkdir -p .lake/build/lib/lean/Research/R2ConsumptionClosure
lake env lean -o .lake/build/lib/lean/Research/R2ConsumptionClosure/EntryValues.olean Research/R2ConsumptionClosure/EntryValues.lean
lake env lean -o .lake/build/lib/lean/Research/R2ConsumptionClosure/ConcreteSuppliers.olean Research/R2ConsumptionClosure/ConcreteSuppliers.lean
lake env lean Research/R2ConsumptionClosure/DependencyAudit.lean
lake env lean Research/R2ConsumptionClosure/LandingBridge.lean
lake env lean Research/R2ConsumptionClosure/SiblingControls.lean
lake env lean Research/R2ConsumptionClosure/ColonTailFrames.lean
lake env lean Research/R2ConsumptionClosure/ProducerAxiomAudit.lean
```

For the failed production diagnostic, use a disposable exact `9f1f7bc6`
checkout. Apply the prior retention-original, retention-strict-delta and
survivor-domain retention-refinements patches, then this directory's
`producer-domain.patch`. Use matching built imports and run
`lake env lean -j 1 L4YAML/Proofs/Production/StreamAccum.lean`. Expected exit 1
and the 14-label roster in `producer-result.json`. The new mandatory supplier
is a proof obligation, not an axiom or a default fallback.
