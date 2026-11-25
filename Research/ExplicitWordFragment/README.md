# Source-defined explicit word fragment

WARRANTED for the exact source-defined fragment after local verification and independently inspected hosted replay on Lean 4.36.0.

`word_fragment_assurance` assumes only that `key` and `value` are nonempty lists
of lowercase ASCII letters. Its source is exactly `? key\n: value`, without a
trailing line break. There is no length bound, scanner-success admission test,
grammar oracle, caller-provided state, enclosing route, slot, event transport,
or EOF premise.

It proves together:

- Successful actual `scanFiltered`, with all eight positioned tokens and both
  scalar payloads fixed by the source words.
- `parseYamlSingle` returns precisely the block mapping from the key word to
  the value word. This is the library's `YamlValue` result, before a Core
  Schema resolver or a foreign-language binding constructs native values.
- The serialization-event list is empty, and the owner's `TraceOf` holds for
  the complete source with exactly that list.
- Four real `scanNextToken` transitions compose through the actual `scanLoop`
  for every remaining fuel. The returned state's offset is the source byte
  length and its next scanner step is `ok none`.

The unbounded induction is `word_prefix`. It preserves the complete scanner
record, not merely its cursor, then proves exact stopping at the key's line
break and the value's EOF. The initialized path discharges the existing root
fold's computable guard from these source facts. That guard is an intermediate
lemma, not a hypothesis of the final theorem. The root proof consumes the
owner's pending-node/content-park infrastructure.

## Evidence and lineage

| Item | Exact boundary |
| --- | --- |
| Owner source | `nasa-jpl/L4YAML@0dbf0c120601fccc1d837025f3bef405cc4f2062` (#377 source, including its deletions) |
| Owner library tree | `0a8d15505cf2520df980bc4af05eca0ad72f86c8` |
| Parent consumer proof | `metalogiclabs/L4YAML@97ea6756695aa32165f95fed72bdbd5462145ef7`, successful run 45573782112 |
| Root-proof source | Workflow `group77-root-event-eof.yml` at `38242e6cc22598c209401d2f330af6b81f96ea5c` |
| Root-proof adaptation | Replace its unavailable retained-comment helper by the already qualified `OwnerExplicitKeyPark.content_leaf_at_retained`; omit unrelated finite fixtures |
| Source/payload/fold proofs | Only `propext`, `Classical.choice`, `Quot.sound` (some use fewer) |
| Final grammar theorem | Exactly the same 45 inherited closed Boolean axioms as the parent consumer; all 45 independently replayed, none rejected |
| New nonstandard axioms | Zero in the new theorem closures |
| Local verification | 523 build jobs; 12 checked profiles; 724 source/parser/token/EOF controls; two corrupted-payload controls |
| Independent qualification | [Run 45582970898](https://github.com/metalogiclabs/L4YAML/actions/runs/45582970898), job 139097352108, exact proof/workflow commit `afdab55ae7d6a4da04e987a33706d4f6faeff920`: terminal success; 541 proof/control build jobs, 12 profiles, all 45 inherited native leaves replay-validated, zero rejected; 724 controls and two corrupted-payload controls |

The replay policy retains its native-evaluation fallback and therefore has the
same additional trust boundary as the parent qualification; this is not a
claim that all inherited native assertions were re-proved with only kernel
reduction. Their names and raw counts are preserved in `local-axiom-replay.txt`.
`source-sha256.json` fixes every research Lean file. The CI artifact records
the evidence commit and verifies the owner's library, toolchain and manifest
remain unchanged.

Independent archive verification (26 November 2026): artifact `15007862196`,
`explicit-word-fragment-evidence`, downloaded ZIP SHA-256
`f7e73ee54018719c346423067db9886bb16d0f9e0ee206146a9a9b0d258fc03f`
exactly matches GitHub's artifact digest. All 50 members pass ZIP CRC checks;
all 15 manifest entries match both archived bytes and exact published source.
The hosted audit reports `WORD_LINEAGE same_inherited_axiom_set=true` and
`WORD_UNION raw=45 validated=45 rejected=0`. This promotes the formerly
candidate hosted qualification only; it adds no proof or broader claim.

## Specification boundary and residual

The source family independently names a conventional explicit block mapping.
The normative [YAML 1.2.2 section 8.2.2](https://yaml.org/spec/1.2.2/#822-block-mappings)
uses explicit-entry production [189], key [190], and value [191]. The value
indicator is on its own line at the mapping column. The 1024-character limit
in that section concerns implicit keys; the controls include explicit keys
of lengths 1023, 1024, 1025 and 2048.

The kernel theorem targets the owner's annotated grammar on this source
family. It is not an independently audited equivalence between the owner's
entire grammar and the normative specification. Full `scan_trace` and Group
7.7 remain open, and prior counterexamples to broader correspondence remain
in force. No property, tag, alias, quoted/block scalar, nested collection,
comment, BOM, additional whitespace or schema-resolution extension is claimed.

The smallest useful next extension is a single explicitly anchored scalar
value. It makes event preservation nonempty while keeping this now-proved
initialization, explicit-key handoff and EOF route available for reuse.
