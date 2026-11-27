# PR #384 description history before landed-root integration

Superseded head: 0146eb0833716f6e8e3ff22babe66b39c9415ebf. Current head: d221fb2d8893984ca4f894964364ebeff2368768. The live description now presents the current qualification. The original complete description is retained below to preserve its source and evidence lineage.

| kind | moved | reading |
|---|---:|---|
| directed (roster fields with a goal) | 6 | toward 4, not toward 2 |
| population (readings without a target) | 131 | consumer-set sizes, holder counts, thread lengths — no direction |

| census | field | before → after | goal | left before → after | move | verdict |
|---|---|---|---:|---|---|---|
| `RelaySupplyCensus` | `DECLINE` | 237 → 235 | 0 | 237 → 235 | shrink-only | toward |
| `PremiseNecessityCensus` | `dead` | 33 → 30 | 0 | 33 → 30 | shrink-only | toward |
| `ValueLinePacks` | `punt` | 19 → 17 | 0 | 19 → 17 | shrink-only | toward |
| `ParkBill` | `Tp` | 40 → 39 | 0 | 40 → 39 | shrink-only | toward |
| `RelaySupplyCensus` | `DECLINE` | 213 → 214 | 0 | 213 → 214 | shrink-only | AWAY (owner's word) |
| `RelaySupplyCensus` | `DECLINE-free` | 117 → 118 | 0 | 117 → 118 | shrink-only | AWAY (owner's word) |

## Current owner refresh — 27 November 2026

Resolved integration against owner `a62ac16b92d6487bc58405043bca79d39bae30d0`. Current PR head: [`0146eb0833716f6e8e3ff22babe66b39c9415ebf`](https://github.com/metalogiclabs/L4YAML/commit/0146eb0833716f6e8e3ff22babe66b39c9415ebf); complete tree: `e4b0cbfcc76446b6a28bcf28291509dd589bbe53`.

[Native qualification](https://github.com/metalogiclabs/L4YAML/actions/runs/45895329112/job/140167683151) passed: Build completed successfully (2645 jobs). Verified: 65238/65238. All repository/census gates, C/Python/Rust bindings and cross-language backend comparisons passed. Hygiene: env clean: 11861 theorems, 0 sorries, 0 custom axioms.

The published merge commit preserves the reviewed head `4c54da7e3716ab0197b126294474bb2868651402` and the owner as parents. Its complete source tree is byte-identical to qualified generated source `c086d848c2fca12dac771ade97d245e2b2f50c6b`; publication changes commit metadata only. [Original qualification artifact](https://github.com/metalogiclabs/L4YAML/actions/runs/45895329112/artifacts/15155282668), SHA-256 `deed08dd25396bb109ec2fd6d1d83a01ef623ce02f3d87d5985389d9ac8bf18a`. Upstream PR CI remains a separate result.

The two adverse directed readings remain disclosed: split declines 213→214 and free declines 117→118. All seven critical optional positions remain.

## Earlier source-qualified implementation and validation

The block consumers discard the `MarkedColsIn` coverage already stored in the pending field. An explicit `:` can then take the off-column deferral because the consumer's list is disconnected from the scanner's actual pending columns. Preserve that coverage, derive the source column's membership from the maintained soundness invariant, and discharge all three off-column applications.
`marked_col_of_explicit_source` is consumed through `scan_content_gives_stream_v2` by the existing scanner/parse strictness capstones. The off-column wrapper and the now-unused singleton helper are retired from the library; their adversarial witnesses remain private in the guard tests. Two document-marker supplies also construct covered empty domains.
Measured improvements: direct relay declines 237 → 235, critical-path direct declines 6 → 4, value-line punts 19 → 17, and the live drop set 8/8 → 7/8. All seven critical optional positions remain.
The stronger domain exposes a previously unconnected empty-list chain. Its existing named alternative is retained: split decline leaves rise **213 → 214** and free declines **117 → 118**. These are the two adverse directed readings for owner review. The census walkers and comparisons remain intact; snapshots and inline cross-check constants were remeasured, with dated causal notes.
This implements the consumer-domain correction discussed in #383 under 12.3.5 and pays two marker supplies. #380's separate root payment is excluded. The remaining writer sequence, flow-frame `PackAltG`, full field retirement, `scannerDrop` removal, universal `scan_trace` and corrected Group 7.7 remain open.
Validation: [current-owner qualification 45777461093](https://github.com/metalogiclabs/L4YAML/actions/runs/45777461093) **passed** on this exact tree and owner `2ebc4740`: full default build (2,645 jobs), all repository/guard/dead-census/dashboard gates, **65,233/65,233 verified cases**, matrix 869 passed / 0 failed / 151 skipped, and compiled-library hygiene (11,860 theorems, zero sorries/custom axioms). All seven existing producer/capstone axiom sets are unchanged; the new lemma uses only `propext`, `Classical.choice`, and `Quot.sound`. Separate event score: 347/358, with eleven event differences.
[Immutable receipt and original qualification archive](https://github.com/metalogiclabs/L4YAML/tree/0b1a3bd547386048f2d46975349b924bbb13060e/Research/ContentSlot). The downloaded archive independently matches SHA-256 `ab094fd74135c38e936b94969fa80b230e4b7c3a48e2ed0a054a41efc307f53b`; all 231 members passed CRC. Independent patch application reproduces the complete tree exactly, and all 32 archived source hashes match.
Source commit `4c54da7e3716ab0197b126294474bb2868651402`, sole parent `2ebc4740262ebaa566d7bce748e0a55a5c2f0cd5`, complete tree `3b7506b0f4439102df820b8f26bf8d76ab136402`. No runtime scanner/parser, toolchain or dependency-pin changes.
