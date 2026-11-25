## Pins moved against `research-root-baseline`

| kind | moved | reading |
|---|---:|---|
| directed (roster fields with a goal) | 3 | toward 1, not toward 2 |
| population (readings without a target) | 12 | consumer-set sizes, holder counts, thread lengths — no direction |

| census | field | before → after | goal | left before → after | move | verdict |
|---|---|---|---:|---|---|---|
| `GhostIndexCensus` | `ghost` | 74 → 73 | 0 | 74 → 73 | shrink-only | toward |
| `RelaySupplyCensus` | `DECLINE` | 213 → 214 | 0 | 213 → 214 | shrink-only | AWAY (owner's word) |
| `RelaySupplyCensus` | `DECLINE-free` | 117 → 118 | 0 | 117 → 118 | shrink-only | AWAY (owner's word) |

<details><summary>population moves</summary>

- `CapstonePathAudit.expectedSummary` streamAccum-reached 1152/1262 → 1152/1264
- `CapstonePathAudit.expectedSummary` arms 235 → 237
- `RelaySupplyCensus.expectedTally` edges 640 → 646
- `RelaySupplyCensus.expectedTally` PAY 51 → 49
- `RelaySupplyCensus.expectedTally` VIA 28 → 36
- `RelaySupplyCensus.expectedSplitLanding` collapsed 12 → 10
- `RelaySupplyCensus.expectedSplitLanding` leaves 419 → 422
- `RelaySupplyCensus.expectedSplitLanding` PAY 195 → 197
- `RelaySupplyCensus.expectedSplitBranch` leaves 419 → 422
- `RelaySupplyCensus.expectedSplitBranch` PAY-free 195 → 197
- `RelaySupplyCensus.expectedDeclineReach` accounted 640/640 → 646/646
- `RelaySupplyCensus.expectedDeclineReach` nodes 157 → 158

</details>
