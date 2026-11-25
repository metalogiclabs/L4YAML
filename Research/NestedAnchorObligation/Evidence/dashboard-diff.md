## Pins moved against `HEAD`

| kind | moved | reading |
|---|---:|---|
| directed (roster fields with a goal) | 1 | toward 1, not toward 0 |
| population (readings without a target) | 3 | consumer-set sizes, holder counts, thread lengths — no direction |

| census | field | before → after | goal | left before → after | move | verdict |
|---|---|---|---:|---|---|---|
| `RelaySupplyCensus` | `DECLINE` | 237 → 236 | 0 | 237 → 236 | shrink-only | toward |

<details><summary>population moves</summary>

- `OrTrueAudit.expectedSummary` paid 24 → 25
- `OrTrueAudit.expectedSummary` relayed 119 → 118
- `RelaySupplyCensus.expectedTally` PAY 50 → 51

</details>
