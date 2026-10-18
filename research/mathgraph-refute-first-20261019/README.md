# MathGraph refute-first claim audit — 19 October 2026

## Question
Does the upstream L4YAML parser at EXACT commit
bca37392fdcb80481342a186a37ab37a5ede6e46 accept the same finite
selection of YAML inputs as two independent parser frontends? How does this
relate to the repository README's broad statement that YAML 1.2.2 conformance
is already established by proof?

This is a READ-ONLY audit of publicly available upstream source. No upstream
files are changed, no JPL PR is opened, and no external person is contacted.

## Frozen protocol
- Source: nasa-jpl/L4YAML at bca37392fdcb80481342a186a37ab37a5ede6e46.
- Cases: cases.json frozen in same audit commit before native execution.
- Reference: independent PyYAML 6.0.3 and ruamel.yaml 0.18.17 parse/composition
  (NOT full YAML 1.2.2 specification oracles).
- Oracle disagreement: no correctness verdict, hard failure.
- Native: L4YAML.TokenParser.parseYaml as actually compiled at the pinned source.
- Full output: reference.json, Probe.lean, native.out, summary.json in CI artifact.
- Positive and negative controls are mixed; no source or parser patch is applied.
- README claim-scope check is independent of native parser execution.

## Pre-declared interpretation
- If a standard-conforming reference accepted input is refused by L4YAML,
  report a SOURCE-PINNED DIFFERENTIAL, not a universal theorem.
- If all finite observations agree, report NO DISAGREEMENT IN FINITE SET,
  not general conformance.
- Distinguish established mismatch from new discovery. Recursive aliases
  were already documented by Nicolas, so re-observing them is NOT novel.
- The original advertised parse_iff_grammar was already refuted and corrected;
  this audit does not claim to discover that again.
- No finite parser experiment replaces an independently specified YAML language,
  an exact input-to-event proof, a verified ABI, or the final capstone theorem.

## Running
On the exact repository revision with Python and Lean toolchain installed:
  python research/mathgraph-refute-first-20261019/run_audit.py prepare
  lake build L4YAML.Parser.Composition
  lake env lean research/mathgraph-refute-first-20261019/Probe.lean > research/mathgraph-refute-first-20261019/native.out
  python research/mathgraph-refute-first-20261019/run_audit.py compare

GitHub Actions performs frozen source verification and stores all receipts.
