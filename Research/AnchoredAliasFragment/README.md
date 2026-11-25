# Unbounded anchored-word / later-alias assurance

Blueprint 7.7 research fragment, on isolated branch
`fix/anchored-word-alias-assurance`. Approved production PR heads are untouched.

The source is exactly:

```yaml
? key
: &a value
? copy
: *a
```

`key` and `value` range over arbitrary nonempty lowercase ASCII words, without a
length bound. The final lemma `AnchoredAliasAssurance.alias_word_assurance` takes
only those word hypotheses. It derives the exact thirteen positioned tokens,
the raw document, the resolved ordered mapping, the event sequence
`[defineAnchor "a", useAlias "a"]`, the independently constructed owner grammar
trace, serialization well-formedness, and the actual initialized scanner fold
through all nine content transitions and the EOF checks. The registry at the
alias is derived from that execution, rather than assumed.

An additional universally quantified lemma establishes that emptying the
registry makes alias content dispatch fail, including at the actual reached
state. This deletion is a causal intervention; the altered state is not claimed
to be independently reachable. The native controls additionally delete, rename,
and restore the registry at reached states.

The mapping semantics are the owner's ordered `YamlValue` pairs. In particular,
`key = "copy"` is included and produces two entries. This is not a normative
YAML key-uniqueness, schema-resolution, or foreign-binding correspondence claim.
The complete `scan_trace`, corrected Group 7.7 biconditional, normative
whole-grammar equivalence, and nested-frame composition remain open.

## Evidence boundary

The local Lean 4.36.0 build passed on owner
`0dbf0c120601fccc1d837025f3bef405cc4f2062`, whose entire library tree
`0a8d15505cf2520df980bc4af05eca0ad72f86c8` is byte-identical to integration
branch `fix-a-grammar-completeness` at merged #377 commit
`cc83019024fb88b7c0d0cdadc4e590bda7a72788`. The local executable audited 23
export closures: only `propext`, `Classical.choice`, and `Quot.sound`; no new or
inherited native assertion axioms. An initial local audit link failed when the
scratch filesystem filled; removing a reproducible compiler download and
relinking succeeded. No proof change was needed for that environmental failure.

Hosted qualification is defined by
`.github/workflows/group77-anchored-alias.yml`, pinned to exact owner `cc830190`.
It runs the already published 697-case alias probe and 24 extra boundary case
executions before staging the new proof. These 721 executions are not claimed
to be 721 distinct sources. Extra boundaries include exact token positions,
fuel values 0, 1, 2, 9, 10, and `key = "copy"`.

The frozen parent comes from qualified anchored-word proof commit
`83a6e3e2bd6a47768aaaba427838dce53057f8f3`, with durable receipts on parent
`b25d1380f413166aa9d765e4aa539f657a87dc4d`. The bounded alias probe was published
separately as `65667a3beba177fa371aebb6842bfc5e58a72f40`.
`source-sha256.txt` binds every proof-preparation input, including the embedded
parent workflow and the probe. The hosted artifact must be independently
digest-, CRC-, manifest-, source-, and axiom-audit-verified before the hosted
claim is promoted. `QUALIFICATION.json`, when present, records that promotion
and the exact run, owner, source commit, artifact, and retained archive.

This is scoped proof/adversarial qualification, not a fresh full-project native
battery, census, binding, documentation build, or five-way integration run.
