# State correspondence removes three escape calls

Research continuation, 26 November 2026. Owner: NASA/JPL L4YAML
`cc83019024fb88b7c0d0cdadc4e590bda7a72788`, library tree
`0a8d15505cf2520df980bc4af05eca0ad72f86c8`, Lean 4.36.0.
Baseline: the independently qualified [root-key-slot payment](../NestedAnchorObligation/HOSTED_QUALIFICATION.json).

Status: CANDIDATE pending the final strict census builds and clean hosted replay.

## Objective and result

Make the remaining proof obligations follow actual scanner state. The existing
`PendingNode.pendingContent.h_vpack` chose a list of columns and proved it covered
the scanner's marks. Two helper parameters then discarded that coverage, making
an arbitrary empty list an admissible informative witness. That lost link also
left an off-column escape in the explicit-value route.

The candidate:

* indexes the constructor field directly by `RegisterWitness.markedCols sc`;
* retains the coverage at both helper boundaries;
* reads an explicit value's column from `PendingKeySound.Sound.reg`, then
  transports that actual mark back through preprocessing;
* uses the result at all three production callers of
  `block_dispatch_deferred_stamp_offcol`, routing each accepted explicit value
  through the existing explicit-value proof;
* reuses an existing named alternative when a funder lacks a covered domain.

The off-column wrapper remains as an existing instrument target; it is no longer
in the final correctness proof's dependency closure. Its broader retirement and
the other census guards belong to a subsequent integration qualification.

## Verification boundary

The local proof module, its `DocumentProduction` consumer, the actual ghost-index
guard, and the dependency/axiom audit were compiled on the exact owner library
with the candidate applied. The six compared axiom profiles are exact sets,
including inherited `native_decide` names. No new custom or native axiom is
permitted for either new lemma. Both new lemmas must be consumed by a capstone.

`ReachableControls.lean` starts from real source initialization. It checks 180
sources, 1,110 accepted explicit values, 930 cases with multiple pending marks,
and 3,660 scanner steps. In all 1,110 source-indicator cases the actual pre-state
domain is nonempty, refuting the arbitrary empty-domain shortcut. The controls
cover depths 1, 2, 3, 8, 16, indentation widths 1, 2, 4, six leaf forms and LF/CRLF.
They are finite controls; the correspondence lemma itself is quantified over
arbitrary states satisfying the scanner invariants already maintained by the
accumulation proof.

| Reading | Qualified root baseline | Candidate |
|---|---:|---:|
| Ghost indices | 74 | 73 |
| Production off-column fallback calls | 3 | 0 |
| Off-column wrapper on final proof path | yes | no |
| Six audited axiom profiles | baseline | unchanged |

Direct relay declines remain 236, critical-path direct declines remain five,
and the seven critical optional positions remain. The final relay reading exposes
one additional declined split leaf (213 to 214; free leaves 117 to 118). It also
records two more paid split leaves. These readings follow the restored domain and
are disclosed with the favorable ghost-index change. The OrTrue summary,
consumer classes and trivial-writer roster remain unchanged; two supply rows move.

The owner censuses, their complete raw readings and the hosted receipt determine
the final numbers. Direct declines are not claimed paid by these edits. A first
restored-cover candidate exposed larger split-leaf counts; its raw reading is
preserved rather than presenting only the favorable metric. The final candidate
also removes a newly manufactured trivial alternative, reusing the existing
declining field instead. Read the final qualification's dashboard diff for that
exact tree.

The workflow replays both the prior root payment and this candidate from the
pinned owner checkout, runs the real census guards, checks the two final theorem
consumers, compares exact axiom sets, and archives source identities and raw logs.
It is a focused proof/census qualification, not the repository's full default,
bindings or documentation qualification.

## Lineage and residual

`PREDICTIONS.md` was written before the restored-cover compiler experiment.
The first compilation identified eight coverage-erasing or coverage-assembling
supplies. Re-indexing the constructor exposed ten producer conversions; each now
uses the producer's coverage to prove the property at every actual mark.
The raw pricing logs are retained with the evidence.

`scannerDrop`, the no-pack and generic escape routes, the remaining critical
`PackAlt` positions, universal `scan_trace`, and corrected Group 7.7 remain open.
No approved production PR head is changed. The next experiment should either
retire the now-unreached wrapper with its census debt or pay a remaining no-pack
producer using an actual maintained scanner invariant.
