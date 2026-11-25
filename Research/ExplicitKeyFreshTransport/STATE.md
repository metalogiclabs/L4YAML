# Explicit-key native fresh-reservation result

Status: WARRANTED within the declared matched-colon column-drop boundary.

The matched-colon owner fold now derives event transport from actual preprocessing and scanValue execution. The arbitrary PushesTrace premise and cleared-key register guard are absent from matched_colon_owner_fold_from_transitions. No new register or reachability assumption replaces them.

## Exact evidence

- Owner: nasa-jpl/L4YAML@0dbf0c120601fccc1d837025f3bef405cc4f2062; L4YAML tree 0a8d15505cf2520df980bc4af05eca0ad72f86c8; Lean 4.36.0.
- Qualified research source: metalogiclabs/L4YAML@fca2d2609e18038147878cf3bf3c1b18629f2b96.
- Successful run: https://github.com/metalogiclabs/L4YAML/actions/runs/45572870504
- Artifact: https://github.com/metalogiclabs/L4YAML/actions/runs/45572870504/artifacts/15002549612
- New proof SHA-256: 337f264b63f32993c0ad4d5abb0b2cb73678b9e0c5d7d37a7e7fe8851f5a95aa.
- Archive SHA-256 independently matched: 00c606e9e0d6441719606a5e584ed9734ce21f9671f5244dd76bc69b5d5b22b9. All 19 manifest entries verified; ZIP contains 23 files. Archived proof bytes equal the locally rebuilt exact-owner proof.

| Check | Measured result |
| --- | --- |
| Fresh matched-colon proof build | 299/299 |
| Three exported fresh lemmas | propext, Classical.choice, Quot.sound only |
| Inherited replay build | 460/460 |
| Inherited native axiom union | 39 validated, 0 rejected |
| Fresh-save native controls | 99 active |
| Column-drop native controls | 660 active |
| Failed hypotheses / theorem refutations | 0 / 0 in this grid |
| Corrupted-reservation negative control | Reached; event destruction detected |
| Positive/negative axiom-replay controls | Passed |

Native controls cover arbitrary existing token prefixes containing anchors, aliases, tags, directives and document markers, and three pending-TAG states. The negative control is a synthetic corrupted scanner state, not a claimed reachable-scanner defect. The theorem is universal over its stated hypotheses; the computational grid is a separate non-vacuity and mutation check.

## Verification boundary and remaining residual

The proof still consumes the existing TSLYamlStream and KeyReady grammar routes, a strictly deeper pre-colon scanner column, the matching colon column, actual preprocessing/scanValue equations and scanner/surface correspondence. It does not derive the complete fold's reachable-state invariant. Full scan_trace and Group 7.7 remain open.

A separate executable replay (ActualKeyReachability.lean, actual-key-reachability.log) ran eleven native scanner inputs to their root explicit colon. Nine reached it through a column drop. Literal and folded block-scalar keys arrived with before_col=colon_col=0 and do not satisfy h_deeper. Those two are outside this result. This replay gives native scanner witnesses, not full KeyReady/TSLYamlStream reachability proofs.

The cheapest next experiment is to extend the retained-key grammar handoff to a zero-column landing, derive its fresh save from the actual block-scalar producer, and combine both native routes into the owner fold. The remaining global task is proving the grammar route is established and maintained by the complete scanner execution.

## Lineage and reuse

- Preserved failures: property-floor run 45568600164; native transport run 45568890606.
- Successful replacements: 45570509942 and 45570308481.
- Reconciled parent 4d27e0b5f2985feaaf7ce8969b11342601704720, run 45571441810: success; its downloaded archive digest was independently matched.
- First fresh-reservation draft 9ce8138584edf193a2f3ed4d753d3620156e4097, run 45572283907: failure. Its 759 native controls passed, while imported-definition transparency and an unqualified helper name caused proof elaboration failure. Guards rejected sorryAx as intended.
- Superseded approach: a line-counter argument unnecessarily inherited two native_decide dependencies. The qualified revision reads the actual break branch directly and needs only the standard axioms.
- Reusable producer fact: a successful decreasing-column block preprocess arms a fresh simple-key reservation, so the colon's retroactive writes touch newly allocated event-silent slots, whether or not scanValueClearKey clears that reservation.

All work is on isolated research/evidence branches. Production branch heads were not edited.

Research OS reconciliation is pending: Notion fetch failed with Transport closed and browser fallback reached a sign-in wall. This GitHub evidence snapshot records the result without claiming a Notion update.
