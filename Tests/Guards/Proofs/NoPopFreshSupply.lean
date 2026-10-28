import Tests.Guards.Proofs.RelaySupplyCensus

/-!
# Item 381: typed fresh-map supply

The new route may be paid only at the empty pending-sequence entry, and
only on the proof branch with `n + 1 ≤ k`. A source-level comment or a
parser verdict is not sufficient to establish this supply classification.
-/

open Lean Meta Elab Command L4YAML.Tests.Guards.RelaySupplyCensus

namespace L4YAML.Tests.Guards.NoPopFreshSupply

run_cmd do
  let ns := `L4YAML.Proofs.StreamAccum
  let opener := ns ++ `indicator_open_map
  let env ← getEnv
  let (es, skipped) ← edges opener
  let mut rows : Array String := #[]
  for e in es do
    if e.callee == opener && binderName env opener e.idx == `h_fresh_land then
      if e.caller == ns ++ `accum_block_on_pendingBlock ||
          e.caller == ns ++ `accum_block_on_pendingBlockContent ||
          e.caller == ns ++ `accum_block_on_noPending then
        rows := rows.push s!"{e.caller.getString!}: {e.how} \
          leaves={e.leaves.toList} src={e.leafSrc.toList}"
  let expected := [
    "accum_block_on_noPending: DECLINE leaves=[] src=[closed]",
    "accum_block_on_pendingBlock: SPLIT dite leaves=[PAY, DECLINE] src=[free, closed]",
    "accum_block_on_pendingBlockContent: DECLINE leaves=[] src=[closed]"
  ]
  unless rows.toList == expected && skipped == 39 do
    throwError "fresh map supply drift:\nexpected={expected}\ngot={rows.toList}\nskipped={skipped}"

end L4YAML.Tests.Guards.NoPopFreshSupply
