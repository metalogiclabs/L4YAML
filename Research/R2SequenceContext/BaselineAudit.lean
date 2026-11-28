import L4YAML.Proofs.Production.StreamAccum
import Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace R2SequenceBaseline

def countConstructor (name : Lean.Name) : Lean.Expr → Nat
  | .const n _ => if n == name then 1 else 0
  | .app f a => countConstructor name f + countConstructor name a
  | .lam _ d b _ | .forallE _ d b _ => countConstructor name d + countConstructor name b
  | .letE _ t v b _ => countConstructor name t + countConstructor name v + countConstructor name b
  | .mdata _ b | .proj _ _ b => countConstructor name b
  | _ => 0

end R2SequenceBaseline

run_cmd do
  let env ← Lean.getEnv
  let ctorName := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock
  let rows := [(`L4YAML.Proofs.StreamAccum.accum_block_on_noPending, 1),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock, 2),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent, 1),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock, 3)]
  let mut total := 0
  for (name, expected) in rows do
    let some ci := env.find? name | throwError "missing producer {name}"
    let some body := ci.value? (allowOpaque := true) | throwError "no producer body {name}"
    let count := R2SequenceBaseline.countConstructor ctorName body
    unless count == expected do throwError "constructor inventory {name}: {count} != {expected}"
    total := total + count
    Lean.logInfo s!"SEQUENCE-INVENTORY {name}: {count}"
  unless total == 7 do throwError "wrong actual construction count {total}"
  let some ctor := env.find? ctorName | throwError "missing constructor"
  let mut cursor := ctor.type
  while let .forallE name domain body _ := cursor do
    if name == `h_close_entry && domain.getUsedConstants.contains
        `L4YAML.Proofs.R2ConsumptionClosure.EntryValues then
      throwError "accepted control unexpectedly carries the new family"
    cursor := body
  for producer in [`L4YAML.Proofs.StreamAccum.compact_open_map,
      `L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented] do
    let axioms ← Lean.collectAxioms producer
    Lean.logInfo s!"SEQUENCE-BASELINE-AXIOMS {producer}: {repr axioms}"
  Lean.logInfo "SEQUENCE-LEGACY-CONTROL constructions=7 whole_family=absent"
