import L4YAML.Proofs.Production.StreamAccum
import Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace R2CompletionBaseline
def countConstructor (name : Lean.Name) : Lean.Expr → Nat
  | .const n _ => if n == name then 1 else 0
  | .app f a => countConstructor name f + countConstructor name a
  | .lam _ _ b _ => countConstructor name b
  | .forallE .. => 0
  | .letE _ _ v b _ => countConstructor name v + countConstructor name b
  | .mdata _ b | .proj _ _ b => countConstructor name b
  | _ => 0
end R2CompletionBaseline

run_cmd do
  let env ← Lean.getEnv
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent
  for (name, expected) in [(`L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented,3),
      (`L4YAML.Proofs.StreamAccum.accum_content_pending,3)] do
    let some ci := env.find? name | throwError "missing producer {name}"
    let some body := ci.value? (allowOpaque := true) | throwError "missing producer body {name}"
    let count := R2CompletionBaseline.countConstructor ctor body
    unless count == expected do throwError "wrong completed-content inventory {name}: {count}"
    Lean.logInfo s!"COMPLETION-INVENTORY {name}: {count}"
  for (ctorName, field) in [(`L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent,`h_closable_entry),
      (`L4YAML.Proofs.StreamAccum.PendingNode.pendingProps,`h_routeE)] do
    let some ci := env.find? ctorName | throwError "missing constructor"
    let mut cursor := ci.type
    let mut found := false
    while let .forallE name domain body _ := cursor do
      if name == field then
        found := true
        if domain.getUsedConstants.contains `L4YAML.Proofs.R2ConsumptionClosure.EntryValues then
          throwError "accepted field unexpectedly carries whole family"
      cursor := body
    unless found do throwError "accepted field name did not resolve"
  for name in [`L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented,
      `L4YAML.Proofs.StreamAccum.compact_open_map,
      `L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented] do
    let axioms ← Lean.collectAxioms name
    Lean.logInfo s!"COMPLETION-BASELINE-AXIOMS {name}: {repr axioms}"
  Lean.logInfo "COMPLETION-LEGACY-CONTROL constructors=6 completed_family=absent props_family=absent"
