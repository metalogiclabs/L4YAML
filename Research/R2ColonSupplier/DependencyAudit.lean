import Research.R2ColonSupplier.ConsumedSibling
import Research.R2ColonSupplier.Supplier
import Lean

open Lean
namespace R2ColonSupplierAudit

partial def dependencies (env : Environment) (roots : List Name) : Std.HashSet Name × Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut missing : Array Name := #[]
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let body := (ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]
      todo := (ci.type.getUsedConstants ++ body).toList ++ todo
    else missing := missing.push n
  return (seen,missing)

end R2ColonSupplierAudit

run_cmd do
  let env := (← getEnv).setExporting false
  for (root, required) in [
      (`R2ColonSupplier.live_landing_of_no_stamp,
        [`R2ColonSupplier.live_register_marked,
         `L4YAML.Proofs.RegisterWitness.preprocess_markedCols]),
      (`R2ColonSupplier.entry_step_at_landing,
        [`L4YAML.Proofs.R2ConsumptionClosure.ValuesBelow.at,
         `L4YAML.Proofs.R2CompactSlot.ValuesBelow.restrict]),
      (`R2ConsumedSibling.cover_does_not_imply_owner,
        [`R2ConcreteSuppliers.nthColon]),
      (`R2ConsumedSibling.actual_consumed_sibling_then_ancestor,
        [`R2ColonComposition.colon_payload_of_step,
         `L4YAML.Surface.SBlockMapEntry.emptyKeyNode,
         `L4YAML.Surface.SCompactMapTail.cons,
         `L4YAML.Surface.SLYamlStream.single,
         `L4YAML.Proofs.R2CompactSlot.SlotValues.compact_question])] do
    unless env.contains root do throwError "missing checked root {root}"
    let (used,missing) := R2ColonSupplierAudit.dependencies env [root]
    unless missing.isEmpty do throwError "unresolved references {missing}"
    for name in required do
      unless used.contains name do throwError "root {root} omits required {name}"
    for name in [`L4YAML.Surface.SLYamlStream.scannerDrop,
        `L4YAML.Surface.SLYamlStream.implicitContinue,
        `L4YAML.Proofs.StreamAccum.dropClose, `sorryAx,
        `R2ConcreteSuppliers.actual_value_domain6,
        `R2ConcreteSuppliers.actual_6_2_0_consumption,
        `R2ConcretePayloads.actual_sibling_tail_consumed] do
      unless env.contains name do throwError "unknown forbidden name {name}"
      if used.contains name then throwError "root {root} uses forbidden {name}"
    let axioms ← Lean.collectAxioms root
    for name in axioms do
      unless [`propext,`Classical.choice,`Quot.sound].contains name do
        throwError "extra axiom {name}"
    logInfo s!"SUPPLIER-AUDIT {root}: constants={used.size} missing=0 required={required.length} forbidden=0 axioms={axioms.map Name.toString}"
