import Research.R2ConsumptionClosure.ConcreteSuppliers
import Lean

open Lean

namespace R2ContextAudit

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
    else
      missing := missing.push n
  return (seen, missing)

end R2ContextAudit

run_cmd do
  let env := (← getEnv).setExporting false
  for root in [`R2ConcreteSuppliers.actual_value_domain4,
      `R2ConcreteSuppliers.actual_value_domain6,
      `R2ConcreteSuppliers.actual_6_2_0_consumption] do
    unless env.contains root do throwError "missing checked supplier {root}"
    let (used, missing) := R2ContextAudit.dependencies env [root]
    unless missing.isEmpty do throwError "supplier {root} has unresolved dependencies {missing}"
    for forbidden in [`L4YAML.Surface.SLYamlStream.scannerDrop,
        `L4YAML.Surface.SLYamlStream.implicitContinue,
        `L4YAML.Proofs.StreamAccum.dropClose, `sorryAx] do
      unless env.contains forbidden do throwError "unknown forbidden audit name {forbidden}"
      if used.contains forbidden then throwError "supplier {root} uses forbidden {forbidden}"
    for required in [`L4YAML.Surface.SLYamlStream.single,
        `L4YAML.Surface.SBlockMapEntry.explicit,
        `L4YAML.Surface.SBlockMapEntry.explicitEmpty] do
      unless env.contains required do throwError "unknown required audit name {required}"
      unless used.contains required do throwError "supplier {root} omits actual constructor {required}"
    let axioms ← Lean.collectAxioms root
    let allowed := [`propext, `Classical.choice, `Quot.sound]
    for axiomName in axioms do
      unless allowed.contains axiomName do throwError "supplier {root} has extra axiom {axiomName}"
    logInfo s!"CONTEXT-AUDIT {root}: constants={used.size} required=3 forbidden=0 axioms={axioms.map Name.toString}"
