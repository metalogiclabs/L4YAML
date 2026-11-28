import Research.R2CompactSlot.JointSibling
import Lean

open Lean
namespace R2CompactAudit

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
  return (seen, missing)

end R2CompactAudit

run_cmd do
  let env := (← getEnv).setExporting false
  for root in [`R2ConcreteSlots.compact_level3,
      `R2ConcreteSlots.actual_root_to_consumption,
      `R2JointSibling.actual_sibling_then_ancestor] do
    unless env.contains root do throwError "missing checked root {root}"
    let (used, missing) := R2CompactAudit.dependencies env [root]
    unless missing.isEmpty do throwError "unresolved references {missing}"
    for forbidden in [`L4YAML.Surface.SLYamlStream.scannerDrop,
        `L4YAML.Surface.SLYamlStream.implicitContinue,
        `L4YAML.Proofs.StreamAccum.dropClose, `sorryAx,
        `R2ConcreteSuppliers.actual_value_domain6,
        `R2ConcreteSuppliers.actual_6_2_0_consumption] do
      unless env.contains forbidden do throwError "unknown forbidden name {forbidden}"
      if used.contains forbidden then throwError "root {root} uses forbidden {forbidden}"
    for required in [`L4YAML.Surface.SLYamlStream.single,
        `L4YAML.Surface.SBlockMapEntry.explicit,
        `L4YAML.Surface.SBlockMapEntry.explicitEmpty,
        `L4YAML.Surface.SBlockIndented.compactMap,
        `L4YAML.Proofs.R2CompactSlot.SlotValues.of_question,
        `L4YAML.Proofs.R2CompactSlot.SlotValues.compact_question] do
      unless env.contains required do throwError "unknown required name {required}"
      unless used.contains required do throwError "root {root} omits actual constructor {required}"
    if root == `R2JointSibling.actual_sibling_then_ancestor then
      unless used.contains `L4YAML.Surface.SCompactMapTail.cons do
        throwError "joint route omitted the non-nil sibling tail"
    let axioms ← Lean.collectAxioms root
    for axiomName in axioms do
      unless [`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "extra axiom {axiomName}"
    logInfo s!"COMPACT-AUDIT {root}: constants={used.size} required=6 forbidden=0 axioms={axioms.map Name.toString}"
