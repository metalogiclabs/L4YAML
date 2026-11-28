import Research.R2ActualValueSuppliers.Witness
import Research.R2ActualValueSuppliers.First
import Research.R2ActualValueSuppliers.Unkeyed
import Lean

open Lean

namespace R2ActualValueAudit

def closure (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      todo := info.type.getUsedConstants.toList ++ todo
      if let some body := info.value? (allowOpaque := true) then
        todo := body.getUsedConstants.toList ++ todo
  return seen

run_cmd do
  let env := (← getEnv).setExporting false
  let root := `R2ActualValueWitness.initialized_complete
  let deps := closure env root
  let required := #[`R2ActualValueSuppliers.actual_same_implicit,
    `R2ActualValueSuppliers.actual_same_value, `R2ActualValueSuppliers.implicit_value_layout,
    `L4YAML.Proofs.PreprocessIndentStable.scanValue_top_not_sequence,
    `R2MandatoryContext.compact_implicit, `R2MandatoryContext.actual_first_question,
    `R2MandatoryContext.actual_compact_sequence, `R2MandatoryContext.same_map_value,
    `R2ActualJointStep.landed_sequence_context, `R2ActualJointStep.explicit_colon,
    `L4YAML.Surface.SCompactMapTail.cons, `L4YAML.Surface.SCompactSeqTail.cons]
  let forbidden := #[`sorryAx, `L4YAML.Surface.SLYamlStream.scannerDrop,
    `L4YAML.Surface.SLYamlStream.implicitContinue, `L4YAML.Proofs.StreamAccum.dropClose,
    `R2MandatoryWitness.initialized_complete, `R2ActualJointWitness.initialized_complete,
    `R2ActualProducers.initialized_complete, `R2JointConcrete.initialized_complete,
    `R2CloseConcrete.actual_pack_sibling_then_ancestor]
  for name in required do unless deps.contains name do throwError "missing actual writer {name}"
  for name in forbidden do if deps.contains name then throwError "forbidden shortcut {name}"
  let some info := env.find? root | throwError "initialized root absent"
  if info.type.isForall then throwError "initialized proof has free input premises"
  let pureRoots := #[root, `R2ActualValueSuppliers.implicit_value_layout,
    `R2ActualValueSuppliers.actual_same_value, `R2ActualValueSuppliers.actual_same_keyless,
    `R2ActualValueSuppliers.actual_same_implicit, `R2ActualValueSuppliers.actual_same_properties,
    `R2ActualValueSuppliers.first_value_layout, `R2ActualValueSuppliers.actual_first_value,
    `R2ActualValueSuppliers.actual_first_keyless, `R2ActualValueSuppliers.actual_first_implicit,
    `R2ActualValueSuppliers.actual_first_properties,
    `R2ActualValueSuppliers.unsaved_value_layout, `R2ActualValueSuppliers.actual_unsaved_value,
    `R2ActualValueSuppliers.actual_unsaved_keyless]
  for name in pureRoots do
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
      throwError "unexpected axiom boundary {name}: {axioms}"
  logInfo m!"ACTUAL-VALUE-AUDIT required={required.size} forbidden={forbidden.size} dependencies={deps.size} free_premises=0 pure_roots={pureRoots.size} axioms=standard_three"

end R2ActualValueAudit
