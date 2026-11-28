import Research.R2ScannerMapOwnership.JointWitness
import Lean

open Lean

def connectedRefs (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
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
  let required := #[
    `R2ActualJointStep.initialized_explicit_colon, `R2ActualJointStep.explicit_colon,
    `R2ActualJointStep.landed_sequence_context, `R2ActualJointStep.context_preprocess,
    `R2MapOwnership.Maps.next, `R2MapOwnership.initialized_facts,
    `R2ActualJointWitness.root_context, `R2ActualJointWitness.sibling_content,
    `R2JointFrames.Joint.consume, `R2JointFrames.Context.resume_sequence,
    `L4YAML.Surface.SCompactSeqTail.cons, `L4YAML.Surface.SBlockMapEntry.explicit]
  let forbidden := #[
    `L4YAML.Surface.SLYamlStream.scannerDrop,
    `L4YAML.Surface.SLYamlStream.implicitContinue,
    `L4YAML.Proofs.StreamAccum.dropClose, `sorryAx,
    `R2JointConcrete.initialized_complete, `R2JointConcrete.actual_landed_family,
    `R2CloseConcrete.actual_pack_sibling_then_ancestor]
  let root := `R2ActualJointWitness.initialized_complete
  let deps := connectedRefs env root
  for name in required do
    unless deps.contains name do throwError "connected root misses {name}"
  for name in forbidden do
    if deps.contains name then throwError "connected root uses forbidden shortcut {name}"
  let some info := env.find? root | throwError "closed source proof absent"
  if info.type.isForall then throwError "closed source proof has free input premises"
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  let leaves := #[
    "consumeNewline_line_succ._native.native_decide.ax_1_2",
    "consumeNewline_line_succ._native.native_decide.ax_1_3",
    "isPlainSafe_not_newline._native.native_decide.ax_1_1",
    "isPlainSafe_not_newline._native.native_decide.ax_1_2"]
  let axioms ← collectAxioms root
  let inherited := axioms.filter (!standard.contains ·)
  unless axioms.size == 7 && inherited.size == 4 &&
      leaves.all (fun leaf => inherited.any (·.toString.contains leaf)) do
    throwError "connected axiom boundary changed: {axioms}"
  for pureRoot in [`R2ActualJointStep.context_preprocess,
      `R2ActualJointStep.landed_sequence_context, `R2ActualJointStep.explicit_colon] do
    let pureAxioms ← collectAxioms pureRoot
    unless pureAxioms.size == 3 && pureAxioms.all standard.contains do
      throwError "universal producer profile changed: {pureRoot}: {pureAxioms}"
  logInfo m!"CONNECTED-JOINT-AUDIT required={required.size} forbidden={forbidden.size} dependencies={deps.size} free_route_premises=0 initialized_axioms=standard_three_plus_four_inherited_native_leaves pure_producers=standard_three"
