import Research.R2MandatoryContext.Witness
import Lean

open Lean

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
  let root := `R2MandatoryWitness.initialized_complete
  let deps := closure env root
  let required := #[`R2MandatoryContext.actual_first_question,
    `R2MandatoryContext.actual_same_question, `R2MandatoryContext.actual_compact_sequence,
    `R2MandatoryContext.context_content, `R2MandatoryContext.slot_sequence,
    `R2ActualJointStep.explicit_colon, `R2JointFrames.Joint.consume,
    `R2ActualJointStep.landed_sequence_context,
    `L4YAML.Surface.SCompactSeqTail.cons, `L4YAML.Surface.SBlockMapEntry.explicit]
  let forbidden := #[`sorryAx, `L4YAML.Surface.SLYamlStream.scannerDrop,
    `L4YAML.Surface.SLYamlStream.implicitContinue, `L4YAML.Proofs.StreamAccum.dropClose,
    `R2ActualJointWitness.initialized_complete, `R2ActualProducers.initialized_complete,
    `R2JointConcrete.initialized_complete, `R2JointConcrete.actual_landed_family,
    `R2CloseConcrete.actual_pack_sibling_then_ancestor]
  for name in required do unless deps.contains name do throwError "missing real producer {name}"
  for name in forbidden do if deps.contains name then throwError "forbidden shortcut {name}"
  let some info := env.find? root | throwError "initialized root absent"
  if info.type.isForall then throwError "initialized proof has free input premises"
  let pureRoots := #[root, `R2MandatoryContext.actual_first_question,
    `R2MandatoryContext.actual_same_question, `R2MandatoryContext.actual_compact_sequence,
    `R2MandatoryContext.sequence_step, `R2MandatoryContext.actual_nested_sequence,
    `R2MandatoryContext.context_content, `R2MandatoryContext.context_flow,
    `R2MandatoryContext.Sequence.content, `R2MandatoryContext.Sequence.flow_close,
    `R2MandatoryContext.Sequence.properties, `R2MandatoryContext.Node.content,
    `R2MandatoryContext.compact_keyless, `R2MandatoryContext.compact_implicit,
    `R2MandatoryContext.same_map_value]
  for name in pureRoots do
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
      throwError "unexpected axiom boundary {name}: {axioms}"
  logInfo m!"MANDATORY-WITNESS-AUDIT required={required.size} forbidden={forbidden.size} dependencies={deps.size} free_premises=0 pure_roots={pureRoots.size} axioms=standard_three"
