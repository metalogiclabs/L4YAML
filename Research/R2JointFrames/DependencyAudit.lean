import Research.R2JointFrames.Omitted
import Research.R2JointFrames.Separation
import Research.R2JointFrames.TotalPack
import Research.R2ContentCompletion.DependencyAudit

open Lean

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[`R2JointConcrete.initialized_complete,
    `R2JointOmitted.initialized_complete,
    `R2JointConcrete.actual_landed_family,
    `R2JointOmitted.actual_landed_family]
  let required := #[`R2JointFrames.Joint.question,
    `R2JointFrames.Context.resume_sequence,
    `R2JointFrames.Joint.sibling_sequence,
    `R2JointFrames.Slot.compact_sequence,
    `R2JointFrames.Slot.compact_question,
    `L4YAML.Surface.SLYamlStream.single,
    `L4YAML.Surface.SBlockMapEntry.explicitEmpty,
    `L4YAML.Surface.SCompactSeqTail.cons]
  let forbidden := #[`sorryAx, `L4YAML.Surface.SLYamlStream.scannerDrop,
    `L4YAML.Surface.SLYamlStream.implicitContinue,
    `L4YAML.Proofs.StreamAccum.dropClose,
    `R2ConcreteSequences.Sibling.actual_sibling_then_ancestor,
    `R2ConcreteSequences.SequenceQuestion.actual_sequence_question_consumption]
  for root in roots do
    let some info := env.find? root | throwError "missing checked root {root}"
    if info.type.isForall then throwError "free premise on initialized proof {root}"
    let (used, missing) := R2CompletionAudit.dependencies env [root]
    unless missing.isEmpty do throwError "unresolved dependencies {missing}"
    for name in required do
      unless env.contains name && used.contains name do throwError "missing actual constructor/reader {name}"
    for name in forbidden do
      unless env.contains name do throwError "unresolved forbidden name {name}"
      if used.contains name then throwError "forbidden shortcut {name}"
    let axioms ← collectAxioms root
    for name in axioms do
      unless #[`propext,`Classical.choice,`Quot.sound].contains name do throwError "unexpected axiom {name}"
    logInfo s!"JOINT-INITIALIZED-AUDIT {root}: constants={used.size} required={required.size} forbidden={forbidden.size} missing=0 free_premises=0 axioms={axioms.map Name.toString}"
  for root in [`R2JointSeparation.flat_without_joint,
      `R2JointSeparation.no_uniform_reconstruction,
      `R2JointFrames.total_sequence_pack] do
    let axioms ← collectAxioms root
    for name in axioms do
      unless #[`propext,`Classical.choice,`Quot.sound].contains name do throwError "unexpected axiom {name}"
  logInfo "JOINT-BOUNDARY-AUDIT uniform_flat_reconstruction=refuted generic_P_only=true total_pack=checked critical_retirements=0"
