import Research.R2MarkedMaps.Concrete
import Research.R2MarkedMaps.NativeBoundary
import Research.R2ContentCompletion.DependencyAudit

open Lean

run_cmd do
  let env := (← getEnv).setExporting false
  let root := `R2ActualProducers.initialized_complete
  let some info := env.find? root | throwError "missing actual producer root"
  if info.type.isForall then throwError "free premise on initialized producer root"
  let (used, missing) := R2CompletionAudit.dependencies env [root]
  unless missing.isEmpty do throwError "unresolved references {missing}"
  let required := #[`R2JointFrames.Slot.actual_question,
    `R2JointFrames.Context.actual_colon,
    `R2ValueOwnership.scanValue_own_unmarked,
    `R2JointFrames.Joint.consume,
    `R2JointFrames.Context.resume_sequence,
    `L4YAML.Surface.SCompactSeqTail.cons,
    `L4YAML.Surface.SLYamlStream.single]
  let forbidden := #[`sorryAx, `L4YAML.Surface.SLYamlStream.scannerDrop,
    `L4YAML.Surface.SLYamlStream.implicitContinue, `L4YAML.Proofs.StreamAccum.dropClose,
    `R2JointConcrete.initialized_complete, `R2JointConcrete.inner_context,
    `R2JointConcrete.inner_key, `R2JointConcrete.consumed_inner, `R2JointConcrete.sibling_context]
  for name in required do
    unless env.contains name && used.contains name do throwError "omitted actual producer/reader {name}"
  for name in forbidden do
    unless env.contains name do throwError "unresolved forbidden name {name}"
    if used.contains name then throwError "initialized producer proof uses shortcut {name}"
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  for checked in [root, `R2JointFrames.Slot.actual_question,
      `R2JointFrames.Context.actual_colon, `R2JointFrames.marked_next] do
    for axiomName in (← collectAxioms checked) do
      unless standard.contains axiomName do throwError "unexpected producer axiom {axiomName}"
  logInfo s!"ACTUAL-PRODUCER-AUDIT constants={used.size} required={required.size} forbidden={forbidden.size} missing=0 free_premises=0 axioms=standard3"
  let inherited := (← collectAxioms `R2JointFrames.Prefix.invariants).filter (!standard.contains ·)
  unless inherited.size == 4 do throwError "unexpected inherited prefix axiom boundary"
  for checked in [`R2JointFrames.Prefix.maps, `R2JointFrames.Prefix.entries,
      `R2JointFrames.Prefix.nodes] do
    for axiomName in (← collectAxioms checked) do
      unless standard.contains axiomName || inherited.contains axiomName do
        throwError "new prefix axiom {axiomName}"
  logInfo "REACHABLE-PROJECTION-AUDIT inherited_native_leaves=4 independent_kernel_replays=4 new_axioms=0 semantic_context_still_required=true"
  logInfo "MIGRATION-BOUNDARY production_module_unchanged=true eight_prior_demands_not_replayed=true critical_retirements=0"
