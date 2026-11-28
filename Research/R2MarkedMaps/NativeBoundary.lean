import Research.R2MarkedMaps.Reachable
import Lean

open Lean L4YAML.CharPredicates

-- Independent kernel replays of every inherited native Boolean leaf.
-- They validate the leaves; they do not rewrite the inherited dependency
-- profile of ColFloor or pretend those dependencies are absent.
lemma R2MarkedMaps.lineFeedBool : decide (isLineBreakBool '\n' = true) = true := by decide +kernel
lemma R2MarkedMaps.carriageReturnBool : decide (isLineBreakBool '\r' = true) = true := by decide +kernel
lemma R2MarkedMaps.lineFeedProp : decide (isLineFeedProp '\n') = true := by decide +kernel
lemma R2MarkedMaps.carriageReturnProp : decide (isCarriageReturnProp '\r') = true := by decide +kernel

run_cmd do
  let env := (← getEnv).setExporting false
  let leaves := (← collectAxioms `R2JointFrames.Prefix.invariants).filter fun n =>
    !#[`propext, `Classical.choice, `Quot.sound].contains n
  let replays := #[`R2MarkedMaps.lineFeedBool, `R2MarkedMaps.carriageReturnBool,
    `R2MarkedMaps.lineFeedProp, `R2MarkedMaps.carriageReturnProp]
  unless leaves.size == 4 do throwError "inherited native boundary changed: {leaves}"
  for (leaf, replay) in leaves.zip replays do
    let some old := env.find? leaf | throwError "missing inherited leaf {leaf}"
    let some checked := env.find? replay | throwError "missing kernel replay {replay}"
    unless (← Lean.Elab.Command.liftTermElabM (Lean.Meta.isDefEq old.type checked.type)) do
      throwError "kernel replay does not match native leaf {leaf}"
    unless (← collectAxioms replay).isEmpty do throwError "kernel replay has an axiom: {replay}"
    logInfo m!"INHERITED-NATIVE {leaf}: independently_kernel_replayed={replay}"
  logInfo "NATIVE-BOUNDARY inherited_leaves=4 kernel_replays=4 replay_axioms=0 original_profiles_preserved=true"
