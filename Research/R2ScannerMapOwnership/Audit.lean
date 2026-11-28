import Research.R2ScannerMapOwnership.Bridge
import Lean

open Lean

run_cmd do
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  for root in [`R2MapOwnership.Maps.next,
      `R2MapOwnership.sound_does_not_imply_maps] do
    let axioms ← collectAxioms root
    unless axioms.size == 3 && axioms.all standard.contains do
      throwError "unexpected axioms at {root}: {axioms}"
  let nativeLeaves := #[
    "consumeNewline_line_succ._native.native_decide.ax_1_2",
    "consumeNewline_line_succ._native.native_decide.ax_1_3",
    "isPlainSafe_not_newline._native.native_decide.ax_1_1",
    "isPlainSafe_not_newline._native.native_decide.ax_1_2"]
  for root in [`R2MapOwnership.initialized_facts, `R2MapOwnership.initialized_maps,
      `R2MapOwnership.initialized_joint_entries, `R2MapOwnership.counterfeit_not_initialized] do
    let axioms ← collectAxioms root
    let inherited := axioms.filter (!standard.contains ·)
    unless axioms.size == 7 && inherited.size == 4 &&
        nativeLeaves.all (fun leaf => inherited.any (·.toString.contains leaf)) do
      throwError "initialized profile changed at {root}: {axioms}"
  logInfo "MAP-OWNERSHIP-AXIOMS step=standard_three separation=standard_three initialized=standard_three_plus_four_inherited_native_leaves custom=0 sorryAx=0"
