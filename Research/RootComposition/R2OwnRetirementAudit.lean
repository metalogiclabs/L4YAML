import L4YAML.Proofs.Production.DocumentProduction
import Scripts.Path.CapstonePath
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let reached := Scripts.Path.CapstonePath.reach env Scripts.Path.CapstonePath.roots
  for n in [`L4YAML.Proofs.RegisterWitness.r2_value_excludes_top_column,
      `L4YAML.Proofs.StreamAccum.scanKey_questionPark] do
    unless reached.contains n do throwError "new scanner fact is not consumed by capstones: {n}"
    let axs ← liftCoreM (collectAxioms n)
    for a in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "unexpected axiom {a} in {n}"
#print axioms L4YAML.Proofs.RegisterWitness.r2_value_excludes_top_column
