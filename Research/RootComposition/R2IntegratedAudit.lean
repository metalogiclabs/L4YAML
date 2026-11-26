import L4YAML.Proofs.Production.StreamAccum
open Lean Elab Command
run_cmd do
  for n in [`L4YAML.Proofs.RegisterWitness.r2_value_excludes_top_column,
      `L4YAML.Proofs.StreamAccum.scanKey_questionPark] do
    let axs ← liftCoreM (collectAxioms n)
    for a in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "unexpected axiom {a} in {n}"
#print axioms L4YAML.Proofs.RegisterWitness.r2_value_excludes_top_column
