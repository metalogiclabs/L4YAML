import L4YAML.Proofs.Production.DocumentProduction
import Scripts.Path.CapstonePath
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let reached := Scripts.Path.CapstonePath.reach env Scripts.Path.CapstonePath.roots
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for n in [`L4YAML.Proofs.StreamAccum.accum_block_on_noPending,
      `L4YAML.Proofs.StreamAccum.accum_content_on_noPending,
      `L4YAML.Proofs.StreamAccum.content_dispatch_routed,
      `L4YAML.Proofs.DocumentProduction.scan_strict_proof,
      `L4YAML.Proofs.DocumentProduction.parse_strict_proof] do
    unless reached.contains n do throwError "root proof is not consumed: {n}"
    let axioms ← liftCoreM (collectAxioms n)
    for a in axioms do
      unless standard.contains a || (a.toString.splitOn "._native.native_decide.ax_").length > 1 do
        throwError "unexpected axiom: {n} {a}"
    for a in axioms.qsort (fun a b => a.toString < b.toString) do
      logInfo m!"ROOT_AXIOM {n} {a}"
