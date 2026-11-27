import L4YAML.Proofs.Production.DocumentProduction
import Scripts.Path.CapstonePath
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let reached := Scripts.Path.CapstonePath.reach env Scripts.Path.CapstonePath.roots
  let newProof := `L4YAML.Proofs.StreamAccum.marked_col_of_explicit_source
  unless reached.contains newProof do throwError "new actual-state proof is not consumed"
  let retired := `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol
  if reached.contains retired then throwError "off-column escape remains on the capstone path"
  for n in [retired, `L4YAML.Proofs.StreamAccum.frameChainOne] do
    if env.contains n then throwError "unused helper remains in the library: {n}"
  let axs ← liftCoreM (collectAxioms newProof)
  for a in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains a do
      throwError "new proof added an axiom: {a}"
  logInfo "CONTENT_SLOT_IMPACT new_state_correspondence_consumed=true offcol_escape_on_capstone=false"
  logInfo "CONTENT_SLOT_RETIREMENT library_offcol_wrapper=false library_singleton_helper=false"
  logInfo m!"CONTENT_SLOT_NEW_AXIOMS {axs}"

