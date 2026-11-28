import Research.R2ContinuationContract.TwoAncestors
import Lean

open Lean

run_cmd do
  let env := (← getEnv).setExporting false
  let top := `L4YAML.Proofs.StreamAccum.ValueOwnership.TopUnmarked
  let ownerProof := `L4YAML.Proofs.StreamAccum.ValueOwnership.scanValue_top_unmarked
  unless env.contains top && env.contains ownerProof do
    throwError "this is not the qualified #392 ownership interface"
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue
  let some info := env.find? ctor | throwError "missing actual map-value constructor"
  let mut cursor := info.type
  let mut retained := false
  while let .forallE field domain rest _ := cursor do
    if field == `h_expl && domain.getUsedConstants.contains top then retained := true
    cursor := rest
  unless retained do throwError "qualified ownership evidence absent from actual h_expl"
  let root := `R2ContinuationTwoAncestors.actual_completed_sibling_two_ancestor_values
  for name in [ownerProof, root] do
    for axiomName in (← collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "unexpected owner/replay axiom {axiomName}"
  logInfo "QUALIFIED-OWNER-BINDING TopUnmarked=present actual_h_expl=retained witness_axioms=standard_three_only"
