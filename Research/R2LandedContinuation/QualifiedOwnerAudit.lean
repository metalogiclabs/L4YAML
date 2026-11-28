import Research.R2LandedContinuation.DependencyAudit
import Lean

open Lean

run_cmd do
  let env := (← getEnv).setExporting false
  let top := `L4YAML.Proofs.StreamAccum.ValueOwnership.TopUnmarked
  let ownerProof := `L4YAML.Proofs.StreamAccum.ValueOwnership.scanValue_top_unmarked
  unless env.contains top && env.contains ownerProof do
    throwError "this is not the frozen qualified #392 ownership interface"
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue
  let some info := env.find? ctor | throwError "missing actual map-value constructor"
  let mut cursor := info.type
  let mut retained := false
  while let .forallE field domain rest _ := cursor do
    if field == `h_expl && domain.getUsedConstants.contains top then retained := true
    cursor := rest
  unless retained do throwError "qualified ownership evidence absent from actual h_expl"
  for root in [ownerProof, `R2LandedTwoAncestors.actual_landed_tail_two_ancestor_values,
      `L4YAML.Proofs.R2LandedContinuation.SlotValues.landed_sequence] do
    for name in (← collectAxioms root) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains name do
        throwError "unexpected owner/landed replay axiom {name}"
  logInfo "QUALIFIED-LANDED-BINDING TopUnmarked=present actual_h_expl=retained landed_witness=checked standard_axioms_only=true"
