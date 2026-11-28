
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [`L4YAML.Proofs.StreamAccum.accum_flow_open_depth0,
      `R2CloseValueFamily.pairAt_of_route, `R2CloseValueFamily.wholePack] do
    let some _ := env.find? name | throwError "missing actual declaration {name}"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "unexpected prefix proof axioms {name}: {axioms}"
  for (ctor, field) in [
      (`L4YAML.Proofs.StreamAccum.PendingNode.pendingContent, `h_vpack),
      (`L4YAML.Proofs.StreamAccum.PendingNode.pendingProps, `h_kslot),
      (`L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk, `vslot),
      (`L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue, `h_explUp)] do
    let some info := env.find? ctor | throwError "missing actual constructor {ctor}"
    let rec domain : Lean.Expr → Option Lean.Expr
      | .forallE name ty body _ => if name == field then some ty else domain body
      | _ => none
    let some ty := domain info.type | throwError "missing actual field {field}"
    unless ty.getUsedConstants.contains `R2UnmarkedOwner.AncestorValue ||
        ty.getUsedConstants.contains `L4YAML.Proofs.R2InvariantPayload.NodeValues do
      throwError "whole family absent from actual field {ctor}.{field}"
  Lean.logInfo "ACCEPTED-PREFIX strong_fields=4 actual_flow_opener=checked axioms=3 sorryAx=absent later_failed_declarations=excluded"

#print axioms L4YAML.Proofs.StreamAccum.accum_flow_open_depth0
