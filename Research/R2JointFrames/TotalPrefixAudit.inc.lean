
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let some ctor := env.find? `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock
    | throwError "missing actual constructor"
  let rec domain : Lean.Expr → Option Lean.Expr
    | .forallE name ty body _ => if name == `h_kslot then some ty else domain body
    | _ => none
  let some ty := domain ctor.type | throwError "missing actual field"
  unless ty.isForall && !ty.getAppFn.isConstOf ``Or do
    throwError "value-pack field is not required"
  for name in [`R2JointFrames.total_sequence_pack,
      `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0] do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
      throwError "unexpected prefix axioms {name}: {axioms}"
  Lean.logInfo "TOTAL-PACK-PREFIX constructor_field=required actual_flow_opener=checked axioms=3 later_eight_demands=excluded"
