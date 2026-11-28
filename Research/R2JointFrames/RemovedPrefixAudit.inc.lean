
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let some ci := env.find? `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock
    | throwError "missing actual constructor"
  let rec hasField : Lean.Expr → Bool
    | .forallE name _ body _ => name == `h_kslot || hasField body
    | _ => false
  if hasField ci.type then throwError "redundant field remains"
  for name in [`R2JointFrames.total_sequence_pack,
      `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0] do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
      throwError "unexpected prefix axioms {name}: {axioms}"
  Lean.logInfo "REMOVED-PACK-PREFIX constructor_field=absent actual_flow_opener=checked axioms=3 later_eight_demands=excluded"
