
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let loop := `L4YAML.Proofs.StreamAccum.scanLoop_grammar_prod
  let root := `L4YAML.Proofs.StreamAccum.scan_content_gives_stream_v2
  let some loopInfo := env.find? loop | throwError "missing actual grammar loop"
  let some loopBody := loopInfo.value? (allowOpaque := true) | throwError "missing actual loop body"
  unless loopBody.getUsedConstants.contains `R2MapOwnership.Maps.next do
    throwError "loop does not pay ownership at its real recursive step"
  let some rootInfo := env.find? root | throwError "missing actual top-level scanner entry"
  let some rootBody := rootInfo.value? (allowOpaque := true) | throwError "missing actual entry body"
  unless rootBody.getUsedConstants.contains `R2MapOwnership.seed_maps do
    throwError "actual root does not seed ownership"
  let mut cursor := rootInfo.type
  while let .forallE name domain body _ := cursor do
    if domain.getUsedConstants.contains `R2MapOwnership.Maps then
      throwError "public top-level statement gained ownership premise {name}"
    cursor := body
  let stepAxioms ← Lean.collectAxioms `R2MapOwnership.Maps.next
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  unless stepAxioms.size == 3 && stepAxioms.all allowed.contains do
    throwError "scanner ownership adds axioms {stepAxioms}"
  Lean.logInfo "MAP-THREAD-AUDIT actual_seed=present actual_recursive_step=present public_external_maps_premise=absent step_axioms=standard_three"
