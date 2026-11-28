
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let producer := `L4YAML.Proofs.StreamAccum.colon_open_map_explicit
  let some info := env.find? producer | throwError "missing actual colon producer"
  let some body := info.value? (allowOpaque := true) | throwError "missing checked producer body"
  for required in [`R2UnmarkedOwner.AncestorValue.payloads,
      `R2ValueOwnership.scanValue_own_unmarked] do
    unless body.getUsedConstants.contains required do throwError "actual colon omits {required}"
  let axioms ← Lean.collectAxioms producer
  let expected := #[`propext, `Classical.choice, `Quot.sound,
    `L4YAML.Proofs.StreamAccum.dispatchBlockValue_full_prod._native.native_decide.ax_1_2,
    `L4YAML.Proofs.StreamAccum.dispatchBlockValue_full_prod._native.native_decide.ax_1_3]
  -- These two native leaves are private to the actual source module. Bind
  -- the raw names to the loaded dispatch helper; use Lean's own user-name
  -- projection only to verify the exact permitted leaf inventory.
  let dispatchAxioms ← Lean.collectAxioms
    `L4YAML.Proofs.StreamAccum.dispatchBlockValue_full_prod
  let userAxioms := dispatchAxioms.map Lean.privateToUserName
  unless userAxioms.size == expected.size && userAxioms.all expected.contains &&
      expected.all userAxioms.contains do throwError "unexpected dispatch leaves {dispatchAxioms}"
  unless axioms.size == dispatchAxioms.size && axioms.all dispatchAxioms.contains &&
      dispatchAxioms.all axioms.contains do
    throwError "composed colon adds axioms beyond its actual dispatch helper {axioms}"
  let some caller := env.find? `L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock
    | throwError "missing integrated landed caller"
  let some callerBody := caller.value? (allowOpaque := true) | throwError "missing integrated caller body"
  unless callerBody.getUsedConstants.contains
      `L4YAML.Proofs.R2LandedContinuation.SlotValues.landed_sequence do
    throwError "integrated caller omits parallel landed family"
  Lean.logInfo "COMPOSITION-AUDIT colon_helpers=2/2 axioms=5 sorryAx=absent actual_landed_reader=present"
