
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock
  let some ci := env.find? ctor | throwError "missing actual constructor"
  if (R2ContinuationProductionAudit.fieldIndex `h_kslot ci.type 0).isSome then
    throwError "redundant h_kslot field remains"
  let some index := R2ContinuationProductionAudit.fieldIndex `h_close_entry ci.type 0
    | throwError "required entry family was removed"
  let rows := [
    (`L4YAML.Proofs.StreamAccum.accum_block_on_noPending,1),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,2),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent,1),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock,3)]
  let mut total : Nat := 0
  for (producer, expected) in rows do
    let some info := env.find? producer | throwError "missing actual producer"
    let some body := info.value? (allowOpaque := true) | throwError "missing actual body"
    let fields := R2ContinuationProductionAudit.fieldTerms ctor
      (R2ContinuationProductionAudit.arity ci.type) index body
    unless fields.size == expected do throwError "actual constructor inventory {producer}: {fields.size}"
    total := total + fields.size
  let mut readers : Nat := 0
  for (name, info) in env.constants.toList do
    if name.getPrefix == `L4YAML.Proofs.StreamAccum then
      if let some body := info.value? (allowOpaque := true) then
        if body.getUsedConstants.contains `R2JointFrames.total_sequence_pack then readers := readers+1
  unless total == 7 && readers == 3 do throwError "actual required-family inventory {total}/{readers}"
  let axioms ← Lean.collectAxioms `R2JointFrames.total_sequence_pack
  unless axioms.size == 3 && axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
    throwError "unexpected required-family projection axioms {axioms}"
  Lean.logInfo "REMOVED-PACK-AUDIT constructor_field=absent actual_writers=7 actual_readers=3 projection_axioms=3 full_migration=unknown"
