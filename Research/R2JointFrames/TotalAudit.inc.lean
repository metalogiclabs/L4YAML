
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock
  let some ci := env.find? ctor | throwError "missing actual pending block constructor"
  let rec domain : Lean.Expr → Option Lean.Expr
    | .forallE name ty body _ => if name == `h_kslot then some ty else domain body
    | _ => none
  let some ty := domain ci.type | throwError "missing actual h_kslot field"
  if ty.getAppFn.isConstOf ``Or then throwError "critical field is still optional"
  unless ty.isForall do throwError "critical field is not a total route"
  let some index := R2ContinuationProductionAudit.fieldIndex `h_kslot ci.type 0
    | throwError "missing actual field index"
  let rows := [
    (`L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,2),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent,1),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock,3)]
  let mut total := 0
  for (producer, count) in rows do
    let some info := env.find? producer | throwError "missing actual producer"
    let some body := info.value? (allowOpaque := true) | throwError "missing actual body"
    let fields := R2ContinuationProductionAudit.fieldTerms ctor
      (R2ContinuationProductionAudit.arity ci.type) index body
    unless fields.size == count do throwError "actual writer inventory changed: {producer} {fields.size}"
    for term in fields do
      unless term.getUsedConstants.contains `R2JointFrames.total_sequence_pack do
        throwError "actual field does not derive from required entry proof"
      for name in term.getUsedConstants do
        if name == `sorryAx || (← Lean.collectAxioms name).contains `sorryAx then
          throwError "actual total projection has sorry-dependent constant {name}"
    total := total + fields.size
  -- The seventh birth is the no-pending root producer. Count it independently
  -- over the complete source environment instead of guessing its private name.
  let mut all := 0
  for (name, info) in env.constants.toList do
    if name.getPrefix == `L4YAML.Proofs.StreamAccum then
      if let some body := info.value? (allowOpaque := true) then
        let fields := R2ContinuationProductionAudit.fieldTerms ctor
          (R2ContinuationProductionAudit.arity ci.type) index body
        all := all + fields.size
  unless total == 6 && all == 7 do throwError "total actual writer inventory {total}/{all}"
  let axioms ← Lean.collectAxioms `R2JointFrames.total_sequence_pack
  unless axioms.size == 3 && axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
    throwError "unexpected total projection axioms {axioms}"
  Lean.logInfo "TOTAL-PACK-AUDIT constructor_field=required actual_writers=7 projection_axioms=3 new_external_family=absent full_migration=unknown"
