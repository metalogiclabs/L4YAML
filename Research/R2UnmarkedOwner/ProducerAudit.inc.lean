
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let cases := [
    (`L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock, 2),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock, 1),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock, 3),
    (`L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent, 3),
    (`L4YAML.Proofs.StreamAccum.accum_content_pending,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent, 3)]
  let mut total := 0
  for (producer, ctor, expected) in cases do
    let some ctorInfo := env.find? ctor | throwError "missing constructor"
    let some index := R2ContinuationProductionAudit.fieldIndex `h_kslotUp ctorInfo.type 0
      | throwError "missing actual ancestor field"
    let count := R2ContinuationProductionAudit.arity ctorInfo.type
    let some info := env.find? producer | throwError "missing producer"
    let some body := info.value? (allowOpaque := true) | throwError "missing checked body"
    let terms := R2ContinuationProductionAudit.fieldTerms ctor count index body
    unless terms.size == expected do throwError "ancestor writer inventory {producer}: {terms.size} expected {expected}"
    for term in terms do
      let names := term.getUsedConstants
      unless names.contains `R2UnmarkedOwner.AncestorValue.of_entries ||
          names.contains `R2UnmarkedOwner.AncestorValue.restrict_state do
        throwError "actual writer omitted retained family"
      if names.contains `sorryAx then throwError "actual ancestor field directly contains sorryAx"
      for name in names do
        if (← Lean.collectAxioms name).contains `sorryAx then
          throwError "actual ancestor field references sorry-dependent constant {name}"
    total := total + terms.size
  for consumer in [`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent,
      `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock] do
    let some info := env.find? consumer | throwError "missing actual colon caller"
    let some body := info.value? (allowOpaque := true) | throwError "missing checked caller body"
    unless body.getUsedConstants.contains `R2UnmarkedOwner.AncestorValue.pair do
      throwError "actual caller omitted family reader"
    let mut cursor := info.type
    while let .forallE name domain next _ := cursor do
      if domain.getUsedConstants.contains `L4YAML.Proofs.StreamAccum.R2KeyPairAt then
        throwError "external pair parameter added: {name}"
      cursor := next
  Lean.logInfo s!"UNMARKED-OWNER-FIELDS checked={total} sorry_terms=0 actual_pair_readers=2 new_external_pair=0"

#print axioms R2UnmarkedOwner.AncestorValue.of_entries
#print axioms R2UnmarkedOwner.AncestorValue.restrict_state
#print axioms R2UnmarkedOwner.AncestorValue.pair
