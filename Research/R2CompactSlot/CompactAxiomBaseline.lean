import L4YAML.Proofs.Production.StreamAccum
run_cmd do
  let axioms ← Lean.collectAxioms `L4YAML.Proofs.StreamAccum.compact_open_map
  Lean.logInfo s!"RAW-COMPACT-AXIOMS {repr axioms}"

run_cmd do
  let env ← Lean.getEnv
  let some ctor := env.find? `L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue
    | throwError "missing accepted constructor"
  let mut cursor := ctor.type
  while let .forallE name domain body _ := cursor do
    if name == `h_vslot && domain.getUsedConstants.contains
        `L4YAML.Proofs.R2ConsumptionClosure.EntryValues then
      throwError "accepted control unexpectedly stores the wide family"
    cursor := body
  let some compact := env.find? `L4YAML.Proofs.StreamAccum.compact_open_map
    | throwError "missing accepted compact producer"
  let some value := compact.value? (allowOpaque := true)
    | throwError "accepted compact producer has no body"
  if value.getUsedConstants.contains `L4YAML.Proofs.R2CompactSlot.SlotValues.compact_question then
    throwError "accepted control unexpectedly uses the new wide context"
  Lean.logInfo "LEGACY-COMPACT-CONTROL wide_storage=absent compact_reader=absent"
