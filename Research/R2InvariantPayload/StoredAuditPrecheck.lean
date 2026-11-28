import L4YAML.Proofs.Production.StreamAccum
run_cmd do
  let env ← Lean.getEnv
  let nodeName := `L4YAML.Proofs.R2InvariantPayload.NodeValues
  let ctorName := `L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue
  let some ctor := env.find? ctorName | throwError "missing pending-value constructor"
  let mut cursor := ctor.type
  let mut stored : Array Lean.Name := #[]
  while let .forallE name domain body _ := cursor do
    if domain.getUsedConstants.contains nodeName then stored := stored.push name
    cursor := body
  unless stored.isEmpty do throwError "legacy control unexpectedly has stored context {stored}"
  let producerName := `L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented
  let some producer := env.find? producerName | throwError "missing actual producer"
  let some value := producer.value? (allowOpaque := true) | throwError "producer has no checked body"
  let refs := value.getUsedConstants
  for required in [`L4YAML.Proofs.R2InvariantPayload.NodeValues.framed_ancestor,
      `L4YAML.Proofs.R2InvariantPayload.own_frame_cover] do
    if refs.contains required then throwError "legacy control unexpectedly spends new reader {required}"
  let mut parameterCursor := producer.type
  let mut parameters : Array Lean.Name := #[]
  while let .forallE name _ body _ := parameterCursor do
    parameters := parameters.push name
    parameterCursor := body
  if parameters.contains `h_entries then throwError "old extra context premise remains"
  if parameters.contains `h_top_old then throwError "legacy control unexpectedly has the new top parameter"
  let callerName := `L4YAML.Proofs.StreamAccum.accum_content_pending
  let some caller := env.find? callerName | throwError "missing actual caller"
  let some callerBody := caller.value? (allowOpaque := true) | throwError "caller has no body"
  unless callerBody.getUsedConstants.contains producerName do throwError "caller bypasses producer"
  Lean.logInfo "LEGACY-CONTROL stored_contexts=0 frame_spenders=0/2 top_parameter=absent actual_caller=connected"
