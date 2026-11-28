
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let completed := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent
  let props := `L4YAML.Proofs.StreamAccum.PendingNode.pendingProps
  let producers := #[
    `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0,
    `L4YAML.Proofs.StreamAccum.accum_step_flow,
    `L4YAML.Proofs.StreamAccum.block_dispatch_deferred,
    `L4YAML.Proofs.StreamAccum.content_dispatch_routed,
    `L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented,
    `L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented,
    `L4YAML.Proofs.StreamAccum.accum_content_pending]
  let mut completedCount := 0
  let mut propsContextWrites := 0
  for (ctor,field) in #[(completed,`h_closable_entry),(props,`h_routeE)] do
    let some ci := env.find? ctor | throwError "missing actual constructor {ctor}"
    let some index := R2MandatoryProductionAudit.fieldIndex field ci.type 0
      | throwError "missing actual field {field}"
    let mut cursor := ci.type
    let mut whole := false
    while let .forallE name domain body _ := cursor do
      if name == field then whole := domain.getUsedConstants.contains `R2JointFrames.Context
      cursor := body
    unless whole do throwError "field lost whole context {field}"
    for producer in producers do
      let some info := env.find? producer | throwError "missing producer {producer}"
      let some body := info.value? (allowOpaque := true) | throwError "missing actual body {producer}"
      let terms := R2MandatoryProductionAudit.arguments ctor (R2MandatoryProductionAudit.arity ci.type) index body
      let mut enriched := 0
      for term in terms do
        unless ← R2MandatoryProductionAudit.clean term do throwError "sorry-dependent actual field {producer}/{field}"
        if term.getUsedConstants.contains `R2MandatoryContext.context_content then enriched := enriched+1
      if field == `h_closable_entry then
        unless enriched == terms.size do throwError "completed field bypassed actual scanner transport"
        completedCount := completedCount + terms.size
      else propsContextWrites := propsContextWrites + enriched
      if !terms.isEmpty then
        Lean.logInfo s!"COMPLETION-FIELD {producer} {field} terms={terms.size} context_transports={enriched} sorry_terms=0"
  unless completedCount > 0 && propsContextWrites > 0 do throwError "missing actual context writes"
  let some sibling := env.find? `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent
    | throwError "completed sibling reader absent"
  let some siblingBody := sibling.value? (allowOpaque := true) | throwError "reader body absent"
  unless siblingBody.getUsedConstants.contains `R2MandatoryContext.sequence_step do
    throwError "completed sibling did not spend actual scanner adapter"
  let pureAxioms ← Lean.collectAxioms `R2MandatoryContext.context_content
  unless pureAxioms.size == 3 && pureAxioms.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
    throwError "context transport axiom boundary {pureAxioms}"
  for name in [
      `L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented,
      `L4YAML.Proofs.StreamAccum.accum_content_pending] do
    let axs ← Lean.collectAxioms name
    if axs.contains `sorryAx then throwError "actual completion producer contains sorryAx {name}"
    Lean.logInfo s!"COMPLETION-PRODUCER {name} axioms={repr axs}"
  Lean.logInfo s!"COMPLETION-CONTEXT-AUDIT completed_terms={completedCount} property_context_writes={propsContextWrites} sorry_terms=0 actual_sibling_reader=connected critical_retirements=0"
