
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let root := `L4YAML.Proofs.StreamAccum.colon_open_map_explicit
  let some producer := env.find? root | throwError "missing actual explicit-colon producer"
  let some body := producer.value? (allowOpaque := true) | throwError "producer has no body"
  for required in [`R2ColonComposition.colon_payload_of_step,
      `L4YAML.Proofs.StreamAccum.ValueOwnership.no_mark_at_or_above_top,
      `L4YAML.Proofs.PendingKeySound.scanValue_sound,
      `L4YAML.Proofs.RegisterWitness.scanValue_markedCols] do
    unless env.contains required do throwError "unknown expected dependency {required}"
    unless body.getUsedConstants.contains required do
      throwError "explicit colon does not spend {required}"
  let mut cursor := producer.type
  let mut entry := false
  let mut prepSound := false
  while let .forallE name domain rest _ := cursor do
    if name == `h_entry then
      entry := domain.getUsedConstants.contains `L4YAML.Proofs.R2ConsumptionClosure.EntryStep
    if name == `h_sound_prep then
      prepSound := domain.getUsedConstants.contains `L4YAML.Proofs.PendingKeySound.Sound
    cursor := rest
  unless entry && prepSound do throwError "producer interface does not expose exact supplied obligations"
  let axioms ← Lean.collectAxioms root
  if axioms.contains `sorryAx then throwError "explicit colon contains sorryAx"
  Lean.logInfo s!"RAW-COLON-AXIOMS {repr axioms}"
  Lean.logInfo "COLON-PRODUCER-AUDIT composition=present ownership=spent backward_domain=spent entry_supplier=mandatory sound_supplier=mandatory sorryAx=absent"
