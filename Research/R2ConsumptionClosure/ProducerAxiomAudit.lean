import L4YAML.Proofs.Production.StreamAccum
#print axioms L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented

run_cmd do
  let axioms ← Lean.collectAxioms `L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented
  Lean.logInfo s!"RAW-PRODUCER-AXIOMS {repr axioms}"
