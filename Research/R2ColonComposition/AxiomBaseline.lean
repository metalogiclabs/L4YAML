import L4YAML.Proofs.Production.StreamAccum

run_cmd do
  for (label, root) in [("COLON", `L4YAML.Proofs.StreamAccum.colon_open_map_explicit),
      ("COMPACT", `L4YAML.Proofs.StreamAccum.compact_open_map),
      ("COMPLETION", `L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented)] do
    let axioms ← Lean.collectAxioms root
    if axioms.contains `sorryAx then throwError "accepted baseline contains sorryAx"
    Lean.logInfo s!"RAW-{label}-AXIOMS {repr axioms}"
