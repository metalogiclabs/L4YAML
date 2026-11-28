
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let producer := `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0
  let ctor := `L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk
  let some info := env.find? producer | throwError "missing actual flow opener"
  let some body := info.value? (allowOpaque := true) | throwError "missing actual flow body"
  let some ci := env.find? ctor | throwError "missing actual flow routes constructor"
  let some index := R2SequenceWriteAudit.fieldIndex `value ci.type 0
    | throwError "missing actual value field"
  let fields := R2SequenceWriteAudit.initializers ctor (R2SequenceWriteAudit.arity ci.type) index body
  let mut clean := 0
  let mut transported := 0
  for term in fields do
    let used := term.getUsedConstants
    let mut okay := !used.contains `sorryAx
    for constant in used do
      if (← Lean.collectAxioms constant).contains `sorryAx then okay := false
    if okay then
      clean := clean+1
      if used.contains `L4YAML.Proofs.StreamAccum.R2Mandatory.Full.of_eq then
        transported := transported+1
  Lean.logInfo s!"FLOW-WRITER-AUDIT expanded_fields={fields.size} clean_fields={clean} transported_fields={transported} global_acceptance=false critical_retirements=0"
  let some closeInfo := env.find? `L4YAML.Proofs.StreamAccum.accum_step_flow
    | throwError "missing actual flow close reader"
  let some closeBody := closeInfo.value? (allowOpaque := true) | throwError "missing flow close body"
  unless closeBody.getUsedConstants.contains `L4YAML.Proofs.StreamAccum.R2Mandatory.Full.of_eq do
    throwError "close readers lost real scanner transport"
  let axs ← Lean.collectAxioms `L4YAML.Proofs.StreamAccum.R2Mandatory.Full.of_eq
  unless !axs.isEmpty && axs.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
    throwError "flow transport axiom boundary {axs}"
  Lean.logInfo s!"FLOW-CLOSE-AUDIT actual_reader=connected transport_axioms={repr axs} public_context_premises_added=0"
