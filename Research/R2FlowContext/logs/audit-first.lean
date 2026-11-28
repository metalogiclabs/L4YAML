
namespace R2FlowAudit

def dependencies (env : Lean.Environment) (root : Lean.Name) : Std.HashSet Lean.Name := Id.run do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      todo := info.type.getUsedConstants.toList ++ todo
      if let some value := info.value? (allowOpaque := true) then
        todo := value.getUsedConstants.toList ++ todo
  return seen

def clean (term : Lean.Expr) : Lean.CoreM Bool := do
  let used := term.getUsedConstants
  if used.contains `sorryAx then return false
  for constant in used do
    if (← Lean.collectAxioms constant).contains `sorryAx then return false
  return true

end R2FlowAudit

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
    if ← R2FlowAudit.clean term then
      clean := clean+1
      if used.contains `L4YAML.Proofs.StreamAccum.R2Mandatory.Full.of_eq then
        transported := transported+1
        for constant in used do
          let deps := R2FlowAudit.dependencies env constant
          for forbidden in #[`sorryAx, `L4YAML.Surface.SLYamlStream.scannerDrop,
              `L4YAML.Surface.SLYamlStream.implicitContinue,
              `L4YAML.Proofs.StreamAccum.dropClose] do
            if deps.contains forbidden then
              throwError "transported field uses forbidden shortcut {forbidden} via {constant}"
  unless fields.size == 13 && clean == 8 && transported == 5 do
    throwError "actual writer inventory changed {fields.size}/{clean}/{transported}"
  Lean.logInfo s!"FLOW-WRITER-AUDIT expanded_fields={fields.size} clean_fields={clean} transported_fields={transported} global_acceptance=false critical_retirements=0"
  let some closeInfo := env.find? `L4YAML.Proofs.StreamAccum.accum_step_flow
    | throwError "missing actual flow close reader"
  let some closeBody := closeInfo.value? (allowOpaque := true) | throwError "missing flow close body"
  unless closeBody.getUsedConstants.contains `L4YAML.Proofs.StreamAccum.R2Mandatory.Full.of_eq do
    throwError "close readers lost real scanner transport"
  let pendingCtor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingContent
  let some pendingInfo := env.find? pendingCtor | throwError "missing completed-content constructor"
  let some closeIndex := R2SequenceWriteAudit.fieldIndex `h_closable pendingInfo.type 0
    | throwError "missing actual close field"
  let readers := R2SequenceWriteAudit.initializers pendingCtor
    (R2SequenceWriteAudit.arity pendingInfo.type) closeIndex closeBody
  let mut cleanReaders := 0
  let mut transportedReaders := 0
  for reader in readers do
    if ← R2FlowAudit.clean reader then
      cleanReaders := cleanReaders+1
      if reader.getUsedConstants.contains `L4YAML.Proofs.StreamAccum.R2Mandatory.Full.of_eq then
        transportedReaders := transportedReaders+1
  Lean.logInfo s!"FLOW-CLOSE-FIELDS expanded={readers.size} clean={cleanReaders} transported={transportedReaders}"
  let axs ← Lean.collectAxioms `L4YAML.Proofs.StreamAccum.R2Mandatory.Full.of_eq
  unless !axs.isEmpty && axs.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
    throwError "flow transport axiom boundary {axs}"
  Lean.logInfo s!"FLOW-CLOSE-AUDIT actual_reader=connected transport_axioms={repr axs} public_context_premises_added=0"
