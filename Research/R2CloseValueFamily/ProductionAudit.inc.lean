
namespace R2CloseProductionAudit

-- Substitute each local definition before inspecting a constructor argument.
-- A reference to a local name cannot hide a sorry-dependent initializer.
partial def closedArguments (callee : Lean.Name) (count index : Nat)
    (e : Lean.Expr) : Array Lean.Expr := Id.run do
  if e.getAppFn.isConstOf callee && e.getAppNumArgs == count then
    return #[e.getAppArgs[index]!]
  match e with
  | .app f a => return closedArguments callee count index f ++ closedArguments callee count index a
  | .lam _ _ b _ => return closedArguments callee count index b
  | .letE _ _ value body _ =>
    return closedArguments callee count index (body.instantiate1 value)
  | .mdata _ body | .proj _ _ body => return closedArguments callee count index body
  | _ => return #[]

def checkTerm (label : String) (term : Lean.Expr) : Lean.Elab.Command.CommandElabM Unit := do
  let used := term.getUsedConstants
  if used.contains `sorryAx then throwError "{label}: direct sorryAx"
  for name in used do
    if (← Lean.collectAxioms name).contains `sorryAx then
      throwError "{label}: sorry-dependent constant {name}"

end R2CloseProductionAudit

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let producers := #[
    `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0,
    `L4YAML.Proofs.StreamAccum.accum_step_flow,
    `L4YAML.Proofs.StreamAccum.block_dispatch_deferred,
    `L4YAML.Proofs.StreamAccum.content_dispatch_routed,
    `L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented,
    `L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented,
    `L4YAML.Proofs.StreamAccum.accum_content_pending]
  let fields := #[
    (`L4YAML.Proofs.StreamAccum.PendingNode.pendingContent, `h_vpack),
    (`L4YAML.Proofs.StreamAccum.PendingNode.pendingProps, `h_kslot),
    (`L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk, `vslot)]
  let mut total := 0
  for (ctor, field) in fields do
    let some ctorInfo := env.find? ctor | throwError "missing actual constructor {ctor}"
    let some index := R2ContinuationProductionAudit.fieldIndex field ctorInfo.type 0
      | throwError "missing actual field {ctor}.{field}"
    let count := R2ContinuationProductionAudit.arity ctorInfo.type
    let mut writers := 0
    for producer in producers do
      let some info := env.find? producer | throwError "missing actual producer {producer}"
      let some body := info.value? (allowOpaque := true) | throwError "missing body {producer}"
      let terms := R2CloseProductionAudit.closedArguments ctor count index body
      for term in terms do
        R2CloseProductionAudit.checkTerm s!"{producer}/{field}" term
      if !terms.isEmpty then
        Lean.logInfo s!"CLOSE-FIELD {producer} {field} writers={terms.size} sorry_terms=0"
      writers := writers + terms.size
    unless writers > 0 do throwError "unmeasured actual field {field}"
    total := total + writers
    Lean.logInfo s!"CLOSE-FIELD-TOTAL {field} writers={writers} sorry_terms=0"
  let colon := `L4YAML.Proofs.StreamAccum.colon_open_map_explicit
  let some colonInfo := env.find? colon | throwError "missing actual colon"
  let some index := R2ContinuationProductionAudit.fieldIndex `hvp colonInfo.type 0
    | throwError "missing actual whole-value argument"
  let count := R2ContinuationProductionAudit.arity colonInfo.type
  let some caller := env.find? `L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock
    | throwError "missing third caller"
  let some body := caller.value? (allowOpaque := true) | throwError "missing third caller body"
  let terms := R2CloseProductionAudit.closedArguments colon count index body
  unless terms.size == 2 do throwError "third colon reader inventory {terms.size}"
  for term in terms do
    R2CloseProductionAudit.checkTerm "third colon caller whole value" term
    unless term.getUsedConstants.contains `R2UnmarkedOwner.AncestorValue.restrict_state do
      throwError "third caller does not spend actual whole value"
  Lean.logInfo s!"CLOSE-FAMILY-AUDIT field_writers={total} actual_colon_calls=2 sorry_terms=0 local_definitions=substituted"

run_cmd do
  for producer in [
      `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0,
      `L4YAML.Proofs.StreamAccum.accum_step_flow,
      `L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented] do
    let axioms ← Lean.collectAxioms producer
    if axioms.contains `sorryAx then throwError "affected producer retains sorryAx: {producer}"
    Lean.logInfo s!"CLOSE-PRODUCER-AXIOMS {producer} {repr (axioms.map Lean.privateToUserName)}"
