
namespace R2CloseProductionAudit

def fieldIndex (field : Lean.Name) : Lean.Expr → Nat → Option Nat
  | .forallE name _ body _, n => if name == field then some n else fieldIndex field body (n+1)
  | _, _ => none

def arity : Lean.Expr → Nat
  | .forallE _ _ body _ => arity body + 1
  | _ => 0

partial def fieldTerms (ctor : Lean.Name) (count index : Nat) (e : Lean.Expr) : Array Lean.Expr := Id.run do
  if e.getAppFn.isConstOf ctor && e.getAppNumArgs == count then return #[e.getAppArgs[index]!]
  match e with
  | .app f a => return fieldTerms ctor count index f ++ fieldTerms ctor count index a
  | .lam _ _ b _ => return fieldTerms ctor count index b
  | .letE _ _ value body _ => return fieldTerms ctor count index value ++ fieldTerms ctor count index body
  | .mdata _ b | .proj _ _ b => return fieldTerms ctor count index b
  | _ => return #[]

end R2CloseProductionAudit

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for (ctor, field) in [
      (`L4YAML.Proofs.StreamAccum.PendingNode.pendingContent, `h_vpack),
      (`L4YAML.Proofs.StreamAccum.PendingNode.pendingProps, `h_kslot),
      (`L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk, `vslot)] do
    let some info := env.find? ctor | throwError "missing actual constructor {ctor}"
    let rec domain : Lean.Expr → Option Lean.Expr
      | .forallE name ty body _ => if name == field then some ty else domain body
      | _ => none
    let some ty := domain info.type | throwError "missing actual field {field}"
    unless ty.getUsedConstants.contains `R2UnmarkedOwner.AncestorValue do
      throwError "actual field does not retain whole value {ctor}.{field}"
  let cases := [
    (`L4YAML.Proofs.StreamAccum.accum_step_flow,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingContent, `h_vpack, 2),
    (`L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingContent, `h_vpack, 3),
    (`L4YAML.Proofs.StreamAccum.accum_content_pending,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingContent, `h_vpack, 5),
    (`L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingProps, `h_kslot, 1),
    (`L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingProps, `h_kslot, 1),
    (`L4YAML.Proofs.StreamAccum.accum_content_pending,
      `L4YAML.Proofs.StreamAccum.PendingNode.pendingProps, `h_kslot, 2)]
  let mut total := 0
  for (producer, ctor, field, expected) in cases do
    let some ctorInfo := env.find? ctor | throwError "missing constructor"
    let some index := R2CloseProductionAudit.fieldIndex field ctorInfo.type 0 | throwError "missing actual field"
    let some info := env.find? producer | throwError "missing actual producer"
    let some value := info.value? (allowOpaque := true) | throwError "missing checked body"
    let terms := R2CloseProductionAudit.fieldTerms ctor (R2CloseProductionAudit.arity ctorInfo.type) index value
    unless terms.size == expected do throwError "actual field inventory {producer}.{field}: {terms.size}, expected {expected}"
    for term in terms do
      let names := term.getUsedConstants
      unless names.contains `R2UnmarkedOwner.AncestorValue.of_entries ||
          names.contains `R2UnmarkedOwner.AncestorValue.restrict_state ||
          names.contains `R2CloseValueFamily.wholePack do
        throwError "actual field omitted whole-value construction {producer}.{field}"
      if names.contains `sorryAx then throwError "direct sorryAx in actual field"
      for name in names do
        if (← Lean.collectAxioms name).contains `sorryAx then
          throwError "sorry-dependent reference in actual field: {name}"
    total := total + terms.size
  let flow := `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0
  if (← Lean.collectAxioms flow).contains `sorryAx then throwError "whole flow opener has sorryAx"
  let ctor := `L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk
  let some ctorInfo := env.find? ctor | throwError "missing flow route constructor"
  let some index := R2CloseProductionAudit.fieldIndex `vslot ctorInfo.type 0 | throwError "missing flow value slot"
  let some info := env.find? flow | throwError "missing actual flow opener"
  let some value := info.value? (allowOpaque := true) | throwError "missing actual flow body"
  let terms := R2CloseProductionAudit.fieldTerms ctor (R2CloseProductionAudit.arity ctorInfo.type) index value
  let informative := terms.filter fun term =>
    term.getUsedConstants.contains `R2UnmarkedOwner.AncestorValue.of_entries ||
    term.getUsedConstants.contains `R2UnmarkedOwner.AncestorValue.restrict_state
  unless informative.size == 3 do throwError "flow informative inventory {informative.size}, expected 3"
  for consumer in [`L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,
      `L4YAML.Proofs.StreamAccum.accum_block_pending] do
    let some ci := env.find? consumer | throwError "missing actual close caller"
    let some body := ci.value? (allowOpaque := true) | throwError "missing checked close body"
    unless body.getUsedConstants.contains `R2UnmarkedOwner.AncestorValue.restrict_state ||
        body.getUsedConstants.contains `R2CloseValueFamily.wholePack do
      throwError "actual caller omits whole-value reader"
    let mut cursor := ci.type
    while let .forallE name domain body _ := cursor do
      if domain.getUsedConstants.contains `R2UnmarkedOwner.AncestorValue && name != `h_vpack then
        throwError "new external family premise {consumer}: {name}"
      cursor := body
  Lean.logInfo s!"WHOLE-VALUE-AUDIT content_and_properties={total} flow_writers={informative.size} field_sorry_terms=0 flow_opener_sorryAx=absent actual_close_readers=2"

#print axioms R2CloseValueFamily.pairAt_of_route
#print axioms R2CloseValueFamily.wholePack
#print axioms L4YAML.Proofs.StreamAccum.accum_flow_open_depth0
