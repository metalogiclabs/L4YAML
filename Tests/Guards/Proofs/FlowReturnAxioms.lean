/- Check every new return proof against the unchanged source/content
producers' inherited axiom boundary; structural returns are standard-only. -/
module
public import Tests.Guards.Proofs.FlowReturnNative
public meta import Lean

#print axioms L4YAML.Proofs.Serialization.TraceOf.FlowReturn.accum_step_flow_return
#print axioms L4YAML.Proofs.Serialization.TraceOf.FlowReturn.accum_step_content_returnK
#print axioms L4YAML.Proofs.Serialization.TraceOf.FlowReturn.accum_step_key_return
#print axioms L4YAML.Proofs.Serialization.TraceOf.FlowReturn.return_first
#print axioms L4YAML.Proofs.Serialization.TraceOf.FlowReturn.return_explicit
#print axioms L4YAML.Proofs.Serialization.TraceOf.FlowReturn.base_close_pending
#print axioms L4YAML.Proofs.StructureProduction.scanFlowSequenceEnd_prod
#print axioms L4YAML.Proofs.StructureProduction.scanFlowMappingEnd_prod

open Lean Elab Command in
run_cmd do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let sourceBase ← collectAxioms ``L4YAML.Proofs.StreamAccum.contentArm_of_dispatch
  let contentBase ← collectAxioms ``L4YAML.Proofs.Serialization.TraceOf.ContentBridge.accum_step_content_traceK
  let env ← getEnv
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "L4YAML.Proofs.Serialization.TraceOf.FlowReturn." && Lean.wasOriginallyTheorem env n then
      let axs ← collectAxioms n
      if axs.contains ``sorryAx then throwError "return proof {n} depends on sorryAx"
      let fresh := axs.filter (fun a => !standard.contains a && !sourceBase.contains a && !contentBase.contains a)
      unless fresh.isEmpty do throwError "return proof {n} adds fresh axioms: {fresh}"
      count := count + 1
  unless count == 41 do throwError "return proof coverage moved: expected 41, got {count}"
  logInfo m!"{count} return proofs: no new axiom or placeholder"
  for n in #[
      ``L4YAML.Proofs.StructureProduction.scanFlowSequenceEnd_prod,
      ``L4YAML.Proofs.StructureProduction.scanFlowMappingEnd_prod,
      ``L4YAML.Proofs.Serialization.TraceOf.FlowReturn.FlowOpenR.closeBase,
      ``L4YAML.Proofs.Serialization.TraceOf.FlowReturn.accum_step_flow_return,
      ``L4YAML.Proofs.Serialization.TraceOf.FlowReturn.accum_step_key_return,
      ``L4YAML.Proofs.Serialization.TraceOf.FlowReturn.return_first,
      ``L4YAML.Proofs.Serialization.TraceOf.FlowReturn.return_explicit,
      ``L4YAML.Proofs.Serialization.TraceOf.FlowReturn.base_close_pending,
      ``L4YAML.Proofs.Serialization.TraceOf.FlowReturn.returned_pending] do
    let axs ← collectAxioms n
    let fresh := axs.filter (fun a => !standard.contains a)
    unless fresh.isEmpty do throwError "structural return {n} uses nonstandard axioms: {fresh}"
    logInfo m!"{n}: standard axioms only"
  let n := ``L4YAML.Tests.Guards.FlowReturnNative.native_directive_after_flow
  let axs ← collectAxioms n
  if axs.contains ``sorryAx then throwError "native return witness depends on sorryAx"
  let fresh := axs.filter (fun a => !standard.contains a && !sourceBase.contains a && !contentBase.contains a)
  unless fresh.isEmpty do throwError "native return witness adds fresh axioms: {fresh}"
  logInfo m!"{n}: {axs.size} inherited axioms; no fresh axiom"
