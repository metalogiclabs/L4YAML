/- Axiom admission for the content producer. Scalar/property production on
this inherited tree uses reflected leaves. The new proofs may reuse exactly
those old leaves; they may not introduce an axiom or a placeholder. The strict
serialization headline sweep is unchanged. -/
module

public import Tests.Guards.Proofs.RightWallContentNative
public meta import Lean

open Lean Elab Command in
run_cmd do
  let leafBase ← collectAxioms ``L4YAML.Proofs.Serialization.TraceOf.StreamBridge.TPendingNode.content_step_noPending
  let sourceBase ← collectAxioms ``L4YAML.Proofs.StreamAccum.contentArm_of_dispatch
  let producers := #[
    ``L4YAML.Proofs.Serialization.TraceOf.RightWallContent.content_step_routed0,
    ``L4YAML.Proofs.Serialization.TraceOf.RightWallContent.content_after_docStart,
    ``L4YAML.Proofs.Serialization.TraceOf.RightWallContent.directive_after_pending_document]
  for n in producers do
    let axs ← collectAxioms n
    if axs.contains ``sorryAx then
      throwError "content producer {n} depends on sorryAx"
    let fresh := axs.filter (fun a => !leafBase.contains a)
    unless fresh.isEmpty do
      throwError "content producer {n} adds axioms beyond the existing content producer: {fresh}"
    logInfo m!"{n}: {axs.size} inherited axioms; no new axiom or placeholder"
  let n := ``L4YAML.Tests.Guards.RightWallContentNative.native_directive_after_explicit_scalar
  let axs ← collectAxioms n
  if axs.contains ``sorryAx then
    throwError "native content witness depends on sorryAx"
  let fresh := axs.filter (fun a => !leafBase.contains a && !sourceBase.contains a)
  unless fresh.isEmpty do
    throwError "native content witness adds axioms beyond the reused source/content proofs: {fresh}"
  logInfo m!"{n}: {axs.size} inherited axioms; no new axiom or placeholder"
