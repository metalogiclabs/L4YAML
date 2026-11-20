/- Capstone 7.7: exact axiom admission for native mapping producers.
Every imported proof in the new namespaces is visited, with nonzero coverage;
structural/key-event proofs are standard-only. Reflected dependencies of
native leaf reading stay within the already verified source/content ceiling. -/
module
public import Tests.Guards.Proofs.MapReturnNative
public import Tests.Guards.Proofs.DirectiveColonProbe
public import L4YAML.Proofs.Serialization.TraceOf.KeyLift
public meta import Lean

#print axioms L4YAML.Proofs.Serialization.TraceOf.KeyEvents.reachable_key_reservations
#print axioms L4YAML.Proofs.Serialization.TraceOf.KeyEvents.reachable_colon_goOut
#print axioms L4YAML.Proofs.Serialization.TraceOf.MapReturn.first_implicit_colon
#print axioms L4YAML.Proofs.Serialization.TraceOf.MapReturn.implicit_key_of_dispatch
#print axioms L4YAML.Proofs.Serialization.TraceOf.KeyLift.flowNode_toKey

open Lean Elab Command in
run_cmd do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let sourceBase ← collectAxioms ``L4YAML.Proofs.StreamAccum.contentArm_of_dispatch
  let contentBase ← collectAxioms ``L4YAML.Proofs.Serialization.TraceOf.ContentBridge.accum_step_content_traceK
  let env ← getEnv
  for (nsPrefix, stdOnly, expected) in #[
      ("L4YAML.Tests.Guards.DirectiveColonProbe.", true, 9),
      ("L4YAML.Proofs.Serialization.TraceOf.KeyEvents.", true, 12),
      ("L4YAML.Proofs.Serialization.TraceOf.KeyLift.", true, 11),
      ("L4YAML.Proofs.Serialization.TraceOf.MapReturn.", false, 5)] do
    let mut count : Nat := 0
    for (n, _) in env.constants.toList do
      if n.toString.startsWith nsPrefix && Lean.wasOriginallyTheorem env n then
        let axs ← collectAxioms n
        if axs.contains ``sorryAx then throwError "mapping proof {n} depends on sorryAx"
        let fresh := axs.filter (fun a => !standard.contains a &&
          (stdOnly || (!sourceBase.contains a && !contentBase.contains a)))
        unless fresh.isEmpty do throwError "mapping proof {n} adds axioms: {fresh}"
        count := count + 1
    unless count == expected do throwError "mapping proof coverage moved: {nsPrefix}: expected {expected}, got {count}"
    logInfo m!"mapping axiom coverage: {nsPrefix}: {count}"
  for n in #[
      ``L4YAML.Proofs.Serialization.TraceOf.MapReturn.first_map_route,
      ``L4YAML.Proofs.Serialization.TraceOf.MapReturn.implicit_key_white,
      ``L4YAML.Proofs.Serialization.TraceOf.MapReturn.first_implicit_colon,
      ``L4YAML.Proofs.Serialization.TraceOf.MapReturn.return_map_value] do
    let axs ← collectAxioms n
    let fresh := axs.filter (fun a => !standard.contains a)
    unless fresh.isEmpty do throwError "mapping structure {n} uses nonstandard axioms: {fresh}"
  let n := ``L4YAML.Tests.Guards.MapReturnNative.native_directive_after_implicit_mapping
  let axs ← collectAxioms n
  if axs.contains ``sorryAx then throwError "native mapping proof depends on sorryAx"
  let fresh := axs.filter (fun a => !standard.contains a && !sourceBase.contains a && !contentBase.contains a)
  unless fresh.isEmpty do throwError "native mapping proof adds axioms: {fresh}"
  logInfo m!"{n}: {axs.size} inherited axioms; no fresh axiom"
