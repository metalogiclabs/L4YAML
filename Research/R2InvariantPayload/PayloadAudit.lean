import Research.R2InvariantPayload.ConcretePayloads
import Lean

open Lean

namespace R2PayloadAudit

partial def dependencies (env : Environment) (roots : List Name) : Std.HashSet Name × Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut missing : Array Name := #[]
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let body := (ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]
      todo := (ci.type.getUsedConstants ++ body).toList ++ todo
    else
      missing := missing.push n
  return (seen, missing)

end R2PayloadAudit

run_cmd do
  let env := (← getEnv).setExporting false
  for root in [`R2ConcretePayloads.actual_question_context,
      `R2ConcretePayloads.actual_sibling_tail_consumed,
      `R2ConcretePayloads.actual_ancestor_frame,
      `R2ConcretePayloads.actual_ancestor_frame_cover] do
    unless env.contains root do throwError "missing checked supplier {root}"
    let (used, missing) := R2PayloadAudit.dependencies env [root]
    unless missing.isEmpty do throwError "supplier {root} has unresolved dependencies {missing}"
    for forbidden in [`L4YAML.Surface.SLYamlStream.scannerDrop,
        `L4YAML.Surface.SLYamlStream.implicitContinue,
        `L4YAML.Proofs.StreamAccum.dropClose, `sorryAx] do
      unless env.contains forbidden do throwError "unknown forbidden audit name {forbidden}"
      if used.contains forbidden then throwError "supplier {root} uses forbidden {forbidden}"
    let isCover := root == `R2ConcretePayloads.actual_ancestor_frame_cover
    let requiredNames := if isCover then
      [`L4YAML.Proofs.R2InvariantPayload.own_frame_cover,
        `R2ConcretePayloads.actual_ancestor_stack_mono]
      else [`L4YAML.Surface.SLYamlStream.single,
        `L4YAML.Surface.SBlockMapEntry.explicit,
        `L4YAML.Surface.SBlockMapEntry.explicitEmpty]
    for required in requiredNames do
      unless env.contains required do throwError "unknown required audit name {required}"
      unless used.contains required do throwError "supplier {root} omits actual constructor {required}"
    if root == `R2ConcretePayloads.actual_question_context then
      unless used.contains `R2ConcretePayloads.question_node do
        throwError "question payload did not spend an actual node witness"
    if root == `R2ConcretePayloads.actual_sibling_tail_consumed then
      unless used.contains `L4YAML.Surface.SCompactMapTail.cons do
        throwError "sibling payload did not spend a non-nil tail"
    if root == `R2ConcretePayloads.actual_ancestor_frame then
      unless used.contains `L4YAML.Proofs.R2InvariantPayload.NodeValues.framed_ancestor do
        throwError "ancestor payload did not spend the stored frame"
      unless used.contains `R2ConcretePayloads.ancestor_value_payload do
        throwError "ancestor frame omits the actual source payload"
    let axioms ← Lean.collectAxioms root
    let allowed := [`propext, `Classical.choice, `Quot.sound]
    for axiomName in axioms do
      unless allowed.contains axiomName do throwError "supplier {root} has extra axiom {axiomName}"
    logInfo s!"PAYLOAD-AUDIT {root}: constants={used.size} required={requiredNames.length} forbidden=0 axioms={axioms.map Name.toString}"
