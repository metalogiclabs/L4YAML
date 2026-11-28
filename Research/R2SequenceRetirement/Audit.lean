module
import all Research.R2SequenceRetirement.MandatoryContext
public import Lean

@[expose] public section R2SequenceRetirementAudit
open Lean

def retirementDependencies (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      todo := info.type.getUsedConstants.toList ++ todo
      if let some body := info.value? (allowOpaque := true) then
        todo := body.getUsedConstants.toList ++ todo
  return seen

run_cmd do
  let env := (← getEnv).setExporting false
  let standard := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[`sorryAx,
    `L4YAML.Surface.SLYamlStream.scannerDrop,
    `L4YAML.Surface.SLYamlStream.implicitContinue,
    `L4YAML.Proofs.StreamAccum.dropClose]
  let root := `R2SequenceRetirement.root_sequence_supplier
  let roots := #[root, `R2SequenceRetirement.sequence_value_pack,
    `R2SequenceRetirement.completed_sequence_value_pack,
    `R2SequenceRetirement.content_value_pack,
    `R2SequenceRetirement.Full.content, `R2SequenceRetirement.Full.sequence_step]
  for name in roots do
    let axioms ← collectAxioms name
    unless axioms.all standard.contains do
      throwError "nonstandard axiom in {name}: {axioms}"
    let deps := retirementDependencies env name
    for shortcut in forbidden do
      if deps.contains shortcut then
        throwError "forbidden shortcut in {name}: {shortcut}"
    logInfo m!"RETIREMENT-DEPENDENCIES root={name} dependencies={deps.size} axioms={axioms}"
  let rootDeps := retirementDependencies env root
  for required in #[`R2SequenceRetirement.scan_sequence_at_base,
      `R2SequenceRetirement.seqTail_append,
      `R2SequenceRetirement.Full.sequence_after,
      `L4YAML.Proofs.StreamAccum.preprocess_indents_of_size_le_one,
      `L4YAML.Proofs.NodeProduction.SBlockSeqEntries_of_compactTail,
      `L4YAML.Surface.SCompactSeqTail.cons,
      `L4YAML.Surface.SLYamlStream.single] do
    unless rootDeps.contains required do
      throwError "root supplier misses required dependency: {required}"
  let some info := env.find? root | throwError "root supplier absent"
  let semanticPremises : Nat ← Elab.Command.liftTermElabM do
    Meta.forallTelescopeReducing info.type fun args _ => do
      let mut count : Nat := 0
      for arg in args do
        let type ← Meta.inferType arg
        if type.getUsedConstants.any (fun name =>
            #[`R2SequenceRetirement.Full, `R2SequenceRetirement.Context,
              `R2SequenceRetirement.Joint].contains name) then
          count := count + 1
      return count
  unless semanticPremises == 0 do
    throwError "root supplier assumes {semanticPremises} semantic contexts"
  for projection in #[`R2SequenceRetirement.sequence_value_pack,
      `R2SequenceRetirement.completed_sequence_value_pack,
      `R2SequenceRetirement.content_value_pack] do
    let deps := retirementDependencies env projection
    for required in #[`R2SequenceRetirement.Full.value_line,
        `R2SequenceRetirement.levels_cover_marks,
        `R2SequenceRetirement.Joint.value_line] do
      unless deps.contains required do
        throwError "projection {projection} misses {required}"
  logInfo m!"RETIREMENT-AUDIT roots={roots.size} forbidden={forbidden.size} root_context_premises={semanticPremises} critical_retirement_claim=none"

end R2SequenceRetirementAudit
