import Research.R2SequenceContext.ConcreteContexts
import Lean

open Lean
namespace R2SequenceAudit

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
    else missing := missing.push n
  return (seen, missing)

end R2SequenceAudit

run_cmd do
  let env := (← getEnv).setExporting false
  for root in [`R2ConcreteSequences.SequenceQuestion.actual_sequence_question_consumption,
      `R2ConcreteSequences.Sibling.actual_sibling_then_ancestor] do
    unless env.contains root do throwError "missing checked root {root}"
    let (used, missing) := R2SequenceAudit.dependencies env [root]
    unless missing.isEmpty do throwError "unresolved references {missing}"
    for forbidden in [`L4YAML.Surface.SLYamlStream.scannerDrop,
        `L4YAML.Surface.SLYamlStream.implicitContinue,
        `L4YAML.Proofs.StreamAccum.dropClose, `sorryAx,
        `R2ConcreteSuppliers.actual_value_domain6,
        `R2ConcreteSuppliers.actual_6_2_0_consumption] do
      unless env.contains forbidden do throwError "unknown forbidden name {forbidden}"
      if used.contains forbidden then throwError "root {root} uses forbidden {forbidden}"
    for required in [`L4YAML.Surface.SLYamlStream.single,
        `L4YAML.Surface.SBlockMapEntry.explicit,
        `L4YAML.Surface.SBlockMapEntry.explicitEmpty,
        `L4YAML.Surface.SCompactSeq.mk,
        `L4YAML.Surface.SBlockIndented.compactSeq,
        `L4YAML.Proofs.R2SequenceContext.SlotValues.compact_sequence] do
      unless env.contains required do throwError "unknown required name {required}"
      unless used.contains required do throwError "root {root} omits actual constructor {required}"
    if root == `R2ConcreteSequences.SequenceQuestion.actual_sequence_question_consumption then
      for reader in [`L4YAML.Proofs.R2SequenceContext.SequenceValues.slot,
          `L4YAML.Proofs.R2CompactSlot.SlotValues.compact_question] do
        unless used.contains reader do throwError "sequence question omitted its actual wide reader"
    else
      for reader in [`L4YAML.Proofs.R2SequenceContext.SequenceValues.sibling,
          `L4YAML.Surface.SCompactSeqTail.cons] do
        unless used.contains reader do throwError "sibling route omitted its actual non-nil tail"
    let axioms ← Lean.collectAxioms root
    for axiomName in axioms do
      unless [`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "extra axiom {axiomName}"
    logInfo s!"SEQUENCE-PROOF-AUDIT {root}: constants={used.size} required=6 readers=2 forbidden=0 axioms={axioms.map Name.toString}"
