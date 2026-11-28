import Research.R2ContinuationContract.TwoAncestors
import Research.R2ContentCompletion.DependencyAudit

open Lean

run_cmd do
  let env := (← getEnv).setExporting false
  let root := `R2ContinuationTwoAncestors.actual_completed_sibling_two_ancestor_values
  let some ci := env.find? root | throwError "missing complete proof"
  if ci.type.isForall then throwError "complete initialized route has a free premise"
  let (used, missing) := R2CompletionAudit.dependencies env [root]
  unless missing.isEmpty do throwError "unresolved dependencies {missing}"
  let required := #[`L4YAML.Surface.SLYamlStream.single,
    `L4YAML.Surface.SBlockMapEntry.explicit,
    `L4YAML.Surface.SBlockMapEntry.explicitEmpty,
    `L4YAML.Surface.SCompactSeq.mk,
    `L4YAML.Surface.SCompactSeqTail.cons,
    `L4YAML.Proofs.R2CompactSlot.SlotValues.compact_question,
    `L4YAML.Proofs.R2SequenceContext.SlotValues.compact_sequence,
    `L4YAML.Proofs.R2ContentCompletion.SequenceValues.complete,
    `L4YAML.Proofs.R2ContentCompletion.CompletedValues.sibling,
    `L4YAML.Proofs.R2ConsumptionClosure.EntryValues.consume,
    `R2ContinuationTwoAncestors.content_reader,
    `R2ContinuationTwoAncestors.inner_consumed,
    `R2ContinuationControls.innerConsumedMarks,
    `R2ContinuationControls.outerConsumedMarks]
  for name in required do
    unless env.contains name do throwError "unresolved required name {name}"
    unless used.contains name do throwError "missing actual constructor or reader {name}"
  let forbidden := #[`L4YAML.Surface.SLYamlStream.scannerDrop,
    `L4YAML.Surface.SLYamlStream.implicitContinue,
    `L4YAML.Proofs.StreamAccum.dropClose, `sorryAx,
    `R2ConcreteSuppliers.actual_value_domain6,
    `R2ConcreteSuppliers.actual_6_2_0_consumption,
    `R2ConcreteSequences.Sibling.actual_sibling_then_ancestor,
    `R2ConcreteSequences.SequenceQuestion.actual_sequence_question_consumption,
    `R2ConcreteCompletion.actual_completed_sibling_ancestor]
  for name in forbidden do
    unless env.contains name do throwError "unresolved forbidden name {name}"
    if used.contains name then throwError "complete proof uses shortcut {name}"
  let axioms ← Lean.collectAxioms root
  for name in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains name do
      throwError "unexpected axiom {name}"
  logInfo s!"TWO-ANCESTOR-AUDIT constants={used.size} required={required.size} forbidden={forbidden.size} missing=0 free_premises=0 axioms={axioms.map Name.toString}"
