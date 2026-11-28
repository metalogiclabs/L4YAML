import Research.R2UnmarkedOwner.Concrete
import Research.R2ContentCompletion.DependencyAudit

open Lean

run_cmd do
  let env := (← getEnv).setExporting false
  let root := `R2UnmarkedOwner.initialized_unmarked_then_ancestor
  let some info := env.find? root | throwError "missing initialized proof"
  if info.type.isForall then throwError "initialized proof has a free premise"
  let (used, missing) := R2CompletionAudit.dependencies env [root]
  unless missing.isEmpty do throwError "unresolved dependencies {missing}"
  let required := #[`R2UnmarkedOwner.AncestorValue.of_entries,
    `R2UnmarkedOwner.AncestorValue.pair,
    `R2ContinuationTwoAncestors.sibling_key,
    `L4YAML.Surface.SLYamlStream.single,
    `L4YAML.Surface.SBlockMapEntry.explicit,
    `L4YAML.Surface.SBlockMapEntry.explicitEmpty,
    `L4YAML.Surface.SCompactSeqTail.cons,
    `L4YAML.Proofs.R2ContentCompletion.SequenceValues.complete,
    `L4YAML.Proofs.R2ContentCompletion.CompletedValues.sibling]
  for name in required do
    unless env.contains name && used.contains name do throwError "missing actual dependency {name}"
  let forbidden := #[`sorryAx, `L4YAML.Surface.SLYamlStream.scannerDrop,
    `L4YAML.Surface.SLYamlStream.implicitContinue,
    `L4YAML.Proofs.StreamAccum.dropClose,
    `R2ContinuationTwoAncestors.actual_completed_sibling_two_ancestor_values,
    `R2ContinuationTwoAncestors.inner_consumed]
  for name in forbidden do
    unless env.contains name do throwError "unresolved forbidden name {name}"
    if used.contains name then throwError "unexpected whole-source shortcut {name}"
  let axioms ← collectAxioms root
  for name in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains name do throwError "unexpected axiom {name}"
  logInfo s!"UNMARKED-PROOF-AUDIT constants={used.size} required={required.size} forbidden={forbidden.size} missing=0 free_premises=0 axioms={axioms.map Name.toString}"
