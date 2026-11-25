module
public import Tests.Guards.Proofs.AnchoredAliasAssurance
public meta import Tests.Guards.Proofs.AnchoredAliasAssurance
public meta import Lean
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredAliasAudit
open Lean

def auditAnchoredAlias : CoreM (Array String) := do
 let names : Array Name := #[
  ``L4YAML.Tests.Guards.AnchoredAliasSource.word_before_question,
  ``L4YAML.Tests.Guards.AnchoredAliasStates.first_value_step,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.q_scan,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.copy_scan,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.c_scan,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.alias_loop,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.alias_scan,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.alias_dispatch,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.next_eof,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.filtered_shape,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.alias_word_fold,
  ``L4YAML.Tests.Guards.AnchoredAliasExecution.alias_word_filtered,
  ``L4YAML.Tests.Guards.AnchoredAliasGrammar.alias_word_trace,
  ``L4YAML.Tests.Guards.AnchoredAliasGrammar.alias_events_wellformed,
  ``L4YAML.Tests.Guards.AnchoredAliasParser.alias_exact,
  ``L4YAML.Tests.Guards.AnchoredAliasParser.second_entry,
  ``L4YAML.Tests.Guards.AnchoredAliasParser.document_word,
  ``L4YAML.Tests.Guards.AnchoredAliasParser.parsed_tokens,
  ``L4YAML.Tests.Guards.AnchoredAliasParser.parsed_raw_source,
  ``L4YAML.Tests.Guards.AnchoredAliasParser.parsed_source,
  ``L4YAML.Tests.Guards.AnchoredAliasAssurance.alias_word_events,
  ``L4YAML.Tests.Guards.AnchoredAliasAssurance.alias_empty_registry_rejected,
  ``L4YAML.Tests.Guards.AnchoredAliasAssurance.alias_word_assurance]
 let allowed : Array Name := #[`propext,`Classical.choice,`Quot.sound]
 let mut rows := #["ANCHORED_ALIAS_AXIOM_AUDIT"]
 for n in names do
  unless (← getEnv).contains n do throwError "missing alias export: {n}"
  let axioms ← collectAxioms n
  let raw := axioms.filter (fun a => !allowed.contains a)
  unless raw.isEmpty do throwError "nonstandard alias dependency: {n}: {raw}"
  rows := rows.push s!"ALIAS_PROFILE {n}: nonstandard=0 standard={axioms.size}"
 rows := rows.push s!"ALIAS_UNION checked={names.size} nonstandard=0 new_native_axioms=0 inherited_native_axioms=0"
 return rows
end L4YAML.Tests.Guards.AnchoredAliasAudit
