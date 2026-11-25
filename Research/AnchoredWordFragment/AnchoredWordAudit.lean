module
public import Tests.Guards.Proofs.AnchoredWordAssurance
public meta import Tests.Guards.Proofs.AnchoredWordAssurance
public meta import Lean
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredWordAudit
open Lean

def auditAnchoredWord : CoreM (Array String) := do
 let names : Array Name := #[
  ``L4YAML.Tests.Guards.ExplicitWordPrefix.question_step,
  ``L4YAML.Tests.Guards.ExplicitWordPrefix.key_step,
  ``L4YAML.Tests.Guards.ExplicitWordPrefix.colon_step,
  ``L4YAML.Tests.Guards.AnchoredWordExecution.anchor_loop,
  ``L4YAML.Tests.Guards.AnchoredWordExecution.anchor_scan,
  ``L4YAML.Tests.Guards.AnchoredWordExecution.anchor_dispatch,
  ``L4YAML.Tests.Guards.AnchoredWordExecution.scalar_scan,
  ``L4YAML.Tests.Guards.AnchoredWordExecution.anchored_word_fold,
  ``L4YAML.Tests.Guards.AnchoredWordExecution.filtered_shape,
  ``L4YAML.Tests.Guards.AnchoredWordExecution.anchored_word_filtered,
  ``L4YAML.Tests.Guards.AnchoredWordGrammar.anchored_word_trace,
  ``L4YAML.Tests.Guards.AnchoredWordParser.parsed_tokens,
  ``L4YAML.Tests.Guards.AnchoredWordParser.parsed_raw_source,
  ``L4YAML.Tests.Guards.AnchoredWordParser.parsed_source,
  ``L4YAML.Tests.Guards.AnchoredWordAssurance.anchored_word_events,
  ``L4YAML.Tests.Guards.AnchoredWordAssurance.anchored_word_assurance]
 let allowed : Array Name := #[`propext,`Classical.choice,`Quot.sound]
 let mut rows := #["ANCHORED_WORD_AXIOM_AUDIT"]
 for n in names do
  unless (← getEnv).contains n do throwError "missing anchored export: {n}"
  let axioms ← collectAxioms n
  let raw := axioms.filter (fun a => !allowed.contains a)
  unless raw.isEmpty do throwError "nonstandard anchored dependency: {n}: {raw}"
  rows := rows.push s!"ANCHOR_PROFILE {n}: nonstandard=0 standard={axioms.size}"
 rows := rows.push s!"ANCHOR_UNION checked={names.size} nonstandard=0 new_native_axioms=0 inherited_native_axioms=0"
 return rows
end L4YAML.Tests.Guards.AnchoredWordAudit
