module

import CapstoneObstructions
import DirectiveResult
import QuotedPublic
public meta import Lean

/-! Persistent Group 7.7 receipt gate. These are distinct claims, not a
completion flag. Inspect the printed types; collect transitive axioms from
the elaborated environment, accepting ONLY the three named standard axioms.
Native reflection leaves and all unlisted axioms are rejected, including
internal ones. Runtime guards remain supplementary, not proof certificates. -/

#check MathGraph.WholeSource.CapstoneObstructions.original_converse_refuted
#check MathGraph.WholeSource.CapstoneObstructions.repaired_completeness_refuted
#check MathGraph.WholeSource.CapstoneObstructions.repaired_leaf_excludes_bad
#check L4YAML.Research.AcceptedSource.source_quoted_public_accepts
#check MathGraph.WholeSource.DirectiveResult.original_empty_document_raw_result

open Lean Elab Command in
run_cmd do
  let required : List Name := [
    ``MathGraph.WholeSource.CapstoneObstructions.original_converse_refuted,
    ``MathGraph.WholeSource.CapstoneObstructions.repaired_completeness_refuted,
    ``MathGraph.WholeSource.CapstoneObstructions.repaired_leaf_excludes_bad,
    ``L4YAML.Research.AcceptedSource.source_quoted_public_accepts,
    ``MathGraph.WholeSource.DirectiveResult.original_empty_document_raw_result]
  for n in required do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a)
    unless bad.isEmpty do
      throwError "UNQUALIFIED {n}: {bad}"
    logInfo m!"QUALIFIED_AXIOMS {n}: {axs}"
