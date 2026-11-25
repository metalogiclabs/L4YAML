module
public import Tests.Guards.Proofs.ExplicitWordAssurance
public meta import Tests.Guards.Proofs.ExplicitWordAssurance
public import Tests.Guards.Proofs.OwnerKeyReplayAudit
public meta import Tests.Guards.Proofs.OwnerKeyReplayAudit
public meta import Lean
set_option compiler.relaxedMetaCheck true
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.ExplicitWordAudit
open Lean L4YAML.Tests.Guards.OwnerKeyReplayAudit

def auditWordFragment : CoreM (Array String) := (do
 let names : Array (Name × Nat) := #[
  (``L4YAML.Tests.Guards.ExplicitWordFragment.word_prefix,0),
  (``L4YAML.Tests.Guards.ExplicitWordFragment.word_eof,0),
  (``L4YAML.Tests.Guards.ExplicitWordFragment.word_before_colon,0),
  (``L4YAML.Tests.Guards.ExplicitWordExecution.scan_filtered,0),
  (``L4YAML.Tests.Guards.ExplicitWordExecution.filtered_shape,0),
  (``L4YAML.Tests.Guards.ExplicitWordAssurance.source_guard,0),
  (``L4YAML.Tests.Guards.ExplicitWordAssurance.word_fragment_trace,45),
  (``L4YAML.Tests.Guards.ExplicitWordParser.parsed_tokens,0),
  (``L4YAML.Tests.Guards.ExplicitWordParser.parsed_source,0),
  (``L4YAML.Tests.Guards.ExplicitWordExecution.word_fold,0),
  (``L4YAML.Tests.Guards.ExplicitWordAssurance.word_events,0),
  (``L4YAML.Tests.Guards.ExplicitWordAssurance.word_fragment_assurance,45)]
 let mut rows := #["EXPLICIT_WORD_FRAGMENT_AUDIT"]
 let mut leaves : Array Name := #[]
 for (n,expected) in names do
  let axs ← collectAxioms n
  let raw := axs.filter (fun a => !allowedCapstoneAxioms.contains a)
  unless raw.size == expected do throwError "fragment profile changed: {n}: {raw.size} expected {expected}"
  let rejected ← unvalidatedAxioms n
  unless rejected.isEmpty do throwError "fragment replay rejected: {n}: {rejected}"
  for a in raw do
   unless leaves.contains a do leaves := leaves.push a
  rows := rows.push s!"WORD_PROFILE {n}: raw={raw.size} validated={raw.size} rejected=0"
 let previous ← collectAxioms ``L4YAML.Tests.Guards.OwnerExplicitKeyConsume.colon_then_content_step
 let inherited := previous.filter (fun a => !allowedCapstoneAxioms.contains a)
 unless inherited.size==leaves.size && leaves.all inherited.contains do
  throwError "fragment inherited dependency set changed"
 rows:=rows.push "WORD_LINEAGE same_inherited_axiom_set=true"
 unless leaves.size==45 do throwError "fragment union changed: {leaves.size}"
 for a in leaves do rows:=rows.push s!"WORD_LEAF {a}"
 rows:=rows.push s!"WORD_UNION raw={leaves.size} validated={leaves.size} rejected=0"
 return rows : AxiomReplayM (Array String)).run' {}
end L4YAML.Tests.Guards.ExplicitWordAudit
end Blanket
