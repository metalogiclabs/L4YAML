module
public import Tests.Guards.Proofs.OwnerExplicitKeyValueContentStep
public import Tests.Guards.Proofs.OwnerKeyReplayAudit
public meta import Tests.Guards.Proofs.OwnerExplicitKeyValueContentStep
public meta import Tests.Guards.Proofs.OwnerKeyReplayAudit
public meta import Lean
public section
open Lean
open L4YAML.Tests.Guards.OwnerKeyReplayAudit
open L4YAML.Tests.Guards.OwnerExplicitKeyValueContentStep

def auditValueContent : CoreM (Array String) := do
  let original ← auditOwnerKeyAxioms
  let extra ← (do
    let mut rows : Array String := #[]
    for (n, expected) in #[( ``matched_colon_owner_content_ready, 0),
        (``matched_colon_then_owner_content_step, 45)] do
      let axs ← collectAxioms n
      let raw := axs.filter fun a => !allowedCapstoneAxioms.contains a
      unless raw.size == expected do throwError "value content native census mismatch {n}: {raw.size}"
      let rejected ← unvalidatedAxioms n
      unless rejected.isEmpty do throwError "value content replay failed {n}: {rejected}"
      rows := rows.push s!"OWNER_VALUE_CONTENT_REPLAY {n}: raw={raw.size} validated={raw.size} rejected=0"
      for a in raw do rows := rows.push s!"OWNER_VALUE_CONTENT_REPLAY_LEAF {a}"
    return rows : AxiomReplayM (Array String)).run' {}
  return original ++ extra

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `Tests.Guards.Proofs.OwnerKeyReplayAudit},
    {module := `Tests.Guards.Proofs.OwnerExplicitKeyValueContentStep}] {} 0 (loadExts := true)
  let ctx : Lean.Core.Context := {fileName := "<owner-value-content-replay>", fileMap := default}
  let state : Lean.Core.State := {env}
  let (rows, _) ← auditValueContent.toIO ctx state
  for row in rows do IO.println row
