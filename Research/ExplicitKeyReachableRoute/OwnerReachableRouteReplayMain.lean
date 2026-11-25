module
public import Tests.Guards.Proofs.OwnerExplicitKeyReachableRoute
public import Tests.Guards.Proofs.OwnerKeyReplayAudit
public meta import Tests.Guards.Proofs.OwnerExplicitKeyReachableRoute
public meta import Tests.Guards.Proofs.OwnerKeyReplayAudit
public meta import Lean
public section
open Lean
open L4YAML.Tests.Guards.OwnerKeyReplayAudit
open L4YAML.Tests.Guards.OwnerExplicitKeyReachableRoute

def auditReachableRoute : CoreM (Array String) := do
  let original ← auditOwnerKeyAxioms
  let extra ← (do
    let mut rows : Array String := #[]
    let mut leaves : Array Name := #[]
    for (n, expected) in #[( ``initial_question_park, 0),
        (``initial_question_from_next, 0), (``initial_key_progress, 45),
        (``initial_scalar_key_ready, 45), (``initial_scalar_matched_colon, 45),
        (``initial_scalar_then_owner_value, 45)] do
      let axs ← collectAxioms n
      let raw := axs.filter fun a => !allowedCapstoneAxioms.contains a
      unless raw.size == expected do throwError "reachable-route native census mismatch {n}: {raw.size}"
      let rejected ← unvalidatedAxioms n
      unless rejected.isEmpty do throwError "reachable-route replay failed {n}: {rejected}"
      rows := rows.push s!"OWNER_REACHABLE_ROUTE_REPLAY {n}: raw={raw.size} validated={raw.size} rejected=0"
      for a in raw do
        unless leaves.contains a do leaves := leaves.push a
    unless leaves.size == 45 do throwError "reachable-route unique native union changed: {leaves.size}"
    for a in leaves do rows := rows.push s!"OWNER_REACHABLE_ROUTE_REPLAY_LEAF {a}"
    rows := rows.push s!"OWNER_REACHABLE_ROUTE_REPLAY_UNION raw={leaves.size} validated={leaves.size} rejected=0"
    return rows : AxiomReplayM (Array String)).run' {}
  return original ++ extra

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `Tests.Guards.Proofs.OwnerKeyReplayAudit},
    {module := `Tests.Guards.Proofs.OwnerExplicitKeyReachableRoute}] {} 0 (loadExts := true)
  let ctx : Lean.Core.Context := {fileName := "<owner-reachable-route-replay>", fileMap := default}
  let state : Lean.Core.State := {env}
  let (rows, _) ← auditReachableRoute.toIO ctx state
  for row in rows do IO.println row
