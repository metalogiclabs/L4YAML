module
public import Tests.Guards.Proofs.ExplicitWordAudit
public meta import Lean
public section
open Lean L4YAML.Tests.Guards.ExplicitWordAudit
unsafe def main : IO Unit := do
 Lean.initSearchPath (← Lean.findSysroot)
 Lean.enableInitializersExecution
 let env ← Lean.importModules #[{module:=`Tests.Guards.Proofs.ExplicitWordAudit}] {} 0 (loadExts:=true)
 let ctx : Lean.Core.Context := {fileName:="<explicit-word-replay>",fileMap:=default}
 let st : Lean.Core.State := {env}
 let (rows,_) ← auditWordFragment.toIO ctx st
 for row in rows do IO.println row
