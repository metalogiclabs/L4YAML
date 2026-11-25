module
public import Tests.Guards.Proofs.AnchoredAliasAudit
public meta import Lean
public section
open Lean L4YAML.Tests.Guards.AnchoredAliasAudit
unsafe def main : IO Unit := do
 Lean.initSearchPath (← Lean.findSysroot)
 Lean.enableInitializersExecution
 let env ← Lean.importModules #[{module:=`Tests.Guards.Proofs.AnchoredAliasAudit}] {} 0 (loadExts:=true)
 let ctx : Lean.Core.Context := {fileName:="<anchored-alias-audit>",fileMap:=default}
 let st : Lean.Core.State := {env}
 let (rows,_) ← auditAnchoredAlias.toIO ctx st
 for row in rows do IO.println row
