module
public import Tests.Guards.Proofs.AnchoredWordAudit
public meta import Lean
public section
open Lean L4YAML.Tests.Guards.AnchoredWordAudit
unsafe def main : IO Unit := do
 Lean.initSearchPath (← Lean.findSysroot)
 Lean.enableInitializersExecution
 let env ← Lean.importModules #[{module:=`Tests.Guards.Proofs.AnchoredWordAudit}] {} 0 (loadExts:=true)
 let ctx : Lean.Core.Context := {fileName:="<anchored-word-audit>",fileMap:=default}
 let st : Lean.Core.State := {env}
 let (rows,_) ← auditAnchoredWord.toIO ctx st
 for row in rows do IO.println row
