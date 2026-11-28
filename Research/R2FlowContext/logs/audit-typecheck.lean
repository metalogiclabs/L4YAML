module
import all L4YAML.Proofs.Production.StreamAccum
import Lean

namespace R2FlowAudit

def dependencies (env : Lean.Environment) (root : Lean.Name) : Std.HashSet Lean.Name := Id.run do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      todo := info.type.getUsedConstants.toList ++ todo
      if let some value := info.value? (allowOpaque := true) then
        todo := value.getUsedConstants.toList ++ todo
  return seen

def clean (term : Lean.Expr) : Lean.Elab.Command.CommandElabM Bool := do
  let used := term.getUsedConstants
  if used.contains `sorryAx then return false
  for constant in used do
    if (← Lean.collectAxioms constant).contains `sorryAx then return false
  return true

end R2FlowAudit


run_cmd do
  unless (← R2FlowAudit.clean (Lean.mkConst `True.intro)) do throwError "clean helper rejected True"
  Lean.logInfo "AUDIT-HELPER clean_true=checked"
