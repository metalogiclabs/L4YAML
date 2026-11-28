
namespace R2ContinuationProductionAudit

def fieldIndex (field : Lean.Name) : Lean.Expr → Nat → Option Nat
  | .forallE name _ rest _, index =>
    if name == field then some index else fieldIndex field rest (index + 1)
  | _, _ => none

def arity : Lean.Expr → Nat
  | .forallE _ _ rest _ => arity rest + 1
  | _ => 0

partial def fieldTerms (ctor : Lean.Name) (count index : Nat) (e : Lean.Expr) : Array Lean.Expr := Id.run do
  if e.getAppFn.isConstOf ctor && e.getAppNumArgs == count then
    return #[e.getAppArgs[index]!]
  match e with
  | .app f a => return fieldTerms ctor count index f ++ fieldTerms ctor count index a
  | .lam _ _ b _ => return fieldTerms ctor count index b
  | .letE _ _ value body _ =>
    return fieldTerms ctor count index value ++ fieldTerms ctor count index body
  | .mdata _ body | .proj _ _ body => return fieldTerms ctor count index body
  | _ => return #[]

end R2ContinuationProductionAudit

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent
  let some ctorInfo := env.find? ctor | throwError "missing actual completed constructor"
  let some index := R2ContinuationProductionAudit.fieldIndex `h_closable_entry ctorInfo.type 0
    | throwError "missing actual completed-entry field"
  let count := R2ContinuationProductionAudit.arity ctorInfo.type
  let mut total := 0
  for (producer, reader) in [
      (`L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented,
        `L4YAML.Proofs.R2ContentCompletion.SequenceValues.complete),
      (`L4YAML.Proofs.StreamAccum.accum_content_pending,
        `L4YAML.Proofs.R2ContentCompletion.NodeSequenceValues.complete)] do
    let some info := env.find? producer | throwError "missing actual producer"
    let some body := info.value? (allowOpaque := true) | throwError "missing actual producer body"
    let terms := R2ContinuationProductionAudit.fieldTerms ctor count index body
    unless terms.size == 3 do throwError "actual field inventory {producer}: {terms.size}"
    for term in terms do
      let names := term.getUsedConstants
      unless names.contains reader do throwError "actual completed field omits {reader}"
      if names.contains `sorryAx then throwError "actual completed field has a direct sorryAx"
      for name in names do
        if (← Lean.collectAxioms name).contains `sorryAx then
          throwError "actual completed field references a sorry-dependent constant {name}"
    total := total + terms.size
  Lean.logInfo s!"ACTUAL-COMPLETION-FIELDS ordinary=3 decorated=3 checked={total} helper_terms=6 sorry_terms=0"
