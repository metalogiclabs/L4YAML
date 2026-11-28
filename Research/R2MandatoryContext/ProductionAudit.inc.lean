
namespace R2MandatoryProductionAudit

def arity : Lean.Expr → Nat
  | .forallE _ _ body _ => 1 + arity body
  | _ => 0

def fieldIndex (field : Lean.Name) : Lean.Expr → Nat → Option Nat
  | .forallE name _ body _, n => if name == field then some n else fieldIndex field body (n+1)
  | _, _ => none

-- Instantiate local definitions before checking actual constructor arguments.
partial def arguments (callee : Lean.Name) (count index : Nat) (e : Lean.Expr) : Array Lean.Expr := Id.run do
  if e.getAppFn.isConstOf callee && e.getAppNumArgs == count then
    return #[e.getAppArgs[index]!]
  match e with
  | .app f a => return arguments callee count index f ++ arguments callee count index a
  | .lam _ _ body _ => return arguments callee count index body
  | .letE _ _ value body _ => return arguments callee count index (body.instantiate1 value)
  | .mdata _ body | .proj _ _ body => return arguments callee count index body
  | _ => return #[]

def clean (term : Lean.Expr) : Lean.Elab.Command.CommandElabM Bool := do
  for name in term.getUsedConstants do
    if name == `sorryAx || (← Lean.collectAxioms name).contains `sorryAx then return false
  pure true

end R2MandatoryProductionAudit

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock
  let some ci := env.find? ctor | throwError "actual pendingBlock absent"
  let some index := R2MandatoryProductionAudit.fieldIndex `h_close_entry ci.type 0
    | throwError "mandatory completion absent"
  let mut cursor := ci.type
  let mut whole := false
  while let .forallE field domain body _ := cursor do
    if field == `h_close_entry then
      whole := domain.getUsedConstants.contains `R2JointFrames.Context
    cursor := body
  unless whole do throwError "actual mandatory field lost Context"
  let producers := #[
    `L4YAML.Proofs.StreamAccum.accum_block_on_noPending,
    `L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,
    `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent,
    `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock]
  let mut all := 0
  let mut supplied := 0
  for producer in producers do
    let some info := env.find? producer | throwError "actual producer absent {producer}"
    let some body := info.value? (allowOpaque := true) | throwError "actual body absent {producer}"
    let terms := R2MandatoryProductionAudit.arguments ctor (R2MandatoryProductionAudit.arity ci.type) index body
    unless terms.size > 0 do throwError "actual writer absent {producer}"
    let mut paid := 0
    for term in terms do
      if ← R2MandatoryProductionAudit.clean term then
        unless term.getUsedConstants.contains `R2MandatoryContext.sequence_step do
          throwError "clean field did not spend actual scanner adapter {producer}"
        paid := paid + 1
    all := all + terms.size
    supplied := supplied + paid
    Lean.logInfo s!"MANDATORY-WRITERS {producer} actual={terms.size} supplied={paid} residual={terms.size-paid}"
  for producer in [`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock,
      `L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented] do
    let some info := env.find? producer | throwError "consumer absent"
    let mut consumerCursor := info.type
    while let .forallE name _ body _ := consumerCursor do
      if name == `h_wholeSequenceContext then throwError "new external context premise"
      consumerCursor := body
  let axioms ← Lean.collectAxioms `R2MandatoryContext.sequence_step
  unless axioms.size == 3 && axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
    throwError "actual adapter axiom boundary changed {axioms}"
  Lean.logInfo s!"MANDATORY-CONTEXT-AUDIT actual_writers={all} supplied={supplied} residual={all-supplied} constructor_fields_added=0 external_context_premises_added=0 critical_retirements=0 full_module_accepted=false"
