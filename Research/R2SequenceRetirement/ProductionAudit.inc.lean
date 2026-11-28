
namespace R2SequenceWriteAudit

def fieldIndex (field : Lean.Name) : Lean.Expr → Nat → Option Nat
  | .forallE name _ rest _, index =>
    if name == field then some index else fieldIndex field rest (index + 1)
  | _, _ => none

def arity : Lean.Expr → Nat
  | .forallE _ _ rest _ => arity rest + 1
  | _ => 0

-- Substitute local definitions. A let-bound name must not conceal a sorry.
partial def initializers (ctor : Lean.Name) (count index : Nat)
    (e : Lean.Expr) : Array Lean.Expr := Id.run do
  if e.getAppFn.isConstOf ctor && e.getAppNumArgs == count then
    return #[e.getAppArgs[index]!]
  match e with
  | .app f a => return initializers ctor count index f ++ initializers ctor count index a
  | .lam _ _ body _ => return initializers ctor count index body
  | .letE _ _ value body _ => return initializers ctor count index (body.instantiate1 value)
  | .mdata _ body | .proj _ _ body => return initializers ctor count index body
  | _ => return #[]

-- Count source sites before expansion; expanding a shared local proof can
-- duplicate the same initializer. Duplicates are checked but never credited
-- as additional source sites.
partial def rawInitializers (ctor : Lean.Name) (count index : Nat)
    (e : Lean.Expr) : Array Lean.Expr := Id.run do
  if e.getAppFn.isConstOf ctor && e.getAppNumArgs == count then
    return #[e.getAppArgs[index]!]
  match e with
  | .app f a => return rawInitializers ctor count index f ++ rawInitializers ctor count index a
  | .lam _ _ body _ => return rawInitializers ctor count index body
  | .letE _ _ value body _ => return rawInitializers ctor count index value ++ rawInitializers ctor count index body
  | .mdata _ body | .proj _ _ body => return rawInitializers ctor count index body
  | _ => return #[]

end R2SequenceWriteAudit

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock
  let some ctorInfo := env.find? ctor | throwError "actual pending constructor absent"
  let some index := R2SequenceWriteAudit.fieldIndex `h_close_entry ctorInfo.type 0
    | throwError "mandatory entry completion absent"
  let count := R2SequenceWriteAudit.arity ctorInfo.type
  let rootRule := `L4YAML.Proofs.StreamAccum.R2Mandatory.root_sequence_supplier
  let stepRule := `L4YAML.Proofs.StreamAccum.R2Mandatory.Full.sequence_step
  let rows := #[
    (`L4YAML.Proofs.StreamAccum.accum_block_on_noPending, 1, 1, rootRule),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock, 2, 1, stepRule),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent, 1, 1, stepRule),
    (`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock, 3, 3, stepRule)]
  let mut checked : Nat := 0
  let mut inventory : Nat := 0
  let mut expandedChecked : Nat := 0
  for (producer, expected, selectedSites, rule) in rows do
    let some info := env.find? producer | throwError "actual producer absent: {producer}"
    let some body := info.value? (allowOpaque := true) | throwError "body absent: {producer}"
    let raw := R2SequenceWriteAudit.rawInitializers ctor count index body
    unless raw.size == expected do
      throwError "actual source inventory changed: {producer}: {raw.size}/{expected}"
    inventory := inventory + raw.size
    let expanded := R2SequenceWriteAudit.initializers ctor count index body
    let selected := expanded.filter (fun term => term.getUsedConstants.contains rule)
    unless selected.size >= selectedSites do
      throwError "actual source misses retained rule: {producer}: {selected.size}/{selectedSites}"
    if expected == selectedSites then
      unless selected.size == expanded.size do
        throwError "an expanded selected writer lost the retained rule: {producer}"
    else
      unless expanded.size - selected.size == 1 do
        throwError "generic landed writer inventory changed: {producer}"
    for field in selected do
      let used := field.getUsedConstants
      if used.contains `sorryAx then
        throwError "selected writer {producer} contains sorryAx"
      for constant in used do
        if (← Lean.collectAxioms constant).contains `sorryAx then
          throwError "selected writer uses sorry-dependent constant {constant}"
    checked := checked + selectedSites
    expandedChecked := expandedChecked + selected.size
    Lean.logInfo m!"MANDATORY-WRITER {producer} source_sites={raw.size} selected_source_sites={selectedSites} expanded_checked={selected.size} required_rule={rule} sorry_terms=0"
  unless inventory == 7 && checked == 6 do
    throwError "writer audit cardinality changed: {inventory}/{checked}"
  Lean.logInfo m!"MANDATORY-WRITER-AUDIT inventory=7 checked=6 expanded_checked={expandedChecked} context_contract=experimental global_acceptance=not_claimed critical_retirement=0"
