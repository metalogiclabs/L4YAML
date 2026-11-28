
namespace R2ColonSupplierProductionAudit

partial def countConst (name : Lean.Name) (e : Lean.Expr) : Nat :=
  match e with
  | .const n _ => if n == name then 1 else 0
  | .app f a => countConst name f + countConst name a
  | .lam _ _ b _ => countConst name b
  | .letE _ _ value body _ => countConst name value + countConst name body
  | .mdata _ body | .proj _ _ body => countConst name body
  | _ => 0

end R2ColonSupplierProductionAudit

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let ctor := `L4YAML.Proofs.StreamAccum.colon_open_map_explicit
  let some target := env.find? ctor | throwError "missing actual colon producer"
  let some index := R2ContinuationProductionAudit.fieldIndex `h_entry target.type 0
    | throwError "missing exact entry-step parameter"
  let arity := R2ContinuationProductionAudit.arity target.type
  for root in [`L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent,
      `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock] do
    let some info := env.find? root | throwError "missing actual sequence caller"
    let some body := info.value? (allowOpaque := true) | throwError "missing actual caller body"
    Lean.logInfo s!"SUPPLIER-TYPE-BEGIN {root}\n{repr info.type}\nSUPPLIER-TYPE-END {root}"
    let terms := R2ContinuationProductionAudit.fieldTerms ctor arity index body
    unless terms.size == 1 do throwError "unexpected actual colon applications {root}: {terms.size}"
    if r2SupplierExpectedFunded then
      for term in terms do
        let names := term.getUsedConstants
        unless names.contains `R2ColonSupplier.entry_step_at_landing do
          throwError "actual caller does not supply entry family {root}"
        if names.contains `sorryAx then throwError "actual supplier term contains sorryAx"
        for name in names do
          if (← Lean.collectAxioms name).contains `sorryAx then
            throwError "supplier term references sorry-dependent {name}"
      for required in [`R2ColonSupplier.live_landing_of_no_stamp,
          `L4YAML.Proofs.R2ConsumptionClosure.EntryValues.pair] do
        unless body.getUsedConstants.contains required do
          throwError "actual caller does not spend {required}"
    for name in [`L4YAML.Proofs.StreamAccum.block_dispatch_deferred,
        `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol,
        `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack,
        `L4YAML.Proofs.StreamAccum.dropClose] do
      Lean.logInfo s!"SUPPLIER-ESCAPE-REFERENCE {root} {name}: {R2ColonSupplierProductionAudit.countConst name body}"
    Lean.logInfo s!"ACTUAL-COLON-SUPPLIER {root}: applications={terms.size} funded={r2SupplierExpectedFunded}"
