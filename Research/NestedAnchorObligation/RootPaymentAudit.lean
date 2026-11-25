import L4YAML.Proofs.Production.DocumentProduction
import L4YAML.Proofs.Production.StreamAccum
import Tests.Guards.Proofs.RelaySupplyCensus
import Tests.Guards.Proofs.OrTrueAudit
import Tests.Guards.Proofs.CapstonePathAudit
import Scripts.Path.CapstonePath

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus

-- Reuse the owner's supply resolver; do not infer a payment by source spelling.
run_cmd do
  let env ← getEnv
  logInfo m!"RELAY_GUARD {expectedTally}"
  logInfo m!"OR_TRUE_GUARD {Tests.Guards.OrTrueAudit.expectedSummary}"
  logInfo m!"CAPSTONE_PATH_GUARD {Tests.Guards.CapstonePathAudit.expectedSummary}"
  let (es,_) ← edges (ns ++ `content_dispatch_routed)
  let producer := `L4YAML.Proofs.StreamAccum.accum_block_on_noPending
  let ctor := `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock
  let rows := es.filter fun e => e.callee==ctor && e.idx==10
  let rootRows := rows.filter fun e => e.caller==producer
  unless rootRows.size==1 do throwError "expected one root constructor supply, got {rootRows.size}"
  for e in rows do logInfo m!"KEYSLOT_SUPPLY caller={e.caller} how={e.how}"
  let pay := rows.filter (fun e => e.how.startsWith "PAY") |>.size
  let decline := rows.filter (fun e => e.how.startsWith "DECLINE") |>.size
  let split := rows.filter (fun e => e.how.startsWith "SPLIT") |>.size
  let reached := Scripts.Path.CapstonePath.reach env Scripts.Path.CapstonePath.roots
  unless reached.contains producer do throwError "producer is not on the owner capstone path"
  logInfo m!"ROOT_PAYMENT producer_on_capstone_path=true root_supply={rootRows[0]!.how} field_pay={pay} field_decline={decline} field_split={split}"
  let allowed : Array Name := #[`propext,`Classical.choice,`Quot.sound]
  for n in [producer,`L4YAML.Proofs.StreamAccum.accum_block_pending,
      `L4YAML.Proofs.DocumentProduction.scan_strict_proof,
      `L4YAML.Proofs.DocumentProduction.parse_strict_proof] do
    let axioms ← liftCoreM (collectAxioms n)
    let native := axioms.filter (fun a => (a.toString.splitOn "._native.native_decide.ax_").length > 1)
    let bad := axioms.filter (fun a => !allowed.contains a && !native.contains a)
    unless bad.isEmpty do throwError "nonstandard axiom dependency {n}: {bad}"
    logInfo m!"ROOT_PAYMENT_AXIOMS {n} other_custom=0 standard={axioms.size-native.size} inherited_native={native.size}"
    for a in native.qsort (fun a b => a.toString < b.toString) do
      logInfo m!"ROOT_PAYMENT_NATIVE {n} {a}"
