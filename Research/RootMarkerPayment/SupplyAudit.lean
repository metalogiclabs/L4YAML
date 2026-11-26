import L4YAML.Proofs.Production.DocumentProduction
import Tests.Guards.Proofs.RelaySupplyCensus
import Tests.Guards.Proofs.CapstonePathAudit
open Lean Elab Command L4YAML.Tests.Guards.RelaySupplyCensus
run_cmd do
  let (es, _) ← edges (ns ++ `content_dispatch_routed)
  let root := es.filter fun e => e.caller == ns ++ `accum_block_on_noPending &&
    e.callee == ns ++ `PendingNode.pendingBlock && e.idx == 10
  unless root.size == 1 && root.all (fun e => e.how.startsWith "PAY") do
    throwError "root key-slot supply is not paid"
  let vpack := es.filter fun e => e.callee == ns ++ `accum_block_on_closeThenBlock && e.idx == 10
  let directDeclines := vpack.filter (fun e => e.how.startsWith "DECLINE") |>.size
  let directPays := vpack.filter (fun e => e.how.startsWith "PAY") |>.size
  unless directDeclines == 3 && directPays == 0 do
    throwError "unexpected value-pack supply boundary: PAY={directPays}, DECLINE={directDeclines}"
  logInfo m!"ROOT_MARKER_PAYMENT root=PAY marker_pays={directPays} vpack_direct_declines={directDeclines}"
  logInfo m!"ROOT_MARKER_RELAY {expectedTally}"
  logInfo m!"ROOT_MARKER_CAPSTONE {Tests.Guards.CapstonePathAudit.expectedSummary}"
