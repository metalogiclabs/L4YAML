import L4YAML.Proofs.Production.DocumentProduction
import Tests.Guards.Proofs.RelaySupplyCensus
import Tests.Guards.Proofs.CapstonePathAudit
open Lean Elab Command L4YAML.Tests.Guards.RelaySupplyCensus
run_cmd do
  let (es, _) ← edges (ns ++ `content_dispatch_routed)
  let vpack := es.filter fun e => e.callee == ns ++ `accum_block_on_closeThenBlock && e.idx == 10
  let declines := vpack.filter (fun e => e.how.startsWith "DECLINE") |>.size
  let pays := vpack.filter (fun e => e.how.startsWith "PAY") |>.size
  unless declines == 1 && pays == 2 do
    throwError "unexpected actual-domain marker supply: PAY={pays}, DECLINE={declines}"
  logInfo m!"ACTUAL_DOMAIN_MARKER_PAYMENTS paid={pays} remaining_direct_declines={declines}"
  logInfo m!"CONTENT_SLOT_CAPSTONE {Tests.Guards.CapstonePathAudit.expectedSummary}"
  logInfo m!"CONTENT_SLOT_RELAY {expectedTally}"
