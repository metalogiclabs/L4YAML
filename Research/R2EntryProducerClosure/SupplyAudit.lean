import Tests.Guards.Proofs.RelaySupplyCensus

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus

set_option maxHeartbeats 0 in
run_cmd do
  let (es, skipped) ← edges (ns ++ `content_dispatch_routed)
  let mut tally : Std.HashMap String Nat := {}
  for e in es do
    let k := (e.how.splitOn " ").head!
    tally := tally.insert k ((tally.getD k 0) + 1)
  let split := es.filter (·.how.startsWith "SPLIT")
  let leaves := split.foldl (fun a e => a ++ e.leaves) #[]
  let pay := leaves.filter (·.startsWith "PAY")
  let decline := leaves.filter (·.startsWith "DECLINE")
  logInfo m!"R2_SUPPLY_TALLY edges={es.size} skipped={skipped} {((tally.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·))}"
  logInfo m!"R2_SUPPLY_SPLITS survived={split.size} leaves={leaves.size} PAY={pay.size} DECLINE={decline.size}"
  for e in es do
    if e.caller == ns ++ `question_open_map || e.caller == ns ++ `compact_open_map then
      logInfo m!"R2_SUPPLY_ROW caller={e.caller} callee={e.callee} binder={e.idx} how={e.how} leaves={e.leaves}"
