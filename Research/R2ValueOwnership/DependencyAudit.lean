import L4YAML.Proofs.Production.StreamAccum
import Scripts.Path.CapstonePath

open Lean Elab Command Scripts.Path.CapstonePath

run_cmd do
  let env ← getEnv
  let root := `L4YAML.Proofs.StreamAccum.scan_content_gives_stream_v2
  let live := reach env [root]
  let required := [
    `L4YAML.Proofs.StreamAccum.ValueOwnership.TopUnmarked,
    `L4YAML.Proofs.StreamAccum.ValueOwnership.last_mark_register,
    `L4YAML.Proofs.StreamAccum.ValueOwnership.prepared_last_mark,
    `L4YAML.Proofs.StreamAccum.ValueOwnership.last_column,
    `L4YAML.Proofs.StreamAccum.ValueOwnership.scanValue_top_unmarked,
    `L4YAML.Proofs.StreamAccum.ValueOwnership.no_mark_at_or_above_top,
    `L4YAML.Proofs.StreamAccum.ValueOwnership.after_colon]
  for n in required do
    unless live.contains n do throwError "unspent ownership declaration: {n}"
  let consumer := reach env [`L4YAML.Proofs.StreamAccum.accum_block_pending]
  unless consumer.contains `L4YAML.Proofs.StreamAccum.ValueOwnership.no_mark_at_or_above_top do
    throwError "the actual value consumer does not spend ownership"
  let scannerFact := reach env [`L4YAML.Proofs.StreamAccum.ValueOwnership.after_colon]
  let forbidden := scannerFact.toList.filter fun n =>
    let s := (privateToUserName n).toString
    s.endsWith ".scannerDrop" || s.endsWith ".implicitContinue" ||
      s.endsWith ".dropClose" || s == "sorryAx"
  unless forbidden.isEmpty do throwError "ownership used a grammar escape: {forbidden}"
  logInfo "OWNERSHIP-DEPENDENCIES: all {required.length} declarations reach capstone 7.2; actual consumer spends exclusion; scanner fact uses no grammar escape"
