import L4YAML.Proofs.Production.DocumentProduction
import L4YAML.Proofs.Production.StreamAccum
import Scripts.Path.CapstonePath

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let reached := Scripts.Path.CapstonePath.reach env Scripts.Path.CapstonePath.roots
  for n in [`L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol,
      `L4YAML.Proofs.StreamAccum.marked_col_of_explicit_source,
      `L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,
      `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock,
      `L4YAML.Proofs.StreamAccum.accum_block_pending] do
    logInfo m!"VALUE_PACK_REACH {n} exists={env.contains n} reached={reached.contains n}"
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for n in [`L4YAML.Proofs.StreamAccum.marked_col_of_explicit_source,
      `L4YAML.Proofs.StreamAccum.every_mark_of_covered_chain] do
    if env.contains n then
      unless reached.contains n do throwError "new lemma is not consumed by a capstone: {n}"
      let axioms ← liftCoreM (collectAxioms n)
      unless axioms.all standard.contains do throwError "new lemma has a nonstandard axiom: {n} {axioms}"
      logInfo m!"VALUE_PACK_NEW_LEMMA {n} reached=true standard_only=true axioms={axioms}"
  for n in [`L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,
      `L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent,
      `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock,
      `L4YAML.Proofs.StreamAccum.accum_block_pending,
      `L4YAML.Proofs.DocumentProduction.scan_strict_proof,
      `L4YAML.Proofs.DocumentProduction.parse_strict_proof] do
    let axioms ← liftCoreM (collectAxioms n)
    let native := axioms.filter fun a => (a.toString.splitOn "._native.native_decide.ax_").length > 1
    let other := axioms.filter fun a => !standard.contains a && !native.contains a
    unless other.isEmpty do throwError "unexpected axiom {n}: {other}"
    logInfo m!"VALUE_PACK_AXIOMS {n} standard={axioms.size-native.size} native={native.size} other=0"
    for a in axioms.qsort (fun a b => a.toString < b.toString) do
      logInfo m!"VALUE_PACK_AXIOM {n} {a}"
