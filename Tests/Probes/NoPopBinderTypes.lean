import L4YAML.Proofs.Production.StreamAccum
import Lean

/-!
# No-pop opener: elaborated binder contract

Read the *kernel-facing types* of the two park builders' resume carriers and
the indicator opener's destination.  This deliberately checks proposition
interfaces, not branch reachability or the existence of a missing bridge.
-/

open Lean Meta Elab Command

namespace L4YAML.Tests.Probes.NoPopBinderTypes

def carrierKinds (declaration binder : Name) : MetaM (Bool × Bool) := do
  let info ← getConstInfo declaration
  forallTelescope info.type fun xs _ => do
    for x in xs do
      if (← x.fvarId!.getUserName) == binder then
        let ty ← inferType x
        let hasSeq := (ty.find? (·.isConstOf ``L4YAML.Surface.SCompactSeqTail)).isSome ||
          (ty.find? (·.isConstOf ``L4YAML.Proofs.StreamAccum.SeqEntryTail)).isSome
        let hasMap := (ty.find? (·.isConstOf ``L4YAML.Surface.SCompactMapTail)).isSome
        return (hasSeq, hasMap)
    throwError "missing {binder} on {declaration}"

run_cmd do
  let ns := `L4YAML.Proofs.StreamAccum
  let builders := [`accum_block_on_pendingBlock, `accum_block_on_pendingBlockContent]
  for b in builders do
    let (hasSeq, hasMap) ← liftTermElabM <| carrierKinds (ns ++ b) `h_closeF_old
    unless hasSeq && !hasMap do
      throwError "builder contract changed: {b} hasSeq={hasSeq} hasMap={hasMap}"
  let (hasSeq, hasMap) ← liftTermElabM <| carrierKinds
    (ns ++ `indicator_open_map) `h_res_land
  unless hasMap && !hasSeq do
    throwError "opener contract changed: hasSeq={hasSeq} hasMap={hasMap}"
  for b in [`indicator_open_map, `colon_open_map, `question_open_map] do
    let (hasSeq, hasMap) ← liftTermElabM <| carrierKinds (ns ++ b) `h_fresh_land
    unless hasSeq && hasMap do
      throwError "fresh continuation contract changed: {b} hasSeq={hasSeq} hasMap={hasMap}"

end L4YAML.Tests.Probes.NoPopBinderTypes
