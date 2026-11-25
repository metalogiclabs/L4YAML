module
import all L4YAML.Proofs.Production.DocumentProduction
import all L4YAML.Proofs.Production.StreamAccum
import all L4YAML.Proofs.Serialization.TraceOf.ContentBridge
import Scripts.Path.CapstonePath
public meta import Scripts.Path.CapstonePath
import Research.NestedAnchorObligation.Controls

open Lean Elab Command
open Scripts.Path.CapstonePath

-- Read actual elaborated declarations, not a textual dependency guess.
run_cmd do
  let env ← getEnv
  for n in roots do
    let some ci := env.find? n | throwError "missing capstone {n}"
    unless (ci.value? (allowOpaque := true)).isSome do
      throwError "unreadable capstone body {n}"
  let r := reach env roots
  let shown := shownSet r
  let critical : List Name :=
    [`L4YAML.Proofs.StreamAccum.PendingNode.pendingContent,
     `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent,
     `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock,
     `L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,
     `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock,
     `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent,
     `L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent]
  for n in critical do
    unless declReached shown n.toString do throwError "critical declaration no longer reached: {n}"
  for n in dropSet do
    unless r.contains n do throwError "deletion-set declaration no longer reached: {n}"
  let newNs := `L4YAML.Research.NestedAnchorObligation.Controls
  let (newReached,newTotal) := moduleReach env r newNs
  unless newTotal>0 && newReached==0 do throwError "unexpected research reach {newReached}/{newTotal}"
  logInfo m!"OBLIGATION_IMPACT critical_declarations_reached={critical.length} deletion_set_reached={dropSet.length} new_controls_reached={newReached}/{newTotal} discharged=0"
  for n in critical do
    logInfo m!"STILL_REACHED {n}"
  let aliasNs := `L4YAML.Tests.Guards.AnchoredAliasAssurance
  -- The existing family theorem was qualified separately, but is not imported by
  -- these owner capstones. Do not turn absence from this environment into a claim
  -- about the contents of the separately qualified research module.
  logInfo m!"BOUNDARY anchored_family_imported_by_capstones={(r.toArray.any aliasNs.isPrefixOf)} universal_scan_trace_proved_by_this_experiment=false"

-- Proof irrelevance forbids observing which Prop disjunct a run used.
-- The completion target must be the informative left-side continuation.
example (s : L4YAML.Scanner.ScannerState) : L4YAML.Proofs.StreamAccum.PackAlt s := trivial
