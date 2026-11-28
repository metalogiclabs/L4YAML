import L4YAML.Proofs.Production.DocumentProduction
import Lean

open Lean

run_cmd do
  let env := (← getEnv).setExporting false
  let some loop := env.find? `L4YAML.Proofs.StreamAccum.scanLoop_grammar_prod
    | throwError "actual scanner grammar loop absent"
  let some loopBody := loop.value? (allowOpaque := true) | throwError "actual loop body absent"
  let some root := env.find? `L4YAML.Proofs.StreamAccum.scan_content_gives_stream_v2
    | throwError "actual public scanner entry absent"
  let some rootBody := root.value? (allowOpaque := true) | throwError "actual public entry body absent"
  let wired := loopBody.getUsedConstants.contains `R2MapOwnership.Maps.next &&
    rootBody.getUsedConstants.contains `R2MapOwnership.seed_maps
  let expected ← IO.getEnv "R2_MAP_EXPECT_WIRED"
  unless wired == (expected == some "1") do throwError "unexpected loop wiring: {wired}"
  let mut cursor := root.type
  while let .forallE name domain body _ := cursor do
    if domain.getUsedConstants.contains `R2MapOwnership.Maps then
      throwError "public entry gained ownership premise {name}"
    cursor := body
  let mut profiles := #[]
  for name in [`L4YAML.Proofs.StreamAccum.scan_content_gives_stream_v2,
      `L4YAML.Proofs.DocumentProduction.scan_strict_proof,
      `L4YAML.Proofs.DocumentProduction.parse_strict_proof] do
    let some info := env.find? name | throwError "missing capstone {name}"
    let axioms := (← collectAxioms name).map Name.toString |>.qsort (· < ·)
    if axioms.contains "sorryAx" then throwError "accepted capstone contains sorryAx: {name}"
    for leafName in axioms do
      if leafName.contains ".L4YAML.Proofs.StreamAccum.dispatchBlock" &&
          !leafName.startsWith "_private.L4YAML.Proofs.Production.StreamAccum.0." then
        throwError "compile under the canonical module path before comparing private leaves: {leafName}"
    profiles := profiles.push (Json.mkObj [
      ("name", toJson name.toString), ("statement_hash", toJson (toString info.type.hash)),
      ("statement_repr", toJson (reprStr info.type)),
      ("axioms", toJson axioms)])
  let some path ← IO.getEnv "R2_MAP_AUDIT_OUTPUT" | throwError "receipt path required"
  IO.FS.writeFile path (Json.pretty (Json.mkObj [
    ("actual_loop_and_seed_wired", toJson wired), ("profiles", Json.arr profiles),
    ("new_public_ownership_premise", toJson false)]))
  logInfo m!"ACCEPTED-MAP-AUDIT loop_and_seed_wired={wired} roots=3 sorryAx=0 public_external_maps_premise=absent"
