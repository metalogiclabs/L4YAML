import Research.R2JointFrames.Controls
import Research.R2SequenceContext.Controls
import Lean

open L4YAML L4YAML.Scanner L4YAML.Proofs
open R2ConcreteSuppliers R2CompactControls R2SequenceControls R2JointFrames

def landingProbeInputs : List (String × Nat) := [
  ("? - ? a\n    : b\n  - c\n: d\n",1),
  ("? - ? a\n  - c\n: d\n",1),
  ("?\n  ? a\n  : b\n- c\n: d\n",1),
  ("?\n  ? a\n- c\n: d\n",1),
  ("? ? a\n  : b\n- c\n: d\n",1),
  ("? - a\n- c\n: d\n",1),
  ("k:\n  ? a\n  : b\n- c\n",1),
  ("? - - a\n  - c\n: d\n",2)]

#eval do
  let rows := landingProbeInputs.toArray.map fun (input,index) =>
    let state := nthDash input index
    let actual : Option Lean.Json := state.map fun (s : ScannerState) => Lean.Json.mkObj [
      ("levels", Lean.Json.arr ((levels s).toArray.map fun (f : L4YAML.Proofs.IndentStackCover.FrameLevel) => Lean.Json.mkObj [
        ("width", Lean.toJson f.width), ("is_sequence", Lean.toJson f.isSeq)])),
      ("marks", Lean.toJson (RegisterWitness.markedCols s))]
    Lean.Json.mkObj [("input", Lean.toJson input), ("dash_index", Lean.toJson index),
      ("scanner_accepts", Lean.toJson (scan input).isOk),
      ("parser_accepts", Lean.toJson (L4YAML.TokenParser.parseYaml input).isOk),
      ("actual_dash_state", actual.getD Lean.Json.null)]
  IO.FS.writeFile "Research/R2JointFrames/landing-probe.json" (Lean.Json.pretty (Lean.Json.arr rows))
  IO.println s!"LANDING-PROBE rows={rows.size} actual_states_only=true proof_arm_observation=false"
