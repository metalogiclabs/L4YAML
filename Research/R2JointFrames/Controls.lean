import Research.R2CompactSlot.Controls
import L4YAML.Parser.Composition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open R2ConcreteSuppliers R2CompactControls

namespace R2JointFrames

-- All levels are a projection of the actual scanner stack. The sentinel
-- has negative width and contributes no grammar collection.
def levels (sc : ScannerState) : List FrameLevel :=
  sc.indents.toList.reverse.filterMap fun e =>
    if e.column < 0 then none
    else some (if e.isSequence then FrameLevel.seq e.column.toNat else FrameLevel.map e.column.toNat)

def mixed : String := "? - ? a\n    : b\n  - c\n: d\n"

example : levels ((ScannerState.mk' "").emit .streamStart) = [] := by decide +kernel
example : levels (questionState "? a\n: b\n" 0) = [FrameLevel.map 0] := by decide +kernel
example : levels (questionState mixed 1) =
    [FrameLevel.map 4, FrameLevel.seq 2, FrameLevel.map 0] := by decide +kernel
example : RegisterWitness.markedCols (questionState mixed 1) = [0,4] := by decide +kernel
example : levels (afterFirstColon mixed) =
    [FrameLevel.map 4, FrameLevel.seq 2, FrameLevel.map 0] := by decide +kernel
example : RegisterWitness.markedCols (afterFirstColon mixed) = [0] := by decide +kernel
#guard (L4YAML.TokenParser.parseYaml mixed).isOk
#guard (L4YAML.TokenParser.parseYaml "? ? - a\n    - b\n  : c\n: d\n").isOk

end R2JointFrames
