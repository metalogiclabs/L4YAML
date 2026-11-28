import Research.R2CompactSlot.JointSibling
import Research.R2ValueOwnership.Controls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness
open R2ConcreteSuppliers R2CompactControls

namespace R2ColonCompositionControls

-- These concrete initialized scanner states precede the new proof.
-- The output is nonempty even though the consumed owner has disappeared.
example : markedCols (questionState R2JointSibling.source 1) = [0, 2] := by decide +kernel
example : markedCols (afterFirstColon R2JointSibling.source) = [0] := by decide +kernel
example : (afterFirstColon R2JointSibling.source).pendingKeys.back? = some none := by decide +kernel
example : (afterFirstColon R2JointSibling.source).currentIndent = 2 := by decide +kernel
example : markedCols (afterFirstColon input6) = [0, 2, 4] := by decide +kernel
example : (afterFirstColon input6).pendingKeys.back? = some none := by decide +kernel
example : (afterFirstColon input6).currentIndent = 6 := by decide +kernel
example : markedCols (afterFirstColon "? a\n: b\n") = [] := by decide +kernel
example : markedCols (questionState "? a\n: b\n" 0) = [0] := by decide +kernel
example : (questionState R2JointSibling.source 1).pendingKeys.back? ≠ some none := by decide +kernel

-- The existing executable matrix includes fuel 0/1/2, empty input,
-- malformed/stamped/flow inputs and nested owners. It is not proof warrant.
#guard R2ValueOwnership.allRows.length == 108
#guard R2ValueOwnership.failures.isEmpty
#guard (R2ValueOwnership.valueRows R2JointSibling.source 0).isEmpty
#guard (R2ValueOwnership.valueRows R2JointSibling.source 1).isEmpty
#guard (R2ValueOwnership.valueRows R2JointSibling.source 2).isEmpty
#guard (L4YAML.TokenParser.parseYaml R2JointSibling.source).isOk
#guard (L4YAML.TokenParser.parseYaml "? ? a\n: e\n").isOk

#eval ("COLON-COMPOSITION-CONTROLS", markedCols (afterFirstColon R2JointSibling.source),
  markedCols (afterFirstColon input6), R2ValueOwnership.allRows.length)

end R2ColonCompositionControls
