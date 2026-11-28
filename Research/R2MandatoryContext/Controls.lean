import Research.R2ScannerMapOwnership.JointColon
import Research.R2SequenceContext.ConcreteContexts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open L4YAML L4YAML.Scanner

namespace R2MandatoryContext

def sources : List String := ["", "? a\n: b\n", ": b\n", "a: b\n", "&p a: b\n",
  "? a\n? b\n: c\n", "? a\n: b\n? c\n: d\n", "? - ? a\n    : b\n  - c\n: d\n",
  "? - ? a\n  - c\n: d\n", "? - - a\n    - b\n  - c\n: d\n",
  "?\n  - a\n  - b\n: c\n", "? [a, {b: c}]\n: d\n", "? &p !foo a\n: b\n",
  "? &p\n: b\n", "? |\n  a\n: b\n", "- a\n? b\n: c\n",
  "---\n? a\n: b\n...\n", "\uFEFF? a\n: b\n"]

#guard sources.all fun input => R2MapOwnership.checkSteps 0 ((ScannerState.mk' input).emit .streamStart)
#guard sources.all fun input => R2MapOwnership.checkSteps 1 ((ScannerState.mk' input).emit .streamStart)
#guard sources.all fun input => R2MapOwnership.checkSteps 2 ((ScannerState.mk' input).emit .streamStart)
#guard sources.all fun input => R2MapOwnership.checkSteps 128 ((ScannerState.mk' input).emit .streamStart)

-- Neither malformed placement nor a missing captured event is turned into a
-- fabricated proof state. Scanner failures are preserved as observations.
#guard (L4YAML.Scanner.scan "- a\n? b\n: c\n").isOk = false
#guard (L4YAML.TokenParser.parseYaml "? a\n? b\n: c\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? a\n: b\n? c\n: d\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? - ? a\n  - c\n: d\n").isOk

end R2MandatoryContext
