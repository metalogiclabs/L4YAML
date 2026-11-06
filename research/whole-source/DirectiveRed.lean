module

import DirectiveControls
meta import DirectiveControls

/-!
Expected-failure control. The official run must reject this single false
equality with the native_decide-false diagnostic. A missing import or other
elaboration failure is not a successful falsification. Qualification is governed
by official CI receipts for the exact source commit.
-/

open MathGraph.WholeSource.DirectiveControls

example : publicAccept one = publicAccept two := by native_decide
