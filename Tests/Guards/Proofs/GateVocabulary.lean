/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.Scanner

/-! # A name in prose is a claim about the environment (DOCS items 265, 266)

§8.1's floor for a flow open is read at the CLOSE (item 172), and the check
that reads it is `scanNextToken_checkFlowValueIndent`.  The name the prose kept
using for an open-side check, `scanNextToken_checkBlockFlowIndent`, resolves to
no constant at all, and item 265 found it in thirty-two places across fourteen
files — describing a
dispatcher layer `scanNextToken` does not have, and in one place carrying a
claim about a PROOF: that the run-end half of the flow open's under-run "is not
a deferral at all", two lines above the `exact drop_ride` that rides β.5's
escape on exactly that half.

A backticked identifier in a docstring is a claim, and it is the one class of
claim nothing in the build checks.  Lean does not read its own comments; a
census that reads the environment cannot see them.  So the reading is
`scripts/gate_vocab.py`'s and the LITERAL is here — the same
pin-from-the-other-side the flip instruments use, turned on prose.

Two vocabularies are read.  The first is the dispatcher's own:
`scanNextToken_…`, `scanLoop_…` and `scanLoopIx_…` spelled out, and the short
`check…` form the prose usually uses, which is required to carry two
capitalized segments so that one-letter macros stay out of it.  The second is
the tree's suffix for a lemma that closes a branch as false, `…_refuted`, added
at item 266 after a second phantom of the same kind turned up in exactly the
place item 265 had just been working: a docstring naming the run-end
refutation as the twin an existing lemma is one production in from, when
items 264-266 measured that no such lemma can be stated at that step.  A name
resolves when it is the final component of a constant in the wide environment,
bare or under any of the three prefixes.

Three numbers stand beside the verdict, because each is a way the check could
pass while reading less than it appears to (§9):

* `families` — references of the form `dispatchStructural_none_*`, which name a
  family and not a constant.  Excluded from the verdict rather than matched.
* `wrapped` — a name a line break splits, whose closing backtick the scan
  cannot see.  Two are genuine wraps in `…FlowMonoChain.Sync.Scenarios.Endpoint`
  and resolve when joined; the third is a `` `` ``-quoted name in
  `PuntCoverInputs`, which the elaborator resolves itself.  A gate's wrap is
  found from its opening half, which carries the prefix; a refutation's cannot
  be, since the suffix is the whole discrimination, so those are found from the
  CONTINUATION line instead, and the continuation is recognized
  without requiring the underscore, which the break may leave on either side.
* `refuted` — how many of the names come from the second vocabulary.  A
  widening that read none of them would pass the same verdict as one that read
  them all.
* `self` — this file's own two mentions.  It has to spell the missing gate out
  in order to say what the check is for, so it is the one file the scan skips,
  and the skip is counted rather than silent.
-/

namespace L4YAML.Tests.Guards.GateVocabulary

/-- What `scripts/gate_vocab.py` reads over `L4YAML/` and `Tests/`.

    **`mentions` moves whenever prose cites a gate, and that is the point.**
    Item 268's own sections added four, across two dispatcher names it had to
    cite by name, and all four resolve.  `unresolved` is what the check is for;
    `mentions` is the population it was taken over, and a `mentions` that never
    moved would mean the scan had stopped seeing new prose.  (The names are not
    spelled here: this file is the one the scan skips, so a name written in this
    docstring would move `self` instead, for no reading.) -/
def expectedGateVocab : String :=
  "names=107 mentions=437 families=13 refuted=7 wrapped=3 self=2 unresolved=0"

end L4YAML.Tests.Guards.GateVocabulary
