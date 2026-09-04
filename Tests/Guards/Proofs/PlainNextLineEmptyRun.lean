import L4YAML.Surface.Node

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `[134]`'s `GStar` admits an empty continuation line (DOCS item 70)

`Surface/Scalars.lean` models `[134] s-ns-plain-next-line(n,c)` with

    GStar (SNbNsPlainInLineEntry c) s₃ s'

and says so in its own note: the spec requires **at least one** `ns-plain-char`
there, the scanner enforces it with a content-length check, and strengthening
the repetition to `GPlus` is a TODO.  This file is what that TODO costs, stated
as a derivation rather than as prose.

**The over-admission.**  With `GStar`, a continuation line may consume nothing
after `[69'] s-flow-line-prefix(n)`, which at `n = 0` is itself zero-width.  So
`[135] ns-plain-multi-line` — and through `[159]` the whole
`[158] ns-flow-content` — admits a derivation whose END is at **column 0**.
The two lemmas below are that derivation, machine-checked.

**What it blocks.**  Item 70 wanted a column invariant on `InteriorGap`
(`0 < sp_scan.col`) so that a flow-interior separator whose landing under-runs
the stack's index could be refused by §6.1: the landing is at column 0, the
cursor is not, so `LandingTabFacts`' "a break was crossed" premise fires.  Every
indicator producer pays that from `glit_col`, and `InteriorGap.props` reads it
off `propsRun_col_gt` at index 0.  The four CONTENT producers cannot pay it at
all — not because the multi-line productions are hard, but because on this
surface the fact is **false**, and these two lemmas are the counter-model.

So the column is downstream of one of two things, neither of which is item 70:

* strengthen `[134]`'s entry repetition to `GPlus`, threading the scanner's
  content-length check through `collectPlainScalarLoop`'s recursion (4 producer
  sites: `ScalarFoldAt` ×2, `ScalarProduction` ×2); or
* carry `sc.needIndentCheck = true` beside the column — `LandingTabFacts`
  accepts either — which is scanner-side, and whose idiom already exists as
  `dispatchContent_{anchor,alias,tag}_line_nic`.

**When `[134]` is strengthened, this file must go**, together with the note in
`Surface/Scalars.lean` that predicts it.  A failure here is the fix landing, not
a regression. -/

namespace L4YAML.Tests.Guards.PlainNextLineEmptyRun

open L4YAML L4YAML.Surface

/-- `a⏎` in flow-in at index 0: `[133]` takes the `a`, then ONE `[134]`
    continuation that consumes only the break — no `ns-plain-char` at all. -/
lemma multiLine_ends_at_col_zero :
    SNsPlainMultiLine 0 .flowIn ⟨['a', '\n'], 0⟩ ⟨[], 0⟩ :=
  .mk 0 .flowIn _ ⟨['\n'], 1⟩ _
    (.mk .flowIn _ _ _
      (.nonIndicator .flowIn 'a' ['\n'] 0
        (by refine ⟨?_, ?_⟩ <;> simp [isNsChar, CharPredicates.isFlowIndicatorProp] <;> decide)
        (by simp [CharPredicates.isIndicatorProp] <;> decide))
      (GStar.nil _))
    (GStar.cons _ ⟨[], 0⟩ _
      (.mk 0 .flowIn ⟨['\n'], 1⟩ ⟨['\n'], 1⟩ ⟨[], 0⟩ ⟨[], 0⟩ ⟨[], 0⟩ ⟨[], 0⟩
        (GStar.nil _) (.lf [] 1) (GStar.nil _)
        (.mk 0 _ _ _ (.zero _) (GOpt.none _))
        (GStar.nil _))
      (GStar.nil _))

/-- …and so `[158] ns-flow-content`, which is what a content step hands the
    accumulation invariant back, can end at column 0.  This is the statement
    `InteriorGap`'s column field would have to refute. -/
lemma flowContent_ends_at_col_zero :
    SFlowContent 0 .flowIn ⟨['a', '\n'], 0⟩ ⟨[], 0⟩ :=
  .plain 0 .flowIn _ _ (by
    show SNsPlainMultiLine 0 .flowIn _ _
    exact .mk 0 .flowIn _ ⟨['\n'], 1⟩ _
      (.mk .flowIn _ _ _
        (.nonIndicator .flowIn 'a' ['\n'] 0
          (by refine ⟨?_, ?_⟩ <;> simp [isNsChar, CharPredicates.isFlowIndicatorProp] <;> decide)
          (by simp [CharPredicates.isIndicatorProp] <;> decide))
        (GStar.nil _))
      (GStar.cons _ ⟨[], 0⟩ _
        (.mk 0 .flowIn ⟨['\n'], 1⟩ ⟨['\n'], 1⟩ ⟨[], 0⟩ ⟨[], 0⟩ ⟨[], 0⟩ ⟨[], 0⟩
          (GStar.nil _) (.lf [] 1) (GStar.nil _)
          (.mk 0 _ _ _ (.zero _) (GOpt.none _))
          (GStar.nil _))
        (GStar.nil _)))

/-! Both print `depends on axioms: [propext]` — the over-admission is the
grammar's, not an artifact of how it is witnessed. -/
#print axioms multiLine_ends_at_col_zero
#print axioms flowContent_ends_at_col_zero

end L4YAML.Tests.Guards.PlainNextLineEmptyRun
