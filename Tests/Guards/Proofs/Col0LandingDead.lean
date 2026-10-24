import L4YAML.Scanner.Scanner

/-! # The explicit-key register at column-0 content landings (item 347, Rule 2)

The register (`explicitKeyLine`) read after the token scanned at each landing.  A column-0
content landing (not `-`, not `:`) leaves `none` when every open `?` has met its `:` — but NOT
after an inner `?` that never did: the hook closes one level (the register's own column) per
preprocess and re-reads the outer key, so `ExplicitValueRefused` is FALSE at that landing
although the document parses.  A column-0 `-` and an indented landing keep the register. -/

open L4YAML L4YAML.Scanner

namespace Col0LandingDead

/-- The register after the `n`-th token of `input` (0-based), `none` on error/EOF. -/
def eklAfter (input : String) (n : Nat) : Option (Option Nat) :=
  go (ScannerState.mk' input) (n + 1)
where
  go (s : ScannerState) : Nat → Option (Option Nat)
    | 0 => none
    | k + 1 =>
      match scanNextToken s with
      | .ok (some s') => if k = 0 then some s'.explicitKeyLine else go s' k
      | _ => none

-- content at column 0 under an open `?`: dead
#guard eklAfter "?\na: 1\n" 1 = some none
#guard eklAfter "?\n  a: 1\nb: 2\n" 4 = some none
-- nested `?`, the column-0 landing closes BOTH keys
#guard eklAfter "? ? a\n  : b\nc: 1\n" 4 = some (some 0)
#guard eklAfter "? ? a\n  : b\nc: 1\n" 5 = some none
#guard eklAfter "?\n  ? a\n  : b\nc: 1\n" 5 = some none
-- REFUTATION of "a column-0 content landing kills the register": an inner `?` never closed
-- by `:` — the hook closes at the inner column, re-reads the outer; the document parses.
#guard eklAfter "?\n  ? a\nc: 1\n" 3 = some (some 0)
#guard eklAfter "?\n  ? a\n  ? b\nc: 1\n" 5 = some (some 0)
#guard eklAfter "? ? a\nc: 1\n" 4 = some none
-- the two excluded shapes: a column-0 `-` keeps the register, an indented landing keeps it
#guard eklAfter "?\n- a\n" 1 = some (some 0)
#guard eklAfter "?\n  a: 1\n  b: 2\n: v\n" 4 = some (some 0)

end Col0LandingDead
