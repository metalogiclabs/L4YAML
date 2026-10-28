import L4YAML

open L4YAML L4YAML.Scanner

namespace L4YAML.Tests.Probes

private def accepted (source : String) : Bool :=
  match L4YAML.TokenParser.parseYaml source with
  | .ok _ => true
  | .error _ => false

private def noPopLandingCounts (source : String) : Nat × Nat := Id.run do
  let mut state := ScannerState.mk' source
  let mut own := 0
  let mut other := 0
  for _ in [:64] do
    match scanNextToken_preprocess state with
    | .ok (some (prep, _)) =>
      if prep.line != state.line then
        let stackShape := fun s : ScannerState =>
          s.indents.map fun frame => (frame.column, frame.isSequence)
        if stackShape prep == stackShape state then
          if (prep.col : Int) == state.currentIndent then
            own := own + 1
          else
            other := other + 1
    | _ => break
    match scanNextToken state with
    | .ok (some next) => state := next
    | _ => break
  return (own, other)

#guard accepted "a: 1\nb: 2\n"
#guard accepted "a:\n  x: 1\nb: 2\n"
#guard accepted "- a\n- b\n"
#guard accepted "- a: 1\n  b: 2\n"

-- A sequence root cannot become a mapping root without a document boundary.
#guard !accepted "- a\nb: 2\n"
#guard !accepted "- a\n? b\n: c\n"
#guard !accepted "- a\n: b\n"

-- A no-pop landing can be at the own level or elsewhere: the two cases must
-- not be conflated by a proposed mapping-continuation repair.
#guard noPopLandingCounts "a: 1\nb: 2" == (1, 0)
#guard noPopLandingCounts "k:\n  a: 1\n  b: 2" == (1, 1)

end L4YAML.Tests.Probes
