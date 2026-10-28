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

-- The scanner's token stream distinguishes a mapping sibling from a block
-- sequence entry: sharing a no-pop indentation category is not evidence that
-- both land in the same pending-node proof builder.
private def hasBlockSequenceIntro (source : String) : Bool :=
  match scanFiltered source with
  | .error _ => false
  | .ok tokens => tokens.any fun t =>
      match t.val with
      | .blockEntry | .blockSequenceStart => true
      | _ => false

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

-- A no-pop mapping sibling need not pass through a sequence-entry builder.
#guard !hasBlockSequenceIntro "a: 1\nb: 2\n"
#guard !hasBlockSequenceIntro "k:\n  a: 1\n  b: 2\n"
#guard hasBlockSequenceIntro "- a\n- b\n"
#guard hasBlockSequenceIntro "- a: 1\n  b: 2\n"

end L4YAML.Tests.Probes
