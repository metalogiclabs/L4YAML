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

private def noPopIndicatorCounts (source : String) : Nat × Nat × Nat × Nat := Id.run do
  let mut state := ScannerState.mk' source
  let mut ownQuestion := 0
  let mut otherQuestion := 0
  let mut ownColon := 0
  let mut otherColon := 0
  for _ in [:64] do
    match scanNextToken_preprocess state with
    | .ok (some (prep, c)) =>
      if prep.line != state.line then
        let stackShape := fun s : ScannerState =>
          s.indents.map fun frame => (frame.column, frame.isSequence)
        if stackShape prep == stackShape state then
          let own := (prep.col : Int) == state.currentIndent
          if c == '?' then
            if own then ownQuestion := ownQuestion + 1
            else otherQuestion := otherQuestion + 1
          else if c == ':' then
            if own then ownColon := ownColon + 1
            else otherColon := otherColon + 1
    | _ => break
    match scanNextToken state with
    | .ok (some next) => state := next
    | _ => break
  return (ownQuestion, otherQuestion, ownColon, otherColon)

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

private def oneBlockMapping (source : String) (entries : Nat) : Bool :=
  match L4YAML.TokenParser.parseYaml source with
  | .error _ => false
  | .ok docs =>
    if docs.size != 1 then false
    else
      match docs[0]!.value with
      | .mapping .block pairs _ _ => pairs.size == entries
      | _ => false

private def singletonBlockSequenceMap (source : String) (entries : Nat) : Bool :=
  match L4YAML.TokenParser.parseYaml source with
  | .error _ => false
  | .ok docs =>
    if docs.size != 1 then false
    else
      match docs[0]!.value with
      | .sequence .block items _ _ =>
        if items.size != 1 then false
        else
          match items[0]! with
          | .mapping .block pairs _ _ => pairs.size == entries
          | _ => false
      | _ => false

-- Item 381: inspect the AST, not just acceptance, for a multi-entry mapping
-- nested in the FIRST sequence item, then a later sequence sibling.
private def blockSequenceFirstMap (source : String)
    (mapEntries totalEntries : Nat) : Bool :=
  match L4YAML.TokenParser.parseYaml source with
  | .error _ => false
  | .ok docs =>
    if docs.size != 1 then false
    else
      match docs[0]!.value with
      | .sequence .block items _ _ =>
        if items.size != totalEntries || items.isEmpty then false
        else
          match items[0]! with
          | .mapping .block pairs _ _ => pairs.size == mapEntries
          | _ => false
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

-- Unlike the broad no-pop count, this census counts only INDICATOR openers
-- at line-start landings.  A plain sibling key is not an opener indicator.
#guard noPopIndicatorCounts "a: 1\nb: 2\n" == (0, 0, 0, 0)

-- Genuine accepted indicator landings occur both at the current level and
-- at a fresh deeper level, even though the ordinary-root example has none.
#guard accepted "-\n  ? a\n  : b\n"
#guard noPopIndicatorCounts "-\n  ? a\n  : b\n" == (0, 1, 1, 0)
#guard accepted "-\n  : b\n"
#guard noPopIndicatorCounts "-\n  : b\n" == (0, 0, 0, 1)
#guard accepted "-\n  ? a\n  : b\n  ? c\n  : d\n"
#guard noPopIndicatorCounts "-\n  ? a\n  : b\n  ? c\n  : d\n" == (1, 1, 2, 0)

-- These accepted ROOT indicator cases still emit no sequence-entry tokens.
#guard accepted "? a\n: b\n? c\n: d\n"
#guard noPopIndicatorCounts "? a\n: b\n? c\n: d\n" == (1, 0, 2, 0)
#guard !hasBlockSequenceIntro "? a\n: b\n? c\n: d\n"
#guard accepted ": a\n: b\n"
#guard noPopIndicatorCounts ": a\n: b\n" == (0, 0, 1, 0)
#guard !hasBlockSequenceIntro ": a\n: b\n"
#guard accepted "a: 1\n? b\n: 2\n"
#guard noPopIndicatorCounts "a: 1\n? b\n: 2\n" == (1, 0, 1, 0)
#guard !hasBlockSequenceIntro "a: 1\n? b\n: 2\n"

-- The accepted no-pop-other opener is a FIRST nested mapping entry, not a
-- second document.  The root explicit siblings form one two-entry mapping.
#guard singletonBlockSequenceMap "-\n  : b\n" 1
#guard singletonBlockSequenceMap "-\n  ? a\n  : b\n" 1
#guard oneBlockMapping "? a\n: b\n? c\n: d\n" 2

-- Explicit and empty-key first entries, compact siblings, comments and a
-- following '-' are all retained in one document with the intended AST shape.
#guard blockSequenceFirstMap "-\n  ? a\n  : b\n  ? c\n  : d\n- tail\n" 2 2
#guard blockSequenceFirstMap "-\n  : b\n  : c\n- tail\n" 2 2
#guard blockSequenceFirstMap "-\n  # between entries\n  ? a\n  : b\n  ? c\n  : d\n- tail\n" 2 2

-- In contrast, these three new indicators after a FINISHED scalar are
-- rejected.  This is a bounded scanner/parser observation, not a theorem
-- that the proof-builder branch is universally unreachable.
#guard !accepted "- a\n  : b\n"
#guard !accepted "- a\n  ? b\n  : c\n"
#guard !accepted "- a\n: b\n"

end L4YAML.Tests.Probes
