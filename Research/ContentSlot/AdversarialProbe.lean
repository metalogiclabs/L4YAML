module
public import Tests.VerifiedResult
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public section
open L4YAML L4YAML.Scanner L4YAML.TokenParser Tests
namespace Tests.AdversarialInstantiation
namespace ContentSlotSource

def walk : Nat → ScannerState → Bool × Nat
  | 0, _ => (false, 0)
  | fuel + 1, s =>
    match scanNextToken_preprocess s, scanNextToken s with
    | .ok none, .ok none => (true, 0)
    | .ok (some (prep, c)), .ok (some out) =>
      let dis := if prep.allowDirectives then
        {prep with allowDirectives := false, documentEverStarted := true} else prep
      let explicit := c == ':' && !dis.inFlow && dis.explicitKeyLine.isSome &&
        !(scanValueClearKey dis).simpleKey.possible && (dis.col : Int) == dis.explicitKeyCol
      let (rest, n) := walk fuel out
      (rest && (!explicit || prep.col ∈ L4YAML.Proofs.RegisterWitness.markedCols s),
        n + (if explicit then 1 else 0))
    | _, _ => (false, 0)

def nest : Nat → String → String
  | 0, leaf => leaf
  | d + 1, leaf => "?\n" ++ "\n".intercalate
      ((nest d leaf).splitOn "\n" |>.map ("  " ++ ·)) ++ "\n: outer"

def test (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Actual explicit-value source columns"
  for depth in [0, 1, 2, 3, 5, 8] do
    for leaf in ["? leaf\n: value", "? 'quoted'\n: value", "? \"quoted\"\n: value",
        "? [one, two]\n: value", "? {one: two}\n: value", "? &a leaf\n: *a",
        "? &a |\n  line\n: value", "? >\n  line\n: value", "?\n  a: b\n  c: d\n: value",
        "? ? leaf\n  : inner\n: outer", "? - one\n  - two\n: value"] do
      for prologue in ["", "# comment\n", "\uFEFF"] do
        for crlf in [false, true] do
          let input := prologue ++ nest depth leaf
          let input := if crlf then "\r\n".intercalate (input.splitOn "\n") else input
          let s := (ScannerState.mk' input).emit .streamStart
          let s := if s.peek? == some '\uFEFF' then s.consumeBOM else s
          let (holds, count) := walk (4 * input.length + 32) s
          check state s!"accepted source, depth {depth}, crlf {crlf}: {repr input}"
            (parseYamlSingle input).isOk
          check state s!"every reached explicit value selects an actual mark ({count}): {repr input}"
            (holds && count > 0)

end ContentSlotSource

end Tests.AdversarialInstantiation

def main : IO Unit := do
  let state ← IO.mkRef ({} : TestCollector)
  Tests.AdversarialInstantiation.ContentSlotSource.test state
  let results ← finish state
  let failures := results.filter fun r => r.outcome.isFail
  if !failures.isEmpty then
    for f in failures do IO.eprintln s!"FAIL {f.name}"
    throw <| IO.userError "explicit-value controls failed"
  IO.println s!"ADVERSARIAL_SOURCE_COLUMNS passed={results.size} failed={failures.size}"
