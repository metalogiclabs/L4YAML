module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public section
open L4YAML L4YAML.Scanner L4YAML.TokenParser L4YAML.Proofs.RegisterWitness

def walkLanded : Nat → ScannerState → IO Nat
  | 0, _ => throw <| IO.userError "landed-slot control exhausted source traversal fuel"
  | fuel + 1, sc => do
    match scanNextToken_preprocess sc, scanNextToken sc with
    | .ok none, .ok none => pure 0
    | .ok (some (prep, c)), .ok (some out) =>
      let marks := markedCols out
      let hit := !prep.inFlow && c == '-' && 0 ∈ marks && 2 ∈ marks
      let later ← walkLanded fuel out
      pure (later + if hit then 1 else 0)
    | _, .error e => throw <| IO.userError s!"accepted landed-slot source failed scanning: {e}"
    | _, _ => throw <| IO.userError "landed-slot preprocess/scan disagreement"

def main : IO Unit := do
  let mut hits := 0
  let mut cases := 0
  for source in ["?\n  ?\n  -\n: w", "?\n  ?\n  - a\n: w"] do
    for crlf in [false, true] do
      let input := if crlf then "\r\n".intercalate (source.splitOn "\n") else source
      unless (parseYaml input).isOk do
        throw <| IO.userError s!"landed-slot fixture rejected: {repr input}"
      let initial := (ScannerState.mk' input).emit .streamStart
      let n ← walkLanded (4 * input.length + 32) initial
      unless n > 0 do
        throw <| IO.userError s!"landed-slot fixture never held both actual ancestor marks: {repr input}"
      hits := hits + n
      cases := cases + 1
  IO.println s!"R2_LANDED_ANCESTOR_CONTROLS cases={cases} accepted={cases} multi_mark_dash_steps={hits} actual_columns=[0,2]"
