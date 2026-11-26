module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public section
open L4YAML L4YAML.Scanner L4YAML.TokenParser L4YAML.Proofs.RegisterWitness

def walkLanded : Nat → ScannerState → IO (Nat × Nat)
  | 0, _ => throw <| IO.userError "slot control exhausted source traversal fuel"
  | fuel + 1, sc => do
    match scanNextToken_preprocess sc, scanNextToken sc with
    | .ok none, .ok none => pure (0, 0)
    | .ok (some (prep, c)), .ok (some out) =>
      let marks := markedCols out
      let multi := !prep.inFlow && c == '-' && 0 ∈ marks && 2 ∈ marks
      let own := !prep.inFlow && c == '-' && marks == [0]
      let (laterMulti, laterOwn) ← walkLanded fuel out
      pure (laterMulti + (if multi then 1 else 0), laterOwn + (if own then 1 else 0))
    | _, .error e => throw <| IO.userError s!"accepted slot source failed scanning: {e}"
    | _, _ => throw <| IO.userError "slot preprocess/scan disagreement"

def main : IO Unit := do
  let mut multiHits := 0
  let mut ownHits := 0
  let mut cases := 0
  for (source, multi) in [("?\n  ?\n  -\n: w", true), ("?\n  ?\n  - a\n: w", true),
      ("? -\n: w", false), ("? - a\n: w", false)] do
    for crlf in [false, true] do
      let input := if crlf then "\r\n".intercalate (source.splitOn "\n") else source
      unless (parseYaml input).isOk do
        throw <| IO.userError s!"slot fixture rejected: {repr input}"
      let initial := (ScannerState.mk' input).emit .streamStart
      let (multiN, ownN) ← walkLanded (4 * input.length + 32) initial
      unless (if multi then multiN > 0 else ownN > 0) do
        throw <| IO.userError s!"slot fixture missed its declared actual mark domain: {repr input}"
      multiHits := multiHits + multiN
      ownHits := ownHits + ownN
      cases := cases + 1
  IO.println s!"R2_SLOT_CONTROLS cases={cases} accepted={cases} multi_mark_dash_steps={multiHits} own_mark_dash_steps={ownHits} source_initialized=true"
