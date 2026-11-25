module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public section
namespace L4YAML.Research.StateLinkedValuePack
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.RegisterWitness

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

def source (depth width : Nat) (leaf : String) : String := Id.run do
  let mut rows : List String := []
  for i in List.range depth do
    rows := rows ++ [spaces (i * width) ++ "?"]
  rows := rows ++ (leaf.splitOn "\n").map (spaces (depth * width) ++ ·)
  for i in (List.range depth).reverse do
    rows := rows ++ [spaces (i * width) ++ ": value"]
  return "\n".intercalate rows

def check (text : String) : IO (Nat × Nat × Nat) := do
  unless (parseYamlSingle text).isOk do
    throw <| IO.userError s!"generated positive source rejected: {text}"
  let mut sc := (ScannerState.mk' text).emit .streamStart
  let mut paid := 0
  let mut nested := 0
  let mut steps := 0
  for _ in List.range (text.length * 2 + 100) do
    match scanNextToken sc with
    | .error e => throw <| IO.userError s!"scanner rejected parser-positive source: {e}"
    | .ok none => return (paid, nested, steps)
    | .ok (some out) =>
      match scanNextToken_preprocess sc with
      | .ok (some (prep, ':')) =>
        let dis := if prep.allowDirectives then
          {prep with allowDirectives := false, documentEverStarted := true} else prep
        if dis.explicitKeyLine.isSome && !(scanValueClearKey dis).simpleKey.possible &&
            (dis.col : Int) == dis.explicitKeyCol then
          unless (markedCols prep).contains prep.col && (markedCols sc).contains prep.col do
            throw <| IO.userError "accepted explicit value lacks its actual pre-state mark"
          unless !(markedCols sc).isEmpty do
            throw <| IO.userError "empty-domain negative control failed"
          paid := paid + 1
          if (markedCols sc).length > 1 then nested := nested + 1
      | _ => pure ()
      sc := out
      steps := steps + 1
  throw <| IO.userError "scanner control exhausted fuel"

def main : IO Unit := do
  let mut cases := 0
  let mut paid := 0
  let mut nested := 0
  let mut steps := 0
  for depth in [1, 2, 3, 8, 16] do
    for width in [1, 2, 4] do
      for leaf in ["leaf", "[leaf]", "- leaf", "&a leaf", "!!str leaf", "? key\n: value"] do
        for crlf in [false, true] do
          let text := source depth width leaf
          let text := if crlf then "\r\n".intercalate (text.splitOn "\n") else text
          let (p, n, s) ← check text
          cases := cases + 1
          paid := paid + p
          nested := nested + n
          steps := steps + s
  unless cases == 180 && paid > 0 && nested > 0 do
    throw <| IO.userError "reachable control population missing"
  IO.println s!"STATE_LINKED_CONTROLS sources={cases} accepted_explicit_values={paid} nested_mark_cases={nested} scanner_steps={steps} empty_domain_refutations={paid} initialized_from_source=true"
end L4YAML.Research.StateLinkedValuePack

def main : IO Unit := L4YAML.Research.StateLinkedValuePack.main
