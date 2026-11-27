module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public section

open L4YAML L4YAML.Scanner L4YAML.TokenParser L4YAML.Proofs.RegisterWitness

def walk : Nat → ScannerState → IO (Nat × Nat)
  | 0, _ => throw <| IO.userError "control traversal exhausted its declared fuel"
  | fuel + 1, sc => do
    match scanNextToken sc with
    | .error e => throw <| IO.userError s!"source-initialized scan failed: {e}"
    | .ok none => pure (0, 0)
    | .ok (some out) =>
      let mut starts := 0
      let mut ends := 0
      if out.tokens.size > sc.tokens.size then
        match out.tokens.back?.map (fun (t : Positioned YamlToken) => t.val) with
        | some YamlToken.documentStart => starts := 1
        | some YamlToken.documentEnd => ends := 1
        | _ => pure ()
      if starts + ends > 0 then
        unless out.explicitKeyLine == none && (markedCols out).isEmpty do
          throw <| IO.userError "document marker retained a live explicit-key mark"
      let (a, b) ← walk fuel out
      pure (starts + a, ends + b)

def main : IO Unit := do
  let mut sources := 0
  let mut starts := 0
  let mut ends := 0
  for history in ["", "? old\n: &a value\n...\n", "?\n  ? inner\n  : value\n: outer\n...\n"] do
    for body in ["", "v", "- x", "? key\n: value", "&a v", "[1, 2]", "|-\n  x"] do
      for prologue in ["", "# comment\n", "\uFEFF"] do
        for crlf in [false, true] do
          let text := prologue ++ history ++ "---\n" ++ body ++ "\n...\n---\n- y\n"
          let text := if crlf then "\r\n".intercalate (text.splitOn "\n") else text
          unless (parseYaml text).isOk do
            throw <| IO.userError s!"positive control source rejected: {repr text}"
          let initial := (ScannerState.mk' text).emit .streamStart
          let initial := if initial.peek? == some '\uFEFF' then initial.consumeBOM else initial
          let (a, b) ← walk (text.length * 4 + 32) initial
          unless a == 2 && b > 0 do
            throw <| IO.userError "required marker states were not reached"
          sources := sources + 1
          starts := starts + a
          ends := ends + b
  IO.println s!"DOCUMENT_MARKER_CONTROLS sources={sources} start_states={starts} end_states={ends} initialized_from_source=true actual_marked_columns_empty=true"
