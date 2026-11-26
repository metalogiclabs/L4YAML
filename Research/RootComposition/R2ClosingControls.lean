module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public section
open L4YAML L4YAML.Scanner L4YAML.TokenParser L4YAML.Proofs.RegisterWitness

structure Counts where
  accepted : Nat := 0
  rejected : Nat := 0
  values : Nat := 0
  closing : Nat := 0
  closingMarkedBefore : Nat := 0
  explicit : Nat := 0
  ancestors : Nat := 0
  deriving Repr

def walk (input : String) (rs : IO.Ref Counts) : Nat → ScannerState → IO Unit
  | 0, _ => throw <| IO.userError "source traversal fuel exhausted"
  | fuel + 1, sc => do
    match scanNextToken_preprocess sc, scanNextToken sc with
    | .ok none, .ok none => pure ()
    | .ok (some (prep, c)), .ok (some out) =>
      let dis := if prep.allowDirectives then
        {prep with allowDirectives := false, documentEverStarted := true} else prep
      if !dis.inFlow && c == ':' then
        match scanNextToken_dispatchBlockIndicators dis c with
        | .ok (some _) =>
          let clear := scanValueClearKey dis
          let marks := markedCols out
          let n := clear.explicitKeyCol.toNat
          let closes := !scanValueKeySurvives dis clear && 0 ≤ clear.explicitKeyCol
          let expl := clear.explicitKeyLine.isSome && !clear.simpleKey.possible &&
            (dis.col : Int) == clear.explicitKeyCol
          if closes && n ∈ marks then
            throw <| IO.userError s!"CLOSING_COLUMN_REFUTED {repr input} n={n} marks={marks}"
          if expl && n ∈ marks then
            throw <| IO.userError s!"EXPLICIT_COLUMN_REFUTED {repr input} n={n} marks={marks}"
          if 0 ≤ out.currentIndent && out.currentIndent.toNat ∈ marks then
            throw <| IO.userError s!"POST_VALUE_OWN_REFUTED {repr input} marks={marks}"
          rs.modify fun r =>
            { r with
              values := r.values + 1
              closing := r.closing + (if closes then 1 else 0)
              closingMarkedBefore := r.closingMarkedBefore + (if closes && n ∈ markedCols dis then 1 else 0)
              explicit := r.explicit + (if expl then 1 else 0)
              ancestors := r.ancestors + (if marks.isEmpty then 0 else 1) }
        | _ => pure ()
      walk input rs fuel out
    | _, .error e => throw <| IO.userError s!"accepted source failed scan: {e} {repr input}"
    | _, _ => throw <| IO.userError "preprocess/scan disagreement"

def nest : Nat → String → String
  | 0, leaf => leaf
  | d + 1, leaf => "?\n" ++ "\n".intercalate
      ((nest d leaf).splitOn "\n" |>.map ("  " ++ ·)) ++ "\n: outer"

def main : IO Unit := do
  let rs ← IO.mkRef ({} : Counts)
  for depth in [0, 1, 2, 3, 5] do
    for leaf in ["plain", "  indented", "'quoted'", "\"quoted\"", "&a value",
        "!<tag:yaml.org,2002:str> value", "|-\n  block", ">-\n  folded",
        "? a\n: b", "?\n- b", "a:\n- b", "a:\n  - b",
        "? ? a\n  : - b\n: c", "? a\n: - b\n: c", "?\n  ? -\n- b",
        "?\n  ? - a\n: w", "[one, {two: three}]", "{one: [two, three]}"] do
      for prologue in ["", "# comment\n", "\uFEFF", "---\n"] do
        for crlf in [false, true] do
          let input := prologue ++ nest depth leaf
          let input := if crlf then "\r\n".intercalate (input.splitOn "\n") else input
          if (parseYaml input).isOk then
            rs.modify fun r => {r with accepted := r.accepted + 1}
            let initial := (ScannerState.mk' input).emit .streamStart
            let initial := if initial.peek? == some '\uFEFF' then initial.consumeBOM else initial
            walk input rs (4 * input.length + 32) initial
          else rs.modify fun r => {r with rejected := r.rejected + 1}
  let r ← rs.get
  unless r.accepted > 0 && r.closingMarkedBefore > 0 && r.explicit > 0 && r.ancestors > 0 do
    throw <| IO.userError "conditional hypotheses were not reached"
  IO.println s!"R2_ACTUAL_CLOSING_CONTROLS {repr r} source_initialized=true"
