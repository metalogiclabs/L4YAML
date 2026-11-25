module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public section
namespace L4YAML.Research.NestedAnchorObligation.RootProducerControls
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.RegisterWitness

-- Adversarial instances before attempting the root producer's payment.
-- A fresh root '-' must have no marked explicit-key column before or after it.
def check (text : String) : IO Unit := do
  unless (parseYamlSingle text).isOk do throw <| IO.userError s!"root source rejected: {text}"
  let initial := (ScannerState.mk' text).emit .streamStart
  let initial := if initial.peek? == some '\uFEFF' then initial.consumeBOM else initial
  match scanNextToken_preprocess initial, scanNextToken initial with
  | .ok (some (prep,'-')), .ok (some out) =>
    unless (markedCols initial).isEmpty && (markedCols prep).isEmpty && (markedCols out).isEmpty do
      throw <| IO.userError "root '-' introduced an explicit-key mark"
    unless initial.explicitKeyLine == none && out.explicitKeyLine == none do
      throw <| IO.userError "root '-' revived the explicit-key register"
  | _,_ => throw <| IO.userError "root '-' not reached from real initialization"

def main : IO Unit := do
  let mut n := 0
  for root in ["-","- x","-\n- x","-\n  - x","-\n  ? key\n  : value","- &a v\n- *a","-\n  target: &a value\n  copy: *a"] do
    for prologue in ["","# comment\n","\uFEFF"] do
      for crlf in [false,true] do
        let text := prologue ++ root
        let text := if crlf then "\r\n".intercalate (text.splitOn "\n") else text
        check text
        n := n+1
  IO.println s!"ROOT_PRODUCER executions={n} actual_initialization=true parser_accepts=true marked_columns_before_prep_after_empty=true"
end L4YAML.Research.NestedAnchorObligation.RootProducerControls

def main : IO Unit := L4YAML.Research.NestedAnchorObligation.RootProducerControls.main
