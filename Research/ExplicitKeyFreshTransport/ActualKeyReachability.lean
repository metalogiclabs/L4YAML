module
public import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Proofs.Serialization.TokenEvents
public section
open L4YAML L4YAML.Scanner
private def samples : Array (String × String) := #[
  ("plain", "? key\n: value\n"),
  ("double-quoted", "? \"key\"\n: value\n"),
  ("single-quoted", "? 'key'\n: value\n"),
  ("alias", "a: &a x\n? *a\n: value\n"),
  ("anchor-and-scalar", "? &a key\n: value\n"),
  ("tag-and-scalar", "? !!str key\n: value\n"),
  ("empty-property-key", "? &a\n: value\n"),
  ("literal", "? |\n  key\n: value\n"),
  ("folded", "? >\n  key\n: value\n"),
  ("flow-sequence", "? [key]\n: value\n"),
  ("flow-map", "? {key: x}\n: value\n")]
private def check (name input : String) : IO Unit := do
  let mut s := (ScannerState.mk' input).emit .streamStart
  let mut seen := false
  for _ in List.range 64 do
    match scanNextToken_preprocess s with
    | .ok (some (p, ':')) =>
      if p.inFlow == false && p.explicitKeyCol == 0 && p.explicitKeyLine.isSome then
        IO.println s!"ACTUAL_ROOT_COLON form={name} before_col={s.col} colon_col={p.col} drop={decide (p.col < s.col)} saved_possible={p.simpleKey.possible} cleared={(scanValueClearKey p).simpleKey.possible == false}"
        seen := true
    | _ => pure ()
    match scanNextToken s with
    | .ok (some s') => s := s'
    | .ok none => break
    | .error _ =>
      IO.println s!"ACTUAL_SCAN_ERROR form={name}"
      break
  unless seen do IO.println s!"ACTUAL_ROOT_COLON_UNREACHED form={name}"
#eval do
  for (name,input) in samples do check name input
