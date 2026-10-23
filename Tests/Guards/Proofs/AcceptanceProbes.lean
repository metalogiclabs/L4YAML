module

public import L4YAML.Proofs.Production.Acceptance.Quoted

public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Proofs.Production.Acceptance.Quoted
@[expose] public section Blanket

/-! Rule-2 instantiations of the quoted-scalar acceptance lemmas: the scanner's landing
    (`content`, byte offset, column) on inputs that `SCDoubleQuotedOk` / `SCSingleQuotedOk`
    derive, and the refuting inputs the unnarrowed converse would wrongly admit. -/

namespace L4YAML.Proofs.Acceptance.Probes

open L4YAML
open L4YAML.Scanner
open L4YAML.Proofs.Acceptance

def quotedAt (scan : ScannerState → Except ScanError ScannerState) (style : ScalarStyle)
    (s : String) (flow : Bool) : Option (String × Nat × Nat) :=
  match scan { ScannerState.mk' s with flowLevel := if flow then 1 else 0 } with
  | .ok s' =>
    match s'.tokens.back? with
    | some t =>
      match t.val with
      | .scalar c st => if st == style then some (c, s'.offset, s'.col) else none
      | _ => none
    | none => none
  | .error _ => none

def dq (s : String) (flow : Bool := false) := quotedAt scanDoubleQuoted .doubleQuoted s flow
def sq (s : String) (flow : Bool := false) := quotedAt scanSingleQuoted .singleQuoted s flow

-- Double-quoted, accepted (offset = bytes consumed, col = chars consumed)
#guard dq "\"abc\"" == some ("abc", 5, 5)
#guard dq "\"\"" == some ("", 2, 2)
#guard dq "\"a b\tc\"" == some ("a b\tc", 7, 7)
#guard dq "\"\\t\\n\\\\\\\"\"" == some ("\t\n\\\"", 10, 10)
#guard dq "\"\\x41\\u00e9\\U0001F600\"" == some ("Aé😀", 22, 22)
#guard dq "\"é\"" == some ("é", 4, 3)
#guard dq "\"a\"  # c" == some ("a", 3, 3)
#guard dq "\"a\": b" == some ("a", 3, 3)
#guard dq "\"a\"\nb" == some ("a", 3, 3)
#guard dq "\"a\" \t" == some ("a", 3, 3)
#guard dq "\"a\"b" true == some ("a", 3, 3)
#guard dq "\"\\ \\/\\_\\N\\L\\P\"" == some (" /\u00A0\u0085\u2028\u2029", 14, 14)
-- Double-quoted refuters of the unnarrowed converse
#guard dq "\"\x01\"" == none          -- [107] admits C0; scanner: invalidControlChar
#guard dq "\"\\uD800\"" == none        -- [60] digits only; scanner: unicodeOutOfRange
#guard dq "\"\\UFFFFFFFF\"" == none    -- [61] digits only; scanner: unicodeOutOfRange
#guard dq "\"a\"b" == none             -- block context: trailingContent

-- Single-quoted, accepted
#guard sq "'abc'" == some ("abc", 5, 5)
#guard sq "''" == some ("", 2, 2)
#guard sq "'a''b'" == some ("a'b", 6, 6)
#guard sq "'a\"b\\c'" == some ("a\"b\\c", 7, 7)
#guard sq "'é'" == some ("é", 4, 3)
#guard sq "'a' #x" == some ("a", 3, 3)
#guard sq "'a': b" == some ("a", 3, 3)
#guard sq "'a'\nb" == some ("a", 3, 3)
#guard sq "'a'b" true == some ("a", 3, 3)
#guard sq "'a b\tc'" == some ("a b\tc", 7, 7)
#guard sq "''''''" == some ("''", 6, 6)
#guard sq "'a' \t" == some ("a", 3, 3)
-- Single-quoted refuters of the unnarrowed converse
#guard sq "'\x01'" == none             -- [118] admits C0; scanner: invalidControlChar
#guard sq "'a'b" == none               -- block context: trailingContent
#guard sq "'''''" == none              -- quote-quote greed: unterminatedScalar
#guard sq "''''" == some ("'", 4, 4)   -- [120] derives `''` at offset 2; scanner lands at 4

-- The block-context trailing hypothesis
#guard TrailingOk "  # c".toList
#guard TrailingOk ": b".toList
#guard TrailingOk "\nb".toList
#guard TrailingOk " \t".toList
#guard TrailingOk "".toList
#guard !TrailingOk "b".toList
#guard !TrailingOk " x".toList

end L4YAML.Proofs.Acceptance.Probes
