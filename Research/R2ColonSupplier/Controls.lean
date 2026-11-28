import Research.R2CompactSlot.Controls
import L4YAML.Parser.Composition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness

namespace R2ColonSupplierControls

def sources : List String := ["", ": x\n", "a: b\n", "? a\n: b\n", "?\n: b\n",
  "? ? a\n  : b\n: c\n", "? ? a\n  : b\n  : c\n: d\n",
  "? : x\n: y\n", "? ? ? a\n    : b\n  : c\n: d\n",
  "? ? - a\n    - b\n  : c\n: d\n", "- ? a\n  : b\n",
  "? a\n: - b\n? c\n: d\n", "k:\n  ? a\n  : b\n",
  "? &a a\n: b\n", "? a\n: &b b\n", "? a\n: |\n  b\n",
  "? a\n: >\n  b\n", "? a\n: [b,c]\n", "? a\n: {b:c}\n",
  "? a\n: b\n? c\n: d\n", "{a:b}\n", "? {a:b}\n: c\n",
  "a: b: c\n", "? a: b\n", "? a\n : b\n", "\ufeff? a\n: b\n"]

-- True is the existing stamping/implicit source, not a new scanner guard.
def implicitSource (s : ScannerState) : Bool :=
  s.explicitKeyLine.isNone || (scanValueClearKey s).simpleKey.possible ||
    decide ((s.col : Int) ≠ s.explicitKeyCol)

def rows (input : String) (budget : Nat) : Array (Bool × Nat × List Nat × List Nat) := Id.run do
  let seed := (ScannerState.mk' input).emit .streamStart
  let mut s := match seed.peek? with | some '\uFEFF' => seed.consumeBOM | _ => seed
  let mut result := #[]
  for _ in [:budget] do
    match scanNextToken s with
    | .ok (some next) =>
      if !next.inFlow && next.tokens.size > s.tokens.size &&
          next.tokens.back?.any (fun t => t.val == .value) then
        match scanNextToken_preprocess s with
        | .ok (some (prep, ':')) =>
          let dispatch := if prep.allowDirectives then
            { prep with allowDirectives := false, documentEverStarted := true } else prep
          result := result.push (implicitSource dispatch, dispatch.col, markedCols s, markedCols next)
        | _ => pure ()
      s := next
    | _ => break
  return result

def allRows := sources.flatMap fun s => [0,1,2,(s.utf8ByteSize+1)*4].map fun b => (s,b,rows s b)
def failures := allRows.filter fun (_,_,rs) => rs.any fun (implicit, own, before, _) =>
  !implicit && !(before.contains own)

#eval rows "? ? a\n  : b\n  : c\n: d\n" 200
#eval rows "? : x\n: y\n" 200
#guard allRows.length == 104
#guard failures.isEmpty
#guard (rows "? a\n: b\n" 0).isEmpty
#guard (rows "? a\n: b\n" 1).isEmpty
#guard (rows "? a\n: b\n" 2).isEmpty
#guard (rows "? ? a\n  : b\n  : c\n: d\n" 200).toList ==
  [(false,2,[0,2],[0]), (true,2,[0],[0]), (false,0,[0],[])]
#guard (rows "? : x\n: y\n" 200).toList == [(true,2,[0],[0]),(false,0,[0],[])]
#guard !(rows "\ufeff? a\n: b\n" 100).isEmpty
#guard (L4YAML.TokenParser.parseYaml "? ? a\n  : b\n  : c\n: d\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? : x\n: y\n").isOk
#eval ("COLON-OWNER-CONTROLS", allRows.length,
  allRows.foldl (fun n (_,_,rs) => n+rs.size) 0, failures)

end R2ColonSupplierControls
