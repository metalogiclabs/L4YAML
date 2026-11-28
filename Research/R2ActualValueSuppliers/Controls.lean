import Research.R2MandatoryContext.Values

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open R2JointFrames R2ActualJointStep

namespace R2ActualValueSuppliers

def sources : List String := [
  "", ": b\n", "a: b\n", "&p: b\n", "!foo: b\n", "&p a: b\n",
  "a: b\nc: d\n", "a: b\n: c\n", "&p a: b\n!foo c: d\n",
  "[a, b]: c\n{d: e}: f\n", "? a\n: b\n", "? a\n? b\n: c\n",
  "? a\n: b\n? c\n: d\n", "? : a\n: b\n", "? a: b\n: c\n",
  "? - a: b\n    c: d\n  - : e\n: f\n",
  "? - ? a\n    : b\n  - c\n: d\n", "? [a, {b: c}]\n: d\n",
  "? &p !foo a\n: b\n", "? &p\n: b\n", "? |\n  a\n: b\n",
  "---\na: b\nc: d\n...\n", "\uFEFFa: b\nc: d\n",
  "- a\n? b\n: c\n", "a: b: c\n", "a:\n  - b\n  - c\nd: e\n"]

def checkValue (s t : ScannerState) : Bool := Id.run do
  if s.inFlow then return true
  let cleared := scanValueClearKey s
  if cleared.simpleKey.possible && s.currentIndent == (cleared.simpleKey.pos.col : Int) then
    let own := cleared.simpleKey.pos.col
    if t.indents != s.indents then return false
    if (levels s).head? != some (.map own) then return false
    if (RegisterWitness.markedCols t).contains own then return false
    if !(RegisterWitness.markedCols t).all (RegisterWitness.markedCols s).contains then return false
  return true

def sweep : Nat → ScannerState → Bool
  | 0, _ => true
  | fuel+1, s =>
    let here := match scanNextToken_preprocess s with
      | .ok (some (prep, ':')) =>
          let dis := dispatchState prep
          match scanValue dis with
          | .ok t => checkValue dis t
          | .error _ => true
      | _ => true
    here && match scanNextToken s with
      | .ok (some t) => sweep fuel t
      | _ => true

def countSame : Nat → ScannerState → Nat
  | 0, _ => 0
  | fuel+1, s =>
    let here := match scanNextToken_preprocess s with
      | .ok (some (prep, ':')) =>
          let dis := dispatchState prep
          match scanValue dis with
          | .ok _ => if !dis.inFlow && (scanValueClearKey dis).simpleKey.possible &&
              dis.currentIndent == ((scanValueClearKey dis).simpleKey.pos.col : Int) then 1 else 0
          | _ => 0
      | _ => 0
    here + match scanNextToken s with
      | .ok (some t) => countSame fuel t
      | _ => 0

#guard sources.all fun input => sweep 0 ((ScannerState.mk' input).emit .streamStart)
#guard sources.all fun input => sweep 1 ((ScannerState.mk' input).emit .streamStart)
#guard sources.all fun input => sweep 2 ((ScannerState.mk' input).emit .streamStart)
#guard sources.all fun input => sweep 128 ((ScannerState.mk' input).emit .streamStart)
#guard (sources.map fun input => countSame 128 ((ScannerState.mk' input).emit .streamStart)).sum > 0
#eval (sources.map fun input => countSame 128 ((ScannerState.mk' input).emit .streamStart)).sum

end R2ActualValueSuppliers
