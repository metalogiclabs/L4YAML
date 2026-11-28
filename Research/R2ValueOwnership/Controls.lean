import L4YAML.Proofs.Scanner.RegisterWitness

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness

namespace R2ValueOwnership

def sources : List String := [
  "", ": x\n", "a: b\n", "? a\n: b\n", "?\n: b\n",
  "? ? a\n  : - b\n: c\n", "? ? ? a\n    : b\n: d\n",
  "? ? ? ? a\n      : b\n  : d\n: e\n",
  "? ? ? ? a\n      : b\n      ? c\n      : d\n  : e\n: f\n",
  "? earth: blue\n: moon: white\n", "? earth: blue\n  : x\n: y\n",
  "? : x\n: y\n", "- ? a\n  : b\n", "k:\n  ? a\n  : b\n",
  "? &a a\n: b\n", "? a\n: &b b\n", "? a\n: |\n  b\n",
  "? a\n: >\n  b\n", "? a\n: [b, c]\n", "? a\n: {b: c}\n",
  "? a\n: b\n? c\n: d\n", "{a: b}\n", "? {a: b}\n: c\n",
  "a: b: c\n", "? a: b\n", "? a\n : b\n", "\ufeff? a\n: b\n"]

def valueRows (input : String) (budget : Nat) : Array (Bool × List Nat × Int) := Id.run do
  let mut state := (ScannerState.mk' input).emit .streamStart
  let mut rows := #[]
  for _ in [:budget] do
    match scanNextToken state with
    | .ok (some next) =>
      if next.tokens.size > state.tokens.size &&
          next.tokens.back?.any (fun t => t.val == .value) then
        rows := rows.push (next.inFlow, markedCols next, next.currentIndent)
      state := next
    | _ => break
  return rows

def budgets (s : String) : List Nat := [0, 1, 2, (s.utf8ByteSize + 1) * 4]
def allRows := sources.flatMap fun s => (budgets s).map fun b => (s, b, valueRows s b)
def failures := allRows.filter fun (_, _, rows) => rows.any fun (flow, marks, top) =>
  !flow && marks.contains top.toNat

#eval ("VALUE-OWNERSHIP-CONTROLS", allRows.length,
  allRows.foldl (fun n (_, _, rows) => n + rows.size) 0,
  failures)
#guard failures.isEmpty

end R2ValueOwnership
