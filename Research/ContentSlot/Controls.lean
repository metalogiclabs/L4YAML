module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public section

namespace L4YAML.Research.ContentSlot
open L4YAML.Scanner L4YAML.TokenParser L4YAML.Proofs.RegisterWitness

structure Reading where
  sources : Nat := 0
  steps : Nat := 0
  content : Nat := 0
  markedContent : Nat := 0
  multiContent : Nat := 0
  closes : Nat := 0
  markedCloses : Nat := 0
  maxMarks : Nat := 0
  explicitValues : Nat := 0
  outerValues : Nat := 0
  dedentValues : Nat := 0
  emptyCoverRejected : Nat := 0
  singletonCoverRejected : Nat := 0
  deriving Repr

def initial (input : String) : ScannerState :=
  let s := (ScannerState.mk' input).emit .streamStart
  if s.peek? == some '\uFEFF' then s.consumeBOM else s

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')
def indent (n : Nat) (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map (spaces n ++ ·))

def nest : Nat → String → String
  | 0, leaf => leaf
  | d + 1, leaf => "?\n" ++ indent 2 (nest d leaf) ++ "\n: outer"

def walk (text : String) (stats : IO.Ref Reading) : Nat → ScannerState → IO Unit
  | 0, _ => throw <| IO.userError "scanner walk exhausted its source-derived bound"
  | fuel + 1, s => do
    match scanNextToken_preprocess s with
    | .error e => throw <| IO.userError s!"preprocess failed on accepted source: {repr e}"
    | .ok none => pure ()
    | .ok (some (prep,c)) =>
      match scanNextToken s with
      | .error e => throw <| IO.userError s!"scan failed on accepted source: {repr e}"
      | .ok none => pure ()
      | .ok (some out) =>
        stats.modify fun r => {r with steps := r.steps + 1, maxMarks := max r.maxMarks (markedCols out).length}
        let dis := if prep.allowDirectives then
          {prep with allowDirectives := false, documentEverStarted := true} else prep
        if c == ':' && !dis.inFlow && dis.explicitKeyLine.isSome &&
            !(scanValueClearKey dis).simpleKey.possible && (dis.col : Int) == dis.explicitKeyCol then
          unless prep.col ∈ markedCols s do
            throw <| IO.userError "explicit value column is absent from actual pre-state marks"
          let ms := markedCols s
          unless !ms.isEmpty do
            throw <| IO.userError "empty cover accepted a live explicit value"
          stats.modify fun r => {r with
            explicitValues := r.explicitValues + 1,
            outerValues := r.outerValues + (if prep.col == 0 then 1 else 0),
            dedentValues := r.dedentValues + (if prep.col < s.col then 1 else 0),
            emptyCoverRejected := r.emptyCoverRejected + 1,
            singletonCoverRejected := r.singletonCoverRejected +
              (if ms.any (fun m => m != prep.col) then 1 else 0)}
        if !prep.inFlow then
          match scanNextToken_dispatchStructural prep c,
              scanNextToken_dispatchFlowIndicators dis c,
              scanNextToken_dispatchBlockIndicators dis c with
          | .ok none, .ok none, .ok none => do
              unless markedCols out == markedCols prep do
                throw <| IO.userError "content dispatch changed actual marked columns"
              let marks := markedCols out
              stats.modify fun r => {r with
                content := r.content + 1,
                markedContent := r.markedContent + (if marks.isEmpty then 0 else 1),
                multiContent := r.multiContent + (if marks.length > 1 then 1 else 0)}
          | _, _, _ => pure ()
        if prep.inFlow && (c == ']' || c == '}') then
          stats.modify fun r => {r with
            closes := r.closes + 1,
            markedCloses := r.markedCloses + (if (markedCols out).isEmpty then 0 else 1)}
        walk text stats fuel out

def main : IO Unit := do
  let stats ← IO.mkRef ({} : Reading)
  let leaves := ["? leaf\n: value", "? 'quoted'\n: value", "? \"quoted\"\n: value",
    "? [one, two]\n: value", "? {one: two}\n: value", "? &a leaf\n: *a",
    "? &a |\n  line\n: value", "? >\n  line\n: value", "?\n  a: b\n  c: d\n: value",
    "? ? leaf\n  : inner\n: outer", "? - one\n  - two\n: value"]
  for depth in [0,1,2,3,5,8] do
    for leaf in leaves do
      for prologue in ["", "# comment\n", "\uFEFF"] do
        for crlf in [false,true] do
          let text := prologue ++ nest depth leaf
          let text := if crlf then "\r\n".intercalate (text.splitOn "\n") else text
          unless (parseYamlSingle text).isOk do
            throw <| IO.userError s!"expected positive source rejected: {repr text}"
          stats.modify fun r => {r with sources := r.sources + 1}
          walk text stats (text.length * 4 + 32) (initial text)
  let r ← stats.get
  unless r.markedContent > 0 && r.multiContent > 0 && r.markedCloses > 0 && r.maxMarks > 2 do
    throw <| IO.userError "nonempty/multiple-mark/flow-close obligations were not reached"
  unless r.explicitValues > 0 && r.outerValues > 0 && r.dedentValues > 0 &&
      r.emptyCoverRejected > 0 && r.singletonCoverRejected > 0 do
    throw <| IO.userError "explicit-value membership/negative controls were not reached"
  IO.println s!"CONTENT_SLOT_CONTROLS {repr r} actual_initialization=true all_sources_accepted=true content_marks_preserved=true"

end L4YAML.Research.ContentSlot
def main : IO Unit := L4YAML.Research.ContentSlot.main
