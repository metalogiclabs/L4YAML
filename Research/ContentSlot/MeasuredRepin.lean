

/-!
# Scripts.Pins — `def expected… :=` pins and the build log that moves them

The port of `scripts/repin.py` (plan `Blueprint/09-scripts-in-lean.md` §3
phase 2.1).  Every guard under `Tests/Guards/Proofs/` pins what its census
counted as a literal (`String`, `Nat`, `List String`, `List Name`) and
throws `"<title>.\nexpected: {expectedFoo}\ngot:      {got}"` when the tree
moves.  This reads one `lake build` log, finds each `expected:`/`got:`
block, locates the `throwError` whose message title matches, and rewrites
the named `def expected… : T :=` to what the build reported.

One run is a FLOOR: a guard that throws on its first check never reaches
its later ones, and a failing module blocks its dependents.  Rebuild and
re-run until the log reports no moved pin.  Then read every change — a pin
is a decision, and the script only does the typing.

A pin whose literal carries comments between or after its entries is
reported `skipped` and left for a hand edit.  The `got:` line is Lean's
`toString`, so a `List String` prints as `[a, b]` without quotes: elements
are split on `, `; an element that itself contains `, ` is re-glued only
when the OLD list had an element with the same prefix, and the result is
flagged `CHECK` either way.

Hand parsers for the Python's `ERR_HEAD`, `NEXT_BLOCK`, `THROW`, `DEF`
regexes (plan §6 Q1: no regex dependency), each with its `#guard` rows.
-/

namespace Scripts.Pins

def isAsciiWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == '\x0b'

def pyStrip (s : String) : String :=
  String.ofList ((s.toList.dropWhile isAsciiWs).reverse.dropWhile isAsciiWs |>.reverse)

def pyRstrip (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile isAsciiWs |>.reverse)

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- `\S+\.lean:\d+:\d+:` at the head of `s`, path greedy: `(path, line, col, rest)`. -/
def locHead? (s : String) : Option (String × Nat × Nat × String) := Id.run do
  let cs := s.toList
  let mut best : Option (String × Nat × Nat × String) := none
  let mut pre : List Char := []
  let mut rest := cs
  while !rest.isEmpty do
    if String.ofList (rest.take 6) == ".lean:" then
      let path := String.ofList (pre.reverse ++ ".lean".toList)
      if !path.isEmpty && !path.any isAsciiWs then
        let after := rest.drop 6
        let (d1, r1) := after.span Char.isDigit
        if !d1.isEmpty then
          match r1 with
          | ':' :: r2 =>
            let (d2, r3) := r2.span Char.isDigit
            if !d2.isEmpty then
              match r3 with
              | ':' :: r4 => best := some (path, (String.ofList d1).toNat!, (String.ofList d2).toNat!, String.ofList r4)
              | _ => pure ()
          | _ => pure ()
    match rest with
    | c :: r => pre := c :: pre; rest := r
    | [] => pure ()
  return best

/-- `ERR_HEAD`: `^(?:error: )?(\S+\.lean):(\d+):(\d+):(?: error:)? ?(.*)$` on the
raw line → `(file, line, body)`. -/
def errHead? (line : String) : Option (String × Nat × String) := do
  let s := if line.startsWith "error: " then String.ofList (line.toList.drop 7) else line
  let (f, l, _, r) ← locHead? s
  let r := if r.startsWith " error:" then String.ofList (r.toList.drop 7) else r
  let r := if r.startsWith " " then String.ofList (r.toList.drop 1) else r
  return (f, l, r)

#guard errHead? "error: Tests/Guards/Proofs/FreeSurfaceCensus.lean:230:4: the census's own import closure moved."
  == some ("Tests/Guards/Proofs/FreeSurfaceCensus.lean", 230, "the census's own import closure moved.")
#guard errHead? "Tests/G.lean:230:4: error: the free surface moved." == some ("Tests/G.lean", 230, "the free surface moved.")
#guard errHead? "Tests/G.lean:230:4: warning: unused" == some ("Tests/G.lean", 230, "warning: unused")
#guard errHead? "Tests/G.lean:230:4:" == some ("Tests/G.lean", 230, "")
#guard errHead? "  Tests/G.lean:230:4: error: x" == none
#guard errHead? "✖ [10/13] Building X (443ms)" == none
#guard errHead? "expected: modulesSeen=267" == none

/-- `NEXT_BLOCK`: the start of another log record. -/
def isNextBlock (line : String) : Bool :=
  (locHead? line).isSome || line.startsWith "error: " || line.startsWith "warning: " ||
  line.startsWith "info: " || line.startsWith "✖" || line.startsWith "⚠" || line.startsWith "✔" ||
  line.startsWith "Build " || line.startsWith "trace: " ||
  (match line.toList with
   | '[' :: rest =>
     let (d1, r1) := rest.span Char.isDigit
     !d1.isEmpty && (match r1 with
       | '/' :: r2 => let (d2, r3) := r2.span Char.isDigit; !d2.isEmpty && r3.head? == some ']'
       | _ => false)
   | _ => false)

#guard isNextBlock "✔ [1341/1342] Built Tests.Guards (1.2s)"
#guard isNextBlock "[12/40] Building X"
#guard isNextBlock "Build completed successfully (1349 jobs)."
#guard isNextBlock "info: L4YAML/X.lean:1:0: 'foo' depends on axioms: [propext]"
#guard !isNextBlock "expected: modulesSeen=267"
#guard !isNextBlock "got:      modulesSeen=268"
#guard !isNextBlock ""

/-- Python `str.splitlines()` for the shapes a lake log carries: `\n`-split, a
trailing `\r` dropped, no last empty line after a final newline. -/
def pySplitLines (s : String) : Array String :=
  let parts := ((s.splitOn "\n").map fun l => if l.endsWith "\r" then String.ofList l.toList.dropLast else l).toArray
  if parts.size > 0 && parts.back! == "" then parts.pop else parts

#guard pySplitLines "a\nb\n" == #["a", "b"]
#guard pySplitLines "a\r\nb" == #["a", "b"]
#guard pySplitLines "" == #[]

/-- `read_blocks`: `(file, line, body lines)` for each `ERR_HEAD` in the log. -/
def readBlocks (log : String) : Array (String × Nat × Array String) := Id.run do
  let lines := pySplitLines log
  let mut out : Array (String × Nat × Array String) := #[]
  let mut i := 0
  while i < lines.size do
    match errHead? lines[i]! with
    | none => i := i + 1
    | some (f, l, b0) =>
      let mut body := #[b0]
      i := i + 1
      while i < lines.size && !isNextBlock lines[i]! && (errHead? lines[i]!).isNone do
        body := body.push lines[i]!
        i := i + 1
      out := out.push (f, l, body)
  return out

#guard readBlocks "✖ [1/2] Building X\nerror: T/G.lean:230:4: the surface moved.\nexpected: a\ngot:      b\n  more\n✔ [2/2] Built Y\n"
  == #[("T/G.lean", 230, #["the surface moved.", "expected: a", "got:      b", "  more"])]
#guard readBlocks "T/A.lean:1:0: error: one\nT/B.lean:2:0: error: two\n" == #[("T/A.lean", 1, #["one"]), ("T/B.lean", 2, #["two"])]

/-! ## `throwError "…"` literals -/

/-- `THROW`: every `throwError\s+"…"` literal body (escapes kept), in order. -/
def throwLiterals (src : String) : List String := Id.run do
  let cs := src.toList
  let mut out : Array String := #[]
  let mut rest := cs
  let key := "throwError".toList
  while !rest.isEmpty do
    if rest.take key.length == key then
      let after := rest.drop key.length
      let ws := after.takeWhile isAsciiWs
      let after' := after.drop ws.length
      match after' with
      | '"' :: body =>
        if !ws.isEmpty then
          -- read to the unescaped closing quote
          let mut acc : Array Char := #[]
          let mut r := body
          let mut closed := false
          while !r.isEmpty && !closed do
            match r with
            | '\\' :: d :: r' => acc := acc.push '\\' |>.push d; r := r'
            | '"' :: r' => closed := true; r := r'
            | c :: r' => acc := acc.push c; r := r'
            | [] => pure ()
          if closed then
            out := out.push (String.ofList acc.toList)
            rest := r
          else rest := after
        else rest := after
      | _ => rest := after
    else
      rest := rest.drop 1
  return out.toList

#guard throwLiterals "  throwError \"the free surface moved.\\nexpected: {expectedCensus}\\ngot:      {got}\\n\\\n      read it\"\n  throwError s!\"x\"\n  throwError \"second\""
  == ["the free surface moved.\\nexpected: {expectedCensus}\\ngot:      {got}\\n\\\n      read it", "second"]
#guard throwLiterals "throwError\"no space\"" == []
#guard throwLiterals "throwError \"a \\\"quoted\\\" word\"" == ["a \\\"quoted\\\" word"]

/-- `normalise_literal`: drop `\`⏎ and the indentation after it, then `\n` → newline, `\"` → `"`. -/
partial def normaliseLiteralGo : List Char → List Char
    | '\\' :: '\n' :: rest => normaliseLiteralGo (rest.dropWhile isAsciiWs)
    | '\\' :: 'n' :: rest => '\n' :: normaliseLiteralGo rest
    | '\\' :: '"' :: rest => '"' :: normaliseLiteralGo rest
    | c :: rest => c :: normaliseLiteralGo rest
    | [] => []

def normaliseLiteral (s : String) : String := String.ofList (normaliseLiteralGo s.toList)

#guard normaliseLiteral "a.\\nexpected: {x}\\ngot: {y}\\n\\\n      tail" == "a.\nexpected: {x}\ngot: {y}\ntail"
#guard normaliseLiteral "say \\\"hi\\\"" == "say \"hi\""

/-- `expected:\s*\{([\w.]+)\}` → the identifier. -/
def expectedName? (lit : String) : Option String := Id.run do
  let mut rest := lit.toList
  let key := "expected:".toList
  while !rest.isEmpty do
    if rest.take key.length == key then
      let after := (rest.drop key.length).dropWhile isAsciiWs
      match after with
      | '{' :: r =>
        let name := r.takeWhile fun c => isWordChar c || c == '.'
        if !name.isEmpty && (r.drop name.length).head? == some '}' then
          return some (String.ofList name)
      | _ => pure ()
    rest := rest.drop 1
  return none

#guard expectedName? "the free surface moved.\nexpected: {expectedCensus}\ngot:      {got}" == some "expectedCensus"
#guard expectedName? "x\nexpected:   {Foo.bar}\n" == some "Foo.bar"
#guard expectedName? "expected: {a b}" == none
#guard expectedName? "no pin here" == none

/-- `pin_name_for`: the `expected…` identifiers of the throw literals whose
first line (normalised, stripped) equals `title.strip()`. -/
def pinNamesFor (src title : String) : List String :=
  (throwLiterals src).filterMap fun m =>
    let lit := normaliseLiteral m
    let first := (lit.splitOn "\n").headD ""
    if pyStrip first != pyStrip title then none else expectedName? lit

#guard pinNamesFor "throwError \"the free surface moved.\\nexpected: {expectedCensus}\\ngot: {g}\"\nthrowError \"other.\\nexpected: {expectedOther}\"" "the free surface moved."
  == ["expectedCensus"]
#guard pinNamesFor "throwError \"the free surface moved.\\nexpected: {expectedCensus}\"" "nope" == []

/-! ## Rendering the new literal -/

/-- `old_list_items`: the double-quoted bodies in the old literal, else the backquoted names. -/
def oldListItems (body : String) : List String := Id.run do
  let cs := body.toList
  let mut strs : Array String := #[]
  let mut r := cs
  while !r.isEmpty do
    match r with
    | '"' :: rest =>
      let mut acc : Array Char := #[]
      let mut rr := rest
      let mut closed := false
      while !rr.isEmpty && !closed do
        match rr with
        | '\\' :: d :: rr' => acc := acc.push '\\' |>.push d; rr := rr'
        | '"' :: rr' => closed := true; rr := rr'
        | c :: rr' => acc := acc.push c; rr := rr'
        | [] => pure ()
      if closed then strs := strs.push (String.ofList acc.toList); r := rr
      else r := rest
    | _ :: rest => r := rest
    | [] => pure ()
  if !strs.isEmpty then return strs.toList
  -- `([\w.«»']+)
  let mut names : Array String := #[]
  r := cs
  while !r.isEmpty do
    match r with
    | '`' :: rest =>
      let n := rest.takeWhile fun c => isWordChar c || c == '.' || c == '«' || c == '»' || c == '\''
      if !n.isEmpty then names := names.push (String.ofList n)
      r := rest.drop n.length
    | _ :: rest => r := rest
    | [] => pure ()
  return names.toList

#guard oldListItems "[\"a, b\",\n   \"c\"]" == ["a, b", "c"]
#guard oldListItems "[`L4YAML.Output.Events, `L4YAML.Output.Json]" == ["L4YAML.Output.Events", "L4YAML.Output.Json"]
#guard oldListItems "[]" == []

/-- `split_list(inner, old_items)` → `(items, flagged)`. -/
def splitList (inner : String) (old : List String) : List String × Bool := Id.run do
  if pyStrip inner == "" then return ([], false)
  let raw := (inner.splitOn ", ").toArray
  let mut out : Array String := #[]
  let mut flagged := false
  let mut i := 0
  while i < raw.size do
    let mut glued := raw[i]!
    let mut j := i
    while !old.contains glued && j + 1 < raw.size && old.any (·.startsWith (glued ++ ", ")) do
      j := j + 1
      glued := glued ++ ", " ++ raw[j]!
      flagged := true
    if (glued.splitOn ", ").length > 1 || old.any (fun o => (o.splitOn ", ").length > 1) then
      flagged := true
    out := out.push glued
    i := j + 1
  return (out.toList, flagged)

#guard splitList "a, b, c" [] == (["a", "b", "c"], false)
#guard splitList "a, b, c" ["a, b"] == (["a, b", "c"], true)
#guard splitList "a, b" ["x, y"] == (["a", "b"], true)
#guard splitList "  " ["a"] == ([], false)

/-- `lean_str`: backslash and quote escaped. -/
def leanStr (x : String) : String :=
  String.ofList (x.toList.flatMap fun c => if c == '\\' then ['\\', '\\'] else if c == '"' then ['\\', '"'] else [c])

#guard leanStr "a\"b\\c" == "a\\\"b\\\\c"

/-- `render(ty, value, old_body)` → `(text after :=, flagged)`; `none` for a
non-list where a list is needed (Python's `ValueError`). -/
def render (ty value oldBody : String) : Option (String × Bool) :=
  if ty == "Nat" then some (" " ++ pyStrip value, false)
  else if ty == "String" then
    let v := leanStr (pyRstrip value)
    if v.length ≤ 60 then some (s!" \"{v}\"", false)
    else
      -- wrap at 76 on single spaces (Python's split(" "): empties kept)
      let words := v.splitOn " "
      let (lines, cur) := words.foldl (fun (acc : List String × String) w =>
        let (ls, cur) := acc
        if !cur.isEmpty && cur.length + 1 + w.length > 76 then (ls ++ [cur], w)
        else (ls, if cur.isEmpty then w else cur ++ " " ++ w)) ([], "")
      let all := lines ++ [cur]
      some ("\n  \"" ++ " \\\n".intercalate all ++ "\"", false)
  else
    let v := pyStrip value
    if !(v.startsWith "[" && v.endsWith "]") then none
    else
      let inner := String.ofList (v.toList.drop 1 |>.dropLast)
      let (items, flagged) := splitList inner (oldListItems oldBody)
      let items := if ty == "List String" then items.map (fun x => s!"\"{leanStr x}\"") else items.map (fun x => s!"`{x}")
      if items.isEmpty then some (" []", flagged)
      else match items with
        | [one] => if one.length < 70 then some (s!" [{one}]", flagged) else some ("\n  [" ++ ",\n   ".intercalate items ++ "]", flagged)
        | _ => some ("\n  [" ++ ",\n   ".intercalate items ++ "]", flagged)

#guard render "Nat" " 273 " "" == some (" 273", false)
#guard render "String" "modulesSeen=268" "" == some (" \"modulesSeen=268\"", false)
#guard render "List String" "[a, b]" "[\"a\", \"x\"]" == some ("\n  [\"a\",\n   \"b\"]", false)
#guard render "List String" "[a]" "" == some (" [\"a\"]", false)
#guard render "List Name" "[L4YAML.A, L4YAML.B]" "" == some ("\n  [`L4YAML.A,\n   `L4YAML.B]", false)
#guard render "List String" "[]" "" == some (" []", false)
#guard render "List String" "not a list" "" == none
#guard (render "String" (String.ofList (List.replicate 30 'a') ++ " " ++ String.ofList (List.replicate 50 'b') ++ " c") "").map (·.1)
  == some ("\n  \"" ++ String.ofList (List.replicate 30 'a') ++ " \\\n" ++ String.ofList (List.replicate 50 'b') ++ " c\"")

/-! ## The `def expected… : T :=` span -/

structure DefHead where
  head : String      -- the text up to and including `:=`
  name : String
  ty : String
  same : String      -- the rest of the line after `:=` and blanks
  deriving DecidableEq, Repr, Inhabited

/-- `DEF`: `^(?:private |protected )?def (\w+)\s*:\s*(String|Nat|List String|List Name)\s*:=[ \t]*(.*)$`. -/
def defHead? (line : String) : Option DefHead := do
  let cs := line.toList
  let (pre, r0) :=
    if line.startsWith "private def " then ("private def ".toList, cs.drop 12)
    else if line.startsWith "protected def " then ("protected def ".toList, cs.drop 14)
    else if line.startsWith "def " then ("def ".toList, cs.drop 4)
    else ([], [])
  if pre.isEmpty then none else
  let name := r0.takeWhile isWordChar
  if name.isEmpty then none else
  let r1 := (r0.drop name.length).dropWhile isAsciiWs
  match r1 with
  | ':' :: r2 =>
    let r2' := r2.dropWhile isAsciiWs
    let ty ← ["List String", "List Name", "String", "Nat"].find? fun (t : String) => (String.ofList r2').startsWith t
    let r3 := (r2'.drop ty.length).dropWhile isAsciiWs
    match r3 with
    | ':' :: '=' :: r4 =>
      let same := r4.dropWhile (fun c => c == ' ' || c == '\t')
      let headLen := cs.length - r4.length
      return { head := String.ofList (cs.take headLen), name := String.ofList name, ty, same := String.ofList same }
    | _ => none
  | _ => none

#guard defHead? "def expectedClosure : String := \"modulesSeen=268\"" ==
  some ⟨"def expectedClosure : String :=", "expectedClosure", "String", "\"modulesSeen=268\""⟩
#guard defHead? "def expectedClosure : Nat := 274  -- +1: x" == some ⟨"def expectedClosure : Nat :=", "expectedClosure", "Nat", "274  -- +1: x"⟩
#guard defHead? "def expectedFree : List String :=" == some ⟨"def expectedFree : List String :=", "expectedFree", "List String", ""⟩
#guard defHead? "private def expectedNames : List Name :=" == some ⟨"private def expectedNames : List Name :=", "expectedNames", "List Name", ""⟩
#guard defHead? "def expectedX : List Nat := [1]" == none
#guard defHead? "  def indented : Nat := 1" == none
#guard defHead? "theorem expectedX : Nat := 1" == none

structure Span where
  start : Nat           -- index of the def line
  stop : Nat            -- exclusive end of the body
  head : DefHead
  comments : Array String
  annotated : Bool
  deriving Repr, Inhabited

/-- `def_span(lines, name)`. -/
def defSpan (lines : Array String) (name : String) : Option Span := Id.run do
  for i in [0:lines.size] do
    match defHead? lines[i]! with
    | some h =>
      if h.name != name then continue
      let mut j := i + 1
      while j < lines.size &&
          (pyStrip lines[j]! == "" || (lines[j]!.toList.head?.any fun c => c == ' ' || c == '\t') ||
           (pyRstrip lines[j-1]!).endsWith "\\") do
        j := j + 1
      while j > i + 1 && pyStrip lines[j-1]! == "" do
        j := j - 1
      let mut comments : Array String := #[]
      let mut k := i + 1
      while k < j && (pyStrip lines[k]!).startsWith "--" do
        comments := comments.push lines[k]!
        k := k + 1
      let annotated := (List.range (j - (i + 1 + comments.size))).any fun d =>
        ((lines[i + 1 + comments.size + d]!).splitOn "--").length > 1
      return some { start := i, stop := j, head := h, comments, annotated }
    | none => continue
  return none

def exampleSrc : Array String := #[
  "import X",
  "",
  "def expectedFree : List String :=",
  "  [\"a\",",
  "   \"b\"]",
  "-- 265 → 266 on 2026-10-28: note",
  "",
  "def expectedClosure : String := \"modulesSeen=268\"",
  "-- 265 → 266 note",
  "",
  "def expectedN : Nat :=",
  "  -- leading comment",
  "  274",
  "",
  "def expectedAnnotated : List String :=",
  "  [\"a\", -- why",
  "   \"b\"]",
  "end"]

#guard (defSpan exampleSrc "expectedFree").map (fun s => (s.start, s.stop, s.comments.size, s.annotated)) == some (2, 5, 0, false)
#guard (defSpan exampleSrc "expectedClosure").map (fun s => (s.start, s.stop, s.comments.size, s.annotated)) == some (7, 8, 0, false)
#guard (defSpan exampleSrc "expectedN").map (fun s => (s.start, s.stop, s.comments.size, s.annotated)) == some (10, 13, 1, false)
#guard (defSpan exampleSrc "expectedAnnotated").map (fun s => (s.start, s.stop, s.comments.size, s.annotated)) == some (14, 17, 0, true)
#guard (defSpan exampleSrc "missing").isNone

/-- `^expected:\s*(.*)$` / `^got:\s*(.*)$` with re.M over the joined body. -/
def fieldAfter? (key : String) (msg : String) : Option String := Id.run do
  let lines := msg.splitOn "\n"
  -- the regex may start on any line; `\s*` may cross newlines, `.*` runs to the line end
  let text := msg.toList
  let mut rest := text
  let mut atLineStart := true
  let k := key.toList
  while !rest.isEmpty do
    if atLineStart && rest.take k.length == k then
      let after := (rest.drop k.length).dropWhile isAsciiWs
      return some (String.ofList (after.takeWhile (· != '\n')))
    match rest with
    | c :: r => atLineStart := c == '\n'; rest := r
    | [] => pure ()
  let _ := lines
  return none

#guard fieldAfter? "expected:" "title.\nexpected: modulesSeen=267\ngot:      modulesSeen=268" == some "modulesSeen=267"
#guard fieldAfter? "got:" "title.\nexpected: modulesSeen=267\ngot:      modulesSeen=268" == some "modulesSeen=268"
#guard fieldAfter? "got:" "title.\nexpected: a\n" == none
#guard fieldAfter? "expected:" "not expected: x" == none

/-- Splice the new literal into the file's lines (`new_block`), returning the
new lines.  Mirrors the Python's two shapes: with leading comments the head
stays on its own line and the literal follows them; otherwise head and
literal share the Python's `(head + new_text).split("\n")`. -/
def splice (lines : Array String) (sp : Span) (newText : String) : Array String :=
  let block : List String :=
    if !sp.comments.isEmpty then
      let lit := (String.ofList (newText.toList.dropWhile (· == '\n'))).splitOn "\n"
      let lit := if !newText.startsWith "\n" then
          -- Python: new_block[-1] = "  " + new_block[-1].strip()
          match lit.reverse with
          | last :: rest => (("  " ++ pyStrip last) :: rest).reverse
          | [] => []
        else lit
      [sp.head.head] ++ sp.comments.toList ++ lit
    else (sp.head.head ++ newText).splitOn "\n"
  (lines.extract 0 sp.start) ++ block.toArray ++ (lines.extract sp.stop lines.size)

#guard (splice exampleSrc { start := 7, stop := 9, head := (defHead? exampleSrc[7]!).get!, comments := #["-- 265 → 266 note"], annotated := false } " \"modulesSeen=269\"").extract 7 10 == #["def expectedClosure : String :=", "-- 265 → 266 note", "  \"modulesSeen=269\""]
#guard (splice exampleSrc { start := 10, stop := 13, head := (defHead? exampleSrc[10]!).get!, comments := #["  -- leading comment"], annotated := false } " 275").extract 10 13 == #["def expectedN : Nat :=", "  -- leading comment", "  275"]
#guard (splice exampleSrc { start := 2, stop := 5, head := (defHead? exampleSrc[2]!).get!, comments := #[], annotated := false } "\n  [\"a\",\n   \"c\"]").extract 2 6
  == #["def expectedFree : List String :=", "  [\"a\",", "   \"c\"]", "-- 265 → 266 on 2026-10-28: note"]

end Scripts.Pins

-- Appended to the unchanged owner Scripts/Pins.lean for execution.
-- Only compiler-emitted data for failed, allowlisted census guards is copied.
namespace Research.MeasuredRepin
open Scripts.Pins

def specs : List (String × List (String × String)) :=
  [("CloseLandingWidth", [("closes", "expectedCloses"), ("sites", "expectedSites"),
     ("spends", "expectedSpends"), ("edges", "expectedEdges"), ("empties", "expectedEmpties")]),
   ("CloseSplitFrames", [("spends", "expectedSpends"), ("decisions", "expectedDecisions"),
     ("args", "expectedArgs"), ("door", "expectedDoor")]),
   ("CloseStackCover", [("rows", "expectedRows"), ("trees", "expectedTrees"),
     ("eight", "expectedEight"), ("door", "expectedDoor")]),
   ("PaidLeafDelta", [("trees", "expectedTrees255"), ("payments", "expectedPayments"),
     ("floorlits", "expectedFloorLits"), ("transports", "expectedTransports")]),
   ("PuntCoverInputs", [("sites", "expectedSites"), ("shapes", "expectedShapes"),
     ("bounds", "expectedBounds"), ("callers", "expectedCallers"),
     ("lack", "expectedLack"), ("bottoms", "expectedBottoms"),
     ("bottomsPaid", "expectedBottomsPaid")]),
   ("ValueLinePacks", [("packs", "expectedPacks"), ("framesOn", "expectedFramesOn"),
     ("params", "expectedParams"), ("writers", "expectedWriters"),
     ("perPos", "expectedPerPos")]),
   ("ValueLineOrigins", [("positions", "expectedPositions"), ("origins", "expectedOrigins"),
     ("rows", "expectedRows"), ("perPos", "expectedPerPos"), ("unborn", "expectedUnborn")])]

def infoHead? (s : String) : Option (String × String) := do
  if !s.startsWith "info: " then none else
  let (file, _, _, body) ← locHead? (String.ofList (s.toList.drop 6))
  return (file, pyStrip body)

def infoBlocks (log : String) : Array (String × Array String) := Id.run do
  let ls := pySplitLines log
  let mut out := #[]
  let mut i := 0
  while i < ls.size do
    match infoHead? ls[i]! with
    | none => i := i + 1
    | some (file, head) =>
      let mut body := #[head]
      i := i + 1
      while i < ls.size && !isNextBlock ls[i]! do
        body := body.push ls[i]!
        i := i + 1
      out := out.push (file, body)
  return out

-- Decode only the literal escapes used by the owner pins; unknown escapes stop.
partial def decodeChars : List Char → Option (List Char)
  | [] => some []
  | '\\' :: '\\' :: xs => ('\\' :: ·) <$> decodeChars xs
  | '\\' :: '"' :: xs => ('"' :: ·) <$> decodeChars xs
  | '\\' :: 'n' :: xs => ('\n' :: ·) <$> decodeChars xs
  | '\\' :: 'r' :: xs => ('\r' :: ·) <$> decodeChars xs
  | '\\' :: 't' :: xs => ('\t' :: ·) <$> decodeChars xs
  | '\\' :: '\n' :: xs => decodeChars (xs.dropWhile isAsciiWs)
  | '\\' :: _ => none
  | x :: xs => (x :: ·) <$> decodeChars xs

def decode (s : String) : Option String := String.ofList <$> decodeChars s.toList

#guard infoHead? "info: Tests/Guards/Proofs/X.lean:1:0: writers:"
  == some ("Tests/Guards/Proofs/X.lean", "writers:")
#guard infoBlocks "info: T.lean:1:0: rows:\n  a, b\n  c\nerror: T.lean:2:0: moved\n"
  == #[("T.lean", #["rows:", "  a, b", "  c"])]
#guard decode "a\\\"b\\\\n" == some "a\"b\\n"
#guard decode "a \\\n    b" == some "a b"
#guard decode "unknown\\q" == none

def lineComment? (line : String) : Option String := Id.run do
  let cs := line.toList.toArray
  let mut quoted := false
  let mut escaped := false
  for i in [0:cs.size] do
    let c := cs[i]!
    if escaped then escaped := false
    else if quoted && c == '\\' then escaped := true
    else if c == '"' then quoted := !quoted
    else if !quoted && c == '-' && cs[i+1]? == some '-' then
      return some (String.ofList (cs.toList.drop i))
  return none

def withoutComment (line : String) : String :=
  match lineComment? line with
  | none => line
  | some c => String.ofList (line.toList.take (line.length - c.length))

def defBody (ls : Array String) (sp : Span) : String :=
  withoutComment sp.head.same ++ "\n" ++
    "\n".intercalate ((ls.extract (sp.start + 1 + sp.comments.size) sp.stop).toList.map withoutComment)

def oldValues? (ls : Array String) (sp : Span) : Option (List String) :=
  (oldListItems (defBody ls sp)).mapM decode

def sameRows (a b : List String) : Bool :=
  a.length == b.length && a.all b.contains && b.all a.contains

-- The owner parser skips only indented leading comments. Mask that indentation
-- for span discovery, then restore every original comment byte.
def measuredSpan (ls : Array String) (name : String) : Option Span := do
  let _start ← (List.range ls.size).find? fun i =>
    (defHead? ls[i]!).any (·.name == name)
  let masked := ls.map fun l => if (pyStrip l).startsWith "--" then "  " ++ l else l
  let raw ← defSpan masked name
  -- A few old lists put their final bracket at column zero.
  let sp := if (raw.head.ty == "List String" || raw.head.ty == "List Name") &&
      (ls[raw.stop]?.map pyStrip) == some "]" then {raw with stop := raw.stop + 1} else raw
  let stop := Id.run do
    let mut j := sp.stop
    while j > sp.start + 1 && ((pyStrip ls[j-1]!).isEmpty ||
        (pyStrip ls[j-1]!).startsWith "--") do j := j - 1
    return j
  return { sp with
    stop := stop,
    comments := ls.extract (sp.start + 1) (sp.start + 1 + sp.comments.size) }

def replaceMeasured (ls : Array String) (name : String) (values : List String)
    (summary : Bool) : Except String (Array String × Bool) := do
  let some sp := measuredSpan ls name | throw s!"missing literal {name}"
  let body := pyStrip (defBody ls sp)
  if summary && !(body.startsWith "\"" && body.endsWith "\"") then
    throw s!"incomplete string literal {name}"
  if !summary && !(body.startsWith "[" && body.endsWith "]") then
    throw s!"incomplete list literal {name}"
  let some old := oldValues? ls sp | throw s!"unsupported literal escape in {name}"
  if summary then
    if sp.head.ty != "String" || values.length != 1 || old.length != 1 then
      throw s!"bad summary {name}"
    if old == values then return (ls, false)
    let lead := if sp.head.same.isEmpty then "\n  " else " "
    let comments := (lineComment? sp.head.same).toList ++
      (ls.extract (sp.start + 1 + sp.comments.size) sp.stop).toList.filterMap lineComment?
    let trailing := if comments.isEmpty then "" else "  " ++ "\n  ".intercalate comments
    let text := lead ++ "\"" ++ leanStr values.head! ++ "\"" ++ trailing
    return (splice ls sp text, true)
  else
    if sp.head.ty != "List String" then throw s!"bad rows {name}"
    if sameRows old values then return (ls, false)
    let items := values.map fun s => "\"" ++ leanStr s ++ "\""
    let comments := (ls.extract (sp.start + 1 + sp.comments.size) sp.stop).toList.filterMap lineComment?
    let retained := if comments.isEmpty then "" else
      "\n" ++ "\n".intercalate (comments.map ("  " ++ ·))
    let text := if items.isEmpty then retained ++ "\n  []"
      else retained ++ "\n  [" ++ ",\n   ".intercalate items ++ "]"
    return (splice ls sp text, true)

def rowCount? (label line : String) : Option Nat := do
  let p := label ++ " ("
  if !line.startsWith p || !line.endsWith "):" then none else
  (String.ofList (line.toList.drop p.length |>.dropLast |>.dropLast)).toNat?

def countedPair? (body : Array String) : Option (List String × List String) := do
  let e ← (List.range body.size).find? fun i => (rowCount? "expected" (pyStrip body[i]!)).isSome
  let en ← rowCount? "expected" (pyStrip body[e]!)
  let g := e + en + 1
  let gn ← rowCount? "got" (pyStrip body[g]!)
  if g + gn + 1 > body.size then none else
  return ((body.extract (e+1) (e+en+1)).toList,
    (body.extract (g+1) (g+gn+1)).toList)

def scalarLine? (label line : String) : Option String := do
  let line := pyStrip line
  if !line.startsWith label then none else
  let rest := line.toList.drop label.length
  if rest.head? == some ':' then some (pyStrip (String.ofList rest.tail!))
  else if rest.head?.any isAsciiWs then
    let s := pyStrip (String.ofList rest)
    if s.startsWith "(" || s.isEmpty then none else some s
  else none

def scalarPair? (body : Array String) : Option (List String × List String) := do
  let old ← body.toList.findSome? (scalarLine? "expected")
  let fresh ← body.toList.findSome? (scalarLine? "got")
  return ([old], [fresh])

#guard countedPair? #["moved", "expected (2):", "a", "b", "got (1):", "c"] == some (["a","b"],["c"])
#guard scalarPair? #["moved", "  got      a=2", "  expected a=1"] == some (["a=1"],["a=2"])
#guard lineComment? "  \"text -- still data\", -- explanation" == some "-- explanation"

-- These three guards print lists differently. Accept only their exact titles,
-- unchanged row keys and the old literal; the compiler supplies every new value.
def printedList? (label : String) (body : Array String) : Option (List String) := do
  let i ← (List.range body.size).find? fun i => (scalarLine? label body[i]!).isSome
  let first ← scalarLine? label body[i]!
  if !first.startsWith "[" then none else do
    let j ← (List.range (body.size - i)).find? fun d => (pyStrip body[i+d]!).endsWith "]"
    let value := pyStrip (" ".intercalate
      (first :: ((body.extract (i+1) (i+j+1)).toList.map pyStrip)))
    if !value.endsWith "]" then none else
      let inner := pyStrip (String.ofList (value.toList.drop 1 |>.dropLast))
      some (if inner.isEmpty then [] else (inner.splitOn ",").map pyStrip)

#guard printedList? "expected" #["title", "expected: [a 1,", " b 2]", "got: [a 2, b 1]"]
  == some ["a 1", "b 2"]
#guard printedList? "got" #["title", "got      [a 2, b 1]", "expected [a 1, b 2]"]
  == some ["a 2", "b 1"]

def combinedCounts? (s : String) : Option (Nat × Nat) := do
  let s := pyStrip s
  if !s.startsWith "expected (" || !s.endsWith "):" then none else do
    let [a,b] := (String.ofList (s.toList.drop 10 |>.dropLast |>.dropLast)).splitOn "), got ("
      | none
    return (← a.toNat?, ← b.toNat?)

#guard combinedCounts? "expected (160), got (160):" == some (160,160)
#guard combinedCounts? "expected (2):" == none

def printedRow (s : String) : String :=
  let s := pyStrip s
  if s.startsWith "\"" && s.endsWith "\"," then
    (decode (String.ofList (s.toList.drop 1 |>.dropLast |>.dropLast))).getD s
  else s

#guard printedRow "    \"decl[10] paid\"," == "decl[10] paid"

-- Some site guards emit only their actual rows. A strict subset can be copied
-- only when one old literal matches and exactly the three retired offcol calls
-- disappear; the remaining wrapper declaration must stay on that roster.
def retiredOffcolRoster (ls body : Array String) : IO (Array String × Nat) := do
  let fresh := ((body.toList.drop 1).takeWhile fun l =>
    (pyStrip l).startsWith "L4YAML.Proofs.StreamAccum.").map pyStrip
  if fresh.isEmpty then return (ls,0)
  let mut names : List String := []
  for line in ls do
    let some h := defHead? line | continue
    if !h.name.startsWith "expected" || h.ty != "List String" then continue
    let some sp := measuredSpan ls h.name | continue
    let some old := oldValues? ls sp | continue
    let removed := old.filter fun x => !fresh.contains x
    if fresh.length + 3 == old.length && fresh.all old.contains &&
        removed.length == 3 && removed.all (fun x =>
          (x.splitOn "block_dispatch_deferred_stamp_offcol").length == 2) then
      names := names ++ [h.name]
  if names.length != 1 then return (ls,0)
  match replaceMeasured ls names.head! fresh false with
  | .error e => IO.eprintln s!"MEASURED_REPIN_SKIP {e}"; return (ls,0)
  | .ok (next, changed) =>
    if changed then IO.println s!"MEASURED_REPIN {names.head!} after exactly three retired offcol applications"
    return (next, if changed then 1 else 0)

-- RouteShapes emits the complete actual roster, without an expected/got pair.
-- Copy only the corresponding literal; for spines, every route and owner must
-- remain in the same order and only the five measured count columns may change.
def routeReading (old fresh : String) : String :=
  let leading := String.ofList (old.toList.takeWhile isAsciiWs)
  let trailing := String.ofList ((old.toList.reverse.takeWhile isAsciiWs).reverse)
  leading ++ pyStrip fresh ++ trailing

#guard routeReading "  old " "  fresh" == "  fresh "
#guard routeReading "  old " (routeReading "  old " "  fresh") == "  fresh "
#guard routeReading "  old" "  fresh " == "  fresh"

def routeSpineKey (s : String) : String :=
  " ".intercalate (((s.splitOn " ").filter (· != "")).drop 5)

#guard routeSpineKey "  stream=0 carry=12 fwd=0 punt=2 closed=0 shape ← owner"
  == routeSpineKey "  stream=0 carry=12 fwd=0 punt=1 closed=1 shape ← owner"
#guard routeSpineKey "  stream=0 carry=12 fwd=0 punt=2 closed=0 shape ← owner"
  != routeSpineKey "  stream=0 carry=12 fwd=0 punt=1 closed=1 other ← owner"

def knownListFormats (file : String) (ls body : Array String) : IO (Array String × Nat) := do
  let title := body[0]?.getD ""
  let name :=
    if file == "Tests/Guards/Proofs/DispatchPrice.lean" && title == "the per-function reading moved:" then
      some "expectedPerFn"
    else if file == "Tests/Guards/Proofs/NarrowingWorthCensus.lean" && title == "the head census moved." then
      some "expectedHeadCensus"
    else if file == "Tests/Guards/Proofs/NarrowingWorthCensus.lean" && title == "the rung-1 census moved." then
      some "expectedChainFaces"
    else if file == "Tests/Guards/Proofs/NarrowingWorthCensus.lean" && title == "the state-reachable set moved." then
      some "expectedStateFaces"
    else if file == "Tests/Guards/Proofs/OrTrueAudit.lean" && title == "the ∨-True SUPPLY classes moved." then
      some "expectedSupply"
    else if file == "Tests/Guards/Proofs/OrTrueAudit.lean" && title == "the ∨-True CONSUMER classes moved." then
      some "expectedConsumers"
    else if file == "Tests/Guards/Proofs/CapstonePathAudit.lean" && title.startsWith "the capstone-path ON roster moved (shrink-only:" then
      some "expectedOn"
    else if file == "Tests/Guards/Proofs/CapstonePathAudit.lean" && title == "the capstone-path OFF residue moved." then
      some "expectedOff"
    else if file == "Tests/Guards/Proofs/CapstonePathAudit.lean" && title == "the capstone-path FAMILIES moved." then
      some "expectedFamilies"
    else if file == "Tests/Guards/Proofs/ParkGapWidth.lean" && title == "the sites moved:" then
      some "expectedSites"
    else if file == "Tests/Guards/Proofs/ParkGapWidth.lean" && title == "the ladder moved:" then
      some "expectedLadder"
    else if file == "Tests/Guards/Proofs/RouteShapes.lean" && title == "a spine's sites moved:" then
      some "expectedSpines"
    else if file == "Tests/Guards/Proofs/RouteShapes.lean" && title == "an exit's hand-off moved:" then
      some "expectedSites"
    else if file == "Tests/Guards/Proofs/RouteShapes.lean" && title == "the spines first built from the stream moved:" then
      some "expectedK"
    else none
  let some name := name | return (ls,0)
  let some sp := measuredSpan ls name | return (ls,0)
  let some old := oldValues? ls sp | return (ls,0)
  let fresh? := if file == "Tests/Guards/Proofs/RouteShapes.lean" then
      let rows := (body.toList.drop 1).takeWhile (fun l => l.startsWith "  " && !(pyStrip l).isEmpty)
      if rows.length != old.length then none else
        some (List.zipWith routeReading old rows)
    else if file == "Tests/Guards/Proofs/ParkGapWidth.lean" then
      let rowHead := if name == "expectedSites" then "L4YAML.Proofs.StreamAccum." else "scanNextToken_"
      let rows := (body.toList.drop 1).takeWhile (fun l => (pyStrip l).startsWith rowHead)
      if rows.isEmpty then none else some (rows.map pyStrip)
    else if name == "expectedSupply" || name == "expectedConsumers" || file == "Tests/Guards/Proofs/CapstonePathAudit.lean" then do
      let i ← (List.range body.size).find? fun i => (combinedCounts? body[i]!).isSome
      let (a,b) ← combinedCounts? body[i]!
      if a != old.length || b != a || i+b+1 > body.size then none else
        some ((body.extract (i+1) (i+b+1)).toList.map printedRow)
    else do
      let before ← printedList? "expected" body
      if before != old then none else printedList? "got" body
  let some fresh := fresh? | return (ls,0)
  let keys := fun (xs : List String) => xs.map (fun x => (x.splitOn " ").headD "")
  if file == "Tests/Guards/Proofs/ParkGapWidth.lean" && name == "expectedSites" then
    let removed := old.filter fun x => !fresh.contains x
    let calls := removed.length == 3 &&
      removed.all (fun x => (x.splitOn "block_dispatch_deferred_stamp_offcol width=1").length == 2)
    let wrapper := removed.length == 1 &&
      removed.all (fun x => x.startsWith "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol <- L4YAML.Proofs.StreamAccum.block_dispatch_deferred width=UNREACHED ")
    if !(fresh.all old.contains) || !(calls || wrapper) then
      if fresh != old then return (ls,0)
  else if file == "Tests/Guards/Proofs/RouteShapes.lean" && name == "expectedSpines" then
    if fresh.length != old.length || fresh.map routeSpineKey != old.map routeSpineKey then return (ls,0)
  else if name == "expectedChainFaces" then
    if fresh.length > old.length || !(fresh.all old.contains) then return (ls,0)
  else if name == "expectedStateFaces" then
    let added := fresh.filter fun x => !old.contains x
    if !(old.all fresh.contains) ||
        !(added.all ["accum_block_on_closeThenBlock#10", "accum_block_on_pendingContent#16"].contains) then
      return (ls,0)
  else if fresh.length != old.length || keys old != keys fresh then return (ls,0)
  match replaceMeasured ls name fresh false with
  | .error e => IO.eprintln s!"MEASURED_REPIN_SKIP {e}"; return (ls,0)
  | .ok (next, changed) =>
    if changed then IO.println s!"MEASURED_REPIN {name} from exact-format compiler list"
    return (next, if changed then 1 else 0)

def genericRepin (ls : Array String) (body : Array String) : IO (Array String × Nat) := do
  -- Pretty-printed lists may span lines. The complete old literal must name
  -- one unique pin; an ambiguous comma inside an old row cannot match it.
  if let some before := printedList? "expected" body then
    if let some fresh := printedList? "got" body then
      let mut names : List String := []
      for line in ls do
        let some h := defHead? line | continue
        if !h.name.startsWith "expected" || h.ty != "List String" then continue
        let some sp := measuredSpan ls h.name | continue
        if oldValues? ls sp == some before then names := names ++ [h.name]
      if names.length == 1 then
        match replaceMeasured ls names.head! fresh false with
        | .error e => IO.eprintln s!"MEASURED_REPIN_SKIP {e}"
        | .ok (next, changed) =>
          if changed then IO.println s!"MEASURED_REPIN {names.head!} from complete compiler list"
          return (next, if changed then 1 else 0)
  let pair := (countedPair? body).map (fun (a,b) => (a,b,false)) <|>
    (scalarPair? body).map (fun (a,b) => (a,b,true))
  let some (old, fresh, summary) := pair | return (ls, 0)
  let mut matchingNames : List String := []
  for l in ls do
    let some h := defHead? l | continue
    if !h.name.startsWith "expected" || h.ty != (if summary then "String" else "List String") then continue
    let some sp := measuredSpan ls h.name | continue
    if oldValues? ls sp == some old then matchingNames := matchingNames ++ [h.name]
  if matchingNames.length != 1 then return (ls, 0)
  match replaceMeasured ls matchingNames.head! fresh summary with
  | .error e => IO.eprintln s!"MEASURED_REPIN_SKIP {e}"; return (ls, 0)
  | .ok (next, changed) =>
    if changed then IO.println s!"MEASURED_REPIN {matchingNames.head!} from unique compiler-emitted old/new values"
    return (next, if changed then 1 else 0)

def run (logPath root : String) (annotateRoot : Bool := false) : IO UInt32 := do
  let log ← IO.FS.readFile logPath
  let failures := (readBlocks log).map (·.1)
  let measured := infoBlocks log
  let mut edits := 0
  for (file, _, body) in readBlocks log do
    if !file.startsWith "Tests/Guards/Proofs/" then continue
    let path := System.FilePath.mk root / file
    let original ← IO.FS.readFile path
    let ls := (original.splitOn "\n").toArray
    let (initial, count) ← genericRepin ls body
    let mut next := initial
    let mut extra := 0
    for part in ("\n".intercalate body.toList).splitOn "\n\n" do
      let (updated, n) ← knownListFormats file next (part.splitOn "\n").toArray
      next := updated
      extra := extra + n
      let (updated, n) ← retiredOffcolRoster next (part.splitOn "\n").toArray
      next := updated
      extra := extra + n
    let changed := "\n".intercalate next.toList
    if changed != original then
      IO.FS.writeFile path changed
      edits := edits + count + extra
    -- This historical cross-check pins two readings inline rather than in defs.
    -- The exact retained diagnostic must report both reduced counts.
    if file == "Tests/Guards/Proofs/CloseSplitFrames.lean" &&
        body[0]? == some "item 251's reading moved under this pass: asked=5 both=3" then
      let current ← IO.FS.readFile path
      let old := "unless asked.size == 6 && nBoth == 4 do"
      match current.splitOn old with
      | [a,b] =>
        IO.FS.writeFile path (a ++ "unless asked.size == 5 && nBoth == 3 do" ++ b)
        edits := edits + 1
        IO.println "MEASURED_REPIN CloseSplitFrames inline asked/both 6/4 to 5/3"
      | _ => pure ()
    if file == "Tests/Guards/Proofs/CloseStackCover.lean" &&
        body[0]? == some "item 252's eight moved under this pass: eight=6" then
      let current ← IO.FS.readFile path
      let old := "unless w.eight.size == 8 do"
      match current.splitOn old with
      | [a,b] =>
        IO.FS.writeFile path (a ++ "unless w.eight.size == 6 do" ++ b)
        edits := edits + 1
        IO.println "MEASURED_REPIN CloseStackCover inline site count 8 to 6"
      | _ => pure ()
    -- This guard's expected rows are inline data, not named definitions.
    if file == "Tests/Guards/Proofs/FlipConsumerSurface.lean" &&
        body[0]? == some "DEFERRAL moved." then
      if let some (old, fresh) := countedPair? body then
        if old.length == fresh.length then
          let mut src := changed
          for (a,b) in old.zip fresh do
            if a == b then continue
            if (a.splitOn ":").headD "" != (b.splitOn ":").headD "" then continue
            let needle := "\"" ++ leanStr a ++ "\""
            match src.splitOn needle with
            | [before, after] =>
              src := before ++ "\"" ++ leanStr b ++ "\"" ++ after
              edits := edits + 1
            | _ => pure ()
          if src != changed then IO.FS.writeFile path src
  for (mod, sections) in specs do
    let file := s!"Tests/Guards/Proofs/{mod}.lean"
    if !failures.contains file then continue
    let path := System.FilePath.mk root / file
    let original ← IO.FS.readFile path
    let mut ls := (original.splitOn "\n").toArray
    for (actualFile, body) in measured do
      if actualFile != file || body.isEmpty then continue
      let head := body[0]!
      let candidate :=
        if head.startsWith (mod ++ " ") then
          some ("expectedLine", [String.ofList (head.toList.drop (mod.length + 1))], true)
        else
          (sections.find? fun s => head == s.1 ++ ":").map fun s =>
            (s.2, ((body.toList.drop 1).map pyStrip).filter (· != ""), false)
      let some (name, values, summary) := candidate | continue
      match replaceMeasured ls name values summary with
      | .error e => IO.eprintln s!"MEASURED_REPIN_SKIP {file} {e}"
      | .ok (next, changed) =>
        if changed then
          ls := next
          edits := edits + 1
          IO.println s!"MEASURED_REPIN {file} {name} from compiler output"
    let mut changed := "\n".intercalate ls.toList
    if changed != original then
      let note := "-- 2026-11-26: snapshots remeasured after the root key-slot payment from actual scanner columns."
      if annotateRoot && (changed.splitOn note).length == 1 then
        changed := changed ++ "\n" ++ note ++ "\n"
      IO.FS.writeFile path changed
  IO.println s!"MEASURED_REPIN_EDITS {edits}"
  return 0

end Research.MeasuredRepin

def main (args : List String) : IO UInt32 := do
  match args with
  | [log, root] => Research.MeasuredRepin.run log root
  | [log, root, "--root-payment"] => Research.MeasuredRepin.run log root true
  | _ => IO.eprintln "usage: measured-repin BUILD_LOG REPO_ROOT [--root-payment]"; return 2
