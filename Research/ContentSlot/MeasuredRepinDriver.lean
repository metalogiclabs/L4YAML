
-- Appended to the unchanged owner Scripts/Pins.lean for execution.
-- Only compiler-emitted data for failed, allowlisted census guards is copied.
namespace Research.MeasuredRepin
open Scripts.Pins

def specs : List (String × List (String × String)) :=
  [("CloseStackCover", [("rows", "expectedRows"), ("trees", "expectedTrees"),
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
  let sp ← defSpan masked name
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

def genericRepin (ls : Array String) (body : Array String) : IO (Array String × Nat) := do
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
    let (next, count) ← genericRepin ls body
    let changed := "\n".intercalate next.toList
    if changed != original then
      IO.FS.writeFile path changed
      edits := edits + count
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
