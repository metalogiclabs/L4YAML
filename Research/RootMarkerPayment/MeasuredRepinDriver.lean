
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

def defBody (ls : Array String) (sp : Span) : String :=
  sp.head.same ++ "\n" ++
    "\n".intercalate (ls.extract (sp.start + 1 + sp.comments.size) sp.stop).toList

def oldValues? (ls : Array String) (sp : Span) : Option (List String) :=
  (oldListItems (defBody ls sp)).mapM decode

def sameRows (a b : List String) : Bool :=
  a.length == b.length && a.all b.contains && b.all a.contains

-- The owner parser skips only indented leading comments. Mask that indentation
-- for span discovery, then restore every original comment byte.
def measuredSpan (ls : Array String) (name : String) : Option Span := do
  let start ← (List.range ls.size).find? fun i =>
    (defHead? ls[i]!).any (·.name == name)
  let masked := Id.run do
    let mut out := ls
    let mut i := start + 1
    while i < ls.size && ((pyStrip ls[i]!).isEmpty || (pyStrip ls[i]!).startsWith "--") do
      if (pyStrip ls[i]!).startsWith "--" then out := out.set! i ("  " ++ ls[i]!)
      i := i + 1
    return out
  let sp ← defSpan masked name
  return { sp with comments := ls.extract (sp.start + 1) (sp.start + 1 + sp.comments.size) }

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
    if sp.annotated then throw s!"literal {name} has embedded comments"
    let lead := if sp.head.same.isEmpty then "\n  " else " "
    let text := lead ++ "\"" ++ leanStr values.head! ++ "\""
    return (splice ls sp text, true)
  else
    if sp.head.ty != "List String" then throw s!"bad rows {name}"
    if sameRows old values then return (ls, false)
    if sp.annotated then
      -- Preserve the annotated writer ledger byte-for-byte except the one
      -- measured root supply. Never regenerate an annotated list wholesale.
      let removed := old.filter fun s => !values.contains s
      let added := values.filter fun s => !old.contains s
      let rootWriterPrefix := "accum_block_on_noPending #1 ctor:pendingBlock.h_kslot idx="
      if name != "expectedWriters" || removed.length != 1 || added.length != 1 ||
          !removed.head!.startsWith rootWriterPrefix || !added.head!.startsWith rootWriterPrefix ||
          (removed.head!.splitOn " :=").headD "" != (added.head!.splitOn " :=").headD "" then
        throw s!"annotated {name} needs manual review"
      let src := "\n".intercalate ls.toList
      let needle := "\"" ++ leanStr removed.head! ++ "\""
      let replacement := "\"" ++ leanStr added.head! ++ "\""
      match src.splitOn needle with
      | [before, after] => return (((before ++ replacement ++ after).splitOn "\n").toArray, true)
      | _ => throw s!"ambiguous root writer literal in {name}"
    let items := values.map fun s => "\"" ++ leanStr s ++ "\""
    let text := if items.isEmpty then " []"
      else "\n  [" ++ ",\n   ".intercalate items ++ "]"
    return (splice ls sp text, true)

def run (logPath root : String) (annotateRoot : Bool := false) : IO UInt32 := do
  let log ← IO.FS.readFile logPath
  let failures := (readBlocks log).map (·.1)
  let measured := infoBlocks log
  let mut edits := 0
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
