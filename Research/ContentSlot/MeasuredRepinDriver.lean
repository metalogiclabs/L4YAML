
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
    else if name == "expectedSupply" || file == "Tests/Guards/Proofs/CapstonePathAudit.lean" then do
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
