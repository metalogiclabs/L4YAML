module

public import Lean.Data.Json
public import Tests.SuiteRunner.HtmlReport

/-!
# Test-result reports

The comparison consumes keyed per-case acceptance observations, not aggregate
counts. Version 2 retains the input and expected outcome at each (id, variant),
so saved evidence can be checked again before HTML claims agreement. Acceptance
agreement says nothing about parsed values, event output, or conformance.

`Tests/SuiteRunner/Main.lean` owns process execution and file I/O. The JUnit
reader and renderer below are the separate `--reports` rendering path.
-/

namespace Tests.SuiteRunner.Reports

@[expose] public section

open Lean

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

def backends : List String := ["lean", "c", "python", "rust"]
def presets : List String := ["unlimited", "default", "strict", "permissive", "safe_tags"]

inductive ObservationOutcome where
  | accepted | rejected | skipped | error | timeout
  deriving Repr, BEq, Inhabited

instance : ToString ObservationOutcome where
  toString
    | .accepted => "accepted"
    | .rejected => "rejected"
    | .skipped => "skipped"
    | .error => "error"
    | .timeout => "timeout"

instance : ToJson ObservationOutcome where
  toJson x := toJson (toString x)

instance : FromJson ObservationOutcome where
  fromJson? j := do
    match ← j.getStr? with
    | "accepted" => return .accepted
    | "rejected" => return .rejected
    | "skipped" => return .skipped
    | "error" => return .error
    | "timeout" => return .timeout
    | s => throw s!"unknown observation outcome: {s}"

/-- `yaml` is exactly the unescaped input supplied to tryparse. Diagnostics are
    retained for review but are not compared between language adapters. -/
structure CaseObservation where
  id : String
  variant : Nat
  yaml : String
  expectFail : Bool
  outcome : ObservationOutcome
  detail : String := ""
  deriving Repr, BEq, Inhabited, ToJson, FromJson

def CaseObservation.key (c : CaseObservation) : String := s!"{c.id}/{c.variant}"

def CaseObservation.sameInput (a b : CaseObservation) : Bool :=
  a.id == b.id && a.variant == b.variant && a.yaml == b.yaml && a.expectFail == b.expectFail

structure BackendEvidence where
  backend : String
  preset : String
  cases : Array CaseObservation
  deriving Repr, Inhabited, ToJson, FromJson

structure CrossLangEvidence where
  schemaVersion : Nat := 2
  comparison : String := "per-case-acceptance"
  runs : Array BackendEvidence
  deriving Repr, Inhabited, ToJson, FromJson

def sortedCases (cs : Array CaseObservation) : Array CaseObservation :=
  cs.insertionSort fun a b => a.id < b.id || (a.id == b.id && a.variant < b.variant)

/-- A complete observation requires at least one actual parse result. Empty,
    skipped-only, duplicate, crashed, and timed-out rosters cannot certify. -/
def validateRun (r : BackendEvidence) : Except String Unit := do
  unless backends.contains r.backend do throw s!"unknown backend {r.backend}"
  unless presets.contains r.preset do throw s!"unknown preset {r.preset}"
  let cs := sortedCases r.cases
  unless cs.any (fun c => c.outcome == .accepted || c.outcome == .rejected) do
    throw s!"{r.backend}/{r.preset}: no applicable parse observations"
  let mut previous : Option (String × Nat) := none
  for c in cs do
    if previous == some (c.id, c.variant) then throw s!"duplicate case {c.key}"
    previous := some (c.id, c.variant)
    if c.id.isEmpty then throw "empty case identifier"
    if c.outcome == .error || c.outcome == .timeout then
      throw s!"{r.backend}/{r.preset}/{c.key}: {c.outcome}: {c.detail}"

/-- Compare keyed coverage and input identity independent of array order.
    Across presets, acceptance can differ, but applicability must agree. -/
def compareCases (a b : BackendEvidence) (compareAcceptance : Bool) : Except String Unit := do
  let xs := sortedCases a.cases
  let ys := sortedCases b.cases
  unless xs.size == ys.size do
    throw s!"{b.backend}/{b.preset}: missing or extra case IDs"
  for (x, y) in xs.zip ys do
    unless x.sameInput y do throw s!"{b.backend}/{b.preset}: case identity/input mismatch at {x.key} / {y.key}"
    unless (x.outcome == .skipped) == (y.outcome == .skipped) do
      throw s!"{b.backend}/{b.preset}/{x.key}: applicability mismatch"
    if compareAcceptance && x.outcome != y.outcome then
      throw s!"{b.backend}/{b.preset}/{x.key}: acceptance mismatch ({x.outcome} / {y.outcome})"

def validatePreset (preset : String) (runs : Array BackendEvidence) : Except String Unit := do
  unless presets.contains preset do throw s!"unknown preset {preset}"
  unless runs.size == backends.length && backends.all (fun b =>
      (runs.filter (fun r => r.backend == b)).size == 1) do
    throw s!"{preset}: require exactly one run for each of lean, c, python, rust"
  for r in runs do
    unless r.preset == preset do throw s!"{r.backend}: preset mismatch ({r.preset} / {preset})"
    validateRun r
  let reference := runs[0]!
  for r in runs do compareCases reference r true

def validateCrossLang (data : CrossLangEvidence) : Except String Unit := do
  unless data.schemaVersion == 2 && data.comparison == "per-case-acceptance" do
    throw "requires version 2 per-case-acceptance evidence; aggregate counts are insufficient"
  unless data.runs.size == backends.length * presets.length do
    throw "require all four backends for all five presets"
  for preset in presets do
    validatePreset preset (data.runs.filter (fun r => r.preset == preset))
  let reference := data.runs[0]!
  for r in data.runs do compareCases reference r false

/-- Counts are display summaries only; the verdict comes from the observations. -/
def acceptanceCounts (cs : Array CaseObservation) : Nat × Nat × Nat :=
  cs.foldl (fun (a, r, s) c => match c.outcome with
    | .accepted => (a + 1, r, s)
    | .rejected => (a, r + 1, s)
    | .skipped => (a, r, s + 1)
    | _ => (a, r, s)) (0, 0, 0)

def presetLine (preset : String) (runs : Array BackendEvidence) : String × Bool :=
  match validatePreset preset runs with
  | .error e => (s!"INCOMPLETE OR MISMATCH: {e}", false)
  | .ok _ =>
    let (a, r, s) := acceptanceCounts runs[0]!.cases
    (s!"{preset}: {a} accepted, {r} rejected, {s} skipped — per-case acceptance agrees across all 4 backends", true)

def verdictLine (allMatch : Bool) : String :=
  if allMatch then "✓ Per-case acceptance agrees for all four backends and five presets (values/output not compared)"
  else "✗ Per-case acceptance comparison failed or has incomplete evidence"

def crossLangJson (data : CrossLangEvidence) : String := (toJson data).pretty

/-- Legacy counts-only files are deliberately rejected, not relabelled as a
    stronger measurement. Re-run `--compare` to produce version 2 evidence. -/
def readCrossLang (j : Json) : Except String CrossLangEvidence := do
  let version ← j.getObjValAs? Nat "schemaVersion"
  let comparison ← j.getObjValAs? String "comparison"
  unless version == 2 && comparison == "per-case-acceptance" do
    throw "requires version 2 per-case-acceptance evidence; aggregate counts are insufficient"
  let data ← fromJson? j
  validateCrossLang data
  return data

/-- Python `html.escape` (quote=True), also used by the JUnit renderer. -/
def pyEscape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;" |>.replace "'" "&#x27;"

#guard pyEscape "a<b>&'\"" == "a&lt;b&gt;&amp;&#x27;&quot;"

/-- Validation is repeated here so even a directly constructed incomplete
    value cannot cause the HTML renderer to claim agreement. -/
def crossLangHtml (data : CrossLangEvidence) : String := Id.run do
  let header := "<!DOCTYPE html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><title>Cross-language acceptance comparison</title>" ++
    "<style>body{font-family:system-ui;margin:2em}table{border-collapse:collapse}th,td{border:1px solid #ccc;padding:.5em}.match{color:#155724}.mismatch{color:#721c24}</style></head><body>" ++
    "<h1>Cross-language acceptance comparison</h1>"
  match validateCrossLang data with
  | .error e => return header ++ s!"<p class=\"mismatch\">Insufficient or inconsistent evidence: {pyEscape e}</p></body></html>"
  | .ok _ => pure ()
  let mut html := header ++ "<p>Each (test ID, variant) has the same input, expectation, applicability, and accept/reject result across Lean, C, Python, and Rust for each preset. Parsed values and emitted output are not compared. Agreement does not establish conformance to the expected result.</p>"
  html := html ++ "<table><tr><th>Preset</th><th>Backend</th><th>Accepted</th><th>Rejected</th><th>Skipped</th><th>Total</th></tr>"
  for preset in presets do
    for backend in backends do
      let some r := data.runs.find? (fun r => r.preset == preset && r.backend == backend) | continue
      let (a, d, s) := acceptanceCounts r.cases
      html := html ++ s!"<tr><td>{pyEscape preset}</td><td>{pyEscape backend}</td><td>{a}</td><td>{d}</td><td>{s}</td><td>{r.cases.size}</td></tr>"
  return html ++ s!"</table><p class=\"match\">{pyEscape (verdictLine true)}</p></body></html>"

/-! ## JUnit XML -/

/-- One `testcase`: `classname.name`, status, css class, `time`. -/
structure Case where
  name : String
  status : String
  css : String
  time : String
  deriving Repr, BEq, Inhabited

/-- Parse hexadecimal XML character references, shared by display and validation. -/
def xmlHexNat (hs : List Char) : Option Nat :=
  if hs.isEmpty || !hs.all (fun c => c.isDigit || "abcdefABCDEF".toList.contains c) then none
  else some (hs.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else (c.toLower.toNat - 'a'.toNat + 10))) 0)

/-- XML entities and character references. -/
def xmlUnescape (s : String) : String := Id.run do
  let mut out := ""
  let mut rest := s.toList
  while !rest.isEmpty do
    match rest with
    | '&' :: t =>
      let ent := t.takeWhile (· != ';')
      let after := t.drop (ent.length + 1)
      let e := String.ofList ent
      let rep : Option String :=
        if e == "amp" then some "&" else if e == "lt" then some "<" else if e == "gt" then some ">"
        else if e == "quot" then some "\"" else if e == "apos" then some "'"
        else match ent with
          | '#' :: 'x' :: hs => (xmlHexNat hs).map fun n => String.singleton (Char.ofNat n)
          | '#' :: ds => ((String.ofList ds).toNat?).map fun n => String.singleton (Char.ofNat n)
          | _ => none
      match rep with
      | some r => if t.length > ent.length then out := out ++ r; rest := after else out := out.push '&'; rest := t
      | none => out := out.push '&'; rest := t
    | c :: t => out := out.push c; rest := t
    | [] => pure ()
  return out

#guard xmlUnescape "a &lt;b&gt; &amp;&quot;&apos;&#65;&#x42; &bogus; &" == "a <b> &\"'AB &bogus; &"

/-- Recognized XML entities and scalar-valued numeric character references.
    Reject malformed references before the permissive display unescaper runs. -/
def validXmlEntities : List Char → Bool
  | [] => true
  | '&' :: t =>
    let ent := t.takeWhile (· != ';')
    let e := String.ofList ent
    let num : Option Nat :=
      if e.startsWith "#x" then xmlHexNat (ent.drop 2)
      else if e.startsWith "#" then (String.ofList (ent.drop 1)).toNat? else none
    let scalar := match num with
      | some n => n == 9 || n == 10 || n == 13 || (n ≥ 32 && n ≤ 0xD7FF) || (n ≥ 0xE000 && n ≤ 0xFFFD) || (n ≥ 0x10000 && n ≤ 0x10FFFF)
      | none => false
    t.length > ent.length && (["amp", "lt", "gt", "quot", "apos"].contains e || scalar) &&
      validXmlEntities (t.drop (ent.length + 1))
  | _ :: t => validXmlEntities t
termination_by cs => cs.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- A start tag's attributes: `name="value"` / `name='value'`, unescaped; an
    unquoted or missing value is an error, as for `xml.etree`. -/
partial def attrsOf (tag : String) : Except String (List (String × String)) :=
  go (tag.toList.dropWhile fun c => !c.isWhitespace) []
where
  go (cs : List Char) (acc : List (String × String)) : Except String (List (String × String)) :=
    let cs := cs.dropWhile Char.isWhitespace
    if cs.isEmpty then .ok acc.reverse else
    let name := cs.takeWhile fun c => c != '=' && !c.isWhitespace && c != '/' && c != '>'
    if name.isEmpty then go (cs.drop 1) acc else
    let rest := (cs.drop name.length).dropWhile Char.isWhitespace
    match rest with
    | '=' :: t =>
      if acc.any (fun kv => kv.1 == String.ofList name) then
        .error s!"duplicate attribute {String.ofList name}"
      else
      match t.dropWhile Char.isWhitespace with
      | q :: v =>
        if q == '"' || q == '\'' then
          let val := v.takeWhile (· != q)
          if val.length == v.length then .error s!"unterminated value of attribute {String.ofList name}"
          else if !validXmlEntities val || val.contains '<' then .error s!"invalid value of attribute {String.ofList name}"
          else
            let afterVal := v.drop (val.length + 1)
            if !(afterVal.headD ' ').isWhitespace && afterVal.headD ' ' != '/' && afterVal.headD ' ' != '>' then
              .error "attributes must be separated by whitespace"
            else
              go afterVal ((String.ofList name, xmlUnescape (String.ofList val)) :: acc)
        else .error s!"unquoted value of attribute {String.ofList name}"
      | [] => .error s!"attribute {String.ofList name} has no value"
    | _ => .error s!"attribute {String.ofList name} has no value"

#guard attrsOf "testcase classname=\"tests.A\" name='t &amp; u' time=\"0.01\"" ==
  .ok [("classname", "tests.A"), ("name", "t & u"), ("time", "0.01")]
#guard attrsOf "testcase name=bare" == .error "unquoted value of attribute name"
#guard attrsOf "testcase name=\"open" == .error "unterminated value of attribute name"
#guard attrsOf "testcase name" == .error "attribute name has no value"
#guard attrsOf "testcase name=\"a\"time=\"1\"" == .error "attributes must be separated by whitespace"

/-- The elements of an XML text as a flat list: `(name, attrs, isStart, isEnd)` —
    comments, declarations and CDATA skipped; `<x/>` is start and end.
    This deliberately bounded JUnit reader rejects a DOCTYPE declaration
    with an internal subset rather than attempting general DTD/entity support.
    An unterminated tag, comment, CDATA or declaration is an error. -/
partial def tokens (s : String) : Except String (List (String × List (String × String) × Bool × Bool)) :=
  go s.toList [] 0
where
  go (cs : List Char) (acc : List (String × List (String × String) × Bool × Bool)) (depth : Nat) :
      Except String (List (String × List (String × String) × Bool × Bool)) :=
    match cs with
    | [] => .ok acc.reverse
    | '<' :: '!' :: '-' :: '-' :: t => do go (← skipTo t ['-', '-', '>'] "comment") acc depth
    | '<' :: '!' :: '[' :: 'C' :: 'D' :: 'A' :: 'T' :: 'A' :: '[' :: t => do go (← skipTo t [']', ']', '>'] "CDATA section") acc depth
    | '<' :: '!' :: 'D' :: 'O' :: 'C' :: 'T' :: 'Y' :: 'P' :: 'E' :: t => do
      go (← skipDoctype t) acc depth
    | '<' :: '!' :: t | '<' :: '?' :: t => do go (← skipTo t ['>'] "declaration") acc depth
    | '<' :: '/' :: t => do
      let name := t.takeWhile fun c => c != '>' && !c.isWhitespace
      let afterName := (t.drop name.length).dropWhile Char.isWhitespace
      match afterName with
      | '>' :: rest => go rest ((String.ofList name, [], false, true) :: acc) (depth - 1)
      | _ => throw s!"invalid end tag </{String.ofList name}>"
    | '<' :: t => do
      let body := takeTag t
      if body.length == t.length then throw s!"unterminated tag <{String.ofList (body.take 20)}"
      let rest := t.drop body.length |>.drop 1
      let selfClose := body.getLast? == some '/'
      let name := body.takeWhile fun c => !c.isWhitespace && c != '/' && c != '>'
      let attrs ← attrsOf (String.ofList body)
      go rest ((String.ofList name, attrs, true, selfClose) :: acc) (depth + if selfClose then 0 else 1)
    | '&' :: t => do
      if depth == 0 then throw "text outside root element"
      let ent := t.takeWhile (· != ';')
      if t.length == ent.length || !validXmlEntities ('&' :: ent ++ [';']) then throw "invalid entity in content"
      go (t.drop (ent.length + 1)) acc depth
    | c :: t => do
      if depth == 0 && !c.isWhitespace then throw "text outside root element"
      go t acc depth
  /-- Accept only a plain DOCTYPE or bounded SYSTEM/PUBLIC external IDs.
      A quote starts an identifier only after the corresponding keyword.
      Internal DTD subsets remain explicitly unsupported. -/
  skipDoctype (cs : List Char) : Except String (List Char) := do
    let afterSpace := cs.dropWhile Char.isWhitespace
    if afterSpace.length == cs.length then throw "invalid DOCTYPE declaration"
    let name := afterSpace.takeWhile fun c =>
      !c.isWhitespace && c != '[' && c != '>' && c != '"' && c != '\''
    if name.isEmpty then throw "invalid DOCTYPE declaration"
    let afterName := afterSpace.drop name.length
    let rest := afterName.dropWhile Char.isWhitespace
    if rest.head? == some '[' then throw "DOCTYPE internal subset unsupported"
    if rest.head? == some '>' then return rest.drop 1
    if afterName.length == rest.length then throw "invalid DOCTYPE declaration"
    if ("SYSTEM".toList).isPrefixOf rest then
      let afterKeyword := rest.drop 6
      if afterKeyword.isEmpty || !(afterKeyword.headD ' ').isWhitespace then
        throw "invalid DOCTYPE declaration"
      finishDoctype (← doctypeLiteral (afterKeyword.dropWhile Char.isWhitespace))
    else if ("PUBLIC".toList).isPrefixOf rest then
      let afterKeyword := rest.drop 6
      if afterKeyword.isEmpty || !(afterKeyword.headD ' ').isWhitespace then
        throw "invalid DOCTYPE declaration"
      let afterPublicId ← doctypeLiteral (afterKeyword.dropWhile Char.isWhitespace)
      if afterPublicId.isEmpty || !(afterPublicId.headD ' ').isWhitespace then
        throw "invalid DOCTYPE declaration"
      finishDoctype (← doctypeLiteral (afterPublicId.dropWhile Char.isWhitespace))
    else throw "invalid DOCTYPE declaration"
  /-- Consume a quoted external identifier without treating delimiters as markup. -/
  doctypeLiteral (cs : List Char) : Except String (List Char) :=
    match cs with
    | '"' :: t => afterDoctypeLiteral '"' t
    | '\'' :: t => afterDoctypeLiteral '\'' t
    | _ => .error "invalid DOCTYPE declaration"
  afterDoctypeLiteral (quote : Char) (cs : List Char) : Except String (List Char) :=
    let chars := cs.takeWhile (· != quote)
    match cs.drop chars.length with
    | [] => .error "unterminated declaration"
    | _ :: t => .ok t
  finishDoctype (cs : List Char) : Except String (List Char) :=
    match cs.dropWhile Char.isWhitespace with
    | '>' :: t => .ok t
    | '[' :: _ => .error "DOCTYPE internal subset unsupported"
    | [] => .error "unterminated declaration"
    | _ => .error "invalid DOCTYPE declaration"
  skipTo (cs : List Char) (pat : List Char) (what : String) : Except String (List Char) :=
    match cs with
    | [] => .error s!"unterminated {what}"
    | _ :: t => if pat.isPrefixOf cs then .ok (cs.drop pat.length) else skipTo t pat what
  /-- the tag body up to its `>`, quotes respected -/
  takeTag (cs : List Char) : List Char :=
    let rec loop (cs : List Char) (q : Option Char) (acc : List Char) : List Char :=
      match cs with
      | [] => acc.reverse
      | c :: t =>
        match q with
        | some qc => loop t (if c == qc then none else q) (c :: acc)
        | none => if c == '>' then acc.reverse else if c == '"' || c == '\'' then loop t (some c) (c :: acc) else loop t none (c :: acc)
    loop cs none []

/-- `generate_python_ffi_html`'s reading of one JUnit file: every `testcase`
    (document order), with `failure` / `skipped` children.  The document must
    be well formed the way `xml.etree` demanded it: tags nest and match, one
    root element, closed, nothing after it — a truncated file is an error, not
    a shorter report. -/
def junitCases (xml : String) : Except String (List Case) := do
  let toks ← tokens xml
  let mut out : List Case := []
  let mut cur : Option (String × String) := none    -- (name, time) of the open testcase
  let mut failed := false
  let mut skipped := false
  let mut stack : List String := []
  let mut rootsClosed := 0
  for (name, attrs, isStart, isEnd) in toks do
    if rootsClosed > 0 then throw s!"element <{name}> after the root element closed"
    if isStart && !isEnd then stack := name :: stack
    if isEnd then
      if isStart then
        if stack.isEmpty then rootsClosed := rootsClosed + 1
      else
        match stack with
        | top :: rest =>
          if top != name then throw s!"end tag </{name}> closes <{top}>"
          stack := rest
          if rest.isEmpty then rootsClosed := rootsClosed + 1
        | [] => throw s!"end tag </{name}> with no open element"
    if name == "testcase" && isStart then
      let n := (attrs.lookup "classname").getD "" ++ "." ++ (attrs.lookup "name").getD ""
      cur := some (n, (attrs.lookup "time").getD "0")
      failed := false; skipped := false
      if isEnd then
        out := out ++ [⟨n, "PASS", "pass", (attrs.lookup "time").getD "0"⟩]; cur := none
    else if name == "failure" && isStart && cur.isSome then failed := true
    else if name == "skipped" && isStart && cur.isSome then skipped := true
    else if name == "testcase" && isEnd then
      if let some (n, t) := cur then
        let (st, css) := if failed then ("FAIL", "fail") else if skipped then ("SKIP", "skip") else ("PASS", "pass")
        out := out ++ [⟨n, st, css, t⟩]
      cur := none
  if let top :: _ := stack then throw s!"document ends inside <{top}>"
  if rootsClosed == 0 then throw "no root element"
  return out

def exampleJunit : String :=
  "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<testsuites><testsuite name=\"pytest\" tests=\"3\">\n" ++
  "<testcase classname=\"tests.A\" name=\"ok\" time=\"0.001\" />\n" ++
  "<testcase classname=\"tests.A\" name=\"bad &lt;x&gt;\" time=\"0.2\"><failure message=\"boom\">trace &amp; more</failure></testcase>\n" ++
  "<testcase classname=\"tests.B\" name=\"later\" time=\"0\"><skipped type=\"pytest.skip\" message=\"no lib\"/></testcase>\n" ++
  "<!-- <testcase name=\"commented\"/> --></testsuite></testsuites>\n"

#guard junitCases exampleJunit == .ok
  [⟨"tests.A.ok", "PASS", "pass", "0.001"⟩, ⟨"tests.A.bad <x>", "FAIL", "fail", "0.2"⟩, ⟨"tests.B.later", "SKIP", "skip", "0"⟩]

structure Section where
  title : String
  rows : List Case
  deriving Repr, Inhabited

def Section.count (s : Section) (css : String) : Nat := (s.rows.filter (·.css == css)).length

/-- `generate_python_ffi_html`'s document, and the test count it prints. -/
def pythonFfiHtml (sections : List Section) : String × Nat := Id.run do
  let mut parts : Array String := #[
    "<!DOCTYPE html>",
    "<html lang=\"en\"><head><meta charset=\"utf-8\">",
    "<title>Python API Test Results</title>",
    "<style>",
    "body{font-family:system-ui,sans-serif;margin:2em;background:#f8f9fa}",
    "h1{color:#1a1a2e} h2{color:#16213e;margin-top:2em}",
    "table{border-collapse:collapse;width:100%;margin:1em 0}",
    "th,td{border:1px solid #dee2e6;padding:6px 12px;text-align:left}",
    "th{background:#343a40;color:#fff}",
    ".pass{background:#d4edda;color:#155724}",
    ".fail{background:#f8d7da;color:#721c24}",
    ".skip{background:#fff3cd;color:#856404}",
    ".summary{font-size:1.1em;margin:0.5em 0}",
    "</style></head><body>",
    "<h1>Python API Test Results</h1>"]
  let mut gt := 0; let mut gp := 0; let mut gf := 0; let mut gs := 0
  for sec in sections do
    let total := sec.rows.length
    let p := sec.count "pass"; let f := sec.count "fail"; let s := sec.count "skip"
    gt := gt + total; gp := gp + p; gf := gf + f; gs := gs + s
    parts := parts.push s!"<h2>{pyEscape sec.title}</h2>"
    parts := parts.push s!"<p class=\"summary\">Total: {total} &mdash; <span class=\"pass\">Passed: {p}</span> &middot; <span class=\"fail\">Failed: {f}</span> &middot; <span class=\"skip\">Skipped: {s}</span></p>"
    parts := parts.push "<table><tr><th>Test</th><th>Status</th><th>Time (s)</th></tr>"
    for c in sec.rows do
      parts := parts.push s!"<tr><td>{pyEscape c.name}</td><td class=\"{c.css}\">{c.status}</td><td>{pyEscape c.time}</td></tr>"
    parts := parts.push "</table>"
  parts := parts.push "<hr>"
  let color := if gf == 0 then "pass" else "fail"
  parts := parts.push s!"<p class=\"summary {color}\">Grand Total: {gt} &mdash; Passed: {gp}, Failed: {gf}, Skipped: {gs}</p>"
  parts := parts.push "</body></html>"
  return ("\n".intercalate parts.toList, gt)

#guard junitCases "<testsuites><testsuite><testcase name=\"first\"/></testsuite>" ==
  .error "document ends inside <testsuites>"
#guard junitCases "<testsuite><testcase name=\"a\"></testsuite>" == .error "end tag </testsuite> closes <testcase>"
#guard junitCases "<testsuite/><testsuite/>" == .error "element <testsuite> after the root element closed"
#guard junitCases "<testsuite><testcase name=\"a\" time=1/></testsuite>" == .error "unquoted value of attribute time"
#guard junitCases "<testsuite><!-- open" == .error "unterminated comment"
#guard junitCases "<testsuite><testcase name=\"a\"" == .error "unterminated tag <testcase name=\"a\""
#guard junitCases "<?xml version=\"1.0\"?>\n" == .error "no root element"
#guard junitCases "</testsuite>" == .error "end tag </testsuite> with no open element"

-- Malformed JUnit documents must not become green one-test reports.  The
-- original Python ElementTree reader rejects all seven inputs.
#guard junitCases "garbage<testsuite><testcase name=\"ok\"/></testsuite>" == .error "text outside root element"
#guard junitCases "<testsuite><testcase name=\"ok\"/></testsuite>garbage" == .error "text outside root element"
#guard junitCases "<testsuite><testcase name=\"a\" name=\"b\"/></testsuite>" == .error "duplicate attribute name"
#guard junitCases "<testsuite><testcase name=\"&unknown;\"/></testsuite>" == .error "invalid value of attribute name"
#guard junitCases "<testsuite><testcase name=\"a\"/> &broken; </testsuite>" == .error "invalid entity in content"
#guard junitCases "<testsuite><testcase name=\"a\"/></testsuite garbage>" == .error "invalid end tag </testsuite>"

-- This bounded reader deliberately refuses DTD internal subsets; lock the boundary.
#guard junitCases "<!DOCTYPE testsuite [<!ELEMENT testsuite ANY>]><testsuite><testcase name=\"a\"/></testsuite>" ==
  .error "DOCTYPE internal subset unsupported"
-- Ordinary DOCTYPE declarations without an internal subset remain accepted.
#guard junitCases "<!DOCTYPE testsuite><testsuite><testcase name=\"a\"/></testsuite>" ==
  .ok [⟨".a", "PASS", "pass", "0"⟩]
-- Quoted delimiters in a system identifier are not an internal subset.
#guard junitCases "<!DOCTYPE testsuite SYSTEM \"report[1].dtd\"><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]
#guard junitCases "<!DOCTYPE testsuite SYSTEM \"report>1.dtd\"><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]
-- An actual subset is rejected even after a quoted bracket in an identifier.
#guard junitCases "<!DOCTYPE testsuite SYSTEM \"report[1].dtd\" [<!ELEMENT testsuite ANY>]><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .error "DOCTYPE internal subset unsupported"
-- A quoted span without SYSTEM or PUBLIC is malformed, even if it contains a bracket.
#guard junitCases "<!DOCTYPE testsuite \"[\"><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .error "invalid DOCTYPE declaration"
#guard junitCases "<!DOCTYPE testsuite \"report.dtd\"><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .error "invalid DOCTYPE declaration"
#guard junitCases "<!DOCTYPE testsuite SYSTEM report.dtd><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .error "invalid DOCTYPE declaration"
#guard junitCases "<!DOCTYPE testsuite SYSTEM \"report.dtd\" \"extra\"><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .error "invalid DOCTYPE declaration"
#guard junitCases "<!DOCTYPE testsuite PUBLIC \"public\" ><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .error "invalid DOCTYPE declaration"
#guard junitCases "<!DOCTYPE testsuite PUBLIC \"-//EXAMPLE//DTD JUnit//EN\" \"report[1].dtd\"><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]
#guard junitCases "<!DOCTYPE testsuite SYSTEM 'report[1].dtd'><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]
-- Rejected missing attribute separators must not create green reports.
#guard junitCases "<testsuite><testcase name=\"a\"time=\"1\"/></testsuite>" ==
  .error "attributes must be separated by whitespace"

-- Legitimate whitespace, escaping, and CDATA remain accepted.
#guard junitCases "\n<testsuite><testcase name=\"a &amp; b\"/></testsuite> \n" ==
  .ok [⟨".a & b", "PASS", "pass", "0"⟩]
#guard junitCases "<testsuite><testcase name=\"ok\"/><![CDATA[&broken;]]></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]

-- Protect valid XML syntax against stricter token/entity rejection.
#guard junitCases "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<testsuite><testcase name=\"ok\"/></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]
#guard junitCases "<testsuite><testcase name=\"&#65;&#x42;\"/></testsuite>" ==
  .ok [⟨".AB", "PASS", "pass", "0"⟩]
#guard junitCases "<testsuite><testcase name=\"ok\"/>&#65;&#x42;</testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]

-- Numeric references to non-XML characters must remain errors.
#guard junitCases "<testsuite><testcase name=\"&#xD800;\"/></testsuite>" == .error "invalid value of attribute name"

def exampleCases : List Case := (junitCases exampleJunit).toOption.getD []
#guard (pythonFfiHtml [⟨"T", exampleCases⟩]).2 == 3
#guard ((pythonFfiHtml [⟨"T", exampleCases⟩]).1.splitOn "\n").length == 25

end

end Tests.SuiteRunner.Reports
