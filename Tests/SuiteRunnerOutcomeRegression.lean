module

public import Tests.SuiteRunner.Reports
public import Tests.SuiteRunner.Protocol

@[expose] public section

/-! Regression controls for the actual suite-runner process and report consumers.
The shell fixtures model the documented tryparse exit/marker contract; they are
not alternate YAML parsers. The fake python3 merely routes its script argument to
the same shell fixture, so no Python test instrument is introduced. -/

namespace Tests.SuiteRunnerOutcomeRegression

open Tests.SuiteRunner Tests.SuiteRunner.Reports

def succeeded {α : Type} (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

def sampleA : CaseObservation :=
  { id := "AAAA", variant := 0, yaml := "A\n", expectFail := false, outcome := .accepted }

def sampleB : CaseObservation :=
  { id := "BBBB", variant := 0, yaml := "B\n", expectFail := false, outcome := .rejected }

def sampleEvidence : CrossLangEvidence :=
  { runs := (presets.flatMap fun p => backends.map fun b =>
      { backend := b, preset := p, cases := #[sampleA, sampleB] }).toArray }

def fixture (name payload : String) (negative : Bool := false) : String :=
  s!"- name: {name}\n  tags: {if negative then "error" else "scalar"}\n" ++
    (if negative then "  fail: true\n" else "") ++
    s!"  yaml: |\n    {payload}\n  tree: |\n    +STR\n    -STR\n"

def writeExe (path : System.FilePath) (body : String) : IO Unit := do
  IO.FS.createDirAll (path.parent.getD ".")
  IO.FS.writeFile path ("#!/bin/sh\n" ++ body)
  let r ← IO.Process.output {cmd := "chmod", args := #["+x", path.toString]}
  if r.exitCode != 0 then throw (IO.userError r.stderr)

def makeRoot (base : System.FilePath) (name : String) : IO System.FilePath := do
  let root := base / name
  if ← root.pathExists then IO.FS.removeDirAll root
  IO.FS.createDirAll (root / "yaml-test-suite" / "src")
  IO.FS.createDirAll (root / "reports")
  return root

def markerBackend (accept : Bool) : String :=
  if accept then "printf 'L4YAML_SUITE_ACCEPT\\n'\nexit 0\n"
  else "printf 'L4YAML_SUITE_REJECT\\n'\nexit 1\n"

def run (exe root : System.FilePath) (args : Array String) : IO IO.Process.Output := do
  let oldPath := (← IO.getEnv "PATH").getD ""
  let fixturePath := (root / "bin").toString ++ ":" ++ oldPath
  let r ← IO.Process.output {
    cmd := exe.toString
    args := args
    cwd := some root
    env := #[("PATH", some fixturePath)]
  }
  IO.FS.writeFile (root / "last-run.log") (s!"exit={r.exitCode}\n" ++ r.stdout ++ r.stderr)
  return r

def installBackends (root : System.FilePath) (opposite : Bool := false) : IO Unit := do
  let behavior (reversed : Bool) :=
    "case \"$(cat \"$1\")\" in\n" ++
    (if reversed then "*CASE_B*) " else "*CASE_A*) ") ++
    "printf 'L4YAML_SUITE_ACCEPT\\n'; exit 0 ;;\n" ++
    "*) printf 'L4YAML_SUITE_REJECT\\n'; exit 1 ;;\nesac\n"
  writeExe (root / ".lake/build/bin/tryparse") (behavior false)
  writeExe (root / "ffi/out/tryparse_c") (behavior opposite)
  writeExe (root / "rust/target/release/examples/tryparse") (behavior false)
  writeExe (root / "bin/python3") ("shift\n" ++ behavior opposite)

def main (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  let exe ← IO.FS.realPath (args.headD ".lake/build/bin/suiterunner")
  let base := cwd / "tmp/suite-outcome-regression"
  IO.FS.createDirAll base
  let failures ← IO.mkRef (#[] : Array String)
  let count ← IO.mkRef (0 : Nat)
  let recordCheck : String → Bool → IO Unit := fun label ok => do
    count.modify (· + 1)
    let status := if ok then "PASS" else "FAIL"
    IO.println s!"{status}: {label}"
    (← IO.getStdout).flush
    unless ok do failures.modify (·.push label)

  recordCheck "complete keyed evidence succeeds" (succeeded (validateCrossLang sampleEvidence))
  recordCheck "version 2 JSON round trip retains checked evidence"
    (succeeded (Lean.Json.parse (crossLangJson sampleEvidence) >>= readCrossLang))
  recordCheck "unversioned per-case file is not silently promoted"
    (!succeeded (readCrossLang (Lean.Json.mkObj [("runs", Lean.toJson sampleEvidence.runs)])))
  recordCheck "case order does not change keyed equality"
    (succeeded (validateCrossLang { sampleEvidence with runs := sampleEvidence.runs.map fun r =>
      if r.backend == "c" then { r with cases := r.cases.reverse } else r }))
  for (label, changed) in [
      ("opposite acceptance despite equal counts", #[{ sampleA with outcome := .rejected }, { sampleB with outcome := .accepted }]),
      ("missing case", #[sampleA]),
      ("duplicate case", #[sampleA, sampleA]),
      ("wrong variant", #[{ sampleA with variant := 1 }, sampleB]),
      ("changed input", #[{ sampleA with yaml := "different" }, sampleB]),
      ("changed expected result", #[{ sampleA with expectFail := true }, sampleB]),
      ("changed applicability", #[{ sampleA with outcome := .skipped }, sampleB]),
      ("backend error", #[{ sampleA with outcome := .error }, sampleB]),
      ("timeout", #[{ sampleA with outcome := .timeout }, sampleB]),
      ("all skipped", #[{ sampleA with outcome := .skipped }, { sampleB with outcome := .skipped }]),
      ("empty", #[])] do
    let altered := { sampleEvidence with runs := sampleEvidence.runs.map fun r =>
      if r.backend == "c" && r.preset == "strict" then { r with cases := changed } else r }
    recordCheck label (!succeeded (validateCrossLang altered))
    recordCheck s!"stored {label} cannot certify" (!succeeded (readCrossLang (Lean.toJson altered)))
  let noRust := { sampleEvidence with runs := sampleEvidence.runs.filter (fun r => r.backend != "rust") }
  recordCheck "missing backend rejected" (!succeeded (validateCrossLang noRust))
  let noStrict := { sampleEvidence with runs := sampleEvidence.runs.filter (fun r => r.preset != "strict") }
  recordCheck "missing preset rejected" (!succeeded (validateCrossLang noStrict))
  let duplicateBackend := { sampleEvidence with runs := sampleEvidence.runs.map fun r =>
    if r.backend == "rust" then { r with backend := "c" } else r }
  recordCheck "duplicate backend rejected" (!succeeded (validateCrossLang duplicateBackend))
  let changedPresetRoster := { sampleEvidence with runs := sampleEvidence.runs.map fun r =>
    if r.preset == "strict" then { r with cases := #[sampleA] } else r }
  recordCheck "cross-preset roster changes rejected" (!succeeded (validateCrossLang changedPresetRoster))
  recordCheck "direct HTML rendering cannot certify incomplete evidence"
    (((crossLangHtml noRust).splitOn (verdictLine true)).length == 1)

  for (code, out, expected) in [
      (0, Protocol.acceptLine, Protocol.Result.accepted),
      (1, Protocol.rejectLine, Protocol.Result.rejected),
      (1, "", Protocol.Result.error),
      (0, Protocol.rejectLine, Protocol.Result.error),
      (1, Protocol.acceptLine, Protocol.Result.error),
      (1, "diagnostic: " ++ Protocol.rejectLine, Protocol.Result.error),
      (1, Protocol.rejectLine ++ "extra\n", Protocol.Result.error),
      (1, " L4YAML_SUITE_REJECT\n", Protocol.Result.error),
      (1, "L4YAML_SUITE_REJECT", Protocol.Result.error),
      (139, Protocol.rejectLine, Protocol.Result.error),
      (124, Protocol.rejectLine, Protocol.Result.timeout)] do
    recordCheck s!"exact stdout/status protocol {code}: {repr out}"
      (Protocol.classify code out == expected)

  let tc : TestCase := { (default : TestCase) with id := "REPORT", expectFail := true }
  let expected : ReportResult := { testCase := tc, outcome := .expectedFail, errorMsg := some "deliberate rejection" }
  recordCheck "expected rejection is success even with diagnostic" (reportSucceeded #[expected] #[])
  recordCheck "expected rejection console count is success" (consoleStats #[expected] == (1, 0, 0))
  recordCheck "ordinary report acceptance succeeds" (reportSucceeded #[{ expected with outcome := .pass }] #[])
  recordCheck "empty report roster cannot pass" (!reportSucceeded #[] #[])
  recordCheck "skipped-only report roster cannot pass"
    (!reportSucceeded #[{ expected with outcome := .skip "control" }] #[])
  for outcome in [TestOutcome.fail, .unexpectedPass, .timeout, .error] do
    recordCheck s!"report fails on {repr outcome}" (!reportSucceeded #[{ expected with outcome }] #[])
  let brokenSuite : Tests.VerifiedSuiteResult := {
    name := "control", label := "control", sourceFile := "control"
    tests := #[{ category := "control", name := "must fail", outcome := .fail "control" }] }
  recordCheck "verified-suite failures propagate into report status" (!reportSucceeded #[expected] #[brokenSuite])

  -- Exercise the real Lean producer as well as the controlled failure fixtures.
  let native := cwd / ".lake/build/bin/tryparse"
  let validYaml := base / "native-valid.yaml"
  let invalidYaml := base / "native-invalid.yaml"
  IO.FS.writeFile validYaml "[a, b]\n"
  IO.FS.writeFile invalidYaml "[\n"
  for preset in presets do
    for (input, code, marker) in [(validYaml, 0, Protocol.acceptLine), (invalidYaml, 1, Protocol.rejectLine)] do
      let result ← IO.Process.output {
        cmd := native.toString
        args := #[input.toString, preset]
        env := #[("L4YAML_SUITE_PROTOCOL", some "1")] }
      recordCheck s!"real Lean protocol {preset}, exit {code}"
        (result.exitCode == code && result.stdout == marker)
  let human ← IO.Process.output {
    cmd := native.toString
    args := #[validYaml.toString]
    env := #[("L4YAML_SUITE_PROTOCOL", none)] }
  recordCheck "ordinary Lean CLI stdout remains unchanged" (human.exitCode == 0 && human.stdout.isEmpty)
  let ioFailure ← IO.Process.output {
    cmd := native.toString
    args := #[(base / "does-not-exist.yaml").toString]
    env := #[("L4YAML_SUITE_PROTOCOL", some "1")] }
  recordCheck "Lean file I/O failure cannot emit deliberate rejection"
    (ioFailure.exitCode != 0 && ioFailure.stdout.isEmpty)

  for (code, marked) in [(0, true), (1, true), (1, false), (2, false),
                          (124, false), (127, false), (139, false)] do
    let root ← makeRoot base s!"negative-{code}-{marked}"
    IO.FS.writeFile (root / "yaml-test-suite/src/NEG1.yaml") (fixture "negative control" "bad" true)
    let body := if marked then markerBackend (code == 0) else s!"exit {code}\n"
    writeExe (root / ".lake/build/bin/tryparse") body
    let r ← run exe root #["error"]
    recordCheck s!"negative exit {code}, marker={marked}" ((r.exitCode == 0) == (code == 1 && marked))

  let missing ← makeRoot base "missing"
  IO.FS.writeFile (missing / "yaml-test-suite/src/NEG1.yaml") (fixture "missing backend" "bad" true)
  recordCheck "missing backend cannot pass negative case" ((← run exe missing #["error"]).exitCode != 0)

  for (label, body) in [
      ("stderr-marker", "printf 'L4YAML_SUITE_REJECT\\n' >&2\nexit 1\n"),
      ("diagnostic-prefix", "printf 'diagnostic L4YAML_SUITE_REJECT\\n'\nexit 1\n"),
      ("contradictory-status", "printf 'L4YAML_SUITE_REJECT\\n'\nexit 0\n"),
      ("crash", "ulimit -c 0\nkill -SEGV $$\n"),
      ("real-timeout", "sleep 3\n" )] do
    let root ← makeRoot base label
    IO.FS.writeFile (root / "yaml-test-suite/src/NEG1.yaml") (fixture label "bad" true)
    writeExe (root / ".lake/build/bin/tryparse") body
    recordCheck s!"negative case rejects {label}" ((← run exe root #["error"]).exitCode != 0)

  let positive ← makeRoot base "positive"
  IO.FS.writeFile (positive / "yaml-test-suite/src/POS1.yaml") (fixture "positive" "good")
  writeExe (positive / ".lake/build/bin/tryparse") (markerBackend true)
  recordCheck "marked ordinary acceptance succeeds" ((← run exe positive #["scalar"]).exitCode == 0)
  writeExe (positive / ".lake/build/bin/tryparse") "exit 0\n"
  recordCheck "unmarked zero exit is not parser evidence" ((← run exe positive #["scalar"]).exitCode != 0)

  for opposite in [true, false] do
    let root ← makeRoot base s!"compare-{opposite}"
    IO.FS.writeFile (root / "yaml-test-suite/src/AAAA.yaml") (fixture "case A" "CASE_A")
    IO.FS.writeFile (root / "yaml-test-suite/src/BBBB.yaml") (fixture "case B" "CASE_B")
    installBackends root opposite
    IO.FS.writeFile (root / "reports/cross-lang-results.json") "stale"
    IO.FS.writeFile (root / "reports/cross-lang-comparison.html") "stale success"
    let r ← run exe root #["--compare", "reports", "--compare-timeout", "20"]
    recordCheck s!"equal totals with per-case opposite={opposite}" ((r.exitCode == 0) == !opposite)
    recordCheck s!"comparison artifact retained iff agreement ({opposite})"
      ((← (root / "reports/cross-lang-results.json").pathExists) == !opposite)
    recordCheck s!"compare invalidates old derived HTML ({opposite})"
      (!(← (root / "reports/cross-lang-comparison.html").pathExists))
    unless opposite do
      recordCheck "saved per-case evidence renders successfully" ((← run exe root #["--reports", "reports"]).exitCode == 0)
      recordCheck "successful rendering creates comparison HTML"
        (← (root / "reports/cross-lang-comparison.html").pathExists)

  for invalid in [false, true] do
    let root ← makeRoot base s!"stale-report-{invalid}"
    IO.FS.writeFile (root / "reports/cross-lang-comparison.html") "stale success"
    IO.FS.writeFile (root / "reports/python-ffi-tests.html") "stale PASS"
    if invalid then IO.FS.writeFile (root / "reports/cross-lang-results.json") "{}"
    let r ← run exe root #["--reports", "reports"]
    recordCheck s!"invalid comparison source returns error ({invalid})" ((r.exitCode != 0) == invalid)
    recordCheck s!"missing/invalid source removes stale HTML ({invalid})"
      (!(← (root / "reports/cross-lang-comparison.html").pathExists))
    recordCheck s!"missing/invalid source removes stale Python HTML ({invalid})"
      (!(← (root / "reports/python-ffi-tests.html").pathExists))

  let empty ← makeRoot base "empty-roster"
  installBackends empty
  recordCheck "empty comparison roster is not evidence"
    ((← run exe empty #["--compare", "reports", "--compare-timeout", "20"]).exitCode != 0)

  for format in ["--html", "--json"] do
    let root ← makeRoot base (if format == "--html" then "report-html" else "report-json")
    -- Verified spec-example suites read examples/ relative to cwd. Keep them
    -- green so an unrelated missing fixture cannot satisfy the failure gate.
    let linked ← IO.Process.output {
      cmd := "ln", args := #["-s", (cwd / "examples").toString, (root / "examples").toString] }
    unless linked.exitCode == 0 do throw (IO.userError linked.stderr)
    IO.FS.writeFile (root / "yaml-test-suite/src/POS1.yaml") (fixture "unexpected refusal" "good")
    writeExe (root / ".lake/build/bin/tryparse") (markerBackend true)
    recordCheck s!"{format} returns zero for ordinary success"
      ((← run exe root #[format, "reports"]).exitCode == 0)
    writeExe (root / ".lake/build/bin/tryparse") (markerBackend false)
    let r ← run exe root #[format, "reports"]
    recordCheck s!"{format} returns nonzero for failed coverage" (r.exitCode != 0)
    recordCheck s!"{format} still writes failure evidence"
      (← (root / "reports/coverage-summary.json").pathExists)
    let parsed := Lean.Json.parse (← IO.FS.readFile (root / "reports/coverage-summary.json"))
    let isolated : Except String Bool := do
      let j ← parsed
      let overall ← j.getObjVal? "overall"
      let verified ← j.getObjVal? "verified"
      let passed ← verified.getObjValAs? Nat "totalPassed"
      let total ← verified.getObjValAs? Nat "totalTests"
      let failed ← overall.getObjValAs? Nat "failed"
      let errors ← overall.getObjValAs? Nat "errors"
      return total > 0 && passed == total && failed == 1 && errors == 0
    recordCheck s!"{format} failure is isolated to the intended coverage case" (isolated == .ok true)

  let legacy := "{\"unlimited\":{\"lean\":{\"passed\":1,\"failed\":0,\"skipped\":0,\"total\":1}}}"
  recordCheck "legacy counts-only JSON cannot warrant per-case agreement"
    (match Lean.Json.parse legacy >>= Tests.SuiteRunner.Reports.readCrossLang with
     | .error _ => true
     | .ok _ => false)

  -- A new counter is absent in older reports. Exercise the actual reader so
  -- missing or malformed evidence cannot be displayed as a measured zero.
  for (label, errors, expected) in [
      ("legacy", (none : Option Lean.Json), "not recorded"),
      ("malformed", some (Lean.Json.str "unknown"), "not recorded"),
      ("zero", some (Lean.toJson (0 : Nat)), "0"),
      ("nonzero", some (Lean.toJson (3 : Nat)), "3")] do
    let fields := [("total", Lean.toJson (1 : Nat)), ("applicable", Lean.toJson (1 : Nat)),
      ("passed", Lean.toJson (1 : Nat)), ("correct", Lean.toJson (1 : Nat))]
    let fields := match errors with
      | some n => fields ++ [("errors", n)]
      | none => fields
    let input := base / s!"reader-{label}.json"
    IO.FS.writeFile input ((Lean.Json.mkObj [
      ("date", Lean.Json.str label), ("overall", Lean.Json.mkObj fields)]).compress)
    let result ← IO.Process.output {
      cmd := (cwd / ".lake/build/bin/queryresults").toString
      args := #[input.toString, "summary"] }
    recordCheck s!"queryresults preserves {label} backend-error evidence"
      (result.exitCode == 0 &&
        (result.stdout.splitOn "\n").contains s!"| Backend errors | {expected} |")

  let failed ← failures.get
  IO.println s!"Suite outcome regression: {(← count.get) - failed.size}/{← count.get} passed"
  return if failed.isEmpty then 0 else 1

end Tests.SuiteRunnerOutcomeRegression

def main := Tests.SuiteRunnerOutcomeRegression.main
