module

public import L4YAML
public import Tests.SuiteRunner.Meta
public import Tests.SuiteRunner.HtmlReport
public import Tests.SuiteRunner.Reports
public import Tests.SuiteRunner.Protocol
public import Tests.VerifiedResult
public import Tests.Main
public import Tests.ExplicitKeyTests
public import Tests.FlowTests
public import Tests.ValidationTests
public import Tests.DumpRoundTrip
public import Tests.RawParseTests
public import Tests.SpecExamples
public import Tests.SchemaDump
public import Tests.ScannerTests
public import Tests.ScannerSpecExamples
public import Tests.AdversarialGrammarTests
public import Tests.AdversarialInstantiation
public import Tests.MutationSuiteTests
public import Tests.PropertyTests
public import Tests.ProductionCoverage
public import Tests.LimitTests
public import Demo

@[expose] public section Blanket

/-!
# yaml-test-suite Runner

Programmatic test runner that reads yaml-test-suite test files,
parses each test's YAML input with our parser, and reports
pass/fail results staged by feature coverage.

## Usage

```bash
# Console output (default)
.lake/build/bin/suiterunner [stage] [-v|--verbose]

# Generate HTML reports
# Both report modes write evidence, then exit nonzero on unexpected failures.
.lake/build/bin/suiterunner --html docs/

# Generate JSON summary only (faster, no HTML)
.lake/build/bin/suiterunner --json docs/

# JSON with timestamped snapshot
.lake/build/bin/suiterunner --json results/ --snapshot

# Four backends × five presets compared (lake run cross-lang-compare -- DIR);
# writes DIR/cross-lang-results.json when every backend agrees (a stale one is
# removed first), exit 1 otherwise;
# each run is killed after --compare-timeout SECS (default 600)
# agreement concerns per-case acceptance, not parsed values or output
.lake/build/bin/suiterunner --compare DIR [--compare-timeout SECS]

# cross-lang-comparison.html and python-ffi-tests.html from DIR's
# cross-lang-results.json and pytest JUnit files (lake run test-reports -- DIR)
.lake/build/bin/suiterunner --reports DIR

# -C ROOT / --root ROOT: run from another checkout (relative DIRs are under ROOT)
```

## References

- <https://github.com/yaml/yaml-test-suite>
- <https://yaml.org/spec/1.2.2/>
-/

open L4YAML
open Tests.SuiteRunner

/-! ## Debug Helpers -/

/-- Flush stdout so piped output (e.g., `| tee`) appears immediately. -/
def flushStdout : IO Unit := do (← IO.getStdout).flush

/-- Log a timestamped debug message to stderr.
    Stderr is line-buffered even when stdout is piped, so these
    always appear immediately. -/
def dbg (startMs : Nat) (msg : String) : IO Unit := do
  let now ← IO.monoMsNow
  let elapsed := now - startMs
  IO.eprintln s!"[DBG +{elapsed}ms] {msg}"
  (← IO.getStderr).flush

/-! ## Test Execution -/

/-- Parser backend for yaml-test-suite testing.
    Each backend maps to a different tryparse binary/script. -/
inductive Backend where
  | lean   -- native Lean tryparse (.lake/build/bin/tryparse)
  | c      -- C API tryparse (ffi/out/tryparse_c)
  | python -- Python API tryparse (Tests/tryparse_python.py)
  | rust   -- Rust API tryparse (rust/target/release/examples/tryparse)
  deriving Repr, BEq

instance : ToString Backend where
  toString
    | .lean => "lean"
    | .c => "c"
    | .python => "python"
    | .rust => "rust"

/-- Parse a backend name from a CLI argument. -/
def parseBackend (s : String) : Option Backend :=
  match s with
  | "lean" => some .lean
  | "c" => some .c
  | "python" => some .python
  | "rust" => some .rust
  | _ => none

/-- Return the command and argument prefix for a given backend.
    The temp file path is appended as the last argument by `runTest`. -/
def Backend.tryparseCmd (b : Backend) : String × Array String :=
  match b with
  | .lean   => (".lake/build/bin/tryparse", #[])
  | .c      => ("ffi/out/tryparse_c", #[])
  | .python => ("python3", #["Tests/tryparse_python.py"])
  | .rust   => ("rust/target/release/examples/tryparse", #[])

/-- Tests tagged `1.3-err`/`1.3-mod` whose YAML 1.2.2 behavior we handle correctly.
    These are included despite the 1.3 tag because the test's expected tree reflects
    the 1.2.2 result. See README P10.6d §2.2 — `foldBlockContent` 4-state machine. -/
def yaml13Include : List String :=
  ["6VJK", "7T8X", "MJS9", "M9B4"]

/-- Result of running a single test case. -/
inductive TestResult where
  | pass (stdout : String := "")
  | fail (reason : String) (stdout : String := "")
  | skip (reason : String)
  | error (reason : String)
  | timeout
  deriving Repr

/-- Run a single test case against our parser (pure computation). -/
def runTestCore (tc : TestCase) : TestResult :=
  let yaml := unescapeTestYaml tc.yaml
  if yaml.isEmpty then .skip "empty yaml input"
  -- Tests tagged 1.3-err or 1.3-mod are YAML 1.3 specific (unless allowlisted)
  else if tc.tags.any (fun t => t == "1.3-err" || t == "1.3-mod")
      && !yaml13Include.contains tc.id then
    .skip "YAML 1.3 specific"
  else if tc.expectFail then .skip "error test (run with 'error' stage)"
  else
    match L4YAML.TokenParser.parseYaml yaml with
    | Except.ok _docs => .pass
    | Except.error e => .fail s!"parse error: {e}"

/-- Run a single test case using OS-level process isolation.
    Writes YAML to a temp file, runs `tryparse` via `timeout(1)`,
    and requires the deliberate parse-result protocol. A nonzero exit by
    itself is never evidence of expected rejection. -/
def runTest (tc : TestCase) (timeoutSec : Nat := 2)
    (backend : Backend := .lean) (limitsPreset : Option String := none)
    : IO TestResult := do
  let yaml := unescapeTestYaml tc.yaml
  if yaml.isEmpty then return .skip "empty yaml input"
  if tc.tags.any (fun t => t == "1.3-err" || t == "1.3-mod")
      && !yaml13Include.contains tc.id then
    return .skip "YAML 1.3 specific"
  -- Write yaml to temp file (use project-local tmp/ per workspace rules)
  let tmpPath := s!"tmp/yaml_suite_test_{tc.id}_{tc.variant}.yaml"
  try
    IO.FS.createDirAll "tmp"
    IO.FS.writeFile tmpPath yaml
    let (cmd, baseArgs) := backend.tryparseCmd
    let result ← IO.Process.output {
      cmd := "timeout"
      args := #[s!"{timeoutSec}", cmd] ++ baseArgs ++ #[tmpPath]
             ++ (match limitsPreset with | some p => #[p] | none => #[])
      env := #[("L4YAML_SUITE_PROTOCOL", some "1")]
    }
    match Protocol.classify result.exitCode result.stdout with
    | .accepted =>
      return if tc.expectFail then .fail "expected parse failure but succeeded" else .pass
    | .rejected =>
      return if tc.expectFail then .pass else .fail s!"parse error: {result.stderr.trimAscii.toString}"
    | .timeout => return .timeout
    | .error =>
      return .error s!"backend error (exit {result.exitCode}, invalid or missing parse-result marker): {result.stderr.trimAscii.toString}"
  catch e =>
    return .error s!"backend launch or I/O error: {e}"
  finally
    try IO.FS.removeFile tmpPath catch _ => pure ()

/-- Summary statistics for a test run. -/
structure TestStats where
  total : Nat := 0
  passed : Nat := 0
  failed : Nat := 0
  skipped : Nat := 0
  failures : Array (String × String) := #[]  -- (testId, reason)
  deriving Repr

instance : ToString TestStats where
  toString s :=
    s!"{s.passed} passed, {s.failed} failed, {s.skipped} skipped ({s.total} total)"

/-! ## File System Operations -/

/-- Read all `.yaml` files from the test suite `src/` directory. -/
def readTestFiles (suiteDir : String) : IO (Array (String × String)) := do
  let srcDir := suiteDir ++ "/src"
  let entries ← System.FilePath.readDir srcDir
  let mut files : Array (String × String) := #[]
  for entry in entries do
    let path := entry.path
    if path.extension == some "yaml" then
      let content ← IO.FS.readFile path
      -- Extract test ID from filename (e.g., "229Q" from "229Q.yaml")
      let testId := path.fileStem.getD "unknown"
      files := files.push (testId, content)
  return files.insertionSort (fun a b => a.1 < b.1)

/-! ## Main Runner -/

/-- Run all tests in a given stage and print results. -/
def runStage (stage : Stage) (testCases : Array TestCase)
    (verbose : Bool := false) (backend : Backend := .lean)
    (limitsPreset : Option String := none) : IO TestStats := do
  let filtered := testCases.filter (·.inStage stage)
  IO.println s!"Running {filtered.size} tests for stage: {stage}"
  IO.println (String.ofList (List.replicate 60 '-'))
  let mut stats : TestStats := {}
  let mut idx : Nat := 0
  for tc in filtered do
    idx := idx + 1
    stats := { stats with total := stats.total + 1 }
    -- Show progress for every test so user can see we're not stuck
    IO.print s!"  [{idx}/{filtered.size}] {tc.id} "
    flushStdout
    let result ← runTest tc (backend := backend) (limitsPreset := limitsPreset)
    match result with
    | .pass .. =>
      stats := { stats with passed := stats.passed + 1 }
      IO.println "✓"
    | .fail reason .. =>
      let failures := stats.failures.push (tc.id, reason)
      stats := { stats with failed := stats.failed + 1 }
      stats := { stats with failures := failures }
      IO.println s!"✗ {reason}"
    | .skip reason =>
      stats := { stats with skipped := stats.skipped + 1 }
      IO.println s!"○ {reason}"
    | .error reason =>
      stats := { stats with
        failed := stats.failed + 1
        failures := stats.failures.push (tc.id, reason) }
      IO.println s!"✗ {reason}"
    | .timeout =>
      stats := { stats with
        failed := stats.failed + 1
        failures := stats.failures.push (tc.id, "timeout") }
      IO.println "✗ timeout"
  IO.println (String.ofList (List.replicate 60 '-'))
  IO.println s!"  {stats}"
  if stats.failures.size > 0 && !verbose then
    IO.println s!"\n  Failed tests:"
    for pair in stats.failures do
      IO.println s!"    {pair.1}: {pair.2}"
  IO.println ""
  return stats

/-- Parse command-line stage argument. -/
def parseStageArg (arg : String) : Stage :=
  match arg with
  | "scalar" => .scalar
  | "flow" => .flow
  | "block" => .block
  | "document" => .document
  | "advanced" => .advanced
  | "error" => .error
  | _ => .all

/-- Run all test cases and collect ReportResults for HTML generation. -/
def runAllForReport (testCases : Array TestCase) (stage : Stage)
    (timeoutSec : Nat := 2) (startMs : Nat := 0)
    (backend : Backend := .lean)
    (limitsPreset : Option String := none) : IO (Array ReportResult) := do
  let filtered := if stage == .all then testCases
                  else testCases.filter (fun tc =>
                    tc.stage == stage || (stage != .error && tc.inStage stage))
  dbg startMs s!"runAllForReport: {filtered.size} tests to run"
  let mut results : Array ReportResult := #[]
  let mut idx : Nat := 0
  for tc in filtered do
    idx := idx + 1
    IO.print s!"  [{idx}/{filtered.size}] {tc.id} "
    flushStdout
    let result ← runTest tc timeoutSec backend limitsPreset
    let reportResult : ReportResult := match result with
      | .pass stdout =>
        let po := if stdout.isEmpty then none else some stdout
        if tc.expectFail then
          { testCase := tc, outcome := .expectedFail, parserOutput := po }
        else
          { testCase := tc, outcome := .pass, parserOutput := po }
      | .fail reason stdout =>
        let po := if stdout.isEmpty then none else some stdout
        if tc.expectFail then
          { testCase := tc, outcome := .unexpectedPass, errorMsg := some reason,
            parserOutput := po }
        else
          { testCase := tc, outcome := .fail, errorMsg := some reason,
            parserOutput := po }
      | .skip reason =>
        { testCase := tc, outcome := .skip reason }
      | .error reason =>
        { testCase := tc, outcome := .error, errorMsg := some reason }
      | .timeout =>
        { testCase := tc, outcome := .timeout, errorMsg := some "timeout" }
    -- Console output
    match reportResult.outcome with
    | .pass => IO.println "✓"
    | .fail => IO.println s!"✗ {reportResult.errorMsg.getD ""}"
    | .expectedFail => IO.println "✓ (expected fail)"
    | .unexpectedPass => IO.println s!"⚠ unexpected pass"
    | .skip reason => IO.println s!"○ {reason}"
    | .timeout => IO.println s!"⏱ timeout"
    | .error => IO.println s!"✗ {reportResult.errorMsg.getD "backend error"}"
    flushStdout
    -- Periodic stderr progress (every 25 tests)
    if idx % 25 == 0 then
      dbg startMs s!"runAllForReport: completed {idx}/{filtered.size}"
    results := results.push reportResult
  dbg startMs s!"runAllForReport: finished all {filtered.size} tests"
  return results

/-- Preserve the actual accept/reject observation separately from whether the
    suite expected it. This is the comparison's evidence, including variants. -/
def observationOfReport (r : ReportResult) : Reports.CaseObservation :=
  { id := r.testCase.id
    variant := r.testCase.variant
    yaml := unescapeTestYaml r.testCase.yaml
    expectFail := r.testCase.expectFail
    outcome := match r.outcome with
      | .pass | .unexpectedPass => .accepted
      | .fail | .expectedFail => .rejected
      | .skip _ => .skipped
      | .timeout => .timeout
      | .error => .error
    detail := match r.outcome with
      | .skip reason => reason
      | _ => r.errorMsg.getD "" }

/-- Python's `pathlib.Path(dir) / name` as a printed path: a leading `./` and
    trailing slashes dropped. -/
def pyJoin (dir name : String) : String :=
  let d := String.ofList (((if dir.startsWith "./" then (dir.drop 2).toString else dir).toList.reverse.dropWhile (· == '/')).reverse)
  if d.isEmpty then name else d ++ "/" ++ name

def underRoot (root : System.FilePath) (dir : String) : System.FilePath :=
  if (System.FilePath.mk dir).isAbsolute then dir else root / dir

/-- Run a process with piped stdout/stderr and a deadline; `none` when it was
    killed at the deadline (the Python's `subprocess.run(timeout=600)`). -/
def outputWithin (limitMs : Nat) (cfg : IO.Process.SpawnArgs) : IO (Option IO.Process.Output) := do
  let child ← IO.Process.spawn { cfg with stdout := .piped, stderr := .piped, stdin := .null }
  let outT ← IO.asTask child.stdout.readToEnd
  let errT ← IO.asTask child.stderr.readToEnd
  let start ← IO.monoMsNow
  repeat
    if let some exitCode ← child.tryWait then
      return some { exitCode, stdout := ← IO.ofExcept outT.get, stderr := ← IO.ofExcept errT.get }
    if (← IO.monoMsNow) - start > limitMs then
      child.kill
      discard child.wait
      return none
    IO.sleep 200
  return none

/-- `--compare DIR`: measure each unique case once for each backend/preset.
    Compare keyed acceptance observations, retain individual run evidence, and
    publish the combined JSON only after complete agreement. A restrictive
    preset's deliberate rejection is a measurement, not an apparatus failure. -/
def runCompare (root : System.FilePath) (dir : String) (timeoutS : Nat) : IO UInt32 := do
  let exe ← IO.appPath
  let root ← IO.FS.realPath root
  let json := underRoot root dir / "cross-lang-results.json"
  IO.FS.createDirAll (underRoot root dir)
  if ← json.pathExists then IO.FS.removeFile json
  let html := underRoot root dir / "cross-lang-comparison.html"
  if ← html.pathExists then IO.FS.removeFile html
  let mut results : Array Reports.BackendEvidence := #[]
  let mut allMatch := true
  for preset in Reports.presets do
    let mut row : Array Reports.BackendEvidence := #[]
    for b in Reports.backends do
      let observations := underRoot root dir / s!"observations-{b}-{preset}.json"
      if ← observations.pathExists then IO.FS.removeFile observations
      try
        let r ← outputWithin (timeoutS * 1000)
          { cmd := exe.toString,
            args := #["--observations", observations.toString, "--backend", b, "--limits", preset],
            cwd := some root }
        match r with
        | none =>
          IO.eprintln s!"ERROR: {b}/{preset} killed after {timeoutS}s"
          allMatch := false
        | some process =>
          if process.exitCode != 0 then
            IO.eprintln s!"ERROR: {b}/{preset} observation run exited {process.exitCode}: {process.stderr.trimAscii}"
            allMatch := false
          else
            let parsed : Except String Reports.BackendEvidence :=
              Lean.Json.parse (← IO.FS.readFile observations) >>= Lean.fromJson?
            match parsed with
            | .error e =>
              IO.eprintln s!"ERROR: {b}/{preset}: {e}"
              allMatch := false
            | .ok evidence =>
              if evidence.backend != b || evidence.preset != preset then
                IO.eprintln s!"ERROR: {b}/{preset}: wrong backend/preset identity"
                allMatch := false
              else row := row.push evidence
      catch e =>
        IO.eprintln s!"ERROR: {b}/{preset} launch or evidence I/O failed: {e}"
        allMatch := false
    let (line, same) := Reports.presetLine preset row
    IO.println line
    if !same then allMatch := false
    results := results ++ row
  let evidence : Reports.CrossLangEvidence := { runs := results }
  match Reports.validateCrossLang evidence with
  | .error e => IO.eprintln s!"ERROR: {e}"; allMatch := false
  | .ok _ => pure ()
  IO.println ""
  IO.println (Reports.verdictLine allMatch)
  if !allMatch then return 1
  IO.FS.writeFile json (Reports.crossLangJson evidence)
  return 0

/-- `--reports DIR` (was `scripts/generate-test-reports.py`):
    `cross-lang-comparison.html` from `cross-lang-results.json` and
    `python-ffi-tests.html` from the two pytest JUnit files, each skipped with
    a message when its input is absent. -/
def runReports (root : System.FilePath) (dir : String) : IO UInt32 := do
  let d := underRoot root dir
  let jf := d / "cross-lang-results.json"
  -- A missing or invalid source must not leave an older success page visible.
  let hf := d / "cross-lang-comparison.html"
  if ← hf.pathExists then IO.FS.removeFile hf
  let pf := d / "python-ffi-tests.html"
  if ← pf.pathExists then IO.FS.removeFile pf
  if ← jf.pathExists then
    match Lean.Json.parse (← IO.FS.readFile jf) >>= Reports.readCrossLang with
    | .error e => IO.eprintln s!"cross-lang-results.json: {e}"; return 1
    | .ok data =>
      IO.FS.writeFile hf (Reports.crossLangHtml data)
      IO.println s!"Generated {pyJoin dir "cross-lang-comparison.html"}"
  else
    IO.println "No cross-lang-results.json found, skipping"
  let mut sections : List Reports.Section := []
  for (file, title) in [("python-ffi-junit.xml", "Python FFI Integration Tests (Tests/)"),
                        ("python-package-junit.xml", "Python Package Tests (python/tests/)")] do
    if ← (d / file).pathExists then
      match Reports.junitCases (← IO.FS.readFile (d / file)) with
      | .error e => IO.eprintln s!"{pyJoin dir file}: {e}"; return 1
      | .ok cases => sections := sections ++ [⟨title, cases⟩]
  if sections.isEmpty then
    IO.println "No JUnit XML files found, skipping Python FFI HTML report"
    return 0
  let (html, n) := Reports.pythonFfiHtml sections
  IO.FS.writeFile pf html
  IO.println s!"Generated {pyJoin dir "python-ffi-tests.html"} ({n} tests)"
  return 0

def main (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  unless args.contains "--compare" || args.contains "--reports" do
    dbg t0 "suiterunner starting"

  -- Parse arguments
  let mut stageArg := "all"
  let mut verbose := false
  let mut htmlDir : Option String := none
  let mut jsonDir : Option String := none
  let mut snapshot := false
  let mut backend : Backend := .lean
  let mut limitsPreset : Option String := none
  let mut compareDir : Option String := none
  let mut reportsDir : Option String := none
  let mut observationsFile : Option String := none
  let mut root : System.FilePath := "."
  let mut compareTimeout : Nat := 600
  let mut i : Nat := 0
  let mut skipNext := false
  for arg in args do
    if skipNext then
      skipNext := false
    else if arg == "-v" || arg == "--verbose" then
      verbose := true
    else if arg == "--html" then
      match args.drop (i + 1) with
      | dir :: _ => htmlDir := some dir; skipNext := true
      | [] => IO.eprintln "Error: --html requires a directory argument"; return 1
    else if arg == "--json" then
      match args.drop (i + 1) with
      | dir :: _ => jsonDir := some dir; skipNext := true
      | [] => IO.eprintln "Error: --json requires a directory argument"; return 1
    else if arg == "--snapshot" then
      snapshot := true
    else if arg == "--observations" then
      match args.drop (i + 1) with
      | file :: _ => observationsFile := some file; skipNext := true
      | [] => IO.eprintln "Error: --observations requires a file argument"; return 1
    else if arg == "--backend" then
      match args.drop (i + 1) with
      | name :: _ =>
        match parseBackend name with
        | some b => backend := b; skipNext := true
        | none =>
          IO.eprintln s!"Error: unknown backend '{name}'; choose from: lean, c, python, rust"
          return 1
      | [] => IO.eprintln "Error: --backend requires an argument (lean|c|python|rust)"; return 1
    else if arg == "--limits" then
      match args.drop (i + 1) with
      | name :: _ =>
        let valid := ["default", "strict", "permissive", "unlimited", "safe_tags"]
        if valid.contains name then
          limitsPreset := some name; skipNext := true
        else
          IO.eprintln s!"Error: unknown limits preset '{name}'; choose from: {valid}"
          return 1
      | [] => IO.eprintln "Error: --limits requires a preset name"; return 1
    else if arg == "--compare" || arg == "--reports" then
      match args.drop (i + 1) with
      | dir :: _ =>
        if arg == "--compare" then compareDir := some dir else reportsDir := some dir
        skipNext := true
      | [] =>
        IO.eprintln s!"Error: {arg} requires a directory argument"
        return if arg == "--compare" then 2 else 1
    else if arg == "-C" || arg == "--root" then
      match args.drop (i + 1) with
      | dir :: _ => root := dir; skipNext := true
      | [] => IO.eprintln s!"Error: {arg} requires a directory argument"; return 1
    else if arg == "--compare-timeout" then
      match (args.drop (i + 1)).head? >>= String.toNat? with
      | some n => compareTimeout := n; skipNext := true
      | none => IO.eprintln "Error: --compare-timeout requires a number of seconds"; return 2
    else
      stageArg := arg
    i := i + 1

  if let some dir := reportsDir then return ← runReports root dir
  if let some dir := compareDir then return ← runCompare root dir compareTimeout

  let stage := parseStageArg stageArg

  -- Locate yaml-test-suite relative to executable
  let suiteDir := "yaml-test-suite"
  let srcPath : System.FilePath := suiteDir ++ "/src"
  let srcExists ← srcPath.pathExists
  if !srcExists then
    IO.eprintln s!"Error: yaml-test-suite not found at {suiteDir}"
    IO.eprintln "Run: git submodule update --init"
    return 1

  IO.println "══════════════════════════════════════════════════════════"
  let limitsLabel := match limitsPreset with | some p => s!", limits={p}" | none => ""
  IO.println s!"  yaml-test-suite Runner for lean4-yaml-verified [{backend}{limitsLabel}]"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""
  flushStdout
  dbg t0 "banner printed"

  -- Read and parse all test files
  IO.print "Loading test files... "
  flushStdout
  dbg t0 "reading test files from yaml-test-suite/src"
  let files ← readTestFiles suiteDir
  dbg t0 s!"read {files.size} files, parsing metadata"
  let mut allCases : Array TestCase := #[]
  for pair in files do
    let cases := parseTestFile pair.1 pair.2
    allCases := allCases ++ cases
  dbg t0 s!"parsed {allCases.size} test cases"
  IO.println s!"{allCases.size} test cases from {files.size} files"
  IO.println ""
  flushStdout

  -- Print stage distribution
  IO.println "Test distribution by stage:"
  let stages := #[Stage.scalar, .flow, .block, .document, .advanced, .error]
  for s in stages do
    let count := allCases.filter (·.stage == s) |>.size
    IO.println s!"  {s}: {count}"
  IO.println ""
  flushStdout
  dbg t0 "distribution printed, entering main test loop"

  -- Measurement mode used by --compare: run the unique roster, retain errors,
  -- and distinguish completed acceptance measurements from conformance gates.
  if let some file := observationsFile then
    let results ← runAllForReport allCases .all (startMs := t0)
      (backend := backend) (limitsPreset := limitsPreset)
    let evidence : Reports.BackendEvidence := {
      backend := toString backend
      preset := limitsPreset.getD "unlimited"
      cases := results.map observationOfReport }
    IO.FS.writeFile file (Lean.toJson evidence).pretty
    match Reports.validateRun evidence with
    | .ok _ => return 0
    | .error e => IO.eprintln e; return 1

  -- Shared helper: run all verified test suites and print progress
  let runVerifiedSuites : IO (Array Tests.VerifiedSuiteResult) := do
    IO.println "\nRunning verified test suites..."
    flushStdout
    dbg t0 "starting verified test suites"
    let collectors : Array (IO Tests.VerifiedSuiteResult) := #[
      Tests.collectTests,
      Tests.ExplicitKey.collectTests,
      Tests.Flow.collectTests,
      Tests.Validation.collectTests,
      Tests.DumpRoundTrip.collectTests,
      Tests.RawParse.collectTests,
      Tests.SpecExamples.collectTests,
      Tests.SchemaDump.collectTests,
      Tests.ScannerTests.collectTests,
      Tests.ScannerSpecExamples.collectTests,
      Tests.AdversarialGrammar.collectTests,
      Tests.AdversarialInstantiation.collectTests,
      Tests.MutationSuite.collectTests,
      Tests.PropertyTests.collectTests,
      Tests.ProdCoverage.collectTests,
      Tests.Limits.collectTests,
      Demo.collectTests
    ]
    let mut verifiedSuites : Array Tests.VerifiedSuiteResult := #[]
    for collect in collectors do
      let result ← collect
      let icon := if result.allPass then "✓" else "✗"
      IO.println s!"  {result.label}: {icon} {result.passed}/{result.total}"
      flushStdout
      dbg t0 s!"verified suite: {result.label} {result.passed}/{result.total}"
      verifiedSuites := verifiedSuites.push result
    let totalVPassed := verifiedSuites.foldl (fun acc s => acc + s.passed) 0
    let totalVTests := verifiedSuites.foldl (fun acc s => acc + s.total) 0
    IO.println s!"\nVerified: {totalVPassed}/{totalVTests}"
    flushStdout
    return verifiedSuites

  -- Shared helper: run all suite tests and collect results
  let runAllSuiteTests : IO (Array ReportResult) := do
    IO.println s!"Running all tests..."
    IO.println (String.ofList (List.replicate 60 '-'))
    flushStdout
    let results ← runAllForReport allCases .all (startMs := t0) (backend := backend)
                     (limitsPreset := limitsPreset)
    IO.println (String.ofList (List.replicate 60 '-'))
    flushStdout
    dbg t0 "computing coverage stats"
    let stats := CoverageStats.fromResults results
    IO.println s!"\nCorrect: {stats.correctCount}/{stats.total} ({stats.successRate.floor}%)"
    flushStdout
    return results

  -- JSON-only mode: run all tests + verified suites, write JSON
  match jsonDir with
  | some dir =>
    let results ← runAllSuiteTests
    let verifiedSuites ← runVerifiedSuites
    dbg t0 "generating JSON"
    IO.println s!"\nGenerating JSON..."
    flushStdout
    writeJsonOnly results dir
      (verifiedSuites := some verifiedSuites)
      (snapshot := snapshot)
    dbg t0 "done"
    return if reportSucceeded results verifiedSuites then 0 else 1
  | none => pure ()

  -- HTML report mode: run all tests and generate reports
  match htmlDir with
  | some dir =>
    let results ← runAllSuiteTests
    let verifiedSuites ← runVerifiedSuites

    dbg t0 "generating HTML reports"
    IO.println s!"\nGenerating HTML reports..."
    flushStdout
    writeReports results dir
      (verifiedSuites := some verifiedSuites)
    dbg t0 "done"
    return if reportSucceeded results verifiedSuites then 0 else 1
  | none => pure ()

  -- Console mode: run the requested stage(s)
  if stage == .all then
    let mut totalStats : TestStats := {}
    for s in stages do
      if s != .error then  -- Skip error tests in "all" mode for now
        let stats ← runStage s allCases verbose backend limitsPreset
        totalStats := {
          total := totalStats.total + stats.total
          passed := totalStats.passed + stats.passed
          failed := totalStats.failed + stats.failed
          skipped := totalStats.skipped + stats.skipped
          failures := totalStats.failures ++ stats.failures
        }
    IO.println "══════════════════════════════════════════════════════════"
    IO.println s!"  TOTAL: {totalStats}"
    IO.println "══════════════════════════════════════════════════════════"
    return if totalStats.failed == 0 then 0 else 1
  else
    let stats ← runStage stage allCases verbose backend limitsPreset
    return if stats.failed == 0 then 0 else 1

end Blanket
