import Lean

-- Source preparation is deliberately mechanical. The compiler, not this
-- instrument, decides which actual writers can supply the strengthened field.
def replaceOnce (source old replacement : String) : IO String := do
  unless (source.splitOn old).length == 2 do
    throw (IO.userError s!"expected one source match, found {(source.splitOn old).length - 1}")
  pure (source.replace old replacement)

def replaceCount (source old replacement : String) (count : Nat) : IO String := do
  unless (source.splitOn old).length == count+1 do
    throw (IO.userError s!"expected {count} source matches, found {(source.splitOn old).length - 1}")
  pure (source.replace old replacement)

def throughParen (chars : List Char) : IO (String × String) := do
  let mut depth : Int := 0
  let mut taken := 0
  for c in chars do
    taken := taken + 1
    if c == '(' then depth := depth + 1
    if c == ')' then depth := depth - 1
    if depth == 0 then
      return (String.ofList (chars.take taken), String.ofList (chars.drop taken))
  throw (IO.userError "unterminated constructor argument")

def wrapWriters (source : String) (extras : Array String) : IO String := do
  let marker := "(fun e node z tail =>"
  let mut rest := source
  let mut result := ""
  for extra in extras do
    let head :: tail := rest.splitOn marker | throw (IO.userError "writer search failed")
    unless !tail.isEmpty do throw (IO.userError "writer absent")
    let (argument, afterArgument) ← throughParen (marker ++ String.intercalate marker tail).toList
    result := result ++ head ++ "(R2MandatoryContext.pair_completion " ++ argument ++ "\n" ++ extra ++ ")"
    rest := afterArgument
  pure (result ++ rest)

def main (args : List String) : IO Unit := do
  let basePath :: outputPath :: modes := args | throw (IO.userError "expected baseline and output paths")
  let base ← IO.FS.readFile basePath
  let snapshot ← IO.FS.readFile "Research/R2ScannerMapOwnership/lineage/joint/Joint.lean"
  let [_, joint] := snapshot.splitOn "namespace R2JointFrames\n" |
    throw (IO.userError "joint snapshot namespace is not unique")
  let levels := "\nnamespace R2JointFrames\ndef levels (sc : ScannerState) : List FrameLevel :=\n  sc.indents.toList.reverse.filterMap fun e =>\n    if e.column < 0 then none\n    else some (if e.isSequence then FrameLevel.seq e.column.toNat else FrameLevel.map e.column.toNat)\n"
  let marker := "namespace L4YAML.Proofs.R2SequenceContext\n\ndef SequenceValues"
  let prepared ← replaceOnce base marker (levels ++ joint ++ "\n" ++ marker)
  let old := "(h_close_entry : ∀ sp_mid,\n        SBlockIndented n .blockIn sp_scan sp_mid →\n        ∀ sp_end, SCompactSeqTail n sp_mid sp_end →\n          SLYamlStream sp_start sp_end ∧ EntryValues sc (SLYamlStream sp_start) sp_end)"
  let replacement := "(h_close_entry : ∀ sp_mid,\n        SBlockIndented n .blockIn sp_scan sp_mid →\n        ∀ sp_end, SCompactSeqTail n sp_mid sp_end →\n          SLYamlStream sp_start sp_end ∧\n          (EntryValues sc (SLYamlStream sp_start) sp_end ∧\n           R2JointFrames.Context sc (SLYamlStream sp_start) sp_end))"
  let prepared ← replaceOnce prepared old replacement
  let mut prepared := prepared
  if modes == ["--fund-four"] then
    let step ← IO.FS.readFile "Research/R2ScannerMapOwnership/JointStep.lean"
    let [_, stepBody] := step.splitOn "namespace R2ActualJointStep\n" | throw (IO.userError "step namespace")
    let stepBody := (stepBody.splitOn "lemma sequence_top").head!
    let births ← IO.FS.readFile "Research/R2MandatoryContext/Births.lean"
    let push := "lemma sequence_push" ++ (((births.splitOn "lemma sequence_push").getLast!).splitOn "lemma actual_compact_sequence").head!
    let empty := "lemma levels_empty" ++ (((births.splitOn "lemma levels_empty").getLast!).splitOn "lemma actual_first_question").head!
    let completion ← IO.FS.readFile "Research/R2MandatoryContext/Completion.lean"
    let [_, completion] := completion.splitOn "namespace R2MandatoryContext\n" | throw (IO.userError "completion namespace")
    let completion := (completion.splitOn "def Completed").head!
    let adapter := "\nnamespace R2ActualJointStep\n" ++ stepBody ++ "\nend R2ActualJointStep\n" ++
      "open R2JointFrames R2ActualJointStep\nnamespace R2MandatoryContext\n" ++
      "def Sequence (s : ScannerState) (P : SurfPos → Prop) (n : Nat) (slot : SurfPos) : Prop :=\n  ∀ e, SBlockIndented n .blockIn slot e → ∀ z, SCompactSeqTail n e z → Context s P z\n" ++
      push ++ empty ++ completion ++ "\nend R2MandatoryContext\n"
    prepared ← replaceOnce prepared marker (adapter ++ marker)
    let param := "(h_close_entry_old : ∀ (sp : SurfPos), SBlockIndented n .blockIn sp_scan sp →\n      ∀ (sp_end : SurfPos), SCompactSeqTail n sp sp_end →\n        SLYamlStream sp_start sp_end ∧ EntryValues sc (SLYamlStream sp_start) sp_end)"
    let paramNew := "(h_close_entry_old : ∀ (sp : SurfPos), SBlockIndented n .blockIn sp_scan sp →\n      ∀ (sp_end : SurfPos), SCompactSeqTail n sp sp_end →\n        SLYamlStream sp_start sp_end ∧ (EntryValues sc (SLYamlStream sp_start) sp_end ∧\n          R2JointFrames.Context sc (SLYamlStream sp_start) sp_end))"
    prepared ← replaceCount prepared param paramNew 2
    let extract := "  have h_sequenceContext : SequenceValues sc sp_start n sp_scan :=\n    fun e node z tail => (h_close_entry_old e node z tail).2"
    let extractNew := "  have h_wholeSequenceContext : R2MandatoryContext.Sequence sc (SLYamlStream sp_start) n sp_scan :=\n    fun e node z tail => (h_close_entry_old e node z tail).2.2\n  have h_sequenceContext : SequenceValues sc sp_start n sp_scan :=\n    fun e node z tail => (h_close_entry_old e node z tail).2.1"
    prepared ← replaceCount prepared extract extractNew 2
    prepared ← replaceOnce prepared "sp_m (SCompactSeqTail.nil n_old sp_m)).2\n" "sp_m (SCompactSeqTail.nil n_old sp_m)).2.1\n"
    let common := "(by\n      apply R2MandatoryContext.sequence_step h_preprocess\n        (dispatchBlockIndicators_dash_scan h_dispatch).2\n        (dispatchBlockIndicators_dash_scan h_dispatch).1 h_sound h_mono\n        (by have hcol := hcorr_prep.col_eq; have hi := SIndent_col h_ind;\n            unfold R2ActualJointStep.dispatchState; split <;> dsimp <;> omega)\n"
    let extras := #[
      common ++ "      intro e node z tail\n      change R2JointFrames.Joint sc (SLYamlStream sp_start) (R2JointFrames.levels sc) z\n      rw [R2MandatoryContext.levels_empty h_mono (h_ntop h_scflow)]\n      exact h_rootTail e node z tail)",
      "(by trace_state; fail \"R2_WHOLE_COMPACT_VALUE_SLOT\")",
      "(by trace_state; fail \"R2_WHOLE_LANDED_SEQUENCE\")",
      "(by trace_state; fail \"R2_WHOLE_COMPLETED_SEQUENCE\")",
      common ++ "      intro e node z tail\n      exact h_wholeSequenceContext sp_mid h_node_old z\n        (SCompactSeqTail.cons k sp_mid _ sp_scan' e z h_ind h_dash2 h_gnot2 node tail))",
      common ++ "      intro e node z tail\n      exact h_wholeSequenceContext z\n        (SBlockIndented.node n .blockIn sp_scan z\n          (nestedBlockSeq hlt h_ssl (SBlockSeqEntries_of_compactTail h_ind h_dash2 h_gnot2 node tail)))\n        z (SCompactSeqTail.nil n z))",
      common ++ "      intro e node z tail\n      exact h_wholeSequenceContext z\n        (SBlockIndented.compactSeq n .blockIn m sp_mid sp_sc z h_ind\n          (SCompactSeq.mk (n+1+m) sp_sc sp_scan' e z h_dash2 h_gnot2 node tail))\n        z (SCompactSeqTail.nil n z))"]
    prepared ← wrapWriters prepared extras
  IO.FS.writeFile outputPath prepared
  IO.println "PREPARED mandatory=h_close_entry new_fields=0 new_optional_alternatives=0"
