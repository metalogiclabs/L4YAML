import Lean

namespace R2CompletionEdit

def replaceCount (source old replacement : String) (count : Nat) : IO String := do
  unless (source.splitOn old).length == count+1 do
    throw (IO.userError s!"expected {count} source matches; found {(source.splitOn old).length-1}: {old.take 90}")
  pure (source.replace old replacement)

def once (source old replacement : String) : IO String := replaceCount source old replacement 1

def throughParen (chars : List Char) : IO (String × String) := do
  let mut depth : Int := 0
  let mut taken := 0
  for c in chars do
    taken := taken+1
    if c == '(' then depth := depth+1
    if c == ')' then depth := depth-1
    if depth == 0 then return (String.ofList (chars.take taken),String.ofList (chars.drop taken))
  throw (IO.userError "unterminated argument")

def wrapCompleted (source : String) (extras : Array String) : IO String := do
  let marker := "(fun e comments z tail =>"
  let mut rest := source
  let mut output := ""
  for extra in extras do
    let head :: tail := rest.splitOn marker | throw (IO.userError "completion search")
    unless !tail.isEmpty do throw (IO.userError "completion absent")
    let (argument,afterArgument) ← throughParen (marker ++ String.intercalate marker tail).toList
    output := output ++ head ++ "(R2MandatoryContext.pair_completed " ++ argument ++ "\n" ++ extra ++ ")"
    rest := afterArgument
  pure (output ++ rest)

end R2CompletionEdit

open R2CompletionEdit

def main (args : List String) : IO Unit := do
  let [basePath,outputPath] := args | throw (IO.userError "expected parent source and output path")
  let mut source ← IO.FS.readFile basePath
  let completion ← IO.FS.readFile "Research/R2MandatoryContext/Completion.lean"
  let content := "lemma context_content" ++ (((completion.splitOn "lemma context_content").getLast!).splitOn "lemma context_flow").head!
  let completed := "def Completed (s : ScannerState) (P : SurfPos → Prop) (n : Nat) (gram : SurfPos) : Prop :=\n  ∀ e, SSLComments gram e → ∀ z, SCompactSeqTail n e z → Context s P z\n"
  let pair := "lemma pair_completed {s : ScannerState} {start gram : SurfPos} {k : Nat}\n    (old : ∀ e, SSLComments gram e → ∀ z, SCompactSeqTail k e z →\n      SLYamlStream start z ∧ L4YAML.Proofs.R2ConsumptionClosure.EntryValues s (SLYamlStream start) z)\n    (whole : Completed s (SLYamlStream start) k gram) :\n    ∀ e, SSLComments gram e → ∀ z, SCompactSeqTail k e z →\n      SLYamlStream start z ∧ (L4YAML.Proofs.R2ConsumptionClosure.EntryValues s (SLYamlStream start) z ∧ Context s (SLYamlStream start) z) :=\n  fun e comments z tail => ⟨(old e comments z tail).1,(old e comments z tail).2,whole e comments z tail⟩\n"
  source ← once source "end R2MandatoryContext\nend R2MandatoryContextImports" (completed ++ content ++ pair ++ "\nend R2MandatoryContext\nend R2MandatoryContextImports")
  let oldPair := "SLYamlStream sp_start sp_end ∧ EntryValues sc (SLYamlStream sp_start) sp_end"
  let newPair := "SLYamlStream sp_start sp_end ∧ (EntryValues sc (SLYamlStream sp_start) sp_end ∧ R2JointFrames.Context sc (SLYamlStream sp_start) sp_end)"
  -- Exactly the property field, completed field, completed reader parameter,
  -- and normalized property reader. Other mandatory fields already carry it.
  source ← replaceCount source oldPair newPair 4
  let oldExtract := "  have h_completedContext : CompletedValues sc sp_start n sp_gram :=\n    fun e comments z tail => (h_entry_old e comments z tail).2"
  let newExtract := "  have h_wholeCompletedContext : R2MandatoryContext.Completed sc (SLYamlStream sp_start) n sp_gram :=\n    fun e comments z tail => (h_entry_old e comments z tail).2.2\n  have h_completedContext : CompletedValues sc sp_start n sp_gram :=\n    fun e comments z tail => (h_entry_old e comments z tail).2.1"
  source ← once source oldExtract newExtract
  source ← replaceCount source "(route e' (by simpa only [coupling] using node') z' tail').2" "(route e' (by simpa only [coupling] using node') z' tail').2.1" 2
  source ← replaceCount source "(routeE e node z tail).2)" "(routeE e node z tail).2.1)" 3
  source ← replaceCount source "(routeE sp_m (h_nodeAtG sp_m h_ssl) sp_e h_tail).2" "(routeE sp_m (h_nodeAtG sp_m h_ssl) sp_e h_tail).2.1" 2
  source ← once source "(routeE sp_m (h_nodeAt sp_m h_ssl) sp_e h_tail).2" "(routeE sp_m (h_nodeAt sp_m h_ssl) sp_e h_tail).2.1"
  let propBirth := "(SequenceValues.nodes h_sequenceContext (fun x hx => markedCols_mem_of_step_content h_preprocess h_dispatch hx)) sp_m h_bn sp_end h_tail⟩⟩)"
  let propBirthNew := "(SequenceValues.nodes h_sequenceContext (fun x hx => markedCols_mem_of_step_content h_preprocess h_dispatch hx)) sp_m h_bn sp_end h_tail,\n                 R2MandatoryContext.context_content h_preprocess h_dispatch\n                   (h_wholeSequenceContext sp_m (SBlockIndented.node n .blockIn sp_scan sp_m h_bn) sp_end h_tail)⟩⟩)"
  source ← once source propBirth propBirthNew
  let ride := "e (by simpa only [coupling] using node) z tail⟩)"
  let rideNew := "e (by simpa only [coupling] using node) z tail,\n                       R2MandatoryContext.context_content h_preprocess h_dispatch (route e node z tail).2.2⟩)"
  source ← replaceCount source ride rideNew 2
  let directFlow := "(by\n      intro e comments z tail\n      exact R2MandatoryContext.context_content h_preprocess h_dispatch\n        (h_wholeSequenceContext e\n          (SBlockIndented.node n .blockIn sp_scan e\n            (SBlockNode.flowInBlock (n+1) .blockIn sp_scan sp_prep sp_gram e\n              h_sep_all (h_flow_all (n+1)) comments)) z tail))"
  let directBlock := "(by\n      intro e comments z tail\n      exact R2MandatoryContext.context_content h_preprocess h_dispatch\n        (h_wholeSequenceContext e (SBlockIndented.node n .blockIn sp_scan e (h_nodeAt e comments)) z tail))"
  let directJson := "(by\n      intro e comments z tail\n      exact R2MandatoryContext.context_content h_preprocess h_dispatch\n        (h_wholeSequenceContext e\n          (SBlockIndented.node n .blockIn sp_scan e\n            (SBlockNode.flowInBlock (n+1) .blockIn sp_scan sp_prep sp_gramf e h_sep_all h_node_f comments)) z tail))"
  let decoratedG := "(by intro e comments z tail; exact R2MandatoryContext.context_content h_preprocess h_dispatch (routeE e (h_nodeAtG e comments) z tail).2.2)"
  let decorated := "(by intro e comments z tail; exact R2MandatoryContext.context_content h_preprocess h_dispatch (routeE e (h_nodeAt e comments) z tail).2.2)"
  source ← wrapCompleted source #[directFlow,directBlock,directJson,decoratedG,decorated,decoratedG]
  let sibling := "(by\n      apply R2MandatoryContext.sequence_step h_preprocess\n        (dispatchBlockIndicators_dash_scan h_dispatch).2\n        (dispatchBlockIndicators_dash_scan h_dispatch).1 h_sound h_mono\n        (by have hcol := hcorr_prep.col_eq; have hi := SIndent_col h_ind;\n            unfold R2ActualJointStep.dispatchState; split <;> change s_prep.col = _ <;> omega)\n      intro e node z tail\n      exact h_wholeCompletedContext sp_mid h_ssl z\n        (SCompactSeqTail.cons k sp_mid _ sp_scan' e z h_ind h_dash2 h_gnot2 node tail))"
  source ← once source "(by trace_state; fail \"R2_WHOLE_COMPLETED_SEQUENCE\")" sibling
  IO.FS.writeFile outputPath source
  IO.println "PREPARED completion_and_property_context new_fields=0 separate_context_parameters=0"
