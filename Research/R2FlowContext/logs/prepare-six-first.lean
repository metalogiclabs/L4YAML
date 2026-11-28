import Lean

def once (s old new : String) : IO String := do
  unless (s.splitOn old).length == 2 do
    throw (IO.userError s!"nonunique source anchor ({(s.splitOn old).length-1}): {old.take 100}")
  pure (s.replace old new)

def main (args : List String) : IO Unit := do
  let inputPath :: outputPath :: modes := args | throw (IO.userError "expected parent and output")
  let mut s ← IO.FS.readFile inputPath
  let [before,routes] := s.splitOn "structure FlowBaseRoutes "
    | throw (IO.userError "flow routes declaration")
  let routes :: after := routes.splitOn "/-- **Kinds index (9b(i))**."
    | throw (IO.userError "flow routes end")
  let old := "SSLComments sp_ne sp_mid → SLYamlStream sp_start sp_mid"
  unless (routes.splitOn old).length == 3 do throw (IO.userError "two value declarations required")
  s := before ++ "structure FlowBaseRoutes " ++
    routes.replace old "SSLComments sp_ne sp_mid → R2Mandatory.Full s0 sp_start sp_mid" ++
    "/-- **Kinds index (9b(i))**." ++ String.intercalate "/-- **Kinds index (9b(i))**." after
  s ← once s "SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m) →\n      FlowStackB sp_start n"
    "SSLComments sp_ne sp_m → R2Mandatory.Full s' sp_start sp_m) →\n      FlowStackB sp_start n"
  let reader := "fun hnd hui sp_m h_ssl => resume.value\n"
  unless (s.splitOn reader).length == 3 do throw (IO.userError "two actual flow-close readers required")
  s := s.replace reader "fun hnd hui sp_m h_ssl => (resume.value\n"
  for (kind,grammar) in [("Sequence","flowSeq"),("Mapping","flowMap")] do
    let oldEnd := "sp_tok sp_m (SFlowContent." ++ grammar ++ " _ _ _ _ h_" ++
      (if kind == "Sequence" then "seq" else "map") ++ ") h_ssl)"
    let newEnd := oldEnd.dropEnd 1 |>.toString
    s ← once s oldEnd (newEnd ++ ").of_eq\n" ++
      "                      ((L4YAML.Proofs.PendingKeysStable.scanFlow" ++ kind ++ "End_preserves_pendingKeys s_ad).trans (h_pk_ad.trans h_pk_park))\n" ++
      "                      ((L4YAML.Proofs.EmitterScannability.scanFlow" ++ kind ++ "End_preserves_indents s_ad).trans (h_ind_ad.trans h_ind_park)))")
  if modes == ["--fund-three"] || modes == ["--fund-six"] then
    s ← once s "  rw [h_fl1]\n  -- Item 363:" "  have flowContext {e : SurfPos} (h : R2Mandatory.Full sc sp_start e) :\n      R2Mandatory.Full s' sp_start e :=\n    (h.preprocess h_preprocess).of_eq h_pk' h_ind'\n  rw [h_fl1]\n  -- Item 363:"
    s ← once s "| pendingBlock _ _ _ n_old h_close _ h_floor_old h_sk_old h_col59"
      "| pendingBlock _ _ _ n_old h_close h_entryFull h_floor_old h_sk_old h_col59"
    s ← once s
      "h_close sp_m (SBlockIndented.node n_old .blockIn sp_scan sp_m\n                 (SBlockNode.flowInBlock (n_old + 1) .blockIn sp_scan sp_prep sp_ne sp_m\n                   h_sep (SFlowNode.content _ _ _ _ h_content) h_ssl)))"
      "flowContext (h_entryFull sp_m (SBlockIndented.node n_old .blockIn sp_scan sp_m\n                 (SBlockNode.flowInBlock (n_old + 1) .blockIn sp_scan sp_prep sp_ne sp_m\n                   h_sep (SFlowNode.content _ _ _ _ h_content) h_ssl)) sp_m (SCompactSeqTail.nil n_old sp_m)))"
    s ← once s
      "h_route (h_pay_p h_g) sp_m (flowInBlock_blockNode h_sep_run\n                 (SFlowNode.propsContent n .flowOut sp_p sp_scan sp_prep sp_ne\n                   h_run.toProperties h_sep h_content) h_ssl))"
      "flowContext (h_route (h_pay_p h_g) sp_m (flowInBlock_blockNode h_sep_run\n                 (SFlowNode.propsContent n .flowOut sp_p sp_scan sp_prep sp_ne\n                   h_run.toProperties h_sep h_content) h_ssl)))"
    s ← once s
      "h_close sp_m (SBlockNode.flowInBlock (n_old + 1) .blockOut sp_scan sp_prep sp_ne sp_m\n                 h_sep (SFlowNode.content _ _ _ _ h_content) h_ssl))"
      "flowContext (h_close sp_m (SBlockNode.flowInBlock (n_old + 1) .blockOut sp_scan sp_prep sp_ne sp_m\n                 h_sep (SFlowNode.content _ _ _ _ h_content) h_ssl)))"
  if modes == ["--fund-six"] then
    s ← once s "    (h_sound : PendingKeySound.Sound sc)\n    {h_maps : R2MapOwnership.Maps sc}\n    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))\n    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)\n    (hcorr_open : ScannerSurfCorr s' sp_open)"
      "    (h_sound : PendingKeySound.Sound sc)\n    {h_maps : R2MapOwnership.Maps sc}\n    {h_mono : IndentStackMono.Mono sc}\n    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))\n    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)\n    (hcorr_open : ScannerSurfCorr s' sp_open)"
    let call := "accum_flow_open_depth0 (h_maps := h_maps) sc"
    unless (s.splitOn call).length == 3 do throw (IO.userError "two geometry callers required")
    s := s.replace call "accum_flow_open_depth0 (h_maps := h_maps) (h_mono := h_mono) sc"
    s ← once s "  rw [h_fl1]\n  -- Item 363:" "  have flowBaseContext {e : SurfPos} (negative : sc.currentIndent < 0)\n      (stream : SLYamlStream sp_start e) : R2Mandatory.Full s' sp_start e :=\n    flowContext (R2Mandatory.Full.at_base h_mono negative stream)\n  rw [h_fl1]\n  -- Item 363:"
    s ← once s "| noPending _ _ h_col h_armN h_nodoc h_noekN _ h_gateN =>"
      "| noPending _ _ h_col h_armN h_nodoc h_noekN h_ntopN h_gateN =>"
    s ← once s
      "(fun _ => nodocFlowResumeSep (h_nodoc h_scflow)\n                 (h_sep.resolve_right (fun h => absurd h.2.2 (by omega))))"
      "(fun _ sp_ne sp_m content comments => flowBaseContext (h_ntopN h_scflow)\n                 (nodocFlowResumeSep (h_nodoc h_scflow)\n                   (h_sep.resolve_right (fun h => absurd h.2.2 (by omega))) sp_ne sp_m content comments))"
    s ← once s
      "h_docnode sp_m (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_ne sp_m\n               h_sep (SFlowNode.content _ _ _ _ h_content) h_ssl))"
      "flowBaseContext (by assumption) (h_docnode sp_m (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_ne sp_m\n               h_sep (SFlowNode.content _ _ _ _ h_content) h_ssl)))"
    s ← once s "((∀ sp_m, SSLComments sp_g sp_m → SuffixRun sp_start sp_m) ∨ True) →"
      "((sc.currentIndent < 0 ∧ ∀ sp_m, SSLComments sp_g sp_m → SuffixRun sp_start sp_m) ∨ True) →"
    s ← once s
      "intro sp_g h_trail h_gateM h_close h_nobreak h_sfx h_tail143 h_mapF176 h_mapFV201"
      "intro sp_g h_trail h_gateM h_close h_nobreak h_sfxFull h_tail143 h_mapF176 h_mapFV201\n    have h_sfx : (∀ sp_m, SSLComments sp_g sp_m → SuffixRun sp_start sp_m) ∨ True := h_sfxFull.imp And.right id"
    s ← once s "match h_sfx with\n               | Or.inl sfx => suffixFlowResumeSep (sfx sp_mid h_ssl)"
      "match h_sfxFull with\n               | Or.inl ⟨negative, sfx⟩ => fun sp_ne sp_m content comments => flowBaseContext negative (suffixFlowResumeSep (sfx sp_mid h_ssl)"
    s ← once s
      "(fun heq => col0_of_ssl_landing h_ssl (heq ▸ hcorr_prep) (preprocess_some_peek h_preprocess))))\n               | Or.inr _ =>"
      "(fun heq => col0_of_ssl_landing h_ssl (heq ▸ hcorr_prep) (preprocess_some_peek h_preprocess)))) sp_ne sp_m content comments)\n               | Or.inr _ =>"
    s ← once s "(Or.inl (fun sp_m h_ssl =>\n        ⟨sp_block, sp_m, h_stream_block,"
      "(Or.inl ⟨by assumption, fun sp_m h_ssl =>\n        ⟨sp_block, sp_m, h_stream_block,"
    s ← once s "(SLDocumentSuffix.mk sp_block sp_scan sp_m h_marker h_ssl) (GStar.nil _),\n         GStar.nil _⟩))"
      "(SLDocumentSuffix.mk sp_block sp_scan sp_m h_marker h_ssl) (GStar.nil _),\n         GStar.nil _⟩⟩)"
  if !modes.isEmpty then
    s := s ++ (← IO.FS.readFile "Research/R2FlowContext/ProductionAudit.inc.lean")
  IO.FS.writeFile outputPath s
  IO.println "PREPARED existing_flow_value_answer=Full existing_scanner_index=s0 close_readers=2"
