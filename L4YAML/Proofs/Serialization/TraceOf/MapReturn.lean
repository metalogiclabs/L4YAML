/- Capstone 7.7 / S3: paid root mapping routes, native ordinary key heads,
and the actual colon-to-pending-map-value handoff. The global paired
scanner fold and collection-key line correspondence remain open. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.KeyEvents
public import L4YAML.Proofs.Serialization.TraceOf.FlowReturn
@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.MapReturn
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.StructureProduction
open L4YAML.Proofs.Serialization.ScannerShape
open L4YAML.Proofs.StreamAccum (dispatchContent_doubleQuoted_key_prod dispatchContent_singleQuoted_key_prod dispatchContent_plainScalar_key_prod)
open L4YAML.Proofs.ScalarProduction L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.Serialization.TraceOf.FlowReturn
open L4YAML.Proofs.Serialization.TraceOf.KeyEvents
open L4YAML.Proofs.ScannerPlainScalarValid

/-- The native leaf is reread as its actual single-line implicit key. Key
line/position premises are the saved register projections consumed by the
successful colon, rather than an assumed trace/key certificate. -/
lemma implicit_key_of_dispatch {sc after : ScannerState} {ch : Char}
    {begin scan : SurfPos}
    (hc : ScannerSurfCorr sc begin) (ha : ScannerSurfCorr after scan)
    (peek : sc.peek? = some ch) (edge : scanNextToken_dispatchContent sc ch = .ok after)
    (saved : sc.simpleKey.pos = sc.currentPos)
    (possible : after.simpleKey.possible = true)
    (line : after.simpleKey.pos.line = after.line)
    (flow : sc.inFlow = false)
    (notDoc : sc.col = 0 → atDocumentBoundary sc = false)
    (noAnchor : ch ≠ '&') (noTag : ch ≠ '!') :
    ∃ events, TImplicitKey begin scan events ∧ PushesTrace sc.tokens after.tokens events := by
  by_cases hb : ch = '|' ∨ ch = '>'
  · exact absurd possible (by
      rw [L4YAML.Proofs.StreamAccum.dispatchContent_blockScalar_simpleKey_false hb edge]
      decide)
  have hpipe : ch ≠ '|' := fun h => hb (Or.inl h)
  have hgt : ch ≠ '>' := fun h => hb (Or.inr h)
  have sameLine (hpp : after.simpleKey.pos = sc.simpleKey.pos) : after.line = sc.line := by
    have h := congrArg YamlPos.line (hpp.trans saved)
    exact line.symm.trans h
  by_cases hstar : ch = '*'
  · subst ch
    obtain ⟨stop, name, ht, hc', halias⟩ :=
      dispatchContent_alias_trace sc begin hc peek after edge
    have hs : stop = scan := ScannerSurfCorr_unique hc' ha
    subst stop
    refine ⟨[.useAlias name], .jsonKey _ _ _ _ (.alias 0 .blockKey _ _ _ halias) (.none _), ?_⟩
    rw [ht]
    simpa [tokenEvent] using pushesTrace_push sc.tokens
      ⟨sc.currentPos, .alias name, sc.currentPos⟩ (by simp) (by simp)
  by_cases hd : ch = '"'
  · subst ch
    obtain ⟨hpp, hkey⟩ := dispatchContent_doubleQuoted_key_prod sc begin hc peek edge
    obtain ⟨stop, hquoted, _, hc'⟩ := hkey (sameLine hpp)
    have hs := ScannerSurfCorr_unique hc' ha
    subst stop
    obtain ⟨_, _, ht, _, _⟩ := dispatchContent_doubleQuoted_trace sc begin hc peek after edge
    refine ⟨[], .jsonKey _ _ _ _ (.content 0 .blockKey _ _ _ (.doubleQ 0 .blockKey _ _ hquoted)) (.none _), ?_⟩
    rw [ht]
    exact pushesTrace_push_scalar _ _ rfl
  by_cases hsq : ch = '\''
  · subst ch
    obtain ⟨hpp, hkey⟩ := dispatchContent_singleQuoted_key_prod sc begin hc peek edge
    obtain ⟨stop, hquoted, _, hc'⟩ := hkey (sameLine hpp)
    have hs := ScannerSurfCorr_unique hc' ha
    subst stop
    obtain ⟨_, _, ht, _, _⟩ := dispatchContent_singleQuoted_trace sc begin hc peek after edge
    refine ⟨[], .jsonKey _ _ _ _ (.content 0 .blockKey _ _ _ (.singleQ 0 .blockKey _ _ hquoted)) (.none _), ?_⟩
    rw [ht]
    exact pushesTrace_push_scalar _ _ rfl
  obtain ⟨hpp, hkey⟩ := dispatchContent_plainScalar_key_prod sc begin hc peek flow
    noAnchor hstar noTag hpipe hgt hd hsq notDoc edge
  obtain ⟨grammarEnd, stop, hplain, hwhite, _, hc'⟩ := hkey (sameLine (by rw [hpp]))
  have hs := ScannerSurfCorr_unique hc' ha
  subst stop
  obtain ⟨_, ht⟩ := dispatchContent_plain_tokens edge
    noAnchor hstar noTag hpipe hgt hd hsq
  refine ⟨[], .yamlKey _ _ _ hplain (gstar_sswhite_to_gopt_sep hwhite), ?_⟩
  rw [ht]
  exact pushesTrace_push_scalar _ _ rfl

/-- First-document mapping-entry return, paid from the source prefix and
indentation. No preceding T stream or global route is assumed. -/
lemma first_map_route {start line key : SurfPos} {k : Nat}
    (prior : GStar SLDocumentPrefix start line) (col : line.col = 0)
    (indent : SIndent k line key) :
    ∀ stop events, TBlockMapEntry k key stop events → TLYamlStream start stop events := by
  intro stop events entry
  exact TLYamlStream.bareRoute prior stop events
    (TBlockNode.blockMap 0 .blockIn k line line line stop [] events (.none _)
      (L4YAML.Proofs.StreamAccum.sslComments_refl_of_col0 col)
      (by simpa only [Nat.zero_add] using TBlockMapEntries.single k line key stop events indent entry))

/-- Retain a key through the actual trailing whites consumed before ':'. -/
lemma implicit_key_white {key stop prep : SurfPos} {events : List Event}
    (h : TImplicitKey key stop events) (white : GStar SSWhite stop prep) :
    TImplicitKey key prep events := by
  have extend {a : SurfPos} (sep : GOpt SSeparateInLine a stop) :
      GOpt SSeparateInLine a prep := by
    cases sep with
    | none => exact gstar_sswhite_to_gopt_sep white
    | some _ inline =>
      cases inline with
      | startOfLine => exact gstar_sswhite_to_gopt_sep white
      | whites _ _ hp =>
        cases hp with
        | mk mid _ first rest =>
          exact .some _ _ (.whites _ _ (.mk _ _ _ first (gstar_sswhite_append rest white)))
  cases h with
  | jsonKey _ mid _ _ node sep => exact .jsonKey _ _ _ _ node (extend sep)
  | yamlKey _ mid _ node sep => exact .yamlKey _ _ _ node (extend sep)

/-- The first mapping's native colon step. The entry route is constructed
from the actual source prefix; native event equality is derived from reach.
No hRoute, T mapping-entry route or event-prefix equality is a premise. -/
lemma first_implicit_colon {input : String} {sc prep after : ScannerState}
    {start line key scan colonPos : SurfPos} {k : Nat} {events : List Event}
    (reach : RightWallHistory.ScannerReachable input sc)
    (trace : TSLYamlStream start sc line [] events [])
    (keyHead : TImplicitKey key scan events)
    (prior : GStar SLDocumentPrefix start line) (col : line.col = 0)
    (indent : SIndent k line key)
    (pre : scanNextToken_preprocess sc = .ok (some (prep, ':')))
    (white : GStar SSWhite scan colonPos)
    (corr : ScannerSurfCorr prep colonPos)
    (edge : scanNextToken_dispatchBlockIndicators
      (if prep.allowDirectives then
        { prep with allowDirectives := false, documentEverStarted := true } else prep)
      ':' = .ok (some after)) :
    ∃ stop, ScannerSurfCorr after stop ∧
      TSLYamlStream start after line [] events [] ∧
      (∀ finish evValue, TBlockNode (k + 1) .blockOut stop finish evValue →
        TLYamlStream start finish (events ++ evValue)) ∧
      TPendingNode start false line stop [] events [] := by
  let ad := if prep.allowDirectives then
    { prep with allowDirectives := false, documentEverStarted := true } else prep
  have hc : ScannerSurfCorr ad colonPos :=
    L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update corr
  have peek : ad.peek? = some ':' := by
    have hp := L4YAML.Proofs.StreamAccum.preprocess_some_peek pre
    dsimp only [ad]
    split <;> exact hp
  obtain ⟨stop, lit, hc'⟩ := L4YAML.Proofs.StructureProduction.scanValue_prod ad colonPos
    hc peek after (L4YAML.Proofs.StreamAccum.dispatchBlock_colon_scanValue edge)
  have ht : TSLYamlStream start after line [] events [] :=
    ⟨trace.stream, by rw [reachable_colon_goOut reach pre edge []]; exact trace.events⟩
  have close : ∀ finish evValue, TBlockNode (k + 1) .blockOut stop finish evValue →
      TLYamlStream start finish (events ++ evValue) := by
    intro finish evValue node
    simpa using first_map_route prior col indent finish (events ++ evValue)
      (.implicitKeyNode k key colonPos stop finish events evValue
        (implicit_key_white keyHead white) lit node)
  exact ⟨stop, hc', ht, close, .pendingMapValue line stop k [] events close⟩

/-- A paid pending-map-value continuation funds its flow opener. This is
the same node route already constructed at the native colon, at its real floor. -/
lemma return_map_value {start node root : SurfPos} {k : Nat} {prior : List Event}
    (close : ∀ finish events, TBlockNode (k + 1) .blockOut node finish events →
      TLYamlStream start finish (prior ++ events))
    (sep : SSeparate (k + 1) .flowOut node root) :
    ∀ stop events, TFlowContent (k + 1) .flowOut root stop events →
      StreamReturn start prior stop events := by
  intro stop events content finish comments
  exact close finish events (.flowInBlock (k + 1) .blockOut node root stop finish events
    sep (.content _ _ _ _ _ content) comments)

end L4YAML.Proofs.Serialization.TraceOf.MapReturn
end Blanket
