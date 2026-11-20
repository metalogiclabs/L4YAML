/- Capstone 7.7: preserve the actual key's trace when the scanner's
single-line key checks reread a flow node in key context. Reuses the source
FlowKeyLift case tree and leaf/separation/residue proofs, retaining events. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.UniqueFlow
public import L4YAML.Proofs.Production.FlowKeyLift
@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.KeyLift
open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.SurfaceSpan
open L4YAML.Proofs.FlowKeyLift

lemma props_toKey {n : Nat} {c tc : YamlContext} (hp : KeyPair c tc)
    {s stop : SurfPos} {ev : List Event} (h : TCNsProperties n c s stop ev) :
    TCNsProperties 0 tc s stop ev ∨ SepResidue s stop := by
  cases h with
  | tagFirst _ mid _ et er tag opt =>
    cases opt with
    | none => exact Or.inl (.tagFirst _ _ _ _ _ tag (.none _))
    | some _ _ _ tail =>
      cases tail with
      | mk _ after _ es ea sep anchor =>
        rcases sep_toKey hp sep.1 with hs | hr
        · have he : es = [] := sep.2
          subst es
          exact Or.inl (.tagFirst _ _ _ _ _ tag
            (.some _ _ _ (.mk _ _ _ [] _ ⟨hs, rfl⟩ anchor)))
        · exact Or.inr (breakOrEnd_extend_right (scNsAnchorProperty_suffix anchor.1)
            (breakOrEnd_extend_left (scNsTagProperty_suffix tag.1) hr))
  | anchorFirst _ mid _ ea er anchor opt =>
    cases opt with
    | none => exact Or.inl (.anchorFirst _ _ _ _ _ anchor (.none _))
    | some _ _ _ tail =>
      cases tail with
      | mk _ after _ es et sep tag =>
        rcases sep_toKey hp sep.1 with hs | hr
        · have he : es = [] := sep.2
          subst es
          exact Or.inl (.anchorFirst _ _ _ _ _ anchor
            (.some _ _ _ (.mk _ _ _ [] _ ⟨hs, rfl⟩ tag)))
        · exact Or.inr (breakOrEnd_extend_right (scNsTagProperty_suffix tag.1)
            (breakOrEnd_extend_left (scNsAnchorProperty_suffix anchor.1) hr))

mutual

lemma flowNode_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TFlowNode n c s s' ev) (hp : KeyPair c tc) :
    TFlowNode 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .alias _ _ _ _ _ ha =>
    exact Or.inl (TFlowNode.alias 0 tc _ _ _ ha)
  | .content _ _ _ _ _ hc =>
    rcases flowContent_toKey hc hp with hc2 | hres
    · exact Or.inl (TFlowNode.content 0 tc _ _ _ hc2)
    · exact Or.inr hres
  | .propsContent _ _ _ _ _ _ _ _ hprops hsep hc =>
    have qprops := tprops_suffix hprops
    have qsep := sSeparate_suffix hsep
    have qc := tFlowContent_suffix hc
    rcases props_toKey hp hprops with hprops2 | hres
    · rcases sep_toKey hp hsep with hsep2 | hres
      · rcases flowContent_toKey hc hp with hc2 | hres
        · exact Or.inl (TFlowNode.propsContent 0 tc _ _ _ _ _ _ hprops2 hsep2 hc2)
        · exact Or.inr (sepResidue_widen (qsep.trans qprops) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen qprops qc hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qc.trans qsep) hres)
  | .propsEmpty _ _ _ _ _ hprops =>
    rcases props_toKey hp hprops with hprops2 | hres
    · exact Or.inl (TFlowNode.propsEmpty 0 tc _ _ _ hprops2)
    · exact Or.inr hres
termination_by structural h

/-- `[161] c-flow-json-content` re-reads: the four bracket forms and the
    three scalar styles. -/
lemma flowContent_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TFlowContent n c s s' ev) (hp : KeyPair c tc) :
    TFlowContent 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .plain _ _ _ _ hpl =>
    rcases plain_toKey hp hpl with hpl2 | hres
    · exact Or.inl (TFlowContent.plain 0 tc _ _ hpl2)
    · exact Or.inr (Or.inl (plainResidue_break hres))
  | .flowSeq _ _ _ _ _ hfs =>
    rcases flowSequence_toKey hfs hp with hfs2 | hres
    · exact Or.inl (TFlowContent.flowSeq 0 tc _ _ _ hfs2)
    · exact Or.inr hres
  | .flowMap _ _ _ _ _ hfm =>
    rcases flowMapping_toKey hfm hp with hfm2 | hres
    · exact Or.inl (TFlowContent.flowMap 0 tc _ _ _ hfm2)
    · exact Or.inr hres
  | .singleQ _ _ _ _ hsq =>
    rcases singleQuoted_toKey hp hsq with hsq2 | hres
    · exact Or.inl (TFlowContent.singleQ 0 tc _ _ hsq2)
    · exact Or.inr (Or.inl (singleResidue_break hres))
  | .doubleQ _ _ _ _ hdq =>
    rcases doubleQuoted_toKey hp hdq with hdq2 | hres
    · exact Or.inl (TFlowContent.doubleQ 0 tc _ _ hdq2)
    · exact Or.inr (Or.inl (doubleResidue_break hres))
termination_by structural h

/-- `[137] c-flow-sequence` re-reads; its entries convert at
    `inFlowCtx tc`, its brackets at `tc`. -/
lemma scFlowJsonContent_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TCFlowJsonContent n c s s' ev) (hp : KeyPair c tc) :
    TCFlowJsonContent 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .flowSeq _ _ _ _ _ hfs =>
    rcases flowSequence_toKey hfs hp with hfs2 | hres
    · exact Or.inl (TCFlowJsonContent.flowSeq 0 tc _ _ _ hfs2)
    · exact Or.inr hres
  | .flowMap _ _ _ _ _ hfm =>
    rcases flowMapping_toKey hfm hp with hfm2 | hres
    · exact Or.inl (TCFlowJsonContent.flowMap 0 tc _ _ _ hfm2)
    · exact Or.inr hres
  | .singleQ _ _ _ _ hsq =>
    rcases singleQuoted_toKey hp hsq with hsq2 | hres
    · exact Or.inl (TCFlowJsonContent.singleQ 0 tc _ _ hsq2)
    · exact Or.inr (Or.inl (singleResidue_break hres))
  | .doubleQ _ _ _ _ hdq =>
    rcases doubleQuoted_toKey hp hdq with hdq2 | hres
    · exact Or.inl (TCFlowJsonContent.doubleQ 0 tc _ _ hdq2)
    · exact Or.inr (Or.inl (doubleResidue_break hres))
termination_by structural h

lemma scFlowJsonNode_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TCFlowJsonNode n c s s' ev) (hp : KeyPair c tc) :
    TCFlowJsonNode 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .content _ _ _ _ _ hc =>
    rcases scFlowJsonContent_toKey hc hp with hc2 | hres
    · exact Or.inl (TCFlowJsonNode.content 0 tc _ _ _ hc2)
    · exact Or.inr hres
  | .propsContent _ _ _ _ _ _ _ _ hprops hsep hc =>
    have qprops := tprops_suffix hprops
    have qsep := sSeparate_suffix hsep
    have qc := tCFlowJsonContent_suffix hc
    rcases props_toKey hp hprops with hprops2 | hres
    · rcases sep_toKey hp hsep with hsep2 | hres
      · rcases scFlowJsonContent_toKey hc hp with hc2 | hres
        · exact Or.inl (TCFlowJsonNode.propsContent 0 tc _ _ _ _ _ _ hprops2 hsep2 hc2)
        · exact Or.inr (sepResidue_widen (qsep.trans qprops) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen qprops qc hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qc.trans qsep) hres)
termination_by structural h

lemma flowSequence_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TFlowSequence n c s s' ev) (hp : KeyPair c tc) :
    TFlowSequence 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .empty _ _ _ _ _ _ hl1 hsep hl2 =>
    have ql1 := glit_suffix hl1
    have ql2 := glit_suffix hl2
    rcases sepOpt_toKey hp hsep with hsep2 | hres
    · exact Or.inl (TFlowSequence.empty 0 tc _ _ _ _ hl1 hsep2 hl2)
    · exact Or.inr (sepResidue_widen ql1 ql2 hres)
  | .nonempty _ _ _ _ _ _ _ _ hl1 hsep hent hl2 =>
    have ql1 := glit_suffix hl1
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    have qent := tFlowSeqEntries_suffix hent
    have ql2 := glit_suffix hl2
    rcases sepOpt_toKey hp hsep with hsep2 | hres
    · rcases flowSeqEntries_toKey hent hp.inFlow with hent2 | hres
      · exact Or.inl (TFlowSequence.nonempty 0 tc _ _ _ _ _ _ hl1 hsep2 hent2 hl2)
      · exact Or.inr (sepResidue_widen (qsep.trans ql1) ql2 hres)
    · exact Or.inr (sepResidue_widen ql1 (ql2.trans qent) hres)
termination_by structural h

/-- `[138] ns-s-flow-seq-entries` re-reads — the comma-separated run. -/
lemma flowSeqEntries_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TFlowSeqEntries n c s s' ev) (hp : KeyPair c tc) :
    TFlowSeqEntries 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .single _ _ _ _ _ _ hent hsep =>
    have qent := tFlowSeqEntry_suffix hent
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    rcases flowSeqEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep with hsep2 | hres
      · exact Or.inl (TFlowSeqEntries.single 0 tc _ _ _ _ hent2 hsep2)
      · exact Or.inr (sepResidue_widen qent (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) qsep hres)
  | .consMore _ _ _ _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 hrest =>
    have qent := tFlowSeqEntry_suffix hent
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcomma := glit_suffix hcomma
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qrest := tFlowSeqEntries_suffix hrest
    rcases flowSeqEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases flowSeqEntries_toKey hrest hp with hrest2 | hres
          · exact Or.inl (TFlowSeqEntries.consMore 0 tc _ _ _ _ _ _ _ _ hent2 hsep1b hcomma hsep2b hrest2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcomma.trans (qsep1.trans qent))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcomma.trans (qsep1.trans qent)) qrest hres)
      · exact Or.inr (sepResidue_widen qent (qrest.trans (qsep2.trans qcomma)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qrest.trans (qsep2.trans (qcomma.trans qsep1))) hres)
  | .consEnd _ _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 =>
    have qent := tFlowSeqEntry_suffix hent
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcomma := glit_suffix hcomma
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    rcases flowSeqEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · exact Or.inl (TFlowSeqEntries.consEnd 0 tc _ _ _ _ _ _ hent2 hsep1b hcomma hsep2b)
        · exact Or.inr (sepResidue_widen (qcomma.trans (qsep1.trans qent)) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen qent (qsep2.trans qcomma) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qsep2.trans (qcomma.trans qsep1)) hres)
termination_by structural h

/-- `[139] ns-flow-seq-entry` re-reads: a node, or a single pair in
    any of its ten written forms. -/
lemma flowSeqEntry_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TFlowSeqEntry n c s s' ev) (hp : KeyPair c tc) :
    TFlowSeqEntry 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .node _ _ _ _ _ hn =>
    rcases flowNode_toKey hn hp with hn2 | hres
    · exact Or.inl (TFlowSeqEntry.node 0 tc _ _ _ hn2)
    · exact Or.inr hres
  | .pairValue _ _ _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv =>
    have qk := tFlowNode_suffix hk
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := sSeparate_suffix hsep2
    have qv := tFlowNode_suffix hv
    rcases flowNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sep_toKey hp hsep2 with hsep2b | hres
        · rcases flowNode_toKey hv hp with hv2 | hres
          · exact Or.inl (TFlowSeqEntry.pairValue 0 tc _ _ _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qk))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qk)) qv hres)
      · exact Or.inr (sepResidue_widen qk (qv.trans (qsep2.trans qcolon)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qv.trans (qsep2.trans (qcolon.trans qsep1))) hres)
  | .pairEmpty _ _ _ _ _ _ _ hk hsep hcolon =>
    have qk := tFlowNode_suffix hk
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    have qcolon := glit_suffix hcolon
    rcases flowNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep with hsep2 | hres
      · exact Or.inl (TFlowSeqEntry.pairEmpty 0 tc _ _ _ _ _ hk2 hsep2 hcolon)
      · exact Or.inr (sepResidue_widen qk qcolon hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qcolon.trans qsep) hres)
  | .pairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv =>
    have qk := tCFlowJsonNode_suffix hk
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qv := tFlowNode_suffix hv
    rcases scFlowJsonNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases flowNode_toKey hv hp with hv2 | hres
          · exact Or.inl (TFlowSeqEntry.pairJsonAdjacentValue 0 tc _ _ _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qk))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qk)) qv hres)
      · exact Or.inr (sepResidue_widen qk (qv.trans (qsep2.trans qcolon)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qv.trans (qsep2.trans (qcolon.trans qsep1))) hres)
  | .explicitPairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := tCFlowJsonNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    have qsep3 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep3
    have qv := tFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases scFlowJsonNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases sepOpt_toKey hp hsep3 with hsep3b | hres
          · rcases flowNode_toKey hv hp with hv2 | hres
            · exact Or.inl (TFlowSeqEntry.explicitPairJsonAdjacentValue 0 tc _ _ _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
            · exact Or.inr (sepResidue_widen (qsep3.trans (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq))))) (List.suffix_refl _) hres)
          · exact Or.inr (sepResidue_widen (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq)))) qv hres)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) (qv.trans (qsep3.trans qcolon)) hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qv.trans (qsep3.trans (qcolon.trans qsep2))) hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep3.trans (qcolon.trans (qsep2.trans qk)))) hres)
  | .explicitPairValue _ _ _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := tFlowNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    have qsep3 := sSeparate_suffix hsep3
    have qv := tFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases sep_toKey hp hsep3 with hsep3b | hres
          · rcases flowNode_toKey hv hp with hv2 | hres
            · exact Or.inl (TFlowSeqEntry.explicitPairValue 0 tc _ _ _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
            · exact Or.inr (sepResidue_widen (qsep3.trans (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq))))) (List.suffix_refl _) hres)
          · exact Or.inr (sepResidue_widen (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq)))) qv hres)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) (qv.trans (qsep3.trans qcolon)) hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qv.trans (qsep3.trans (qcolon.trans qsep2))) hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep3.trans (qcolon.trans (qsep2.trans qk)))) hres)
  | .explicitPairEmpty _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := tFlowNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · exact Or.inl (TFlowSeqEntry.explicitPairEmpty 0 tc _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) qcolon hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qcolon.trans qsep2) hres)
    · exact Or.inr (sepResidue_widen qq (qcolon.trans (qsep2.trans qk)) hres)
  | .explicitPairKeyOnly _ _ _ _ _ _ _ hq hsep hk =>
    have qq := glit_suffix hq
    have qsep := sSeparate_suffix hsep
    have qk := tFlowNode_suffix hk
    rcases sep_toKey hp hsep with hsep2 | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · exact Or.inl (TFlowSeqEntry.explicitPairKeyOnly 0 tc _ _ _ _ _ hq hsep2 hk2)
      · exact Or.inr (sepResidue_widen (qsep.trans qq) (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen qq qk hres)
  | .explicitPairEmptyNodes _ _ _ _ _ hq hsep =>
    have qq := glit_suffix hq
    rcases sep_toKey hp hsep with hsep2 | hres
    · exact Or.inl (TFlowSeqEntry.explicitPairEmptyNodes 0 tc _ _ _ hq hsep2)
    · exact Or.inr (sepResidue_widen qq (List.suffix_refl _) hres)
  | .emptyKeyValue _ _ _ _ _ _ _ hcolon hsep hv =>
    have qcolon := glit_suffix hcolon
    have qsep := sSeparate_suffix hsep
    have qv := tFlowNode_suffix hv
    rcases sep_toKey hp hsep with hsep2 | hres
    · rcases flowNode_toKey hv hp with hv2 | hres
      · exact Or.inl (TFlowSeqEntry.emptyKeyValue 0 tc _ _ _ _ _ hcolon hsep2 hv2)
      · exact Or.inr (sepResidue_widen (qsep.trans qcolon) (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen qcolon qv hres)
  | .emptyKeyEmpty _ _ _ _ hcolon =>
    exact Or.inl (TFlowSeqEntry.emptyKeyEmpty 0 tc _ _ hcolon)
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ _ hq hsep1 hcolon hsep2 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := sSeparate_suffix hsep2
    have qv := tFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases sep_toKey hp hsep2 with hsep2b | hres
      · rcases flowNode_toKey hv hp with hv2 | hres
        · exact Or.inl (TFlowSeqEntry.explicitEmptyKeyValue 0 tc _ _ _ _ _ _ _ hq hsep1b hcolon hsep2b hv2)
        · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qq))) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qq)) qv hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep2.trans qcolon)) hres)
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ hq hsep hcolon =>
    have qq := glit_suffix hq
    have qcolon := glit_suffix hcolon
    rcases sep_toKey hp hsep with hsep2 | hres
    · exact Or.inl (TFlowSeqEntry.explicitEmptyKeyEmpty 0 tc _ _ _ _ hq hsep2 hcolon)
    · exact Or.inr (sepResidue_widen qq qcolon hres)
termination_by structural h

/-- `[140] c-flow-mapping` re-reads; the same split as the sequence. -/
lemma flowMapping_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TFlowMapping n c s s' ev) (hp : KeyPair c tc) :
    TFlowMapping 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .empty _ _ _ _ _ _ hl1 hsep hl2 =>
    have ql1 := glit_suffix hl1
    have ql2 := glit_suffix hl2
    rcases sepOpt_toKey hp hsep with hsep2 | hres
    · exact Or.inl (TFlowMapping.empty 0 tc _ _ _ _ hl1 hsep2 hl2)
    · exact Or.inr (sepResidue_widen ql1 ql2 hres)
  | .nonempty _ _ _ _ _ _ _ _ hl1 hsep hent hl2 =>
    have ql1 := glit_suffix hl1
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    have qent := tFlowMapEntries_suffix hent
    have ql2 := glit_suffix hl2
    rcases sepOpt_toKey hp hsep with hsep2 | hres
    · rcases flowMapEntries_toKey hent hp.inFlow with hent2 | hres
      · exact Or.inl (TFlowMapping.nonempty 0 tc _ _ _ _ _ _ hl1 hsep2 hent2 hl2)
      · exact Or.inr (sepResidue_widen (qsep.trans ql1) ql2 hres)
    · exact Or.inr (sepResidue_widen ql1 (ql2.trans qent) hres)
termination_by structural h

/-- `[141] ns-s-flow-map-entries` re-reads — the comma-separated run. -/
lemma flowMapEntries_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TFlowMapEntries n c s s' ev) (hp : KeyPair c tc) :
    TFlowMapEntries 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .single _ _ _ _ _ _ hent hsep =>
    have qent := tFlowMapEntry_suffix hent
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    rcases flowMapEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep with hsep2 | hres
      · exact Or.inl (TFlowMapEntries.single 0 tc _ _ _ _ hent2 hsep2)
      · exact Or.inr (sepResidue_widen qent (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) qsep hres)
  | .consMore _ _ _ _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 hrest =>
    have qent := tFlowMapEntry_suffix hent
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcomma := glit_suffix hcomma
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qrest := tFlowMapEntries_suffix hrest
    rcases flowMapEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases flowMapEntries_toKey hrest hp with hrest2 | hres
          · exact Or.inl (TFlowMapEntries.consMore 0 tc _ _ _ _ _ _ _ _ hent2 hsep1b hcomma hsep2b hrest2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcomma.trans (qsep1.trans qent))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcomma.trans (qsep1.trans qent)) qrest hres)
      · exact Or.inr (sepResidue_widen qent (qrest.trans (qsep2.trans qcomma)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qrest.trans (qsep2.trans (qcomma.trans qsep1))) hres)
  | .consEnd _ _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 =>
    have qent := tFlowMapEntry_suffix hent
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcomma := glit_suffix hcomma
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    rcases flowMapEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · exact Or.inl (TFlowMapEntries.consEnd 0 tc _ _ _ _ _ _ hent2 hsep1b hcomma hsep2b)
        · exact Or.inr (sepResidue_widen (qcomma.trans (qsep1.trans qent)) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen qent (qsep2.trans qcomma) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qsep2.trans (qcomma.trans qsep1)) hres)
termination_by structural h

/-- `[142] ns-flow-map-entry` re-reads: eleven written forms of one
    key/value pair. -/
lemma flowMapEntry_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos} {ev : List Event}
    (h : TFlowMapEntry n c s s' ev) (hp : KeyPair c tc) :
    TFlowMapEntry 0 tc s s' ev ∨ SepResidue s s' := by
  match h with
  | .explicitValue _ _ _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := tFlowNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    have qsep3 := sSeparate_suffix hsep3
    have qv := tFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases sep_toKey hp hsep3 with hsep3b | hres
          · rcases flowNode_toKey hv hp with hv2 | hres
            · exact Or.inl (TFlowMapEntry.explicitValue 0 tc _ _ _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
            · exact Or.inr (sepResidue_widen (qsep3.trans (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq))))) (List.suffix_refl _) hres)
          · exact Or.inr (sepResidue_widen (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq)))) qv hres)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) (qv.trans (qsep3.trans qcolon)) hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qv.trans (qsep3.trans (qcolon.trans qsep2))) hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep3.trans (qcolon.trans (qsep2.trans qk)))) hres)
  | .explicitEmpty _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := tFlowNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · exact Or.inl (TFlowMapEntry.explicitEmpty 0 tc _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) qcolon hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qcolon.trans qsep2) hres)
    · exact Or.inr (sepResidue_widen qq (qcolon.trans (qsep2.trans qk)) hres)
  | .explicitKeyOnly _ _ _ _ _ _ _ hq hsep hk =>
    have qq := glit_suffix hq
    have qsep := sSeparate_suffix hsep
    have qk := tFlowNode_suffix hk
    rcases sep_toKey hp hsep with hsep2 | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · exact Or.inl (TFlowMapEntry.explicitKeyOnly 0 tc _ _ _ _ _ hq hsep2 hk2)
      · exact Or.inr (sepResidue_widen (qsep.trans qq) (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen qq qk hres)
  | .implicitValue _ _ _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv =>
    have qk := tFlowNode_suffix hk
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := sSeparate_suffix hsep2
    have qv := tFlowNode_suffix hv
    rcases flowNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sep_toKey hp hsep2 with hsep2b | hres
        · rcases flowNode_toKey hv hp with hv2 | hres
          · exact Or.inl (TFlowMapEntry.implicitValue 0 tc _ _ _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qk))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qk)) qv hres)
      · exact Or.inr (sepResidue_widen qk (qv.trans (qsep2.trans qcolon)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qv.trans (qsep2.trans (qcolon.trans qsep1))) hres)
  | .implicitEmpty _ _ _ _ _ _ _ hk hsep hcolon =>
    have qk := tFlowNode_suffix hk
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    have qcolon := glit_suffix hcolon
    rcases flowNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep with hsep2 | hres
      · exact Or.inl (TFlowMapEntry.implicitEmpty 0 tc _ _ _ _ _ hk2 hsep2 hcolon)
      · exact Or.inr (sepResidue_widen qk qcolon hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qcolon.trans qsep) hres)
  | .jsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv =>
    have qk := tCFlowJsonNode_suffix hk
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qv := tFlowNode_suffix hv
    rcases scFlowJsonNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases flowNode_toKey hv hp with hv2 | hres
          · exact Or.inl (TFlowMapEntry.jsonKeyAdjacentValue 0 tc _ _ _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qk))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qk)) qv hres)
      · exact Or.inr (sepResidue_widen qk (qv.trans (qsep2.trans qcolon)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qv.trans (qsep2.trans (qcolon.trans qsep1))) hres)
  | .explicitJsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := tCFlowJsonNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    have qsep3 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep3
    have qv := tFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases scFlowJsonNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases sepOpt_toKey hp hsep3 with hsep3b | hres
          · rcases flowNode_toKey hv hp with hv2 | hres
            · exact Or.inl (TFlowMapEntry.explicitJsonKeyAdjacentValue 0 tc _ _ _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
            · exact Or.inr (sepResidue_widen (qsep3.trans (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq))))) (List.suffix_refl _) hres)
          · exact Or.inr (sepResidue_widen (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq)))) qv hres)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) (qv.trans (qsep3.trans qcolon)) hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qv.trans (qsep3.trans (qcolon.trans qsep2))) hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep3.trans (qcolon.trans (qsep2.trans qk)))) hres)
  | .bareKey _ _ _ _ _ hk =>
    rcases flowNode_toKey hk hp with hk2 | hres
    · exact Or.inl (TFlowMapEntry.bareKey 0 tc _ _ _ hk2)
    · exact Or.inr hres
  | .emptyKeyValue _ _ _ _ _ _ _ hcolon hsep hv =>
    have qcolon := glit_suffix hcolon
    have qsep := sSeparate_suffix hsep
    have qv := tFlowNode_suffix hv
    rcases sep_toKey hp hsep with hsep2 | hres
    · rcases flowNode_toKey hv hp with hv2 | hres
      · exact Or.inl (TFlowMapEntry.emptyKeyValue 0 tc _ _ _ _ _ hcolon hsep2 hv2)
      · exact Or.inr (sepResidue_widen (qsep.trans qcolon) (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen qcolon qv hres)
  | .emptyKeyEmpty _ _ _ _ hcolon =>
    exact Or.inl (TFlowMapEntry.emptyKeyEmpty 0 tc _ _ hcolon)
  | .explicitEmptyNodes _ _ _ _ _ hq hsep =>
    have qq := glit_suffix hq
    rcases sep_toKey hp hsep with hsep2 | hres
    · exact Or.inl (TFlowMapEntry.explicitEmptyNodes 0 tc _ _ _ hq hsep2)
    · exact Or.inr (sepResidue_widen qq (List.suffix_refl _) hres)
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ _ hq hsep1 hcolon hsep2 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := sSeparate_suffix hsep2
    have qv := tFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases sep_toKey hp hsep2 with hsep2b | hres
      · rcases flowNode_toKey hv hp with hv2 | hres
        · exact Or.inl (TFlowMapEntry.explicitEmptyKeyValue 0 tc _ _ _ _ _ _ _ hq hsep1b hcolon hsep2b hv2)
        · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qq))) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qq)) qv hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep2.trans qcolon)) hres)
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ hq hsep hcolon =>
    have qq := glit_suffix hq
    have qcolon := glit_suffix hcolon
    rcases sep_toKey hp hsep with hsep2 | hres
    · exact Or.inl (TFlowMapEntry.explicitEmptyKeyEmpty 0 tc _ _ _ _ hq hsep2 hcolon)
    · exact Or.inr (sepResidue_widen qq qcolon hres)
termination_by structural h

end

end L4YAML.Proofs.Serialization.TraceOf.KeyLift
end Blanket
