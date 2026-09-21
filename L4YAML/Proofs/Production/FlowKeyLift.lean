/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Surface.Node
import L4YAML.Spec.CharPredicates
import L4YAML.Proofs.Foundation.SurfaceSpan

/-! # The closed flow node re-read as `[154]`'s key (DOCS item 56)

    A completed depth-0 flow collection followed by a same-line `:` is
    `[193] c-s-implicit-json-key`'s node — `c-flow-json-node(0, block-key)`.
    The collection was built at the frame's index in the `flow-out`/`flow-in`
    contexts; the KEY contexts read the same characters with two changes:
    the index drops to 0 and every interior separation must be
    `s-separate-in-line` (the key is single-line — which the scanner's
    §7.4 implicit-key checks enforce on everything that reaches a `:`).

    This file is the conversion family: one lemma per type of the flow
    grammar's mutual block, each `… → (converted) ∨ <residue>`, the residue
    taken on a multi-line interior (a `.commented` separation or a multi-line
    scalar body) — inputs the scanner refuses as keys anyway.

    **Corrected at item 228**, in two places.  The residue was written `True`
    everywhere, which made every one of these lemmas a statement that
    `Or.inr trivial` proves; §0 gives the four leaf residues their own names
    and five of the ten now carry one.  And "taken exactly on a multi-line
    interior" was imprecise for the separation: `[70]`'s comment-delimited arm
    admits a derivation that crosses no line at all (`[79] s-l-comments` has a
    comment-free arm at column 0 and `[63] s-indent(0)` consumes nothing), so
    `SepResidue` and `[80] s-separate-in-line` hold at the same zero-width
    span.  The remaining five keep `True` because their residue arises at an
    INTERIOR span and the conclusion is about the OUTER one; carrying it out
    needs a suffix lemma over this mutual block, which item 229 built
    (`L4YAML/Proofs/Foundation/SurfaceSpan.lean`) and which §4 uses to settle
    the four leaf residues — narrowing the five is the operation it does not
    do, because each needs its own motive strengthened, not a new fact.

    The context pairing is tracked as `KeyPair c tc`: the top node converts
    `(flowOut → blockKey)`, interiors `(flowIn → flowKey)`, and `inFlowCtx`
    maps the first onto the second — `isNsPlainSafe` is EQUAL on each pair,
    which is what the plain leaves transport. -/

set_option autoImplicit false

namespace L4YAML.Proofs.FlowKeyLift

open L4YAML.Surface
open L4YAML.Proofs.SurfaceSpan

/-- The two source→target context pairings the key re-reading makes. -/
def KeyPair (c tc : L4YAML.YamlContext) : Prop :=
  (c = .flowOut ∧ tc = .blockKey) ∨ (c = .flowIn ∧ tc = .flowKey)

lemma KeyPair.inFlow {c tc : L4YAML.YamlContext} (h : KeyPair c tc) :
    KeyPair (inFlowCtx c) (inFlowCtx tc) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact Or.inr ⟨rfl, rfl⟩

lemma KeyPair.tc_key {c tc : L4YAML.YamlContext} (h : KeyPair c tc) :
    tc = .blockKey ∨ tc = .flowKey := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `ns-plain-safe` is EQUAL on each pairing. -/
lemma KeyPair.safe {c tc : L4YAML.YamlContext} (h : KeyPair c tc) {ch : Char}
    (hs : isNsPlainSafe c ch) : isNsPlainSafe tc ch := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hs

/-! ## §0 What the conversion declines ON (DOCS item 228)

Each conversion below used to end in `… ∨ True`, and `Or.inr trivial` proves
that whatever is on the left: the statement was not a theorem about the
conversion at all.  These are the residues those `True`s stood for, read off
the arm each proof actually takes.  They are `def`s so the residue carries its
own docstring and so a census can select on it.

They are NOT interchangeable, and that is the finding item 228 recorded and
item 229 proved: three of the four consume a line break by construction, so a
consumer holding a single-line key can refute them — which is the entire worth
of a narrowing.  `SepResidue` cannot be refuted that way, and §4 gives the
reason rather than the observation: its span can be EMPTY
(`sepResidue_span_can_be_empty`). -/

/-- **The residue a separation leaves**: `[70] s-separate-lines(n)`'s
    comment-delimited arm, for which `[69]`'s key contexts have no production. -/
def SepResidue (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ s₁, SSLComments s s₁ ∧ SFlowLinePrefix n s₁ s'

/-- **The residue a plain scalar leaves**: at least one
    `[134] s-ns-plain-next-line(n,c)` past `[133] ns-plain-one-line(c)`.  Every
    one of them opens with `[28] b-break`. -/
def PlainResidue (n : Nat) (c : L4YAML.YamlContext) (s s' : SurfPos) : Prop :=
  ∃ s₁, SNsPlainOneLine c s s₁ ∧ GPlus (SSNsPlainNextLine n c) s₁ s'

/-- **The residue a double-quoted scalar leaves**: `[116]
    nb-double-multi-line(n)`'s `multi` arm, inside the quotes.  `[113]
    s-double-break(n)` is an escaped break or a folded one; either consumes
    one. -/
def DoubleResidue (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ s₁ s₂ a b, GLit '"' s s₁ ∧ SNbDoubleOneLine s₁ a ∧ SSDoubleBreak n a b ∧
    SNbDoubleMultiLine n b s₂ ∧ GLit '"' s₂ s'

/-- **The residue a single-quoted scalar leaves**: `[125]
    nb-single-multi-line(n)`'s `multi` arm, inside the quotes, whose second
    component is `[28] b-break` itself. -/
def SingleResidue (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ s₁ s₂ a b cc d, GLit '\'' s s₁ ∧ SNbSingleOneLine s₁ a ∧ SBBreak a b ∧
    GStar (SLEmpty n .flowIn) b cc ∧ SFlowLinePrefix n cc d ∧
    SNbSingleMultiLine n d s₂ ∧ GLit '\'' s₂ s'

/-! ## §1 Scalar leaves -/

lemma plainFirst_toKey {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlainFirst c s s') : SNsPlainFirst tc s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hNotInd =>
    exact SNsPlainFirst.nonIndicator tc ch rest col (hp.safe hSafe) hNotInd
  | dashSafe next rest col hSafe =>
    exact SNsPlainFirst.dashSafe tc next rest col (hp.safe hSafe)
  | colonSafe next rest col hSafe =>
    exact SNsPlainFirst.colonSafe tc next rest col (hp.safe hSafe)
  | questionSafe next rest col hSafe =>
    exact SNsPlainFirst.questionSafe tc next rest col (hp.safe hSafe)

lemma plainChar_toKey {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlainChar c s s') : SNsPlainChar tc s s' := by
  cases h with
  | safe ch rest col hSafe hNC hNH =>
    exact SNsPlainChar.safe tc ch rest col (hp.safe hSafe) hNC hNH
  | colonSafe prev next rest col hSafe =>
    exact SNsPlainChar.colonSafe tc prev next rest col (hp.safe hSafe)
  | hashAfterNs rest col hC => exact SNsPlainChar.hashAfterNs tc rest col hC

lemma plainEntry_toKey {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNbNsPlainInLineEntry c s s') :
    SNbNsPlainInLineEntry tc s s' := by
  cases h with
  | mk s₁ _ hws hch =>
    exact SNbNsPlainInLineEntry.mk tc _ s₁ _ hws (plainChar_toKey hp hch)

lemma plainOneLine_toKey {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlainOneLine c s s') : SNsPlainOneLine tc s s' := by
  cases h with
  | mk s₁ _ hfirst hentries =>
    refine SNsPlainOneLine.mk tc _ s₁ _ (plainFirst_toKey hp hfirst) ?_
    clear hfirst
    induction hentries with
    | nil => exact GStar.nil _
    | cons a b cc hx _ ih => exact GStar.cons a b cc (plainEntry_toKey hp hx) ih

/-- A plain scalar re-reads at the key context when it is single-line. -/
lemma plain_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlain n c s s') :
    SNsPlain 0 tc s s' ∨ PlainResidue n c s s' := by
  have h' : SNsPlainMultiLine n c s s' := by
    rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact h
  cases h' with
  | mk _ _ hone hnext =>
    cases hnext with
    | nil =>
      have hone' := plainOneLine_toKey hp hone
      rcases hp.tc_key with rfl | rfl <;> exact Or.inl hone'
    | cons _ _ _ hx hrest => exact Or.inr ⟨_, hone, GPlus.mk _ _ _ hx hrest⟩

/-- A double-quoted scalar re-reads at the key context when its body is
    single-line (the one-line body is context- and index-free). -/
lemma doubleQuoted_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCDoubleQuoted n c s s') :
    SCDoubleQuoted 0 tc s s' ∨ DoubleResidue n s s' := by
  cases h with
  | mk s₁ s₂ _ hq1 hbody hq2 =>
    have hbody' : SNbDoubleMultiLine n s₁ s₂ := by
      rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hbody
    cases hbody' with
    | single _ _ hl =>
      have hkey : SNbDoubleText 0 tc s₁ s₂ := by
        rcases hp.tc_key with rfl | rfl <;> exact hl
      exact Or.inl (SCDoubleQuoted.mk 0 tc _ _ _ _ hq1 hkey hq2)
    | multi _ a b _ _ hone hbrk hrest =>
      exact Or.inr ⟨_, _, a, b, hq1, hone, hbrk, hrest, hq2⟩

/-- The single-quoted twin. -/
lemma singleQuoted_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCSingleQuoted n c s s') :
    SCSingleQuoted 0 tc s s' ∨ SingleResidue n s s' := by
  cases h with
  | mk s₁ s₂ _ hq1 hbody hq2 =>
    have hbody' : SNbSingleMultiLine n s₁ s₂ := by
      rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hbody
    cases hbody' with
    | single _ _ hl =>
      have hkey : SNbSingleText 0 tc s₁ s₂ := by
        rcases hp.tc_key with rfl | rfl <;> exact hl
      exact Or.inl (SCSingleQuoted.mk 0 tc _ _ _ _ hq1 hkey hq2)
    | multi _ a b cc d _ hone hbrk hempty hpre hrest =>
      exact Or.inr ⟨_, _, a, b, cc, d, hq1, hone, hbrk, hempty, hpre, hrest, hq2⟩

/-! ## §2 Separations and properties -/

/-- A separation re-reads at the key context when it is inline. -/
lemma sep_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SSeparate n c s s') :
    SSeparate 0 tc s s' ∨ SepResidue n s s' := by
  have h' : SSeparateLines n s s' := by
    rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact h
  cases h' with
  | inline _ sil =>
    refine Or.inl ?_
    rcases hp.tc_key with rfl | rfl <;> exact sil
  | commented _ _ _ _ => exact Or.inr ⟨_, ‹SSLComments _ _›, ‹SFlowLinePrefix _ _ _›⟩

lemma sepOpt_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : GOpt (SSeparate n c) s s') :
    GOpt (SSeparate 0 tc) s s' ∨ SepResidue n s s' := by
  cases h with
  | none => exact Or.inl (GOpt.none _)
  | some _ hx =>
    rcases sep_toKey hp hx with hx' | hr
    · exact Or.inl (GOpt.some _ _ hx')
    · exact Or.inr hr

/-- Properties re-read at the key context when their interior separation is
    inline (the tag/anchor tokens themselves are context-free). -/
lemma props_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCNsProperties n c s s') :
    SCNsProperties 0 tc s s' ∨ True := by
  cases h with
  | tagFirst _ _ htag hopt =>
    cases hopt with
    | none => exact Or.inl (SCNsProperties.tagFirst 0 tc _ _ _ htag (GOpt.none _))
    | some _ hseq =>
      cases hseq
      rename_i hsep hanchor
      rcases sep_toKey hp hsep with hsep' | _
      · exact Or.inl (SCNsProperties.tagFirst 0 tc _ _ _ htag
          (GOpt.some _ _ (GSeq.mk _ _ _ hsep' hanchor)))
      · exact Or.inr trivial
  | anchorFirst _ _ hanchor hopt =>
    cases hopt with
    | none => exact Or.inl (SCNsProperties.anchorFirst 0 tc _ _ _ hanchor (GOpt.none _))
    | some _ hseq =>
      cases hseq
      rename_i hsep htag
      rcases sep_toKey hp hsep with hsep' | _
      · exact Or.inl (SCNsProperties.anchorFirst 0 tc _ _ _ hanchor
          (GOpt.some _ _ (GSeq.mk _ _ _ hsep' htag)))
      · exact Or.inr trivial

/-! ## §3 The collection family

    The flow grammar is one arm of an 18-type mutual block, so the `induction`
    tactic does not apply — it refuses a mutually inductive type outright — and
    the conversion is written against the family's own recursor.

    **Corrected at item 229**: this paragraph also said the equation compiler
    does not apply, "structural recursion does not eliminate a proof of a
    mutual inductive `Prop`".  It does.  `lemma` inside `mutual` is a macro in
    this repo precisely so that it reaches `elabMutual` (`L4YAML/Init.lean`),
    and `L4YAML/Proofs/Foundation/SurfaceSpan.lean` §4 is eighteen mutually
    structural lemmas over this same family.  The recursor is still the right
    shape HERE, because the motives differ per type; it is not the only one
    available.  The ten block-side motives are `True`
    — the recursion never leaves the flow grammar — and the eight flow motives
    carry the pairing UNIVERSALLY quantified, which is what lets a collection's
    entries convert at `inFlowCtx tc` while its brackets convert at `tc`.

    Every interior piece converts or the whole conversion returns `True`.
    That `True` is the one item 228 could not replace: the residue belongs to
    an interior span and this conclusion is about the outer one, so the
    proposition that would carry it out is a statement about the CHARACTERS
    between the two.  The 18 types below have 69 constructors, and at item 228
    not one lemma related any of them to a suffix; item 229 wrote all
    eighteen, so the statement is now sayable — what it still needs is this
    recursor application's motives rebuilt around it. -/

/-- **The conversion**: a flow node re-reads at index 0 in the paired key
    context, unless some interior crossed a line. -/
lemma flowNode_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowNode n c s s') (hp : KeyPair c tc) : SFlowNode 0 tc s s' ∨ True :=
  SFlowNode.rec
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True) (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True) (motive_10 := fun _ _ _ => True)
    (motive_11 := fun _ c s s' _ => ∀ tc, KeyPair c tc → (SFlowNode 0 tc s s' ∨ True))
    (motive_12 := fun _ c s s' _ => ∀ tc, KeyPair c tc → (SFlowContent 0 tc s s' ∨ True))
    (motive_13 := fun _ c s s' _ => ∀ tc, KeyPair c tc → (SFlowSequence 0 tc s s' ∨ True))
    (motive_14 := fun _ c s s' _ => ∀ tc, KeyPair c tc → (SFlowSeqEntries 0 tc s s' ∨ True))
    (motive_15 := fun _ c s s' _ => ∀ tc, KeyPair c tc → (SFlowSeqEntry 0 tc s s' ∨ True))
    (motive_16 := fun _ c s s' _ => ∀ tc, KeyPair c tc → (SFlowMapping 0 tc s s' ∨ True))
    (motive_17 := fun _ c s s' _ => ∀ tc, KeyPair c tc → (SFlowMapEntries 0 tc s s' ∨ True))
    (motive_18 := fun _ c s s' _ => ∀ tc, KeyPair c tc → (SFlowMapEntry 0 tc s s' ∨ True))
    -- the ten block-side motives are `True`: the recursion stays in the flow grammar
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    -- SFlowNode.alias
    (by
      intro _ _ _ _ ha tc hp
      exact Or.inl (SFlowNode.alias 0 tc _ _ ha))
    -- SFlowNode.content
    (by
      intro _ _ _ _ hc ih tc hp
      rcases ih tc hp with hc2 | _
      · exact Or.inl (SFlowNode.content 0 tc _ _ hc2)
      · exact Or.inr trivial)
    -- SFlowNode.propsContent
    (by
      intro _ _ _ _ _ _ hprops hsep hc ih tc hp
      rcases props_toKey hp hprops with hprops2 | _
      · rcases sep_toKey hp hsep with hsep2 | _
        · rcases ih tc hp with hc2 | _
          · exact Or.inl (SFlowNode.propsContent 0 tc _ _ _ _ hprops2 hsep2 hc2)
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowNode.propsEmpty
    (by
      intro _ _ _ _ hprops tc hp
      rcases props_toKey hp hprops with hprops2 | _
      · exact Or.inl (SFlowNode.propsEmpty 0 tc _ _ hprops2)
      · exact Or.inr trivial)
    -- SFlowContent.plain
    (by
      intro _ _ _ _ hpl tc hp
      rcases plain_toKey hp hpl with hpl2 | _
      · exact Or.inl (SFlowContent.plain 0 tc _ _ hpl2)
      · exact Or.inr trivial)
    -- SFlowContent.flowSeq
    (by
      intro _ _ _ _ hfs ih tc hp
      rcases ih tc hp with hfs2 | _
      · exact Or.inl (SFlowContent.flowSeq 0 tc _ _ hfs2)
      · exact Or.inr trivial)
    -- SFlowContent.flowMap
    (by
      intro _ _ _ _ hfm ih tc hp
      rcases ih tc hp with hfm2 | _
      · exact Or.inl (SFlowContent.flowMap 0 tc _ _ hfm2)
      · exact Or.inr trivial)
    -- SFlowContent.singleQ
    (by
      intro _ _ _ _ hsq tc hp
      rcases singleQuoted_toKey hp hsq with hsq2 | _
      · exact Or.inl (SFlowContent.singleQ 0 tc _ _ hsq2)
      · exact Or.inr trivial)
    -- SFlowContent.doubleQ
    (by
      intro _ _ _ _ hdq tc hp
      rcases doubleQuoted_toKey hp hdq with hdq2 | _
      · exact Or.inl (SFlowContent.doubleQ 0 tc _ _ hdq2)
      · exact Or.inr trivial)
    -- SFlowSequence.empty
    (by
      intro _ _ _ _ _ _ hl1 hsep hl2 tc hp
      rcases sepOpt_toKey hp hsep with hsep2 | _
      · exact Or.inl (SFlowSequence.empty 0 tc _ _ _ _ hl1 hsep2 hl2)
      · exact Or.inr trivial)
    -- SFlowSequence.nonempty
    (by
      intro _ _ _ _ _ _ _ hl1 hsep hent hl2 ih tc hp
      rcases sepOpt_toKey hp hsep with hsep2 | _
      · rcases ih (inFlowCtx tc) hp.inFlow with hent2 | _
        · exact Or.inl (SFlowSequence.nonempty 0 tc _ _ _ _ _ hl1 hsep2 hent2 hl2)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntries.single
    (by
      intro _ _ _ _ _ hent hsep ih tc hp
      rcases ih tc hp with hent2 | _
      · rcases sepOpt_toKey hp hsep with hsep2 | _
        · exact Or.inl (SFlowSeqEntries.single 0 tc _ _ _ hent2 hsep2)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntries.consMore
    (by
      intro _ _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 hrest ih1 ih2 tc hp
      rcases ih1 tc hp with hent2 | _
      · rcases sepOpt_toKey hp hsep1 with hsep1b | _
        · rcases sepOpt_toKey hp hsep2 with hsep2b | _
          · rcases ih2 tc hp with hrest2 | _
            · exact Or.inl (SFlowSeqEntries.consMore 0 tc _ _ _ _ _ _ hent2 hsep1b hcomma hsep2b hrest2)
            · exact Or.inr trivial
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntries.consEnd
    (by
      intro _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 ih tc hp
      rcases ih tc hp with hent2 | _
      · rcases sepOpt_toKey hp hsep1 with hsep1b | _
        · rcases sepOpt_toKey hp hsep2 with hsep2b | _
          · exact Or.inl (SFlowSeqEntries.consEnd 0 tc _ _ _ _ _ hent2 hsep1b hcomma hsep2b)
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntry.node
    (by
      intro _ _ _ _ hn ih tc hp
      rcases ih tc hp with hn2 | _
      · exact Or.inl (SFlowSeqEntry.node 0 tc _ _ hn2)
      · exact Or.inr trivial)
    -- SFlowSeqEntry.pairValue
    (by
      intro _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv ih1 ih2 tc hp
      rcases ih1 tc hp with hk2 | _
      · rcases sepOpt_toKey hp hsep1 with hsep1b | _
        · rcases sep_toKey hp hsep2 with hsep2b | _
          · rcases ih2 tc hp with hv2 | _
            · exact Or.inl (SFlowSeqEntry.pairValue 0 tc _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
            · exact Or.inr trivial
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntry.pairEmpty
    (by
      intro _ _ _ _ _ _ hk hsep hcolon ih tc hp
      rcases ih tc hp with hk2 | _
      · rcases sepOpt_toKey hp hsep with hsep2 | _
        · exact Or.inl (SFlowSeqEntry.pairEmpty 0 tc _ _ _ _ hk2 hsep2 hcolon)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntry.explicitPairValue
    (by
      intro _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv ih1 ih2 tc hp
      rcases sep_toKey hp hsep1 with hsep1b | _
      · rcases ih1 tc hp with hk2 | _
        · rcases sepOpt_toKey hp hsep2 with hsep2b | _
          · rcases sep_toKey hp hsep3 with hsep3b | _
            · rcases ih2 tc hp with hv2 | _
              · exact Or.inl (SFlowSeqEntry.explicitPairValue 0 tc _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
              · exact Or.inr trivial
            · exact Or.inr trivial
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntry.explicitPairEmpty
    (by
      intro _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon ih tc hp
      rcases sep_toKey hp hsep1 with hsep1b | _
      · rcases ih tc hp with hk2 | _
        · rcases sepOpt_toKey hp hsep2 with hsep2b | _
          · exact Or.inl (SFlowSeqEntry.explicitPairEmpty 0 tc _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon)
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntry.explicitPairKeyOnly
    (by
      intro _ _ _ _ _ _ hq hsep hk ih tc hp
      rcases sep_toKey hp hsep with hsep2 | _
      · rcases ih tc hp with hk2 | _
        · exact Or.inl (SFlowSeqEntry.explicitPairKeyOnly 0 tc _ _ _ _ hq hsep2 hk2)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntry.explicitPairEmptyNodes
    (by
      intro _ _ _ _ _ hq hsep tc hp
      rcases sep_toKey hp hsep with hsep2 | _
      · exact Or.inl (SFlowSeqEntry.explicitPairEmptyNodes 0 tc _ _ _ hq hsep2)
      · exact Or.inr trivial)
    -- SFlowSeqEntry.emptyKeyValue
    (by
      intro _ _ _ _ _ _ hcolon hsep hv ih tc hp
      rcases sep_toKey hp hsep with hsep2 | _
      · rcases ih tc hp with hv2 | _
        · exact Or.inl (SFlowSeqEntry.emptyKeyValue 0 tc _ _ _ _ hcolon hsep2 hv2)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntry.emptyKeyEmpty
    (by
      intro _ _ _ _ hcolon tc hp
      exact Or.inl (SFlowSeqEntry.emptyKeyEmpty 0 tc _ _ hcolon))
    -- SFlowSeqEntry.explicitEmptyKeyValue
    (by
      intro _ _ _ _ _ _ _ _ hq hsep1 hcolon hsep2 hv ih tc hp
      rcases sep_toKey hp hsep1 with hsep1b | _
      · rcases sep_toKey hp hsep2 with hsep2b | _
        · rcases ih tc hp with hv2 | _
          · exact Or.inl (SFlowSeqEntry.explicitEmptyKeyValue 0 tc _ _ _ _ _ _ hq hsep1b hcolon hsep2b hv2)
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowSeqEntry.explicitEmptyKeyEmpty
    (by
      intro _ _ _ _ _ _ hq hsep hcolon tc hp
      rcases sep_toKey hp hsep with hsep2 | _
      · exact Or.inl (SFlowSeqEntry.explicitEmptyKeyEmpty 0 tc _ _ _ _ hq hsep2 hcolon)
      · exact Or.inr trivial)
    -- SFlowMapping.empty
    (by
      intro _ _ _ _ _ _ hl1 hsep hl2 tc hp
      rcases sepOpt_toKey hp hsep with hsep2 | _
      · exact Or.inl (SFlowMapping.empty 0 tc _ _ _ _ hl1 hsep2 hl2)
      · exact Or.inr trivial)
    -- SFlowMapping.nonempty
    (by
      intro _ _ _ _ _ _ _ hl1 hsep hent hl2 ih tc hp
      rcases sepOpt_toKey hp hsep with hsep2 | _
      · rcases ih (inFlowCtx tc) hp.inFlow with hent2 | _
        · exact Or.inl (SFlowMapping.nonempty 0 tc _ _ _ _ _ hl1 hsep2 hent2 hl2)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntries.single
    (by
      intro _ _ _ _ _ hent hsep ih tc hp
      rcases ih tc hp with hent2 | _
      · rcases sepOpt_toKey hp hsep with hsep2 | _
        · exact Or.inl (SFlowMapEntries.single 0 tc _ _ _ hent2 hsep2)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntries.consMore
    (by
      intro _ _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 hrest ih1 ih2 tc hp
      rcases ih1 tc hp with hent2 | _
      · rcases sepOpt_toKey hp hsep1 with hsep1b | _
        · rcases sepOpt_toKey hp hsep2 with hsep2b | _
          · rcases ih2 tc hp with hrest2 | _
            · exact Or.inl (SFlowMapEntries.consMore 0 tc _ _ _ _ _ _ hent2 hsep1b hcomma hsep2b hrest2)
            · exact Or.inr trivial
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntries.consEnd
    (by
      intro _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 ih tc hp
      rcases ih tc hp with hent2 | _
      · rcases sepOpt_toKey hp hsep1 with hsep1b | _
        · rcases sepOpt_toKey hp hsep2 with hsep2b | _
          · exact Or.inl (SFlowMapEntries.consEnd 0 tc _ _ _ _ _ hent2 hsep1b hcomma hsep2b)
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntry.explicitValue
    (by
      intro _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv ih1 ih2 tc hp
      rcases sep_toKey hp hsep1 with hsep1b | _
      · rcases ih1 tc hp with hk2 | _
        · rcases sepOpt_toKey hp hsep2 with hsep2b | _
          · rcases sep_toKey hp hsep3 with hsep3b | _
            · rcases ih2 tc hp with hv2 | _
              · exact Or.inl (SFlowMapEntry.explicitValue 0 tc _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
              · exact Or.inr trivial
            · exact Or.inr trivial
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntry.explicitEmpty
    (by
      intro _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon ih tc hp
      rcases sep_toKey hp hsep1 with hsep1b | _
      · rcases ih tc hp with hk2 | _
        · rcases sepOpt_toKey hp hsep2 with hsep2b | _
          · exact Or.inl (SFlowMapEntry.explicitEmpty 0 tc _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon)
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntry.explicitKeyOnly
    (by
      intro _ _ _ _ _ _ hq hsep hk ih tc hp
      rcases sep_toKey hp hsep with hsep2 | _
      · rcases ih tc hp with hk2 | _
        · exact Or.inl (SFlowMapEntry.explicitKeyOnly 0 tc _ _ _ _ hq hsep2 hk2)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntry.implicitValue
    (by
      intro _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv ih1 ih2 tc hp
      rcases ih1 tc hp with hk2 | _
      · rcases sepOpt_toKey hp hsep1 with hsep1b | _
        · rcases sep_toKey hp hsep2 with hsep2b | _
          · rcases ih2 tc hp with hv2 | _
            · exact Or.inl (SFlowMapEntry.implicitValue 0 tc _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
            · exact Or.inr trivial
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntry.implicitEmpty
    (by
      intro _ _ _ _ _ _ hk hsep hcolon ih tc hp
      rcases ih tc hp with hk2 | _
      · rcases sepOpt_toKey hp hsep with hsep2 | _
        · exact Or.inl (SFlowMapEntry.implicitEmpty 0 tc _ _ _ _ hk2 hsep2 hcolon)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntry.bareKey
    (by
      intro _ _ _ _ hk ih tc hp
      rcases ih tc hp with hk2 | _
      · exact Or.inl (SFlowMapEntry.bareKey 0 tc _ _ hk2)
      · exact Or.inr trivial)
    -- SFlowMapEntry.emptyKeyValue
    (by
      intro _ _ _ _ _ _ hcolon hsep hv ih tc hp
      rcases sep_toKey hp hsep with hsep2 | _
      · rcases ih tc hp with hv2 | _
        · exact Or.inl (SFlowMapEntry.emptyKeyValue 0 tc _ _ _ _ hcolon hsep2 hv2)
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntry.emptyKeyEmpty
    (by
      intro _ _ _ _ hcolon tc hp
      exact Or.inl (SFlowMapEntry.emptyKeyEmpty 0 tc _ _ hcolon))
    -- SFlowMapEntry.explicitEmptyNodes
    (by
      intro _ _ _ _ _ hq hsep tc hp
      rcases sep_toKey hp hsep with hsep2 | _
      · exact Or.inl (SFlowMapEntry.explicitEmptyNodes 0 tc _ _ _ hq hsep2)
      · exact Or.inr trivial)
    -- SFlowMapEntry.explicitEmptyKeyValue
    (by
      intro _ _ _ _ _ _ _ _ hq hsep1 hcolon hsep2 hv ih tc hp
      rcases sep_toKey hp hsep1 with hsep1b | _
      · rcases sep_toKey hp hsep2 with hsep2b | _
        · rcases ih tc hp with hv2 | _
          · exact Or.inl (SFlowMapEntry.explicitEmptyKeyValue 0 tc _ _ _ _ _ _ hq hsep1b hcolon hsep2b hv2)
          · exact Or.inr trivial
        · exact Or.inr trivial
      · exact Or.inr trivial)
    -- SFlowMapEntry.explicitEmptyKeyEmpty
    (by
      intro _ _ _ _ _ _ hq hsep hcolon tc hp
      rcases sep_toKey hp hsep with hsep2 | _
      · exact Or.inl (SFlowMapEntry.explicitEmptyKeyEmpty 0 tc _ _ _ _ hq hsep2 hcolon)
      · exact Or.inr trivial)
    h tc hp

/-- **The top wrapper**: a completed depth-0 flow node re-reads as `[154]`'s
    JSON key when it is single-line. -/
lemma flowNode_toBlockKey {n : Nat} {s s' : SurfPos}
    (h : SFlowNode n .flowOut s s') : SFlowNode 0 .blockKey s s' ∨ True :=
  flowNode_toKey h (Or.inl ⟨rfl, rfl⟩)

/-- The same conversion one level down, for a key that a held `[96]` run
    DECORATES (`&a [1]: b`): the properties are the head's, so what the
    collection owes is `[158]`'s content, and `[161]`'s `propsContent` arm is
    assembled at the site that holds the run. -/
lemma flowContent_toBlockKey {n : Nat} {s s' : SurfPos}
    (h : SFlowContent n .flowOut s s') : SFlowContent 0 .blockKey s s' ∨ True := by
  rcases flowNode_toBlockKey (.content _ _ _ _ h) with h_node | _
  · cases h_node with
    | content _ _ _ _ hc => exact Or.inl hc
    | _ => exact Or.inr trivial
  · exact Or.inr trivial

/-- A separation re-reads at `block-key` when it is inline — the pairing
    spelled for the one the block side uses. -/
lemma sep_toBlockKey {n : Nat} {s s' : SurfPos} (h : SSeparate n .flowOut s s') :
    SSeparate 0 .blockKey s s' ∨ SepResidue n s s' :=
  sep_toKey (Or.inl ⟨rfl, rfl⟩) h

/-! ## §4 What the narrowing buys (DOCS item 229)

Item 228 narrowed six conclusions and could not say whether the narrowing was
worth anything: a residue is worth exactly what a consumer can refute
(`Tests.Guards.ConclusionObligationCensus.conclusion_eliminable_iff`), and
refuting "some interior crossed a line" needs the span — the characters
between the conclusion's own two positions — which the library could not name.
`L4YAML/Proofs/Foundation/SurfaceSpan.lean` names it, so the four residues can
now be sorted by the only question that matters.

Three carry a `[28] b-break` inside their span, so `¬ BreakBetween s s'`
refutes them.  `SepResidue` does not, and `sepResidue_span_can_be_empty` is
the proof, not the observation: item 228's zero-width witness has an EMPTY
span, and no predicate on characters can distinguish it from a separation that
was never taken. -/

lemma plainResidue_break {n : Nat} {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : PlainResidue n c s s') : BreakBetween s s' := by
  obtain ⟨_, hone, hplus⟩ := h
  match hplus with
  | .mk _ _ _ hx hrest =>
    refine breakBetween_extend_right ?_
      (breakBetween_extend_left ?_ (ssNsPlainNextLine_break hx))
    · exact gstar_suffix (fun _ _ => ssNsPlainNextLine_suffix) hrest
    · exact snsPlainOneLine_suffix hone

lemma doubleResidue_break {n : Nat} {s s' : SurfPos} (h : DoubleResidue n s s') :
    BreakBetween s s' := by
  obtain ⟨_, _, _, _, hq1, hone, hbrk, hrest, hq2⟩ := h
  refine breakBetween_extend_right ?_ (breakBetween_extend_left ?_ (ssDoubleBreak_break hbrk))
  · exact (glit_suffix hq2).trans (snbDoubleMultiLine_suffix hrest)
  · exact (snbDoubleOneLine_suffix hone).trans (glit_suffix hq1)

lemma singleResidue_break {n : Nat} {s s' : SurfPos} (h : SingleResidue n s s') :
    BreakBetween s s' := by
  obtain ⟨_, _, _, _, _, _, hq1, hone, hbrk, hempty, hpre, hrest, hq2⟩ := h
  refine breakBetween_extend_right ?_ (breakBetween_extend_left ?_ (breakBetween_of_break hbrk))
  · exact (glit_suffix hq2).trans ((snbSingleMultiLine_suffix hrest).trans
      ((sFlowLinePrefix_suffix hpre).trans (gstar_suffix (fun _ _ => sLEmpty_suffix) hempty)))
  · exact (snbSingleOneLine_suffix hone).trans (glit_suffix hq1)

/-- **The fourth residue's span can be empty**, so no character predicate
    refutes it.  This is `sepResidue_of_startOfLine` read through the span:
    item 228 showed the residue and its own left disjunct hold together, and
    the reason is that the derivation consumes nothing at all. -/
lemma sepResidue_span_can_be_empty (chars : List Char) :
    SepResidue 0 ⟨chars, 0⟩ ⟨chars, 0⟩ ∧ ¬ BreakBetween ⟨chars, 0⟩ ⟨chars, 0⟩ := by
  refine ⟨⟨⟨chars, 0⟩, SSLComments.startOfLine chars _ (GStar.nil _),
    SFlowLinePrefix.mk 0 _ _ _ (SIndent.zero _) (GOpt.none _)⟩, ?_⟩
  rintro ⟨pre, hspan, ch, hmem, -⟩
  have hpre : pre = [] := by
    simp only [Span] at hspan
    simpa using hspan.symm
  exact absurd (hpre ▸ hmem) (by simp)

/-- **…and it can be non-empty and still crossed no line.**  `[77] b-comment`
    ends a comment at END OF INPUT as well as at a break, so ` #c<EOF>` is a
    comment-delimited separation whose span is three characters, none of them a
    break.  Together with `sepResidue_span_can_be_empty` this is why no
    predicate on the span refutes `SepResidue` — not `BreakBetween`, and not
    "the span contains a `#`" either, since the zero-width witness has neither.
    The residue that WOULD be a partition is "this separation is not inline",
    and `sep_toKey` has to be re-proved to produce it. -/
lemma sepResidue_at_eof_comment :
    SepResidue 0 ⟨[' ', '#', 'c'], 3⟩ ⟨[], 6⟩ ∧
      ¬ BreakBetween ⟨[' ', '#', 'c'], 3⟩ ⟨[], 6⟩ := by
  refine ⟨⟨⟨[], 6⟩,
    SSLComments.withComment _ _ _
      (SSBComment.withSep _ _ _ _
        (SSeparateInLine.whites _ _
          (GPlus.mk _ ⟨['#', 'c'], 4⟩ _ (SSWhite.space _ 3) (GStar.nil _)))
        (GOpt.some ⟨['#', 'c'], 4⟩ ⟨[], 6⟩
          (SCNbCommentText.mk ['c'] 4 ⟨[], 6⟩
            (GStar.cons ⟨['c'], 5⟩ ⟨[], 6⟩ ⟨[], 6⟩
              (GChar.mk (p := isCommentTextChar) 'c' [] 5
                (by simp [isCommentTextChar, CharPredicates.isLineBreakProp,
                  CharPredicates.isLineFeedProp, CharPredicates.isCarriageReturnProp]))
              (GStar.nil _))))
        (SBComment.eof 6))
      (GStar.nil _),
    SFlowLinePrefix.mk 0 _ _ _ (SIndent.zero _) (GOpt.none _)⟩, ?_⟩
  rintro ⟨pre, hspan, ch, hmem, hbr⟩
  simp only [Span, List.append_nil] at hspan
  subst hspan
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> revert hbr <;> decide

/-! ### The payment

`narrowed_conclusion_pays` (item 228's §1) with the residue discharged: a
consumer holding "this key's span crosses no line" — which is what
`[193] c-s-implicit-json-key` requires of everything that reaches a `:` —
gets the conversion outright, with no disjunction left to case on. -/

lemma plain_toKey_of_noBreak {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlain n c s s') (hnb : ¬ BreakBetween s s') :
    SNsPlain 0 tc s s' :=
  (plain_toKey hp h).resolve_right (fun hr => hnb (plainResidue_break hr))

lemma doubleQuoted_toKey_of_noBreak {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCDoubleQuoted n c s s') (hnb : ¬ BreakBetween s s') :
    SCDoubleQuoted 0 tc s s' :=
  (doubleQuoted_toKey hp h).resolve_right (fun hr => hnb (doubleResidue_break hr))

lemma singleQuoted_toKey_of_noBreak {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCSingleQuoted n c s s') (hnb : ¬ BreakBetween s s') :
    SCSingleQuoted 0 tc s s' :=
  (singleQuoted_toKey hp h).resolve_right (fun hr => hnb (singleResidue_break hr))

end L4YAML.Proofs.FlowKeyLift
