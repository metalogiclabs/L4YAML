module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Proofs.Serialization.TraceOf.Document

/-! # Annotated [211] continuation regressions (Rule 2)

Capstone chain: 7.7 `parse_iff_grammar` ← source serialization semantics ←
document boundaries must not introduce spurious bare-document readings.

The former `readAnchor` / `readTwoDocs` constructions and their three
whole-stream refutation consequences are preserved in the parent source:
`64795a8db28ccfdae85082c93b6453001ae9d3e4`,
`Tests/Guards/Proofs/TraceOfBlockAmbiguity.lean`. They used the old arbitrary
document premise of `TLYamlStream.implicitContinue`. The guards below now
exclude those exact explicit-document slots and retain the valid component
derivations. Positive controls preserve explicit documents, suffix-then-bare
documents, comments, and BOMs.

This closes those two constructor applications, not full trace uniqueness.
The literal node witnesses remain; no claim is made that block-scalar
autodetection or the scanner-to-trace bridge is complete. -/

namespace L4YAML.Tests.Guards.TraceOfBlockAmbiguity

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

private lemma ns_x : isNsAnchorChar 'x' := by unfold isNsAnchorChar isNsChar; decide
private lemma nsc_a : isNsChar 'a' := by unfold isNsChar; decide
private lemma nsc_amp : isNsChar '&' := by unfold isNsChar; decide
private lemma nsc_x : isNsChar 'x' := by unfold isNsChar; decide
private lemma notInd_a : ¬ isIndicatorProp 'a' := by unfold isIndicatorProp; decide

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

/-! ## Regression 1: `a⏎&x` retains its plain reading, not the old bare append -/
section ImplicitContinue

abbrev u0 : SurfPos := ⟨['a', '\n', '&', 'x'], 0⟩
abbrev u1 : SurfPos := ⟨['\n', '&', 'x'], 1⟩
abbrev u2 : SurfPos := ⟨['&', 'x'], 0⟩
abbrev u3 : SurfPos := ⟨['x'], 1⟩
abbrev u4 : SurfPos := ⟨[], 2⟩

/-- Reading A (the parser's): one bare document, plain scalar `a &x` folded over the break. -/
lemma readPlain : TLYamlStream u0 u4 [] :=
  .single u0 u0 u4 u4 [] [] (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _
      (.flowInBlock 0 .blockIn u0 u0 u4 u4 []
        (.inline 0 _ _ (.startOfLine _))
        (.content 0 .flowOut u0 u4 [] (.plain 0 .flowOut u0 u4
          (SNsPlainMultiLine.mk 0 .flowOut u0 u1 u4
            (SNsPlainOneLine.mk .flowOut u0 u1 u1
              (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
            (.cons u1 u4 u4
              (SSNsPlainNextLine.mk 0 .flowOut u1 u1 u2 u2 u2 u3 u4
                (.nil _) (SBBreak.lf _ 1) (.nil _)
                (SFlowLinePrefix.mk 0 u2 u2 u2 (.zero _) (.none _))
                (SNsPlainChar.safe .flowOut '&' _ 0 nsc_amp (by decide) (by decide))
                (.cons u3 u4 u4
                  (SNbNsPlainInLineEntry.mk .flowOut u3 u3 u4 (.nil _)
                    (SNsPlainChar.safe .flowOut 'x' _ 1 nsc_x (by decide) (by decide)))
                  (.nil _)))
              (.nil _)))))
        (eofComments 2)))))
    (.nil _)

/-- The old second document is still a valid node. What is rejected is its
placement in an unmarked next-document slot, not the anchor syntax itself. -/
lemma anchorNode : TBlockNode 0 .blockIn u2 u4 [Event.defineAnchor "x"] :=
  .flowInBlock 0 .blockIn u2 u2 u4 u4 [Event.defineAnchor "x"]
    (.inline 0 _ _ (.startOfLine _))
    (.propsEmpty 0 .flowOut u2 u4 _
      (TCNsProperties.anchorFirst u2 u4 u4 [Event.defineAnchor "x"] []
        (And.intro
          (SCNsAnchorProperty.mk _ 0 u4
            (GPlus.mk _ _ _ (GChar.mk 'x' _ 1 ns_x) (.nil _))
            (fun _ hg => by cases hg))
          (by decide))
        (.none _)))
    (eofComments 2)

lemma traceOf_plain : TraceOf "a\n&x" [] := ⟨2, readPlain⟩

/-- Exact negative control for the former second bare document. -/
lemma anchor_not_explicit (ev : List Event) : ¬ TLExplicitDocument u2 u4 ev := by
  intro h
  cases h with
  | withContent =>
    rename_i hm _
    cases hm

/-- The same unmarked slot must not introduce an alias document. -/
lemma alias_not_explicit (rest : List Char) (col : Nat) (t : SurfPos) (ev : List Event) :
    ¬ TLExplicitDocument ⟨'*' :: rest, col⟩ t ev := by
  intro h
  cases h with
  | withContent =>
    rename_i hm _
    cases hm

/-- A directive document needs the suffix branch, rather than this explicit slot. -/
lemma directive_not_explicit (rest : List Char) (col : Nat) (t : SurfPos) (ev : List Event) :
    ¬ TLExplicitDocument ⟨'%' :: rest, col⟩ t ev := by
  intro h
  cases h with
  | withContent =>
    rename_i hm _
    cases hm

end ImplicitContinue

/-! ## Regression 2: literal witnesses retained, the old second bare mapping excluded

The `[173]` EOF-tail repair is unchanged. The annotation-only [211] narrowing
rejects the formerly used unmarked next-document slot; it does not settle the
remaining block-scalar or whole-language obligations. -/
section LiteralTail

private instance : DecidablePred isNbChar := fun c => by unfold isNbChar; infer_instance

private lemma nbRun (cs rest : List Char) (col : Nat) (h : ∀ c ∈ cs, isNbChar c) :
    GStar SNbChar ⟨cs ++ rest, col⟩ ⟨rest, col + cs.length⟩ := by
  induction cs generalizing col with
  | nil => exact GStar.nil _
  | cons c cs ih =>
    refine GStar.cons _ ⟨cs ++ rest, col + 1⟩ _ (GChar.mk c _ col (h c (by simp))) ?_
    have := ih (col + 1) (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have e : col + 1 + cs.length = col + (c :: cs).length := by simp; omega
    rw [e] at this
    exact this

private lemma nbPlus (c : Char) (cs rest : List Char) (col : Nat) (hc : isNbChar c)
    (h : ∀ d ∈ cs, isNbChar d) :
    GPlus SNbChar ⟨c :: cs ++ rest, col⟩ ⟨rest, col + 1 + cs.length⟩ :=
  GPlus.mk _ _ _ (GChar.mk c _ col hc) (nbRun cs rest (col + 1) h)

private lemma gnot_anchor_of_head {c : Char} {rest : List Char} {col : Nat}
    (h : ¬ isNsAnchorChar c) : GNot (GChar isNsAnchorChar) ⟨c :: rest, col⟩ :=
  fun _ hg => by cases hg with | mk _ _ _ hp => exact h hp

private lemma nsc_b : isNsChar 'b' := by unfold isNsChar; decide
private lemma notInd_b : ¬ isIndicatorProp 'b' := by unfold isIndicatorProp; decide
private lemma notAnchor_space : ¬ isNsAnchorChar ' ' := by unfold isNsAnchorChar isNsChar; decide

abbrev tail3 : List Char := ['\n', ' ', ' ', '&', 'x', ' ', 'b', ':', ' ', '*', 'x']
abbrev v0 : SurfPos := ⟨'a' :: ':' :: ' ' :: '|' :: '\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 0⟩
abbrev v1 : SurfPos := ⟨':' :: ' ' :: '|' :: '\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 1⟩
abbrev v2 : SurfPos := ⟨' ' :: '|' :: '\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 2⟩
abbrev v3 : SurfPos := ⟨'|' :: '\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 3⟩
abbrev v4 : SurfPos := ⟨'\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 4⟩
abbrev v5 : SurfPos := ⟨' ' :: ' ' :: ' ' :: 'x' :: tail3, 0⟩
abbrev v6 : SurfPos := ⟨' ' :: ' ' :: 'x' :: tail3, 1⟩
abbrev v8 : SurfPos := ⟨'x' :: tail3, 3⟩
abbrev v9 : SurfPos := ⟨tail3, 4⟩
abbrev v10 : SurfPos := ⟨[' ', ' ', '&', 'x', ' ', 'b', ':', ' ', '*', 'x'], 0⟩
abbrev v11 : SurfPos := ⟨[' ', '&', 'x', ' ', 'b', ':', ' ', '*', 'x'], 1⟩
abbrev v12 : SurfPos := ⟨['&', 'x', ' ', 'b', ':', ' ', '*', 'x'], 2⟩
abbrev v14 : SurfPos := ⟨[' ', 'b', ':', ' ', '*', 'x'], 4⟩
abbrev v15 : SurfPos := ⟨['b', ':', ' ', '*', 'x'], 5⟩
abbrev v16 : SurfPos := ⟨[':', ' ', '*', 'x'], 6⟩
abbrev v17 : SurfPos := ⟨[' ', '*', 'x'], 7⟩
abbrev v18 : SurfPos := ⟨['*', 'x'], 8⟩
abbrev vEnd : SurfPos := ⟨[], 10⟩

/-- The shared prefix `a: ` of both readings: key `a`, then `:`. -/
private lemma keyA : TImplicitKey v0 v1 [] :=
  .yamlKey v0 v1 v1
    (SNsPlainOneLine.mk .blockKey v0 v1 v1
      (SNsPlainFirst.nonIndicator .blockKey 'a' _ 0 nsc_a notInd_a) (.nil _))
    (.none _)

/-- `|` + empty header + the comment-less line end; the body starts at `v5`. -/
private lemma header : SCBBlockHeader v4 v5 :=
  .mk v4 v4 v5
    (.left _ _ (.mk _ _ _ (.empty _) (.empty _)))
    (.noSep _ _ (.break _ _ (SBBreak.lf _ 4)))

/-- Reading A: autodetected indent `m = 0`, content indent 1 — BOTH following lines are
literal text (the extra spaces are `nb-char`s).  One entry, trace `[]`. -/
lemma literalA : SCLLiteral 1 v3 vEnd :=
  .mk 1 0 _ 3 v5 vEnd header
    (SLLiteralContent.mk 1 v5 vEnd vEnd vEnd vEnd vEnd
      (.some _ _ (.mk v5 v9 vEnd
        (SLNbLiteralText.mk 1 v5 v5 v9 (.nil _)
          (.mk v5 v6 v9 (.succ 0 _ 0 v6 (.zero _))
            (nbPlus ' ' [' ', 'x'] tail3 1 (by decide) (by decide))))
        (.cons v9 vEnd vEnd
          (SBNbLiteralNext.mk 1 v9 v10 vEnd (SBBreak.lf _ 4)
            (SLNbLiteralText.mk 1 v10 v10 vEnd (.nil _)
              (.mk v10 v11 vEnd (.succ 0 _ 0 v11 (.zero _))
                (nbPlus ' ' ['&', 'x', ' ', 'b', ':', ' ', '*', 'x'] [] 1 (by decide) (by decide)))))
          (.nil _))))
      (.none _) (.nil _) (.none _) (.none _))

lemma readOneEntry : TBlockNode 0 .blockIn v0 vEnd [] :=
  .blockMap 0 .blockIn 0 v0 v0 v0 vEnd [] [] (.none _) (.startOfLine _ _ (.nil _))
    (.single 0 v0 v0 vEnd [] (.zero _)
      (.implicitKeyNode 0 v0 v1 v2 vEnd [] [] keyA (GLit.mk _ 1)
        (.blockLiteral 1 .blockOut v2 v3 v3 vEnd []
          (.inline 1 _ _ (.whites _ _ (.mk _ _ _ (.space _ 2) (.nil _))))
          (.none _) literalA)))

/-- Reading B: autodetected indent `m = 2`, content indent 3 — the second line is text, the
third is not indented enough, so the content ENDS after the break (at `v10`).

`[173]`'s partial-indent tail is now confined to end of input, so the two spaces of line 3
are NOT the scalar's: the enclosing mapping at indent 0 cannot resume at indent 2 either, and
the former two-entries-in-one-mapping refutation is closed. The smaller scalar
derivation is retained here. Its former assembly with a second bare document
through `TLYamlStream.implicitContinue` is now excluded by
`literal_tail_not_explicit`; this is not a proof of whole-stream uniqueness. -/
lemma literalB : SCLLiteral 1 v3 v10 :=
  .mk 1 2 _ 3 v5 v10 header
    (SLLiteralContent.mk 3 v5 v9 v10 v10 v10 v10
      (.some _ _ (.mk v5 v9 v9
        (SLNbLiteralText.mk 3 v5 v5 v9 (.nil _)
          (.mk v5 v8 v9 (.succ 2 _ 0 v8 (.succ 1 _ 1 v8 (.succ 0 _ 2 v8 (.zero _))))
            (nbPlus 'x' [] tail3 3 (by decide) (by decide))))
        (.nil _)))
      (.some _ _ (SBBreak.lf _ 4)) (.nil _) (.none _) (.none _))

/-- First document of reading B: the single entry `a: |⏎   x⏎` with the `m = 2` literal. -/
lemma readOneEntryB : TBlockNode 0 .blockIn v0 v10 [] :=
  .blockMap 0 .blockIn 0 v0 v0 v0 v10 [] [] (.none _) (.startOfLine _ _ (.nil _))
    (.single 0 v0 v0 v10 [] (.zero _)
      (.implicitKeyNode 0 v0 v1 v2 v10 [] [] keyA (GLit.mk _ 1)
        (.blockLiteral 1 .blockOut v2 v3 v3 v10 []
          (.inline 1 _ _ (.whites _ _ (.mk _ _ _ (.space _ 2) (.nil _))))
          (.none _) literalB)))

private lemma keyAnchoredB : TImplicitKey v12 v16 [Event.defineAnchor "x"] :=
  .jsonKey v12 v16 v16 _
    (.propsContent 0 .blockKey v12 v14 v15 v16 [Event.defineAnchor "x"] []
      (TCNsProperties.anchorFirst v12 v14 v14 [Event.defineAnchor "x"] []
        (And.intro
          (SCNsAnchorProperty.mk _ 2 v14
            (GPlus.mk _ _ _ (GChar.mk 'x' _ 3 ns_x) (.nil _))
            (gnot_anchor_of_head notAnchor_space))
          (by decide))
        (.none _))
      (.whites _ _ (.mk _ _ _ (.space _ 4) (.nil _)))
      (.plain 0 .blockKey v15 v16
        (SNsPlainOneLine.mk .blockKey v15 v16 v16
          (SNsPlainFirst.nonIndicator .blockKey 'b' _ 5 nsc_b notInd_b) (.nil _))))
    (.none _)

private lemma aliasValue (n : Nat) : TBlockNode n .blockOut v17 vEnd [Event.useAlias "x"] :=
  .flowInBlock n .blockOut v17 v18 vEnd vEnd _
    (.inline n _ _ (.whites _ _ (.mk _ _ _ (.space _ 7) (.nil _))))
    (.alias n .flowOut v18 vEnd _
      (And.intro
        (SCNsAliasNode.mk _ 8 vEnd
          (GPlus.mk _ _ _ (GChar.mk 'x' _ 9 ns_x) (.nil _))
          (fun _ hg => by cases hg))
        (by decide)))
    (eofComments 10)

/-- Second document of reading B: the bare document `  &x b: *x`, a block mapping at indent 2. -/
lemma secondDoc : TBlockNode 0 .blockIn v10 vEnd [Event.defineAnchor "x", Event.useAlias "x"] :=
  .blockMap 0 .blockIn 2 v10 v10 v10 vEnd [] _ (.none _) (.startOfLine _ _ (.nil _))
    (.single 2 v10 v12 vEnd _ (.succ 1 _ 0 v12 (.succ 0 _ 1 v12 (.zero _)))
      (.implicitKeyNode 2 v12 v16 v17 vEnd [Event.defineAnchor "x"] [Event.useAlias "x"]
        keyAnchoredB (GLit.mk _ 6) (aliasValue 3)))

/-- Exact negative control for the old unmarked second mapping. The spaces
and anchor at this source position are not a leading explicit-document marker. -/
lemma literal_tail_not_explicit (ev : List Event) :
    ¬ TLExplicitDocument v10 vEnd ev := by
  intro h
  cases h with
  | withContent =>
    rename_i hm _
    cases hm

private lemma streamOf {s' : SurfPos} {ev : List Event} (h : TBlockNode 0 .blockIn v0 s' ev) :
    TLYamlStream v0 s' ev := by
  have := TLYamlStream.single v0 v0 s' s' ev [] (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _ h))) (.nil _)
  simpa using this

lemma traceOf_literalA : TraceOf "a: |\n   x\n  &x b: *x" [] := ⟨10, streamOf readOneEntry⟩
end LiteralTail

/-! ## Positive continuation controls for the actual annotated stream -/
section ContinuationControls

private lemma empty_at (s : SurfPos) : TLYamlStream s s [] :=
  .single s s s s [] [] (.nil s) (.none s) (.nil s)

private lemma explicit_preserved {s p q : SurfPos} {ev ed : List Event}
    (h : TLYamlStream s p ev) (hd : TLExplicitDocument p q ed) :
    TLYamlStream s q (ev ++ ed) := by
  simpa only [List.append_nil] using
    (TLYamlStream.implicitContinue s p p q q ev ed [] h (.nil p) hd (.nil q))

private lemma suffix_then_bare_preserved {s p q t : SurfPos} {ev es ed : List Event}
    (h : TLYamlStream s p ev) (hs : TPlus TLDocumentSuffix p q es)
    (hd : TLBareDocument q t ed) : TLYamlStream s t (ev ++ es ++ ed) := by
  simpa only [List.append_nil] using
    (TLYamlStream.suffixContinue s p q q t t ev es ed [] h hs (.nil q)
      (.some q t ed (.bare q t ed hd)) (.nil t))

private lemma comment_preserved {s p q : SurfPos} {ev : List Event}
    (h : TLYamlStream s p ev) (hc : SLComment p q) : TLYamlStream s q ev := by
  simpa only [List.append_nil] using
    (TLYamlStream.prefixContinue s p q q ev [] h
      (.cons p q q (.comments p q (.cons p q q hc (.nil q))) (.nil q))
      (.nil q))

private lemma bom_preserved {s : SurfPos} (rest : List Char) (col : Nat) {ev : List Event}
    (h : TLYamlStream s ⟨'\uFEFF' :: rest, col⟩ ev) :
    TLYamlStream s ⟨rest, col⟩ ev := by
  simpa only [List.append_nil] using
    (TLYamlStream.prefixContinue s ⟨'\uFEFF' :: rest, col⟩ ⟨rest, col⟩ ⟨rest, col⟩
      ev [] h
      (.cons _ _ _ (.bom rest col ⟨rest, col⟩ (.nil _)) (.nil _))
      (.nil _))

private lemma explicit_empty_after (rest : List Char) (q : SurfPos)
    (hc : SSLComments ⟨rest, 3⟩ q) :
    TLExplicitDocument ⟨'-' :: '-' :: '-' :: rest, 0⟩ q [.beginDocument] :=
  .withContent _ _ _ [] (.mk rest)
    (.right _ _ [] (.mk _ _ _ [] [] ⟨.mk _, rfl⟩ ⟨hc, rfl⟩))

lemma explicit_empty : TLYamlStream ⟨['-', '-', '-'], 0⟩ ⟨[], 3⟩ [.beginDocument] :=
  explicit_preserved (empty_at _) (explicit_empty_after [] _ (eofComments 3))

lemma two_explicit :
    TLYamlStream ⟨['-', '-', '-', '\n', '-', '-', '-'], 0⟩ ⟨[], 3⟩
      [.beginDocument, .beginDocument] := by
  have hfirst := explicit_empty_after ['\n', '-', '-', '-'] ⟨['-', '-', '-'], 0⟩
    (SSLComments.withComment _ _ _
      (.noSep _ _ (.break _ _ (.lf ['-', '-', '-'] 3))) (.nil _))
  have hstart := explicit_preserved (empty_at _) hfirst
  exact explicit_preserved hstart (explicit_empty_after [] _ (eofComments 3))

/-- The anchor syntax excluded from the unmarked slot is retained after the
document-suffix marker. The optional initial document is empty in this smallest
suffix-branch control. -/
lemma anchor_after_suffix :
    TLYamlStream ⟨['.', '.', '.', '\n', '&', 'x'], 0⟩ u4
      [.endDocument, .defineAnchor "x"] := by
  have hs : TPlus TLDocumentSuffix ⟨['.', '.', '.', '\n', '&', 'x'], 0⟩ u2
      [.endDocument] :=
    .mk _ u2 u2 [.endDocument] []
      (.mk _ ⟨['\n', '&', 'x'], 3⟩ u2 (.mk ['\n', '&', 'x'])
        (.withComment _ u2 u2 (.noSep _ _ (.break _ _ (.lf ['&', 'x'] 3))) (.nil _)))
      (.nil u2)
  exact suffix_then_bare_preserved (empty_at _) hs (.mk u2 u4 _ anchorNode)

lemma standalone_bom : TLYamlStream ⟨['\uFEFF'], 0⟩ ⟨[], 0⟩ [] :=
  bom_preserved [] 0 (empty_at _)

lemma standalone_comment : TLYamlStream ⟨['#', '\n'], 0⟩ ⟨[], 0⟩ [] := by
  apply comment_preserved (empty_at _)
  exact SLComment.mk _ _ _ _ (.startOfLine _)
    (.some _ _ (.mk ['\n'] 0 _ (.nil _)))
    (.break _ _ (.lf [] 1))

end ContinuationControls

#print axioms readPlain
#print axioms anchorNode
#print axioms traceOf_plain
#print axioms anchor_not_explicit
#print axioms alias_not_explicit
#print axioms directive_not_explicit
#print axioms literalA
#print axioms literalB
#print axioms readOneEntry
#print axioms readOneEntryB
#print axioms secondDoc
#print axioms literal_tail_not_explicit
#print axioms traceOf_literalA
#print axioms explicit_empty
#print axioms two_explicit
#print axioms anchor_after_suffix
#print axioms standalone_bom
#print axioms standalone_comment

end L4YAML.Tests.Guards.TraceOfBlockAmbiguity
