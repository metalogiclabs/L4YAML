module

public import L4YAML.Proofs.Serialization.TraceOf.Node
public meta import L4YAML.Proofs.Serialization.TraceOf.Node

/-! # `tFlowNode_unique` on the event-annotated flow grammar (Rule 2)

Refutations (all three closed) of

    TFlowNode n c s s' ev₁ → TFlowNode n c s s' ev₂ → ev₁ = ev₂

each a pair of hand-built derivations of the same span with different traces.

1. `&xa` — CLOSED: `[101]`/`[104]` now demand the maximal anchor name
   (`GNot (GChar isNsAnchorChar)` after the run), so the reading "anchor `x`,
   empty `s-separate`, plain `a`" is no longer a derivation
   (`anchorX_not_property`); only `[defineAnchor "xa"]` remains.
2. `[a # b, &x⏎]` — plain-vs-comment, CLOSED: `#` after a space is a comment
   under `s-separate`.  `SNsPlainChar.hashAfterNs` (guard `col > 0`, not
   "preceded by ns-char") used to admit it inside the plain scalar too; now
   `[130]` has no `#` and `[132]`'s `hash` entry needs an empty `s-white*`,
   so ` #` is no entry (`hash_after_white_not_entry`) and only the comment
   reading `readComment` (trace `[]`) remains.
3. `[!t &x a]` — tag non-maximal, CLOSED: `!t` is a primary tag, or it was the
   non-specific tag `!` followed by an EMPTY `s-separate` and the plain scalar
   `t &x a` (traces `[useTag "!", defineAnchor "x"]` vs `[useTag "!"]`).  Every
   `[97]` arm now ends with `GNot (GChar isTagCharProp)`, so `[100]` cannot stop
   in front of `t` (`nonSpecific_not_before_t`); only the first reading remains. -/

namespace L4YAML.Tests.Guards.TraceOfFlowAmbiguity

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

private lemma ns_x : isNsAnchorChar 'x' := by unfold isNsAnchorChar isNsChar; decide
private lemma ns_a : isNsAnchorChar 'a' := by unfold isNsAnchorChar isNsChar; decide
private lemma safe_a : isNsPlainSafe .flowIn 'a' := by unfold isNsPlainSafe isNsChar; decide
private lemma safe_b : isNsPlainSafe .flowIn 'b' := by unfold isNsPlainSafe isNsChar; decide

/-! ## Refutation 1 (CLOSED by maximal anchor names): `[&xa]` -/
section AnchorSplit

abbrev s0 : SurfPos := ⟨['&', 'x', 'a', ']'], 1⟩
abbrev s1 : SurfPos := ⟨['a', ']'], 3⟩
abbrev s2 : SurfPos := ⟨[']'], 4⟩

/-- The `[101]`/`[104]` lookahead at a position whose head char is not an anchor char. -/
private lemma gnot_anchor_of_head {c : Char} {rest : List Char} {col : Nat}
    (h : ¬ isNsAnchorChar c) : GNot (GChar isNsAnchorChar) ⟨c :: rest, col⟩ :=
  fun _ hg => by cases hg with | mk _ _ _ hp => exact h hp

/-- `&xa` as one property, anchor `xa`; `]` is not an anchor char. -/
lemma readAnchorXA : TFlowNode 0 .flowIn s0 s2 [Event.defineAnchor "xa"] :=
  .propsEmpty 0 .flowIn s0 s2 _
    (TCNsProperties.anchorFirst s0 s2 s2 [Event.defineAnchor "xa"] []
      (And.intro
        (SCNsAnchorProperty.mk _ 1 s2
          (GPlus.mk _ _ _ (GChar.mk 'x' _ 2 ns_x)
            (GStar.cons _ _ _ (GChar.mk 'a' _ 3 ns_a) (GStar.nil _)))
          (gnot_anchor_of_head (by unfold isNsAnchorChar isNsChar; decide)))
        (by decide))
      (TOpt.none _))

/-- The former second reading — anchor `x` stopping in front of `a` — is no
longer a `[101]` derivation: the name must be maximal. -/
lemma anchorX_not_property : ¬ SCNsAnchorProperty s0 s1 :=
  fun h => by cases h with | mk _ _ _ _ hnot => exact hnot _ (GChar.mk 'a' _ 3 ns_a)

end AnchorSplit

/-! ## Refutation 2: `[a # b, &x⏎]` -/
section PlainComment

abbrev t0 : SurfPos := ⟨['[', 'a', ' ', '#', ' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 0⟩
abbrev t1 : SurfPos := ⟨['a', ' ', '#', ' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 1⟩
abbrev t2 : SurfPos := ⟨[' ', '#', ' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 2⟩
abbrev t3 : SurfPos := ⟨['#', ' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 3⟩
abbrev t4 : SurfPos := ⟨[' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 4⟩
abbrev t5 : SurfPos := ⟨['b', ',', ' ', '&', 'x', '\n', ']'], 5⟩
abbrev t6 : SurfPos := ⟨[',', ' ', '&', 'x', '\n', ']'], 6⟩
abbrev t7 : SurfPos := ⟨[' ', '&', 'x', '\n', ']'], 7⟩
abbrev t8 : SurfPos := ⟨['&', 'x', '\n', ']'], 8⟩
abbrev t9 : SurfPos := ⟨['x', '\n', ']'], 9⟩
abbrev t10 : SurfPos := ⟨['\n', ']'], 10⟩
abbrev t11 : SurfPos := ⟨[']'], 0⟩
abbrev t12 : SurfPos := ⟨[], 1⟩

private lemma cc (ch : Char) (h : ¬isLineBreakProp ch) : isCommentTextChar ch := h

/-- Plain `a`, then `s-separate` = ` # b, &x⏎` as a comment, then `]`. -/
lemma readComment : TFlowSequence 0 .flowOut t0 t12 [] :=
  .nonempty 0 .flowOut t0 t1 t1 t11 t12 []
    (GLit.mk _ 0) (GOpt.none _)
    (.single 0 .flowIn t1 t2 t11 []
      (.node 0 .flowIn t1 t2 [] (.content 0 .flowIn t1 t2 [] (.plain 0 .flowIn t1 t2
        (SNsPlainMultiLine.mk 0 .flowIn t1 t2 t2
          (SNsPlainOneLine.mk .flowIn t1 t2 t2
            (SNsPlainFirst.nonIndicator .flowIn 'a' _ 1 safe_a (by decide)) (GStar.nil _))
          (GStar.nil _)))))
      (GOpt.some _ _ (SSeparateLines.commented 0 t2 t11 t11
        (SSLComments.withComment t2 t11 t11
          (SSBComment.withSep t2 t3 t10 t11
            (SSeparateInLine.whites t2 t3 (GPlus.mk _ _ _ (SSWhite.space _ 2) (GStar.nil _)))
            (GOpt.some _ _ (SCNbCommentText.mk _ 3 t10
              (GStar.cons _ _ _ (GChar.mk ' ' _ 4 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk 'b' _ 5 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk ',' _ 6 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk ' ' _ 7 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk '&' _ 8 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk 'x' _ 9 (cc _ (by decide)))
              (GStar.nil _)))))))))
            (SBComment.break t10 t11 (SBBreak.lf _ 10)))
          (GStar.nil _))
        (SFlowLinePrefix.mk 0 t11 t11 t11 (SIndent.zero _) (GOpt.none _)))))
    (GLit.mk _ 0)

/-- The second derivation is gone: ` #` (white, then `#`) is NOT a `[132]` entry.  `mk`'s
    `ns-plain-char` has no `#`, and `hash` wants the `#` at the entry's own start — here
    the entry starts with a space.  `[a # b, &x⏎]` keeps only `readComment`. -/
lemma hash_after_white_not_entry : ¬ SNbNsPlainInLineEntry .flowIn t2 t4 := by
  intro h
  cases h
  · rename_i hws hch
    cases hws
    · cases hch
    · rename_i hw hws'
      cases hw
      cases hws'
      · cases hch
        rename_i hNotHash
        exact hNotHash rfl
      · rename_i hw' _
        cases hw'
  · rename_i hl
    cases hl

end PlainComment

/-! ## Refutation 3: `[!t &x a]` (a listed input) -/
section TagSplit

abbrev u0 : SurfPos := ⟨['!', 't', ' ', '&', 'x', ' ', 'a', ']'], 1⟩
abbrev u1 : SurfPos := ⟨['t', ' ', '&', 'x', ' ', 'a', ']'], 2⟩
abbrev u2 : SurfPos := ⟨[' ', '&', 'x', ' ', 'a', ']'], 3⟩
abbrev u3 : SurfPos := ⟨['&', 'x', ' ', 'a', ']'], 4⟩
abbrev u4 : SurfPos := ⟨['x', ' ', 'a', ']'], 5⟩
abbrev u5 : SurfPos := ⟨[' ', 'a', ']'], 6⟩
abbrev u6 : SurfPos := ⟨['a', ']'], 7⟩
abbrev u7 : SurfPos := ⟨[']'], 8⟩

private lemma gnot_tag_u2 : GNot (GChar isTagCharProp) u2 :=
  fun _ h => by cases h with | mk _ _ _ hp => exact absurd hp (by decide)

/-- Tag `!t`, anchor `&x`, plain `a`. -/
lemma readTagAnchor : TFlowNode 0 .flowIn u0 u7 [Event.useTag "!", Event.defineAnchor "x"] :=
  .propsContent 0 .flowIn u0 u5 u6 u7 [Event.useTag "!", Event.defineAnchor "x"] []
    (TCNsProperties.tagFirst u0 u2 u5 [Event.useTag "!"] [Event.defineAnchor "x"]
      (And.intro
        (SCNsTagProperty.primary _ 1 u2
          (GPlus.mk _ _ _ (GChar.mk 't' _ 2 (by decide)) (GStar.nil _))
          gnot_tag_u2)
        (by decide))
      (TOpt.some _ _ _ (TSeq.mk u2 u3 u5 [] [Event.defineAnchor "x"]
        (And.intro
          (SSeparateLines.inline 0 u2 u3
            (SSeparateInLine.whites u2 u3 (GPlus.mk _ _ _ (SSWhite.space _ 3) (GStar.nil _))))
          rfl)
        (And.intro
          (SCNsAnchorProperty.mk _ 4 u5
            (GPlus.mk _ _ _ (GChar.mk 'x' _ 5 ns_x) (GStar.nil _))
            (gnot_anchor_of_head (by unfold isNsAnchorChar isNsChar; decide)))
          (by decide)))))
    (SSeparateLines.inline 0 u5 u6
      (SSeparateInLine.whites u5 u6 (GPlus.mk _ _ _ (SSWhite.space _ 6) (GStar.nil _))))
    (.plain 0 .flowIn u6 u7
      (SNsPlainMultiLine.mk 0 .flowIn u6 u7 u7
        (SNsPlainOneLine.mk .flowIn u6 u7 u7
          (SNsPlainFirst.nonIndicator .flowIn 'a' _ 7 safe_a (by decide)) (GStar.nil _))
        (GStar.nil _)))

/-- The former second reading — `[100]` stopping in front of `t` — is no
longer a derivation: the tag must be maximal (`t` is a `[40] ns-tag-char`). -/
lemma nonSpecific_not_before_t : ¬ GNot (GChar isTagCharProp) u1 :=
  fun h => h _ (GChar.mk 't' _ 2 (by decide))

end TagSplit

end L4YAML.Tests.Guards.TraceOfFlowAmbiguity
