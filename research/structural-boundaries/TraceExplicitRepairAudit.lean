module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Proofs.Serialization.TraceOf.Document

/-!
# Bounded annotation-only repair for YAML [211]

Source pin: nasa-jpl/L4YAML 64795a8db28ccfdae85082c93b6453001ae9d3e4.
STATUS: CANDIDATE; this sidecar has not yet passed native Lean compilation.

This is a repair experiment, not another capstone and not a claim of complete
YAML exactness. The existing annotation allows an unmarked arbitrary document
after an existing stream. The variant below replaces that choice with an
explicit document OR a document-free prefix/suffix continuation. Thus comments
and BOM continuations are preserved, rather than accidentally dropped together
with the bad bare-document alternative.

The generic embedding is into the existing event-annotated stream, preserving
the exact event list. It is NOT an erasure theorem into Surface: no scannerDrop
shortcut is used. Surface erasure of the 18-member annotated node family is a
separate, currently absent obligation. Nothing here edits the production grammar
or StreamAccum. The known upstream ambiguity is not claimed as a new finding.
-/

namespace MathGraph.TraceExplicitRepairAudit

@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

/-- An annotation-only narrowing. The first two arms are unchanged. -/
inductive RepairedStream : TRel where
  | single (s s₁ s₂ s' : SurfPos) (e₁ e₂ : List Event) :
      GStar SLDocumentPrefix s s₁ →
      TOpt TLAnyDocument s₁ s₂ e₁ →
      TStar TLDocumentSuffix s₂ s' e₂ →
      RepairedStream s s' (e₁ ++ e₂)
  | suffixContinue (s s₁ s₂ s₃ s₄ s' : SurfPos) (e₀ e₁ e₂ e₃ : List Event) :
      RepairedStream s s₁ e₀ →
      TPlus TLDocumentSuffix s₁ s₂ e₁ →
      GStar SLDocumentPrefix s₂ s₃ →
      TOpt TLAnyDocument s₃ s₄ e₂ →
      TStar TLDocumentSuffix s₄ s' e₃ →
      RepairedStream s s' (e₀ ++ e₁ ++ e₂ ++ e₃)
  | explicitContinue (s s₁ s₂ s₃ s' : SurfPos) (e₀ e₁ e₂ : List Event) :
      RepairedStream s s₁ e₀ →
      GStar SLDocumentPrefix s₁ s₂ →
      TLExplicitDocument s₂ s₃ e₁ →
      TStar TLDocumentSuffix s₃ s' e₂ →
      RepairedStream s s' (e₀ ++ e₁ ++ e₂)
  | prefixContinue (s s₁ s₂ s' : SurfPos) (e₀ e₁ : List Event) :
      RepairedStream s s₁ e₀ →
      GStar SLDocumentPrefix s₁ s₂ →
      TStar TLDocumentSuffix s₂ s' e₁ →
      RepairedStream s s' (e₀ ++ e₁)

/-- Every repaired derivation is an old derivation with the same source,
endpoint, and event trace. This is a narrowing, not an extension. -/
lemma embeds_old {s s' : SurfPos} {ev : List Event}
    (h : RepairedStream s s' ev) : TLYamlStream s s' ev := by
  induction h with
  | single s s₁ s₂ s' e₁ e₂ hp hd ht =>
    exact .single s s₁ s₂ s' e₁ e₂ hp hd ht
  | suffixContinue s s₁ s₂ s₃ s₄ s' e₀ e₁ e₂ e₃ _ hs hp hd ht ih =>
    exact .suffixContinue s s₁ s₂ s₃ s₄ s' e₀ e₁ e₂ e₃ ih hs hp hd ht
  | explicitContinue s s₁ s₂ s₃ s' e₀ e₁ e₂ _ hp hd ht ih =>
    exact .implicitContinue s s₁ s₂ s₃ s' e₀ e₁ e₂ ih hp
      (.some s₂ s₃ e₁ (.explicit s₂ s₃ e₁ hd)) ht
  | prefixContinue s s₁ s₂ s' e₀ e₁ _ hp ht ih =>
    simpa only [List.append_nil] using
      (TLYamlStream.implicitContinue s s₁ s₂ s₂ s' e₀ [] e₁
        ih hp (.none s₂) ht)

/-- Compatibility with the minimal one-premise patch: use optional EXPLICIT
documents while keeping the existing no-document continuation. -/
lemma unmarkedContinue (s s₁ s₂ s₃ s' : SurfPos) (e₀ e₁ e₂ : List Event)
    (h : RepairedStream s s₁ e₀) (hp : GStar SLDocumentPrefix s₁ s₂)
    (hd : TOpt TLExplicitDocument s₂ s₃ e₁)
    (ht : TStar TLDocumentSuffix s₃ s' e₂) :
    RepairedStream s s' (e₀ ++ e₁ ++ e₂) := by
  cases hd with
  | none =>
    simpa only [List.append_nil] using RepairedStream.prefixContinue _ _ _ _ _ _ h hp ht
  | some =>
    rename_i hd
    exact .explicitContinue _ _ _ _ _ _ _ _ h hp hd ht

lemma empty_at (s : SurfPos) : RepairedStream s s [] :=
  .single s s s s [] [] (.nil s) (.none s) (.nil s)

/-- Existing single-document paths are unaffected, including the valid plain
reading and the valid single-document literal reading in the upstream guard. -/
lemma single_preserved (s s₁ s₂ s' : SurfPos) (e₁ e₂ : List Event)
    (hp : GStar SLDocumentPrefix s s₁) (hd : TOpt TLAnyDocument s₁ s₂ e₁)
    (ht : TStar TLDocumentSuffix s₂ s' e₂) :
    RepairedStream s s' (e₁ ++ e₂) := .single _ _ _ _ _ _ hp hd ht

/-- Explicit continuation needs no extra suffix and preserves its trace. -/
lemma explicit_preserved {s p q : SurfPos} {ev ed : List Event}
    (h : RepairedStream s p ev) (hd : TLExplicitDocument p q ed) :
    RepairedStream s q (ev ++ ed) := by
  simpa only [List.append_nil] using
    (RepairedStream.explicitContinue s p p q q ev ed [] h (.nil p) hd (.nil q))

/-- A bare document remains available AFTER a nonempty document-suffix run. -/
lemma suffix_then_bare_preserved {s p q t : SurfPos} {ev es ed : List Event}
    (h : RepairedStream s p ev) (hs : TPlus TLDocumentSuffix p q es)
    (hd : TLBareDocument q t ed) : RepairedStream s t (ev ++ es ++ ed) := by
  simpa only [List.append_nil] using
    (RepairedStream.suffixContinue s p q q t t ev es ed [] h hs (.nil q)
      (.some q t ed (.bare q t ed hd)) (.nil t))

/-- The no-document alternative retains every full-line comment, with no reset
or other event added to the trace. -/
lemma comment_preserved {s p q : SurfPos} {ev : List Event}
    (h : RepairedStream s p ev) (hc : SLComment p q) : RepairedStream s q ev := by
  simpa only [List.append_nil] using
    (RepairedStream.prefixContinue s p q q ev [] h
      (.cons p q q (.comments p q (.cons p q q hc (.nil q))) (.nil q))
      (.nil q))

/-- The no-document alternative retains a BOM at the current source position,
with the exact column and event trace unchanged. -/
lemma bom_preserved {s : SurfPos} (rest : List Char) (col : Nat) {ev : List Event}
    (h : RepairedStream s ⟨'\uFEFF' :: rest, col⟩ ev) :
    RepairedStream s ⟨rest, col⟩ ev := by
  simpa only [List.append_nil] using
    (RepairedStream.prefixContinue s ⟨'\uFEFF' :: rest, col⟩ ⟨rest, col⟩ ⟨rest, col⟩
      ev [] h
      (.cons _ _ _ (.bom rest col ⟨rest, col⟩ (.nil _)) (.nil _))
      (.nil _))

/-- Every newly appended document on the unmarked arm begins at `---`.
Bare nodes, anchors, aliases, and directive documents cannot occupy this slot. -/
lemma explicit_starts_marker {s t : SurfPos} {ev : List Event}
    (h : TLExplicitDocument s t ev) : ∃ rest, s = ⟨'-' :: '-' :: '-' :: rest, 0⟩ := by
  cases h with
  | withContent =>
    rename_i hm _
    cases hm
    exact ⟨_, rfl⟩

lemma alias_not_explicit (rest : List Char) (col : Nat) (t : SurfPos) (ev : List Event) :
    ¬ TLExplicitDocument ⟨'*' :: rest, col⟩ t ev := by
  intro h
  cases h with
  | withContent =>
    rename_i hm _
    cases hm

lemma anchor_not_explicit (rest : List Char) (col : Nat) (t : SurfPos) (ev : List Event) :
    ¬ TLExplicitDocument ⟨'&' :: rest, col⟩ t ev := by
  intro h
  cases h with
  | withContent =>
    rename_i hm _
    cases hm

lemma directive_not_explicit (rest : List Char) (col : Nat) (t : SurfPos) (ev : List Event) :
    ¬ TLExplicitDocument ⟨'%' :: rest, col⟩ t ev := by
  intro h
  cases h with
  | withContent =>
    rename_i hm _
    cases hm

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

private lemma explicit_empty_after (rest : List Char) (q : SurfPos)
    (hc : SSLComments ⟨rest, 3⟩ q) :
    TLExplicitDocument ⟨'-' :: '-' :: '-' :: rest, 0⟩ q [.beginDocument] :=
  .withContent _ _ _ [] (.mk rest)
    (.right _ _ [] (.mk _ _ _ [] [] ⟨.mk _, rfl⟩ ⟨hc, rfl⟩))

/-- Concrete positive: a single empty explicit document survives. -/
lemma explicit_empty : RepairedStream ⟨['-', '-', '-'], 0⟩ ⟨[], 3⟩ [.beginDocument] := by
  exact explicit_preserved (empty_at _) (explicit_empty_after [] _ (eofComments 3))

/-- Concrete positive: `---\n---` is still two explicit documents, with both
document-start events retained. -/
lemma two_explicit :
    RepairedStream ⟨['-', '-', '-', '\n', '-', '-', '-'], 0⟩ ⟨[], 3⟩
      [.beginDocument, .beginDocument] := by
  have hfirst := explicit_empty_after ['\n', '-', '-', '-'] ⟨['-', '-', '-'], 0⟩
    (SSLComments.withComment _ _ _
      (.noSep _ _ (.break _ _ (.lf ['-', '-', '-'] 3))) (.nil _))
  have hstart := explicit_preserved (empty_at _) hfirst
  exact explicit_preserved hstart (explicit_empty_after [] _ (eofComments 3))

/-- Concrete positive: a standalone BOM continuation remains possible. -/
lemma standalone_bom : RepairedStream ⟨['\uFEFF'], 0⟩ ⟨[], 0⟩ [] :=
  bom_preserved [] 0 (empty_at _)

/-- Concrete positive: a standalone empty comment line remains possible. -/
lemma standalone_comment : RepairedStream ⟨['#', '\n'], 0⟩ ⟨[], 0⟩ [] := by
  apply comment_preserved (empty_at _)
  exact SLComment.mk _ _ _ _ (.startOfLine _)
    (.some _ _ (.mk ['\n'] 0 _ (.nil _)))
    (.break _ _ (.lf [] 1))

end

end MathGraph.TraceExplicitRepairAudit

#print axioms MathGraph.TraceExplicitRepairAudit.embeds_old
#print axioms MathGraph.TraceExplicitRepairAudit.unmarkedContinue
#print axioms MathGraph.TraceExplicitRepairAudit.single_preserved
#print axioms MathGraph.TraceExplicitRepairAudit.suffix_then_bare_preserved
#print axioms MathGraph.TraceExplicitRepairAudit.comment_preserved
#print axioms MathGraph.TraceExplicitRepairAudit.bom_preserved
#print axioms MathGraph.TraceExplicitRepairAudit.explicit_starts_marker
#print axioms MathGraph.TraceExplicitRepairAudit.alias_not_explicit
#print axioms MathGraph.TraceExplicitRepairAudit.anchor_not_explicit
#print axioms MathGraph.TraceExplicitRepairAudit.directive_not_explicit
#print axioms MathGraph.TraceExplicitRepairAudit.explicit_empty
#print axioms MathGraph.TraceExplicitRepairAudit.two_explicit
#print axioms MathGraph.TraceExplicitRepairAudit.standalone_bom
#print axioms MathGraph.TraceExplicitRepairAudit.standalone_comment
