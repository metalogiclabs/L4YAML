module

public import L4YAML.Proofs.Parser.StreamCompleteness
import all L4YAML.Proofs.Serialization.TokenEvents
public meta import Lean

/-! Reusable parser-premise bridge for scalar and recursive flow sequence
token images. It reads actual token positions and never invokes the parser
to establish the grammar premise. -/

@[expose] public section
namespace MathGraph.WholeSource.FlowTokenBridge

open L4YAML L4YAML.TokenParser L4YAML.Proofs.TokenGrammar
open L4YAML.Proofs.Serialization.TokenEvents (tokenEvent tokenEvents go)

/-- Structural token image. Nodes are positive-width, and their first token
is determined by the scalar or sequence constructor. -/
inductive Shape (ts : Toks) : Sym → Nat → Nat → Prop where
  | scalar {i text style} : tok ts i = some (.scalar text style) →
      Shape ts .node i (i + 1)
  | seq {i k} : tok ts i = some .flowSequenceStart →
      Shape ts (.flowSeqItems true) (i + 1) k →
      tok ts k = some .flowSequenceEnd → Shape ts .node i (k + 1)
  | done {first i} : tok ts i = some .flowSequenceEnd → Shape ts (.flowSeqItems first) i i
  | trailing {i} : tok ts i = some .flowEntry → tok ts (i + 1) = some .flowSequenceEnd →
      Shape ts (.flowSeqItems false) i (i + 1)
  | first {i m k} : Shape ts .node i m → Shape ts (.flowSeqItems false) m k →
      Shape ts (.flowSeqItems true) i k
  | more {i m k} : tok ts i = some .flowEntry → Shape ts .node (i + 1) m →
      Shape ts (.flowSeqItems false) m k → Shape ts (.flowSeqItems false) i k

private lemma node_head {ts : Toks} {i j : Nat} (h : Shape ts .node i j) :
    (∃ text style, tok ts i = some (.scalar text style)) ∨ tok ts i = some .flowSequenceStart := by
  cases h with
  | scalar h => exact Or.inl ⟨_, _, h⟩
  | seq h _ _ => exact Or.inr h

private lemma node_progress {ts : Toks} {i j : Nat} (h : Shape ts .node i j) : i < j := by
  have aux {sym i j} (h : Shape ts sym i j) : i ≤ j := by
    induction h <;> omega
  cases h with
  | scalar _ => omega
  | seq _ h _ => have := aux h; omega

private lemma node_of_content {ts : Toks} {i j : Nat} (hProp : isProp (tok ts i) = false)
    (h : TG ts (.content (isSeqEntryAt ts i)) i j) : TG ts .node i j :=
  .node (.props_none hProp) (by intro hlt; omega) h

lemma Shape.toTG {ts : Toks} {sym : Sym} {i j : Nat} (h : Shape ts sym i j) : TG ts sym i j := by
  induction h with
  | scalar h => exact node_of_content (by simp [h, isProp]) (.content_scalar h)
  | seq h _ hc ih =>
    exact node_of_content (by simp [h, isProp]) (.content_flowSeq (.flowSeq h ih hc))
  | done h => exact .flowSeqItems_end h
  | trailing hc he => exact .flowSeqItems_trailing hc he
  | first hn _ ihn ihrest =>
    obtain ⟨_, _, h⟩ | h := node_head hn <;>
      exact .flowSeqItems_node (by simp [h]) (Or.inl ⟨rfl, rfl⟩)
        (by simp [h]) (by simp [h]) ihn ihrest
  | more hc hn _ ihn ihrest =>
    obtain ⟨_, _, h⟩ | h := node_head hn <;>
      exact .flowSeqItems_node (by simp [hc]) (Or.inr ⟨rfl, hc, rfl⟩)
        (by simp [h]) (by simp [h]) ihn ihrest

lemma single_document_grammar {ts : Toks} {j : Nat}
    (hStart : tok ts 0 = some .streamStart) (hNode : Shape ts .node 1 j)
    (hEnd : tok ts j = some .streamEnd) (hSize : j + 1 = ts.size) : TokenGrammar ts := by
  have hProgress := node_progress hNode
  obtain ⟨_, _, h⟩ | h := node_head hNode <;>
    exact ⟨hStart, j, .stream_doc h (by simp) (by simp) rfl
      (.document (.directives_nil (by simp [h, isDirective]))
        (Or.inr ⟨by simp [h], rfl, rfl⟩) hNode.toTG)
      hProgress (by simp [hEnd]) (.stream_end (Or.inl hEnd)), hSize⟩

/-- A local sufficient state condition for the event-free fragment. -/
def Quiet (v : YamlToken) : Prop :=
  tokenEvent v = none ∧ v ≠ .documentStart ∧ ∀ handle pfx, v ≠ .tagDirective handle pfx

lemma quiet_values_state {ts : Toks} {values : List YamlToken}
    (hValues : ts.toList.map (·.val) = values) (hQuiet : ∀ v ∈ values, Quiet v) :
    TokenStateOk ts := by
  have hGo (xs : List (Positioned YamlToken))
      (hq : ∀ v ∈ xs.map (·.val), Quiet v) : go xs [] = [] := by
    induction xs with
    | nil => simp [go]
    | cons t rest ih =>
      have ht := hq t.val (by simp)
      have hr := ih (by intro v hv; exact hq v (by simp [hv]))
      unfold go
      split
      · rename_i handle pfx heq
        exact False.elim (ht.2.2 handle pfx heq)
      · rename_i heq
        exact False.elim (ht.2.1 heq)
      · rename_i v heq
        rw [ht.1]
        exact hr
  have he : tokenEvents ts = [] := hGo ts.toList (by simpa only [hValues] using hQuiet)
  unfold TokenStateOk
  rw [he]
  trivial

#print axioms single_document_grammar
#print axioms quiet_values_state

end MathGraph.WholeSource.FlowTokenBridge
