/-
Group 7.7 admission test on unchanged integration 14eb6dba.

The actual duplicate-TAG scanner output satisfies BOTH premises of the
existing token-parser completeness theorem.  The theorem itself therefore
supplies acceptance of the offending token stream.  A replacement token
parser cannot reject this stream while retaining that unchanged contract.

The independent requirement below reads explicit TAG handles directly from
tokens and preserves their multiplicity.  It does not run a parser and is
not a definition of the complete YAML language.  The owner blueprint keeps
the source-level Group 7.7 capstone open; this test concerns the already
proved token-level consumer, not an assertion that Group 7.7 was completed.
-/
module

public import L4YAML.Proofs.Parser.StreamCompleteness
public import Tests.Guards.Proofs.TagDirectiveContract
public meta import L4YAML.Proofs.Parser.TokenGrammar
import all Init.Data.Range.Basic

@[expose] public section

namespace L4YAML.Tests.Guards.TagDirectiveCompleteness

open L4YAML
open L4YAML.Proofs.TokenGrammar
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-- The actual scanner output. The success equality below excludes the
fallback; no hand-constructed token stream substitutes for the scanner. -/
def duplicateTokens : Array (Positioned YamlToken) :=
  match Scanner.scanFiltered TagDirectiveContract.duplicate with
  | .ok ts => ts
  | .error _ => #[]

/-- Explicit TAG handles in each boundary-delimited directive window.
`---` closes the preceding directive run; `...` separates documents.
Empty windows are harmless. This extraction is independent of parsing and
of `tokenEvents`, and retains primary, secondary and named declarations. -/
def tagDirectiveWindows : List YamlToken → List String → List (List String)
  | [], pending => [pending.reverse]
  | .tagDirective h _ :: rest, pending => tagDirectiveWindows rest (h :: pending)
  | .documentStart :: rest, pending => pending.reverse :: tagDirectiveWindows rest []
  | .documentEnd :: rest, pending => pending.reverse :: tagDirectiveWindows rest []
  | _ :: rest, pending => tagDirectiveWindows rest pending

/-- No repeated explicit TAG handle within a directive window. This is the
section 6.8.2 uniqueness requirement for the grammatical streams in this
experiment; malformed placement is a separate grammar obligation. -/
def TokenTagDirectivesUnique (ts : Array (Positioned YamlToken)) : Prop :=
  ∀ hs ∈ tagDirectiveWindows (ts.toList.map Positioned.val) [], hs.Nodup

-- Boundary controls before the admission proofs. Different handles may share
-- a prefix; the same handle may recur in a later document. Builtin handles
-- count only when explicitly declared, rather than being pre-seeded here.
#guard tagDirectiveWindows [] [] = [[]]
#guard tagDirectiveWindows [.tagDirective "!" "!x", .documentStart] [] = [["!"], []]
#guard tagDirectiveWindows [.tagDirective "!" "!x", .tagDirective "!" "!x", .documentStart] [] = [["!", "!"], []]
#guard tagDirectiveWindows [.tagDirective "!h!" "!x", .tagDirective "!g!" "!x", .documentStart] [] = [["!h!", "!g!"], []]
#guard tagDirectiveWindows [.tagDirective "!h!" "!x", .documentStart,
    .documentEnd, .tagDirective "!h!" "!y", .documentStart] [] = [["!h!"], [], ["!h!"], []]
#guard checkTokenGrammar duplicateTokens
#guard checkFrom {} (tokenEvents duplicateTokens)

lemma duplicate_scan_exact :
    Scanner.scanFiltered TagDirectiveContract.duplicate = .ok duplicateTokens := by
  cbv

lemma duplicate_token_grammar : TokenGrammar duplicateTokens :=
  checkTokenGrammar_sound (by cbv)

lemma duplicate_token_state : TokenStateOk duplicateTokens := by
  have hevents : tokenEvents duplicateTokens = [.beginDocument] := by
    have h := TagDirectiveContract.duplicate_actual_trace
    simpa only [TagDirectiveContract.scanEvents, duplicate_scan_exact, Option.some.injEq] using h
  change SerializationWellFormed (tokenEvents duplicateTokens)
  rw [hevents]
  exact TagDirectiveContract.actual_trace_well_formed

lemma duplicate_directive_windows :
    tagDirectiveWindows (duplicateTokens.toList.map Positioned.val) [] = [["!", "!"], []] := by
  cbv

lemma duplicate_directive_requirement_false : ¬ TokenTagDirectivesUnique duplicateTokens := by
  simp [TokenTagDirectivesUnique, duplicate_directive_windows]

/-- The existing, production token-completeness theorem is the consumer.
Its actual premises are proved above; neither is an unpaid hypothesis. -/
lemma existing_completeness_accepts_duplicate :
    ∃ docs, TokenParser.parseStream duplicateTokens = .ok docs :=
  parseStream_accepts duplicateTokens duplicate_token_grammar duplicate_token_state

/-- No replacement parser can retain the original token-completeness
guarantee and reject this particular duplicate-directive stream. -/
lemma no_complete_replacement_rejects_duplicate :
    ¬ ∃ replacement : Array (Positioned YamlToken) → Except ScanError (Array YamlDocument),
      (∀ ts, TokenGrammar ts → TokenStateOk ts →
        ∃ docs, replacement ts = .ok docs) ∧
      (replacement duplicateTokens).isOk = false := by
  intro ⟨replacement, hcomplete, hreject⟩
  obtain ⟨docs, hok⟩ :=
    hcomplete duplicateTokens duplicate_token_grammar duplicate_token_state
  rw [hok] at hreject
  contradiction

/-- The same obstruction stated using the independent token requirement.
This concerns the unchanged token premises. A repaired source predicate,
stronger token premise, or intentionally narrower token API remains possible. -/
lemma no_complete_replacement_enforces_directive_uniqueness :
    ¬ ∃ replacement : Array (Positioned YamlToken) → Except ScanError (Array YamlDocument),
      (∀ ts, TokenGrammar ts → TokenStateOk ts →
        ∃ docs, replacement ts = .ok docs) ∧
      (∀ ts docs, replacement ts = .ok docs → TokenTagDirectivesUnique ts) := by
  intro ⟨replacement, hcomplete, hsound⟩
  obtain ⟨docs, hok⟩ :=
    hcomplete duplicateTokens duplicate_token_grammar duplicate_token_state
  exact duplicate_directive_requirement_false (hsound duplicateTokens docs hok)

#print axioms duplicate_scan_exact
#print axioms duplicate_token_grammar
#print axioms duplicate_token_state
#print axioms duplicate_directive_windows
#print axioms duplicate_directive_requirement_false
#print axioms existing_completeness_accepts_duplicate
#print axioms no_complete_replacement_rejects_duplicate
#print axioms no_complete_replacement_enforces_directive_uniqueness

end L4YAML.Tests.Guards.TagDirectiveCompleteness

end
