module
public import DirectiveTransfer
public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition

/-!
# Original-source YAML directive dispatch

Capstone path: source version syntax → actual directive dispatch → actual
parser declaration consumption → Group 7.7 grammar completeness.
The TAG and version-body antecedents remain unchanged. Scope: one ASCII-space
separator, nonempty digit runs, LF termination and an unrestricted suffix.
Numeric decoding is the runtime's toNat!, not an independent decimal theorem.
-/
namespace MathGraph.WholeSource.DirectiveDispatch
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open MathGraph.WholeSource.DirectiveBridge
open MathGraph.WholeSource.DirectiveTransfer

private def accepts (input : String) : Bool :=
  (L4YAML.TokenParser.parseYaml input).toOption.isSome
#guard accepts "%YAML 1.2\n---" = true
#guard accepts "%YAML 1.2\n--- café" = true
#guard accepts "%YAML .2\n---" = false
#guard accepts "%YAML 1.\n---" = false
#guard accepts "%YAML 1.2\n%YAML 1.2\n---" = false
#guard accepts "%YAML 1.2\n---\n...\n%YAML 1.2\n---" = true

lemma digit_not_white {c : Char} (hd : isNsDecDigit c) : ¬ isWhiteSpaceProp c := by
  intro hw
  simp only [isWhiteSpaceProp, isSpaceProp, isTabProp, beq_iff_eq] at hw
  rcases hw with rfl | rfl <;> simp [isNsDecDigit] at hd

/-- Reuse the name/whitespace/body capabilities at the actual dispatcher.
All preexisting tokens are retained; the exact version token is appended. -/
lemma yaml_dispatch (sc : ScannerState) (major minor rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcorr : ScannerSurfCorr sc
      ⟨'%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' :: (major ++ '.' :: (minor ++ '\n' :: rest)), 0⟩)
    (hallow : sc.allowDirectives = true) (hseen : sc.seenYamlDirective = false) :
    ∃ out, scanDirective sc = .ok out ∧
      ScannerSurfCorr out ⟨'\n' :: rest, 6 + major.length + 1 + minor.length⟩ ∧
      out.tokens = sc.tokens.push { pos := sc.currentPos, val := .versionDirective (String.ofList major).toNat! (String.ofList minor).toNat! } ∧
      out.seenYamlDirective = true ∧ out.directivesPresent = true := by
  let body := major ++ '.' :: (minor ++ '\n' :: rest)
  have hcadv := advance_corr hcorr (by decide) (by decide)
  have hnameSyntax : LexRun isNsChar ['Y','A','M','L']
      ⟨'Y' :: 'A' :: 'M' :: 'L' :: ' ' :: body, 1⟩ ⟨' ' :: body, 5⟩ := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> unfold isNsChar <;> decide
    · intro c hc
      simp only [List.head?_cons, Option.some.injEq] at hc
      subst c
      intro hn
      exact hn.2.1 (by decide)
  have hfuel := fuel_of_corr hcadv
  have hiadv := (keeps_advance sc).2.1
  obtain ⟨name, sc₁, hname, hn, hc₁, hk₁⟩ := collectDirectiveNameLoop_accepts
    hnameSyntax sc.advance hcadv (sc.inputEnd - sc.advance.offset) (by
      simpa only [body, hiadv] using hfuel)
  have hn' : name = "YAML" := by simpa using hn
  subst name
  have hsep : LexRun isWhiteSpaceProp [' '] ⟨' ' :: body, 5⟩ ⟨body, 6⟩ := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro c hc; simp only [List.mem_singleton] at hc; subst c; decide
    · cases major with
      | nil => exact False.elim (hneMa rfl)
      | cons c cs =>
        intro d hd
        simp only [body, List.cons_append, List.head?_cons, Option.some.injEq] at hd
        subst d
        exact digit_not_white (hma c (by simp))
  obtain ⟨hc₂, hk₂⟩ := whitespace_accepts hsep sc₁ hc₁
  have hlim : sc.inputEnd = (skipWhitespace sc₁).inputEnd := by
    rw [hk₂.2.1, hk₁.2.1, hiadv]
  obtain ⟨out, hok, hco, htok, hs, hd⟩ := yaml_body_before_lf sc (skipWhitespace sc₁)
    major minor rest hma hmi hneMa hneMi 6 hc₂ hlim hseen
  refine ⟨out, ?_, hco, ?_, hs, hd⟩
  · unfold scanDirective
    simp only [hallow, Bool.not_true, Bool.false_eq_true, ite_false, hname]
    simp only [show ("YAML" == "YAML") = true from rfl, ite_true, hok]
    rw [skipToEndOfLine_of_ending hco (Or.inr (Or.inl rfl))]
  · rw [htok, hk₂.1, hk₁.1, (keeps_advance sc).1]

/-- Initial original-input consumer; no scanner-success/correspondence premise. -/
lemma original_yaml_dispatch (input : String) (major minor rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ '\n' :: rest))) :
    ∃ out, scanDirective (ScannerState.mk' input) = .ok out ∧
      out.tokens = #[{ pos := (ScannerState.mk' input).currentPos, val := .versionDirective (String.ofList major).toNat! (String.ofList minor).toNat! }] ∧
      out.seenYamlDirective = true ∧ out.directivesPresent = true := by
  have hc := initial_corr input input.toList (chars_from_zero_toList input)
  rw [hsource] at hc
  obtain ⟨out, hok, _, ht, hs, hd⟩ := yaml_dispatch (ScannerState.mk' input)
    major minor rest hma hmi hneMa hneMi hc rfl rfl
  exact ⟨out, hok, by simpa [ScannerState.mk'] using ht, hs, hd⟩

/-- Actual parser consumption for an arbitrary version token. -/
lemma parser_consumes_version (major minor : Nat) (pos : YamlPos) :
    (L4YAML.TokenParser.parseDirectives
      (L4YAML.TokenParser.ParseState.mk' #[{ pos := pos, val := .versionDirective major minor }])).1 =
      #[.yaml (toString major ++ "." ++ toString minor)] := by
  unfold L4YAML.TokenParser.parseDirectives
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size, List.forIn_cons,
    L4YAML.TokenParser.ParseState.mk', L4YAML.TokenParser.ParseState.peek?,
    L4YAML.TokenParser.ParseState.advance, bind, pure]

/-- Original source through full directive dispatch into the actual parser's
version declaration. The trailing source is not parsed by this lemma. -/
lemma original_yaml_declaration (input : String) (major minor rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ '\n' :: rest))) :
    ∃ out, scanDirective (ScannerState.mk' input) = .ok out ∧
      (L4YAML.TokenParser.parseDirectives (L4YAML.TokenParser.ParseState.mk' out.tokens)).1 =
        #[.yaml (toString (String.ofList major).toNat! ++ "." ++ toString (String.ofList minor).toNat!)] := by
  obtain ⟨out, hok, ht, _, _⟩ := original_yaml_dispatch input major minor rest hma hmi hneMa hneMi hsource
  refine ⟨out, hok, ?_⟩
  rw [ht]
  exact parser_consumes_version _ _ _

#print axioms yaml_dispatch
#print axioms original_yaml_dispatch
#print axioms parser_consumes_version
#print axioms original_yaml_declaration
end
end MathGraph.WholeSource.DirectiveDispatch
