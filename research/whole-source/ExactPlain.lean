module

public import ExactQuoted
public import L4YAML.Proofs.Production.Acceptance.Plain
public meta import Lean

/-! Group 7.7: YAML 1.2.2 [126]–[135], pinned in source-bridge-map.json.
The existing one-line rules carry colon lookahead in [130] and encode
hash adjacency by a separate entry with no preceding whitespace. Reuse
those rules and the checked [74] folding relation. The source endpoints
delimit a grammatical span. Its owning node or stream still has to
supply maximal landing, delimiter and forbidden-marker conditions. -/

set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactPlain

open L4YAML L4YAML.Surface L4YAML.CharPredicates L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.Acceptance
open MathGraph.WholeSource.ExactQuoted

/-- [134]. The continuation starts after a line break and optional whitespace,
so its first content character cannot take [130]'s hash-lookbehind arm. -/
abbrev NextLine (n : Nat) (ctx : YamlContext) :=
  GSeq3 (FlowFolded n) (SNsPlainChar ctx) (GStar (SNbNsPlainInLineEntry ctx))

/-- [135]. -/
abbrev MultiLine (n : Nat) (ctx : YamlContext) :=
  GSeq (SNsPlainOneLine ctx) (GStar (NextLine n ctx))

/-- [131]. Only the four contexts in the production have derivations. -/
def Plain (n : Nat) (ctx : YamlContext) : SurfPos → SurfPos → Prop :=
  match ctx with
  | .flowOut | .flowIn => MultiLine n ctx
  | .blockKey | .flowKey => SNsPlainOneLine ctx
  | .blockOut | .blockIn => fun _ _ => False

/-- The context partition for [127]. Outer callers still enforce [131]. -/
def flowSafeContext (ctx : YamlContext) : Bool :=
  match ctx with
  | .flowIn | .flowKey => true
  | _ => false

private lemma safe_iff (ctx : YamlContext) (ch : Char) :
    isPlainSafeBool ch (flowSafeContext ctx) = true ↔ isNsPlainSafe ctx ch := by
  rw [isPlainSafe_iff]
  cases ctx <;> simp only [flowSafeContext, isPlainSafeProp, isNsPlainSafe,
    isNsChar, Bool.false_eq_true, ite_false, ite_true] <;> simp only [and_assoc, and_comm, and_left_comm]

private lemma first_to_guarded {ctx : YamlContext} {s t : SurfPos}
    (h : SNsPlainFirst ctx s t) :
    PlainFirstOk (flowSafeContext ctx) s t ∧ 0 < t.col := by
  cases h with
  | nonIndicator ch rest col hs hi =>
    exact ⟨.nonIndicator ch rest col ((safe_iff ctx ch).mpr hs)
      (Bool.eq_false_iff.mpr (fun h => hi ((isIndicator_iff ch).mp h))), by simp⟩
  | dashSafe ch rest col hs =>
    exact ⟨.indicator '-' ch rest col (Or.inl rfl) ((safe_iff ctx ch).mpr hs), by simp⟩
  | colonSafe ch rest col hs =>
    exact ⟨.indicator ':' ch rest col (Or.inr (Or.inr rfl)) ((safe_iff ctx ch).mpr hs), by simp⟩
  | questionSafe ch rest col hs =>
    exact ⟨.indicator '?' ch rest col (Or.inr (Or.inl rfl)) ((safe_iff ctx ch).mpr hs), by simp⟩

private lemma char_to_guarded {ctx : YamlContext} {s t : SurfPos} (afterWhite : Bool)
    (h : SNsPlainChar ctx s t) :
    PlainCharOk (flowSafeContext ctx) afterWhite s t ∧ 0 < t.col := by
  cases h with
  | safe ch rest col hs hc hh =>
    exact ⟨.safe afterWhite ch rest col ((safe_iff ctx ch).mpr hs) hc hh, by simp⟩
  | colonSafe _ ch rest col hs =>
    exact ⟨.colonSafe afterWhite ch rest col ((safe_iff ctx ch).mpr hs), by simp⟩

private lemma entries_to_guarded {ctx : YamlContext} {s t : SurfPos}
    (h : GStar (SNbNsPlainInLineEntry ctx) s t) (hCol : 0 < s.col) :
    GStar (PlainEntryOk (flowSafeContext ctx)) s t := by
  induction h with
  | nil => exact .nil _
  | cons s u t he _ ih =>
    cases he with
    | mk mid _ hWhite hChar =>
      cases hWhite with
      | nil =>
        obtain ⟨hStep, hPos⟩ := char_to_guarded false hChar
        exact .cons _ _ _ (.noWhite _ _ hStep) (ih hPos)
      | cons _ _ _ hFirst hRest =>
        obtain ⟨hStep, hPos⟩ := char_to_guarded true hChar
        exact .cons _ _ _ (.white _ mid _ (.mk _ _ _ hFirst hRest) hStep) (ih hPos)
    | hash _ hHash =>
      cases hHash with
      | mk rest col =>
        exact .cons _ _ _ (.noWhite _ _ (.hash rest col hCol)) (ih (by simp))

/-- A grammatical one-line span supplies the existing scanner's content
premise. The scanner landing still needs its separate stop premise. -/
lemma one_line_to_guarded {ctx : YamlContext} {s t : SurfPos}
    (h : SNsPlainOneLine ctx s t) :
    PlainOneLineOk (flowSafeContext ctx) s t := by
  cases h with
  | mk _ _ hFirst hEntries =>
    obtain ⟨hGuarded, hCol⟩ := first_to_guarded hFirst
    exact .mk _ _ _ hGuarded (entries_to_guarded hEntries hCol)

/-- One-line flow content followed by a flow indicator yields the actual
plain scanner's landing and token append. Horizontal separation can be
consumed by the scanner while remaining outside the scalar's source span. -/
lemma scan_flow_plain_to_indicator (sc : ScannerState) {s contentEnd landing : SurfPos}
    {ctx : YamlContext} (hCtx : ctx = .flowIn ∨ ctx = .flowKey)
    (hCorr : ScannerSurfCorr sc s) (hFlow : sc.inFlow = true)
    (hSpan : SNsPlainOneLine ctx s contentEnd)
    (hWhite : GStar SSWhite contentEnd landing)
    (hIndicator : ∃ c rest, landing.chars = c :: rest ∧ isFlowIndicatorProp c)
    (hDoc : sc.col = 0 → atDocumentBoundary sc = false) :
    ∃ next value, scanPlainScalar sc = .ok next ∧ ScannerSurfCorr next landing ∧
      next.tokens = sc.tokens.push {pos := sc.currentPos, val := .scalar value .plain} := by
  have hContent : PlainOneLineOk sc.inFlow s contentEnd := by
    rw [hFlow]
    rcases hCtx with rfl | rfl <;> exact one_line_to_guarded hSpan
  have hStop : PlainStopOk sc.inFlow false landing.chars := by
    obtain ⟨c, rest, hChars, hInd⟩ := hIndicator
    rw [hChars]
    exact Or.inr (Or.inr (Or.inl ⟨hFlow, (isFlowIndicator_iff c).mpr hInd⟩))
  exact scanPlainScalar_accepts sc hCorr hContent hWhite hStop (fun h => Bool.noConfusion h) hDoc

end MathGraph.WholeSource.ExactPlain
