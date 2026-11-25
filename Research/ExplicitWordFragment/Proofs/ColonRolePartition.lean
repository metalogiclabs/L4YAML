module
public import L4YAML.Proofs.Scanner.ExplicitKeyCoupling
public import L4YAML.Parser.Composition
public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Parser.Composition
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.ColonRolePartition
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.ExplicitKeyCoupling

/-- Explicitly preserve the alternative in the existing preprocessing theorem.
    It is not licensed to silently identify a re-read register with the old one. -/
def StaleAt (s s1 : ScannerState) : Prop :=
  s.explicitKeyLine ≠ none ∧
    ∃ (t : ScannerState) (c' : Char), t.peek? = some c' ∧
      s1 = (t.closeStaleAt c').readPendingKey

/-- The matching coordinate follows on the un-stamped, retained-register route.
    The actual scanner chain yields a partition, not unconditional equality.
    The stamp or either stale-register path must remain visible to a consumer. -/
lemma scalar_colon_role_partition
    {q sc prep ad k v out : ScannerState} {c : Char}
    (hq : scanKey q = .ok sc)
    (hpre : scanNextToken_preprocess sc = .ok (some (prep, c)))
    (had : ad = if prep.allowDirectives then
      { prep with allowDirectives := false, documentEverStarted := true } else prep)
    (hdispatch : scanNextToken_dispatchContent ad c = .ok k)
    (hvpre : scanNextToken_preprocess k = .ok (some (v, ':')))
    (hv : scanValue v = .ok out)
    (hf : v.inFlow = false)
    (hp : v.peek? = some ':') :
    v.col = q.col ∨ out.implicitValueLine = some out.line ∨
      StaleAt sc prep ∨ StaleAt k v := by
  rcases preprocess_explicitKey_cases sc prep c hpre with h1 | h1
  · rcases preprocess_explicitKey_cases k v ':' hvpre with h2 | h2
    · have ha : ad.explicitKeyCol = prep.explicitKeyCol := by
        rw [had]
        split <;> rfl
      have hk := dispatchContent_preserves_explicitKeyCol ad c k hdispatch
      have hr : v.explicitKeyCol = (q.col : Int) :=
        h2.2.trans (hk.trans (ha.trans (h1.2.trans (scanKey_ok_explicitKey hq).2)))
      by_cases hm : v.col = q.col
      · exact Or.inl hm
      · right
        left
        apply scanValue_stamp_of_col_ne hv hf hp
        rw [hr]
        omega
    · exact Or.inr (Or.inr (Or.inr h2))
  · exact Or.inr (Or.inr (Or.inl h1))

/-- Recover the old coordinate premise only after the actual alternative
    branches have been excluded, never merely from scanner success. -/
lemma matching_column_of_no_stamp_or_stale
    {q sc prep ad k v out : ScannerState} {c : Char}
    (hq : scanKey q = .ok sc)
    (hpre : scanNextToken_preprocess sc = .ok (some (prep, c)))
    (had : ad = if prep.allowDirectives then
      { prep with allowDirectives := false, documentEverStarted := true } else prep)
    (hdispatch : scanNextToken_dispatchContent ad c = .ok k)
    (hvpre : scanNextToken_preprocess k = .ok (some (v, ':')))
    (hv : scanValue v = .ok out)
    (hf : v.inFlow = false)
    (hp : v.peek? = some ':')
    (hn : out.implicitValueLine ≠ some out.line)
    (hs1 : ¬ StaleAt sc prep) (hs2 : ¬ StaleAt k v) :
    v.col = q.col := by
  rcases scalar_colon_role_partition hq hpre had hdispatch hvpre hv hf hp with
    h | h | h | h
  · exact h
  · exact False.elim (hn h)
  · exact False.elim (hs1 h)
  · exact False.elim (hs2 h)

#print axioms scalar_colon_role_partition
#print axioms matching_column_of_no_stamp_or_stale

end L4YAML.Tests.Guards.ColonRolePartition
end Blanket
