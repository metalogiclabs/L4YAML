/-
MathGraph Right-Wall: native directive transition preserves eligible token history.
The source and event contracts are taken from the actual scanner lemmas,
not invented as a free route or a new scanner axiom.
Imported from 09eeb316225759a67aad88aec59fbabd5eac38b7, whose parent is
ea3fc8626ceb3d4f7b7326978898d30d520b0ddf. Current integration starts at 0629c303.
-/
module

public import Tests.Guards.Proofs.RightWallTokenHistory
public import L4YAML.Proofs.Scanner.DirectiveRuns

@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.RightWallHistory

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.DirectiveRuns
open L4YAML.Proofs.CouplingBridge (ScannerSurfCorr)
open L4YAML.Proofs.Serialization.TraceOf.DocBridge (scanDirective_trace)

/-- Every emitted directive token is event-silent and is not a document start. -/
lemma directive_token_nonemitting {v : YamlToken}
    (h : isDirTok (some v) = true) : NonEmitting v := by
  cases v <;> simp_all [isDirTok, NonEmitting,
    L4YAML.Proofs.Serialization.TokenEvents.tokenEvent]

/-- Event-silent additions, of any finite length, preserve either lawful
    eligible history alternative. -/
lemma eligibleHistory_append_nonemitting_list
    (pfx sfx : List (Positioned YamlToken))
    (h : EligibleHistory pfx)
    (hSilent : ∀ t ∈ sfx, NonEmitting t.val) :
    EligibleHistory (pfx ++ sfx) := by
  induction sfx generalizing pfx with
  | nil => simpa using h
  | cons t rest ih =>
    have ht : NonEmitting t.val := hSilent t (by simp)
    have hRest : ∀ u ∈ rest, NonEmitting u.val := by
      intro u hu
      exact hSilent u (by simp [hu])
    have h1 := eligibleHistory_append_nonemitting pfx t h ht
    simpa [List.append_assoc] using ih (pfx ++ [t]) h1 hRest

/-- The real native `scanDirective` transition never falsifies eligible
    token-history provenance.  The scanner's token production and S-side
    directive classification are both checked; arbitrary event-producing
    token additions are not assumed away. -/
lemma native_scanDirective_preserves_eligible_history
    (sc sc' : ScannerState) (sp : SurfPos)
    (hCorr : ScannerSurfCorr sc sp)
    (hPeek : sc.peek? = some '%')
    (hScan : scanDirective sc = .ok sc')
    (hHistory : EligibleHistory sc.tokens.toList) :
    EligibleHistory sc'.tokens.toList := by
  obtain ⟨stop, hSource, hCorr', hTail, new, hTokens, hEvents, hStable⟩ :=
    scanDirective_trace sc sp hCorr hPeek sc' hScan
  have hValues : vals sc' = vals sc ++ new.map Positioned.val := by
    simp [vals, toks, hTokens, List.map_append]
  have hCase := (scanDirective_fields sc sc' hScan).1
  have hNew : ∀ t ∈ new, NonEmitting t.val := by
    intro t ht
    have hMember : t.val ∈ new.map Positioned.val :=
      List.mem_map.mpr ⟨t, ht, rfl⟩
    rcases hCase with hSame | ⟨d, hOne, hDir⟩
    · have hNil : new.map Positioned.val = [] := by
        have hEq : vals sc ++ new.map Positioned.val =
            vals sc ++ ([] : List YamlToken) := by
          simpa only [List.append_nil] using hValues.symm.trans hSame
        exact List.append_cancel_left hEq
      rw [hNil] at hMember
      simp at hMember
    · have hSingle : new.map Positioned.val = [d] := by
        have hEq : vals sc ++ new.map Positioned.val = vals sc ++ [d] :=
          hValues.symm.trans hOne
        exact List.append_cancel_left hEq
      have hVal : t.val = d := by
        simpa [hSingle] using hMember
      simpa [hVal] using directive_token_nonemitting hDir
  rw [hTokens]
  exact eligibleHistory_append_nonemitting_list sc.tokens.toList new hHistory hNew

#print axioms directive_token_nonemitting
#print axioms eligibleHistory_append_nonemitting_list
#print axioms native_scanDirective_preserves_eligible_history

end L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
end Blanket
