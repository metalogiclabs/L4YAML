module
public import Research.R2ScannerMapOwnership.Step

@[expose] public section MapOwnershipReachable

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs
open L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.IndentStackMono (Mono)

namespace R2MapOwnership

-- Exactly scan's initialization, including its actual optional BOM branch.
def seed (input : String) : ScannerState :=
  let s := (ScannerState.mk' input).emit .streamStart
  match s.peek? with
  | some '\uFEFF' => s.consumeBOM
  | _ => s

def prefixes (input : String) : Nat → Option ScannerState
  | 0 => some (seed input)
  | n+1 => (prefixes input n).bind fun s =>
      match scanNextToken s with
      | .ok (some t) => some t
      | _ => none

lemma seed_facts (input : String) :
    Sound (seed input) ∧ Mono (seed input) ∧ SentinelBase (seed input) ∧
      ColFloor.ColFloor (seed input) ∧ Maps (seed input) := by
  have mono : Mono ((ScannerState.mk' input).emit .streamStart) :=
    (IndentStackMono.mk'_mono input).of_indents_eq (ScannerContracts.emit_indents _ _)
  have base : SentinelBase ((ScannerState.mk' input).emit .streamStart) :=
    (IndentStackBase.mk'_base input).of_indents_eq (ScannerContracts.emit_indents _ _)
  have maps : Maps ((ScannerState.mk' input).emit .streamStart) :=
    (Maps.initial input).of_eq rfl rfl
  unfold seed
  dsimp only
  split
  · exact ⟨ColFloor.seed_bom_sound input,
      mono.of_indents_eq (L4YAML.Proofs.ScannerLoopInvariant.advance_indents _),
      base.of_indents_eq (L4YAML.Proofs.ScannerLoopInvariant.advance_indents _),
      ColFloor.seed_bom_colfloor input ‹_›,
      maps.of_eq (L4YAML.Proofs.PendingKeysStable.advance_preserves_pendingKeys _)
        (L4YAML.Proofs.ScannerLoopInvariant.advance_indents _)⟩
  · exact ⟨ColFloor.seed_sound input, mono, base, ColFloor.seed_colfloor input, maps⟩

-- Every successful initialized token prefix, for arbitrary input and length.
-- No map-kind, scanner soundness or route premise is supplied by the caller.
lemma initialized_facts (input : String) (n : Nat) (s : ScannerState)
    (reached : prefixes input n = some s) :
    Sound s ∧ Mono s ∧ SentinelBase s ∧ ColFloor.ColFloor s ∧ Maps s := by
  induction n generalizing s with
  | zero =>
    simp only [prefixes, Option.some.injEq] at reached
    exact reached ▸ seed_facts input
  | succ n ih =>
    simp only [prefixes, Option.bind_eq_some_iff] at reached
    obtain ⟨before, previous, step⟩ := reached
    obtain ⟨sound, mono, base, floor, maps⟩ := ih before previous
    cases scanStep : scanNextToken before with
    | error e => simp [scanStep] at step
    | ok result =>
      cases result with
      | none => simp [scanStep] at step
      | some after =>
        simp only [scanStep, Option.some.injEq] at step
        subst after
        obtain ⟨newSound, newFloor⟩ := ColFloor.scanNextToken_sound_colfloor scanStep sound mono base floor
        exact ⟨newSound, IndentStackMono.scanNextToken_mono scanStep mono base,
          IndentStackBase.scanNextToken_base scanStep base, newFloor,
          maps.next scanStep sound mono base (ColFloor.preprocessFloor floor base)⟩

lemma initialized_maps (input : String) (n : Nat) (s : ScannerState)
    (reached : prefixes input n = some s) : Maps s :=
  (initialized_facts input n s reached).2.2.2.2

lemma seed_maps (input : String) : Maps (seed input) := (seed_facts input).2.2.2.2

example : (prefixes "\uFEFF? a\n: b\n" 3).isSome = true := by decide +kernel
example : (prefixes "? - ? a\n    : b\n  - c\n: d\n" 4).isSome = true := by decide +kernel

#print axioms initialized_facts
#print axioms initialized_maps

end R2MapOwnership

end MapOwnershipReachable
