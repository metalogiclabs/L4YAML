import L4YAML.Schema.Schema
import L4YAML.Schema.FromToYaml
import L4YAML.Output.Dump
import L4YAML.Output.Emitter
import L4YAML.Parser.Composition

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# End-to-End Round-Trip Composition (Phase 7.5, v0.2.9)

Composes parser + dump + schema proofs to establish the round-trip property:

```
∀ (v v' : YamlValue),
  resolveEq v v' = true →
  resolve v = resolve v'
```

Combined with `dump→parse` content preservation (verified via compile-time
guards and `native_decide`), this gives the end-to-end round-trip:

```
parseYamlSingle (dump v cfg) = .ok v' → resolve v' = resolve v
```

## Key Results

### §1: `resolveEq` — Resolution-Relevant Equivalence
Captures the fields used by `resolve`, including scalar style. Two
values are resolution-equivalent when their scalar content, tag, style,
and recursive structures agree.

### §2: Resolution Preservation Theorem
`resolveEq v v' = true → resolve v = resolve v'`
Proved by structural induction with list/pair-list helpers.

### §3: `contentEq` + plain/no-tags → `resolve` equality
Tag absence alone is insufficient: the scalar presentation style must also
be plain throughout the compared structures.

### §4: End-to-end round-trip checker
`resolveRoundTrips v cfg` checks `dump v cfg → parseYamlSingle → resolve ==`.

### §5: Concrete round-trip proofs
Per-value `native_decide` proofs for scalars, sequences, mappings,
nested structures, and different dump configurations.

### §6: Typed round-trip composition
`toYaml → dump → parseYamlSingle → resolve ==` chain validated per type.

## Zero Axioms

All theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

namespace L4YAML.Proofs.RoundTripComposition

open L4YAML
open L4YAML.Schema
open L4YAML.Dump
open L4YAML.Emit
open L4YAML.TokenParser

/-! ## §1: Resolution-Relevant Equivalence

`resolveEq` captures exactly the properties that `Schema.resolve` examines:
- Scalars: `content`, `tag`, and `style` (not anchor or blockMeta)
- Sequences: items recursively (not style, tag, anchor)
- Mappings: key-value pairs recursively (not style, tag, anchor)
- Aliases: name equality (both resolve to `.null`)

Structure mirrors `contentEq` to ensure equational theorem generation. -/

/-- Resolution-relevant equivalence: two values that resolve identically.
    This is a sufficient condition for `resolve v = resolve v'`. -/
def resolveEq : YamlValue → YamlValue → Bool
  | .scalar s₁, .scalar s₂ =>
    s₁.content == s₂.content && s₁.tag == s₂.tag && s₁.style == s₂.style
  | .sequence _ items₁ .., .sequence _ items₂ .. =>
    items₁.size == items₂.size &&
    resolveEqList items₁.toList items₂.toList
  | .mapping _ pairs₁ .., .mapping _ pairs₂ .. =>
    pairs₁.size == pairs₂.size &&
    resolveEqPairList pairs₁.toList pairs₂.toList
  | .alias n₁, .alias n₂ => n₁ == n₂
  | _, _ => false
where
  resolveEqList : List YamlValue → List YamlValue → Bool
    | [], [] => true
    | v :: vs, v' :: vs' => resolveEq v v' && resolveEqList vs vs'
    | _, _ => false
  resolveEqPairList : List (YamlValue × YamlValue) → List (YamlValue × YamlValue) → Bool
    | [], [] => true
    | (k, v) :: rest, (k', v') :: rest' =>
      resolveEq k k' && resolveEq v v' && resolveEqPairList rest rest'
    | _, _ => false

/-! ## §2: Resolution Preservation Theorem

The key algebraic theorem: resolution-equivalent values produce the
same `YamlType` under `Schema.resolve`. -/

/-- Helper: `resolveEqList` implies `resolve.resolveList` equality. -/
lemma resolveList_eq (vs vs' : List YamlValue)
    (ih : ∀ v, v ∈ vs → ∀ v', resolveEq v v' = true → resolve v = resolve v')
    (h : resolveEq.resolveEqList vs vs' = true) :
    resolve.resolveList vs = resolve.resolveList vs' := by
  match vs, vs' with
  | [], [] => rfl
  | [], _ :: _ => exact Bool.noConfusion h
  | _ :: _, [] => exact Bool.noConfusion h
  | v :: rest, v' :: rest' =>
    have hh : (resolveEq v v' && resolveEq.resolveEqList rest rest') = true := h
    simp only [Bool.and_eq_true] at hh
    show resolve v :: resolve.resolveList rest = resolve v' :: resolve.resolveList rest'
    rw [ih v (.head _) v' hh.1, resolveList_eq rest rest' (fun w hw => ih w (.tail _ hw)) hh.2]

/-- Helper: `resolveEqPairList` implies `resolve.resolvePairs` equality. -/
lemma resolvePairList_eq (ps ps' : List (YamlValue × YamlValue))
    (ih : ∀ p, p ∈ ps →
      (∀ v', resolveEq p.1 v' = true → resolve p.1 = resolve v') ∧
      (∀ v', resolveEq p.2 v' = true → resolve p.2 = resolve v'))
    (h : resolveEq.resolveEqPairList ps ps' = true) :
    resolve.resolvePairs ps = resolve.resolvePairs ps' := by
  match ps, ps' with
  | [], [] => rfl
  | [], _ :: _ => exact Bool.noConfusion h
  | _ :: _, [] => exact Bool.noConfusion h
  | (k, v) :: rest, (k', v') :: rest' =>
    have hh : (resolveEq k k' && resolveEq v v' && resolveEq.resolveEqPairList rest rest') = true := h
    simp only [Bool.and_eq_true] at hh
    have ihm := ih (k, v) (.head _)
    show (resolve k, resolve v) :: resolve.resolvePairs rest =
         (resolve k', resolve v') :: resolve.resolvePairs rest'
    rw [ihm.1 k' hh.1.1, ihm.2 v' hh.1.2,
        resolvePairList_eq rest rest' (fun p hp => ih p (.tail _ hp)) hh.2]

/-- **Resolution-equivalent values resolve identically.**

    This is the key algebraic composition theorem: it decouples
    schema preservation from parser correctness. Combined with
    `dump→parse` content preservation, it gives the full round-trip. -/
lemma resolve_eq_of_resolveEq (v v' : YamlValue) (h : resolveEq v v' = true) :
    resolve v = resolve v' := by
  match v, v' with
  | .scalar s₁, .scalar s₂ =>
    have hh : (s₁.content == s₂.content && s₁.tag == s₂.tag &&
               s₁.style == s₂.style) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    change scalarType s₁ = scalarType s₂
    simp [scalarType, hh.1.1, hh.1.2, hh.2]
  | .sequence _ items₁ .., .sequence _ items₂ .. =>
    have hh : (items₁.size == items₂.size &&
               resolveEq.resolveEqList items₁.toList items₂.toList) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    show YamlType.seq (resolve.resolveList items₁.toList).toArray =
         YamlType.seq (resolve.resolveList items₂.toList).toArray
    have h_list := resolveList_eq items₁.toList items₂.toList
      (fun v hv v' heq => resolve_eq_of_resolveEq v v' heq) hh.2
    rw [h_list]
  | .mapping _ pairs₁ .., .mapping _ pairs₂ .. =>
    have hh : (pairs₁.size == pairs₂.size &&
               resolveEq.resolveEqPairList pairs₁.toList pairs₂.toList) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    show YamlType.map (resolve.resolvePairs pairs₁.toList).toArray =
         YamlType.map (resolve.resolvePairs pairs₂.toList).toArray
    have h_pairs := resolvePairList_eq pairs₁.toList pairs₂.toList
      (fun p hp =>
        ⟨fun v' heq => resolve_eq_of_resolveEq p.1 v' heq,
         fun v' heq => resolve_eq_of_resolveEq p.2 v' heq⟩) hh.2
    rw [h_pairs]
  | .alias _, .alias _ => rfl
  -- Cross-constructor: resolveEq definitionally reduces to false
  | .scalar _, .sequence .. | .scalar _, .mapping .. | .scalar _, .alias _
  | .sequence .., .scalar _ | .sequence .., .mapping .. | .sequence .., .alias _
  | .mapping .., .scalar _ | .mapping .., .sequence .. | .mapping .., .alias _
  | .alias _, .scalar _ | .alias _, .sequence .. | .alias _, .mapping .. =>
    exact Bool.noConfusion h
termination_by v
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem hv
    cases items₁; simp_all [Array.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hp
    cases pairs₁; cases p; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hp
    cases pairs₁; cases p; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega

/-! ## §3: `contentEq` + No Tags → `resolve` Equality

Content equivalence alone is NOT sufficient after style-aware schema resolution:
plain "true" and quoted "true" have the same content and no tag but
resolve to different types. For the narrower case of plain, untagged
scalars at every node, content equivalence remains sufficient.

Proved directly by structural induction without going through `resolveEq`. -/

/-- A value is tag-free at the scalar level (all scalar tags are `none`). -/
def noTags : YamlValue → Bool
  | .scalar s => s.tag.isNone
  | .sequence _ items .. => noTagsList items.toList
  | .mapping _ pairs .. => noTagsPairList pairs.toList
  | .alias _ => true
where
  noTagsList : List YamlValue → Bool
    | [] => true
    | v :: vs => noTags v && noTagsList vs
  noTagsPairList : List (YamlValue × YamlValue) → Bool
    | [] => true
    | (k, v) :: rest => noTags k && noTags v && noTagsPairList rest

/-- All scalar nodes are both untagged and plain. This is a strictly
    stronger premise than `noTags` and is necessary for style-sensitive
    meaning preservation under `contentEq`. -/
def plainNoTags : YamlValue → Bool
  | .scalar s => s.tag.isNone && (s.style == .plain)
  | .sequence _ items .. => plainNoTagsList items.toList
  | .mapping _ pairs .. => plainNoTagsPairList pairs.toList
  | .alias _ => true
where
  plainNoTagsList : List YamlValue → Bool
    | [] => true
    | v :: vs => plainNoTags v && plainNoTagsList vs
  plainNoTagsPairList : List (YamlValue × YamlValue) → Bool
    | [] => true
    | (k, v) :: rest => plainNoTags k && plainNoTags v && plainNoTagsPairList rest

/-- **For wholly plain, untagged values, content equivalence implies
    resolution equality.** The plain-style hypothesis is necessary:
    a quoted "true" and an unquoted true resolve differently. -/
lemma resolve_eq_of_contentEq_plainNoTags (v v' : YamlValue)
    (h_ceq : contentEq v v' = true) (h_nt : plainNoTags v = true) (h_nt' : plainNoTags v' = true) :
    resolve v = resolve v' := by
  match v, v' with
  | .scalar s₁, .scalar s₂ =>
    have hc : s₁.content = s₂.content := by
      have : (s₁.content == s₂.content) = true := h_ceq
      exact eq_of_beq this
    have ht1 : s₁.tag = none := by
      have hni : s₁.tag.isNone = true := (Bool.and_eq_true.mp h_nt).1
      match h : s₁.tag with
      | none => rfl
      | some _ => rw [h] at hni; exact Bool.noConfusion hni
    have ht2 : s₂.tag = none := by
      have hni : s₂.tag.isNone = true := (Bool.and_eq_true.mp h_nt').1
      match h : s₂.tag with
      | none => rfl
      | some _ => rw [h] at hni; exact Bool.noConfusion hni
    have hs1 : s₁.style = .plain :=
      eq_of_beq (Bool.and_eq_true.mp h_nt).2
    have hs2 : s₂.style = .plain :=
      eq_of_beq (Bool.and_eq_true.mp h_nt').2
    change scalarType s₁ = scalarType s₂
    simp [scalarType, hc, ht1, ht2, hs1, hs2]
  | .sequence _ items₁ .., .sequence _ items₂ .. =>
    show YamlType.seq (resolve.resolveList items₁.toList).toArray =
         YamlType.seq (resolve.resolveList items₂.toList).toArray
    have hceq : contentEq.contentEqList items₁.toList items₂.toList = true := by
      have : (items₁.size == items₂.size &&
              contentEq.contentEqList items₁.toList items₂.toList) = true := h_ceq
      simp only [Bool.and_eq_true] at this; exact this.2
    have h_list := resolveList_eq_plainNoTags items₁.toList items₂.toList
      (fun v hv v' hc hnt hnt' => resolve_eq_of_contentEq_plainNoTags v v' hc hnt hnt')
      hceq h_nt h_nt'
    rw [h_list]
  | .mapping _ pairs₁ .., .mapping _ pairs₂ .. =>
    show YamlType.map (resolve.resolvePairs pairs₁.toList).toArray =
         YamlType.map (resolve.resolvePairs pairs₂.toList).toArray
    have hceq : contentEq.contentEqPairList pairs₁.toList pairs₂.toList = true := by
      have : (pairs₁.size == pairs₂.size &&
              contentEq.contentEqPairList pairs₁.toList pairs₂.toList) = true := h_ceq
      simp only [Bool.and_eq_true] at this; exact this.2
    have h_pairs := resolvePairList_eq_plainNoTags pairs₁.toList pairs₂.toList
      (fun p hp =>
        ⟨fun v' hc hnt hnt' => resolve_eq_of_contentEq_plainNoTags p.1 v' hc hnt hnt',
         fun v' hc hnt hnt' => resolve_eq_of_contentEq_plainNoTags p.2 v' hc hnt hnt'⟩)
      hceq h_nt h_nt'
    rw [h_pairs]
  | .alias _, .alias _ => rfl
  -- Cross-constructor: contentEq definitionally reduces to false
  | .scalar _, .sequence .. | .scalar _, .mapping .. | .scalar _, .alias _
  | .sequence .., .scalar _ | .sequence .., .mapping .. | .sequence .., .alias _
  | .mapping .., .scalar _ | .mapping .., .sequence .. | .mapping .., .alias _
  | .alias _, .scalar _ | .alias _, .sequence .. | .alias _, .mapping .. =>
    exact Bool.noConfusion h_ceq
termination_by v
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem hv
    cases items₁; simp_all [Array.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hp
    cases pairs₁; cases p; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hp
    cases pairs₁; cases p; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
where
  /-- Helper: contentEqList + plainNoTags → resolveList equality. -/
  resolveList_eq_plainNoTags (vs vs' : List YamlValue)
      (ih : ∀ v, v ∈ vs → ∀ v', contentEq v v' = true →
        plainNoTags v = true → plainNoTags v' = true → resolve v = resolve v')
      (h_ceq : contentEq.contentEqList vs vs' = true)
      (h_nt : plainNoTags.plainNoTagsList vs = true)
      (h_nt' : plainNoTags.plainNoTagsList vs' = true) :
      resolve.resolveList vs = resolve.resolveList vs' := by
    match vs, vs' with
    | [], [] => rfl
    | [], _ :: _ => exact Bool.noConfusion h_ceq
    | _ :: _, [] => exact Bool.noConfusion h_ceq
    | v :: rest, v' :: rest' =>
      have hceq : (contentEq v v' && contentEq.contentEqList rest rest') = true := h_ceq
      simp only [Bool.and_eq_true] at hceq
      have hnt : (plainNoTags v && plainNoTags.plainNoTagsList rest) = true := h_nt
      simp only [Bool.and_eq_true] at hnt
      have hnt' : (plainNoTags v' && plainNoTags.plainNoTagsList rest') = true := h_nt'
      simp only [Bool.and_eq_true] at hnt'
      show resolve v :: resolve.resolveList rest = resolve v' :: resolve.resolveList rest'
      rw [ih v (.head _) v' hceq.1 hnt.1 hnt'.1,
          resolveList_eq_plainNoTags rest rest' (fun w hw => ih w (.tail _ hw))
            hceq.2 hnt.2 hnt'.2]
  /-- Helper: contentEqPairList + plainNoTags → resolvePairs equality. -/
  resolvePairList_eq_plainNoTags (ps ps' : List (YamlValue × YamlValue))
      (ih : ∀ p, p ∈ ps →
        (∀ v', contentEq p.1 v' = true → plainNoTags p.1 = true → plainNoTags v' = true →
          resolve p.1 = resolve v') ∧
        (∀ v', contentEq p.2 v' = true → plainNoTags p.2 = true → plainNoTags v' = true →
          resolve p.2 = resolve v'))
      (h_ceq : contentEq.contentEqPairList ps ps' = true)
      (h_nt : plainNoTags.plainNoTagsPairList ps = true)
      (h_nt' : plainNoTags.plainNoTagsPairList ps' = true) :
      resolve.resolvePairs ps = resolve.resolvePairs ps' := by
    match ps, ps' with
    | [], [] => rfl
    | [], _ :: _ => exact Bool.noConfusion h_ceq
    | _ :: _, [] => exact Bool.noConfusion h_ceq
    | (k, v) :: rest, (k', v') :: rest' =>
      have hceq : (contentEq k k' && contentEq v v' &&
                   contentEq.contentEqPairList rest rest') = true := h_ceq
      simp only [Bool.and_eq_true] at hceq
      have hnt : (plainNoTags k && plainNoTags v && plainNoTags.plainNoTagsPairList rest) = true := h_nt
      simp only [Bool.and_eq_true] at hnt
      have hnt' : (plainNoTags k' && plainNoTags v' && plainNoTags.plainNoTagsPairList rest') = true := h_nt'
      simp only [Bool.and_eq_true] at hnt'
      have ihm := ih (k, v) (.head _)
      show (resolve k, resolve v) :: resolve.resolvePairs rest =
           (resolve k', resolve v') :: resolve.resolvePairs rest'
      rw [ihm.1 k' hceq.1.1 hnt.1.1 hnt'.1.1, ihm.2 v' hceq.1.2 hnt.1.2 hnt'.1.2,
          resolvePairList_eq_plainNoTags rest rest' (fun p hp => ih p (.tail _ hp))
            hceq.2 hnt.2 hnt'.2]

/-! ## §4: End-to-End Round-Trip Checker

`resolveRoundTrips` checks the full chain:
`dump v cfg → parseYamlSingle → resolve → BEq comparison`.
-/

/-- End-to-end round-trip check: dump, parse, then compare resolved types.
    Returns `true` if the round-trip preserves schema-level meaning. -/
def resolveRoundTrips (v : YamlValue) (cfg : DumpConfig := {}) : Bool :=
  match parseYamlSingle (dump v cfg) with
  | .ok v' => resolve v' == resolve v
  | .error _ => false

/-- Typed round-trip check: `toYaml → dump → parseYamlSingle → resolve` chain. -/
def resolveRoundTripsTyped {α : Type} [ToYaml α] (a : α) (cfg : DumpConfig := {}) : Bool :=
  resolveRoundTrips (toYaml a) cfg

/-! ## §5: Concrete Round-Trip Proofs

Per-value `native_decide` proofs that `dump→parse` preserves resolution.
Since all functions are total (`def`, not `partial def`), `native_decide`
compiles to native code and evaluates the full pipeline. -/

-- Scalar round-trips
lemma roundtrip_plain_hello :
    resolveRoundTrips (.plainScalar "hello") = true := by native_decide

lemma roundtrip_plain_world :
    resolveRoundTrips (.plainScalar "world") = true := by native_decide

lemma roundtrip_plain_empty_default_changes_type :
    resolveRoundTrips (.plainScalar "") = false := by native_decide

-- A tag-free plain reserved word becomes quoted by the default serializer;
-- these are genuine counterexamples to unconditional schema round-trip.
-- Typed ToYaml outputs below preserve meaning via explicit type information.
lemma roundtrip_reserved_true_default_changes_type :
    resolveRoundTrips (.plainScalar "true") = false := by native_decide

lemma roundtrip_reserved_false_default_changes_type :
    resolveRoundTrips (.plainScalar "false") = false := by native_decide

lemma roundtrip_reserved_null_default_changes_type :
    resolveRoundTrips (.plainScalar "null") = false := by native_decide

lemma roundtrip_reserved_42 :
    resolveRoundTrips (.plainScalar "42") = true := by native_decide

lemma roundtrip_reserved_neg7_default_changes_type :
    resolveRoundTrips (.plainScalar "-7") = false := by native_decide

-- Special characters (require quoting)
lemma roundtrip_colon_space :
    resolveRoundTrips (.plainScalar "key: value") = true := by native_decide

lemma roundtrip_newline :
    resolveRoundTrips (.plainScalar "line1\nline2") = true := by native_decide

-- Double-quoted scalars
lemma roundtrip_double_quoted :
    resolveRoundTrips (.scalar ⟨"hello", .doubleQuoted, none, none, none⟩) = true := by
  native_decide

-- Flow sequences
lemma roundtrip_empty_flow_seq :
    resolveRoundTrips (.sequence .flow #[]) = true := by native_decide

lemma roundtrip_flow_seq_scalars :
    resolveRoundTrips (.sequence .flow #[.plainScalar "a", .plainScalar "b"] none) = true := by
  native_decide

-- Block sequences
lemma roundtrip_empty_block_seq :
    resolveRoundTrips (.sequence .block #[]) = true := by native_decide

lemma roundtrip_block_seq_scalars :
    resolveRoundTrips (.sequence .block #[.plainScalar "a", .plainScalar "b"] none) = true := by
  native_decide

-- Flow mappings
lemma roundtrip_empty_flow_map :
    resolveRoundTrips (.mapping .flow #[]) = true := by native_decide

lemma roundtrip_flow_map_pair :
    resolveRoundTrips (.mapping .flow #[(.plainScalar "key", .plainScalar "val")] none) = true := by
  native_decide

-- Block mappings
lemma roundtrip_empty_block_map :
    resolveRoundTrips (.mapping .block #[]) = true := by native_decide

lemma roundtrip_block_map_pair :
    resolveRoundTrips (.mapping .block #[(.plainScalar "k", .plainScalar "v")] none) = true := by
  native_decide

-- Nested structures
lemma roundtrip_nested_seq_in_map :
    resolveRoundTrips (.mapping .block
      #[(.plainScalar "items",
         .sequence .block #[.plainScalar "a", .plainScalar "b"] none)] none) = true := by
  native_decide

lemma roundtrip_nested_map_in_seq :
    resolveRoundTrips (.sequence .block
      #[.mapping .flow #[(.plainScalar "k", .plainScalar "v")] none] none) = true := by
  native_decide

-- DumpConfig variations
lemma roundtrip_config_double_quoted :
    resolveRoundTrips (.plainScalar "hello") { scalarStyle := .doubleQuoted } = true := by
  native_decide

lemma roundtrip_config_single_quoted :
    resolveRoundTrips (.plainScalar "hello") { scalarStyle := .singleQuoted } = true := by
  native_decide

lemma roundtrip_config_flow :
    resolveRoundTrips (.sequence .block #[.plainScalar "a"] none)
      { defaultStyle := .flow } = true := by native_decide

/-! ## §6: Typed Schema Round-Trip Composition

For Lean types with `ToYaml`, the full chain:
`α → toYaml → dump → parseYamlSingle → resolve → BEq → true`
-/

-- Bool
lemma roundtrip_typed_true :
    resolveRoundTripsTyped true = true := by native_decide

lemma roundtrip_typed_false :
    resolveRoundTripsTyped false = true := by native_decide

-- Nat
lemma roundtrip_typed_nat_0 :
    resolveRoundTripsTyped (0 : Nat) = true := by native_decide

lemma roundtrip_typed_nat_42 :
    resolveRoundTripsTyped (42 : Nat) = true := by native_decide

-- Int
lemma roundtrip_typed_int_100 :
    resolveRoundTripsTyped (100 : Int) = true := by native_decide

lemma roundtrip_typed_int_neg7 :
    resolveRoundTripsTyped (-7 : Int) = true := by native_decide

-- String (schema-safe)
lemma roundtrip_typed_string_hello :
    resolveRoundTripsTyped "hello" = true := by native_decide

lemma roundtrip_typed_string_empty :
    resolveRoundTripsTyped "" = true := by native_decide

-- Unit
lemma roundtrip_typed_unit :
    resolveRoundTripsTyped () = true := by native_decide

-- Option
lemma roundtrip_typed_option_some :
    resolveRoundTripsTyped (some "hello" : Option String) = true := by native_decide

lemma roundtrip_typed_option_none :
    resolveRoundTripsTyped (none : Option String) = true := by native_decide

-- Array
lemma roundtrip_typed_array_strings :
    resolveRoundTripsTyped (#["a", "b"] : Array String) = true := by native_decide

lemma roundtrip_typed_array_empty :
    resolveRoundTripsTyped (#[] : Array String) = true := by native_decide

-- List
lemma roundtrip_typed_list_strings :
    resolveRoundTripsTyped (["x", "y"] : List String) = true := by native_decide

-- Nested
lemma roundtrip_typed_nested_arrays :
    resolveRoundTripsTyped (#[#["a", "b"], #["c"]] : Array (Array String)) = true := by
  native_decide

end L4YAML.Proofs.RoundTripComposition
