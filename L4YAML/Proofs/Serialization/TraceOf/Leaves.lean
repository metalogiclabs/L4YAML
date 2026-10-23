/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Surface.Document
public import L4YAML.Proofs.Serialization.EventsOf

public meta import L4YAML.Proofs.Serialization.EventsOf
public meta import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Event-annotated grammar — combinators and leaves (EVENTSOF-CONCEPT §10)

`TraceOf/Node.lean` (generated) is the copy of `Surface/Node.lean`'s mutual
block with one more index, the trace.  This file supplies what the copy refers
to: the annotated combinators (`TSeq`, `TOpt`, …, mirroring `GSeq`, `GOpt`, …),
`Lift` for the productions that carry no event, and the two leaves where
events arise — node properties and aliases.  A leaf's events are a *function
of the span it consumed* (`propEvents`, `aliasEvents`), so leaf traces are
unique by construction; uniqueness of the whole is the grammar's business.
-/

namespace L4YAML.Proofs.Serialization.TraceOf

@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.EventsOf (handleOf isTagCharBool)
open L4YAML.Proofs.Serialization.SourceEvents (isAnchorCharBool)

abbrev TRel := SurfPos → SurfPos → List Event → Prop

/-- A production without events, as an annotated relation. -/
def Lift (P : SurfPos → SurfPos → Prop) : TRel := fun s s' ev => P s s' ∧ ev = []

inductive TSeq (P Q : TRel) : TRel where
  | mk (s₁ s₂ s₃ : SurfPos) (e₁ e₂ : List Event) :
      P s₁ s₂ e₁ → Q s₂ s₃ e₂ → TSeq P Q s₁ s₃ (e₁ ++ e₂)

inductive TSeq3 (P Q R : TRel) : TRel where
  | mk (s₁ s₂ s₃ s₄ : SurfPos) (e₁ e₂ e₃ : List Event) :
      P s₁ s₂ e₁ → Q s₂ s₃ e₂ → R s₃ s₄ e₃ → TSeq3 P Q R s₁ s₄ (e₁ ++ e₂ ++ e₃)

inductive TAlt (P Q : TRel) : TRel where
  | left (s s' : SurfPos) (e : List Event) : P s s' e → TAlt P Q s s' e
  | right (s s' : SurfPos) (e : List Event) : Q s s' e → TAlt P Q s s' e

inductive TStar (P : TRel) : TRel where
  | nil (s : SurfPos) : TStar P s s []
  | cons (s₁ s₂ s₃ : SurfPos) (e₁ e₂ : List Event) :
      P s₁ s₂ e₁ → TStar P s₂ s₃ e₂ → TStar P s₁ s₃ (e₁ ++ e₂)

inductive TPlus (P : TRel) : TRel where
  | mk (s₁ s₂ s₃ : SurfPos) (e₁ e₂ : List Event) :
      P s₁ s₂ e₁ → TStar P s₂ s₃ e₂ → TPlus P s₁ s₃ (e₁ ++ e₂)

inductive TOpt (P : TRel) : TRel where
  | none (s : SurfPos) : TOpt P s s []
  | some (s s' : SurfPos) (e : List Event) : P s s' e → TOpt P s s' e

/-- The characters a derivation from `s` to `s'` consumed. -/
def span (s s' : SurfPos) : List Char := s.chars.take (s.chars.length - s'.chars.length)

/-- Events of a tag lexeme: a verbatim `!<…>` names no handle (§6 Q4). -/
def tagEvents (chars : List Char) : List Event :=
  if chars.take 2 = ['!', '<'] then [] else [.useTag (handleOf chars)]

/-- Events of a `c-ns-properties` span, in text order: `&name` and `!…`
lexemes separated by white (`s-separate`, which may span lines and comments). -/
def propEvents : List Char → Nat → List Event
  | _, 0 => []
  | [], _ => []
  | '&' :: cs, fuel + 1 =>
      let (name, rest) := cs.span isAnchorCharBool
      .defineAnchor (String.ofList name) :: propEvents rest fuel
  | '!' :: cs, fuel + 1 =>
      let (body, rest) := cs.span isTagCharBool
      tagEvents ('!' :: body) ++ propEvents rest fuel
  | _ :: cs, fuel + 1 => propEvents cs fuel

/-- Events of a `c-ns-alias-node` span. -/
def aliasEvents : List Char → List Event
  | '*' :: cs => [.useAlias (String.ofList (cs.takeWhile isAnchorCharBool))]
  | _ => []

#guard propEvents "&a !t".toList 5 = [.defineAnchor "a", .useTag "!"]
#guard propEvents "!!str &a".toList 8 = [.useTag "!!", .defineAnchor "a"]
#guard propEvents "!<tag:x> &a".toList 11 = [.defineAnchor "a"]
#guard propEvents "!e!x".toList 4 = [.useTag "!e!"]
#guard aliasEvents "*a".toList = [.useAlias "a"]

/-- Annotated `[96] c-ns-properties`: the surface relation, trace read off the span. -/
def TCNsProperties (n : Nat) (c : YamlContext) : TRel :=
  fun s s' ev => SCNsProperties n c s s' ∧ ev = propEvents (span s s') (span s s').length

/-- Annotated `[104] c-ns-alias-node`. -/
def TCNsAliasNode : TRel :=
  fun s s' ev => SCNsAliasNode s s' ∧ ev = aliasEvents (span s s')

end

end L4YAML.Proofs.Serialization.TraceOf
