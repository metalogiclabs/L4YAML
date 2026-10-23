/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Token.Token
public import L4YAML.Proofs.Serialization.SerializationWellFormed

public meta import L4YAML.Token.Token
public meta import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Serialization events of a token stream (EVENTSOF-CONCEPT §9, S2)

`tokenEvents` reads the scanner's token stream the way `eventsOfSegs` reads a
lexical skeleton: anchors, aliases and shorthand tags become events in stream
order, `documentEnd` is `endDocument`, and `documentStart` is `beginDocument`
followed by the `%TAG` directives scanned before it (`RuntimeScopes.documentEvents`
pins that order: the directives belong to the document the reset opens).

It is executable and mentions no `Prop`; S3 proves the scan's skeleton witness
has exactly this trace, S5 relates it to the parser's own anchor/tag checks.
-/

namespace L4YAML.Proofs.Serialization.TokenEvents

public section

open L4YAML.Proofs.Serialization.SerializationWellFormed

/-- The event a single token contributes, if any; directives and document
starts are handled by `tokenEvents` because their order is not local. -/
def tokenEvent : YamlToken → Option Event
  | .anchor name => some (.defineAnchor name)
  | .alias name => some (.useAlias name)
  | .tag handle _ => if handle.isEmpty then none else some (.useTag handle)
  | .documentEnd => some .endDocument
  | _ => none

/-- Fold over the stream with the named `%TAG` handles pending until the next
`documentStart`; handles still pending at the end are emitted there.  `!` and
`!!` are builtin (`TagHandleAllowed`), so redeclaring them is no event — the
same reading as the skeleton's `declaredHandle`. -/
def go : List (Positioned YamlToken) → List String → List Event
  | [], pending => pending.reverse.map .declareTag
  | t :: ts, pending =>
    match t.val with
    | .tagDirective handle _ =>
      if BuiltinTagHandle handle then go ts pending else go ts (handle :: pending)
    | .documentStart => .beginDocument :: (pending.reverse.map .declareTag ++ go ts [])
    | v => match tokenEvent v with
      | some e => e :: go ts pending
      | none => go ts pending

def tokenEvents (tokens : Array (Positioned YamlToken)) : List Event :=
  go tokens.toList []

/-- A token at a default position, for the guards. -/
def tok (v : YamlToken) : Positioned YamlToken := ⟨default, v, default⟩

#guard tokenEvents #[] = []
#guard tokenEvents #[tok (.anchor "x"), tok (.alias "x")] =
  [.defineAnchor "x", .useAlias "x"]
#guard tokenEvents #[tok (.tagDirective "!" "!x"), tok (.documentStart), tok (.tag "!" "a")] =
  [.beginDocument, .useTag "!"]
#guard tokenEvents #[tok (.tag "" "tag:x")] = []
#guard tokenEvents #[tok (.documentEnd), tok (.documentStart)] = [.endDocument, .beginDocument]
#guard tokenEvents #[tok (.tagDirective "!h!" "p")] = [.declareTag "!h!"]
#guard tokenEvents #[tok (.tagDirective "!" "p"), tok (.tagDirective "!!" "q"), tok .documentStart] = [.beginDocument]

end

end L4YAML.Proofs.Serialization.TokenEvents
