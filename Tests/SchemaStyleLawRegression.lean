import L4YAML.Proofs.RoundTrip.RoundTripComposition

open L4YAML
open L4YAML.Schema
open L4YAML.Proofs.RoundTripComposition

/-- Two presentations with identical scalar content and tags but different
    Core Schema meaning: a constructive counterexample to tag-only equivalence. -/
def unquotedTrue : YamlValue := .scalar { content := "true", style := .plain }
def quotedTrue : YamlValue := .scalar { content := "true", style := .doubleQuoted }

#guard contentEq unquotedTrue quotedTrue
#guard noTags unquotedTrue && noTags quotedTrue
#guard plainNoTags unquotedTrue && !plainNoTags quotedTrue
#guard !resolveEq unquotedTrue quotedTrue
#guard Schema.resolve unquotedTrue == .bool true
#guard Schema.resolve quotedTrue == .str "true"
#guard Schema.resolve unquotedTrue != Schema.resolve quotedTrue
#guard resolveRoundTripsTyped true
#guard resolveRoundTripsTyped ("true" : String)
#guard resolveRoundTripsTyped (some "null" : Option String)
#guard resolveRoundTripsTyped (none : Option String)
