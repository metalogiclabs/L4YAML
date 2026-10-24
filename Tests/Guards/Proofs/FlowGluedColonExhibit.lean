module

public import L4YAML.Scanner.Scanner
public import L4YAML.Parser.Composition
public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Parser.Composition

/-! # Rule-2 exhibit: `:` glued to a flow collection value after a non-JSON key

Spec `[147] c-ns-flow-map-separate-value ::= ":" (s-separate(n,c) ns-flow-node(n,c) | e-node)`
requires `s-separate` between the `:` and a present value; the separator-free form is
`[149] c-ns-flow-map-adjacent-value`, reachable only through
`[148] c-ns-flow-map-json-key-entry` (a JSON-like key).  With `[66] s-separate-in-line`
narrowed to col 0 the Surface derivation of `{a:[1]}` has no arm: `a` is a yaml key, so
`[147]` is the only entry, and nothing non-empty separates `:` from `[`.

The scanner used to accept these (`isValueCandidate`'s `[147]` branch takes a flow
indicator after `:` as the value indicator and then scans the collection with no
separator).  `scanValueValidate` / `scanValueValidateIx` now refuse them
(`flowGluedCollectionValue`, error `unseparatedValue`); the JSON-key shapes stay accepted.
`[148]`/`[149]` themselves are not yet in `L4YAML/Surface/Node.lean` — companion gap. -/

namespace L4YAML.Tests.Guards.FlowGluedColonExhibit

open L4YAML

def accepts (s : String) : Bool := (TokenParser.parseYaml s).isOk

-- Refused: yaml key (plain, empty, or explicit), `:` glued to `[`/`{` — [147] needs s-separate.
#guard accepts "{a:[1]}" = false
#guard accepts "[a:[1]]" = false
#guard accepts "{a:{b: c}}" = false
#guard accepts "[a:{b: c}]" = false
#guard accepts "{a:[]}" = false
#guard accepts "{a:{}}" = false
#guard accepts "{a :[1]}" = false
#guard accepts "{:[1]}" = false
#guard accepts "[:[1]]" = false
#guard accepts "{? a :[1]}" = false
#guard accepts "[? a :[1]]" = false

-- Accepted: JSON-like key, adjacent value ([148]/[149]) — spec-valid, no Surface arm yet.
#guard accepts "{\"a\":b}" = true
#guard accepts "{\"a\":[1]}" = true
#guard accepts "{'a':{b: c}}" = true
#guard accepts "{[a]:[1]}" = true

-- Controls: separated value; `a:b` is one plain scalar (`:` followed by ns-plain-safe).
#guard accepts "{a: [1]}" = true
#guard accepts "{a:b}" = true
#guard accepts "{a:\"x\"}" = true
#guard accepts "a: [1]" = true

/-- The scalar tokens of `scan`, in order. -/
def scalars (s : String) : List (String × ScalarStyle) :=
  match L4YAML.Scanner.scan s with
  | .ok toks => toks.toList.filterMap fun t => match t.val with
      | .scalar c st => some (c, st)
      | _ => none
  | .error _ => []

-- The other glued indicators `" ' & ! *` never reach the value validator: in flow context
-- `:` followed by them continues the plain scalar (`ns-plain-safe(c)` excludes only `[ ] { } ,`),
-- so there is nothing to refuse — the key absorbs them.  `[`/`{` are the only glued shapes.
#guard scalars "{a:\"x\"}" = [("a:\"x\"", .plain)]
#guard scalars "{a:'x'}" = [("a:'x'", .plain)]
#guard scalars "{a:&x b}" = [("a:&x b", .plain)]
#guard scalars "{a:!t b}" = [("a:!t b", .plain)]
#guard scalars "{a:*x}" = [("a:*x", .plain)]
#guard scalars "[a:*x]" = [("a:*x", .plain)]
#guard scalars "a:[1]" = [("a:[1]", .plain)]
-- In block context the same glued `:` after a JSON key is already refused (§8.2.2).
#guard accepts "\"a\":[1]" = false

end L4YAML.Tests.Guards.FlowGluedColonExhibit
