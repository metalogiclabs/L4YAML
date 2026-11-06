/-
Strict behavioral regression for L4YAML alias-resolution order.
Baseline provenance: 64795a8db28ccfdae85082c93b6453001ae9d3e4.
No production code is changed by this file.
-/
module

public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition
public import L4YAML.Output.Emitter
public meta import L4YAML.Output.Emitter

@[expose] public section

/-!
# A later inner declaration remains current when its enclosing node closes

Normative source: YAML 1.2.2 §3.2.2.2,
https://yaml.org/spec/1.2.2/#3222-anchors-and-aliases

An alias denotes the most recent serialization EVENT carrying its anchor.
The collection START precedes the contained scalar's anchor. Consequently,
the scalar remains the latest declaration when the enclosing collection ends.
Renaming the outer anchor changes no referenced target in these examples.

All expected values are hand-built from that event order. They are not
computed by the resolver under test. `contentEq` is used only to compare
actual and expected values, ignoring style differences between flow/block
syntax. These examples are untagged and acyclic, so the test does not make a
claim about cycle expansion or tagged-value equivalence.

The same-name sequence, mapping, and block tests are intended RED regressions
on the baseline. The renamed and ordinary cases are positive controls.
Do not invert the three failing assertions to accommodate baseline behavior.

Relevant implementation: `L4YAML/Spec/Types.lean`,
`YamlValue.resolveAliasesOrdered` and `YamlDocument.compose`; public caller
`L4YAML/Parser/Composition.lean`, `TokenParser.parseYamlSingle`.
-/

namespace L4YAML.IndependentAudit.AnchorRebindingExpected

open L4YAML
open L4YAML.TokenParser

def inner : YamlValue := .scalar { content := "inner", style := .plain }
def old : YamlValue := .scalar { content := "old", style := .plain }
def key : YamlValue := .scalar { content := "k", style := .plain }

def wantNestedSequence : YamlValue :=
  .sequence .flow #[.sequence .flow #[inner], inner]

def wantNestedMapping : YamlValue :=
  .sequence .flow #[.mapping .flow #[(key, inner)], inner]

def wantSiblingRebinding : YamlValue :=
  .sequence .flow #[old, old, inner, inner]

def wantClosedCollection : YamlValue :=
  .sequence .flow #[.sequence .flow #[inner], .sequence .flow #[inner]]

def matches (src : String) (expected : YamlValue) : Bool :=
  match parseYamlSingle src with
  | .ok value => Emit.contentEq value expected
  | .error _ => false

def renderLoad (src : String) : String :=
  match parseYamlSingle src with
  | .ok value => Emit.emit value
  | .error err => "ERROR: " ++ reprStr err

def testCases : List (String × String × YamlValue) := [
  ("flow sequence: inner rebind wins", "[&x [&x inner], *x]", wantNestedSequence),
  ("flow sequence: unused outer renamed", "[&outer [&x inner], *x]", wantNestedSequence),
  ("flow mapping: inner rebind wins", "[&x {k: &x inner}, *x]", wantNestedMapping),
  ("flow mapping: unused outer renamed", "[&outer {k: &x inner}, *x]", wantNestedMapping),
  ("block sequence: inner rebind wins", "- &x\n  - &x inner\n- *x\n", wantNestedSequence),
  ("block sequence: unused outer renamed", "- &outer\n  - &x inner\n- *x\n", wantNestedSequence),
  ("sibling rebinding remains ordered", "[&x old, *x, &x inner, *x]", wantSiblingRebinding),
  ("ordinary closed collection remains reusable", "[&x [inner], *x]", wantClosedCollection)
]

#eval testCases.map (fun (label, src, expected) =>
  (label, renderLoad src, Emit.emit expected, matches src expected))

-- Strict expectations, independently derived from declaration-event order.
#guard matches "[&x [&x inner], *x]" wantNestedSequence
#guard matches "[&outer [&x inner], *x]" wantNestedSequence
#guard matches "[&x {k: &x inner}, *x]" wantNestedMapping
#guard matches "[&outer {k: &x inner}, *x]" wantNestedMapping
#guard matches "- &x\n  - &x inner\n- *x\n" wantNestedSequence
#guard matches "- &outer\n  - &x inner\n- *x\n" wantNestedSequence

-- Positive controls distinguish the new boundary from already repaired cases.
#guard matches "[&x old, *x, &x inner, *x]" wantSiblingRebinding
#guard matches "[&x [inner], *x]" wantClosedCollection
#guard (parseYaml "&x [*x]").isOk
#guard (parseYaml "&x {a: *x}").isOk
#guard (parseYaml "[*x]").isOk == false
#guard (parseYaml "[*x, &x inner]").isOk == false
#guard (parseYaml "&x inner\n---\n*x\n").isOk == false

end L4YAML.IndependentAudit.AnchorRebindingExpected

end
