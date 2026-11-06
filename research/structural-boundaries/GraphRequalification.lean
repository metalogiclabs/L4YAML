/-
Current-pin requalification of the existing MathGraph graph-composition probe.

L4YAML baseline: 64795a8db28ccfdae85082c93b6453001ae9d3e4.
Original MathGraph source: PR #206, commit
b4c32a57a7d41f67015a502b0ebbb1c987d757c0,
research/l4yaml_semantic_diff_v2/GraphComposeProbe.lean,
Git blob d962e97a653b970d1527c74f9110c9a0b474be29.

GraphComposeProbeOriginal.lean is the unchanged original source. This file
adds only external, executable checks; no L4YAML implementation is changed.
-/
module

public import GraphComposeProbeOriginal
public meta import GraphComposeProbeOriginal

@[expose] public section

/-!
# Reuse the existing node-start allocator, rather than rediscovering it

Normative source: YAML 1.2.2 section 3.2.2.2,
https://yaml.org/spec/1.2.2/#3222-anchors-and-aliases

Expected graphs below are hand-built in serialization node-start order.
They do not call `build`, `graphOf`, `aliasTarget`, `rawTreeActions`, or the
scalar serializer to derive expected answers. The expected alias edges and
allocation receipts are likewise explicit. Comparing two parsers alone
would not be an independent content oracle; each is checked against these
separately specified answers.

This covers an untagged finite test family, including cycles and sharing as
graph edges. It does not prove arbitrary source-to-graph fidelity, preserve
all YAML tags or scalar semantics, or make the JSON graph a drop-in replacement
for L4YAML's tree API. The original scalar payload schema stores JSON text as
a string; `scalarNode` receives that text literally, without resolving it.

The numeric nested-rebinding case is already present in the original probe
and its historical qualification. Passing this file would establish reuse
at the new L4YAML pin, not a newly discovered repair or a universal theorem.
-/

namespace L4YAML.IndependentAudit.GraphRequalification

open Lean
open MathGraph.GraphCompose

def scalarNode (jsonText : String) : Json :=
  Json.mkObj [("kind", .str "scalar"), ("json", .str jsonText)]

def sequenceNode (items : Array Nat) : Json :=
  Json.mkObj [("kind", .str "sequence"), ("items", toJson items)]

def mappingNode (pairs : Array (Nat × Nat)) : Json :=
  Json.mkObj [
    ("kind", .str "mapping"),
    ("pairs", .arr (pairs.map fun (key, value) => .arr #[toJson key, toJson value]))]

def startReceipt (id : Nat) (anchor : Option String) : Json :=
  Json.mkObj [
    ("event", .str "nodeStart"),
    ("id", toJson id),
    ("anchor", match anchor with | some name => .str name | none => .null)]

def aliasReceipt (name : String) (target : Nat) : Json :=
  Json.mkObj [
    ("event", .str "aliasTo"), ("name", .str name), ("target", toJson target)]

structure GraphCase where
  label : String
  source : String
  expectedNodes : Array Json
  expectedReceipts : Array Json

def expectedDocument (c : GraphCase) : Json :=
  Json.mkObj [
    ("root", toJson (0 : Nat)),
    ("nodes", .arr c.expectedNodes),
    ("receipts", .arr c.expectedReceipts)]

def expectedDocuments (c : GraphCase) : Json := .arr #[expectedDocument c]

-- Outer collection is ID 1; inner scalar is ID 2. The final alias is ID 2.
def nestedSequenceNodes (jsonText : String) : Array Json :=
  #[sequenceNode #[1, 2], sequenceNode #[2], scalarNode jsonText]

def nestedSequenceReceipts (outerName : String) : Array Json :=
  #[startReceipt 0 none, startReceipt 1 (some outerName),
    startReceipt 2 (some "x"), aliasReceipt "x" 2]

-- Outer mapping is ID 1, key ID 2, inner anchored scalar ID 3.
def nestedMappingNodes : Array Json :=
  #[sequenceNode #[1, 3], mappingNode #[(2, 3)],
    scalarNode "\"k\"", scalarNode "\"inner\""]

def nestedMappingReceipts (outerName : String) : Array Json :=
  #[startReceipt 0 none, startReceipt 1 (some outerName), startReceipt 2 none,
    startReceipt 3 (some "x"), aliasReceipt "x" 3]

def acceptedCases : List GraphCase := [
  { label := "historical numeric nested rebinding"
    source := "[&x [&x 1], *x]"
    expectedNodes := nestedSequenceNodes "1"
    expectedReceipts := nestedSequenceReceipts "x" },
  { label := "flow sequence inner rebind wins"
    source := "[&x [&x inner], *x]"
    expectedNodes := nestedSequenceNodes "\"inner\""
    expectedReceipts := nestedSequenceReceipts "x" },
  { label := "flow sequence unused outer renamed"
    source := "[&outer [&x inner], *x]"
    expectedNodes := nestedSequenceNodes "\"inner\""
    expectedReceipts := nestedSequenceReceipts "outer" },
  { label := "flow mapping inner rebind wins"
    source := "[&x {k: &x inner}, *x]"
    expectedNodes := nestedMappingNodes
    expectedReceipts := nestedMappingReceipts "x" },
  { label := "flow mapping unused outer renamed"
    source := "[&outer {k: &x inner}, *x]"
    expectedNodes := nestedMappingNodes
    expectedReceipts := nestedMappingReceipts "outer" },
  { label := "block sequence inner rebind wins"
    source := "- &x\n  - &x inner\n- *x\n"
    expectedNodes := nestedSequenceNodes "\"inner\""
    expectedReceipts := nestedSequenceReceipts "x" },
  { label := "block sequence unused outer renamed"
    source := "- &outer\n  - &x inner\n- *x\n"
    expectedNodes := nestedSequenceNodes "\"inner\""
    expectedReceipts := nestedSequenceReceipts "outer" },
  { label := "sibling rebinding chooses latest preceding start"
    source := "[&x old, *x, &x inner, *x]"
    expectedNodes := #[sequenceNode #[1, 1, 2, 2], scalarNode "\"old\"",
      scalarNode "\"inner\""]
    expectedReceipts := #[startReceipt 0 none, startReceipt 1 (some "x"),
      aliasReceipt "x" 1, startReceipt 2 (some "x"), aliasReceipt "x" 2] },
  { label := "sequence self cycle is an edge not expansion"
    source := "&x [*x]"
    expectedNodes := #[sequenceNode #[0]]
    expectedReceipts := #[startReceipt 0 (some "x"), aliasReceipt "x" 0] },
  { label := "mapping self cycle is an edge not expansion"
    source := "&x {a: *x}"
    expectedNodes := #[mappingNode #[(1, 0)], scalarNode "\"a\""]
    expectedReceipts := #[startReceipt 0 (some "x"), startReceipt 1 none,
      aliasReceipt "x" 0] },
  { label := "new sequence start shadows prior scalar before its own alias"
    source := "[&x old, &x [*x]]"
    expectedNodes := #[sequenceNode #[1, 2], scalarNode "\"old\"", sequenceNode #[2]]
    expectedReceipts := #[startReceipt 0 none, startReceipt 1 (some "x"),
      startReceipt 2 (some "x"), aliasReceipt "x" 2] },
  { label := "completed inner alias chain preserves both shared targets"
    source := "[&a one, &b [*a], *b]"
    expectedNodes := #[sequenceNode #[1, 2, 2], scalarNode "\"one\"", sequenceNode #[1]]
    expectedReceipts := #[startReceipt 0 none, startReceipt 1 (some "a"),
      startReceipt 2 (some "b"), aliasReceipt "a" 1, aliasReceipt "b" 2] },
  { label := "ordinary closed collection sharing"
    source := "[&x [inner], *x]"
    expectedNodes := #[sequenceNode #[1, 1], sequenceNode #[2], scalarNode "\"inner\""]
    expectedReceipts := #[startReceipt 0 none, startReceipt 1 (some "x"),
      startReceipt 2 none, aliasReceipt "x" 1] },
  { label := "ordinary scalar"
    source := "plain"
    expectedNodes := #[scalarNode "\"plain\""]
    expectedReceipts := #[startReceipt 0 none] },
  { label := "ordinary block mapping"
    source := "k: inner\n"
    expectedNodes := #[mappingNode #[(1, 2)], scalarNode "\"k\"", scalarNode "\"inner\""]
    expectedReceipts := #[startReceipt 0 none, startReceipt 1 none, startReceipt 2 none] },
  { label := "ordinary empty sequence"
    source := "[]"
    expectedNodes := #[sequenceNode #[]]
    expectedReceipts := #[startReceipt 0 none] },
  { label := "ordinary empty mapping"
    source := "{}"
    expectedNodes := #[mappingNode #[]]
    expectedReceipts := #[startReceipt 0 none] }
]

def acceptedCasePasses (c : GraphCase) : Bool :=
  match graphLegacyReceipt c.source, graphIndexedReceipt c.source with
  | .ok legacy, .ok indexed =>
      legacy == indexed && legacy == expectedDocuments c && traceOrderMatched c.source
  | _, _ => false

def acceptedRecord (c : GraphCase) : Json :=
  Json.mkObj [
    ("label", .str c.label), ("input", .str c.source),
    ("pass", .bool (acceptedCasePasses c)),
    ("expected", expectedDocuments c),
    ("legacy", resultJson (graphLegacyReceipt c.source)),
    ("indexed", resultJson (graphIndexedReceipt c.source)),
    ("source_order", traceOrderRecord c.source)]

def rejectedCases : List (String × String) := [
  ("undefined alias", "[*x]"),
  ("forward alias", "[*x, &x inner]"),
  ("anchor scope ends at document boundary", "&x inner\n---\n*x\n")
]

def bothReject (source : String) : Bool :=
  match graphLegacyReceipt source, graphIndexedReceipt source with
  | .error _, .error _ => true
  | _, _ => false

def rejectedRecord (c : String × String) : Json :=
  Json.mkObj [
    ("label", .str c.1), ("input", .str c.2),
    ("pass", .bool (bothReject c.2)),
    ("legacy", resultJson (graphLegacyReceipt c.2)),
    ("indexed", resultJson (graphIndexedReceipt c.2))]

-- Emit named expected and actual answers before aggregate assertions. A
-- failed case therefore remains identifiable in an ordinary Lean CI log.
#eval IO.println (Json.arr (acceptedCases.toArray.map acceptedRecord)).compress
#eval IO.println (Json.arr (rejectedCases.toArray.map rejectedRecord)).compress

#guard acceptedCases.length == 17
#guard acceptedCases.all acceptedCasePasses
#guard rejectedCases.length == 3
#guard rejectedCases.all (fun c => bothReject c.2)

-- These are the unchanged original generic builder lemmas. Their dependency
-- inspection is separate from the executable, finite #guard qualification.
#print axioms MathGraph.GraphCompose.build_alias_exact
#print axioms MathGraph.GraphCompose.build_alias_unbound
#print axioms MathGraph.GraphCompose.build_alias_of_newly_started_node
#print axioms MathGraph.GraphCompose.build_scalar_exact
#print axioms MathGraph.GraphCompose.build_single_self_cycle

end L4YAML.IndependentAudit.GraphRequalification

end
