/-
Independent diagnostic for L4YAML 64795a8db28ccfdae85082c93b6453001ae9d3e4.
No production code is changed by this file.

Characterization probes below are source-derived hypotheses until checked by
Lean. This file does not certify its own successful execution.
-/
module

public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition
public import L4YAML.Output.Emitter
public meta import L4YAML.Output.Emitter

@[expose] public section

/-!
# Anchor declaration order versus node-completion order

YAML 1.2.2 §3.2.2.2 defines alias resolution using the most recent
serialization EVENT carrying that anchor. A collection's anchor belongs to
its START event, not its completion. Rebinding the same name within an
anchored collection therefore makes the inner declaration the current one.

Normative source: https://yaml.org/spec/1.2.2/#3222-anchors-and-aliases
Relevant implementation: `L4YAML/Spec/Types.lean`,
`YamlValue.resolveAliasesOrdered` (sequence/mapping branches) and
`YamlDocument.compose`. Public caller: `L4YAML/Parser/Composition.lean`,
`TokenParser.parseYaml`, which maps `compose` over `parseYamlRaw` output.

The core pair below is acyclic. The outer anchor is never referenced after
the inner declaration shadows it. Renaming that unused outer anchor must
not change the loaded content. These expectations are derived from the
event order, independently of L4YAML's resolver.

This is a DIAGNOSTIC, not a repaired regression test: current behavior is
printed and pinned, while `expectedContent` records the independent target.
The hand-built raw documents isolate `compose` from scanner/parser behavior.
The source cases check whether the end-to-end pipeline exposes the same gap.

The tests would cease to characterize the current bug if collection close
stopped overwriting a later inner anchor declaration. A repair must make
both load results equal to `expectedContent`, not change that expectation.
-/

namespace L4YAML.IndependentAudit.AnchorRebinding

open L4YAML
open L4YAML.TokenParser

def shadowSource : String := "[&x [&x inner], *x]"
def renamedSource : String := "[&outer [&x inner], *x]"
def startShadowSource : String := "[&x old, &x [*x]]"
def expectedContent : String := "[[\"inner\"], \"inner\"]"

def innerScalar : YamlValue :=
  .scalar { content := "inner", style := .plain, anchor := some "x" }

def rawShadow : YamlDocument :=
  { value := .sequence .flow
      #[.sequence .flow #[innerScalar] none (some "x"), .alias "x"] none none }

def rawRenamed : YamlDocument :=
  { value := .sequence .flow
      #[.sequence .flow #[innerScalar] none (some "outer"), .alias "x"] none none }

def actualShadow : YamlValue := rawShadow.compose.value
def actualRenamed : YamlValue := rawRenamed.compose.value

/-- Intended kernel-reduction test for the result inequality. No scanner,
    external oracle, `native_decide`, or deliberately weakened proof is used. -/
lemma composed_content_differs : (actualShadow == actualRenamed) = false := rfl

/-- Concrete incorrect result: the closing outer collection replaced the
    newer scalar binding. This pins the bug, not the normative contract. -/
lemma shadow_composes_to_outer_collection :
    actualShadow =
      .sequence .flow
        #[.sequence .flow
            #[.scalar { content := "inner", style := .plain }] none none,
          .sequence .flow
            #[.scalar { content := "inner", style := .plain }] none none]
        none none := rfl

/-- Renaming only the unreferenced outer binder restores the correct scalar. -/
lemma renamed_composes_to_inner_scalar :
    actualRenamed =
      .sequence .flow
        #[.sequence .flow
            #[.scalar { content := "inner", style := .plain }] none none,
          .scalar { content := "inner", style := .plain }]
        none none := rfl

def renderLoad (src : String) : String :=
  match parseYaml src with
  | .ok docs => String.intercalate " | "
      (docs.toList.map fun doc => Emit.emit doc.value)
  | .error e => "ERROR: " ++ reprStr e

def renderRaw (src : String) : String :=
  match parseYamlRaw src with
  | .ok docs => reprStr (docs.map (·.value))
  | .error e => "ERROR: " ++ reprStr e

def sourceCases : List (String × String) := [
  ("nested same-name sequence", shadowSource),
  ("unused outer anchor renamed", renamedSource),
  ("nested same-name mapping", "[&x {k: &x inner}, *x]"),
  ("mapping outer anchor renamed", "[&outer {k: &x inner}, *x]"),
  ("nested block same-name", "- &x\n  - &x inner\n- *x\n"),
  ("nested block outer renamed", "- &outer\n  - &x inner\n- *x\n"),
  ("sibling rebinding control", "[&x old, *x, &x inner, *x]"),
  ("closed collection control", "[&x [inner], *x]"),
  ("self alias accepted control", "&x [*x]"),
  ("self alias mapping control", "&x {a: *x}"),
  -- Here the second &x START shadows the earlier scalar immediately. The
  -- inner alias denotes the enclosing sequence, not the scalar "old".
  -- This is a cyclic graph identity obligation, separate from the acyclic
  -- content mismatch above and from any deliberate expansion limit.
  ("self alias shadows old binding", startShadowSource),
  ("undefined alias refused control", "[*x]"),
  ("forward alias refused control", "[*x, &x inner]"),
  ("document scope refused control", "&x inner\n---\n*x\n")
]

#eval ("hand-built same name", Emit.emit actualShadow)
#eval ("hand-built renamed", Emit.emit actualRenamed)
#eval ("independent target", expectedContent)
#eval ("raw same name", renderRaw shadowSource)
#eval ("raw renamed", renderRaw renamedSource)
#eval ("raw start-shadow", renderRaw startShadowSource)
#eval sourceCases.map (fun (label, src) => (label, renderLoad src))

-- Characterization of the current compose defect (hand-built input).
#guard Emit.emit actualShadow == "[[\"inner\"], [\"inner\"]]"
#guard Emit.emit actualRenamed == expectedContent
#guard (Emit.emit actualShadow == expectedContent) == false

-- Previously repaired declaration timing must remain repaired.
#guard (parseYaml "&x [*x]").isOk
#guard (parseYaml "&x {a: *x}").isOk
#guard (parseYaml "&x\n- *x\n").isOk
#guard (parseYaml "[*x]").isOk == false
#guard (parseYaml "[*x, &x inner]").isOk == false
#guard (parseYaml "&x inner\n---\n*x\n").isOk == false

#print axioms composed_content_differs
#print axioms shadow_composes_to_outer_collection
#print axioms renamed_composes_to_inner_scalar

end L4YAML.IndependentAudit.AnchorRebinding

end
