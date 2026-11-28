module
public import Research.R2SequenceRetirement.MandatoryContext
public import L4YAML.Parser.Composition

@[expose] public section R2SequenceRetirementGeometry
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs

namespace R2SequenceRetirement.Geometry

def rootSource := "- a\n- b\n"
def indentlessValue := "a:\n- a\n- b\n"
def indentlessKey := "?\n- a\n- b\n: c\n"
def decoratedKey := "?\n- [a]\n- &p b\n: c\n"

def stackAt (input : String) (n : Nat) : Option (List (Int × Bool)) :=
  (R2MapOwnership.prefixes input n).map fun state =>
    state.indents.toList.map fun entry => (entry.column, entry.isSequence)

-- The ordinary root dash pushes a real sequence level.
lemma root_pushes_sequence : stackAt rootSource 1 = some [(-1,false), (0,true)] := by
  decide +kernel

-- These are actual successful initialized prefixes, not invented scanner states.
-- Indentless sequences reuse the mapping's width, so scanBlockEntry pushes no
-- sequence level. The PendingNode entry continuation is semantically necessary.
lemma value_has_mapping_top : stackAt indentlessValue 3 = some [(-1,false), (0,false)] := by
  decide +kernel

lemma key_has_mapping_top : stackAt indentlessKey 2 = some [(-1,false), (0,false)] := by
  decide +kernel

lemma key_keeps_mark :
    (R2MapOwnership.prefixes indentlessKey 3).map RegisterWitness.markedCols = some [0] := by
  decide +kernel

def nextDash (input : String) (n : Nat) : Option (Bool × Int × Nat) := do
  let state ← R2MapOwnership.prefixes input n
  match scanNextToken_preprocess state with
  | .ok (some (prep, '-')) => some (atSequenceIndent prep, prep.currentIndent, prep.col)
  | _ => none

lemma root_sibling_is_sequence_top : nextDash rootSource 2 = some (true,0,0) := by
  decide +kernel

lemma indentless_sibling_is_mapping_top : nextDash indentlessKey 3 = some (false,0,0) := by
  decide +kernel

lemma decorated_sibling_is_mapping_top : nextDash decoratedKey 5 = some (false,0,0) := by
  decide +kernel

-- Parser checks establish these are accepted inputs. They do not prove a
-- universal accumulator invariant or a grammar context for every decorated form.
#guard (L4YAML.TokenParser.parseYaml rootSource).isOk
#guard (L4YAML.TokenParser.parseYaml indentlessValue).isOk
#guard (L4YAML.TokenParser.parseYaml indentlessKey).isOk
#guard (L4YAML.TokenParser.parseYaml decoratedKey).isOk

#print axioms root_pushes_sequence
#print axioms indentless_sibling_is_mapping_top
#print axioms decorated_sibling_is_mapping_top

end R2SequenceRetirement.Geometry
end R2SequenceRetirementGeometry
