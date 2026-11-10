import L4YAML.Config.Limits
import L4YAML.Parser.IndexedComposition

/-!
MathGraph research-only graph-identity boundary audit.

Input pair:
  a: &shared [1]    a: [1]
  b: *shared        b: [1]

The YAML representation graphs differ in node sharing.
This probe isolates raw serialization, pure composition and the exact
safe/limited composition used by the public FFI. It never changes
the upstream source or treats a comparison as a theorem proof.
-/

open L4YAML
open L4YAML.TokenParser

namespace MathGraph.GraphIdentityBoundary

def aliasSource : String := "a: &shared [1]\nb: *shared\n"
def copySource : String := "a: [1]\nb: [1]\n"
def differentSource : String := "a: [1]\nb: [2]\n"

def rawBothOK : Bool :=
  match TokenParser.Indexed.parseYamlRawIx aliasSource,
        TokenParser.Indexed.parseYamlRawIx copySource with
  | .ok a, .ok b => a.size == 1 && b.size == 1
  | _, _ => false

def rawDifferent : Bool :=
  match TokenParser.Indexed.parseYamlRawIx aliasSource,
        TokenParser.Indexed.parseYamlRawIx copySource with
  | .ok a, .ok b =>
      a.size == 1 && b.size == 1 && !(a[0]!.value == b[0]!.value)
  | _, _ => false

def pureComposeEqual : Bool :=
  match TokenParser.Indexed.parseYamlSingleRawIx aliasSource,
        TokenParser.Indexed.parseYamlSingleRawIx copySource with
  | .ok a, .ok b => a.compose.value == b.compose.value
  | _, _ => false

def limitedComposeEqual : Bool :=
  match TokenParser.Indexed.parseYamlSingleRawIx aliasSource,
        TokenParser.Indexed.parseYamlSingleRawIx copySource with
  | .ok a, .ok b =>
      match composeLimited a ({} : ParserLimits), composeLimited b ({} : ParserLimits) with
      | .ok ca, .ok cb => ca.value == cb.value
      | _, _ => false
  | _, _ => false

def publicSafeBothOK : Bool :=
  match parseYamlSingleSafe aliasSource, parseYamlSingleSafe copySource with
  | .ok _, .ok _ => true
  | _, _ => false

def publicSafeEqual : Bool :=
  match parseYamlSingleSafe aliasSource, parseYamlSingleSafe copySource with
  | .ok a, .ok b => a == b
  | _, _ => false

def positiveDistinct : Bool :=
  match parseYamlSingleSafe copySource, parseYamlSingleSafe differentSource with
  | .ok a, .ok b => !(a == b)
  | _, _ => false

#eval IO.println s!"MG_RAW_BOTH_OK={rawBothOK}"
#eval IO.println s!"MG_RAW_DIFFERENT={rawDifferent}"
#eval IO.println s!"MG_PURE_COMPOSE_EQUAL={pureComposeEqual}"
#eval IO.println s!"MG_LIMITED_COMPOSE_EQUAL={limitedComposeEqual}"
#eval IO.println s!"MG_PUBLIC_SAFE_BOTH_OK={publicSafeBothOK}"
#eval IO.println s!"MG_PUBLIC_SAFE_EQUAL={publicSafeEqual}"
#eval IO.println s!"MG_POSITIVE_DISTINCT={positiveDistinct}"


/-! ## Second-stage probe: anchor-present but never aliased -/
def anchoredCopySource : String := "a: &shared [1]\nb: [1]\n"

def rawAliasAnchoredDifferent : Bool :=
  match TokenParser.Indexed.parseYamlSingleRawIx aliasSource,
        TokenParser.Indexed.parseYamlSingleRawIx anchoredCopySource with
  | .ok a, .ok b => !(a.value == b.value)
  | _, _ => false

def pureResolvedAliasAnchoredEqual : Bool :=
  match TokenParser.Indexed.parseYamlSingleRawIx aliasSource,
        TokenParser.Indexed.parseYamlSingleRawIx anchoredCopySource with
  | .ok a, .ok b =>
      (a.value.resolveAliasesOrdered a.anchors).fst ==
        (b.value.resolveAliasesOrdered b.anchors).fst
  | _, _ => false

def limitedResolvedAliasAnchoredEqual : Bool :=
  match TokenParser.Indexed.parseYamlSingleRawIx aliasSource,
        TokenParser.Indexed.parseYamlSingleRawIx anchoredCopySource with
  | .ok a, .ok b =>
      match resolveAliasesLimited a.value a.anchors ({} : AliasLimits),
            resolveAliasesLimited b.value b.anchors ({} : AliasLimits) with
      | .ok ra, .ok rb => ra == rb
      | _, _ => false
  | _, _ => false

def limitedResolvedAnchoredPlainDifferent : Bool :=
  match TokenParser.Indexed.parseYamlSingleRawIx anchoredCopySource,
        TokenParser.Indexed.parseYamlSingleRawIx copySource with
  | .ok a, .ok b =>
      match resolveAliasesLimited a.value a.anchors ({} : AliasLimits),
            resolveAliasesLimited b.value b.anchors ({} : AliasLimits) with
      | .ok ra, .ok rb => !(ra == rb)
      | _, _ => false
  | _, _ => false

def strippedAnchoredPlainEqual : Bool :=
  match TokenParser.Indexed.parseYamlSingleRawIx anchoredCopySource,
        TokenParser.Indexed.parseYamlSingleRawIx copySource with
  | .ok a, .ok b =>
      match resolveAliasesLimited a.value a.anchors ({} : AliasLimits),
            resolveAliasesLimited b.value b.anchors ({} : AliasLimits) with
      | .ok ra, .ok rb => ra.stripAnchors == rb.stripAnchors
      | _, _ => false
  | _, _ => false

def publicThreeEqual : Bool :=
  match parseYamlSingleSafe aliasSource,
        parseYamlSingleSafe anchoredCopySource,
        parseYamlSingleSafe copySource with
  | .ok a, .ok b, .ok c => a == b && b == c
  | _, _, _ => false

#eval IO.println s!"MG2_RAW_ALIAS_ANCHORED_DIFFERENT={rawAliasAnchoredDifferent}"
#eval IO.println s!"MG2_PURE_RESOLVED_ALIAS_ANCHORED_EQUAL={pureResolvedAliasAnchoredEqual}"
#eval IO.println s!"MG2_LIMITED_RESOLVED_ALIAS_ANCHORED_EQUAL={limitedResolvedAliasAnchoredEqual}"
#eval IO.println s!"MG2_LIMITED_RESOLVED_ANCHORED_PLAIN_DIFFERENT={limitedResolvedAnchoredPlainDifferent}"
#eval IO.println s!"MG2_STRIPPED_ANCHORED_PLAIN_EQUAL={strippedAnchoredPlainEqual}"
#eval IO.println s!"MG2_PUBLIC_THREE_EQUAL={publicThreeEqual}"

end MathGraph.GraphIdentityBoundary
