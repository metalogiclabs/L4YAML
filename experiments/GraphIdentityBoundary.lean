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
import L4YAML.Config.Limits
import L4YAML.Parser.IndexedComposition

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

end MathGraph.GraphIdentityBoundary
