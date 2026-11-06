module

public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition

/-!
# Public-parser controls for directive erasure

Qualification is external: pinned official CI receipts for the exact source
commit govern status; this file alone makes no passing claim.
These controls call the actual public parser, not a scanner surrogate.
They detect loss of duplicate-version rejection or document-scope reset.
The duplicate TAG positive is existing implementation behavior, already exercised
in `Tests/AdversarialInstantiation.lean`; it is not a YAML-validity claim.
No production behavior is changed here.
-/

namespace MathGraph.WholeSource.DirectiveControls

@[expose] public section

def one : String := "%YAML 1.2\n---"
def two : String := "%YAML 1.2\n%YAML 1.2\n---"

def publicAccept (input : String) : Bool :=
  (L4YAML.TokenParser.parseYaml input).toOption.isSome

-- Exact collision pair, both EOF forms, and nonempty-body controls.
#guard publicAccept "%YAML 1.2\n---" = true
#guard publicAccept "%YAML 1.2\n---\n" = true
#guard publicAccept "%YAML 1.2\n%YAML 1.2\n---" = false
#guard publicAccept "%YAML 1.2\n%YAML 1.2\n---\n" = false
#guard publicAccept "%YAML 1.2\n--- a" = true
#guard publicAccept "%YAML 1.2\n%YAML 1.2\n--- a" = false
#guard publicAccept "%YAML 1.2\n%YAML 1.1\n---" = false

-- A directive block per document is distinct from duplication in one block.
#guard publicAccept "%YAML 1.2\n---\n...\n%YAML 1.2\n---" = true
#guard publicAccept "%YAML 1.2\n---\n...\n%YAML 1.2\n---\n" = true

-- Existing TAG analogues: same-document duplicate acceptance is intentionally
-- pinned as implementation behavior, not as conformance to YAML 1.2.2 §6.8.2.
#guard publicAccept "%TAG !t! tag:x,2000:\n--- !t!a b" = true
#guard publicAccept "%TAG !t! tag:x,2000:\n%TAG !t! tag:y,2000:\n--- !t!a b" = true
#guard publicAccept "%TAG !t! tag:x,2000:\n--- !t!a b\n...\n%TAG !t! tag:y,2000:\n--- !t!c d" = true

end

end MathGraph.WholeSource.DirectiveControls
