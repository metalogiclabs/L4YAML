module

public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Parser.Composition

@[expose] public section

namespace L4YAML.Research.AcceptedSource

open L4YAML Surface Grammar
open L4YAML.Proofs.Acceptance

/-- Five independent source productions. No optional separator whitespace is
    included in this family, and neither scanner nor parser execution defines it. -/
inductive QuotedPair : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s₃ s₄ s' : SurfPos) :
      GLit '[' s s₁ → SCDoubleQuotedOk s₁ s₂ → GLit ',' s₂ s₃ →
      SCDoubleQuotedOk s₃ s₄ → GLit ']' s₄ s' → QuotedPair s s'

end L4YAML.Research.AcceptedSource
