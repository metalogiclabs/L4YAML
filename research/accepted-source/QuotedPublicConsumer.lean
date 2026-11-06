module

public import QuotedPublic

open L4YAML L4YAML.Surface L4YAML.Grammar
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.Acceptance

namespace L4YAML.Research.AcceptedSource.Consumer

/- This unchanged consumer requires a theorem about arbitrary original source,
   not an emitter image, finite corpus, scanner-success premise, or token oracle. -/
example (input : String)
    (h : ∃ col, SCDoubleQuotedOk ⟨input.toList, 0⟩ ⟨[], col⟩) :
    ∃ docs, TokenParser.parseYaml input = .ok docs := by
  exact L4YAML.Research.AcceptedSource.source_quoted_public_accepts input h

end L4YAML.Research.AcceptedSource.Consumer
