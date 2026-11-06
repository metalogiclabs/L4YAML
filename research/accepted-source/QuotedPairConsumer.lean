module

public import QuotedPair

open L4YAML

namespace L4YAML.Research.AcceptedSource.Consumer

/- Kept unchanged across RED and GREEN. Arbitrary original source and the
   independent five-piece grammar are the only external assumptions. -/
example (input : String)
    (h : ∃ col, QuotedPair ⟨input.toList, 0⟩ ⟨[], col⟩) :
    ∃ docs, TokenParser.parseYaml input = .ok docs := by
  exact L4YAML.Research.AcceptedSource.source_quoted_pair_public_accepts input h

end L4YAML.Research.AcceptedSource.Consumer
