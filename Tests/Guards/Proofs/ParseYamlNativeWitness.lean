module
public import L4YAML.Parser.Composition
public import Tests.Guards.Proofs.TraceOfBlockAmbiguity
public meta import L4YAML.Parser.Composition
public meta import Tests.Guards.Proofs.TraceOfBlockAmbiguity

@[expose] public section Blanket

namespace L4YAML.Tests.Guards.ParseYamlNativeWitness

/-! Independent native executable observation on EXACT owner metagraph branch
aeacc60258b89fc1c5bb34b6f0ba9a5286801c02.
The checked alias ambiguity is held fixed.  Do not confuse `#guard` with
a kernel-proved `parseYaml` equality; the latter is checked separately. -/

#eval L4YAML.TokenParser.parseYamlRaw "a\n*x"
#eval L4YAML.TokenParser.parseYaml "a\n*x"
#eval (L4YAML.TokenParser.parseYaml "a\n*x").isOk
#guard (L4YAML.TokenParser.parseYaml "a\n*x").isOk
#guard (L4YAML.TokenParser.parseYaml "a").isOk
#guard (L4YAML.TokenParser.parseYaml "a\n&x").isOk

#check L4YAML.Tests.Guards.TraceOfBlockAmbiguity.traceOf_plainStar
#check L4YAML.Tests.Guards.TraceOfBlockAmbiguity.traceOf_alias
#check L4YAML.Tests.Guards.TraceOfBlockAmbiguity.traceWellFormed_refuted
#print axioms L4YAML.Tests.Guards.TraceOfBlockAmbiguity.traceWellFormed_refuted

end L4YAML.Tests.Guards.ParseYamlNativeWitness
end Blanket
