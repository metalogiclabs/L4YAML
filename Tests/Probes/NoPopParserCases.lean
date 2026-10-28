import L4YAML

namespace L4YAML.Tests.Probes

private def accepted (source : String) : Bool :=
  match L4YAML.TokenParser.parseYaml source with
  | .ok _ => true
  | .error _ => false

#guard accepted "a: 1\nb: 2\n"
#guard accepted "a:\n  x: 1\nb: 2\n"
#guard accepted "- a\n- b\n"
#guard accepted "- a: 1\n  b: 2\n"

-- A sequence root cannot become a mapping root without a document boundary.
#guard !accepted "- a\nb: 2\n"
#guard !accepted "- a\n? b\n: c\n"
#guard !accepted "- a\n: b\n"

end L4YAML.Tests.Probes
