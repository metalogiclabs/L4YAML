import L4YAML.Parser.Composition

-- A consumed inner mapping may still gain siblings before its enclosing
-- entry gets a value. These executable controls precede the tail adapter.
#guard (L4YAML.TokenParser.parseYaml
  "? ? ? a\n    : b\n    ? c\n    : d\n: e\n").isOk
#guard (L4YAML.TokenParser.parseYaml
  "? ? ? ? a\n      : b\n      ? c\n      : d\n  : e\n: f\n").isOk
