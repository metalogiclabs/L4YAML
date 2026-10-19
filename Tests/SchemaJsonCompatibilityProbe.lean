import L4YAML.Output.Json

open L4YAML
open L4YAML.Schema

/-- Backward-compatible Json helper names agree with shared typed schema. -/
#guard L4YAML.Json.normalizeTag "!!int" == "tag:yaml.org,2002:int"
#guard L4YAML.Json.scalarType ({ content := "true", style := .plain } : Scalar) == .bool true
#guard L4YAML.Json.scalarType ({ content := "true", style := .doubleQuoted } : Scalar) == .str "true"
#guard L4YAML.Json.scalarType ({ content := "null", style := .singleQuoted } : Scalar) == .str "null"
