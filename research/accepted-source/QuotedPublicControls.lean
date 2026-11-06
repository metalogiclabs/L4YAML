module

public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition

/-! Original-source public boundary observations. These executable controls
    complement, and do not replace, the arbitrary-input proof consumers. -/

namespace L4YAML.Research.AcceptedSource.PublicControls

open L4YAML Scanner

def accepted (s : String) : Bool := (TokenParser.parseYaml s).toOption.isSome

def values (s : String) : Option (List YamlToken) :=
  (Scanner.scanFiltered s).toOption.map (fun ts => ts.toList.map (·.val))

-- Independent spellings, not the output of emitScalar.
#guard accepted "\"\"" = true
#guard accepted "\"é\"" = true
#guard accepted "\"𝄞\"" = true
#guard accepted "\"\\x61\"" = true
#guard accepted "\"\\u0061\"" = true
#guard accepted "\"\\U00000061\"" = true
#guard accepted "\"\\n\"" = true
#guard values "\"\\x61\"" = some [.streamStart, .scalar "a" .doubleQuoted, .streamEnd]
#guard values "\"é\"" = some [.streamStart, .scalar "é" .doubleQuoted, .streamEnd]

-- Illegal raw controls, non-scalars, malformed escapes, and extra source.
#guard accepted "\"\x01\"" = false
#guard accepted "\"\\uD800\"" = false
#guard accepted "\"\\U00110000\"" = false
#guard accepted "\"\\xG1\"" = false
#guard accepted "\"\\q\"" = false
#guard accepted "\"a\"junk" = false
#guard accepted "\"unterminated" = false

-- A public success can lie outside the exact quoted-source family.
#guard accepted "\"a\" " = true
#guard accepted "a" = true

-- Five-piece flow composition and whole-scanner-output checks.
#guard accepted "[\"\",\"\"]" = true
#guard accepted "[\"é\",\"𝄞\"]" = true
#guard accepted "[\"\\x61\",\"\\u0062\"]" = true
#guard accepted "[\"\\n\",\"\\U00000061\"]" = true
#guard values "[\"\\x61\",\"\\u0062\"]" = some
  [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted,
   .flowEntry, .scalar "b" .doubleQuoted, .flowSequenceEnd, .streamEnd]
#guard accepted "[\"a\",\"b\"" = false
#guard accepted "[\"a\",\"b\"}" = false
#guard accepted "[\"a\",,\"b\"]" = false
#guard accepted "[\"a\"\"b\"]" = false
#guard accepted "[\"a\",\"\\uD800\"]" = false
#guard accepted "[\"a\",\"b\"]junk" = false

end L4YAML.Research.AcceptedSource.PublicControls
