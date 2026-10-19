import L4YAML.Schema.Api
import L4YAML.Schema.Deriving
import L4YAML.Schema.Struct
import L4YAML.Output.Dump
open L4YAML

/-!
Regression probes for nasa-jpl/L4YAML#6. No mock parsers.
Quoted scalars are strings; typed values survive dump/reparse.
-/

structure Q where
  x : Option String
deriving Repr, BEq, Schema.FromYaml, Schema.ToYaml

def qNone : Q := { x := none }
def qNull : Q := { x := some "null" }

-- Source-origin style must take precedence over implicit Core resolution.
#guard (parseAs String "\"42\"\n").toOption == some "42"
#guard (parseAs String "\"true\"\n").toOption == some "true"
#guard (parseAs Bool "\"true\"\n").toOption.isNone
#guard (parseAs (Option String) "\"null\"\n").toOption == some (some "null")
#guard (parseAs Q "x: \"null\"\n").toOption.map (·.x) == some (some "null")

-- Typed serialization must not confuse data booleans/nulls with strings.
#guard Dump.dump (toYaml true) == "true"
#guard Dump.dump (toYaml [true, false]) == "- true\n- false"
#guard Dump.dump (toYaml ()) == "null"
#guard Dump.dump (toYaml (none : Option String)) == "null"
#guard Dump.dump (toYaml qNone) == "x: null"
#guard Dump.dump (toYaml qNull) == "x: \"null\""
#guard Dump.dump (toYaml ("42" : String)) == "\"42\""
#guard Dump.dump (toYaml ("true" : String)) == "\"true\""
#guard Dump.dump (toYaml ("null" : String)) == "\"null\""
#guard Dump.dump (toYaml (-7 : Int)) == "-7"
#guard (parseAs Q (Dump.dump (toYaml qNone))).toOption.map (·.x) == some none
#guard (parseAs Q (Dump.dump (toYaml qNull))).toOption.map (·.x) == some (some "null")
#guard (parseAs Int (Dump.dump (toYaml (-7 : Int)))).toOption == some (-7)
