module

public import Init.System.IO

/-!
The suite runner's opt-in tryparse protocol. Exit status alone cannot distinguish
a deliberate parse rejection from an uncaught runtime error. A conforming child
emits exactly one stdout line, after parsing and cleanup, with the matching status.
This records acceptance only; no parsed value or event output is compared.
-/

namespace Tests.SuiteRunner.Protocol

@[expose] public section

def acceptLine : String := "L4YAML_SUITE_ACCEPT\n"
def rejectLine : String := "L4YAML_SUITE_REJECT\n"

inductive Result where
  | accepted
  | rejected
  | error
  | timeout
  deriving Repr, BEq

/-- A marker embedded in a diagnostic, extra stdout, or a contradictory exit
    status is not a parse observation. The child is trusted to emit honestly. -/
def classify (exitCode : UInt32) (stdout : String) : Result :=
  if exitCode == 0 && stdout == acceptLine then .accepted
  else if exitCode == 1 && stdout == rejectLine then .rejected
  else if exitCode == 124 then .timeout
  else .error

/-- Human CLI output is unchanged unless the suite explicitly opts in. -/
def emit (accepted : Bool) : IO Unit := do
  if (← IO.getEnv "L4YAML_SUITE_PROTOCOL") == some "1" then
    IO.print (if accepted then acceptLine else rejectLine)
    (← IO.getStdout).flush

end

end Tests.SuiteRunner.Protocol
