import Scripts.Ledger
open Scripts.Ledger

-- Fixed regression obligations, including valid controls. No native_decide.
def gateRejects (text : String) : Bool :=
  !(check { pin := 0, rows := #[] }
    { pyFiles := #[], sites := sitesOfText "scripts/probe.sh" text, exes := #[] }).isEmpty

#guard gateRejects "python3 -B -c 'print(1)'"
#guard gateRejects "python3 -I -c 'print(1)'"
#guard gateRejects "python3 -W ignore -c 'print(1)'"
#guard gateRejects "python3 -Wignore -c 'print(1)'"
#guard gateRejects "python3 -X dev -c 'print(1)'"
#guard gateRejects "python3 -Xdev -c 'print(1)'"
#guard gateRejects "python3 -B -I -W ignore -c 'print(1)'"
#guard gateRejects "python3 -B scripts/unlisted.py"
#guard gateRejects "python3 -- scripts/unlisted.py"
#guard gateRejects "python3 --unknown-option -c 'print(1)'"
#guard gateRejects "python3"
#guard !gateRejects "python3 -B --version"
#guard !gateRejects "python3 -I --help"
#guard !gateRejects "echo 'python3 -B -c print(1)'"
#guard !gateRejects "cat <<'EOF'\npython3 -B -c 'print(1)'\nEOF\n"
#guard coveredModuleRun "python3 -B -m pytest Tests/test_python_ffi.py -v"
#guard !coveredModuleRun "python3 -B -m json.tool"

-- Exact ledger key is retained: adding a flag needs its own authorization.
def allowedInline : Inventory :=
  { pyFiles := #[], sites := sitesOfText "scripts/probe.sh" "python3 -B -c 'print(1)'", exes := #[] }
#guard check { pin := 1, rows := #[{ key := "inline:scripts/probe.sh:python3 -B -c 'print(1)'", cls := .G, status := .todo }] } allowedInline == #[]
#guard !(check { pin := 1, rows := #[{ key := "inline:scripts/probe.sh:python3 -c 'print(1)'", cls := .G, status := .todo }] } allowedInline).isEmpty
#guard check { pin := 1, rows := #[{ key := "scripts/allowed.py", cls := .G, status := .todo }] }
  { pyFiles := #["scripts/allowed.py"], sites := sitesOfText "scripts/probe.sh" "python3 -B scripts/allowed.py", exes := #[] } == #[]
