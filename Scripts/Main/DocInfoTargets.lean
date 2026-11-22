module

public import Lean.Elab.ParseImportsFast
public import Lean.Util.Path

@[expose] public section

/-!
# Dependency-ordered API documentation priming

`lake exe scripts-doc-info-targets` prints one `+MODULE:docInfo` target per
local source module in the six qualification roots' import closures, with
dependencies before importers. It uses the same header parser as Lake;
comments, `public`/`meta` modifiers and `import all` are not inferred by regex.
External-package imports are left to Lake. This only schedules memory-bounded
priming: the complete documentation gate is still `lake build :docs`.
-/

namespace Scripts.Main.DocInfoTargets

open Lean

def roots : Array Name := #[
  `L4YAML, `Tests.Guards, `Tests.DeclineReachCensus,
  `Tests.DeclineArmCensus, `Tests.DeclineCornerCensus, `Tests.Reflections
]

/-- Postorder over local source imports; a cycle is an error, not a valid order. -/
partial def visit (mod : Name) (active : List Name) (ordered : Array Name)
    : IO (Array Name) := do
  if ordered.contains mod then return ordered
  if active.contains mod then
    throw <| IO.userError s!"cyclic source imports at {mod}"
  let path := modToFilePath "." mod "lean"
  if !(← path.pathExists) then return ordered
  let header ← parseImports' (← IO.FS.readFile path) path.toString
  let mut ordered := ordered
  for imp in header.imports do
    ordered ← visit imp.module (mod :: active) ordered
  return ordered.push mod

def run : IO Unit := do
  let mut ordered : Array Name := #[]
  for root in roots do
    let path := modToFilePath "." root "lean"
    if !(← path.pathExists) then
      throw <| IO.userError s!"missing documentation root {root}: {path}"
    ordered ← visit root [] ordered
  -- Emit only after the whole walk succeeds; an error cannot leave a partial list.
  for mod in ordered do IO.println s!"+{mod}:docInfo"

end Scripts.Main.DocInfoTargets

public def main (args : List String) : IO UInt32 := do
  if !args.isEmpty then
    IO.eprintln "usage: lake exe scripts-doc-info-targets (run from the repository root)"
    return 2
  try
    Scripts.Main.DocInfoTargets.run
    return 0
  catch e =>
    IO.eprintln s!"scripts-doc-info-targets: {e}"
    return 1
