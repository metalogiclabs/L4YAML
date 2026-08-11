#!/usr/bin/env python3
"""CI gate: no orphan modules.

1. Every `L4YAML/**/*.lean` module must be transitively imported from one of the
   `@[default_target]` roots in `ROOTS` below — the library plus the four emitter
   exes (textual `import` parsing — deliberately NOT importGraph env-loading:
   merging the full Proofs environment trips a duplicate equation-lemma error,
   see .github/workflows/test-coverage.yml). Fenced code blocks are stripped
   before parsing, so a docstring example cannot satisfy the gate.
2. Every `Tests/Reflections/*.lean` must be imported by the
   `Tests/Reflections.lean` index (a file missing from the index is never
   built by CI and can rot silently).
"""

import re
import sys
from pathlib import Path

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.«»]+)", re.M)
FENCE_RE = re.compile(r"^```.*?^```", re.M | re.S)

# Closure roots: every `@[default_target]` whose root is a module, not just the
# library. `L4YAML.lean` is the library; the four emitters are opt-in modules
# reached through the exes that root at them (the Quick Start in L4YAML.lean's
# docstring documents them as separate imports on purpose — they are how the
# matrix observes the parser, not part of the umbrella API).  Rooting only at
# `L4YAML` reported them as orphans; see lakefile.lean.
ROOTS = ["L4YAML", "Tests.EmitEvents", "Tests.EmitJson",
         "Tests.EmitEventsIx", "Tests.EmitJsonIx"]


def module_of(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def imports_of(path: Path):
    """Imports of a module. Fenced code blocks are stripped first: a `​```lean`
    example inside a module docstring is documentation, not an import. Reading
    them as imports made `L4YAML.lean`'s Quick Start silently satisfy this gate
    for `Output.Events` and `Output.Json` — so two of the four emitters were
    reported as orphans and two were not (2026-08-11)."""
    return IMPORT_RE.findall(FENCE_RE.sub("", path.read_text()))


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    failures = []

    # --- 1. library reachability from the default targets ---
    lib_files = sorted((repo / "L4YAML").rglob("*.lean"))
    on_disk = {module_of(f.relative_to(repo)): f for f in lib_files}
    seen, frontier = set(), list(ROOTS)
    file_of = dict(on_disk)
    for root in ROOTS:
        file_of[root] = repo / Path(*root.split(".")).with_suffix(".lean")
    missing = [r for r in ROOTS if not file_of[r].exists()]
    if missing:
        print(f"closure root(s) not on disk (stale ROOTS in {Path(__file__).name}?): "
              f"{missing}", file=sys.stderr)
        return 1
    while frontier:
        mod = frontier.pop()
        if mod in seen:
            continue
        seen.add(mod)
        f = file_of.get(mod)
        if f is None or not f.exists():
            continue
        for imp in imports_of(f):
            if imp == "L4YAML" or imp.startswith("L4YAML."):
                frontier.append(imp)
    orphans = sorted(set(on_disk) - seen)
    for mod in orphans:
        failures.append(f"orphan library module (unreachable from any default "
                        f"target — {', '.join(ROOTS)}): "
                        f"{on_disk[mod].relative_to(repo)}")

    # --- 2. Tests/Reflections index completeness ---
    index = repo / "Tests" / "Reflections.lean"
    indexed = set(imports_of(index))
    for f in sorted((repo / "Tests" / "Reflections").glob("*.lean")):
        mod = f"Tests.Reflections.{f.stem}"
        if mod not in indexed:
            failures.append(f"unindexed reflection (add `import {mod}` to "
                            f"Tests/Reflections.lean): {f.relative_to(repo)}")

    if failures:
        print("\n".join(failures))
        print(f"error: {len(failures)} import-closure violations", file=sys.stderr)
        return 1
    print(f"OK: {len(on_disk)} library modules reachable from {len(ROOTS)} default "
          f"targets; Tests/Reflections index complete ({len(indexed)} imports)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
