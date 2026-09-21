#!/usr/bin/env python3
"""PAY every optional premise whose left disjunct is itself vacuous, and let
the compiler say what the narrowing bought (DOCS item 227).

Item 226 answered "is a `_ ∨ True` premise NEEDED" by declining all of them at
once: `Or.inr trivial` everywhere, one build, zero errors.  It refused to drop
any, because the 163 are the surface a NARROWING lands on, and it closed by
asking what the narrowing is worth.

A narrowing replaces `A ∨ True` with `A`.  That is worth something only if `A`
is worth something, and for 22 of the premises it is not: their left disjunct
is `∃ ns : List Nat, ∀ nv ∈ ns, P nv`, which the EMPTY LIST proves.  So at
those sites `Or.inr trivial` and `Or.inl ⟨[], _⟩` are the same decline written
two ways, and narrowing moves the premise from one unconditional inhabitant to
another.

This script runs the other branch of item 226's experiment.  Same roster, same
insertion point, same two builds -- `decline_all_optional.shadow`'s `witness`
and `keep` seam -- but the witness is `Or.inl ⟨[], by simp⟩` and the roster is
filtered to the rows a probe has just watched the elaborator discharge that
way.  If the module builds, the PAYING branch is as free as the declining one
and the narrowing's worth at those sites is zero, by the compiler rather than
by a reading.

MEASURED (item 227), `StreamAccum`: see the item's entry in `DOCS.md`.

WHY THIS BUILDS FIRST, and again at the end: `lake env lean` does not rebuild
(item 226's own contamination).  Inherited from the module this imports.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from decline_all_optional import MODULE, ROOT, SCRATCH, SRC, run, shadow  # noqa: E402

PROBE = SCRATCH / "ChainRoster.lean"

PROBE_SRC = """import Tests.Guards.Proofs.PremiseNecessityCensus

open Lean Elab Command Meta Term in
open L4YAML.Proofs.StreamAccum in
open L4YAML.Tests.Guards.RelaySupplyCensus in
open Tests.Guards.HypothesisReaderCensus in
run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let stx ← `(term| by exact ⟨[], by simp⟩)
  let mut rows : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if isMechanism env nm then continue
    for (i, bn) in (optBinders ci.type).1 do
      let kind := if (match env.find? nm with
        | some (.ctorInfo _) => true | _ => false) then "ctor" else "lemma"
      let chain ← liftTermElabM do
        forallBoundedTelescope ci.type (some i) fun _ body => do
          match body with
          | .forallE _ a _ _ =>
              withoutModifyingState do
                try
                  let e ← withoutErrToSorry do elabTerm stx (some (a.getArg! 0))
                  synthesizeSyntheticMVarsNoPostponing
                  let e ← instantiateMVars e
                  if e.hasExprMVar || e.hasSorry then pure false
                  else do check e; pure true
                catch _ => pure false
          | _ => pure false
      rows := rows.push
        s!"ROSTER {nm.getString!}|{bn}|{i}|{kind}|{if chain then "chain" else "-"}"
  logInfo (String.intercalate "\\n" (rows.qsort (· < ·)).toList)
"""


def roster() -> list[tuple[str, ...]]:
    SCRATCH.mkdir(exist_ok=True)
    PROBE.write_text(PROBE_SRC)
    try:
        out = run(["lake", "env", "lean", str(PROBE.relative_to(ROOT))])
    finally:
        PROBE.unlink(missing_ok=True)
    rows = []
    for line in (out.stdout + out.stderr).splitlines():
        line = line.strip()
        if line.startswith("ROSTER "):
            rows.append(tuple(line[len("ROSTER "):].split("|")))
    if not rows:
        sys.exit("no roster rows; probe output was:\n" + out.stdout + out.stderr)
    return rows


def main() -> int:
    print("building first (a probe reads oleans, not sources)...")
    if run(["lake", "build"]).returncode != 0:
        return sys.exit("baseline build failed; refusing to measure")

    rows = roster()
    chain = [r for r in rows if r[4] == "chain"]
    print(f"roster {len(rows)} optional binders, {len(chain)} with a vacuous LEFT disjunct")
    backup = SRC.with_suffix(".lean.item227-backup")
    shutil.copy(SRC, backup)
    ok = False
    try:
        n, skipped = shadow(
            rows,
            witness="Or.inl ⟨[], by simp⟩",
            keep=lambda r: r[4] == "chain",
        )
        for why, k in sorted(skipped.items()):
            print(f"  skipped {k:>4}  {why}")
        print(f"  PAID {n}")
        out = run(["lake", "build", MODULE])
        log = out.stdout + out.stderr
        errors = len(re.findall(r": error", log))
        unref = len(re.findall(r"is not explicitly referenced", log))
        ok = out.returncode == 0 and errors == 0
        print(f"build      {'OK' if ok else 'FAILED'}  errors={errors}")
        print(f"linter     {unref} binders reported unreferenced")
        if not ok:
            print("--- errors ---")
            for line in log.splitlines():
                if ": error" in line:
                    print(line)
    finally:
        shutil.copy(backup, SRC)
        backup.unlink()
        print("restored; rebuilding so no later probe reads this experiment...")
        run(["lake", "build"])
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
