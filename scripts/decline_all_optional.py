#!/usr/bin/env python3
"""Decline EVERY optional-context premise at once, and let the compiler answer
(DOCS item 226).

Item 225 censused the `_ ∨ True` premises by what the proof term DOES with them
-- `READ=85`, `RELAY=44` -- and closed by naming the `RELAY` lane as "the first
place one would look for a premise that could simply be dropped".  The reader
census cannot answer that question, and neither can item 226's dead-parameter
fixpoint: both measure what a proof does, and necessity is a question about the
STATEMENT.

For a premise of type `A ∨ True` the statement answers it alone -- the type is
unconditionally inhabited, so `opt_premise_buys_nothing` discharges it in one
line.  What is left is whether the proof BODY survives being handed the
canonical inhabitant instead of whatever its caller supplied, and that is a
question only the compiler can settle.  This script settles it, for all of them
at once:

  1. build (so the roster is read off a CURRENT olean -- see WHY THIS BUILDS
     FIRST below);
  2. read the roster of optional binders off the environment, with a throwaway
     probe under `L4YAML/Scratch/`;
  3. insert `have <binder> : <type> := Or.inr trivial` at the top of each
     lemma's proof, shadowing the premise;
  4. build the one module;
  5. restore the source and rebuild.

MEASURED (item 226), `StreamAccum`:

    roster                162 optional binders
      constructor fields   34   (no proof to shadow -- this is the ETA lane)
      term-mode proofs      9   (no `:= by` to insert into)
      SHADOWED            119
    build               0 errors, `Build completed successfully`
    linter              95 x "Variable name `...` is not explicitly referenced"

So every optional premise in the module can be declined at once and the module
still builds, and Lean's own `unusedVariables` linter -- which gates the
`UNUSED` lane and is blind to the `RELAY` one -- then names 95 of them.  The
substitution is what converts the ungated lane into the gated one.

Nothing is dropped on the strength of this.  The 163 are the narrowing surface
items 212-218 built a supply census to price; a premise that is vacuous today
is the slot a narrowing lands in tomorrow.

WHY THIS BUILDS FIRST, and again at the end.  `lake env lean <probe>` does NOT
rebuild dependencies: it reads whatever oleans are in `.lake/build`.  Run a
probe straight after this script's own experiment and it reads the experiment's
olean, in which every optional premise really IS unused -- which is exactly the
contamination that produced a first, wrong reading of item 226 (`probe.recal.log`
in the item's scratchpad).  The two builds are the fix, and they are not
optional.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML" / "Proofs" / "Production" / "StreamAccum.lean"
MODULE = "L4YAML.Proofs.Production.StreamAccum"
SCRATCH = ROOT / "L4YAML" / "Scratch"
PROBE = SCRATCH / "OptionalRoster.lean"

PROBE_SRC = """import Tests.Guards.Proofs.PremiseNecessityCensus

open Lean Elab Command in
open L4YAML.Proofs.StreamAccum in
open L4YAML.Tests.Guards.RelaySupplyCensus in
open Tests.Guards.HypothesisReaderCensus in
run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let mut rows : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if isMechanism env nm then continue
    for (i, bn) in (optBinders ci.type).1 do
      let kind := if (match env.find? nm with
        | some (.ctorInfo _) => true | _ => false) then "ctor" else "lemma"
      rows := rows.push s!"ROSTER {nm.getString!}|{bn}|{i}|{kind}"
  logInfo (String.intercalate "\\n" (rows.qsort (· < ·)).toList)
"""


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def roster() -> list[tuple[str, str, str, str]]:
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


def strip_comment(s: str) -> str:
    j = s.find("--")
    return s[:j] if j >= 0 else s


def shadow(rows) -> tuple[int, dict[str, int]]:
    """Insert one shadowing `have` per optional binder.  Returns (n, skipped)."""
    lines = SRC.read_text().split("\n")
    lemma_at: dict[str, int] = {}
    for i, l in enumerate(lines):
        m = re.match(r"^(?:private )?(?:lemma|theorem) ([A-Za-z_][A-Za-z0-9_'!?]*)", l)
        if m and m.group(1) not in lemma_at:
            lemma_at[m.group(1)] = i

    def binder_span(start: int, bname: str):
        for op, cl in (("(", ")"), ("{", "}")):
            pat = op + bname + " : "
            for i in range(start, min(start + 400, len(lines))):
                c = lines[i].find(pat)
                if c < 0:
                    continue
                depth, li, ci = 0, i, c
                while li < len(lines):
                    ch = lines[li][ci] if ci < len(lines[li]) else "\n"
                    if ch == op:
                        depth += 1
                    elif ch == cl:
                        depth -= 1
                        if depth == 0:
                            return i, c, li, ci, op
                    ci += 1
                    if ci >= len(lines[li]):
                        li, ci = li + 1, 0
        return None

    def proof_start(start: int):
        for i in range(start, min(start + 700, len(lines))):
            s = strip_comment(lines[i]).rstrip()
            if s.endswith(":= by"):
                return i, True
            if s.endswith(":="):
                return i, False
        return None, None

    inserts, skipped = [], {}
    for lem, bn, _idx, kind in rows:
        if kind == "ctor":
            skipped["constructor field"] = skipped.get("constructor field", 0) + 1
            continue
        if lem not in lemma_at:
            skipped["no lemma"] = skipped.get("no lemma", 0) + 1
            continue
        sp = binder_span(lemma_at[lem], bn)
        if sp is None:
            skipped["no binder"] = skipped.get("no binder", 0) + 1
            continue
        bi, bc, ei, ec, op = sp
        head = op + bn + " : "
        if bi == ei:
            ty = strip_comment(lines[bi][bc + len(head):ec])
        else:
            parts = [strip_comment(lines[bi][bc + len(head):])]
            parts += [strip_comment(lines[k]) for k in range(bi + 1, ei)]
            parts.append(strip_comment(lines[ei][:ec]))
            ty = " ".join(p.strip() for p in parts)
        ty = " ".join(ty.split())
        pi, isby = proof_start(ei)
        if pi is None:
            skipped["no proof"] = skipped.get("no proof", 0) + 1
            continue
        if not isby:
            skipped["term-mode proof"] = skipped.get("term-mode proof", 0) + 1
            continue
        inserts.append((pi, f"  have {bn} : {ty} := Or.inr trivial"))

    for pi, txt in sorted(inserts, key=lambda t: -t[0]):
        lines.insert(pi + 1, txt)
    SRC.write_text("\n".join(lines))
    return len(inserts), skipped


def main() -> int:
    print("building first (a probe reads oleans, not sources)...")
    if run(["lake", "build"]).returncode != 0:
        return sys.exit("baseline build failed; refusing to measure")

    rows = roster()
    backup = SRC.with_suffix(".lean.item226-backup")
    shutil.copy(SRC, backup)
    try:
        n, skipped = shadow(rows)
        print(f"roster {len(rows)} optional binders")
        for why, k in sorted(skipped.items()):
            print(f"  skipped {k:>4}  {why}")
        print(f"  SHADOWED {n}")
        out = run(["lake", "build", MODULE])
        log = out.stdout + out.stderr
        errors = len(re.findall(r": error", log))
        unref = len(re.findall(r"is not explicitly referenced", log))
        ok = out.returncode == 0 and errors == 0
        print(f"build      {'OK' if ok else 'FAILED'}  errors={errors}")
        print(f"linter     {unref} binders reported unreferenced")
        if not ok:
            print("--- first errors ---")
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
