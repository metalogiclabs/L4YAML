#!/usr/bin/env python3
"""Narrow a no-op CONCLUSION and let the compiler price the obligation
(DOCS item 228).

Item 227 counted 27 declarations whose CONCLUSION `Or.inr trivial` proves: a
statement of the form `… ∨ True`, which is a theorem about nothing.  Item 227
stopped there on purpose — "the census says who would have to pay; nothing yet
says what the payment is worth" was item 226's complaint about PREMISES, and
the same complaint lands on conclusions.

This script performs the narrowing and lets `lake build` say what it costs.
The narrowed residue is `False`, which is the TIGHTEST narrowing there is: it
asserts the right arm is never taken.  Every place the proof reached for the
right disjunct then fails, and the error count IS the obligation.

  * `--each` narrows one declaration at a time and builds after each, so the
    price is attributed with no cascade.
  * `--all` narrows every declaration in the module at once — item 226's
    shape, one build — and the total is the price of narrowing the module.

A count of zero means the proof never reaches the right arm at all, and the
`∨ True` is decoration the statement could drop for free.

WHY `False` AND NOT THE HONEST RESIDUE.  The honest residue differs per lemma
(a `.commented` separation, a multi-line scalar body, an interior that crossed
a line) and choosing it is design work; `False` is uniform, needs no design,
and gives an UPPER bound on the number of sites that must produce a witness
under ANY narrowing.  A site that survives `∨ False` survives every narrowing.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

MODULES = {
    "FlowKeyLift": ("L4YAML/Proofs/Production/FlowKeyLift.lean",
                    "L4YAML.Proofs.Production.FlowKeyLift"),
    "StreamAccum": ("L4YAML/Proofs/Production/StreamAccum.lean",
                    "L4YAML.Proofs.Production.StreamAccum"),
    "PreprocessIndentStable": ("L4YAML/Proofs/Scanner/PreprocessIndentStable.lean",
                               "L4YAML.Proofs.Scanner.PreprocessIndentStable"),
}

DECL = re.compile(r"^(?:private )?(?:lemma|theorem) ([A-Za-z_][A-Za-z0-9_'!?.]*)")


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def strip_comment(s: str) -> str:
    j = s.find("--")
    return s[:j] if j >= 0 else s


def statement_span(lines: list[str], start: int) -> tuple[int, int] | None:
    """From the `lemma` line to the line whose stripped text ends the
    statement (`:=` or `:= by`).  Returns the inclusive line range."""
    for i in range(start, min(start + 700, len(lines))):
        s = strip_comment(lines[i]).rstrip()
        if s.endswith(":=") or s.endswith(":= by"):
            return start, i
    return None


def conclusion_site(lines: list[str], lo: int, hi: int) -> tuple[int, int] | None:
    """The LAST `∨ True` inside the statement span — the conclusion's."""
    for i in range(hi, lo - 1, -1):
        c = strip_comment(lines[i]).rfind("∨ True")
        if c >= 0:
            return i, c
    return None


def resolve(at: dict[str, int], nm: str) -> str | None:
    """A declaration is written under whatever suffix of its full name the
    surrounding `namespace` leaves — `IndentFloor.transport`, not
    `transport` and not `L4YAML.Proofs.PreprocessIndentStable.IndentFloor.transport`."""
    parts = nm.split(".")
    for i in range(len(parts)):
        k = ".".join(parts[i:])
        if k in at:
            return k
    return None


def decl_lines(lines: list[str]) -> dict[str, int]:
    at: dict[str, int] = {}
    for i, l in enumerate(lines):
        m = DECL.match(l)
        if m and m.group(1) not in at:
            at[m.group(1)] = i
    return at


def decl_end(lines: list[str], start: int) -> int:
    """The line before the next top-level declaration, docstring or `end`."""
    for i in range(start + 1, len(lines)):
        if DECL.match(lines[i]) or lines[i].startswith(("/-- ", "/-! ", "end ", "def ")):
            return i - 1
    return len(lines) - 1


def narrow_deep(src: Path, names: list[str]) -> tuple[dict[str, int], dict[str, str]]:
    """The conclusion, plus every `∨ True` in the proof BODY — the motives.

    A proof written as one recursor application hides its residue sites behind
    the motives: narrowing only the conclusion makes the elaborator report ONE
    mismatch for the whole term, and the count is then a fact about how the
    proof is written, not about the obligation.

    PREMISES are left alone, deliberately.  Narrowing a premise `A ∨ True` to
    `A ∨ False` STRENGTHENS the hypothesis, so a proof that relays it can get
    EASIER; a probe that narrowed premises too would under-report."""
    lines = src.read_text().split("\n")
    at = decl_lines(lines)
    hits, skipped = {}, {}
    for nm in names:
        short = resolve(at, nm)
        if short is None:
            skipped[nm] = "no declaration (projection or structure field)"
            continue
        span = statement_span(lines, at[short])
        if span is None:
            skipped[nm] = "no statement end"
            continue
        lo, hi = span
        site = conclusion_site(lines, lo, hi)
        if site is None:
            skipped[nm] = "no `∨ True` in the statement"
            continue
        k = 0
        i, c = site
        lines[i] = lines[i][:c] + "∨ False" + lines[i][c + len("∨ True"):]
        k += 1
        for j in range(hi + 1, decl_end(lines, at[short]) + 1):
            body = strip_comment(lines[j])
            n = body.count("∨ True")
            if n:
                k += n
                lines[j] = body.replace("∨ True", "∨ False") + lines[j][len(body):]
        hits[nm] = k
    src.write_text("\n".join(lines))
    return hits, skipped


def narrow(src: Path, names: list[str]) -> tuple[list[str], dict[str, str]]:
    """Rewrite each named declaration's conclusion `∨ True` to `∨ False`.
    Returns (narrowed, skipped-with-reason)."""
    lines = src.read_text().split("\n")
    at = decl_lines(lines)
    done, skipped = [], {}
    for nm in names:
        short = resolve(at, nm)
        if short is None:
            skipped[nm] = "no declaration (projection or structure field)"
            continue
        span = statement_span(lines, at[short])
        if span is None:
            skipped[nm] = "no statement end"
            continue
        site = conclusion_site(lines, *span)
        if site is None:
            skipped[nm] = "no `∨ True` in the statement"
            continue
        i, c = site
        lines[i] = lines[i][:c] + "∨ False" + lines[i][c + len("∨ True"):]
        done.append(nm)
    src.write_text("\n".join(lines))
    return done, skipped


#: Lake renders a Lean diagnostic as `error: <file>:<line>:<col>: <msg>`.
#: Matching `": error"` -- which `scripts/decline_all_optional.py` did, and
#: `scripts/pay_chain_optional.py` inherited -- never matches ANY line of it.
#: Those two scripts rested their verdict on the return code, which is sound;
#: their `errors=` column was not measuring anything.  Corrected at item 228.
ERROR_LINE = re.compile(r"^error: .*\.lean:\d+:\d+: ")


def build(module: str) -> tuple[int, list[str]]:
    out = run(["lake", "build", module])
    log = out.stdout + out.stderr
    errs = [l for l in log.splitlines() if ERROR_LINE.match(l)]
    return len(errs), errs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("module", choices=sorted(MODULES))
    ap.add_argument("names", nargs="+")
    ap.add_argument("--all", action="store_true",
                    help="narrow every name at once (one build)")
    ap.add_argument("--deep", action="store_true",
                    help="narrow every `∨ True` in the declaration, motives included")
    args = ap.parse_args()

    rel, module = MODULES[args.module]
    src = ROOT / rel
    backup = src.with_suffix(".lean.item228-backup")

    if run(["lake", "build", module]).returncode != 0:
        return sys.exit("baseline build failed; refusing to measure")

    groups = [args.names] if args.all else [[n] for n in args.names]
    shutil.copy(src, backup)
    try:
        for g in groups:
            shutil.copy(backup, src)
            if args.deep:
                hits, skipped = narrow_deep(src, g)
                done = [k for k, v in hits.items() if v]
                extra = " ".join(f"{k}:{v}" for k, v in hits.items())
            else:
                done, skipped = narrow(src, g)
                extra = ""
            for nm, why in skipped.items():
                print(f"  SKIP  {nm:<44} {why}")
            if not done:
                continue
            n, errs = build(module)
            tag = ",".join(done) if len(done) > 1 else done[0]
            print(f"  PRICE {tag:<44} errors={n}  {extra}")
            for e in errs:
                print(f"          {e.strip()[:160]}")
    finally:
        shutil.copy(backup, src)
        backup.unlink()
        run(["lake", "build", module])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
