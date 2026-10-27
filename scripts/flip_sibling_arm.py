#!/usr/bin/env python3
"""Price lane B's sibling arm (DOCS item 373): the `h_op = true` arm of the four
`_or_refused` wrappers (`rootMapRoute_or_refused`, `rootMapRouteF_or_refused`,
`bareNodeRoute_or_refused`, `topLevelFlowResumeSep_or_refused`) spends the bare
route unconditionally.  This flip makes each wrapper DEMAND that the landing is
at no open level (`h_nosib`), so every application that could reach the sibling
arm stops compiling; the breaks are the lines that must either route the open
level's continuation or declare the decline at the `[211]` flip.

Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`,
classifies with `scripts/flip_census.py`, restores; md5 printed both sides.
`--dry` patches nothing and reports the sites; `--keep` leaves the patch.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
GUARD = "  cases h_op : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) with\n"
NOSIB = "    (h_nosib : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false)\n"
WRAPPERS = ("rootMapRoute_or_refused", "rootMapRouteF_or_refused",
            "bareNodeRoute_or_refused", "topLevelFlowResumeSep_or_refused")
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    out, n = [], 0
    lines = text.splitlines(keepends=True)
    i = 0
    while i < len(lines):
        l = lines[i]
        if any(l.startswith(f"lemma {w} ") for w in WRAPPERS):
            # copy the signature up to the `:= by` line, inserting h_nosib before the conclusion
            j = i
            while not lines[j].rstrip().endswith(":= by"): j += 1
            # the conclusion starts at the first line after the last `(h_` binder
            k = j
            while k > i and not lines[k].lstrip().startswith("(h_"): k -= 1
            out.extend(lines[i:k + 1]); out.append(NOSIB); out.extend(lines[k + 1:j + 1])
            i = j + 1
            # the body: replace the `| true => exact …` arm by the refutation
            while i < len(lines) and not lines[i].startswith("lemma ") and not lines[i].startswith("/--"):
                if lines[i].startswith("  | true =>"):
                    out.append("  | true => exact absurd h_op (by rw [h_nosib]; decide)\n"); n += 1
                else:
                    out.append(lines[i])
                i += 1
            continue
        out.append(l); i += 1
    if n != 4: sys.exit(f"expected 4 `| true =>` arms, patched {n}; nothing to price")
    return "".join(out)
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    if "h_nosib" in SRC.read_text(): sys.exit("h_nosib already present: the arm is priced/landed, see DOCS item 373")
    before = md5(SRC); orig = SRC.read_text(); new = patch(orig)
    print(f"md5 before: {before}\nsites: 4 wrappers (signature + `| true =>` arm each)")
    if dry: return
    SRC.write_text(new)
    if keep: print(f"kept; md5 now {md5(SRC)}"); return
    try:
        log = ROOT / "scratch/373-flip-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run([sys.executable, "scripts/flip_census.py", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'NOT RESTORED'})")
if __name__ == "__main__": main()
