#!/usr/bin/env python3
"""What each `drop_ride` arm HOLDS, premise by premise (DOCS item 270).

Item 269 restated the carrier's source and declined to say whether any arm can
feed it: "whether a given arm can supply the second is a measurement of that
arm, not of this lemma."  This is that measurement, and it is taken by
ELABORATION rather than by reading -- at each of the three sites that spend
`drop_ride`, a `have ... := by assumption` is inserted for each premise and the
module is elaborated.  A cell is PAID when a term already in scope has the type
and OWED when none does.

`by assumption` is `isDefEq` against the local context, so a cell reads PAID
only if the arm holds the premise itself -- not if it could derive it.  That is
the intended reading: the question is what the arm HAS, and a derivation is a
different bill from a binder.
"""
import hashlib, re, subprocess, sys
from pathlib import Path

ROOT = Path("/home/nfr/projects/lean/L4YAML")
ACC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
PIN = ROOT / "Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean"
BACKSLASH = chr(92)
SPEND = "exact drop_ride"

#: The three arms, in source order, named for the park each one is.  Item 271
#: fixed the third: the sites sit in `pendingProps`, `pendingBlock` and
#: `pendingMapValue`, and `pendingContent` is a different arm of the same
#: `cases` that spends no ride.  The names are checked by elaboration in
#: `scripts/coordinate_price.py`'s `ident` probe -- each arm's own constructor
#: declares a binder the other two do not, and the 3x3 matrix is diagonal.
ARMS = ["pendingProps", "pendingBlock", "pendingMapValue"]

#: `preprocess_floor_eq`'s four premises, then the two guards item 147's floor
#: sits behind in `preprocess_some_ssl_comments_anyCol`'s landed disjunct.
PREMISES = [
    ("hok",   "scanNextToken_preprocess sc = .ok (some (s_prep, c))", None),
    ("base",  "IndentStackBase.SentinelBase sc", None),
    ("le",    "(s_prep.col : Int) ≤ sc.currentIndent", None),
    ("floor", "s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1", None),
    ("noflow_prep", "s_prep.inFlow = false", None),
    ("park_col_ne0", "sp_scan.col ≠ 0", None),
    # Two rows that ask whether a NAME is in scope rather than whether a type
    # is inhabited: the gate's own output, and the floor the sibling arm holds.
    # `assumption` cannot ask this -- a name that is not bound is an elaboration
    # error, which is the reading.
    ("gate_gp", "True", "exact (fun _ => trivial) gp"),
    ("sibling_floor_prep", "True", "exact (fun _ => trivial) h_floor_prep"),
]



def read_pin():
    """The pinned table as the guard file carries it, or None.

    Scanned character by character rather than matched: the literal may be
    split with a trailing backslash, which is a line continuation and not a
    character, and a pattern that has to spell backslashes survives neither
    a heredoc nor a reviewer.
    """
    src = PIN.read_text()
    i = src.find('def expectedArmTable : String :=')
    if i < 0:
        return None
    i = src.find('"', i)
    if i < 0:
        return None
    out = []
    i += 1
    while i < len(src):
        ch = src[i]
        if ch == '"':
            break
        if ch == BACKSLASH:
            # a continuation: the backslash, the newline and the indent
            # that follows it all stand for nothing
            i += 1
            while i < len(src) and src[i] in ' \t\n':
                i += 1
            continue
        out.append(ch)
        i += 1
    else:
        return None
    return ''.join(out)

def spend_lines(text):
    """The line index of each `exact drop_ride`, in source order.

    Two spellings reach the same tactic: a bare `exact drop_ride` and one
    focused by a `·`.  Matching only the bare form finds two of the three,
    which is why the count is asserted below rather than trusted.
    """
    out = []
    for i, l in enumerate(text.split("\n")):
        s = l.strip()
        if s == SPEND or s == "· " + SPEND:
            out.append(i)
    return out


def with_probe(line, ty, tac=None):
    """The probe, inserted so it shares the tactic block with the spend."""
    indent = line[:len(line) - len(line.lstrip())]
    have = f"have _probe270 : {ty} := by {tac or 'assumption'}"
    if line.strip().startswith("· "):
        # focused: the dot takes the probe and the spend moves in under it
        return [f"{indent}· {have}", f"{indent}  {SPEND}"]
    return [f"{indent}{have}", line]


def main():
    pristine = ACC.read_text()
    before = hashlib.md5(ACC.read_bytes()).hexdigest()
    idxs = spend_lines(pristine)
    if len(idxs) != len(ARMS):
        sys.exit(f"expected {len(ARMS)} spends of `{SPEND}`, found {len(idxs)} "
                 "-- the arm population moved and this table is not about it")
    rows = []
    try:
        for a, (arm, li) in enumerate(zip(ARMS, idxs)):
            for name, ty, tac in PREMISES:
                lines = pristine.split("\n")
                lines[li:li + 1] = with_probe(lines[li], ty, tac)
                ACC.write_text("\n".join(lines))
                r = subprocess.run(
                    ["lake", "env", "lean", str(ACC.relative_to(ROOT))],
                    cwd=ROOT, capture_output=True, text=True)
                paid = r.returncode == 0
                rows.append((arm, name, paid))
                print(f"{'PAID' if paid else 'OWED'}  {arm:16s} {name}",
                      flush=True)
                if not paid:
                    for l in (r.stdout + r.stderr).split("\n"):
                        if "_probe270" in l or "assumption" in l:
                            print(f"      {l.strip()[:140]}")
                            break
    finally:
        ACC.write_text(pristine)
    after = hashlib.md5(ACC.read_bytes()).hexdigest()
    print(f"\nmd5 {ACC.name}  before {before}  after {after}  "
          f"{'==' if before == after else '!! DIFFERS'}")
    paid = sum(1 for _, _, p in rows if p)
    got = f"cells={len(rows)} paid={paid} owed={len(rows) - paid}"
    for name, _, _ in PREMISES:
        per = "".join("P" if p else "O" for a, n, p in rows if n == name)
        got += f" {name}={per}"
    print("ARMTABLE " + got)

    rc = 0 if before == after else 1
    want = read_pin()
    if want is None:
        print(f'no pin in {PIN.relative_to(ROOT)}')
        return 1
    if want != got:
        print(f'ARM-PIN DISAGREES\n  Lean:   {want}\n  script: {got}')
        rc = 1
    else:
        print(f'ARM-PIN agrees with {PIN.relative_to(ROOT)}')
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
