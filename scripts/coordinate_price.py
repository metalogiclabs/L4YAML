#!/usr/bin/env python3
"""What the `drop_ride` coordinate costs, premise by premise (DOCS item 271).

Item 270 read each premise of `preprocess_landing_on_stack` with `by assumption`
at the three sites that spend `drop_ride` and scored PAID or OWED.  That
instrument asks whether a term of the type is ALREADY BOUND; it cannot tell a
premise the arm does not have from one the arm has in a different shape.  This
script asks the second question, and it asks it by elaboration too:

    bridge   null (`assumption`) against a NAMED derivation, per arm.  A row is
             PAID when the null succeeds, BRIDGE when only the named one does,
             and OWED when neither does.
    ident    the 3x3 arm-identity matrix -- one binder that exists in each arm
             probed at all three sites.  The diagonal must elaborate and the
             off-diagonal must not, which is what fixes the arm NAMES.
    split    the arity flip on `preprocess_some_separate_at_floor`: its
             under-run disjunct gains a component that is true everywhere
             (`0 = 0`), supplied in the lemma's own proof, so the census is of
             sites that must now WRITE something rather than of sites where the
             fact is hard (the reading item 208 established and items 266/268
             re-used).  Errors are grouped by DECLARATION, never by line.
    wide     the same flip with the module's own three sites repaired, built
             over the tree -- otherwise the modules that consume the splitter
             are never reached, because a module that fails builds none of its
             dependents (item 269's fixpoint reading).  Held OUT of `all`, and
             out of the battery, because it rebuilds 135 modules; its number is
             quoted in DOCS rather than pinned, as `wire_price.py --wide` is.
    reach    the REAL widening: the under-run disjunct carries item 147's
             guarded floor, which the splitter already proves and throws away.
             The arms then bind it, and the row reads what it takes to spend.

Every probe restores the file it edited and prints the md5 either side.

Usage:
    python3 scripts/coordinate_price.py bridge
    python3 scripts/coordinate_price.py all     # bridge, ident, split, reach
    python3 scripts/coordinate_price.py wide    # the tree census, minutes
"""
import hashlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ACC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
PIN = ROOT / "Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean"
SPEND = "exact drop_ride"

#: The three arms of `accum_flow_open_depth0`'s `cases h_pending`, in source
#: order.  Item 270 named the third `pendingContent`; `pendingContent` is a
#: different arm of the same `cases` and spends no ride.  `ident` checks this.
ARMS = ["pendingProps", "pendingBlock", "pendingMapValue"]

#: A binder each arm's own constructor declares and no other arm has.
IDENT = {
    "pendingProps": "h_col0_p",
    "pendingBlock": "h_col59",
    "pendingMapValue": "h_col0_mv",
}

#: The arm's `IndentFloor`, and the park column in the shape the arm holds it.
FLOOR_H = {
    "pendingProps": "h_floor_p",
    "pendingBlock": "h_floor_old",
    "pendingMapValue": "h_floor_mv",
}
COL_TERM = {
    "pendingProps": "Nat.ne_of_gt h_col0_p",
    "pendingBlock": "h_col59 ▸ Nat.succ_ne_zero n_old",
    "pendingMapValue": "Nat.ne_of_gt h_col0_mv",
}

LE_TY = "(s_prep.col : Int) ≤ sc.currentIndent"
COL_TY = "sp_scan.col ≠ 0"
FLOOR_TY = ("s_prep.currentIndent ≤ (s_prep.col : Int) ∨ "
            "s_prep.indents.size ≤ 1")


def bridge_rows(arm):
    """(name, type, named derivation or None) for one arm."""
    return [
        ("le", LE_TY,
         f"exact underRunEnd_col_le_currentIndent {FLOOR_H[arm]} h_col02 hj "
         "h_ind h_end hcorr_prep"),
        ("park_col_ne0", COL_TY, f"exact {COL_TERM[arm]}"),
        # No named derivation: the datum is not in scope under any spelling --
        # the splitter proves it and drops it.  `split`/`reach` price that.
        ("floor", FLOOR_TY, None),
    ]


def spend_lines(text):
    """The line index of each `exact drop_ride`, in source order.

    Two spellings reach the same tactic: a bare `exact drop_ride` and one
    focused by a `·`.  Matching only the bare form finds two of the three.
    """
    out = []
    for i, l in enumerate(text.split("\n")):
        s = l.strip()
        if s == SPEND or s == "· " + SPEND:
            out.append(i)
    return out


def with_probe(line, ty, tac):
    """The probe, inserted so it shares the tactic block with the spend."""
    indent = line[:len(line) - len(line.lstrip())]
    have = f"have _probe271 : {ty} := by {tac}"
    if line.strip().startswith("· "):
        return [f"{indent}· {have}", f"{indent}  {SPEND}"]
    return [f"{indent}{have}", line]


def elaborate():
    r = subprocess.run(["lake", "env", "lean", str(ACC.relative_to(ROOT))],
                       cwd=ROOT, capture_output=True, text=True)
    return r.returncode == 0, r.stdout + r.stderr


def probe_at(base, li, ty, tac):
    lines = base.split("\n")
    lines[li:li + 1] = with_probe(lines[li], ty, tac)
    ACC.write_text("\n".join(lines))
    return elaborate()


# ---------------------------------------------------------------- bridge/ident

def run_bridge(base, idxs, verbose=True):
    cells = {}
    for arm, li in zip(ARMS, idxs):
        for name, ty, named in bridge_rows(arm):
            ok_null, _ = probe_at(base, li, ty, "assumption")
            verdict = "P"
            if not ok_null:
                verdict = "O"
                if named is not None:
                    ok_named, out = probe_at(base, li, ty, named)
                    verdict = "B" if ok_named else "O"
            cells[(arm, name)] = verdict
            if verbose:
                print(f"  {verdict}  {arm:16s} {name}", flush=True)
    return cells


def run_ident(base, idxs, verbose=True):
    grid = {}
    for arm, li in zip(ARMS, idxs):
        for owner in ARMS:
            ok, _ = probe_at(base, li, "True",
                             f"exact (fun _ => trivial) {IDENT[owner]}")
            grid[(arm, owner)] = ok
            if verbose:
                print(f"  {'yes' if ok else 'no ':3s} site={arm:16s} "
                      f"binder={IDENT[owner]} ({owner})", flush=True)
    return grid


# ------------------------------------------------------------------ flip census

CONCL = ("          LandingTabFacts sc.currentIndent sc.needIndentCheck "
         "s_prep.peek? sp sp_mid) := by")
RETURN = "          Or.inr ⟨sp_mid, h_ssl_col.1, h_ssl_col.2.1, h_ur, h_ltsl⟩⟩"
ARM_PAT = ("    rcases h_sep_or with ⟨h_sep, h_floor_prep⟩ | "
           "⟨sp_mid2, _h_ssl2, h_col02, h_ur, h_ltsl2⟩")
FLOOR_HEAD = "lemma preprocess_some_separate_at_floor (n : Nat) (sc : ScannerState)"

DUMMY_CONCL = CONCL.replace(") := by", " ∧ 0 = 0) := by")
DUMMY_RETURN = RETURN.replace("h_ltsl⟩⟩", "h_ltsl, rfl⟩⟩")
REAL_CONCL = CONCL.replace(
    ") := by",
    " ∧\n          (sp.col ≠ 0 → s_prep.inFlow = false →\n"
    "            (s_prep.currentIndent ≤ (s_prep.col : Int) ∨\n"
    "              s_prep.indents.size ≤ 1))) := by")
REAL_RETURN = RETURN.replace(
    "h_ltsl⟩⟩", "h_ltsl, fun hc hf => (h_ssl_col.2.2 hc hf).2.2.2⟩⟩")


def _all(lines, needle):
    return [i for i, l in enumerate(lines) if l == needle]


def _floor_half(lines, needle, expect=2):
    """The occurrence that belongs to `preprocess_some_separate_at_floor`.

    Both splitters carry the line verbatim, so position alone would be faith.
    The index is checked against the lemma's own head line instead.
    """
    hits = _all(lines, needle)
    assert len(hits) == expect, f"expected {expect} of {needle!r}, got {len(hits)}"
    heads = [i for i, l in enumerate(lines) if l.startswith(FLOOR_HEAD)]
    assert len(heads) == 1, f"expected one {FLOOR_HEAD!r}, got {len(heads)}"
    after = [h for h in hits if h > heads[0]]
    assert len(after) == 1, f"{needle!r}: {len(after)} hits after the head"
    return after[0]


def patch_split(base, real=False, repair=False):
    lines = base.split("\n")
    lines[_floor_half(lines, CONCL)] = REAL_CONCL if real else DUMMY_CONCL
    lines[_floor_half(lines, RETURN)] = REAL_RETURN if real else DUMMY_RETURN
    if repair:
        pats = _all(lines, ARM_PAT)
        assert len(pats) == 3, f"expected 3 arm patterns, got {len(pats)}"
        extra = "h_floor147" if real else "_"
        for i in pats:
            lines[i] = ARM_PAT.replace("h_ltsl2⟩", f"h_ltsl2, {extra}⟩")
    return "\n".join(lines)


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def|structure|abbrev) "
                     r"([A-Za-z_][A-Za-z0-9_.'!?]*)", lines[i])
        if m:
            decl = m.group(1)
    return decl


def run_split(base, verbose=True):
    """Library census: elaborate the module alone under the arity flip."""
    patched = patch_split(base)
    ACC.write_text(patched)
    _, body = elaborate()
    here = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    raw = sorted({int(m.group(1)) for m in
                  (here.match(l) for l in body.split("\n")) if m})
    if not raw:
        raise SystemExit("split: the flip broke nothing -- it did not apply")
    plines = patched.split("\n")
    by_decl = {}
    for r in raw:
        by_decl.setdefault(enclosing_decl(plines, r), []).append(r)
    if verbose:
        for d, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            print(f"  {len(hits):3d}  {d}")
    return len(by_decl), sorted(by_decl)


#: The two drivers spell a location DIFFERENTLY, which is the whole reason this
#: probe first read an empty census for a flip that provably breaks a consumer:
#:
#:     lake env lean   Tests/.../X.lean:121:22: error: Tactic `rfl` failed
#:     lake build      error: Tests/.../X.lean:121:22: Tactic `rfl` failed
#:
#: A pattern written for either one reads NOTHING under the other -- the word
#: `error` moves from after the column to before the path -- and there is no
#: single anchored pattern that covers both, so both are spelled out and
#: `error_loc` tries each.  The format was measured, not read: a deliberate
#: `example : False := by rfl` under `lake build` prints the second line above.
LAKE_LOC = re.compile(r"^error: ([A-Za-z0-9_./-]+\.lean):(\d+):(\d+): ")
LEAN_LOC = re.compile(r"^([A-Za-z0-9_./-]+\.lean):(\d+):(\d+): error")
SELF = "Proofs/Production/StreamAccum.lean"


def error_loc(line):
    """`(file, line)` for a diagnostic from either driver, or None."""
    m = LAKE_LOC.match(line) or LEAN_LOC.match(line)
    return (m.group(1), int(m.group(2))) if m else None


def run_wide(base, verbose=True):
    """Tree census: the same flip with the module's own sites repaired."""
    ACC.write_text(patch_split(base, repair=True))
    r = subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    body = r.stdout + r.stderr
    hits, unrepaired = {}, []
    for l in body.split("\n"):
        loc = error_loc(l)
        if loc is None:
            continue
        if loc[0].endswith(SELF):
            unrepaired.append(l)
        else:
            hits.setdefault(loc[0], []).append(loc[1])
    if unrepaired:
        raise SystemExit("wide: the repair did not take -- the module still "
                         f"fails ({len(unrepaired)} sites), so nothing "
                         "downstream was built")
    # An arity flip that breaks nothing ANYWHERE has not been applied, or the
    # build never reached a consumer.  A green build is not a census of zero,
    # it is an absent census (CLAUDE.md section 9), so it is refused rather
    # than reported.
    if r.returncode == 0:
        raise SystemExit("wide: the tree BUILT under the flip -- so either the "
                         "probe did not apply or no consumer was reached.  A "
                         "green build here is not a census of zero.")
    # ...and a build that FAILED while parsing no location at all is a broken
    # pattern, not an empty census.  This is the assertion that was missing
    # when the probe printed zero consumers over three failed modules.
    if not hits:
        raise SystemExit("wide: the build failed and no location parsed -- the "
                         "diagnostic pattern does not match this driver's "
                         "output, so the census is absent rather than zero.")
    if verbose:
        for f, ls in sorted(hits.items()):
            print(f"  {len(ls):3d}  {f}")
        for mod in re.findall(r"Building (\S+)", "\n".join(
                l for l in body.split("\n") if l.lstrip().startswith("✖"))):
            print(f"       failed module: {mod}")
    return len(hits), sorted(hits)


def run_reach(base, idxs, verbose=True):
    """What the arms can spend once the splitter carries item 147's floor."""
    widened = patch_split(base, real=True, repair=True)
    ACC.write_text(widened)
    ok, body = elaborate()
    if not ok:
        raise SystemExit("reach: the widened splitter does not elaborate:\n"
                         + "\n".join(l for l in body.split("\n")
                                     if ": error" in l)[:2000])
    out = {}
    for arm, li in zip(ARMS, idxs):
        tac = f"exact h_floor147 ({COL_TERM[arm]}) h_noflow_prep"
        ok_n, _ = probe_at(widened, li, FLOOR_TY, tac)
        ok_a, _ = probe_at(widened, li, FLOOR_TY, "assumption")
        out[arm] = "P" if ok_a else ("B" if ok_n else "O")
        if verbose:
            print(f"  {out[arm]}  {arm:16s} floor (widened splitter)", flush=True)
    return out


# ------------------------------------------------------------------------- pin

BACKSLASH = chr(92)


def read_pin():
    """The pinned table as the guard file carries it, or None.

    Scanned character by character rather than matched: the literal is split
    with a trailing backslash, which is a line continuation and not a
    character, and a pattern that has to spell backslashes survives neither a
    heredoc nor a reviewer (item 270 shipped one that demanded two where Lean
    has one, found no pin, and was read as agreement).
    """
    src = PIN.read_text()
    i = src.find("def expectedCoordPrice : String :=")
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
            # a continuation: the backslash, the newline and the indent that
            # follows it all stand for nothing
            i += 1
            while i < len(src) and src[i] in " \t\n":
                i += 1
            continue
        out.append(ch)
        i += 1
    else:
        return None
    return "".join(out)


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    base = ACC.read_text()
    before = hashlib.md5(ACC.read_bytes()).hexdigest()
    idxs = spend_lines(base)
    if len(idxs) != len(ARMS):
        sys.exit(f"expected {len(ARMS)} spends of `{SPEND}`, found {len(idxs)} "
                 "-- the arm population moved and this table is not about it")
    cells = grid = reach = None
    lib = tree = None
    try:
        if which in ("bridge", "all"):
            print("-- bridge: null (assumption) against a named derivation")
            cells = run_bridge(base, idxs)
        if which in ("ident", "all"):
            print("-- ident: which arm each site is in")
            grid = run_ident(base, idxs)
        if which in ("split", "all"):
            print("-- split: the arity flip, by declaration, in the module")
            lib, libnames = run_split(base)
        if which == "wide":
            # NOT part of `all`: it rebuilds every module that imports the
            # patched one, twice over a battery run.  `wire_price.py --wide`
            # is held out of the battery for the same reason, and the number
            # it reports is quoted rather than pinned.
            print("-- wide: the same flip over the tree, module repaired")
            tree, treenames = run_wide(base)
        if which in ("reach", "all"):
            print("-- reach: the floor once the splitter carries it")
            reach = run_reach(base, idxs)
    finally:
        ACC.write_text(base)
    after = hashlib.md5(ACC.read_bytes()).hexdigest()
    print(f"\nmd5 {ACC.name}  before {before}  after {after}  "
          f"{'==' if before == after else '!! DIFFERS'}")
    if before != after:
        return 1
    if which != "all":
        return 0

    bad = [f"{a}/{o}" for a in ARMS for o in ARMS
           if grid[(a, o)] != (a == o)]
    ident = "diagonal" if not bad else "BROKEN:" + ",".join(bad)
    got = (f"arms={','.join(ARMS)} ident={ident} "
           + " ".join(f"{n}=" + "".join(cells[(a, n)] for a in ARMS)
                      for n, _, _ in bridge_rows(ARMS[0]))
           + f" lib={lib} "
           + "reach=" + "".join(reach[a] for a in ARMS))
    print("COORD-PRICE " + got)
    print(f"  library declarations broken: {', '.join(libnames)}")

    want = read_pin()
    if want is None:
        print(f"no pin in {PIN.relative_to(ROOT)}")
        return 1
    if want != got:
        print(f"COORD-PIN DISAGREES\n  Lean:   {want}\n  script: {got}")
        return 1
    print(f"COORD-PIN agrees with {PIN.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
