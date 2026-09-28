#!/usr/bin/env python3
"""What the frame's CLOSE can pay for a reshaped carrier (DOCS item 274).

Item 273 priced what receives the carrier and recorded the next step: reshape
`FlowBaseAnchor`'s `some` arm to `choice`, because the close is where the shape
is decided.  `FlowBaseAnchor.gate` proves `GateOf g` off `ParkAnchor`'s
EQUATION between two verdicts; `ParkSlot`'s two spends make a verdict FIRE
instead.  So the question this script asks is not what the reshape costs to
WRITE -- item 273 read that as `3 + 7` -- but what the slot branch of `gate`
can be closed with, and whether the premises it needs can be named where the
spend is applied.

    anchor    the control: `gate`'s existing proof, restated as a standalone
              probe over `ParkAnchor`.  It must read `B`, or the instrument is
              measuring its own scaffolding rather than the carriers.
    bare      the slot branch from the premises `gate` has today.
    nonoffer  the same, with §9.2's own two premises supplied -- the run
              STARTS at the open and the token in front of it offers no slot.
    offer     the same, with §8.1's premise supplied instead.
    floor     `offer` plus the close's own §8.1 reading.

    name      the premise the slot branch needs, written over `sc0`, on
              `FlowBaseAnchor.gate` and on `FlowBaseAnchor.gate_of_close`.
    wrap      the same premise written over `g` (`∀ sc0, g = some sc0 → …`).
    gate      the arity census of the wrapped premise on `gate`;
    close     the same on `gate_of_close` -- who must WRITE one;
    closable  the same on `PendingNode.pendingContent`'s `h_closable`, which
              is where a verdict on the close's own state lands -- the count of
              sites a FURTHER one would cost, re-derived where item 275 paid
              the second.

The five probes are ONE insertion and ONE elaboration: they are separate
declarations, so a refusal is reported against the probe that wrote it and the
others still read.  Each carries a null twin (`by assumption`) that must FAIL,
which is what says the row measured a derivation rather than a hypothesis the
scaffolding handed it.

The two rows that read `B` close by EX FALSO, so their premise sets are
contradictory on purpose and "is it vacuous" is the wrong question to ask of
them -- the contradiction IS the reading.  What is worth asking is whether each
half is realized by real inputs, and §14's sweep answers it: the slot-side
premises hold at 54 cells and 90, and the close-side reading each contradicts
(`hnd`, `hui`) is false at exactly those same cells.

Every probe restores the file it edited and prints the md5 either side.

Usage:
    python3 scripts/close_price.py probe
    python3 scripts/close_price.py all       # every probe but `wide`
    python3 scripts/close_price.py wide      # the tree census, minutes
"""
import hashlib
import re
import signal
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from coordinate_price import (  # noqa: E402
    ACC, ROOT, elaborate, enclosing_decl, error_loc,
)

PIN = ROOT / "Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean"

SELF = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")

#: The probes go AFTER both slot spends, at the head of the next section.
PROBE_ANCHOR = "/-! ### The `[96]` park's reading, relayed to its own RIDES (item 165)"

#: The four readings `gate` takes today, verbatim from its own signature.
CLOSE_READINGS = """\
    (hpre : ∀ j, j < s_bc.tokens.size → s_cl.tokens[j]! = s_bc.tokens[j]!)
    (hind : s_cl.indents = s_bc.indents)
    (hflow : s_cl.inFlow = false)
    (hlast : prevRealIdx? s_cl.tokens s_cl.tokens.size = some s_bc.tokens.size)
    (hclose : s_cl.tokens[s_bc.tokens.size]!.val.isFlowClose = true)
    (hnd : danglingNodePos? s_cl = none)"""

#: §9.2's two extra premises, as `ParkSlot.dangling_fires` states them.
NONOFFER = """\
    (hst : propsRunStart s_cl.tokens sc0.tokens.size = sc0.tokens.size)
    (hoff : ∀ j, prevRealIdx? s_cl.tokens sc0.tokens.size = some j →
      s_cl.tokens[j]!.val.offersNodeSlot = false)"""

#: §8.1's, as `ParkSlot.underIndented_eq` states it.
OFFER = """\
    (hoff : ∃ j, prevRealIdx? s_cl.tokens
        (propsRunStart s_cl.tokens sc0.tokens.size) = some j ∧
      s_cl.tokens[j]!.val.offersNodeSlot = true)"""

#: The close's own §8.1 reading -- the datum item 268 found NO declaration
#: holding, at either depth.
FLOOR_READ = "    (hui : underIndentedFlowValuePos? s_cl = none)"

FIRES = ("have hf := h.dangling_fires hpre hind hflow hlast hclose {hst} {hoff}; "
         "rw [hnd] at hf; simp at hf")
UNDER = ("have hf := h.underIndented_eq hpre hind hflow hlast hclose hoff; "
         "rw [{ui}] at hf; simp at hf")

#: (row, carrier, extra premises, the named derivation offered).
#:
#: `bare` and `offer` offer the RIGHT spend with `by assumption` standing where
#: the premise it lacks would go, so a refusal names the missing datum instead
#: of reporting a tactic that was never written.
ROWS = [
    ("anchor", "ParkAnchor", None,
     "exact ((h.dangling_eq hpre hind hflow hlast hclose).symm).trans hnd"),
    ("bare", "ParkSlot", None,
     FIRES.format(hst="(by assumption)", hoff="(by assumption)")),
    ("nonoffer", "ParkSlot", NONOFFER, FIRES.format(hst="hst", hoff="hoff")),
    ("offer", "ParkSlot", OFFER,
     UNDER.format(ui="(by assumption : underIndentedFlowValuePos? s_cl = none)")),
    ("floor", "ParkSlot", OFFER + "\n" + FLOOR_READ, UNDER.format(ui="hui")),
]
ROW_NAMES = [r[0] for r in ROWS]


def probe_block():
    """Every row and its null twin, as one insertion."""
    out = []
    for row, carrier, extra, tac in ROWS:
        for kind, body in (("probe", tac), ("null", "assumption")):
            prem = [f"    (h : {carrier} sc0 s_bc 0)", CLOSE_READINGS]
            if extra is not None:
                prem.append(extra)
            out.append(
                f"private lemma _{kind}274_{row} "
                "{sc0 s_bc s_cl : ScannerState}\n"
                + "\n".join(prem)
                + f" : GateOf (some sc0) := by\n  {body}\n")
    return "\n".join(out)


def _one(lines, needle):
    hits = [i for i, l in enumerate(lines) if l == needle]
    assert len(hits) == 1, f"expected exactly one {needle!r}, found {len(hits)}"
    return hits[0]


def run_probes(base, verbose=True):
    """One elaboration; a row is `B` when no error lands inside its probe."""
    lines = base.split("\n")
    i = _one(lines, PROBE_ANCHOR)
    lines[i:i] = probe_block().split("\n")
    patched = "\n".join(lines)
    ACC.write_text(patched)
    _, body = elaborate()
    plines = patched.split("\n")
    hit, why = {}, {}
    for l in body.split("\n"):
        m = SELF.match(l)
        if not m:
            continue
        d = enclosing_decl(plines, int(m.group(1)))
        hit.setdefault(d, []).append(l.strip())
    stray = sorted(d for d in hit if not d.startswith("_probe274_")
                   and not d.startswith("_null274_"))
    if stray:
        raise SystemExit("probe: the insertion broke declarations of its own "
                         f"host: {', '.join(stray)}")
    cells = {}
    for row in ROW_NAMES:
        ok = f"_probe274_{row}" not in hit
        vacuous = f"_null274_{row}" not in hit
        if vacuous:
            raise SystemExit(f"probe/{row}: `by assumption` PROVED the goal -- "
                             "the row reads a hypothesis, not a derivation.")
        cells[row] = "B" if ok else "O"
        if not ok:
            why[row] = hit[f"_probe274_{row}"][0]
        if verbose:
            print(f"  {cells[row]}  {row}", flush=True)
    return cells, why


# ------------------------------------------------------- naming, at the spend

GATE_HEAD = ("lemma FlowBaseAnchor.gate {g : Option ScannerState} "
             "{s_bc s_cl : ScannerState}")
CLOSE_HEAD = ("lemma FlowBaseAnchor.gate_of_close {g : Option ScannerState} "
              "{s_bc s_cl : ScannerState}")
#: `pendingBlockContent` carries a premise spelled the same way (item 159), so
#: the anchor is the CONSTRUCTOR and the premise is found under it.  The close
#: carries BOTH verdicts since item 275, so the dummy lands after the second.
PENDING_HEAD = "  | pendingContent (sp_start sp_block sp_scan : SurfPos)"
CLOSABLE = "        underIndentedFlowValuePos? sc = none → ∀ sp_mid,"
CLOSABLE2 = "        underIndentedFlowValuePos? sc = none → 0 = 0 → ∀ sp_mid,"


def patch_closable(base):
    """A second verdict on the close's own state, where the first one lands."""
    lines = base.split("\n")
    i = _one(lines, PENDING_HEAD)
    hits = [j for j in range(i, i + 24) if lines[j] == CLOSABLE]
    assert len(hits) == 1, (
        f"expected one {CLOSABLE!r} under `pendingContent`, found {len(hits)}")
    lines[hits[0]] = CLOSABLE2
    return "\n".join(lines)

#: An arity census counts error LOCATIONS: a shifted argument list reports one
#: application more than once (the `close` row reads four at two spends).  A
#: rename breaks each application exactly once, so `apps` is the honest count
#: of who APPLIES the spend, beside the count of what must be rewritten.
CLOSE_RENAME = CLOSE_HEAD.replace("gate_of_close", "gate_of_close_x")

BARE_PREM = ("    (hst : propsRunStart s_cl.tokens sc0.tokens.size = "
             "sc0.tokens.size)")
WRAP_PREM = ("    (hst : ∀ sc0, g = some sc0 → propsRunStart s_cl.tokens "
             "sc0.tokens.size = sc0.tokens.size)")

#: Lean prints `error(lean.unknownIdentifier): Unknown identifier `sc0.tokens``,
#: so matching prose would read a naming refusal as an arity one.  The error
#: CLASS and the identifier's root are what this row is actually about.
UNKNOWN = re.compile(r"lean\.unknownIdentifier.*`sc0")


def patch_prem(base, head, prem):
    lines = base.split("\n")
    i = _one(lines, head)
    lines[i + 1:i + 1] = [prem]
    return "\n".join(lines)


def patch_rename(base):
    lines = base.split("\n")
    lines[_one(lines, CLOSE_HEAD)] = CLOSE_RENAME
    return "\n".join(lines)


def run_name(base, head, prem, verbose=True):
    """Can the premise be STATED on this declaration?

    `O` is reserved for a refusal that names `sc0` as unknown: any other
    failure is the arity census below, not a naming one.
    """
    ACC.write_text(patch_prem(base, head, prem))
    ok, body = elaborate()
    errs = [l.strip() for l in body.split("\n") if SELF.match(l)]
    named = any(UNKNOWN.search(e) for e in errs)
    if verbose:
        print(f"  {'O' if named else 'B'}  {head.split()[1]}"
              f"{'  ' + errs[0][:110] if errs else ''}")
    if named:
        return "O", errs[0]
    if ok:
        raise SystemExit(
            f"name/{head.split()[1]}: adding a premise broke NOTHING -- "
            "the census below would be vacuous and the edit did not apply.")
    return "B", errs[0] if errs else ""


def run_flip(base, patched, label, verbose=True):
    """Elaborate the module under one edit; group the errors by declaration."""
    ACC.write_text(patched)
    _, body = elaborate()
    raw = sorted({int(m.group(1)) for m in
                  (SELF.match(l) for l in body.split("\n")) if m})
    if not raw:
        raise SystemExit(f"{label}: the flip broke nothing -- it did not apply")
    plines = patched.split("\n")
    by_decl = {}
    for r in raw:
        by_decl.setdefault(enclosing_decl(plines, r), []).append(r)
    if verbose:
        for d, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            # the lines too: a census of SITES inside one declaration is only
            # readable if a reader can see whether four errors are four spends
            # or one spend reported four times.
            print(f"  {len(hits):3d}  {d}  @ {', '.join(str(h) for h in hits)}")
    return len(raw), sorted(by_decl)


def run_wide(base, verbose=True):
    """The wrapped premise on `gate_of_close`, over the TREE."""
    ACC.write_text(patch_prem(base, CLOSE_HEAD, WRAP_PREM))
    r = subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    body = r.stdout + r.stderr
    hits, inside = {}, 0
    for l in body.split("\n"):
        loc = error_loc(l)
        if loc is None:
            continue
        if loc[0].endswith("Proofs/Production/StreamAccum.lean"):
            inside += 1
        else:
            hits.setdefault(loc[0], []).append(loc[1])
    # Item 271's two refusals, kept.
    if r.returncode == 0:
        raise SystemExit("wide: the tree BUILT under the flip -- a green build "
                         "here is not a census of zero.")
    if not hits and not inside:
        raise SystemExit("wide: the build failed and no location parsed -- the "
                         "census is absent rather than zero.")
    if verbose:
        print(f"  {inside:3d}  (inside the edited module)")
        for f, ls in sorted(hits.items()):
            print(f"  {len(ls):3d}  {f}")
    return inside, hits


# ------------------------------------------------------------------------- pin

BACKSLASH = chr(92)


def read_pin(name="expectedClosePrice"):
    """The pinned table as the guard file carries it, or None."""
    src = PIN.read_text()
    i = src.find(f"def {name} : String :=")
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
    cells = why = None
    name = {}
    flips = {}
    # A kill in the middle of a probe leaves the module PATCHED, and a patched
    # module is the one thing this instrument must never leave behind.
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(130))
    try:
        if which in ("probe", "all"):
            print("-- probe: what the slot branch of `gate` can be closed with")
            cells, why = run_probes(base)
        if which in ("name", "all"):
            print("-- name: can the premise be stated where the spend is?")
            for tag, head in (("gate", GATE_HEAD), ("close", CLOSE_HEAD)):
                name[("bare", tag)] = run_name(base, head, BARE_PREM)[0]
            for tag, head in (("gate", GATE_HEAD), ("close", CLOSE_HEAD)):
                name[("wrap", tag)] = run_name(base, head, WRAP_PREM)[0]
        if which in ("flip", "all"):
            print("-- flip: who must WRITE one, by declaration")
            for tag, head in (("gate", GATE_HEAD), ("close", CLOSE_HEAD)):
                print(f"   {tag}:")
                flips[tag] = run_flip(base, patch_prem(base, head, WRAP_PREM), tag)
            print("   apps:")
            flips["apps"] = run_flip(base, patch_rename(base), "apps")
            print("   closable:")
            flips["closable"] = run_flip(base, patch_closable(base), "closable")
        if which == "wide":
            print("-- wide: the wrapped premise on `gate_of_close`, over the tree")
            run_wide(base)
    finally:
        ACC.write_text(base)
    after = hashlib.md5(ACC.read_bytes()).hexdigest()
    print(f"\nmd5 {ACC.name}  before {before}  after {after}  "
          f"{'==' if before == after else '!! DIFFERS'}")
    if before != after:
        return 1
    if which != "all":
        return 0

    got = (" ".join(f"{n}=" + cells[n] for n in ROW_NAMES)
           + " name=" + "".join(name[("bare", t)] for t in ("gate", "close"))
           + " wrap=" + "".join(name[("wrap", t)] for t in ("gate", "close"))
           + "".join(f" {t}={flips[t][0]}/{len(flips[t][1])}"
                     for t in ("gate", "close", "closable"))
           + f" apps={flips['apps'][0]}")
    print("CLOSE-PRICE " + got)
    for t in ("gate", "close", "closable", "apps"):
        print(f"  {t} sites in: {', '.join(flips[t][1])}")
    for row, out in sorted(why.items()):
        print(f"  {row} refused: {out[:170]}")

    want = read_pin()
    if want is None:
        print(f"no pin in {PIN.relative_to(ROOT)}")
        return 1
    if want != got:
        print(f"CLOSE-PIN DISAGREES\n  Lean:   {want}\n  script: {got}")
        return 1
    print(f"CLOSE-PIN agrees with {PIN.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
