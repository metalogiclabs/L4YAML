#!/usr/bin/env python3
"""What the RIDE can carry, and what the frame will receive (DOCS item 273).

Item 272 priced the ring an applied source needs — a conjunct on item 165's
`h_optok`, three sites in two declarations — and recorded an order for item
273: build the ride per arm first, because paying `optok` on its own adds a
premise two call sites must discharge for a carrier nothing spends.

That order was written from what each ring buys.  This script asks the question
it was written before: **what receives the carrier.**  A ride that takes a
`ParkSlot` has exactly one place to put it — the frame's own
`FlowBaseAnchor g s' 0` argument — and `FlowBaseAnchor`'s `some` arm names
`ParkAnchor`, a different carrier over the same core.

    slot      `ParkSlot s_prep s' 0` at the arm, ring PAID.  This is item 272's
              `pay` row re-taken as a standing fact rather than under a
              hypothesis: the payment is applied to the module and the probe
              carries no holes.
    floor     `ParkFloor s_prep s' 0` at the same arm — the frame's other half.
    prop_sc   `ParkAnchor`'s own field at the state the STEP began with, where
              the props arm can name it (`propsPark_prevReal_prop`).
    prop      the same field at the LANDING's park, which is the only park this
              family can open over (item 272's P3: preprocessing's pushes sit
              between the two arrays).
    gated     `FlowBaseAnchor (some s_prep) s' 0` — the frame argument itself.

    ride      the arity flip on `have drop_ride` — how many terms spend the
              ride.  A `have` has no arity to the repo, so this is the only way
              to count them, and the count is of SITES inside one declaration.
    carrier   three reshapes of `FlowBaseAnchor`'s `some` arm, each a census by
              declaration: `add` puts `ParkSlot` beside the anchor (item 268's
              `anchor` ring, re-derived), `swap` puts it in the anchor's place,
              `choice` makes the carrier a disjunction.
    transport the arity flip on `FlowBaseAnchor.transport`, the funnel every
              other carrier lemma goes through — the second wave any reshape
              pays.

The arm table is IMPORTED from `coordinate_price.py` and the payment from
`transport_price.py`; two copies of either drift (item 271).

Every probe restores the file it edited and prints the md5 either side.

Usage:
    python3 scripts/ride_price.py arm
    python3 scripts/ride_price.py all       # every probe but `wide`
    python3 scripts/ride_price.py wide      # the tree census, minutes
"""
import hashlib
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from coordinate_price import (  # noqa: E402
    ACC, ARMS, ROOT, elaborate, enclosing_decl, error_loc, probe_at,
    spend_lines,
)
from transport_price import OPEN_TOK, patch_pay, pay_tac  # noqa: E402

PIN = ROOT / "Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean"

#: `ParkFloor` at depth 0: the open clears the pending key and the stacked
#: range is empty.  Written exactly as `propsPark_open_gate` writes it, so a
#: reader can see the two are the same term and not two guesses.
FLOOR_TERM = ("exact ⟨KeyFloor.cleared h_opsk, "
              "fun i hlo hhi => absurd hhi (by omega)⟩")

#: `ParkAnchor.parkProp`, at whichever state the row names.
def prop_ty(state):
    return (f"∃ k, prevRealIdx? {state}.tokens {state}.tokens.size = some k ∧ "
            f"{state}.tokens[k]!.val.isNodeProperty = true")


#: The props arm holds the four fields the property law reads; the other two
#: parks have no `[96]` run, so there is no candidate to offer and the row is
#: `O` on `assumption` alone.  Naming that here rather than letting a reader
#: infer it from a blank is item 271's rule about shipped tables.
PROP_TERM = {
    "pendingProps": ("exact (propsPark_prevReal_prop h_real_p h_run h_anchor_p "
                     "h_tag_p).imp (fun k hk => ⟨hk.1, hk.2.1⟩)"),
    "pendingBlock": None,
    "pendingMapValue": None,
}


def intro(arm):
    """(prologue, the push, the kind) as the arm holds item 165's witness."""
    if OPEN_TOK[arm] is None:
        return "obtain ⟨p, htok, hop, hpos⟩ := h_optok; ", "htok", "hop"
    return "", OPEN_TOK[arm][1], OPEN_TOK[arm][2]


def rows(arm):
    """(name, type, named derivation or None) for one arm, in report order."""
    pre, tok, op = intro(arm)
    return [
        ("slot", "ParkSlot s_prep s' 0", pay_tac(arm)),
        ("floor", "ParkFloor s_prep s' 0", FLOOR_TERM),
        ("prop_sc", prop_ty("sc"), PROP_TERM[arm]),
        ("prop", prop_ty("s_prep"),
         None if PROP_TERM[arm] is None else PROP_TERM[arm]),
        ("gated", "FlowBaseAnchor (some s_prep) s' 0",
         pre + f"exact ⟨ParkAnchor.ofOpen {tok} {op} h_ind' h_noflow_prep "
               "(by assumption), ⟨KeyFloor.cleared h_opsk, "
               "fun i hlo hhi => absurd hhi (by omega)⟩⟩"),
    ]


ROW_NAMES = [n for n, _, _ in rows(ARMS[0])]


def run_arms(paid, idxs, verbose=True):
    """The five rows at each arm, on the module with the ring PAID."""
    cells, why = {}, {}
    for arm, li in zip(ARMS, idxs):
        for name, ty, named in rows(arm):
            ok_null, _ = probe_at(paid, li, ty, "assumption", "_probe273")
            if ok_null:
                cells[(arm, name)] = "P"
            elif named is None:
                cells[(arm, name)] = "O"
            else:
                ok_named, out = probe_at(paid, li, ty, named, "_probe273")
                cells[(arm, name)] = "B" if ok_named else "O"
                if not ok_named:
                    why[(arm, name)] = out
            if verbose:
                print(f"  {cells[(arm, name)]}  {arm:16s} {name}", flush=True)
    return cells, why


# ------------------------------------------------------------------ the flips

SELF = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")

RIDE_HEAD = "  have drop_ride :"
RIDE_TY = "      ∃ sp_gram' sp_block' sp_flow' sp_scan',"
RIDE_BODY = ("    ⟨sp_block, sp_block, sp_open, sp_open, h_stream_block, "
             "BlockStack.nil _,")

ANCHOR_ARM = "  | some sc0, s, d => ParkAnchor sc0 s d ∧ ParkFloor sc0 s d"
CARRIER = {
    "add": ANCHOR_ARM + " ∧ ParkSlot sc0 s d",
    "swap": "  | some sc0, s, d => ParkSlot sc0 s d ∧ ParkFloor sc0 s d",
    "choice": ("  | some sc0, s, d => (ParkAnchor sc0 s d ∨ ParkSlot sc0 s d)"
               " ∧ ParkFloor sc0 s d"),
}

TRANSPORT_F = "    (f : ∀ sc0, ParkAnchor sc0 s d → ParkFloor sc0 s d →"
TRANSPORT_F2 = ("    (f : ∀ sc0, 0 = 0 → ParkAnchor sc0 s d → "
                "ParkFloor sc0 s d →")


def _one(lines, needle):
    hits = [i for i, l in enumerate(lines) if l == needle]
    assert len(hits) == 1, f"expected exactly one {needle!r}, found {len(hits)}"
    return hits[0]


def patch_flip(base, which):
    """One edit that fails on ARITY, so the census is of sites that must write."""
    lines = base.split("\n")
    if which == "ride":
        # The ride's type spans five lines and its opening `∃` is not unique in
        # the file, so the anchor is the `have` and the line after it is
        # CHECKED rather than trusted.
        i = _one(lines, RIDE_HEAD)
        assert lines[i + 1] == RIDE_TY, (
            f"the ride's type does not start where it did: {lines[i + 1]!r}")
        lines[i + 1] = "      0 = 0 → " + RIDE_TY.strip()
        lines[_one(lines, RIDE_BODY)] = "    fun _ => " + RIDE_BODY.strip()
    elif which == "transport":
        lines[_one(lines, TRANSPORT_F)] = TRANSPORT_F2
    else:
        lines[_one(lines, ANCHOR_ARM)] = CARRIER[which]
    return "\n".join(lines)


def run_flip(base, which, verbose=True):
    """Elaborate the module alone under one flip; group by declaration."""
    patched = patch_flip(base, which)
    ACC.write_text(patched)
    _, body = elaborate()
    raw = sorted({int(m.group(1)) for m in
                  (SELF.match(l) for l in body.split("\n")) if m})
    if not raw:
        raise SystemExit(f"{which}: the flip broke nothing -- it did not apply")
    plines = patched.split("\n")
    by_decl = {}
    for r in raw:
        by_decl.setdefault(enclosing_decl(plines, r), []).append(r)
    if verbose:
        for d, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            print(f"  {len(hits):3d}  {d}")
    return len(raw), sorted(by_decl)


def run_wide(base, which, verbose=True):
    """The same flip over the TREE: who outside the module must write one."""
    ACC.write_text(patch_flip(base, which))
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
        raise SystemExit(f"wide/{which}: the tree BUILT under the flip -- a "
                         "green build here is not a census of zero.")
    if not hits and not inside:
        raise SystemExit(f"wide/{which}: the build failed and no location "
                         "parsed -- the census is absent rather than zero.")
    if verbose:
        print(f"  {inside:3d}  (inside the edited module)")
        for f, ls in sorted(hits.items()):
            print(f"  {len(ls):3d}  {f}")
    return inside, hits


# ------------------------------------------------------------------------- pin

BACKSLASH = chr(92)


def read_pin(name="expectedRidePrice"):
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
    ride = tr = None
    ride_d = tr_d = None
    carrier = {}
    try:
        if which in ("arm", "all"):
            print("-- arm: what each arm can build, with item 272's ring PAID")
            paid = patch_pay(base)
            ACC.write_text(paid)
            ok, body = elaborate()
            if not ok:
                raise SystemExit(
                    "arm: the paid module does not elaborate:\n"
                    + "\n".join(l for l in body.split("\n") if ": error" in l))
            idxs = spend_lines(paid)
            if len(idxs) != len(ARMS):
                raise SystemExit(f"expected {len(ARMS)} spends, found {len(idxs)}")
            cells, why = run_arms(paid, idxs)
        if which in ("ride", "all"):
            print("-- ride: how many terms spend the ride")
            ride, ride_d = run_flip(base, "ride")
        if which in ("carrier", "all"):
            print("-- carrier: three reshapes of the frame's `some` arm")
            for v in ("add", "swap", "choice"):
                print(f"   {v}:")
                carrier[v] = run_flip(base, v)
        if which in ("transport", "all"):
            print("-- transport: who goes through the carrier funnel")
            tr, tr_d = run_flip(base, "transport")
        if which == "wide":
            print("-- wide: the `choice` reshape over the tree")
            run_wide(base, "choice")
    finally:
        ACC.write_text(base)
    after = hashlib.md5(ACC.read_bytes()).hexdigest()
    print(f"\nmd5 {ACC.name}  before {before}  after {after}  "
          f"{'==' if before == after else '!! DIFFERS'}")
    if before != after:
        return 1
    if which != "all":
        return 0

    got = (" ".join(f"{n}=" + "".join(cells[(a, n)] for a in ARMS)
                    for n in ROW_NAMES)
           + f" ride={ride}/{len(ride_d)}"
           + "".join(f" {v}={carrier[v][0]}/{len(carrier[v][1])}"
                     for v in ("add", "swap", "choice"))
           + f" transport={tr}/{len(tr_d)}")
    print("RIDE-PRICE " + got)
    print(f"  ride sites in: {', '.join(ride_d)}")
    for v in ("add", "swap", "choice"):
        print(f"  {v} sites in: {', '.join(carrier[v][1])}")
    print(f"  transport sites in: {', '.join(tr_d)}")
    for (a, n), out in sorted(why.items()):
        first = next((l for l in out.split("\n") if ": error" in l), "")
        print(f"  {a}/{n} refused: {first.strip()[:160]}")

    want = read_pin()
    if want is None:
        print(f"no pin in {PIN.relative_to(ROOT)}")
        return 1
    if want != got:
        print(f"RIDE-PIN DISAGREES\n  Lean:   {want}\n  script: {got}")
        return 1
    print(f"RIDE-PIN agrees with {PIN.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
