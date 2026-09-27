#!/usr/bin/env python3
"""What the APPLIED source still owes the carrier (DOCS item 272).

Item 271 priced the coordinate `preprocess_landing_on_stack`'s premises cost at
the three arms that spend `drop_ride`, and item 272 landed the one real debt:
`preprocess_some_separate_at_floor`'s under-run disjunct carries item 147's
floor, so all three premises are readable at the arm and the source APPLIES.

Item 268 priced four rings for a carrier — `gate=49 anchor=2 route=3 eof=1` —
against a source that could not be applied at all.  This script asks the
question those numbers were taken before: with the source applied, what stands
between the membership it returns and a frame the close can spend?

    source    the membership at the arm: null (`assumption`) against the named
              composition.  This is the applied source, read by elaboration.
    hcol      the same membership in the shape `ParkSlot.ofOpen` names it —
              over the OPEN TOKEN's column rather than the landing's cursor —
              with the source offered as the named derivation.  The row is the
              gap, and the elaborator's own message names it.
    genesis   `ParkSlot s_prep s' 0` at the arm, GIVEN the position equation as
              a hypothesis.  A `B` here says the position equation is the only
              thing missing: everything else the genesis asks for is bound.
    optok     the arity flip on `h_optok`, item 165's own hypothesis — who must
              supply the open token's position.  This is the ring.
    frames    the arity flip on `h_kpkg`, the frame builder — how many frames
              the declaration constructs, all inside one declaration, so the
              census is of SITES and the declaration count is 1 by
              construction.
    ride      whether each arm's own binder is visible where `drop_ride` is
              BUILT.  The ride is one `have` before `cases h_pending`, so the
              data the source needs postdates the term that would carry it; the
              row is the second ring, and no arity flip can see it because a
              `have` has no arity.

The arm table is IMPORTED from `coordinate_price.py` rather than restated: item
271 found a shipped instrument naming the wrong arm, and two copies of a table
drift in exactly that way.

Every probe restores the file it edited and prints the md5 either side.

Usage:
    python3 scripts/transport_price.py source
    python3 scripts/transport_price.py all      # every probe but `wide`
    python3 scripts/transport_price.py wide     # the tree census, minutes
"""
import hashlib
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from coordinate_price import (  # noqa: E402
    ACC, ARMS, COL_TERM, FLOOR_H, IDENT, ROOT, elaborate, enclosing_decl,
    error_loc, probe_at, spend_lines, with_probe,
)

PIN = ROOT / "Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean"

#: The composition item 272 adds, instantiated at one arm.  Every name in it is
#: bound at the run-end half of that arm's under-run split.
def source_term(arm):
    return (f"underRunEnd_landing_on_stack h_preprocess h_base {FLOOR_H[arm]} "
            f"h_col02 hj h_ind h_end hcorr_prep "
            f"(_h_landed ({COL_TERM[arm]}) h_noflow_prep)")


MEM_TY = "(s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = true"
HCOL_TY = ("∀ p : Positioned YamlToken, s'.tokens = s_prep.tokens.push p → "
           "p.val.isFlowOpen = true → "
           "(s_prep.indents.any fun e => e.column == (p.pos.col : Int)) = true")
POS_TY = ("∀ p : Positioned YamlToken, s'.tokens = s_prep.tokens.push p → "
          "p.val.isFlowOpen = true → p.pos.col = s_prep.col")
GENESIS_TY = f"({POS_TY}) → ParkSlot s_prep s' 0"


#: The open token's push, in the shape each arm holds it.  `pendingProps` has
#: already destructured `h_optok` -- it is the one arm that builds a GATED
#: frame (`propsPark_open_gate`), and `obtain` consumes the existential -- so a
#: probe that re-opens it there reports an unknown identifier and would be read
#: as the genesis failing.  The other two arms never touch it.
OPEN_TOK = {
    "pendingProps": ("p_br", "h_br_tok", "h_br_open"),
    "pendingBlock": None,
    "pendingMapValue": None,
}


def genesis_tac(arm):
    src = source_term(arm)
    held = OPEN_TOK[arm]
    if held is None:
        intro = "obtain ⟨p, htok, hop⟩ := h_optok; "
        p_, tok, op = "p", "htok", "hop"
    else:
        intro = ""
        p_, tok, op = held
    return ("intro hpos; " + intro +
            f"refine ParkSlot.ofOpen {tok} {op} h_ind' h_noflow_prep ?_; "
            f"rw [hpos {p_} {tok} {op}]; exact {src}")


def rows(arm):
    """(name, type, named derivation) for one arm, in report order."""
    src = source_term(arm)
    return [
        ("source", MEM_TY, f"exact {src}"),
        # The RIGHT derivation, offered at the shape the genesis names.  It
        # fails on the column and on nothing else, which is the finding.
        ("hcol", HCOL_TY, f"exact fun p _ _ => {src}"),
        ("genesis", GENESIS_TY, genesis_tac(arm)),
    ]


# ------------------------------------------------------------------ the probes

def run_arms(base, idxs, verbose=True):
    """`source`, `hcol` and `genesis`, at each arm's run-end half."""
    cells, why = {}, {}
    for arm, li in zip(ARMS, idxs):
        for name, ty, named in rows(arm):
            ok_null, _ = probe_at(base, li, ty, "assumption", "_probe272")
            if ok_null:
                cells[(arm, name)] = "P"
            else:
                ok_named, out = probe_at(base, li, ty, named, "_probe272")
                cells[(arm, name)] = "B" if ok_named else "O"
                if not ok_named:
                    why[(arm, name)] = out
            if verbose:
                print(f"  {cells[(arm, name)]}  {arm:16s} {name}", flush=True)
    return cells, why


# --------------------------------------------------------------- the two flips

OPTOK = "      s'.tokens = s_prep.tokens.push p ∧ p.val.isFlowOpen = true)"
OPTOK2 = "      s'.tokens = s_prep.tokens.push p ∧ p.val.isFlowOpen = true ∧ 0 = 0)"
KPKG = "      FlowBaseAnchor g s' 0 →"
KPKG2 = "      FlowBaseAnchor g s' 0 → 0 = 0 →"
KPKG_FUN = "    fun g n _ _ h_st hfl h_anch h_b =>"
KPKG_FUN2 = "    fun g n _ _ h_st hfl h_anch _ h_b =>"
SELF = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")


def _one(lines, needle):
    hits = [i for i, l in enumerate(lines) if l == needle]
    assert len(hits) == 1, f"expected exactly one {needle!r}, found {len(hits)}"
    return hits[0]


def patch_flip(base, which):
    lines = base.split("\n")
    if which == "optok":
        lines[_one(lines, OPTOK)] = OPTOK2
    else:
        lines[_one(lines, KPKG)] = KPKG2
        lines[_one(lines, KPKG_FUN)] = KPKG_FUN2
    return "\n".join(lines)


def run_flip(base, which, verbose=True):
    """Elaborate the module alone under one arity flip; group by declaration."""
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
    # Item 271's two refusals, kept: a green build is not a census of zero, and
    # a failed build that parses no location is a broken pattern.
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


# -------------------------------------------------------------------- the pay

#: The ring, PAID: `h_optok` carries the open token's column, and the two call
#: sites supply it from the lemma they already rewrite with
#: (`scanFlow…Start_tokens` writes the token at `currentPos`, and the
#: `allowDirectives` update preserves it).  This is the difference between
#: pricing a ring and knowing the price can be met.
OPTOK_REAL = ("      s'.tokens = s_prep.tokens.push p ∧ p.val.isFlowOpen = true ∧" + chr(10) +
              "        p.pos.col = s_prep.col)")
PROPS_OBTAIN = "    obtain ⟨p_br, h_br_tok, h_br_open⟩ := h_optok"
PROPS_OBTAIN2 = "    obtain ⟨p_br, h_br_tok, h_br_open, h_br_pos⟩ := h_optok"
CALLSITE = ("              ⟨_, by rw [scanFlow{K}Start_tokens, "
            "allowDirectives_update_tokens], rfl⟩")
CALLSITE2 = ("              ⟨_, by rw [scanFlow{K}Start_tokens, "
             "allowDirectives_update_tokens], rfl," + chr(10) +
             "                by rw [allowDirectives_update_currentPos]; rfl⟩")


def patch_pay(base):
    lines = base.split("\n")
    lines[_one(lines, OPTOK)] = OPTOK_REAL
    lines[_one(lines, PROPS_OBTAIN)] = PROPS_OBTAIN2
    for kind in ("Sequence", "Mapping"):
        want = CALLSITE.format(K=kind)
        # the two call sites are indented differently; find by content
        hits = [i for i, l in enumerate(lines) if l.strip() == want.strip()]
        assert len(hits) == 1, f"expected one {kind} call site, got {len(hits)}"
        i = hits[0]
        ind = lines[i][:len(lines[i]) - len(lines[i].lstrip())]
        body = CALLSITE2.format(K=kind).split("\n")
        lines[i:i + 1] = [ind + body[0].strip(),
                          ind + "  " + body[1].strip()]
    return "\n".join(lines)


def pay_tac(arm):
    src = source_term(arm)
    held = OPEN_TOK[arm]
    if held is None:
        intro = "obtain ⟨p, htok, hop, hpos⟩ := h_optok; "
        tok, op, pos = "htok", "hop", "hpos"
    else:
        intro = ""
        tok, op, pos = held[1], held[2], "h_br_pos"
    return (intro + f"refine ParkSlot.ofOpen {tok} {op} h_ind' h_noflow_prep ?_; "
            f"rw [{pos}]; exact {src}")


def run_pay(base, verbose=True):
    """`ParkSlot` at the arm, with the ring paid -- no hypothesis, no holes."""
    paid = patch_pay(base)
    ACC.write_text(paid)
    ok, body = elaborate()
    if not ok:
        raise SystemExit("pay: the paid module does not elaborate:\n"
                         + "\n".join(l for l in body.split("\n")
                                     if ": error" in l)[:2000])
    idxs = spend_lines(paid)
    out = {}
    for arm, li in zip(ARMS, idxs):
        ok_n, _ = probe_at(paid, li, "ParkSlot s_prep s' 0", pay_tac(arm),
                           "_probe272")
        ok_a, _ = probe_at(paid, li, "ParkSlot s_prep s' 0", "assumption",
                           "_probe272")
        out[arm] = "P" if ok_a else ("B" if ok_n else "O")
        if verbose:
            print(f"  {out[arm]}  {arm:16s} ParkSlot (ring paid)", flush=True)
    return out


# ------------------------------------------------------------------- the ride

RIDE_ANCHOR = "  have drop_ride :"


def run_ride(base, verbose=True):
    """Is each arm's own binder visible where `drop_ride` is BUILT?

    The control is the other half of the reading: a binder that IS in scope
    there must elaborate, or the row would say `no` for a harness reason rather
    than for the declaration's.
    """
    lines = base.split("\n")
    li = _one(lines, RIDE_ANCHOR)
    seen = {}
    for arm in ARMS:
        ok, _ = probe_at(base, li, "True",
                         f"exact (fun _ => trivial) {IDENT[arm]}", "_probe272")
        seen[arm] = ok
        if verbose:
            print(f"  {'yes' if ok else 'no ':3s} {IDENT[arm]} ({arm}) at the ride")
    ok_ctl, _ = probe_at(base, li, "True",
                         "exact (fun _ => trivial) h_base", "_probe272")
    if verbose:
        print(f"  {'yes' if ok_ctl else 'no ':3s} h_base (control) at the ride")
    if not ok_ctl:
        raise SystemExit("ride: the CONTROL failed -- a hypothesis of the "
                         "declaration is invisible at the ride, so the probe "
                         "is measuring its own insertion and not the scope.")
    return sum(1 for a in ARMS if seen[a]), seen


# ------------------------------------------------------------------------- pin

BACKSLASH = chr(92)


def read_pin():
    """The pinned table as the guard file carries it, or None.

    Scanned character by character for the reason `coordinate_price.read_pin`
    gives: the literal is split with a trailing backslash continuation.
    """
    src = PIN.read_text()
    i = src.find("def expectedTransportPrice : String :=")
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
    idxs = spend_lines(base)
    if len(idxs) != len(ARMS):
        sys.exit(f"expected {len(ARMS)} spends, found {len(idxs)} -- the arm "
                 "population moved and this table is not about it")
    cells = why = None
    optok = frames = ride = pay = None
    optok_d = frames_d = None
    try:
        if which in ("arms", "all"):
            print("-- arms: the applied source, the shape the genesis names, "
                  "and the genesis")
            cells, why = run_arms(base, idxs)
        if which in ("optok", "all"):
            print("-- optok: who must supply the open token's position")
            optok, optok_d = run_flip(base, "optok")
        if which in ("frames", "all"):
            print("-- frames: how many frames the declaration builds")
            frames, frames_d = run_flip(base, "frames")
        if which in ("pay", "all"):
            print("-- pay: the genesis once the ring is paid")
            pay = run_pay(base)
        if which in ("ride", "all"):
            print("-- ride: what is in scope where `drop_ride` is built")
            ride, _ = run_ride(base)
        if which == "wide":
            # Held OUT of `all` and out of the battery: it rebuilds every
            # module that imports the patched one.  Its number is quoted in
            # DOCS rather than pinned, as `coordinate_price.py wide` is.
            print("-- wide: the `optok` ring over the tree")
            run_wide(base, "optok")
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
                    for n, _, _ in rows(ARMS[0]))
           + f" optok={optok} pay=" + "".join(pay[a] for a in ARMS)
           + f" frames={frames} ride={ride}/{len(ARMS)}")
    print("TRANSPORT-PRICE " + got)
    print(f"  optok sites in: {', '.join(optok_d)}")
    print(f"  frames sites in: {', '.join(frames_d)}")
    for (a, n), out in sorted(why.items()):
        first = next((l for l in out.split("\n") if ": error" in l), "")
        print(f"  {a}/{n} refused: {first.strip()[:160]}")

    want = read_pin()
    if want is None:
        print(f"no pin in {PIN.relative_to(ROOT)}")
        return 1
    if want != got:
        print(f"TRANSPORT-PIN DISAGREES\n  Lean:   {want}\n  script: {got}")
        return 1
    print(f"TRANSPORT-PIN agrees with {PIN.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
