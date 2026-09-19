#!/usr/bin/env python3
"""Price `KeyPackPunt`'s four reasons, and decide the phantom (item 211).

Item 184 measured the two surviving reasons twice and recorded the agreement:

    Deleting each constructor and building breaks exactly: `dedent` 7
    applications in 5 definitions ... and `noKeyContext` 6 in 5 ...
    `FlipConsumerSurface`'s new PACK PUNT lane reads the same rows from the
    elaborated environment -- a narrowing patch and an environment census,
    agreeing row for row, and the census is what makes the number re-derivable
    at every future item rather than remembered from this one.

Half of that is true.  The environment census IS re-derived at every build and
still reads 7/5 and 6/5 at item 211.  The deletion patch was run once, at item
184, and its agreement with the census has ridden twenty-two NEXT lists by hand.
This script is that half, as an artifact.

Both numbers reproduce.  Three things around them do not.

MEASURED (item 211), `lake env lean` on StreamAccum:

                    deletion       environment      split
                    errors/decls   applications     productions/consumer arms
    tab             7 / 5          5 / 5            2 / 3
    dedent          7 / 5          7 / 5            4 / 3
    implicitValue   6 / 6          6 / 6            3 / 3
    noKeyContext    6 / 5          6 / 5            3 / 3

1.  THE TWO INSTRUMENTS DISAGREE, at `tab`.  Item 189 said why in passing --
    "a `match` costs more to break than an `Or.inr trivial`" -- and here it is:
    `tab` is written as `refine Or.inr (KeyPackPunt.tab ?_ ...)` at both its
    productions, and the orphaned `?_` goal is a second error each time.  So the
    agreement item 184 recorded is a fact about those two reasons, not about the
    method, and the first third reason it is asked of breaks it.

2.  THE UNIT GLUES TWO KINDS OF SITE.  `dedent`'s 7 is 4 PRODUCTIONS and 3
    CONSUMER ARMS; `noKeyContext`'s 6 is 3 and 3.  A production hands the reason
    over and is emptied by a proof about the input; a consumer arm is the
    `cases` label that spends it and goes when the last production does.  The
    surface that has to be paid is 7 productions, not 13 sites.

3.  `tab` AND `implicitValue` ARE STILL PRODUCED -- 2 and 3 times -- against
    `FlipConsumerSurface`'s "refuted at their consumers and have no producer
    left".  They are refuted at ONE consumer (`colon_fires_implicit_key`); at
    `colon_fires_props_key` `tab` RIDES the deferral exactly as `dedent` and
    `noKeyContext` do -- three unconditionally, and `implicitValue` on its
    break branch too, so the inline class has at least THREE surviving reasons
    there and two at its sibling.

`keyPackPunt_transport` is reported on its own line at every reason, for the
census's own reason: it re-writes a reason it was handed rather than spending
one, so it is a transport of the surface and not part of it.

THE PHANTOM.  Item 184 noted `noKeyContext` had no named input, "which by R646
is the signature of a branch that may be a phantom".  `reaches` decides it at
the production: `content_dispatch_routed` reaches the punt only when FIVE
optional contexts decline at once, and of its 8 applications exactly ONE does
(L31195, the `---` marker park), while SEVEN relay their own `h_keyctx` to
their callers.  The one that declines is the park whose key class the scanner
refuses outright (`--- a: 1` = `contentOnDocumentStartLine`, item 43), so the
punt there is produced for inputs no parse reaches.  And at
`flowKeyPack_of_close` both callers pay with `close_col_of_base` and
`resume.key`, which carry the same `∨ True` -- so the decision moves down a
construct again.  "Possibly a phantom" is the right doubt for the wrong reason:
it is not a missing input, it is a RELAY, and naming the input means following
the conjunct's value through the relays that carry it -- item 201's open census.

Usage:
    python3 scripts/punt_reason_price.py all       # the deletion control
    python3 scripts/punt_reason_price.py split     # productions vs consumer arms
    python3 scripts/punt_reason_price.py reaches   # the phantom, at the production
    python3 scripts/punt_reason_price.py phantom   # the flow close's two switches
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

REASONS = ["tab", "dedent", "implicitValue", "noKeyContext"]

# The declaration the PACK PUNT lane skips, and why.  Printed apart rather than
# dropped: an instrument that hides a row cannot be asked about it.
TRANSPORT = "keyPackPunt_transport"


def inductive_block(lines):
    """`(first, last)` line indices of `inductive KeyPackPunt`'s constructors."""
    start = next(i for i, l in enumerate(lines)
                 if l.startswith("inductive KeyPackPunt "))
    end = next(i for i in range(start + 1, len(lines)) if not lines[i].strip())
    return start + 1, end


def constructor_span(lines, reason):
    """The line range `| <reason> ...` occupies, one constructor's worth."""
    first, last = inductive_block(lines)
    heads = [i for i in range(first, last)
             if re.match(r"^  \| \w+", lines[i])]
    assert len(heads) == len(REASONS), \
        f"{len(heads)} constructors, expected {len(REASONS)} -- the type moved"
    for j, i in enumerate(heads):
        if re.match(rf"^  \| {reason}\b", lines[i]):
            return i, (heads[j + 1] if j + 1 < len(heads) else last)
    raise SystemExit(f"no constructor `{reason}` in KeyPackPunt")


def apply_delete(lines, reason):
    """Comment the constructor out, keeping every other line where it is.

    Commenting rather than deleting is what keeps the reported line numbers
    the ones a reader can open, which is the whole point of grouping by the
    enclosing declaration.
    """
    lo, hi = constructor_span(lines, reason)
    out = list(lines)
    for i in range(lo, hi):
        out[i] = "  -- PUNT REASON DELETED (scripts/punt_reason_price.py): " \
            + out[i].strip()
    return out, (lo + 1, hi)


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def|abbrev) (\w+)", lines[i])
        if m:
            decl = m.group(1)
    return decl


def price(reason, lines):
    backup = TARGET.with_suffix(".lean.punt-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched, span = apply_delete(lines, reason)
        TARGET.write_text("\n".join(patched))
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True)
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    pat = re.compile(
        r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    hits = sorted({int(m.group(1)) for line in body.split("\n")
                   if (m := pat.match(line))})
    # the constructor's own lines are the patch, not a site
    hits = [h for h in hits if not (span[0] <= h <= span[1])]
    census = {}
    for h in hits:
        census.setdefault(enclosing_decl(lines, h), []).append(h)
    return census


def report(reason, census):
    spend = {k: v for k, v in census.items() if k != TRANSPORT}
    total = sum(len(v) for v in spend.values())
    print(f"\n=== {reason}: {total} errors / {len(spend)} declarations ===")
    for decl, hits in sorted(spend.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(hits):3d}  {decl:<36} "
              + ", ".join(f"L{h}" for h in hits))
    if TRANSPORT in census:
        print(f"  [{len(census[TRANSPORT])}] {TRANSPORT:<34} "
              + ", ".join(f"L{h}" for h in census[TRANSPORT])
              + "   (RE-WRITES a reason, does not spend one)")
    if not census:
        print("  none -- the reason has no producer at all: a PHANTOM by the "
              "compiler's own reading")



# ---------------------------------------------------------------------------
# `phantom` mode (item 211).
#
# `dedent` and `noKeyContext` are produced in structurally different places, and
# that difference is what R646's "no named input" was pointing at.  `dedent`'s
# branch is a `by_cases` on a runtime datum -- whether the landing's column is
# one of the frames the park holds -- so it is a property of the INPUT and has
# a named one (`k:\n  :\nb: 2`).  Every `noKeyContext` sits in the `inr` branch
# of a caller-supplied `... ∨ True`, so it is a property of the CALL SITE: the
# reason fires exactly when a caller declined to supply a context.
#
# So the phantom question is asked without a single input: FALSIFY the optional
# premise -- `P ∨ True` becomes `P ∨ False` -- and rebuild.  Every caller
# breaks, paid or not, because the payers are themselves lemmas returning the
# optional type; what decides is WHERE each error lands, and at which COLUMN.
#
# NOT by deleting the `∨ True`, which was this item's first reading and is a
# control that cannot fail: narrowing `P ∨ True` to `P` rejects `Or.inl h`
# exactly as it rejects `Or.inr trivial`, so it reports every call site and
# measures nothing.  It read 8 of 8.
#
# And not by the error's LINE either: four of these call sites put several
# context arguments on one line, and a line-wide read called a relayed
# `h_keyctx` a decline because an `Or.inr trivial` for the next context sat
# beside it.  The column points at the sub-term that mismatched -- the `trivial`
# inside `Or.inr trivial` -- and that is what separates the three cases.
PHANTOM = {
    # (`content_dispatch_routed`'s own key context is not here: its punt needs
    # FIVE contexts to decline at once, which is `reaches` rather than one
    # falsification.)
    # the flow close's stamp reading: `inl` gives `implicitValue`, `inr` gives
    # `noKeyContext`, so narrowing this decides which of the two L871 is
    "stamp": ("flowKeyPack_of_close",
              r"^      \(sc\.implicitValueLine = some sc\.simpleKey\.pos\.line ∨ True\)\)$",
              "here"),
    # and the close's key ROUTE, the other switch that reaches the same punt
    "keyroute": ("flowKeyPack_of_close",
                 r"ResumeFrames \(ExplValueLine sp_start nv\) ks sp_e\) ∨ True\)\) ∨ True\)$",
                 "last"),
}


def apply_narrow(lines, which):
    """Falsify one optional premise: `∨ True` becomes `∨ False`, in place."""
    decl, anchor, where = PHANTOM[which]
    start = next(i for i, l in enumerate(lines) if re.match(rf"^lemma {decl}\b", l))
    pat = re.compile(anchor)
    hit = next(i for i in range(start, len(lines)) if pat.search(lines[i]))
    if where == "first":
        hit = next(i for i in range(hit, len(lines)) if " ∨ True)" in lines[i])
    out = list(lines)
    if where == "last":
        head, _, tail = out[hit].rpartition("∨ True")
        out[hit] = head + "∨ False" + tail
    else:
        out[hit] = out[hit].replace("∨ True", "∨ False", 1)
    return out, decl, hit + 1


def phantom_census(which):
    lines = TARGET.read_text().split("\n")
    backup = TARGET.with_suffix(".lean.punt-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched, decl, hit = apply_narrow(lines, which)
        TARGET.write_text("\n".join(patched))
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True)
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    pat = re.compile(
        r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): error")
    hits = sorted({(int(m.group(1)), int(m.group(2)))
                   for line in body.split("\n") if (m := pat.match(line))})
    census = {}
    for h, col in hits:
        census.setdefault(enclosing_decl(lines, h), []).append((h, col))
    own = census.pop(decl, [])
    total = sum(len(v) for v in census.values())
    print(f"\n=== narrow {which} ({decl}, L{hit}): "
          f"{total} caller errors / {len(census)} declarations ===")
    for d, hs in sorted(census.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(hs):3d}  {d}")
        for h, col in hs:
            # the error column points at the SUB-TERM that mismatched, which
            # for a declined context is the `trivial` inside `Or.inr trivial`
            prefix, text = lines[h - 1][:col], lines[h - 1][col:].strip()
            declined = (text.startswith("trivial")
                        and prefix.rstrip().endswith("Or.inr"))
            kind = "DECLINES" if declined else "pays/relays"
            print(f"         L{h}:{col:<4} {kind:<12} {text[:48]}")
    print(f"  [{len(own)}] {decl + "  (its own body)":<34} "
          + ", ".join(f"L{h}" for h, _ in own))
    if not census:
        print("  NO CALLER declines the premise -- the `inr` branch is reachable "
              "from no call site in this tree")



# ---------------------------------------------------------------------------
# `split` mode (item 211): the unit the recorded numbers glued together.
#
# Item 184 recorded `dedent` as "7 applications in 5 definitions" and
# `noKeyContext` as "6 in 5".  Both halves reproduce -- but a site is one of two
# things, and the two price differently.  A PRODUCTION hands the reason to a
# consumer and is emptied by a proof about the input; a CONSUMER ARM is the
# `cases` label where the reason is spent, and it goes when the last production
# does.  `dedent` is 4 productions and 3 consumer arms; `noKeyContext` is 3 and
# 3.  The arm's verdict is read off its body: `exact h_punt` RIDES the caller's
# deferral, `Or.inr trivial` WEAKENS the consumer's own optional premise, and
# anything else SPENDS the reason on a refutation.
ARM_VERDICTS = [
    ("RIDES the caller's deferral", "exact h_punt"),
    ("WEAKENS the consumer's own premise", "Or.inr trivial"),
]


def punt_match_blocks(lines):
    """Every `cases <x> with` block whose alternatives are KeyPackPunt reasons.

    Asking for the labels rather than the scrutinee's name is what keeps the
    `| tab` of an unrelated inductive out -- `gstar_white_sIndent_or_tab` has
    one, and a name match alone reported it as a punt consumer.
    """
    lo, hi = inductive_block(lines)
    blocks = []
    for i, line in enumerate(lines):
        m = re.match(r"^(\s*(?:· )?)cases \w+ with\s*$", line)
        if not m:
            continue
        ind = len(m.group(1))
        alts = []
        for j in range(i + 1, len(lines)):
            s = lines[j]
            if not s.strip() or s.strip().startswith("--"):
                continue
            cur = len(s) - len(s.lstrip())
            if cur < ind:
                break
            a = re.match(r"^\s*\| (\w+)", s)
            if a and cur == ind:
                alts.append((j, a.group(1)))
            elif cur == ind:
                break
        names = {n for _, n in alts}
        if len(names) >= 2 and names <= set(REASONS):
            blocks += [(j, n) for j, n in alts if not (lo <= j <= hi)]
    return blocks


def split_census():
    """The unit item 184's two numbers glued together, split by the compiler's
    own two kinds of site."""
    lines = TARGET.read_text().split("\n")
    lo, hi = inductive_block(lines)
    arms = punt_match_blocks(lines)
    for reason in REASONS:
        prod = [(i + 1, enclosing_decl(lines, i)) for i, line in enumerate(lines)
                if f"KeyPackPunt.{reason}" in line and not (lo <= i <= hi)
                and not line.strip().startswith("--") and "`" not in line
                and enclosing_decl(lines, i) != TRANSPORT]
        mine = [(j + 1, enclosing_decl(lines, j), lines[j])
                for j, n in arms if n == reason
                and enclosing_decl(lines, j) != TRANSPORT]
        print(f"\n=== {reason}: {len(prod)} productions / "
              f"{len(mine)} consumer arms ===")
        for ln, decl in prod:
            print(f"  PRODUCTION   L{ln:<6} {decl}")
        for ln, decl, line in mine:
            s = line.strip()
            body = s.split("=>", 1)[1].strip() if "=>" in s else ""
            if not body:
                body = next((t.strip() for t in lines[ln:]
                             if t.strip() and not t.strip().startswith("--")), "")
            verdict = next((v for v, pat in ARM_VERDICTS if pat in body),
                           "SPENDS it -- a refutation, or the reason as a datum")
            print(f"  CONSUMER ARM L{ln:<6} {decl:<28} {verdict}")



# ---------------------------------------------------------------------------
# `reaches` mode (item 211): the phantom question, decided at the production.
#
# `content_dispatch_routed` builds `noKeyContext` only after FIVE optional
# contexts have each taken their `inr` branch, so narrowing one of them says
# which callers decline THAT one and nothing about the punt.  What decides the
# punt is the INTERSECTION: an application of the lemma that declines all five
# is one whose every input leaves the landed `:` with no key context at all.
#
# Each falsification's errors are collapsed onto the nearest preceding
# application of the lemma, which is how a caller's several argument lines
# become the one call site they belong to.
CONTEXTS = ["h_keyctx", "h_suffixctx", "h_nodocctx", "h_markerctx", "h_propsctx"]
REACH_DECL = "content_dispatch_routed"


def narrow_binder(lines, decl, binder):
    start = next(i for i, l in enumerate(lines) if re.match(rf"^lemma {decl}\b", l))
    b = next(i for i in range(start, len(lines))
             if re.match(rf"^    \({binder} :", lines[i]))
    hit = next(i for i in range(b, len(lines)) if " ∨ True)" in lines[i])
    out = list(lines)
    out[hit] = out[hit].replace("∨ True", "∨ False", 1)
    return out, hit + 1


def call_sites(lines, decl):
    """Line numbers at which `decl` is APPLIED, its own signature excluded."""
    return [i + 1 for i, l in enumerate(lines)
            if decl in l and not re.match(rf"^lemma {decl}\b", l)
            and not l.strip().startswith("--") and "`" not in l]


def reaches_census():
    """Which call sites DECLINE all five contexts, read off the compiler's own
    error locations.

    Falsifying a context (`P ∨ True` -> `P ∨ False`) breaks every caller, paid
    or not, because the payers are themselves lemmas returning the optional
    type -- so the error COUNT decides nothing.  What decides is WHERE each
    error lands: a caller that declines the context wrote `Or.inr trivial` at
    that argument and the error sits on it; a caller that pays wrote the payer
    and the error sits on the payer instead.  The site list is the compiler's;
    the two-way classification is a reading of the source line it points at,
    printed with that line so it can be checked rather than taken.
    """
    lines = TARGET.read_text().split("\n")
    apps = call_sites(lines, REACH_DECL)
    print(f"{REACH_DECL}: {len(apps)} applications "
          + ", ".join(f"L{a}" for a in apps))
    backup = TARGET.with_suffix(".lean.punt-bak")
    declines = {a: set() for a in apps}
    relays = set()
    for binder in CONTEXTS:
        shutil.copyfile(TARGET, backup)
        try:
            patched, hit = narrow_binder(lines, REACH_DECL, binder)
            TARGET.write_text("\n".join(patched))
            proc = subprocess.run(
                ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
                cwd=ROOT, capture_output=True, text=True)
            body = proc.stdout + proc.stderr
        finally:
            shutil.copyfile(backup, TARGET)
            backup.unlink()
        pat = re.compile(
            r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): error")
        hits = sorted({(int(m.group(1)), int(m.group(2)))
                       for line in body.split("\n") if (m := pat.match(line))})
        rows = []
        for h, col in hits:
            if enclosing_decl(lines, h - 1) == REACH_DECL:
                continue
            site = max((a for a in apps if a <= h), default=0)
            # the COLUMN is what picks the argument: several arguments share a
            # line at four of these call sites, and a line-wide read called a
            # relayed `h_keyctx` a decline because an `Or.inr trivial` for the
            # NEXT context sat beside it
            # the error column points at the SUB-TERM that mismatched, which
            # for a declined context is the `trivial` inside `Or.inr trivial`
            prefix, text = lines[h - 1][:col], lines[h - 1][col:].strip()
            declined = (text.startswith("trivial")
                        and prefix.rstrip().endswith("Or.inr"))
            if declined:
                declines[site].add(binder)
                rows.append((site, h, col, "DECLINES", text))
            elif re.search(rf"\b{binder}\b", text):
                # item 210's relay, one construct over: the caller hands its
                # OWN premise on, so the decision is not this call site's
                relays.add(site)
                rows.append((site, h, col, "RELAYS  ", text))
            else:
                rows.append((site, h, col, "pays    ", text))
        print(f"\n  {binder}:")
        for site, h, col, verdict, text in rows:
            print(f"    L{site:<6} {verdict} at L{h}:{col:<4} {text[:46]}")
    print()
    for a in apps:
        n = len(declines[a])
        mark = ("  <-- RELAYS: the decision is its own caller's"
                if a in relays else
                "  <-- reaches `noKeyContext`" if n == len(CONTEXTS) else "")
        print(f"  L{a:<6} {enclosing_decl(lines, a - 1):<30} declines "
              f"{n}/{len(CONTEXTS)}{mark}")
    reach = [a for a in apps
             if len(declines[a]) == len(CONTEXTS) and a not in relays]
    print(f"\n  {len(reach)} of {len(apps)} applications decline ALL FIVE "
          f"({len(relays)} relay their caller's)")
    if not reach:
        print("  -- no application reaches `noKeyContext`: a PHANTOM at this "
              "production, on the compiler's own locations")


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which == "reaches":
        reaches_census()
        return
    if which == "split":
        split_census()
        return
    if which in PHANTOM:
        phantom_census(which)
        return
    if which == "phantom":
        for k in PHANTOM:
            phantom_census(k)
        return
    if which not in REASONS + ["all"]:
        sys.exit("usage: punt_reason_price.py "
                 f"[{'|'.join(REASONS)}|all|split|phantom|reaches|"
                 f"{'|'.join(PHANTOM)}]")
    lines = TARGET.read_text().split("\n")
    for reason in (REASONS if which == "all" else [which]):
        report(reason, price(reason, lines))


if __name__ == "__main__":
    main()
