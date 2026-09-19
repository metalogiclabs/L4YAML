#!/usr/bin/env python3
"""Price item 154's flag READ AT THE BLOCK LANDING (item 210).

Item 205 wrote, of `_stamp_compact`'s carrier chain:

    That premise -- `sp_scan.col = 0 -> sc.needIndentCheck = true`, item 154's
    field read at the BLOCK landing -- has **12** application sites, of which 5
    pay by refuting the hypothesis from a column field the park already carries.

Every other number in that paragraph has since been re-derived by an instrument
and four of the five moved (item 206, `park_nic0_price.py`).  The **12** never
was.  It rode four items' NEXT lists verbatim -- 205, 206, 207, 208, 209 --
which is exactly what CLAUDE.md §10 calls a forecast copied forward.

This script is the missing instrument.  It splices a SECOND copy of the premise
into a block-landing consumer's signature, rebuilds, and groups the failures by
the declaration containing them -- the same method `park_top_price.py` uses for
the park TOP and `park_nic0_price.py` for the park's own field, one ring further
out.  Probing the PAID tree with a second field measures exactly what the first
one cost, which is `park_nic0_price.py`'s own documented control.

The five consumers are the block dispatch's landing arms.  Three carry the real
premise (items 208/209); `noPending` and `pendingBlock` do not, and the census
says what they would cost if they did.

MEASURED (item 210) -- the five per-lemma runs sum to the blanket one, which is
this instrument's own control:

    accum_block_on_closeThenBlock      11 sites / 4 declarations
    accum_block_on_noPending            1      / 1
    accum_block_on_pendingContent       1      / 1
    accum_block_on_pendingBlockContent  1      / 1
    accum_block_on_pendingBlock         1      / 1
    all                                15      / 4

`payers` splits the fifteen by what each spends -- 5 column refutations (the
three parks item 205 named), 5 park fields, 3 RELAYS (a landing arm handing its
own premise to another landing arm) and 2 arms that take no flag at all.  The
three relays are what a park census cannot see, and `12 = 15 - 3`.

`drop` is the load-bearing control: rename the premise in a carrier's signature,
leaving its arity alone, and every USE breaks instead of every call site.  All
three carriers spend it -- 3 / 2 / 4, nine sites, six of them
`dash_landing_floor` applications and three relays.

Usage:
    python3 scripts/landing_nic0_price.py all
    python3 scripts/landing_nic0_price.py accum_block_on_closeThenBlock
    python3 scripts/landing_nic0_price.py payers
    python3 scripts/landing_nic0_price.py drop
"""
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"

# The block dispatch's five landing arms, each with the binder naming the PARK's
# surface position.  `noPending`'s park IS the block context, so it binds
# `sp_block` and no `sp_scan`; the other four bind both.
LEMMAS = {
    "accum_block_on_noPending": "sp_block",
    "accum_block_on_closeThenBlock": "sp_scan",
    "accum_block_on_pendingContent": "sp_scan",
    "accum_block_on_pendingBlockContent": "sp_scan",
    "accum_block_on_pendingBlock": "sp_scan",
}

PROBE = "    -- LANDING NIC0 PROBE (scripts/landing_nic0_price.py)"
CONCLUSION = "    ∃ sp_gram' sp_block' sp_flow' sp_scan',"


def signature_end(lines, name):
    """Index of the `) :` line that ends `name`'s binder list."""
    start = next(i for i, l in enumerate(lines)
                 if re.match(rf"^lemma {name}\b", l))
    concl = next(i for i in range(start, len(lines)) if lines[i] == CONCLUSION)
    assert lines[concl - 1].rstrip().endswith(") :"), lines[concl - 1]
    return concl - 1


def apply_drop(lines, name):
    """Rename `h_nic0` in one consumer's signature, leaving its arity alone.

    Dropping the binder outright breaks every CALL site and measures the supply
    again; renaming it breaks every USE and measures the SPEND.  A consumer whose
    rename costs nothing is carrying a premise its body never reads -- item 197's
    rule, asked of a premise instead of a field.
    """
    start = next(i for i, l in enumerate(lines) if re.match(rf"^lemma {name}\b", l))
    end = next(i for i in range(start, len(lines)) if lines[i] == CONCLUSION)
    out = list(lines)
    sig = [i for i in range(start, end) if "(h_nic0 :" in out[i]]
    assert len(sig) == 1, f"{name}: {len(sig)} `h_nic0` binders"
    out[sig[0]] = out[sig[0]].replace("(h_nic0 :", "(h_nic0_dropped :")
    return out, sig[0] + 1


def apply_probe(lines, which):
    targets = list(LEMMAS) if which == "all" else [which]
    out = list(lines)
    for name in sorted(targets, key=lambda n: -signature_end(lines, n)):
        sig = signature_end(out, name)
        field = (f"    (h_nic0_probe : {LEMMAS[name]}.col = 0 → "
                 f"sc.needIndentCheck = true) :")
        out[sig: sig + 1] = [out[sig].rstrip()[:-2].rstrip(), PROBE, field]
    return out, sorted(targets)


def enclosing_decl(lines, lineno):
    decl = "<file scope>"
    for i in range(min(lineno, len(lines))):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def) (\w+)", lines[i])
        if m:
            decl = m.group(1)
    return decl


# `payers` mode: what each PAID landing site spends on the real premise.  The
# argument sits last in the application, so the classification is read off the
# source and every line number is printed -- a reading, labelled as one, beside
# a census the compiler produced.
PAYER_FORMS = [
    ("a RELAY of the consumer's own premise (item 208)",
     re.compile(r"^h_nic0\)?$")),
    ("the PARK's own field (items 154/206/207)",
     re.compile(r"^h_nic0[A-Za-z0-9_]+\)?$")),
    ("`PendingNode.nic0`, the park-agnostic reader (item 207)",
     re.compile(r"PendingNode\.nic0|\.nic0\b")),
    ("a COLUMN refutation -- the park cannot stand at a line start",
     re.compile(r"nic0_of_col_pos|absurd")),
]


def payers_census():
    """What each landing site spends on the flag.

    The SITE list is the compiler's (`all`); the classification below is a
    READING of the last argument at each of them, printed with its line so a
    reader can check it rather than take it.  The flag is every carrier's last
    binder, so the last argument is the payment.
    """
    lines = TARGET.read_text().split("\n")
    app = re.compile(r"(^|[ (·])(accum_block_on_\w+)\b")
    census = {}
    for i, line in enumerate(lines):
        m = app.search(line)
        if not m or m.group(2) not in LEMMAS or line.lstrip().startswith("--") \
                or re.match(rf"^lemma {m.group(2)}\b", line) or "`" in line:
            continue
        ind = len(line) - len(line.lstrip())
        last = ""
        for j in range(i + 1, len(lines)):
            t = lines[j]
            if not t.strip():
                continue
            if len(t) - len(t.lstrip()) <= ind and not t.lstrip().startswith("--"):
                break
            if not t.lstrip().startswith("--"):
                last = t.strip()
        kind = next((k for k, pat in PAYER_FORMS if pat.search(last)),
                    "another route -- the consumer takes no flag")
        census.setdefault(kind, []).append((i + 1, m.group(2), last))

    total = sum(len(v) for v in census.values())
    print(f"landing applications: {total}\n")
    for kind, hits in sorted(census.items(), key=lambda kv: -len(kv[1])):
        print(f"  {len(hits):3d}  {kind}")
        for ln, name, text in hits:
            print(f"         L{ln:<6} {name:<36} {text[:44]}")


def drop_census():
    """The control: is the premise SPENT at each consumer that carries it?"""
    original = TARGET.read_text()
    carriers = [n for n in LEMMAS if "(h_nic0 :" in "\n".join(
        original.split("\n")[
            next(i for i, l in enumerate(original.split("\n"))
                 if re.match(rf"^lemma {n}\b", l)):][:400])]
    backup = TARGET.with_suffix(".lean.landing-bak")
    print(f"carriers of the real premise: {len(carriers)} "
          f"({', '.join(carriers)})\n")
    for name in carriers:
        shutil.copyfile(TARGET, backup)
        try:
            patched, sigline = apply_drop(original.split("\n"), name)
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
        verdict = ("SPENT" if hits else
                   "VESTIGIAL -- the body never reads it")
        print(f"  {len(hits):3d}  {name:<36} {verdict}")
        if hits:
            print("       " + ", ".join(f"L{h}" for h in hits))


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which == "payers":
        payers_census()
        return
    if which == "drop":
        drop_census()
        return
    if which not in list(LEMMAS) + ["all"]:
        sys.exit("usage: landing_nic0_price.py "
                 f"[{'|'.join(LEMMAS)}|all|payers|drop]")

    original = TARGET.read_text()
    backup = TARGET.with_suffix(".lean.landing-bak")
    shutil.copyfile(TARGET, backup)
    try:
        patched, names = apply_probe(original.split("\n"), which)
        TARGET.write_text("\n".join(patched))
        print(f"probe: {which} -> {', '.join(names)}")
        proc = subprocess.run(
            ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        body = proc.stdout + proc.stderr
    finally:
        shutil.copyfile(backup, TARGET)
        backup.unlink()

    src = TARGET.read_text().split("\n")
    patched, _ = apply_probe(src, which)
    pat = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):\d+: error")
    census = {}
    for line in body.split("\n"):
        m = pat.match(line)
        if m:
            census.setdefault(int(m.group(1)), None)
    for raw in census:
        census[raw] = enclosing_decl(patched, raw)

    # Item 208: an error is not a producer.  Anchor each error on the nearest
    # preceding APPLICATION of a probed lemma and print what collapsed, so the
    # collapse is checkable rather than asserted.
    anchors = [(i + 1, n) for i, line in enumerate(patched) for n in names
               if n in line and not re.match(rf"^lemma {n}\b", line)
               and not line.lstrip().startswith("--")]
    groups, unanchored = {}, []
    for raw in sorted(census):
        prior = [a for a in anchors if a[0] <= raw]
        (unanchored.append(raw) if not prior
         else groups.setdefault(prior[-1], []).append(raw))

    print(f"\nraw error sites: {len(census)}")
    print(f"applications:    {len(groups) + len(unanchored)}   <- the site census")
    by_decl = {}
    for (aline, _n), hits in groups.items():
        by_decl.setdefault(enclosing_decl(patched, aline), []).append(hits)
    for raw in unanchored:
        by_decl.setdefault(census[raw], []).append([raw])
    print(f"declarations:    {len(by_decl)}\n")
    for decl, hits in sorted(by_decl.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(hits):3d}  {decl}")
    per_lemma = {}
    for (aline, n), hits in groups.items():
        per_lemma.setdefault(n, []).append(aline)
    if len(names) > 1:
        print("\nby probed lemma:")
        for n in names:
            lns = sorted(per_lemma.get(n, []))
            print(f"  {len(lns):3d}  {n:<36} " + ", ".join(f"L{x}" for x in lns))
    cascaded = {a: h for a, h in groups.items() if len(h) > 1}
    if cascaded:
        print(f"\ncollapsed cascades "
              f"({sum(len(h) - 1 for h in cascaded.values())} errors were not "
              f"sites):")
        for (aline, n), hits in sorted(cascaded.items()):
            print(f"  L{aline}  {n}  <- errors at " + ", ".join(map(str, hits)))
    if unanchored:
        print(f"\nUNANCHORED ({len(unanchored)}): no application precedes these, "
              f"so they are counted one-for-one and the total is a CEILING:")
        for raw in unanchored:
            print(f"  L{raw}  in {census[raw]}")
    if not census:
        print("  (none -- the premise is already discharged everywhere)")


if __name__ == "__main__":
    main()
