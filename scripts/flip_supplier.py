#!/usr/bin/env python3
"""Flip a SUPPLIER'S STATEMENT and report what stops typechecking (DOCS item 240).

The three standing flips (`flip_210.py`, `flip_supply.py`, `flip_drop.py`) all
tighten or delete a *production*.  This one changes a *lemma's type*, which is
a different edge: item 238's `S=0` measured what a deleted CONSTRUCTOR
propagates and found nothing, because a consumer depends on its supplier's
TYPE and not on its proof.  `PendingNode.close_with_ssl` is the supplier β.5
must repair (item 239 proved its statement false in the environment that
deletes `SLYamlStream.scannerDrop` and keeps `PendingNode.pendingFlow`), so
what it propagates is the number this gate exists to produce.

**A repaired statement is a CHOICE, so one flip measures one repair and not
the obligation.**  This gate runs three points of the repair lattice and
reports the triple:

    weak    `close_with_ssl` gains a premise `SLYamlStream sp_start sp_scan`
            and its flow arm closes with it.  The edge traveled is the
            supplier's CONSUMERS.
    field   `PendingNode.pendingFlow` gains the same connection as a FIELD and
            `close_with_ssl` reads it from the park.  `close_with_ssl`'s own
            type is UNCHANGED; the edge traveled is the park's PRODUCER.
    retire  `pendingFlow` is deleted outright, arm and docstring together.
            `close_with_ssl`'s type is unchanged again; what breaks is
            everything that case-splits on the park or builds it.

A fourth end is not a fourth point of the lattice:

    producer
            the `field` repair THREADED ONE LEVEL.  The park keeps its new
            field, `close_with_ssl` still reads it, and
            `block_dispatch_deferred` — the one definition the `field` end
            breaks — gains `(h_scan : SLYamlStream sp_start sp_scan')` and
            spends it on the park it builds.  What breaks is that producer's
            own consumers, so this is the SECOND WAVE of the `field` end and
            its count belongs beside `field=1` rather than inside the lattice.

**A flip on the producer measures a propagation a DERIVATION would make zero**,
and this gate cannot tell those apart: if `block_dispatch_deferred` could
derive the datum from what it already holds, the premise would never be added
and the wave would not exist.  That question is asked first and separately, in
`Tests/Guards/Proofs/ProducerDerivation.lean` (DOCS item 241) — a census of
what the library derives from a `ScannerSurfCorr`, and a refutation in the
post-β.5 model.  Read the wave only after that answer.

None of the four deletes `scannerDrop`: that flip already exists and costs a
known 2 (`dropClose`, `close_with_ssl`), and mixing it in would charge this
gate for a deletion it is not measuring.

**What the count is.**  Each flip leaves a well-typed, drop-free supplier
behind, so every error it reports is a TYPE error at a consumer — a
PROPAGATION.  It is not a proof bill: a definition that breaks here may need
one extra argument or a new premise of its own, and only the second kind
changes a STATEMENT.  The gate cannot tell those apart and does not claim to;
`Tests/Guards/Proofs/RepairChoice.lean` is what decides that question,
and `Tests/Guards/Proofs/ProducerDerivation.lean` decides it for the fourth
end below.

    scripts/flip_supplier.py                 # all three ends
    scripts/flip_supplier.py --end weak      # one end
    scripts/flip_supplier.py --map <log>     # just map an existing log

Destructive while it runs — it edits `L4YAML/Proofs/Production/StreamAccum.lean`
in place — so each end restores from its own backup in a `finally` and prints
the md5 both before and after.  A run that dies between the two leaves the
backup beside the source.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML" / "Proofs" / "Production" / "StreamAccum.lean"

#: The log mapper is item 210's; one instrument, five gates.
_spec = importlib.util.spec_from_file_location(
    "flip210", Path(__file__).resolve().parent / "flip_210.py")
flip210 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(flip210)

# ---------------------------------------------------------------------------
# The anchors.  Every one is located by CONTENT (item 210's rule): a re-indent
# or a docstring rewrite re-aims the gate loudly instead of matching silently.
# ---------------------------------------------------------------------------

#: `close_with_ssl`'s stream premise, the line the new one goes beside.  The
#: close carries BOTH silences since item 275, so the anchor spans the pair and
#: a further one re-aims this gate rather than matching a prefix of it.
SIG = ("    (h_stream : SLYamlStream sp_start sp_block)\n"
       "    (h_nd : danglingNodePos? sc = none)\n"
       "    -- Item 275: §8.1's silence, relayed to `pendingContent`'s face."
       "  Only that\n"
       "    -- arm reads it; `pendingBlockContent`'s own `h_closable` is"
       " unchanged.\n"
       "    (h_ui : underIndentedFlowValuePos? sc = none)\n"
       "    (h_ssl : SSLComments sp_scan sp_mid) :\n"
       "    SLYamlStream sp_start sp_mid := by\n")

#: `close_with_ssl`'s flow arm — the one place in the library that spends the
#: escape on a park (`dropClose` is the other spender and is not a park).
ARM = ("  | pendingFlow =>\n"
       "    -- Absorb opaque scanner content (flow/block indicators) via scannerDrop.\n"
       "    exact SLYamlStream.scannerDrop sp_start sp_block sp_scan sp_mid"
       " h_stream h_ssl\n")

#: The park's last field and the conclusion beneath it.
FIELD = ("      (h_nic0 : sp_scan.col = 0 → sc.needIndentCheck = true) :\n"
         "      PendingNode sc false sp_start sp_block sp_scan\n"
         "  /-- Content token scanned INSIDE a block entry")

#: `block_dispatch_deferred`'s head — the producer the `field` end breaks.
PROD_HEAD = ("lemma block_dispatch_deferred\n"
             "    (sp_start sp_X sp_scan' : SurfPos) (s' : ScannerState)\n"
             "    (h_stream : SLYamlStream sp_start sp_X)\n")

#: the one place the producer builds the park.
PROD_BODY = ("   PendingNode.pendingFlow sp_start sp_X sp_scan' h_stream h_arm"
             " h_nodir h_nic0,\n")

#: The park itself, docstring and constructor together.
CTOR_HEAD = "  /-- Flow indicator scanned (`]`, `}`, `,`), or deferred block dispatch."
CTOR_TAIL = ("      (h_nic0 : sp_scan.col = 0 → sc.needIndentCheck = true) :\n"
             "      PendingNode sc false sp_start sp_block sp_scan\n")


def _edit_weak(src: str) -> str:
    src = _sub1(src, SIG,
                "    (h_stream : SLYamlStream sp_start sp_block)\n"
                "    (h_scan : SLYamlStream sp_start sp_scan)\n"
                "    (h_nd : danglingNodePos? sc = none)\n"
                "    (h_ui : underIndentedFlowValuePos? sc = none)\n"
                "    (h_ssl : SSLComments sp_scan sp_mid) :\n"
                "    SLYamlStream sp_start sp_mid := by\n")
    return _sub1(src, ARM,
                 "  | pendingFlow =>\n"
                 "    exact ssl_comments_extend_stream sp_start sp_scan sp_mid"
                 " h_scan h_ssl\n")


def _edit_field(src: str) -> str:
    src = _sub1(src, FIELD,
                "      (h_nic0 : sp_scan.col = 0 → sc.needIndentCheck = true)\n"
                "      (h_scan : SLYamlStream sp_start sp_scan) :\n"
                "      PendingNode sc false sp_start sp_block sp_scan\n"
                "  /-- Content token scanned INSIDE a block entry")
    return _sub1(src, ARM,
                 "  | pendingFlow =>\n"
                 "    exact ssl_comments_extend_stream _ _ sp_mid (by assumption) h_ssl\n")


def _edit_retire(src: str) -> str:
    if src.count(CTOR_HEAD) != 1:
        sys.exit("the park's docstring is no longer unique; this gate needs "
                 "re-aiming")
    head = src.index(CTOR_HEAD)
    tail = src.index(CTOR_TAIL, head) + len(CTOR_TAIL)
    block = src[head:tail]
    # `CTOR_TAIL` is four parks' last field, so the span is checked by what it
    # CONTAINS rather than by the anchor being unique: exactly one constructor
    # head, and it is this park's.
    if block.count("\n  | ") != 1 or "\n  | pendingFlow (" not in block:
        sys.exit(f"the span this gate would delete is not one constructor:\n"
                 f"{block[:400]}\n... ({len(block)} chars)")
    return _sub1(src[:head] + src[tail:], ARM, "")


def _edit_producer(src: str) -> str:
    """The `field` end, with the producer paying instead of breaking."""
    src = _edit_field(src)
    src = _sub1(src, PROD_HEAD,
                "lemma block_dispatch_deferred\n"
                "    (sp_start sp_X sp_scan' : SurfPos) (s' : ScannerState)\n"
                "    (h_stream : SLYamlStream sp_start sp_X)\n"
                "    (h_scan : SLYamlStream sp_start sp_scan')\n")
    return _sub1(src, PROD_BODY,
                 "   PendingNode.pendingFlow sp_start sp_X sp_scan' h_stream h_arm"
                 " h_nodir h_nic0 h_scan,\n")


def _sub1(src: str, old: str, new: str) -> str:
    n = src.count(old)
    if n != 1:
        sys.exit(f"expected exactly one occurrence of\n---\n{old}---\nin "
                 f"{SRC.relative_to(ROOT)}, found {n}; the statement moved and "
                 "this gate needs re-aiming")
    return src.replace(old, new)


#: The head LINE of each declaration a flip leaves with a proof to elaborate.
#: `run_end` reads the build's error locations against these spans, so that
#: "the repair elaborates" is a reading rather than an absence.
SUPPLIER_HEAD = "lemma PendingNode.close_with_ssl {sc : ScannerState}"
PRODUCER_HEAD = "lemma block_dispatch_deferred"

#: Three points of the repair lattice, and one SECOND WAVE.  `LATTICE_ENDS`
#: is what the summary line compares; `producer` is reported beside it
#: because it travels the `field` end's own edge one level further and
#: putting it inside the lattice would read as a fourth repair.
ENDS = {
    "weak": (_edit_weak, [SUPPLIER_HEAD],
             "close_with_ssl gains a premise — the edge is its CONSUMERS"),
    "field": (_edit_field, [SUPPLIER_HEAD],
              "pendingFlow gains a field — the edge is the park's PRODUCER"),
    "retire": (_edit_retire, [SUPPLIER_HEAD],
               "pendingFlow is deleted — the edge is every reader of the park"),
    "producer": (_edit_producer, [SUPPLIER_HEAD, PRODUCER_HEAD],
                 "the field repair THREADED — block_dispatch_deferred pays "
                 "instead of breaking, and the edge is ITS consumers"),
}

LATTICE_ENDS = ("weak", "field", "retire")


def md5(path: Path) -> str:
    return hashlib.md5(path.read_bytes()).hexdigest()


def repaired_errors(flipped: str, log: str, head: str) -> int:
    """How many of the build's errors are inside the repaired declaration.

    Every end leaves the declarations it edits with a proof that must still
    elaborate, and a count taken from the absence of their names in the broken
    list would be reading a silence.  This reads the LOCATIONS: an error
    inside a repaired declaration's own span means the repair does not
    elaborate and the end's count measures nothing.
    """
    lines = flipped.split("\n")
    start = next(i for i, l in enumerate(lines) if l.startswith(head))
    end = next(i for i in range(start + 1, len(lines))
               if lines[i].startswith("/-!") or lines[i].startswith("/--"))
    rel = str(SRC.relative_to(ROOT))
    return sum(1 for m in flip210.ERROR_LOC.finditer(log)
               if m.group(1) == rel and start < int(m.group(2)) <= end)


def run_end(name: str, log_dir: Path | None) -> int | None:
    edit, heads, blurb = ENDS[name]
    print(f"=== END {name}: {blurb} ===")
    before = md5(SRC)
    print(f"md5 before  {before}")
    src = SRC.read_text()
    backup = SRC.with_suffix(f".lean.{name}-backup")
    shutil.copy(SRC, backup)
    count = None
    try:
        flipped = edit(src)
        SRC.write_text(flipped)
        out = subprocess.run(["lake", "build"], cwd=ROOT,
                             capture_output=True, text=True)
        log = out.stdout + out.stderr
        if log_dir:
            (log_dir / f"flip.supplier.{name}.log").write_text(log)
        n_rep = sum(repaired_errors(flipped, log, h) for h in heads)
        print(f"REPAIRED errors={n_rep} over {len(heads)} declaration(s)"
              + ("  — every edited declaration ELABORATES, so every error "
                 "below is a consumer's" if n_rep == 0 else
                 "  — THE REPAIR ITSELF DOES NOT ELABORATE; the count below "
                 "measures nothing"))
        if out.returncode == 0:
            print("THE FLIP BUILT CLEAN — this end of the lattice propagates "
                  "NOTHING, which is a finding and not a pass")
            count = 0
        else:
            defs, nlocs, complaints = flip210.broken_definitions(log)
            for d in defs:
                print(f"BROKEN {d}")
            for c in complaints:
                print(f"UNMAPPED {c}")
            print(f"COUNT {len(defs)} definitions from {nlocs} locations")
            print("LOWER BOUND — the build stopped at the first failing "
                  "module, so no definition behind it was attempted")
            count = len(defs)
    finally:
        shutil.copy(backup, SRC)
        backup.unlink()
        after = md5(SRC)
        print(f"md5 after   {after}")
        if after != before:
            sys.exit("the restore did not restore; fix the source before "
                     "trusting anything else in this run")
        print("rebuilding so no later probe reads the flipped oleans...")
        subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    return count


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--end", choices=[*ENDS, "all"], default="all")
    ap.add_argument("--map", metavar="LOG",
                    help="map an existing build log instead of running the gate")
    ap.add_argument("--log-dir", metavar="DIR", help="write the build logs here")
    args = ap.parse_args()

    if args.map:
        return 1 if flip210.report(Path(args.map).read_text()) else 0

    log_dir = Path(args.log_dir) if args.log_dir else None
    names = list(ENDS) if args.end == "all" else [args.end]
    # An anchor that no longer matches must cost ONE end, not the rest of the
    # run: item 275 moved `close_with_ssl`'s signature and `weak` refused, which
    # is the anchors-by-content rule working — but a bare comprehension took
    # `field`, `retire` and `producer` down with it and the battery logged a
    # single refusal where four measurements were owed.
    counts, refused = {}, []
    for n in names:
        try:
            counts[n] = run_end(n, log_dir)
        except SystemExit as e:
            refused.append(n)
            print(f"END {n} REFUSED — re-aim this end; the others still ran\n{e}")
    lat = {n: c for n, c in counts.items() if n in LATTICE_ENDS}
    if len(lat) > 1:
        print("LATTICE " + "  ".join(f"{n}={c}" for n, c in lat.items()))
        print("The three counts travel THREE DIFFERENT EDGES and are not a "
              "ratio: `weak` is the only end that changes the supplier's own "
              "type, and it is the only one whose breakage can force a "
              "consumer's STATEMENT to change.")
    if "producer" in counts:
        print(f"WAVE2 producer={counts['producer']}")
        print("Not a fourth point of the lattice: this is `field` once its "
              "one broken definition pays rather than absorbs.  It is a "
              "PROPAGATION only because the producer cannot derive the datum "
              "— Tests/Guards/Proofs/ProducerDerivation.lean is what "
              "establishes that, and without it this number measures nothing.")
    if refused:
        print(f"SUPPLIER-REFUSED {len(refused)}: {', '.join(refused)}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
