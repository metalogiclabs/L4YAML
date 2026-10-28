#!/usr/bin/env python3
"""Source-scoped diagnostic for the block-indicator no-pop route.

This is a *static* reader of selected Lean declarations, not a Lean checker,
proof-term inspector, or claim that a missing derivation is impossible.
The repository's native build and term-level guards remain authoritative.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys


BUILDERS = (
    "accum_block_on_pendingBlock",
    "accum_block_on_pendingBlockContent",
)
TARGET = "indicator_open_map"
DEFAULT_SOURCE = Path(__file__).resolve().parent.parent / (
    "L4YAML/Proofs/Production/StreamAccum.lean"
)
DECLARATION = re.compile(
    r"(?m)^(?:(?:private|protected)\s+)?(?:lemma|theorem|def|inductive|structure)\s+"
    r"([A-Za-z0-9_'.]+)(?:\s|$)"
)
NO_POP_DECLINE = re.compile(
    r"Classical\.em\s*\(\s*s_prep\.indents\s*=\s*sc\.indents\s*\)\s*"
    r"\)\.elim\s*\(\s*fun\s+_\s*=>\s*Or\.inr\s+trivial\s*\)"
)
TAIL_TYPES = ("SCompactSeqTail", "SCompactMapTail")


class AuditSourceError(ValueError):
    """Expected source signature disappeared; refuse to infer a result."""


def without_comments(source: str) -> str:
    """Erase Lean line and nested block comments while retaining line breaks."""
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(source):
        if depth > 0:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if source[i] == "\n":
                    out.append("\n")
                i += 1
        elif source.startswith("/-", i):
            depth += 1
            i += 2
        elif source.startswith("--", i):
            newline = source.find("\n", i)
            if newline < 0:
                break
            out.append("\n")
            i = newline + 1
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise AuditSourceError("unclosed Lean block comment")
    return "".join(out)


def declaration(source: str, name: str) -> str:
    positions = list(DECLARATION.finditer(source))
    matches = [i for i, p in enumerate(positions) if p.group(1) == name]
    if len(matches) != 1:
        raise AuditSourceError(f"expected one declaration {name}, found {len(matches)}")
    idx = matches[0]
    end = positions[idx + 1].start() if idx + 1 < len(positions) else len(source)
    return source[positions[idx].start():end]


def binder_type(lemma: str, name: str) -> str:
    match = re.search(r"\(\s*" + re.escape(name) + r"\s*:\s*", lemma)
    if match is None:
        raise AuditSourceError(f"expected binder {name}")
    start = match.end()
    depth = 1
    for i in range(start, len(lemma)):
        if lemma[i] == "(":
            depth += 1
        elif lemma[i] == ")":
            depth -= 1
            if depth == 0:
                return lemma[start:i]
    raise AuditSourceError(f"unclosed binder {name}")


def kind_of_tail(binder: str) -> str:
    present = [name for name in TAIL_TYPES if re.search(r"\b" + name + r"\b", binder)]
    if len(present) != 1:
        raise AuditSourceError(f"expected exactly one tail kind, found {present}")
    return present[0]


def audit(source: str, sha: str) -> dict:
    clean = without_comments(source)
    target = kind_of_tail(binder_type(declaration(clean, TARGET), "h_res_land"))
    builders = []
    for name in BUILDERS:
        body = declaration(clean, name)
        carrier = kind_of_tail(binder_type(body, "h_closeF_old"))
        declined = bool(NO_POP_DECLINE.search(body))
        builders.append({
            "name": name,
            "carrier_tail": carrier,
            "same_level_declined": declined,
            "type_gap_candidate": declined and carrier != target,
            "by_cases_count": len(re.findall(r"\bby_cases\b", body)),
            "classical_em_count": len(re.findall(r"\bClassical\.em\b", body)),
            "trivial_fallback_count": len(re.findall(r"\bOr\.inr\s+trivial\b", body)),
        })
    return {
        "source_sha": sha,
        "target": TARGET,
        "target_tail": target,
        "builders": builders,
        "verification_boundary": "STATIC_SOURCE_AUDIT_ONLY",
        "limitations": [
            "A type-kind difference does not prove the route uninhabited.",
            "A syntactic fallback is not proof that an accepted input reaches that branch.",
            "Counts are syntactic proxies, not measured human readability.",
            "Native Lean build, axiom census, and term-level guards are separate gates.",
        ],
    }


def as_markdown(result: dict) -> str:
    rows = [
        "# No-pop route contract audit",
        "",
        f"Source revision: `{result['source_sha']}`",
        f"Verification boundary: **{result['verification_boundary']}**",
        "",
        f"The opener `{result['target']}` requires a `{result['target_tail']}` continuation.",
        "",
        "| Proof builder | Available tail | Same-level route declined? | Kind gap? |",
        "| --- | --- | --- | --- |",
    ]
    for item in result["builders"]:
        yesno = lambda b: "yes" if b else "no"
        rows.append(
            f"| `{item['name']}` | `{item['carrier_tail']}` | "
            f"{yesno(item['same_level_declined'])} | {yesno(item['type_gap_candidate'])} |"
        )
    rows += [
        "",
        "**CANDIDATE:** A missing interface may prevent direct construction of the "
        "mapping-tail continuation from the available sequence-tail closure. "
        "A different premise or a scanner-state restriction might supply the bridge.",
        "",
        "**UNKNOWN:** Whether any accepted input reaches the declined proof arm; "
        "whether the current premises suffice; whether the capstone can close.",
        "",
        "This output is not a Lean theorem, an axiom check, a runtime parser test, "
        "or a measured human-reviewability improvement.",
    ]
    return "\n".join(rows)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--sha", help="Exact source revision; defaults to Git HEAD")
    parser.add_argument("--format", choices=("json", "markdown"), default="json")
    args = parser.parse_args()
    if args.sha is None:
        args.sha = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=args.source.parent, text=True
        ).strip()
    try:
        result = audit(args.source.read_text(encoding="utf-8"), args.sha)
    except (AuditSourceError, OSError) as exc:
        print(f"source audit refused: {exc}", file=sys.stderr)
        return 2
    print(as_markdown(result) if args.format == "markdown" else
          json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
