#!/usr/bin/env python3
"""Diff two `parse_iff_grammar` ledger snapshots (Blueprint/ledgers/parse_iff_grammar/YYYY-MM-DD.md).

A ledger is Markdown whose `##` sections hold tables keyed by their first
column (`F1`, `Row 12`, `S4 block`, …) and one `## Instruments` table of
`| key | value |` rows.  The diff pairs rows by (section, key) and reports:

  * instruments whose value moved (numeric deltas computed when both parse);
  * table rows whose cells changed (old → new, cell by cell);
  * rows added or removed.

Usage:
  scripts/ledger_diff.py OLD.md NEW.md           # explicit pair
  scripts/ledger_diff.py --latest                 # two newest snapshots in the series dir
  scripts/ledger_diff.py --latest --out FILE.md   # also write the report

Exit status 0; the report is Markdown on stdout.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SERIES = ROOT / "Blueprint" / "ledgers" / "parse_iff_grammar"
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}\.md$")
NUM_RE = re.compile(r"^-?\d+(\.\d+)?$")


def split_row(line: str) -> list[str]:
    r"""Split a Markdown table row on unescaped pipes.

    A pipe is escaped when an odd number of backslashes precedes it; `\|` decodes
    to `|`, any other backslash run is kept as written."""
    body = line.strip()
    if body.startswith("|"):
        body = body[1:]
    cells: list[str] = []
    cur: list[str] = []
    i = 0
    while i < len(body):
        ch = body[i]
        if ch == "\\":
            j = i
            while j < len(body) and body[j] == "\\":
                j += 1
            run = j - i
            if j < len(body) and body[j] == "|" and run % 2 == 1:
                cur.append("\\" * (run - 1) + "|")
                i = j + 1
            else:
                cur.append("\\" * run)
                i = j
            continue
        if ch == "|":
            cells.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
        i += 1
    tail = "".join(cur)
    if tail.strip() != "" or not cells:
        cells.append(tail)
    return [c.strip() for c in cells]


def esc(cell: str) -> str:
    """Encode a cell for a Markdown table in the report."""
    return cell.replace("|", "\\|")


def is_rule(cells: list[str]) -> bool:
    return all(re.fullmatch(r":?-{3,}:?", c) for c in cells if c) and any(cells)


def parse(path: Path) -> dict[str, dict]:
    """section -> {"header": [...], "rows": {key: [cells]}, "order": [keys]}"""
    sections: dict[str, dict] = {}
    section = "(preamble)"
    header: list[str] | None = None
    in_code = False
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if raw.startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        if raw.startswith("## "):
            section = raw[3:].strip()
            header = None
            continue
        if raw.startswith("|"):
            cells = split_row(raw)
            if is_rule(cells):
                continue
            sec = sections.setdefault(section, {"header": None, "rows": {}, "order": []})
            if header is None:
                header = cells
                sec["header"] = cells
                continue
            if len(cells) != len(header):
                print(f"{path.name}:{lineno}: {len(cells)} cells, header has {len(header)}",
                      file=sys.stderr)
            key = cells[0]
            sec["rows"][key] = cells
            sec["order"].append(key)
        else:
            header = None if raw.strip() == "" else header
    return sections


def num(s: str):
    s2 = s.replace("`", "").replace(",", "").strip()
    return float(s2) if NUM_RE.match(s2) else None


def fmt_num(x: float) -> str:
    return str(int(x)) if x == int(x) else f"{x:g}"


def diff_instruments(old: dict, new: dict, out: list[str]) -> None:
    o = old.get("Instruments", {"rows": {}, "order": []})
    n = new.get("Instruments", {"rows": {}, "order": []})
    keys = list(dict.fromkeys(list(o["order"]) + list(n["order"])))
    moved, same = [], 0
    for k in keys:
        ov = o["rows"].get(k, [None, ""])[1] if k in o["rows"] else None
        nv = n["rows"].get(k, [None, ""])[1] if k in n["rows"] else None
        if ov == nv:
            same += 1
            continue
        delta = ""
        if ov is not None and nv is not None:
            a, b = num(ov), num(nv)
            if a is not None and b is not None:
                d = b - a
                delta = f"{'+' if d >= 0 else ''}{fmt_num(d)}"
        moved.append((k, ov if ov is not None else "—", nv if nv is not None else "—", delta))
    out.append("## Instruments\n")
    if not moved:
        out.append(f"No instrument moved ({same} unchanged).\n")
        return
    out.append("| key | old | new | Δ |")
    out.append("|---|---|---|---|")
    for k, ov, nv, d in moved:
        out.append(f"| `{esc(k)}` | {esc(ov)} | {esc(nv)} | {d} |")
    out.append(f"\n{len(moved)} moved, {same} unchanged.\n")


def cell_diff(oc: list[str], nc: list[str], header: list[str] | None) -> list[str]:
    lines = []
    width = max(len(oc), len(nc))
    for i in range(1, width):
        a = oc[i] if i < len(oc) else ""
        b = nc[i] if i < len(nc) else ""
        if a != b:
            col = header[i] if header and i < len(header) else f"col {i}"
            lines.append(f"  - **{col}**")
            lines.append(f"    - was: {a}")
            lines.append(f"    - now: {b}")
    return lines


def diff_tables(old: dict, new: dict, out: list[str]) -> None:
    sections = [s for s in dict.fromkeys(list(old) + list(new)) if s not in ("Instruments", "(preamble)")]
    changed = added = removed = unchanged = 0
    for s in sections:
        o = old.get(s, {"header": None, "rows": {}, "order": []})
        n = new.get(s, {"header": None, "rows": {}, "order": []})
        keys = list(dict.fromkeys(list(o["order"]) + list(n["order"])))
        block: list[str] = []
        for k in keys:
            orow, nrow = o["rows"].get(k), n["rows"].get(k)
            if orow is None:
                added += 1
                block.append(f"- **{k}** — ADDED: " + " · ".join(nrow[1:]))
            elif nrow is None:
                removed += 1
                block.append(f"- **{k}** — REMOVED (was: " + " · ".join(orow[1:]) + ")")
            elif orow[1:] != nrow[1:]:
                changed += 1
                block.append(f"- **{k}** — changed")
                block.extend(cell_diff(orow, nrow, n["header"] or o["header"]))
            else:
                unchanged += 1
        if block:
            out.append(f"## {s}\n")
            out.extend(block)
            out.append("")
    out.append(f"**Rows:** {changed} changed, {added} added, {removed} removed, {unchanged} unchanged.\n")


def pick_latest() -> tuple[Path, Path]:
    files = sorted(p for p in SERIES.glob("*.md") if DATE_RE.match(p.name))
    if len(files) < 2:
        sys.exit(f"need two snapshots in {SERIES}, found {len(files)}")
    return files[-2], files[-1]


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("old", nargs="?")
    ap.add_argument("new", nargs="?")
    ap.add_argument("--latest", action="store_true", help="diff the two newest snapshots in the series")
    ap.add_argument("--out", help="also write the report to this file")
    a = ap.parse_args()
    if a.latest:
        old_p, new_p = pick_latest()
    elif a.old and a.new:
        old_p, new_p = Path(a.old), Path(a.new)
    else:
        ap.error("give OLD NEW or --latest")
    old, new = parse(old_p), parse(new_p)
    out = [f"# Ledger diff: `{old_p.name}` → `{new_p.name}`\n"]
    diff_instruments(old, new, out)
    diff_tables(old, new, out)
    report = "\n".join(out)
    print(report)
    if a.out:
        Path(a.out).write_text(report + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
