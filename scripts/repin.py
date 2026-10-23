#!/usr/bin/env python3
"""Re-derive the census pins (`def expected… :=`) from one `lake build` log.

Every guard under `Tests/Guards/Proofs/` pins what its census counted as a literal
(`String`, `Nat`, `List String`, `List Name`) and throws
`"<title>.\\nexpected: {expectedFoo}\\ngot:      {got}"` when the tree moves.  Any PR that
touches a proof moves several of them, and every merge onto the base moves them again,
so re-pinning by hand (read `got:`, find the def, paste) is the recurring tax of
parallel work.  This reads the log once and rewrites each moved pin to what the build
reported.

Usage:
    lake build > /tmp/build.log 2>&1
    python3 scripts/repin.py /tmp/build.log            # rewrite the pins
    python3 scripts/repin.py /tmp/build.log --check    # report, do not write
    lake build                                         # the next layer may move more

One run is a FLOOR: a guard that throws on its first check never reaches its later
ones, and a failing module blocks its dependents.  Rebuild and re-run until the log
reports no moved pin.  Then read every change — a pin is a decision, and the script
only does the typing.

A pin whose literal carries comments between or after its entries is reported as
`skipped` and left for a hand edit — the notes beside the rows are readings, not noise.

The `got:` line is Lean's `toString`, so a `List String` prints as `[a, b]` without
quotes.  Elements are split on `, `; an element that itself contains `, ` is re-glued
only when the OLD list had an element with the same prefix, and the result is flagged
`CHECK` in the report either way.
"""
import pathlib
import re
import sys

ERR_HEAD = re.compile(r"^(?:error: )?(\S+\.lean):(\d+):(\d+):(?: error:)? ?(.*)$")
NEXT_BLOCK = re.compile(r"^(?:\S+\.lean:\d+:\d+:|error: |warning: |info: |✖|⚠|✔|Build |\[\d+/\d+\]|trace: )")
THROW = re.compile(r'throwError\s+"((?:[^"\\]|\\.|\\\n)*)"', re.DOTALL)
DEF = re.compile(r"^(?P<head>(?:private |protected )?def (?P<name>\w+)\s*:\s*(?P<ty>String|Nat|List String|List Name)\s*:=)[ \t]*(?P<same>.*)$")


def read_blocks(log_text):
    """Yield (file, line, message_lines) for each `error:` in the log."""
    lines = log_text.splitlines()
    i = 0
    while i < len(lines):
        m = ERR_HEAD.match(lines[i])
        if not m:
            i += 1
            continue
        body = [m.group(4)]
        i += 1
        while i < len(lines) and not NEXT_BLOCK.match(lines[i]) and not ERR_HEAD.match(lines[i]):
            body.append(lines[i])
            i += 1
        yield m.group(1), int(m.group(2)), body


def normalise_literal(s):
    s = re.sub(r"\\\n\s*", "", s)
    return s.replace("\\n", "\n").replace('\\"', '"')


def pin_name_for(src, title):
    """The `expected…` identifier of the throwError whose message starts with `title`."""
    hits = []
    for m in THROW.finditer(src):
        lit = normalise_literal(m.group(1))
        if lit.split("\n", 1)[0].strip() != title.strip():
            continue
        k = re.search(r"expected:\s*\{([\w.]+)\}", lit)
        if k:
            hits.append(k.group(1))
    return hits


def split_list(inner, old_items):
    if inner.strip() == "":
        return [], False
    raw = inner.split(", ")
    out, flagged, i = [], False, 0
    while i < len(raw):
        glued, j = raw[i], i
        while glued not in old_items and j + 1 < len(raw) and any(o.startswith(glued + ", ") for o in old_items):
            j += 1
            glued = glued + ", " + raw[j]
            flagged = True
        if ", " in glued or any(", " in o for o in old_items):
            flagged = True
        out.append(glued)
        i = j + 1
    return out, flagged


def old_list_items(body):
    items = re.findall(r'"((?:[^"\\]|\\.)*)"', body)
    if items:
        return items
    return re.findall(r"`([\w.«»']+)", body)


def lean_str(x):
    """Encode `x` as the body of a Lean string literal (backslash and quote escaped)."""
    return x.replace("\\", "\\\\").replace('"', '\\"')


def render(ty, value, old_body):
    """Return (new_text_after_:=, flagged)."""
    if ty == "Nat":
        return " " + value.strip(), False
    if ty == "String":
        v = lean_str(value.rstrip())
        if len(v) <= 60:
            return f' "{v}"', False
        words, lines, cur = v.split(" "), [], ""
        for w in words:
            if cur and len(cur) + 1 + len(w) > 76:
                lines.append(cur)
                cur = w
            else:
                cur = w if not cur else cur + " " + w
        lines.append(cur)
        return '\n  "' + " \\\n".join(lines) + '"', False
    v = value.strip()
    if not (v.startswith("[") and v.endswith("]")):
        raise ValueError(f"not a list literal: {v!r}")
    items, flagged = split_list(v[1:-1], old_list_items(old_body))
    if ty == "List String":
        items = [f'"{lean_str(x)}"' for x in items]
    else:
        items = [f"`{x}" for x in items]
    if not items:
        return " []", flagged
    if len(items) == 1 and len(items[0]) < 70:
        return f" [{items[0]}]", flagged
    return "\n  [" + ",\n   ".join(items) + "]", flagged


def def_span(lines, name):
    """(start, end, match, comments): the `def name … :=` line, the end of its body,
    and the comment lines that sit between the head and the literal."""
    for i, ln in enumerate(lines):
        m = DEF.match(ln)
        if not (m and m.group("name") == name):
            continue
        j = i + 1
        while j < len(lines) and (lines[j].strip() == "" or lines[j][0] in " \t"
                                  or lines[j - 1].rstrip().endswith("\\")):
            j += 1
        while j > i + 1 and lines[j - 1].strip() == "":
            j -= 1
        comments = []
        for k in range(i + 1, j):
            if lines[k].strip().startswith("--"):
                comments.append(lines[k])
            else:
                break
        annotated = any("--" in ln for ln in lines[i + 1 + len(comments):j])
        return i, j, m, comments, annotated
    return None


def main(argv):
    if len(argv) < 2 or argv[1] in ("-h", "--help"):
        print(__doc__)
        return 2
    check = "--check" in argv[2:]
    root = pathlib.Path(next((a for a in argv[2:] if not a.startswith("--")), "."))
    log = pathlib.Path(argv[1]).read_text(encoding="utf-8", errors="replace")
    edits = {}
    report, skipped = [], []
    for file, line, body in read_blocks(log):
        msg = "\n".join(body)
        exp = re.search(r"^expected:\s*(.*)$", msg, re.M)
        got = re.search(r"^got:\s*(.*)$", msg, re.M)
        if not (exp and got):
            continue
        path = root / file
        if not path.exists():
            skipped.append(f"{file}:{line}: file not found under {root}")
            continue
        src = path.read_text(encoding="utf-8")
        names = pin_name_for(src, body[0])
        if len(names) != 1:
            skipped.append(f"{file}:{line}: {body[0]!r} matches {len(names)} throw sites {names}")
            continue
        edits.setdefault(path, []).append((names[0], exp.group(1), got.group(1), f"{file}:{line}"))
    for path, pins in edits.items():
        lines = path.read_text(encoding="utf-8").split("\n")
        for name, expected, gotv, where in pins:
            span = def_span(lines, name)
            if span is None:
                skipped.append(f"{where}: no `def {name} : … :=` found")
                continue
            i, j, m, comments, annotated = span
            if annotated:
                skipped.append(f"{where}: `{name}` carries comments inside its literal; re-pin it by hand")
                continue
            old_body = (m.group("same") + "\n" + "\n".join(lines[i + 1 + len(comments):j])).strip()
            try:
                new_text, flagged = render(m.group("ty"), gotv, old_body)
            except ValueError as e:
                skipped.append(f"{where}: {e}")
                continue
            new_block = [m.group("head")] + comments + new_text.lstrip("\n").split("\n") \
                if comments else (m.group("head") + new_text).split("\n")
            if comments and not new_text.startswith("\n"):
                new_block[-1] = "  " + new_block[-1].strip()
            lines[i:j] = new_block
            report.append((where, name, m.group("ty"), expected, gotv, flagged))
        if not check:
            path.write_text("\n".join(lines), encoding="utf-8")
    for where, name, ty, expected, gotv, flagged in report:
        tag = "  CHECK" if flagged else ""
        print(f"{'would re-pin' if check else 're-pinned'} {where} {name} : {ty}{tag}\n    was {expected}\n    now {gotv}")
    for s in skipped:
        print(f"skipped {s}")
    if not report and not skipped:
        print("no moved pin in the log")
    return 0 if report or not skipped else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
