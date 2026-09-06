#!/usr/bin/env python3
"""Rewrite <img> tags whose src is an SVG into <object> embeds, in place.

Verso renders every Markdown image as <img>. An SVG loaded through <img> is
static: browsers disable all navigation inside it, so the Graphviz `URL=`
attributes the theorem-dependency graphs carry (doc-gen4 links on every node,
emitted by L4YAML.FGM's TheoremGraph tool) are dead. Loaded through
<object type="image/svg+xml"> the same SVG keeps its hyperlinks.

Run this over the MULTI-page site only (doc/_out/html-multi), after
`lake exe l4yaml-doc`. The single page stays <img> on purpose: it exists to
feed scripts/html-to-pdf.py, and WeasyPrint rasterizes <img src="*.svg">
natively while an <object> would render as its fallback text.

The rewrite keeps the src URL verbatim (as `data=`), so it resolves through
each page's <base> tag exactly as the <img> did, and it moves the alt text
into the element body, where it serves the same fallback role. Idempotent:
a second run finds no matching <img>.
"""

import re
import sys
from pathlib import Path

IMG_RE = re.compile(r"<img\b[^>]*>", re.IGNORECASE)
ATTR_RE = re.compile(r'([a-zA-Z-]+)\s*=\s*"([^"]*)"')


def rewrite(html: str) -> tuple[str, int]:
    count = 0

    def replace(m: re.Match) -> str:
        nonlocal count
        attrs = dict(ATTR_RE.findall(m.group(0)))
        src = attrs.get("src", "")
        if not src.split("#")[0].split("?")[0].lower().endswith(".svg"):
            return m.group(0)
        count += 1
        title = f' title="{attrs["title"]}"' if attrs.get("title") else ""
        # Attribute values are already HTML-escaped, and every entity that is
        # valid in an attribute is valid as element content, so the alt text
        # can be moved into the body verbatim.
        alt = attrs.get("alt", "")
        return f'<object type="image/svg+xml" data="{src}"{title}>{alt}</object>'

    return IMG_RE.sub(replace, html), count


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <html-tree>", file=sys.stderr)
        return 2
    root = Path(sys.argv[1])
    if not root.is_dir():
        print(f"error: {root} is not a directory", file=sys.stderr)
        return 2

    pages = files = 0
    for path in sorted(root.rglob("*.html")):
        html = path.read_text(encoding="utf-8")
        rewritten, n = rewrite(html)
        if n:
            path.write_text(rewritten, encoding="utf-8")
            pages += 1
            files += n
    print(f"svg-objects: rewrote {files} SVG <img> into <object> across {pages} pages under {root}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
