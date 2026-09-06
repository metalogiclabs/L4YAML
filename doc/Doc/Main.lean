/-
  L4YAML Documentation — Build entry point

  Build with:  lake exe l4yaml-doc
  Serve with:  python3 -m http.server 8000 --directory Doc/_out
-/
import VersoManual
import Doc.L4YAML

open Verso Doc
open Verso.Genre Manual

/--
Backport of verso PR #977 (upstream commit `a20c785b`, on `main` only): the margin-note
counter must be created inside `<main>`. Verso makes `<main>` a size query container
(`container: main / inline-size`, Html/Style.lean), and a query container applies CSS
*style containment*, which counters cannot cross — with the counter established on
`<body>` (Marginalia.css), each note's `counter-increment` finds no counter in scope,
starts its own, and every margin note and its in-text mark renders as "1". The reset
cannot sit on `<main>` itself either: a containment boundary blocks its own interior.
Upstream resets on `.content-wrapper`, and this rule is that fix verbatim.

Advancing the verso pin to `a20c785b` instead is blocked by the toolchain lockstep:
that commit's own `lean-toolchain` is v4.34.0-rc2, past this stack's v4.33.0.
Delete this override when the verso pin advances past #977.
-/
def versoMarginNoteCounterFix : String := r##"
.content-wrapper {
  counter-reset: margin-note-counter;
}
"##

def config : RenderConfig where
  emitTeX := false
  -- Also emit the self-contained single page; the PDF is rendered from it so the
  -- document (and its bookmark outline) come out in true document order, instead of
  -- the alphabetical, lossy merge a multi-page directory would produce.
  emitHtmlSingle := .immediately
  emitHtmlMulti := .immediately
  htmlDepth := 2
  -- One copy at the site root: every page's <base> tag points there, so the chapters'
  -- page-relative `graphs/<name>.svg` references resolve on every multi-page page and
  -- on the single page alike.
  extraFilesHtml := [("Doc/L4YAML/graphs", "graphs")]
  extraCss := [versoMarginNoteCounterFix]

def main (args : List String) := manualMain (%doc Doc.L4YAML) (options := args) (config := config)
