module

public import L4YAML.Proofs.Production.Acceptance.Quoted

public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Proofs.Production.Acceptance.Quoted
public meta import L4YAML.Proofs.Production.Acceptance.Properties
@[expose] public section Blanket

/-! Rule-2 instantiations of the quoted-scalar acceptance lemmas: the scanner's landing
    (`content`, byte offset, column) on inputs that `SCDoubleQuotedOk` / `SCSingleQuotedOk`
    derive, and the refuting inputs the unnarrowed converse would wrongly admit. -/

namespace L4YAML.Proofs.Acceptance.Probes

open L4YAML
open L4YAML.Scanner
open L4YAML.Proofs.Acceptance

def quotedAt (scan : ScannerState → Except ScanError ScannerState) (style : ScalarStyle)
    (s : String) (flow : Bool) : Option (String × Nat × Nat) :=
  match scan { ScannerState.mk' s with flowLevel := if flow then 1 else 0 } with
  | .ok s' =>
    match s'.tokens.back? with
    | some t =>
      match t.val with
      | .scalar c st => if st == style then some (c, s'.offset, s'.col) else none
      | _ => none
    | none => none
  | .error _ => none

def dq (s : String) (flow : Bool := false) := quotedAt scanDoubleQuoted .doubleQuoted s flow
def sq (s : String) (flow : Bool := false) := quotedAt scanSingleQuoted .singleQuoted s flow

-- Double-quoted, accepted (offset = bytes consumed, col = chars consumed)
#guard dq "\"abc\"" == some ("abc", 5, 5)
#guard dq "\"\"" == some ("", 2, 2)
#guard dq "\"a b\tc\"" == some ("a b\tc", 7, 7)
#guard dq "\"\\t\\n\\\\\\\"\"" == some ("\t\n\\\"", 10, 10)
#guard dq "\"\\x41\\u00e9\\U0001F600\"" == some ("Aé😀", 22, 22)
#guard dq "\"é\"" == some ("é", 4, 3)
#guard dq "\"a\"  # c" == some ("a", 3, 3)
#guard dq "\"a\": b" == some ("a", 3, 3)
#guard dq "\"a\"\nb" == some ("a", 3, 3)
#guard dq "\"a\" \t" == some ("a", 3, 3)
#guard dq "\"a\"b" true == some ("a", 3, 3)
#guard dq "\"\\ \\/\\_\\N\\L\\P\"" == some (" /\u00A0\u0085\u2028\u2029", 14, 14)
-- Double-quoted refuters of the unnarrowed converse
#guard dq "\"\x01\"" == none          -- [107] admits C0; scanner: invalidControlChar
#guard dq "\"\\uD800\"" == none        -- [60] digits only; scanner: unicodeOutOfRange
#guard dq "\"\\UFFFFFFFF\"" == none    -- [61] digits only; scanner: unicodeOutOfRange
#guard dq "\"a\"b" == none             -- block context: trailingContent

-- Single-quoted, accepted
#guard sq "'abc'" == some ("abc", 5, 5)
#guard sq "''" == some ("", 2, 2)
#guard sq "'a''b'" == some ("a'b", 6, 6)
#guard sq "'a\"b\\c'" == some ("a\"b\\c", 7, 7)
#guard sq "'é'" == some ("é", 4, 3)
#guard sq "'a' #x" == some ("a", 3, 3)
#guard sq "'a': b" == some ("a", 3, 3)
#guard sq "'a'\nb" == some ("a", 3, 3)
#guard sq "'a'b" true == some ("a", 3, 3)
#guard sq "'a b\tc'" == some ("a b\tc", 7, 7)
#guard sq "''''''" == some ("''", 6, 6)
#guard sq "'a' \t" == some ("a", 3, 3)
-- Single-quoted refuters of the unnarrowed converse
#guard sq "'\x01'" == none             -- [118] admits C0; scanner: invalidControlChar
#guard sq "'a'b" == none               -- block context: trailingContent
#guard sq "'''''" == none              -- quote-quote greed: unterminatedScalar
#guard sq "''''" == some ("'", 4, 4)   -- [120] derives `''` at offset 2; scanner lands at 4

-- The block-context trailing hypothesis
#guard TrailingOk "  # c".toList
#guard TrailingOk ": b".toList
#guard TrailingOk "\nb".toList
#guard TrailingOk " \t".toList
#guard TrailingOk "".toList
#guard !TrailingOk "b".toList
#guard !TrailingOk " x".toList

-- Multi-line: `quotedAtInd` sets the block indentation floor the scanner folds against.
def quotedAtInd (scan : ScannerState → Except ScanError ScannerState) (style : ScalarStyle)
    (s : String) (flow : Bool) (indent : Int) : Option (String × Nat × Nat) :=
  let base := ScannerState.mk' s
  let entry : IndentEntry := { column := indent, isSequence := false }
  match scan { base with flowLevel := if flow then 1 else 0, indents := base.indents.push entry } with
  | .ok s' =>
    match s'.tokens.back? with
    | some t =>
      match t.val with
      | .scalar c st => if st == style then some (c, s'.offset, s'.col) else none
      | _ => none
    | none => none
  | .error _ => none

def dqi (s : String) (indent : Int) (flow : Bool := false) :=
  quotedAtInd scanDoubleQuoted .doubleQuoted s flow indent
def sqi (s : String) (indent : Int) (flow : Bool := false) :=
  quotedAtInd scanSingleQuoted .singleQuoted s flow indent

-- Double-quoted multi-line, accepted (`SCDoubleQuotedMultiOk n`, `n` above the floor)
#guard dq "\"a\nb\"" == some ("a b", 5, 2)
#guard dq "\"a\n\nb\"" == some ("a\nb", 6, 2)
#guard dq "\"a\n  \n\t\n b\"" == some ("a\n\nb", 11, 3)
#guard dq "\"a \n  b\"" == some ("a b", 8, 4)
#guard dq "\"a\\\n  b\"" == some ("ab", 8, 4)
#guard dq "\"a\\\n\n  b\"" == some ("a\nb", 9, 4)
#guard dq "\"a\n...\"" == some ("a ...", 7, 4)
#guard dq "\"a\r\nb\"" == some ("a b", 6, 2)
#guard dq "\"a\rb\"" == some ("a b", 5, 2)
#guard dqi "\"a\n  b\"" 1 == some ("a b", 7, 4)
#guard dqi "\"a\n \tb\"" 0 == some ("a b", 7, 4)
#guard dqi "\"a\n\n  b\"" 0 true == some ("a\nb", 8, 4)
-- Double-quoted multi-line, refuted without the narrowing
#guard dq "\"a\n---\nb\"" == none        -- document marker at the landing
#guard dqi "\"a\nb\"" 0 == none            -- continuation does not clear the floor
#guard dqi "\"a\n\tb\"" 1 == none          -- tab in indentation under the floor
#guard dqi "\"a\n\nb\"" 0 true == none      -- same floor in flow context

-- Single-quoted multi-line, accepted (`SCSingleQuotedMultiOk n`)
#guard sq "'a\nb'" == some ("a b", 5, 2)
#guard sq "'a\n\nb'" == some ("a\nb", 6, 2)
#guard sq "'a\n  \n\t\n b'" == some ("a\n\nb", 11, 3)
#guard sq "'a \n  b'" == some ("a b", 8, 4)
#guard sq "'a\n...'" == some ("a ...", 7, 4)
#guard sq "'a\r\nb'" == some ("a b", 6, 2)
#guard sq "'a\rb'" == some ("a b", 5, 2)
#guard sq "'a\n b''c'" == some ("a b'c", 9, 6)
#guard sqi "'a\n  b'" 1 == some ("a b", 7, 4)
#guard sqi "'a\n \tb'" 0 == some ("a b", 7, 4)
#guard sqi "'a\n\n  b'" 0 true == some ("a\nb", 8, 4)
-- Single-quoted multi-line, refuted without the narrowing
#guard sq "'a\n---\nb'" == none
#guard sqi "'a\nb'" 0 == none
#guard sqi "'a\n\tb'" 1 == none
#guard sqi "'a\n\nb'" 0 true == none

/-! ## Plain scalars, one line (`Acceptance/Plain.lean`)

`pln s` is the scanner's landing `(content, offset, col)`; `scanPlainScalar` never fails in
block context, it stops. Accepted inputs land at the end of the derivation's trailing white
run with the trimmed content; the refuters show where `[133]` derives further. -/
def pln (s : String) (flow : Bool := false) := quotedAt scanPlainScalar .plain s flow

#guard pln "a b" == some ("a b", 3, 3)
#guard pln "a#c" == some ("a#c", 3, 3)
#guard pln "a:b" == some ("a:b", 3, 3)
#guard pln "a,b" == some ("a,b", 3, 3)
#guard pln "a\t b" == some ("a\t b", 4, 4)
#guard pln "-a" == some ("-a", 2, 2)
#guard pln "- a" == some ("- a", 3, 3)
#guard pln ":a" == some (":a", 2, 2)
#guard pln "? a" == some ("? a", 3, 3)
#guard pln "a :b" == some ("a :b", 4, 4)
#guard pln "a: b" == some ("a", 1, 1)
#guard pln "a,b" true == some ("a", 1, 1)
#guard pln "a]b" true == some ("a", 1, 1)
-- Trailing whites are consumed and trimmed: the landing is after the white run.
#guard pln "a  " == some ("a", 3, 3)
#guard pln "a \t" == some ("a", 3, 3)
-- Refuter: `[130] hashAfterNs` derives `#` after a space (`col > 0`); the scanner reads a comment.
#guard pln "a #b" == some ("a", 2, 2)
#guard pln "a #c" == some ("a", 2, 2)
-- `[130]` via `isNsChar` and the scanner agree on C0: both stop before `\x01`.
#guard pln "a\x01b" == some ("a", 1, 1)
-- Refuter: `[126] dashSafe` derives `---`; at col 0 the scanner sees a document marker
-- (`atDocumentBoundary`) and emits an empty plain scalar without moving.
#guard pln "---" == some ("", 0, 0)
#guard pln "--- x" == some ("", 0, 0)
#guard pln "... x" == some ("", 0, 0)
#guard pln "---x" == some ("---x", 4, 4)

/-! ## Plain scalars, multi-line (`scanPlainScalar_accepts_multi`)

Block-context `[134]`/`[135]` folds: a single break folds to a space, `k` blank lines to `k`
line feeds; trailing whites before the break are dropped; the landing after the break is a
maximal white run and may use tabs.  Refuters: `#` on the continuation line (`[130]` admits it
after the `[69]` prefix; the scanner rolls back to the break), a document marker, a landing
below the content indent, and a break with nothing after it (the scanner rolls back). -/

def plnI (s : String) (indent : Int) (flow : Bool := false) :=
  quotedAtInd scanPlainScalar .plain s flow indent

#guard pln "a\n b" == some ("a b", 4, 2)
#guard pln "a\nb" == some ("a b", 3, 1)
#guard pln "a\n\n b" == some ("a\nb", 5, 2)
#guard pln "a\n b\n c" == some ("a b c", 7, 2)
#guard pln "a\n  b\n c" == some ("a b c", 8, 2)
#guard pln "a \n b" == some ("a b", 5, 2)
#guard pln "a\t\n b" == some ("a b", 5, 2)
#guard pln "a\r\n b" == some ("a b", 5, 2)
#guard pln "a\n \n b" == some ("a\nb", 6, 2)
#guard pln "a\n b\n\n\n c" == some ("a b\n\nc", 9, 2)
#guard pln "a\n\tb" == some ("a b", 4, 2)
#guard pln "a\n \tb" == some ("a b", 5, 3)
#guard pln "a\n b: c" == some ("a b", 4, 2)
#guard pln "a\n b #c" == some ("a b", 5, 3)
#guard pln "a\n- b" == some ("a - b", 5, 3)
#guard pln "a\n -b" == some ("a -b", 5, 3)
#guard pln "a\n---x" == some ("a ---x", 6, 4)
#guard plnI "a\n  b" 1 == some ("a b", 5, 3)
#guard plnI "a\n b" 0 == some ("a b", 4, 2)
-- Refuters: `#` after the fold, document markers, under-indentation, nothing after the break.
#guard pln "a\n #c\n b" == some ("a", 1, 1)
#guard pln "a\n---\nb" == some ("a", 1, 1)
#guard pln "a\n--- \nb" == some ("a", 1, 1)
#guard pln "a\n...\nb" == some ("a", 1, 1)
#guard plnI "a\n b" 1 == some ("a", 1, 1)
#guard pln "a\n" == some ("a", 1, 1)
#guard pln "a\n  " == some ("a", 1, 1)
#guard pln "a\n b\n " == some ("a b", 4, 2)

/-! ## Plain scalars, break-terminated (`PlainBreakStopOk`)

The scanner tries the fold at every break and rolls back to the break when the next line is
under-indented, a document marker, or adds no content (EOF, `#`, `: `, an unsafe character). -/

#guard pln "a \n" == some ("a", 2, 2)
#guard pln "a\n: b" == some ("a", 1, 1)
#guard pln "a\n:" == some ("a", 1, 1)
#guard pln "a\n\x01" == some ("a", 1, 1)
#guard pln "a\n #c" == some ("a", 1, 1)
#guard pln "a\n\n#c" == some ("a", 1, 1)
#guard pln "a\n\n" == some ("a", 1, 1)
#guard pln "a\n \n" == some ("a", 1, 1)
#guard pln "a\n---" == some ("a", 1, 1)
#guard pln "a\n..." == some ("a", 1, 1)
#guard pln "a b\n#c" == some ("a b", 3, 3)
#guard plnI "a\nb" 0 == some ("a", 1, 1)
#guard plnI "a\n \tb" 1 == some ("a", 1, 1)
#guard plnI "a\n  b\n c" 1 == some ("a b", 5, 3)

/-! ## Plain scalars, multi-line in flow context (`PlainNextLineOk true`, `PlainFlowBreakStopOk`)

Same folds as block context, but under-indentation is a hard `underIndentedScalar` error (and a
tab in the indentation `tabInIndentation`), so those inputs scan to `none`; `#`, a flow
indicator, `: `, EOF or a document marker after the fold roll back to the break. -/

#guard pln "a\n b" true == some ("a b", 4, 2)
#guard pln "a\nb" true == some ("a b", 3, 1)
#guard plnI "a\n b" 0 true == some ("a b", 4, 2)
#guard plnI "a\n  b" 1 true == some ("a b", 5, 3)
#guard pln "a\n\n b" true == some ("a\nb", 5, 2)
#guard pln "a \n b" true == some ("a b", 5, 2)
#guard pln "a\n \n b" true == some ("a\nb", 6, 2)
#guard pln "a\r\n b" true == some ("a b", 5, 2)
#guard pln "a\n b," true == some ("a b", 4, 2)
#guard pln "a\n b]" true == some ("a b", 4, 2)
#guard pln "a\n b: c" true == some ("a b", 4, 2)
#guard pln "a\n\tb" true == some ("a b", 4, 2)
-- Rollbacks to the break.
#guard pln "a\n #c" true == some ("a", 1, 1)
#guard pln "a\n" true == some ("a", 1, 1)
#guard pln "a\n  " true == some ("a", 1, 1)
#guard pln "a\n," true == some ("a", 1, 1)
#guard pln "a\n]" true == some ("a", 1, 1)
#guard pln "a\n: b" true == some ("a", 1, 1)
#guard pln "a\n---\nb" true == some ("a", 1, 1)
#guard pln "a\n--- b" true == some ("a", 1, 1)
-- Hard errors (no refusal arm): the converse needs the floor hypothesis.
#guard plnI "a\nb" 0 true == none
#guard plnI "a\n b" 1 true == none
#guard plnI "a\n\tb" 0 true == none

||||||| parent of d7d4c298 (proof(acceptance): anchor/alias/tag scanner converses (Stream E))
||||||| parent of 2aacaaa7 (proof(acceptance): anchor/alias/tag scanner converses (Stream E))
/-! ### Node properties (`scanAnchorOrAlias_accepts`, `scanTag_accepts`) -/

def propAt (scan : ScannerState → Except ScanError ScannerState) (s : String) :
    Option (String × String × Nat × Nat) :=
  match scan (ScannerState.mk' s) with
  | .ok s' =>
    match s'.tokens.back? with
    | some t =>
      match t.val with
      | .anchor n => some ("&", n, s'.offset, s'.col)
      | .alias n => some ("*", n, s'.offset, s'.col)
      | .tag h suf => some (h, suf, s'.offset, s'.col)
      | _ => none
    | none => none
  | .error _ => none

def anc (s : String) := propAt (scanAnchorOrAlias · true) s
def ali (s : String) := propAt (scanAnchorOrAlias · false) s
def tg (s : String) := propAt scanTag s

-- Anchors: a maximal `[102] ns-anchor-char` run; `[23]` flow indicators stop it in any context.
#guard anc "&a b" == some ("&", "a", 2, 2)
#guard anc "&abc" == some ("&", "abc", 4, 4)
#guard anc "&a-b_c.d" == some ("&", "a-b_c.d", 8, 8)
#guard anc "&a,b" == some ("&", "a", 2, 2)
#guard anc "&a]b" == some ("&", "a", 2, 2)
#guard anc "&a{b" == some ("&", "a", 2, 2)
#guard anc "&a\tb" == some ("&", "a", 2, 2)
#guard anc "&a\nb" == some ("&", "a", 2, 2)
#guard anc "&a\rb" == some ("&", "a", 2, 2)
#guard anc "&é b" == some ("&", "é", 3, 2)
#guard anc "&a:b" == some ("&", "a:b", 4, 4)
#guard anc "&a#b" == some ("&", "a#b", 4, 4)
-- Non-printable and BOM stop the run (`isPrintableBool`, `c != '\uFEFF'`).
#guard anc "&a\x01b" == some ("&", "a", 2, 2)
#guard anc "&a\uFEFFb" == some ("&", "a", 2, 2)
-- Refuter of the unnarrowed `GStar`: an empty name is `emptyAnchorName`.
#guard anc "& b" == none
#guard anc "&" == none
#guard anc "&,x" == none
-- Aliases share the collector.
#guard ali "*a b" == some ("*", "a", 2, 2)
#guard ali "*abc" == some ("*", "abc", 4, 4)
#guard ali "*a,b" == some ("*", "a", 2, 2)
#guard ali "*a}b" == some ("*", "a", 2, 2)
#guard ali "*a b" == some ("*", "a", 2, 2)
#guard ali "*é" == some ("*", "é", 3, 2)
#guard ali "*a\nb" == some ("*", "a", 2, 2)
#guard ali "* b" == none
#guard ali "*" == none
#guard ali "*[a" == none

-- Tags, verbatim `[98]`: `!<` uri+ `>`; `>` is consumed.
#guard tg "!<tag:x> b" == some ("", "tag:x", 8, 8)
#guard tg "!<tag:x>b" == some ("", "tag:x", 8, 8)
#guard tg "!<a,b>" == some ("", "a,b", 6, 6)
#guard tg "!<%21>" == some ("", "%21", 6, 6)
#guard tg "!<> b" == none
#guard tg "!<tag:x" == none
#guard tg "!<tag x>" == none
-- Secondary `[91]`: `!!` then a maximal `[40] ns-tag-char` run (`,`/`[`/`]`/`{`/`}` excluded).
#guard tg "!!str b" == some ("!!", "str", 5, 5)
#guard tg "!!" == some ("!!", "", 2, 2)
#guard tg "!!a:b" == some ("!!", "a:b", 5, 5)
#guard tg "!!a,b" == some ("!!", "a", 3, 3)
#guard tg "!!%21" == some ("!!", "%21", 5, 5)
-- Named `[92]`: `!` word+ `!` then a tag-char run.
#guard tg "!e!x b" == some ("!e!", "x", 4, 4)
#guard tg "!e! b" == some ("!e!", "", 3, 3)
#guard tg "!e!a:b" == some ("!e!", "a:b", 6, 6)
#guard tg "!e!a,b" == some ("!e!", "a", 4, 4)
#guard tg "!a-b!x" == some ("!a-b!", "x", 6, 6)
-- Primary `[90]` / non-specific `[100]`: the scanner reads only `[38] ns-word-char`s here.
#guard tg "!a b" == some ("!", "a", 2, 2)
#guard tg "! b" == some ("!", "", 1, 1)
#guard tg "!" == some ("!", "", 1, 1)
#guard tg "!a,b" == some ("!", "a", 2, 2)
#guard tg "!a-b" == some ("!", "a-b", 4, 4)
-- Refuters: `SCNsTagProperty.primary` admits any `[40]` suffix (`%21`, `a:b`); the scanner
-- stops at `%` and `:` — hence `TagOk.primary` uses `isWordCharProp`.
#guard tg "!%21 b" == some ("!", "", 1, 1)
#guard tg "!a:b" == some ("!", "a", 2, 2)
#guard tg "!a%21" == some ("!", "a", 2, 2)

end L4YAML.Proofs.Acceptance.Probes
