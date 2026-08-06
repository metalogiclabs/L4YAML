/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.CharStream
import L4YAML.Spec.CharPredicates

/-! # `IndexedScanner` — Phase 3 character/whitespace layer (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6). The legacy `L4YAML/Scanner/*.lean`
remains the production scanner for the duration of Phase 3 Steps 2–5.

## What this layer provides

The lowest-level recognisers over `IxCursor input`:

- **Layer A — character-class peeks**: `peekIsLineBreak`,
  `peekIsWhiteSpace`, `peekIsBlank`, `peekIsIndentChar` — each
  inspects the current character (if any) against a YAML 1.2.2
  character class from `Spec.CharPredicates`.

- **Layer B — whitespace runs**: `skipSpaces` (consume `s-space*`,
  returning the count for indent tracking) and `skipWhitespace`
  (consume `s-white*` = spaces + tabs, for `[66] s-separate-in-line`).

- **Layer C — line break**: `consumeLineBreak` advances past one
  `[28] b-break`, with the CRLF special case folded to a single line
  increment (matching legacy `ScannerState.consumeNewline`).

Whitespace and line breaks are *consumed*, not emitted as tokens
(matches the legacy convention: `YamlToken` has no whitespace
constructor; indentation changes produce *virtual* `blockEnd` /
`blockSequenceStart` / `blockMappingStart` tokens at higher layers).

## Termination

`skipSpaces` / `skipWhitespace` recurse on a `Nat` fuel parameter.
The entry points pass `input.utf8ByteSize` — a safe upper bound,
since each loop step that advances strictly increases the cursor
offset (`advance_offset_lt_of_hasMore` from `Indexed.CharStream`).
Termination correctness — that the cursor ends at a non-whitespace
or at end-of-input — is proven in
`L4YAML/Proofs/Scanner/IndexedWhitespace.lean`.
-/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.CharPredicates L4YAML.Indexed

/-! ## Layer A — character-class peeks

Each `peekIs*` returns `true` exactly when the cursor's current
character is in the corresponding YAML 1.2.2 class. At end-of-input
all return `false` (no character to inspect). -/

/-- Cursor points at a §5.4 line-break character (`'\n'` or `'\r'`). -/
@[inline] def peekIsLineBreak {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | some ch => isLineBreakBool ch
  | none    => false

/-- Cursor points at a §5.5 whitespace character (space or tab). -/
@[inline] def peekIsWhiteSpace {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | some ch => isWhiteSpaceBool ch
  | none    => false

/-- Cursor points at a blank: whitespace or line break. -/
@[inline] def peekIsBlank {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | some ch => isBlankBool ch
  | none    => false

/-- Cursor points at a §6.1 indent character (space only — tabs are
    *not* indent characters per §6.1). -/
@[inline] def peekIsIndentChar {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | some ch => isIndentCharBool ch
  | none    => false

/-! ## Layer B — whitespace runs -/

/-- Inner loop for `skipSpaces`. Structurally recursive on `fuel`.
    Returns `(c', n)` where `c'` is the cursor after the run and
    `n` is the count of spaces consumed. The body uses `.1`/`.2`
    projections rather than `let`-destructure so that `simp` /
    `rfl` reduction goes through cleanly in proofs. -/
def skipSpacesLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input × Nat
  | 0          => (c, 0)
  | fuel + 1 =>
    if peekIsIndentChar c then
      let r := skipSpacesLoop c.advance fuel
      (r.1, r.2 + 1)
    else
      (c, 0)

/-- Consume a maximal run of `s-space` characters (§6.1 indentation).
    Tabs are *not* consumed — they remain at the cursor. Returns the
    post-run cursor and the number of spaces consumed (Step 3's
    indent-tracking will use the count). -/
@[inline] def skipSpaces {input : String} (c : IxCursor input) :
    IxCursor input × Nat :=
  skipSpacesLoop c input.utf8ByteSize

/-- Inner loop for `skipWhitespace`. -/
def skipWhitespaceLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input
  | 0          => c
  | fuel + 1 =>
    if peekIsWhiteSpace c then
      skipWhitespaceLoop c.advance fuel
    else
      c

/-- Consume a maximal run of `s-white` characters (spaces *and* tabs,
    [66] s-separate-in-line). Used in flow context and after key/value
    indicators where tabs are permitted. -/
@[inline] def skipWhitespace {input : String} (c : IxCursor input) :
    IxCursor input :=
  skipWhitespaceLoop c input.utf8ByteSize

/-! ## Layer B' — comment text (§6.6 [75] `c-nb-comment-text`)

Comment scanning is split into two halves:

- `skipCommentTextLoop` (here) — consume the body of a comment
  starting from *after* the `'#'`. The body is `nb-char*`
  ([27] `nb-char ::= c-printable - b-char - c-byte-order-mark`):
  every non-line-break, non-EOF character, with no inner
  validation of `c-printable` (that's a separate spec check, not
  scanning state).

- `skipToContent` (Layer D, below) — composite that consumes
  whitespace, a `'#'`-introduced comment if present, the line
  break, then recurses for the next line.

`skipCommentText` is its own loop because:

1. Its termination condition is *different* from `skipWhitespace`
   (stops at LF/CR, not at non-whitespace).
2. It does not produce a count — the comment text characters
   themselves are uninteresting for indent tracking (comments
   never establish indent).
3. Step 4 may want to capture comment text for round-tripping
   (the legacy scanner has a side-channel `comments` array); the
   capture is bolted onto `skipCommentTextLoop` then. -/

/-- Inner loop: consume characters until a line break (or EOF).
    Structurally recursive on `fuel`. -/
def skipCommentTextLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input
  | 0          => c
  | fuel + 1 =>
    if peekIsLineBreak c then c
    else
      match c.peek? with
      | none    => c
      | some _  => skipCommentTextLoop c.advance fuel

/-- Consume a comment body (`nb-char*`), stopping at the first
    line-break character or end-of-input. The leading `'#'` must
    already have been consumed by the caller (Layer D / dispatch). -/
@[inline] def skipCommentText {input : String} (c : IxCursor input) : IxCursor input :=
  skipCommentTextLoop c input.utf8ByteSize

/-- Collect-variant of `skipCommentTextLoop`: advances the cursor past a
    comment body while accumulating its text characters. Indexed twin of
    `L4YAML.Scanner.collectCommentTextLoop`. Used by `scanWithCommentsIx`
    to preserve comment text for round-tripping. -/
def collectCommentTextLoop {input : String} (c : IxCursor input) (text : String) :
    Nat → String × IxCursor input
  | 0          => (text, c)
  | fuel + 1 =>
    if peekIsLineBreak c then (text, c)
    else
      match c.peek? with
      | none    => (text, c)
      | some ch => collectCommentTextLoop c.advance (text.push ch) fuel

/-- Collect a comment body (`nb-char*`) starting after the `'#'`. Returns
    the text plus the cursor at the terminating line-break (or EOF). -/
@[inline] def collectCommentText {input : String} (c : IxCursor input) :
    String × IxCursor input :=
  collectCommentTextLoop c "" input.utf8ByteSize

/-! ## Layer C — line-break consumption -/

/-- Consume one `[28] b-break`. Three cases:

    - LF (`'\n'`): single `advance`.
    - CR (`'\r'`) not followed by LF: single `advance`.
    - CRLF (`'\r' '\n'`): two `advance`s, but only one logical line
      bump. `IxCursor.advance` already increments `line` on `'\r'`;
      advancing the `'\n'` would bump again, so we override the line
      counter to keep the post-CRLF line equal to the post-CR line.

    At any non-break character (including end-of-input) the cursor is
    returned unchanged. Matches legacy `ScannerState.consumeNewline`.

    We use `if/else` rather than Char-literal patterns in the match
    to keep the proof obligations decidable on `Char` equality. -/
def consumeLineBreak {input : String} (c : IxCursor input) : IxCursor input :=
  match c.peek? with
  | none    => c
  | some ch =>
    if isLineFeedBool ch then
      c.advance
    else if isCarriageReturnBool ch then
      match c.peekAt? 1 with
      | some n =>
        if isLineFeedBool n then
          let cAfterCR := c.advance
          let cAfterLF := cAfterCR.advance
          { pos := { offset := cAfterLF.pos.offset
                     line   := cAfterCR.pos.line
                     col    := 0 }
            posBound := cAfterLF.posBound }
        else
          c.advance
      | none => c.advance
    else
      c

/-! ## Layer D — composite line-comment dispatch
    (§6.6 [77] `s-b-comment`, §6.7 [79] `s-l-comments`)

`skipToContent` consumes the *between-token* whitespace:

1. `s-white*` — spaces and tabs (separation, not indentation).
2. An optional `'#'` comment to end-of-line.
3. A line break — if present, recurse on the next line.

Stops at the first character that is *content* (not whitespace,
not a comment, not a line break) or at end-of-input.

This matches the legacy `Scanner/Whitespace.lean::skipToContent`
*structurally* but without:

- The `needIndentCheck` flag (Step 3's indent-stack approach
  handles indent measurement explicitly, not via a flag).
- Tab-as-indentation error reporting (§6.1 tab error checks
  belong with the indent-stack at Step 4, where the current
  block's indent is known).
- The simple-key reset (a parser-layer concern; not in the
  scanner's character/line layer).

`skipToContent` therefore behaves correctly only as a *neutral*
consumer of skippable content — error reporting and simple-key
handling are layered on top in Step 4. -/

/-- Inner loop. Structurally recursive on `fuel`. The body is
    written without `let`-bindings (each call to `skipWhitespace c`
    is duplicated) so that `split` can decompose the `match` in
    proofs — Lean's elaborator opacifies `let`-bound expressions
    against the `split` tactic. -/
def skipToContentLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input
  | 0          => c
  | fuel + 1 =>
    -- After skipWhitespace, peek? is none, a line break, '#', or content.
    match (skipWhitespace c).peek? with
    | none    => skipWhitespace c
    | some ch =>
      if isCommentBool ch then
        skipToContentLoop
          (consumeLineBreak (skipCommentText (skipWhitespace c).advance)) fuel
      else if isLineBreakBool ch then
        skipToContentLoop (consumeLineBreak (skipWhitespace c)) fuel
      else
        skipWhitespace c

/-- Consume skippable inter-token content: whitespace, comments,
    and line breaks. Stops at the first content character or EOF.

    Matches `s-l-comments` ([79]) semantically; see legacy
    `Scanner/Whitespace.lean::skipToContent` for the error-aware
    counterpart that handles §6.1 tab violations. -/
@[inline] def skipToContent {input : String} (c : IxCursor input) : IxCursor input :=
  skipToContentLoop c (input.utf8ByteSize + 1)

/-- Comment-collecting variant of `skipToContentLoop`. Mirrors its
    structure but captures each comment's `(position, text)` pair as
    it scans. The position is the cursor at the `'#'`; the text is the
    body up to (but not including) the terminating line break.

    Indexed twin of legacy `Scanner.skipToContentLoop` +
    `skipToContentComment` (which thread a side-channel `comments`
    array through `ScannerState`). -/
def skipToContentLoopWithComments {input : String} (c : IxCursor input)
    (acc : Array (YamlPos × String)) :
    Nat → IxCursor input × Array (YamlPos × String)
  | 0          => (c, acc)
  | fuel + 1 =>
    let cAfterWs := skipWhitespace c
    match cAfterWs.peek? with
    | none    => (cAfterWs, acc)
    | some ch =>
      if isCommentBool ch then
        let commentPos := cAfterWs.pos
        let cAfterHash := cAfterWs.advance
        let (text, cAfterText) := collectCommentText cAfterHash
        let acc' := acc.push (commentPos, text)
        skipToContentLoopWithComments (consumeLineBreak cAfterText) acc' fuel
      else if isLineBreakBool ch then
        skipToContentLoopWithComments (consumeLineBreak cAfterWs) acc fuel
      else
        (cAfterWs, acc)

/-- Comment-collecting variant of `skipToContent`. Consumes skippable
    inter-token content (whitespace, comments, line breaks) while
    capturing each `'#'`-introduced comment's `(position, text)` pair.

    Used by `scanWithCommentsIx` to preserve comments for the
    comment-preserving public entry point `parseYamlWithComments`. -/
@[inline] def skipToContentWithComments {input : String} (c : IxCursor input)
    (acc : Array (YamlPos × String)) :
    IxCursor input × Array (YamlPos × String) :=
  skipToContentLoopWithComments c acc (input.utf8ByteSize + 1)

/-! ### Skip-to-content strictness walker (§6.1, §6.6)

`skipToContent` is a *neutral* consumer with no error channel (see the
layer note above), so the legacy `skipToContentWs` §6.1
tab-as-indentation check and the legacy `skipToContentComment`
"comment requires preceding `s-separate-in-line`" rule were silently
dropped at the cutover: the twin accepted tab-indented block content
(4EJS, Y79Y/003) and glued comments (`]#c` — 9JBA, CVW2, SU5Z).

`skipToContentErrIx` is a read-only walker over the same region the
real `skipToContent` consumes, reproducing exactly the errors the
legacy skip loop (plus its dispatcher `unexpectedChar '#'` fallback)
would raise. `scanNextTokenIx_preprocess` runs it on the pre-skip
cursor and throws; on `none` the real skip is behaviourally identical
to legacy. -/

/-- Is the character *before* byte offset `pos` `s-white`, a line
    break, or a BOM (all legal comment/tab context)? `true` at input
    start, mirroring legacy `peekBack? = none`. -/
def prevCharIsWhiteOrBomIx (input : String) (pos : Nat) : Bool :=
  if pos == 0 then true
  else
    isWhiteSpaceBool (String.Pos.Raw.get input (String.Pos.Raw.prev input ⟨pos⟩))
    || isLineBreakBool (String.Pos.Raw.get input (String.Pos.Raw.prev input ⟨pos⟩))
    || String.Pos.Raw.get input (String.Pos.Raw.prev input ⟨pos⟩) == '﻿'

/-- §6.6 [75]: may a comment start at cursor `c`?  `c-nb-comment-text`
    requires preceding `s-separate-in-line` = `s-white+` |
    start-of-line; a BOM is transparent (§5.2). Mirror of legacy
    `skipToContentComment`'s `commentOk`. -/
@[inline] def commentStartOkIx {input : String} (c : IxCursor input) : Bool :=
  c.pos.col == 0 || prevCharIsWhiteOrBomIx input c.pos.offset

/-- Phase-1 mirror of legacy `skipToContentWs` (§6.1): skip `s-space*`
    indentation, then reject a tab still inside indentation territory
    (at or below `currentIndent`, or at stream level outside flow)
    unless it precedes a comment, a blank rest-of-line, EOF, or — at
    stream level — an unambiguous flow indicator. Returns the cursor
    at which the comment phase continues. -/
@[yaml_spec "6.1", yaml_spec "6.3" 67 "s-line-prefix(n,c)"]
def skipToContentErrWsIx {input : String} (c : IxCursor input) (inFlow : Bool)
    (currentIndent : Int) (needIndentCheck : Bool) :
    Except ScanError (IxCursor input) :=
  if needIndentCheck then
    if (!inFlow && currentIndent < 0)
        || ((skipSpaces c).1.pos.col : Int) ≤ currentIndent then
      match (skipSpaces c).1.peek? with
      | some '\t' =>
        match (skipWhitespace (skipSpaces c).1).peek? with
        | some pc =>
          if isCommentBool pc then .ok (skipWhitespace (skipSpaces c).1)
          else if isLineBreakBool pc then .ok (skipWhitespace (skipSpaces c).1)
          else if currentIndent < 0 &&
              (pc == '{' || pc == '[' || pc == '}' || pc == ']' ||
               pc == '"' || pc == '\'' || pc == '!' || pc == '&' || pc == '*') then
            .ok (skipWhitespace (skipSpaces c).1)
          else
            .error (.tabInIndentation (skipSpaces c).1.pos.line (skipSpaces c).1.pos.col)
        | none => .ok (skipWhitespace (skipSpaces c).1)
      | _ => .ok (skipSpaces c).1
    else .ok (skipWhitespace c)
  else .ok (skipWhitespace c)

/-- Per-line strictness walker: phase 1 (`skipToContentErrWsIx`), then
    the §6.6 comment-start rule — a `#` *not* preceded by
    `s-separate-in-line`/line-start/BOM is exactly where the legacy
    dispatcher's `unexpectedChar` fallback fires (the legacy skip
    leaves the `#` unconsumed; no token can start with it). Recurses
    across line breaks with `needIndentCheck := true`, as legacy
    `consumeNewline` would set. Returns the first error, or `none`
    when the real `skipToContent` consumes the same region legally. -/
@[yaml_spec "6.6" 75 "c-nb-comment-text", yaml_spec "6.6" 79 "s-l-comments"]
def skipToContentErrLoopIx {input : String} (c : IxCursor input) (inFlow : Bool)
    (currentIndent : Int) (needIndentCheck : Bool) : Nat → Option ScanError
  | 0 => none
  | fuel + 1 =>
    match skipToContentErrWsIx c inFlow currentIndent needIndentCheck with
    | .error e => some e
    | .ok cw =>
      match cw.peek? with
      | some ch =>
        if isCommentBool ch then
          if commentStartOkIx cw then
            match (skipCommentText cw.advance).peek? with
            | some lb =>
              if isLineBreakBool lb then
                skipToContentErrLoopIx (consumeLineBreak (skipCommentText cw.advance))
                  inFlow currentIndent true fuel
              else none
            | none => none
          else some (.unexpectedChar '#' cw.pos.line cw.pos.col)
        else if isLineBreakBool ch then
          skipToContentErrLoopIx (consumeLineBreak cw) inFlow currentIndent true fuel
        else none
      | none => none

/-- Strictness walker over the inter-token skip region. See
    `skipToContentErrLoopIx`. -/
@[inline] def skipToContentErrIx {input : String} (c : IxCursor input)
    (inFlow : Bool) (currentIndent : Int) (needIndentCheck : Bool) :
    Option ScanError :=
  skipToContentErrLoopIx c inFlow currentIndent needIndentCheck
    (input.utf8ByteSize + 1)

/-! ## Layer E — scalar recognisers (§7.3, single-line subset)

Phase 3 Step 4a scope: quoted scalars (single- and double-) on a
single line, plus a single-line plain scalar. Multi-line folding,
plain scalars spanning multiple lines, and block scalars (literal +
folded) land in Step 4b.

Each quoted recogniser returns `Option (String × IxCursor input)`:
- `some (content, after)` — the matched scalar's resolved content
  and the cursor *after* the closing delimiter.
- `none` — recoverable failure (unterminated quote, invalid escape,
  multi-line content that Step 4a does not handle yet). Error
  reporting is layered on top in Step 5; the staging recognisers
  signal *failure* but do not classify *which* error.

The plain scalar recogniser is total (always returns) because plain
scalars terminate by *not finding* a continuation character; the
empty plain scalar is `("", c)` which is a valid (degenerate) match.

### Layer E1 — escape sequences (§5.7, single-char + hex)

`processEscapeIx` handles the 18 single-character escapes (`\0`, `\a`,
`\b`, `\t`, `\n`, `\v`, `\f`, `\r`, `\e`, `\ `, `\"`, `\/`, `\\`,
`\N`, `\_`, `\L`, `\P`, `\TAB`) and the three hex escapes (`\x`,
`\u`, `\U` with 2/4/8 hex digits). The cursor must already be
positioned *after* the leading `\`. -/

/-- `[36] ns-hex-digit ::= ns-dec-digit | [#x41-#x46] | [#x61-#x66]`
    — code-point ranges so the spec literals stay in numeric form. -/
@[inline,
  yaml_spec "5.6" 35 "ns-dec-digit",
  yaml_spec "5.6" 36 "ns-hex-digit"]
def isHexDigitBool (c : Char) : Bool :=
  (c.val ≥ 0x30 && c.val ≤ 0x39) || (c.val ≥ 0x41 && c.val ≤ 0x46)
  || (c.val ≥ 0x61 && c.val ≤ 0x66)

/-- Collect `n` hex digits from the cursor. Returns the digit string
    and the post-collection cursor. Stops early on non-hex or EOF —
    the caller checks the returned string's length against `n`. -/
def collectHexDigitsLoopIx {input : String} (c : IxCursor input)
    (hex : String) : Nat → String × IxCursor input
  | 0      => (hex, c)
  | n' + 1 =>
    match c.peek? with
    | some ch =>
      if isHexDigitBool ch then
        collectHexDigitsLoopIx c.advance (hex.push ch) n'
      else (hex, c)
    | none    => (hex, c)

/-- Hex-digit value, decoded under the assumption that the character
    is in `0..9 | a..f | A..F`. For non-hex inputs the result is
    undefined (in practice the caller has already filtered via
    `isHexDigitBool`). Code points refer to `[35] ns-dec-digit` (`#x30`)
    and `[36] ns-hex-digit` (`#x41`, `#x61`). -/
@[inline,
  yaml_spec "5.6" 35 "ns-dec-digit",
  yaml_spec "5.6" 36 "ns-hex-digit"]
def hexDigitValue (ch : Char) : Nat :=
  if ch.val ≥ 0x30 ∧ ch.val ≤ 0x39 then ch.toNat - 0x30
  else if ch.val ≥ 0x61 then ch.toNat - 0x61 + 10
  else ch.toNat - 0x41 + 10

/-- Fold a hex-digit string to its `Nat` value. Standalone so the
    `let val := ...` does not appear inside the `parseHexEscapeIx`
    body, where it would obstruct `split` in proofs (Reflection 37). -/
@[inline] def hexStringValue (hex : String) : Nat :=
  hex.foldl (fun acc ch => acc * 16 + hexDigitValue ch) 0

/-- Parse `n` hex digits and decode to a `Char`. Returns `none` if
    fewer than `n` digits are available or the value is ≥ 0x110000
    (outside the Unicode scalar range). -/
def parseHexEscapeIx {input : String} (c : IxCursor input) (n : Nat) :
    Option (Char × IxCursor input) :=
  if (collectHexDigitsLoopIx c "" n).1.length != n then
    none
  else if hexStringValue (collectHexDigitsLoopIx c "" n).1 < 0x110000 then
    some (Char.ofNat (hexStringValue (collectHexDigitsLoopIx c "" n).1),
          (collectHexDigitsLoopIx c "" n).2)
  else
    none

/-- The 18 single-character escapes of §5.7. `none` means the
    character is not a simple-escape indicator (could still be `'x'`,
    `'u'`, `'U'`, or unknown — `processEscapeIx` dispatches further). -/
def simpleEscapeChar (ch : Char) : Option Char :=
  if isNsEscNullBool ch              then some nsEscNullChar
  else if isNsEscBellBool ch         then some nsEscBellChar
  else if isNsEscBackspaceBool ch    then some nsEscBackspaceChar
  else if isNsEscHorizontalTabBool ch then some tabChar
  else if isTabBool ch               then some tabChar
  else if isNsEscLineFeedBool ch     then some lineFeedChar
  else if isNsEscVerticalTabBool ch  then some nsEscVerticalTabChar
  else if isNsEscFormFeedBool ch     then some nsEscFormFeedChar
  else if isNsEscCarriageReturnBool ch then some carriageReturnChar
  else if isNsEscEscapeBool ch       then some nsEscEscapeChar
  else if isSpaceBool ch             then some spaceChar
  else if isDoubleQuoteBool ch       then some doubleQuoteChar
  else if isNsEscSlashBool ch        then some slashChar
  else if isEscapeBool ch            then some backslashChar
  else if isNsEscNextLineBool ch     then some nsEscNextLineChar
  else if isNsEscNbspBool ch         then some nsEscNbspChar
  else if isNsEscLineSeparatorBool ch then some nsEscLineSeparatorChar
  else if isNsEscParagraphSeparatorBool ch then some nsEscParagraphSeparatorChar
  else none

/-- Process a single escape sequence. Cursor is positioned at the
    character *after* the leading `\`. Returns the decoded character
    and the post-escape cursor, or `none` for unknown / malformed
    escapes (incl. EOF after the `\`). The split between
    `simpleEscapeChar` and the hex dispatch keeps the proof obligation
    tractable: monotonicity reduces to three branches at top level
    (simple → `c.advance`, hex → `parseHexEscapeIx`, unknown → `none`)
    rather than 21 sequentially-nested `if`s. -/
def processEscapeIx {input : String} (c : IxCursor input) :
    Option (Char × IxCursor input) :=
  match c.peek? with
  | none    => none
  | some ch =>
    match simpleEscapeChar ch with
    | some decoded => some (decoded, c.advance)
    | none =>
      if isNsEsc8BitBool ch then parseHexEscapeIx c.advance 2
      else if isNsEsc16BitBool ch then parseHexEscapeIx c.advance 4
      else if isNsEsc32BitBool ch then parseHexEscapeIx c.advance 8
      else none

/-- Trim trailing space/tab from a string. -/
def trimTrailingWSIx (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile isWhiteSpaceBool).reverse)

/-! ### Layer F1 — multi-line quoted scalar folding helpers

`foldQuotedNewlinesIx` is the line-fold step shared by double- and
single-quoted scalars when they span multiple lines (§6.5 [73] /
[74]). Given a cursor sitting at a line break, it:

1. Consumes the break.
2. Counts consecutive *blank* lines (whitespace + LF runs).
3. Skips leading whitespace on the next non-blank line.

Returns the **folded replacement** (`" "` for a single break,
`"\n"*emptyCount` for two or more) and the post-fold cursor. Error
reporting (tab in indentation §6.1) is deferred to the dispatcher
in line with Step 3's neutrality. -/

/-- Inner loop: count consecutive blank lines, advancing the cursor
    past each `s-white* b-break` run. Returns `(c', emptyCount)`.
    Structural recursion on `fuel`. The `skipWhitespace c` call
    is duplicated rather than `let`-bound; binding would obstruct
    `split` in the monotonicity proof (Reflection 40 / 37).

    An all-white line (spaces *and/or* tabs) is an `l-empty` line [70];
    skip `s-white` — not just `s-space` — to recognise it as blank, else
    a `  \t`-style line is mistaken for content and its `\n` folds to a
    space (5GBF quoted / NB6Z plain; legacy fixes B1/B3). Non-blank
    lines yield the *saved* cursor, so the caller's indent decision is
    unaffected. -/
def skipBlankLinesLoopIx {input : String} (c : IxCursor input)
    (emptyCount : Nat) : Nat → IxCursor input × Nat
  | 0          => (c, emptyCount)
  | fuel + 1 =>
    -- After skipWhitespace, the cursor sits at LF / non-white / EOF.
    match (skipWhitespace c).peek? with
    | some ch =>
      if isLineBreakBool ch then
        skipBlankLinesLoopIx (consumeLineBreak (skipWhitespace c)) (emptyCount + 1) fuel
      else
        -- Hit content: yield the cursor *before* the blank-line
        -- whitespace was consumed (the caller's `skipSpaces` handles
        -- the continuation line's leading spaces explicitly).
        (c, emptyCount)
    | none    => (c, emptyCount)

/-- Fold a single quoted-scalar line break per §6.5. Cursor must be
    at the line-break character (caller has detected it). Returns
    `(folded, c')`:
    - `folded = " "` if exactly one line break with no intervening
      blank lines (`b-as-space` [70]).
    - `folded = String.ofList (List.replicate n '\n')` for `n ≥ 1`
      blank lines (`b-l-trimmed(n,c)` [69]). -/
def foldQuotedNewlinesIx {input : String} (c : IxCursor input) :
    String × IxCursor input :=
  -- Use `.1`/`.2` projections rather than `let`-destructure on the
  -- blank-line counter; the `let` would opacify proofs that try to
  -- `split` on the inner conditional (Reflection 40 / 37).
  if (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2 > 0 then
    (String.ofList
       (List.replicate
         (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2
         lineFeedChar),
     skipWhitespace
       (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1)
  else
    (String.singleton spaceChar,
     skipWhitespace
       (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1)

/-! ### Layer E2 — double-quoted scalar (§7.3.1)

`collectDoubleQuotedLoopIx` consumes the body of a double-quoted
scalar starting from *after* the opening `"`. Stops at:
- `'"'`: closing quote — return content + cursor past the quote
- `'\\'` then line break: line-continuation escape — consume LF and
  leading whitespace, emit no character
- `'\\'` otherwise: escape — recurse with `processEscapeIx`'s result
- line break: fold per `foldQuotedNewlinesIx` (Layer F1), trim
  trailing whitespace of the current content, append the folded
  string, continue
- EOF: `none`. -/

def collectDoubleQuotedLoopIx {input : String} (c : IxCursor input)
    (content : String) (protectedLen : Nat) : Nat → Option (String × IxCursor input)
  -- `protectedLen` is the number of leading characters of `content` that a line
  -- fold must NOT trim (§6.5): everything up to and including the last
  -- `ns-double-char` — a non-white char *or* an **escaped** white char
  -- (`ns-esc-tab`/`ns-esc-space`, [62]).  Only the *unescaped* `s-white*` run
  -- past `protectedLen` is layout whitespace and is dropped at a fold.  This
  -- keeps an escaped trailing tab (`"…\t\n …"`, DE56/00–03) as content while
  -- still trimming a literal trailing tab (DE56/04–05).  For any scalar without
  -- an escaped trailing white char, `protectedLen` equals the naive
  -- `trimTrailingWSIx` boundary, so behaviour is byte-identical (legacy fix B2).
  | 0          => none
  | fuel + 1 =>
    match c.peek? with
    | none       => none
    | some ch    =>
      if isDoubleQuoteBool ch then
        some (content, c.advance)
      else if isEscapeBool ch then
        -- Look at the character after the backslash to decide
        -- between line-continuation escape and normal escape.
        match c.advance.peek? with
        | some lbCh =>
          if isLineBreakBool lbCh then
            -- `\\<LF>` line-continuation: consume newline + leading WS,
            -- emit no character.
            collectDoubleQuotedLoopIx
              (skipWhitespace (consumeLineBreak c.advance)) content protectedLen fuel
          else
            match processEscapeIx c.advance with
            | some (decoded, cAfterEsc) =>
              -- An escaped char is `ns-double-char` (content, never layout), so
              -- the whole prefix through it is protected from a fold's trim.
              collectDoubleQuotedLoopIx cAfterEsc (content.push decoded)
                (content.push decoded).length fuel
            | none => none
        | none => none
      else if isLineBreakBool ch then
        -- Multi-line continuation: trim only the *unescaped* trailing white
        -- run (everything past `protectedLen`), fold the break.
        -- We use `.1`/`.2` projections rather than `let`-destructuring
        -- on the fold result; the `let` would be hoisted to `have`
        -- by elaboration and opacify the body to `split` in proofs
        -- (Reflection 40 / 37).  A folded space (`b-as-space`) is layout and
        -- stays trimmable; folded line feeds (`b-l-trimmed`) are content and
        -- are protected.
        collectDoubleQuotedLoopIx (foldQuotedNewlinesIx c).2
          (String.ofList (content.toList.take protectedLen) ++ (foldQuotedNewlinesIx c).1)
          ((String.ofList (content.toList.take protectedLen)).length
            + (if (foldQuotedNewlinesIx c).1 == " " then 0 else (foldQuotedNewlinesIx c).1.length))
          fuel
      else
        -- Unescaped space/tab is layout (`s-white`) — leave `protectedLen` so it
        -- stays trimmable at a fold; any other char advances the boundary.
        collectDoubleQuotedLoopIx c.advance (content.push ch)
          (if isWhiteSpaceBool ch then protectedLen else (content.push ch).length) fuel

/-- Scan a double-quoted scalar. Cursor must be at the opening `"`.
    Multi-line folding (§6.5) is handled by
    `collectDoubleQuotedLoopIx`'s line-break branch. -/
def scanDoubleQuotedIx {input : String} (c : IxCursor input) :
    Option (String × IxCursor input) :=
  match c.peek? with
  | some ch =>
    if isDoubleQuoteBool ch then
      collectDoubleQuotedLoopIx c.advance "" 0 input.utf8ByteSize
    else
      none
  | none => none

/-! ### Layer E3 — single-quoted scalar (§7.3.2)

`collectSingleQuotedLoopIx` consumes the body of a single-quoted
scalar starting from *after* the opening `'`. Stops at:
- `'\''` not followed by `'\''`: closing quote
- `'\''` followed by `'\''`: doubled-quote escape — emit one `'`
- line break: fold per §6.5 (multi-line continuation)
- EOF: `none`. -/

def collectSingleQuotedLoopIx {input : String} (c : IxCursor input)
    (content : String) : Nat → Option (String × IxCursor input)
  | 0          => none
  | fuel + 1 =>
    match c.peek? with
    | none      => none
    | some ch   =>
      if isSingleQuoteBool ch then
        match c.advance.peek? with
        | some next =>
          if isSingleQuoteBool next then
            collectSingleQuotedLoopIx c.advance.advance
              (content.push singleQuoteChar) fuel
          else
            some (content, c.advance)
        | none =>
          some (content, c.advance)
      else if isLineBreakBool ch then
        collectSingleQuotedLoopIx (foldQuotedNewlinesIx c).2
          (trimTrailingWSIx content ++ (foldQuotedNewlinesIx c).1) fuel
      else
        collectSingleQuotedLoopIx c.advance (content.push ch) fuel

/-- Scan a single-quoted scalar. Cursor must be at the opening `'`. -/
def scanSingleQuotedIx {input : String} (c : IxCursor input) :
    Option (String × IxCursor input) :=
  match c.peek? with
  | some ch =>
    if isSingleQuoteBool ch then
      collectSingleQuotedLoopIx c.advance "" input.utf8ByteSize
    else
      none
  | none => none

/-! ### Layer E4 — plain scalar (§7.3.3)

`collectPlainScalarLoopIx` consumes a plain scalar starting at a
character satisfying `canStartPlainScalarBool`. The scalar
terminates at end-of-input, `' #'`, `: ` / `:EOF` (block) or
`:<flow-indicator>` (flow), or a flow indicator (flow). Line breaks
trigger multi-line continuation per Layer F2 below:

- In **flow** context, continuation uses `foldQuotedNewlinesIx`
  (newline → space, blanks → newlines).
- In **block** context, continuation uses `handleBlockLineBreakIx`
  with a `contentIndent` floor and document-boundary termination.

Trailing whitespace is trimmed by the entry point `scanPlainScalarIx`. -/

/-- Helper: whether `:` at the cursor terminates a plain scalar
    (peeks one past the colon and applies the `inFlow` rule). -/
@[inline] def colonTerminatesPlain {input : String} (c : IxCursor input)
    (inFlow : Bool) : Bool :=
  match c.peekAt? 1 with
  | some n => isBlankBool n || (inFlow && isFlowIndicatorBool n)
              || !isPrintableBool n || n == '﻿'
  | none   => true

/-! ### Layer F2 — document-boundary check + multi-line plain

`atDocumentBoundaryIx` mirrors `Scanner/Document.lean` for `IxCursor`:
returns `true` exactly when the cursor sits at column 0 of a `---`
or `...` marker (followed by blank or EOF). -/

/-- True iff cursor at col 0 is at a `---` document-start marker. -/
@[inline] def atDocumentStartIx {input : String} (c : IxCursor input) : Bool :=
  c.pos.col == 0
  && (match c.peekAt? 0 with | some d => isSequenceEntryBool d | none => false)
  && (match c.peekAt? 1 with | some d => isSequenceEntryBool d | none => false)
  && (match c.peekAt? 2 with | some d => isSequenceEntryBool d | none => false)
  && match c.peekAt? 3 with
     | none   => true
     | some d => isBlankBool d

/-- True iff cursor at col 0 is at a `...` document-end marker. -/
@[inline] def atDocumentEndIx {input : String} (c : IxCursor input) : Bool :=
  c.pos.col == 0
  && (match c.peekAt? 0 with | some d => isDocEndDotBool d | none => false)
  && (match c.peekAt? 1 with | some d => isDocEndDotBool d | none => false)
  && (match c.peekAt? 2 with | some d => isDocEndDotBool d | none => false)
  && match c.peekAt? 3 with
     | none   => true
     | some d => isBlankBool d

/-- True iff cursor is at a document boundary (start or end marker). -/
@[inline] def atDocumentBoundaryIx {input : String} (c : IxCursor input) : Bool :=
  atDocumentStartIx c || atDocumentEndIx c

/-! ### Quoted-scalar strictness walker (§6.1, §8.1, §9.1.2)

The quoted recognisers above are cursor-level `Option` functions with
no error channel and no knowledge of `currentIndent`/`inFlow`, so the
legacy `collectDoubleQuotedLoop`/`collectSingleQuotedLoop` fold-time
checks were silently dropped at the cutover: document markers inside a
multiline quoted scalar (5TRB, RXY3, 9MQT/01), under-indented
continuation lines (QB6E), and tab-indented continuation lines
(DK95/01) were all accepted.

`quotedScalarErrIx` walks the same span the recogniser consumes —
identical escape/fold/blank-line stepping — and reproduces exactly the
legacy fold-time errors in legacy order (tab, then document marker,
then indent). The dispatcher's `"`/`'` arms run it before the
recogniser and throw; on `none` the recogniser proceeds unchanged. -/

/-- Walk a quoted-scalar body from *after* the opening quote,
    reporting the first legacy fold-time error. `isDouble` selects the
    `"`/`'` termination and escape rules; `startLine` is the opening
    quote's line (legacy `documentMarkerInScalar` reports it). -/
@[yaml_spec "6.5" 74 "s-flow-folded", yaml_spec "9.1.2", yaml_spec "6.1"]
def quotedScalarErrLoopIx {input : String} (c : IxCursor input)
    (isDouble : Bool) (startLine : Nat) (inFlow : Bool)
    (currentIndent : Int) : Nat → Option ScanError
  | 0 => none
  | fuel + 1 =>
    match c.peek? with
    | none => none
    | some ch =>
      if isDouble && isDoubleQuoteBool ch then none
      else if !isDouble && isSingleQuoteBool ch then
        match c.advance.peek? with
        | some next =>
          if isSingleQuoteBool next then
            quotedScalarErrLoopIx c.advance.advance isDouble startLine
              inFlow currentIndent fuel
          else none
        | none => none
      else if isDouble && isEscapeBool ch then
        match c.advance.peek? with
        | some next =>
          if isLineBreakBool next then
            -- `\<b-break>` line continuation: legacy consumes the break +
            -- `s-white*` with *no* checks (Scalar.lean:260-264).
            quotedScalarErrLoopIx (skipWhitespace (consumeLineBreak c.advance))
              isDouble startLine inFlow currentIndent fuel
          else
            -- Ordinary escape: the escaped character is never a line break,
            -- a quote terminator, or layout — skip both characters.
            quotedScalarErrLoopIx c.advance.advance isDouble startLine
              inFlow currentIndent fuel
        | none => none
      else if isLineBreakBool ch then
        -- Fold event: mirror `foldQuotedNewlines`'s checks in legacy order.
        -- 1. §6.1: tab in the indentation zone of the continuation line
        --    (checked at the post-`s-space*` cursor, before `s-white*`).
        if !inFlow
            && (((skipSpaces (skipBlankLinesLoopIx (consumeLineBreak c) 0
                  input.utf8ByteSize).1).1.pos.col : Int) ≤ currentIndent)
            && (match (skipSpaces (skipBlankLinesLoopIx (consumeLineBreak c) 0
                  input.utf8ByteSize).1).1.peek? with
                | some '\t' => true
                | _ => false) then
          some (.tabInIndentation
            (skipSpaces (skipBlankLinesLoopIx (consumeLineBreak c) 0
              input.utf8ByteSize).1).1.pos.line
            (skipSpaces (skipBlankLinesLoopIx (consumeLineBreak c) 0
              input.utf8ByteSize).1).1.pos.col)
        -- 2. §9.1.2: document marker at column 0 terminates the scalar.
        else if atDocumentStartIx (skipWhitespace
                  (skipBlankLinesLoopIx (consumeLineBreak c) 0
                    input.utf8ByteSize).1)
              || atDocumentEndIx (skipWhitespace
                  (skipBlankLinesLoopIx (consumeLineBreak c) 0
                    input.utf8ByteSize).1) then
          some (.documentMarkerInScalar
            (if isDouble then ScalarStyle.doubleQuoted else ScalarStyle.singleQuoted)
            startLine)
        -- 3. §8.1: continuation line must be indented past the block level.
        else if ((skipWhitespace (skipBlankLinesLoopIx (consumeLineBreak c) 0
                  input.utf8ByteSize).1).pos.col : Int) ≤ currentIndent then
          some (.underIndentedScalar
            (if isDouble then ScalarStyle.doubleQuoted else ScalarStyle.singleQuoted)
            (skipWhitespace (skipBlankLinesLoopIx (consumeLineBreak c) 0
              input.utf8ByteSize).1).pos.line)
        else
          quotedScalarErrLoopIx (skipWhitespace
              (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1)
            isDouble startLine inFlow currentIndent fuel
      else
        quotedScalarErrLoopIx c.advance isDouble startLine inFlow currentIndent fuel

/-- Strictness walker for a quoted scalar. Cursor must be at the
    opening quote (as in `scanDoubleQuotedIx`/`scanSingleQuotedIx`). -/
@[inline] def quotedScalarErrIx {input : String} (c : IxCursor input)
    (isDouble : Bool) (inFlow : Bool) (currentIndent : Int) :
    Option ScanError :=
  quotedScalarErrLoopIx c.advance isDouble c.pos.line inFlow currentIndent
    (input.utf8ByteSize + 1)

/-- Block-context line-break handler for plain scalars. Returns
    `none` if the continuation line is under-indented or hits a
    document boundary; otherwise `some (folded, c')` with the
    folded replacement string and the cursor at the continuation
    line's first non-whitespace character. Projections (`.1`/`.2`)
    are duplicated rather than `let`-bound — the `let` would
    obstruct `split` in the monotonicity proof (Reflection 40). -/
def handleBlockLineBreakIx {input : String} (c : IxCursor input)
    (contentIndent : Nat) : Option (String × IxCursor input) :=
  if (skipSpaces
        (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1.pos.col
       < contentIndent then
    none
  else if atDocumentBoundaryIx
            (skipSpaces
              (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1 then
    none
  else
    -- Past the required indent (tested with `skipSpaces` above, §6.1), any
    -- further spaces/tabs are `s-separate-in-line` [66] leading white space
    -- and are folded away; a leading tab is therefore stripped rather than
    -- kept as content (HS5T, UV7Q; legacy fix B3).
    if (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2 > 0 then
      some (String.ofList
              (List.replicate
                (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2
                lineFeedChar),
            skipWhitespace
              (skipSpaces
                (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1)
    else
      some (String.singleton spaceChar,
            skipWhitespace
              (skipSpaces
                (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1)

/-- Plain-scalar continuation loop. Adds a `contentIndent` parameter
    (continuation indent floor in block context) and folds line
    breaks into the content string. When folding in either context
    yields an empty continuation (no further non-terminator content),
    the loop terminates at the pre-fold cursor so the caller can
    decide what to do with the partially-collected content.

    **`#`-after-fold termination** (YAML 1.2.2 §6.7 + §7.3.3): if the
    post-fold cursor sits at `#`, the continuation line is a comment,
    so the plain scalar terminates *at the pre-fold cursor* (the line
    break is left in the input so the comment is properly scanned).
    Without this check the loop would append `' '` (from the fold)
    followed by `'#'`, producing a `' '`-then-`'#'` sequence in
    content that violates `noSpaceHashProp`. Mirrors the legacy
    `Scanner/Scalar.lean::collectPlainScalarLoop`'s explicit
    `some '#' => terminate` arm. -/
def collectPlainScalarLoopIx {input : String} (c : IxCursor input)
    (content : String) (spaces : String) (inFlow : Bool)
    (contentIndent : Nat) : Nat → String × IxCursor input
  | 0          => (content ++ spaces, c)
  | fuel + 1 =>
    match c.peek? with
    | none    => (content ++ spaces, c)
    | some ch =>
      if isCommentBool ch && spaces.length > 0 then
        (content, c)
      else if isMappingValueBool ch && colonTerminatesPlain c inFlow then
        (content, c)
      else if isMappingValueBool ch then
        collectPlainScalarLoopIx c.advance
          (content ++ spaces ++ String.singleton ch) "" inFlow contentIndent fuel
      else if inFlow && isFlowIndicatorBool ch then
        (content, c)
      else if isLineBreakBool ch then
        if inFlow then
          match (foldQuotedNewlinesIx c).2.peek? with
          | some '#' => (content, c)
          | _ =>
            collectPlainScalarLoopIx (foldQuotedNewlinesIx c).2
              (content ++ (foldQuotedNewlinesIx c).1) "" inFlow contentIndent fuel
        else
          match handleBlockLineBreakIx c contentIndent with
          | none => (content, c)
          | some (folded, cAfterFold) =>
            match cAfterFold.peek? with
            | some '#' => (content, c)
            | _ =>
              collectPlainScalarLoopIx cAfterFold (content ++ folded) "" inFlow contentIndent fuel
      else if isWhiteSpaceBool ch then
        collectPlainScalarLoopIx c.advance content (spaces.push ch) inFlow contentIndent fuel
      else if !isPlainSafeBool ch inFlow then
        (content, c)
      else
        collectPlainScalarLoopIx c.advance
          (content ++ spaces ++ String.singleton ch) "" inFlow contentIndent fuel

/-- Scan a plain scalar starting at the cursor's current character.
    The caller is responsible for enforcing the
    `canStartPlainScalarBool` precondition at dispatch.
    `contentIndent` is the continuation-line indent floor used for
    block context (caller supplies; flow context ignores it). -/
def scanPlainScalarIx {input : String} (c : IxCursor input)
    (inFlow : Bool) (contentIndent : Nat) :
    String × IxCursor input :=
  let (raw, c') := collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize
  (trimTrailingWSIx raw, c')

/-! ## Layer F3 — block scalars (§8.1, literal + folded)

Block scalars introduce the only scanner production that requires
an *enclosing* indent context (`parentIndent`). The body sits
*below* a header line of the form `('|' | '>') chomp? indent?
comment?`, with content indented strictly more than the parent.

The fold step (`foldBlockContent`) is a pure `String → String`
function over the raw line-stripped content: it operates on the
post-collection accumulator rather than on the cursor, so its
proof obligations are simple string-induction facts (deferred to
Step 5/6's content-correctness pass). Chomping (`strip` / `clip` /
`keep`) likewise acts on the raw string after collection.

The four-state fold machine `FoldState` (start / content / empty /
more) lives here as an inductive — making each case a named
constructor for pattern matching in proofs. -/

/-- States for folded block scalar newline processing (§8.1.3).
    Mirrors `Scanner/Scalar.lean::FoldState`. -/
inductive FoldState where
  | start   : FoldState
  | content : FoldState
  | empty   : FoldState
  | more    : FoldState
  deriving Repr, BEq

/-- Append `n` newlines to `acc`. Structurally recursive. -/
def appendNewlines (acc : String) : Nat → String
  | 0      => acc
  | n + 1 => appendNewlines (acc.push lineFeedChar) n

/-- Inner step of `foldBlockContent`. Walks the raw `List Char`,
    accumulating into `acc`, tracking `FoldState`, and counting
    pending newlines. The rules derive from YAML 1.2.2 [170]-[181];
    see legacy `Scanner/Scalar.lean::foldBlockContent` for the
    long-form table. -/
def foldBlockContentGo : List Char → String → FoldState → Nat → String
  -- End of input. The fold pass runs *after* chomping, so `pending` here IS the
  -- chomp result (strip → 0, clip → 1, keep → N) and must be re-emitted: a
  -- trailing run is never folded to a space, which would need a following
  -- content char. `.start` means no content char was ever seen (an all-blank
  -- body), so `acc` is empty and a clip/strip scalar over blanks stays empty.
  -- Dropping `pending` unconditionally made every folded scalar behave as `>-`
  -- (DOCS.md § Indexed-pipeline parity gap, D1).
  | [],            acc, .start, _       => acc
  | [],            acc, _,      pending => appendNewlines acc pending
  | c :: rest,     acc, st,  pending =>
    if isLineFeedBool c then
      foldBlockContentGo rest acc st (pending + 1)
    else
      match pending with
      | pending' + 1 =>
        -- More-indented [173] is `s-white`, not just `s-space`: a tab-led line
        -- keeps the breaks around it literally rather than folding them to a
        -- space (MJS9, R4YG). D2 of the same parity gap.
        let isMore := isWhiteSpaceBool c
        let newSt  := if isMore then FoldState.more else .content
        let acc'   := match st with
          | .start => appendNewlines acc (pending' + 1)
          | .content =>
            if pending' == 0 && !isMore then
              acc.push spaceChar
            else if pending' == 0 && isMore then
              acc.push lineFeedChar
            else if isMore then
              appendNewlines acc (pending' + 1)
            else
              appendNewlines acc pending'
          | .more  => appendNewlines acc (pending' + 1)
          | .empty => appendNewlines acc (pending' + 1)
        foldBlockContentGo rest (acc'.push c) newSt 0
      | 0 =>
        let newSt := match st with
          -- `s-white`, not just `s-space` (MJS9, R4YG): a tab-led *first* line
          -- is more-indented too — same rule as the pending > 0 branch above.
          | .start => if isWhiteSpaceBool c then FoldState.more else .content
          | s      => s
        foldBlockContentGo rest (acc.push c) newSt 0

/-- Fold a raw block-scalar accumulator per §8.1.3 (the folded
    style; literal style skips this pass and uses the raw string
    directly). -/
@[inline] def foldBlockContent (raw : String) : String :=
  foldBlockContentGo raw.toList "" .start 0

/-- Consume exactly `count` spaces (and not tabs) starting at the
    cursor. Returns the number of spaces actually consumed (≤
    `count`) and the post-consumption cursor. -/
def consumeExactSpacesIx {input : String} (c : IxCursor input) :
    Nat → Nat × IxCursor input
  | 0          => (0, c)
  | count' + 1 =>
    if peekIsIndentChar c then
      let (consumed, c') := consumeExactSpacesIx c.advance count'
      (consumed + 1, c')
    else
      (0, c)

/-- Consume characters until a line break or EOF, accumulating into
    `content`. Mirrors `collectLineContentLoop` from legacy. -/
def collectLineContentLoopIx {input : String} (c : IxCursor input)
    (content : String) : Nat → String × IxCursor input
  | 0          => (content, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if isLineBreakBool ch || !isPrintableBool ch || ch == '﻿' then (content, c)
      else collectLineContentLoopIx c.advance (content.push ch) fuel
    | none    => (content, c)

/-- Auto-detect block-scalar content indentation. Probes whitespace
    runs and stops at the first non-empty line whose column ≥
    `minContentIndent`. Returns the detected indent + the input
    cursor *unchanged* (probe only — actual consumption is done by
    `collectBlockScalarLoopIx`). -/
def autoDetectBlockScalarIndentLoopIx {input : String} (probe : IxCursor input)
    (maxWSCol : Nat) (minContentIndent : Nat) :
    Nat → Nat
  | 0          =>
    if maxWSCol > minContentIndent then maxWSCol else minContentIndent
  | fuel + 1 =>
    let (probeAfterSp, _) := skipSpaces probe
    match probeAfterSp.peek? with
    | some c =>
      if isLineBreakBool c then
        let maxWSCol' := if probeAfterSp.pos.col > maxWSCol then probeAfterSp.pos.col else maxWSCol
        autoDetectBlockScalarIndentLoopIx (consumeLineBreak probeAfterSp)
          maxWSCol' minContentIndent fuel
      else
        if probeAfterSp.pos.col > minContentIndent then probeAfterSp.pos.col
        else minContentIndent
    | none   =>
      -- No non-empty line.  The content indentation is the widest blank line
      -- (§8.1.1.1).  When the input ends without a final line break, the loop
      -- reaches EOF *on* that last whitespace-only line (it never took the
      -- `isLineBreakBool` branch that records `maxWSCol`), so fold its column
      -- in here — else an all-blank scalar with no trailing newline
      -- mis-detects its indent and keeps stray spaces (JEF9/02; legacy fix E).
      if max maxWSCol probeAfterSp.pos.col > minContentIndent then
        max maxWSCol probeAfterSp.pos.col
      else minContentIndent

/-- Entry point for indent auto-detection. -/
@[inline] def autoDetectBlockScalarIndentIx {input : String} (c : IxCursor input)
    (minContentIndent : Nat) : Nat :=
  autoDetectBlockScalarIndentLoopIx c 0 minContentIndent input.utf8ByteSize

/-- Inner loop of `collectBlockScalarLoopIx`. Consumes content
    line-by-line starting from a line boundary:
    1. Probe for document boundary (`---` / `...` at col 0) — stop.
    2. Consume up to `contentIndent` spaces of indent.
    3. If next char is a line break (= empty/short line) → append
       `'\n'` to the raw accumulator and recurse.
    4. If the line is *less* indented than `contentIndent` and not
       empty → stop (with the cursor *before* the indent probe).
    5. Otherwise collect content to the next line break, append
       `'\n'` if a break is found, and recurse.

    The indent-probe result and per-line collection result are
    referenced via `.1`/`.2` projections rather than `let`-destructured;
    `let`-binding would opacify `split` in the monotonicity proof
    (Reflection 40 / 37). -/
def collectBlockScalarLoopIx {input : String} (c : IxCursor input)
    (rawContent : String) (contentIndent : Nat) :
    Nat → String × IxCursor input
  | 0          => (rawContent, c)
  | fuel + 1 =>
    if c.pos.col == 0 && atDocumentBoundaryIx c then
      (rawContent, c)
    else
      match (consumeExactSpacesIx c contentIndent).2.peek? with
      | none    =>
        -- A trailing whitespace-only line at end-of-input.  EOF acts as an
        -- implicit b-break (`b-chomped-last(t)` = `… | <end-of-input>`), so a
        -- fully-indented blank final line still contributes its `\n` for the
        -- chomp to keep/clip (JEF9/02; legacy fix E).  Guard on consumed > 0
        -- so a genuinely empty body (`|` immediately at EOF) stays empty.
        -- The `\n` goes into the *content* string only; the cursor stays put.
        ((if (consumeExactSpacesIx c contentIndent).1 > 0
          then rawContent.push lineFeedChar else rawContent),
         (consumeExactSpacesIx c contentIndent).2)
      | some ch =>
        if isLineBreakBool ch then
          collectBlockScalarLoopIx
            (consumeLineBreak (consumeExactSpacesIx c contentIndent).2)
            (rawContent.push lineFeedChar) contentIndent fuel
        else if (consumeExactSpacesIx c contentIndent).1 < contentIndent then
          (rawContent, c)
        else
          match
              (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                input.utf8ByteSize).2.peek? with
          | some ch' =>
            if isLineBreakBool ch' then
              collectBlockScalarLoopIx
                (consumeLineBreak
                  (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                    input.utf8ByteSize).2)
                ((rawContent ++
                  (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                    input.utf8ByteSize).1).push lineFeedChar)
                contentIndent fuel
            else
              -- Line stopped at a non-printable/BOM char (not nb-char [27]):
              -- end the block scalar here; dispatch rejects the char.
              (rawContent ++
                (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                  input.utf8ByteSize).1,
               (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                  input.utf8ByteSize).2)
          | none   =>
            -- Line terminated by end-of-input.  Add the implicit final b-break
            -- only for a trailing *whitespace-only* line (e.g. `   ` beyond the
            -- indent → a lone space, as in L24T/01; legacy fix E): a real
            -- content line at EOF takes the `<end-of-input>` alternative of
            -- `b-chomped-last(t)` [165] and gains no phantom `\n` (matches
            -- libfyaml/pyyaml/ruamel and keeps dumper round-trips faithful).
            ((if ((collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                    input.utf8ByteSize).1).all isWhiteSpaceBool
              then ((rawContent ++
                    (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                      input.utf8ByteSize).1).push lineFeedChar)
              else (rawContent ++
                    (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                      input.utf8ByteSize).1)),
             (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                input.utf8ByteSize).2)

/-- Parse the header characters that may follow `|` or `>`:
    chomping indicator (`-` strip / `+` keep) and an explicit
    indentation indicator (digit `1..9`). Either order is permitted.
    The fuel is the maximum number of header characters (2 is the
    spec maximum: one chomp + one indent). -/
def parseBlockHeaderLoopIx {input : String} (c : IxCursor input)
    (chomp : ChompStyle) (explicitOffset : Option Nat) :
    Nat → ChompStyle × Option Nat × IxCursor input
  | 0          => (chomp, explicitOffset, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if isSequenceEntryBool ch then
        parseBlockHeaderLoopIx c.advance .strip explicitOffset fuel
      else if isChompKeepBool ch then
        parseBlockHeaderLoopIx c.advance .keep explicitOffset fuel
      else if ch.isDigit && !isNsEscNullBool ch then
        -- Digit value = `ch - '0'`. NOT `nsEscNullChar`, which is `'\x00'` — the
        -- *result* of the `\0` escape [42], where `isNsEscNullBool` on the line
        -- above is its *selector* `'0'`. Subtracting the result instead of the
        -- selector made `|2` mean an indentation indicator of 50, so the body
        -- collected nothing and the content line was re-scanned as a bare
        -- document (DOCS.md § Indexed-pipeline parity gap, D4).
        parseBlockHeaderLoopIx c.advance chomp
          (some (ch.toNat - '0'.toNat)) fuel
      else
        (chomp, explicitOffset, c)
    | none => (chomp, explicitOffset, c)

/-- Strip trailing `\n` characters from `s`. -/
def stripTrailingNewlines (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile isLineFeedBool).reverse)

/-- Apply chomping per §8.1.1: `strip` removes every trailing `\n`,
    `clip` keeps at most one trailing `\n`, `keep` preserves them. -/
def applyChomp (chomp : ChompStyle) (raw : String) : String :=
  match chomp with
  | .strip => stripTrailingNewlines raw
  | .clip  =>
    let stripped := stripTrailingNewlines raw
    let nl      := String.singleton lineFeedChar
    if raw.endsWith nl then stripped ++ nl else stripped
  | .keep  => raw

/-- Helper: the post-header cursor for `scanBlockScalarIx`. Built
    as a chain `skipWhitespace ∘ (optional comment) ∘ consumeLineBreak`
    on top of `parseBlockHeaderLoopIx`'s output. Named so the proof
    can refer to it without rebuilding the chain each time. -/
def blockHeaderToBodyIx {input : String} (c : IxCursor input) : IxCursor input :=
  consumeLineBreak
    (if (match (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).peek?
          with | some d => isCommentBool d | none => false) then
       skipCommentText
         (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).advance
     else
       skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2)

/-- §6.7 [76] `b-comment`: does the block-scalar header line end in a
    line break or EOF?  Same header/whitespace/comment chain as
    `blockHeaderToBodyIx`, stopping before its `consumeLineBreak`.
    Legacy `scanBlockScalarConsumeNewline` throws `expectedNewline`
    here; the cursor-level recogniser has no error channel, so the
    dispatcher checks this predicate and throws.  Without it,
    `--- |10`'s dangling `0` scans as content (2G84/01). -/
def blockScalarHeaderEndsLineIx {input : String} (c : IxCursor input) : Bool :=
  -- §6.6 [75]: the trailing comment needs preceding `s-white` — a `#`
  -- glued to the header (`>#c`, X4QW) is not a comment, so the header
  -- does not end in `b-comment` and the dispatcher must throw. The
  -- whitespace-consumed test (col moved) mirrors legacy
  -- `skipHeaderComment`'s `peekBack?` whitespace requirement.
  match (if (match (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).peek?
              with | some d => isCommentBool d | none => false)
            && (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).pos.col
               != (parseBlockHeaderLoopIx c.advance .clip none 2).2.2.pos.col then
           skipCommentText
             (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).advance
         else
           skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).peek? with
  | some d => isLineBreakBool d
  | none   => true

/-! ### Block-scalar auto-detect strictness walker (§6.1, §8.1.3)

Legacy `autoDetectBlockScalarIndentLoop` threads an `Option ScanError`
alongside the detected indent: a tab inside the indentation zone of
the probe (`\t` before content indent is known — Y79Y/000) is a §6.1
violation, and a whitespace-only line wider than the eventually
detected content indent (5LLU, S98Z, W9L4) violates §8.1.3.
`autoDetectBlockScalarIndentLoopIx` above returns only the indent, so
these were silently dropped at the cutover.

`blockScalarBodyErrIx` reruns the probe from the post-header cursor
and reproduces exactly the legacy error outputs; the dispatcher's
`|`/`>` arm runs it after the §6.7 header check and throws. Explicit
indentation indicators skip auto-detection in legacy, so the walker
returns `none` for them too. -/

/-- Probe mirror of legacy `autoDetectBlockScalarIndentLoop`'s error
    channel: reports a tab in the indentation zone, or a
    whitespace-only line wider than the detected content indent. -/
@[yaml_spec "8.1" 163 "c-indentation-indicator", yaml_spec "6.1"]
def blockScalarAutoIndentErrLoopIx {input : String} (probe : IxCursor input)
    (maxWSCol maxWSLine : Nat) (minContentIndent : Nat) :
    Nat → Option ScanError
  | 0 => none
  | fuel + 1 =>
    match (skipSpaces probe).1.peek? with
    | some ch =>
      if ch == '\t' && (skipSpaces probe).1.pos.col < minContentIndent then
        some (.tabInIndentation (skipSpaces probe).1.pos.line
          (skipSpaces probe).1.pos.col)
      else if isLineBreakBool ch then
        blockScalarAutoIndentErrLoopIx (consumeLineBreak (skipSpaces probe).1)
          (if (skipSpaces probe).1.pos.col > maxWSCol
           then (skipSpaces probe).1.pos.col else maxWSCol)
          (if (skipSpaces probe).1.pos.col > maxWSCol
           then (skipSpaces probe).1.pos.line else maxWSLine)
          minContentIndent fuel
      else
        if maxWSCol > max minContentIndent (skipSpaces probe).1.pos.col then
          some (.blockScalarIndentMismatch maxWSLine maxWSCol)
        else none
    | none => none

/-- Strictness walker for a block-scalar body. Cursor must be at the
    introducer `|`/`>` (as in `scanBlockScalarIx`); `indentFloor` is
    the same minimum content indent the dispatcher passes there. -/
def blockScalarBodyErrIx {input : String} (c : IxCursor input)
    (indentFloor : Nat) : Option ScanError :=
  match (parseBlockHeaderLoopIx c.advance .clip none 2).2.1 with
  | some _ => none
  | none   =>
    blockScalarAutoIndentErrLoopIx (blockHeaderToBodyIx c) 0 0 indentFloor
      (input.utf8ByteSize + 1)

/-- Scan a block scalar. The cursor must be at the introducer `|`
    (literal) or `>` (folded). Returns `(content, style, c')`
    where `style` is `.literal` or `.folded` and `c'` is the cursor
    after the block-scalar content.

    `indentFloor` is the *minimum content indent*,
    `(max 0 (currentIndent + 1)).toNat` at the dispatch site — NOT the
    raw parent column.  Passing the clamped parent column
    `(max 0 currentIndent).toNat` loses the top-level `currentIndent
    = -1` case: a zero-indented block scalar after `---` (DK3J, FP8R)
    then mis-detects its content as under-indented and scans empty.
    Legacy keeps the `Int` and computes `max 0 (parentIndent + 1)` /
    `max 0 (parentIndent + m)` inside `scanBlockScalarBody`; the
    indexed twin pre-computes the floor so the parameter stays `Nat`:
    auto-detect uses `indentFloor` directly, an explicit indicator `m`
    uses `indentFloor + m - 1` (= `max 0 (currentIndent + m)` for
    `m ≥ 1`, both signs of `currentIndent`).

    The intermediate cursors are not `let`-bound; they reference
    `blockHeaderToBodyIx c` and `parseBlockHeaderLoopIx`'s output
    via projection — the `let` would opacify `split` in the
    monotonicity proof (Reflection 40 / 37). -/
def scanBlockScalarIx {input : String} (c : IxCursor input)
    (indentFloor : Nat) :
    Option (String × ScalarStyle × IxCursor input) :=
  match c.peek? with
  | some ch =>
    if isLiteralBool ch || isFoldedBool ch then
      some
        ( (if isLiteralBool ch then
             applyChomp (parseBlockHeaderLoopIx c.advance .clip none 2).1
               (collectBlockScalarLoopIx (blockHeaderToBodyIx c) ""
                 (match (parseBlockHeaderLoopIx c.advance .clip none 2).2.1 with
                   | some m => indentFloor + m - 1
                   | none   =>
                     autoDetectBlockScalarIndentIx (blockHeaderToBodyIx c)
                       indentFloor)
                 input.utf8ByteSize).1
           else
             foldBlockContent
               (applyChomp (parseBlockHeaderLoopIx c.advance .clip none 2).1
                 (collectBlockScalarLoopIx (blockHeaderToBodyIx c) ""
                   (match (parseBlockHeaderLoopIx c.advance .clip none 2).2.1 with
                     | some m => indentFloor + m - 1
                     | none   =>
                       autoDetectBlockScalarIndentIx (blockHeaderToBodyIx c)
                         indentFloor)
                   input.utf8ByteSize).1))
        , (if isLiteralBool ch then ScalarStyle.literal else ScalarStyle.folded)
        , (collectBlockScalarLoopIx (blockHeaderToBodyIx c) ""
            (match (parseBlockHeaderLoopIx c.advance .clip none 2).2.1 with
              | some m => indentFloor + m - 1
              | none   =>
                autoDetectBlockScalarIndentIx (blockHeaderToBodyIx c)
                  indentFloor)
            input.utf8ByteSize).2 )
    else
      none
  | none   => none

end L4YAML.Scanner.Indexed
