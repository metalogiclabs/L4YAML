/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State

/-!
# Scanner — Token-Stream Queries

Read-only queries over the emitted token array: the last/penultimate REAL
(non-placeholder) token, the trailing `[96] c-ns-properties` run, and the
same-line structural predicates the indicator scanners consult (item 48
moved these out of `Scanner.lean` so `SimpleKey.lean` can read them — same
`L4YAML.Scanner` namespace, so every downstream reference and proof is
unchanged).
-/

namespace L4YAML.Scanner

open L4YAML

/-- Find the last non-placeholder token value, skipping reservation slots.
    Returns `none` if there are no real tokens. -/
def lastRealTokenVal? (tokens : Array (Positioned YamlToken)) : Option YamlToken :=
  if tokens.size > 0 then
    let lastIdx := tokens.size - 1
    let tok1 := tokens[lastIdx]!.val
    if tok1 == .placeholder && lastIdx > 0 then
      let tok2 := tokens[lastIdx - 1]!.val
      if tok2 == .placeholder && lastIdx > 1 then
        some (tokens[lastIdx - 2]!.val)
      else some tok2
    else some tok1
  else none

/-- The index of the token `lastRealTokenVal?` reads, or `none` when there is no
    real token.  Split out so `penultRealTokenVal?` can restart the same
    placeholder skip from strictly before it. -/
def lastRealTokenIdx? (tokens : Array (Positioned YamlToken)) : Option Nat :=
  if tokens.size > 0 then
    let lastIdx := tokens.size - 1
    if tokens[lastIdx]!.val == .placeholder && lastIdx > 0 then
      if tokens[lastIdx - 1]!.val == .placeholder && lastIdx > 1 then
        some (lastIdx - 2)
      else some (lastIdx - 1)
    else some lastIdx
  else none

/-- The real token *before* the one `lastRealTokenVal?` reads, skipping
    placeholder reservation slots the same way.  `none` if there is no second
    real token. -/
def penultRealTokenVal? (tokens : Array (Positioned YamlToken)) : Option YamlToken :=
  match lastRealTokenIdx? tokens with
  | some i => lastRealTokenVal? (tokens.extract 0 i)
  | none => none

/-- `lastRealTokenVal?`'s positioned twin: the whole token, not just its value.
    Added by item 9k, whose test is about *where* the token sits. -/
def lastRealToken? (tokens : Array (Positioned YamlToken)) :
    Option (Positioned YamlToken) :=
  if tokens.size > 0 then
    let lastIdx := tokens.size - 1
    let tok1 := tokens[lastIdx]!
    if tok1.val == .placeholder && lastIdx > 0 then
      let tok2 := tokens[lastIdx - 1]!
      if tok2.val == .placeholder && lastIdx > 1 then
        some tokens[lastIdx - 2]!
      else some tok2
    else some tok1
  else none

/-- `penultRealTokenVal?`'s positioned twin. -/
def penultRealToken? (tokens : Array (Positioned YamlToken)) :
    Option (Positioned YamlToken) :=
  match lastRealTokenIdx? tokens with
  | some i => lastRealToken? (tokens.extract 0 i)
  | none => none

/-- The trailing run of node-property tokens, most recent first.

    §6.9 [96] `c-ns-properties` admits at most one anchor and one tag, so a
    *legal* run is at most two tokens long; the run is therefore read with two
    lookbacks and capped there.  A third property is rejected by the same test
    applied at the second — `&a !t &b` fails because the run `[!t, &a]` visible
    at `&b` already carries an anchor. -/
def trailingPropertyRun (tokens : Array (Positioned YamlToken)) : List YamlToken :=
  match lastRealTokenVal? tokens with
  | some t1 =>
    if t1.isNodeProperty then
      match penultRealTokenVal? tokens with
      | some t2 => if t2.isNodeProperty then [t1, t2] else [t1]
      | none => [t1]
    else []
  | none => []

/-! ### The trailing node run (§9.2's dangling node) -/

/-- The previous REAL token's index, strictly before `i`, skipping the
    reservation placeholders `saveSimpleKey` pushes.

    `lastRealTokenVal?` above skips at most two, which is exactly one save's
    reservation and is all its callers need.  This walk is unbounded because a
    RUN's start can sit behind an arbitrary number of them, and it is
    structurally recursive on `i`, so it is total. -/
def prevRealIdx? (tokens : Array (Positioned YamlToken)) : Nat → Option Nat
  | 0 => none
  | i + 1 => if tokens[i]!.val == .placeholder then prevRealIdx? tokens i else some i

/-- The trailing `[96]* (scalar|alias)?` run at the end of the token array: the
    index it STARTS at, paired with the index of the real token before it.
    `none` when the array does not end in a node run at all.

    §6.9 admits at most one anchor and one tag, so the property walk-back is
    capped at two — the same cap, for the same reason, as
    `trailingPropertyRun`'s two lookbacks. -/
def trailingNodeRun? (tokens : Array (Positioned YamlToken)) :
    Option (Nat × Option Nat) :=
  match prevRealIdx? tokens tokens.size with
  | none => none
  | some i =>
    let t := tokens[i]!.val
    if t.isNodeProperty then
      -- A property run with no body of its own (`&p`, `&p !t`).
      let st := match prevRealIdx? tokens i with
                | some j => if tokens[j]!.val.isNodeProperty then j else i
                | none => i
      some (st, prevRealIdx? tokens st)
    else if t.isNodeBody then
      let st := match prevRealIdx? tokens i with
                | some j =>
                  if tokens[j]!.val.isNodeProperty then
                    match prevRealIdx? tokens j with
                    | some k => if tokens[k]!.val.isNodeProperty then k else j
                    | none => j
                  else i
                | none => i
      some (st, prevRealIdx? tokens st)
    else none

/-! ### When token adjacency means "same property run" (items 9e and 9k)

    Token adjacency means "same node" only when nothing that emits no token can
    intervene.  Two contexts guarantee that, and the three tests below are the
    disjunction of them.

    **Inside a flow collection** (item 9e).  `[137]`/`[140]` admit
    `ns-flow-node` only, so no block collection can open between two tokens, and
    two adjacent property tokens necessarily belong to one node — at any
    distance, across as many lines as the collection spans.

    **On one line** (item 9k).  In block context the flow argument fails: a
    block collection opens without a token of its own, so adjacent property
    tokens can belong to different nodes.

    ```yaml
    &mapping
    &key [ &item a, b, c ]: value    # 26DV / suite: &mapping is on the MAPPING
    top3: &node3
      *alias1 : scalar3              # &node3 is on the nested mapping, not on *alias1
    ```

    Both are valid, and both put an `anchor` directly before an `anchor`/`alias`
    in the token stream — so the tests may not be ungated.  But both also put
    the two tokens on DIFFERENT lines, and that is not an accident: `[200]
    s-l+block-collection(n,c)` reads its properties then `s-l-comments`, whose
    `[77] s-b-comment` is `b-non-content` or end of input.  A block collection's
    properties are therefore *always* separated from its content by a break, so
    a property token and a property token on the SAME line cannot be split by a
    block opening.

    Same-line adjacency is a sound approximation, not an exact one: a run
    already broken across lines is not read (`&a⏎!t &b c` keeps only `!t`), so
    the block-context tests under-reject rather than over-reject.  The flow
    disjunct keeps the unrestricted run, which is why widening costs the
    in-flow case nothing. -/

/-- `trailingPropertyRun`, truncated at a line change: the same two-token
    lookback, keeping only tokens that start on `line`.  This is the run the
    BLOCK-context half of the three tests below reads. -/
@[yaml_spec "6.9" 96 "c-ns-properties",
  yaml_spec "8.2.3" 200 "s-l+block-collection(n,c)",
  yaml_spec "6.6" 77 "s-b-comment"]
def trailingPropertyRunOnLine (tokens : Array (Positioned YamlToken)) (line : Nat) :
    List YamlToken :=
  match lastRealToken? tokens with
  | some t1 =>
    if t1.val.isNodeProperty && t1.pos.line == line then
      match penultRealToken? tokens with
      | some t2 =>
        if t2.val.isNodeProperty && t2.pos.line == line then [t1.val, t2.val] else [t1.val]
      | none => [t1.val]
    else []
  | none => []

/-- Is the last real token a node property that starts on `line`? -/
def lastTokenIsNodePropertyOnLine (tokens : Array (Positioned YamlToken)) (line : Nat) :
    Bool :=
  match lastRealToken? tokens with
  | some t => t.val.isNodeProperty && t.pos.line == line
  | none => false

/-- Walk this line's tokens backwards looking for a `---` (item 48): the
    marker's line admits `s-l-comments` or one same-line node and nothing
    else, so a block indicator or value indicator dispatched with a `---`
    still on the line has no derivation.  Bounded by the line: the walk
    stops at the first token of an earlier line. -/
def docStartOnLineLoop (tokens : Array (Positioned YamlToken)) (i : Nat)
    (line : Nat) : Bool :=
  match i with
  | 0 => false
  | j + 1 =>
    let t := tokens[j]!
    if t.val == .documentStart && t.pos.line == line then true
    else if t.pos.line == line || t.val == .placeholder then
      docStartOnLineLoop tokens j line
    else false

@[yaml_spec "9.1.1" 203 "c-directives-end"]
def docStartOnLine (tokens : Array (Positioned YamlToken)) (line : Nat) : Bool :=
  docStartOnLineLoop tokens tokens.size line

end L4YAML.Scanner
