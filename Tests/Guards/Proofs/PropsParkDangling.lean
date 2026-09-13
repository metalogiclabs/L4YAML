import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The property lane's reading, and the half of it that scans clean (DOCS item 158)

Item 156 derived §9.2's dangling reading at the producer for a content dispatch
off `&`/`!`; item 157 built the consumer face for `pendingContent` and left the
property lane as the gate's named residue, recording that "the lane IS
refutable and the scanner already refuses every shape in it".

This item lands the producer half for the property arm and measures the second
claim, which is **half true**:

* `dispatchContent_tokens_push_prop` — a `&` pushes one `.anchor` and a `!` one
  `.tag`, at the dispatch's own `currentPos`;
* `dispatchContent_tokens_push_node` — with the body arm beside it, the
  dispatcher's whole token census is ONE statement: exactly one node token, at
  its own position;
* `trailingNodeRun?_push_prop` / `_push_node` — a property pushed on top starts
  a trailing run of one, exactly as a body does;
* so `danglingPark_of_dispatch` and its two spent forms lose their `c ≠ '&'`
  and `c ≠ '!'` premises, and `ContentRouteGate`'s left disjunct loses them
  with it.

What the measurement adds is the lane's SPLIT.  A property run with a BLOCK
body is refused by the scanner at the run's start, which is the property (§2).
A property run whose body is a FLOW collection is not refused at all (§3): the
collection's close ends the trailing run, so §9.2's end-of-input check reads
`none`, and §8.1's floor measures the BRACKET's column, which the run has moved
right.  `a: 1⏎&p [b]` scans clean and the parser refuses it — so the props park
really does owe an unconditional route, and the face item 157 named cannot
simply be added.

§4 measures what the field would cost and where it stops. -/

namespace L4YAML.Tests.Guards.PropsParkDangling

open L4YAML L4YAML.Scanner L4YAML.Proofs.StreamAccum

private def posStr : Option YamlPos → String
  | some p => s!"{p.line},{p.col}"
  | none => "none"

private def kindOf (t : YamlToken) : String :=
  if t.isNodeProperty then "prop" else if t.isNodeBody then "body" else "other"

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

/-- The trailing node run at the state `n` steps in — the kind of token it
    starts with, where that token sits, whether its predecessor offers the run
    a slot — and the reading `danglingNodePos?` takes off it. -/
private def parkAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    let run := match trailingNodeRun? s.tokens with
      | none => "run=none"
      | some (st, pred) =>
        let sp := s.tokens[st]!.pos
        let pk := match pred with
          | some j => if s.tokens[j]!.val.offersNodeSlot then "slot" else "no-slot"
          | none => "no-pred"
        s!"run={kindOf s.tokens[st]!.val}@{sp.line},{sp.col} pred={pk}"
    s!"{run} park={posStr (danglingNodePos? s)}"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

/-! ## §1  The dispatcher's token census, in one statement

Off `&`/`!` the content dispatch pushes a node BODY (item 156); at `&`/`!` it
pushes a `[96] c-ns-properties` half.  There is no third arm, so the census is
one statement — and it is what takes the character premises off everything
below. -/

example {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    ∃ t : YamlToken, (t.isNodeBody = true ∨ t.isNodeProperty = true) ∧
      s'.tokens = s.tokens.push { pos := s.currentPos, val := t } :=
  dispatchContent_tokens_push_node hok

example {s s' : ScannerState}
    (hok : scanNextToken_dispatchContent s '&' = .ok s') :
    ∃ t : YamlToken, t.isNodeProperty = true ∧
      s'.tokens = s.tokens.push { pos := s.currentPos, val := t } :=
  dispatchContent_tokens_push_prop hok (Or.inl rfl)

example {s s' : ScannerState}
    (hok : scanNextToken_dispatchContent s '!' = .ok s') :
    ∃ t : YamlToken, t.isNodeProperty = true ∧
      s'.tokens = s.tokens.push { pos := s.currentPos, val := t } :=
  dispatchContent_tokens_push_prop hok (Or.inr rfl)

-- …and the run it starts is a run of ONE, with the array's own last real slot
-- as its predecessor — the property arm of `trailingNodeRun?`, which item 157
-- named as the missing piece.
example {ts : Array (Positioned YamlToken)} {p : Positioned YamlToken} {i : Nat}
    (hb : p.val.isNodeProperty = true)
    (hprev : prevRealIdx? ts ts.size = some i)
    (hprop : ts[i]!.val.isNodeProperty = false) :
    trailingNodeRun? (ts.push p) = some (ts.size, some i) :=
  trailingNodeRun?_push_prop hb hprev hprop

/-! ## §2  The refutation, with no case on the character

`danglingPark_of_dispatch` now reads the same at every content character, so
§9.2's two checks refuse a property park exactly as they refuse a scalar
one. -/

example {s s' : ScannerState}
    (hok : scanNextToken_dispatchContent s '&' = .ok s')
    (h_noflow : s'.inFlow = false)
    (h_tail : CompletedTail s)
    (h_op : (s.indents.any fun e => e.column == (s.col : Int)) = true) :
    danglingNodePos? s' = some s.currentPos :=
  danglingPark_of_dispatch hok h_noflow (CompletedTail.danglingPred h_tail) h_op

example {s s' s_land : ScannerState}
    (hok : scanNextToken_dispatchContent s '&' = .ok s')
    (h_noflow : s'.inFlow = false)
    (h_tail : CompletedTail s)
    (h_op : (s.indents.any fun e => e.column == (s.col : Int)) = true)
    (h_dn : scanNextToken_checkDanglingNode s' s_land = .ok ())
    (h_ska : s_land.simpleKeyAllowed = true) : False :=
  danglingPark_refutes_landing hok h_noflow h_tail h_op h_dn h_ska

example {s s' : ScannerState}
    (hok : scanNextToken_dispatchContent s '!' = .ok s')
    (h_noflow : s'.inFlow = false)
    (h_tail : CompletedTail s)
    (h_op : (s.indents.any fun e => e.column == (s.col : Int)) = true)
    (h_dn : scanLoop_checkDanglingNode s' = .ok ()) : False :=
  danglingPark_refutes_eof hok h_noflow h_tail h_op h_dn

-- Item 157's four witnesses, refused at the RUN's start — and the run's start
-- is the PROPERTY, which is what the lemmas above say and what the scanner
-- reports.
#guard ["a: 1\n&p b\n", "k:\n  a: 1\n  &p b\n", "- a\n&p b\n", "a: 1\n!!str b\n"].map scanOk
  == ["SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 2",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"]

#guard [("a: 1\n&p b\n", 4), ("k:\n  a: 1\n  &p b\n", 6), ("- a\n&p b\n", 3),
        ("a: 1\n!!str b\n", 4)].map (fun (p : String × Nat) => parkAt p.1 p.2)
  == ["run=prop@1,0 pred=no-slot park=1,0",
      "run=prop@2,2 pred=no-slot park=2,2",
      "run=prop@1,0 pred=no-slot park=1,0",
      "run=prop@1,0 pred=no-slot park=1,0"]

/-! ## §3  The half that scans clean

A property run whose body is a FLOW collection is not refused by the scanner at
all.  Two mechanisms miss it, and they miss it for different reasons:

* §9.2's end-of-input check reads `trailingNodeRun?`, and a `]` or `}` is
  neither a body nor a property — so once the collection closes, the array ends
  in no node run and the reading is `none`;
* §8.1's floor, which refuses the same shape WITHOUT a run (`a: 1⏎[b]` is
  `underIndentedFlowContent`), measures the BRACKET's column — and the property
  run has moved it right.

The parser refuses all four anyway, at the run's start, which is where the
scanner would have reported. -/

#guard ["a: 1\n&p [b]\n", "a: 1\n&p {b: 1}\n", "a: 1\n!t [b]\n", "- a\n&p [b]\n",
        "a: 1\n[b]\n"].map scanOk
  == ["SCAN-OK", "SCAN-OK", "SCAN-OK", "SCAN-OK",
      "SCAN-ERR L4YAML.ScanError.underIndentedFlowContent 1 0"]

#guard ["a: 1\n&p [b]\n", "a: 1\n&p {b: 1}\n", "a: 1\n!t [b]\n", "- a\n&p [b]\n",
        "a: 1\n[b]\n"].map parseOk
  == ["PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.underIndentedFlowContent 1 0"]

-- `a: 1⏎&p [b]` step by step: the props park at step 4 DOES read the dangling
-- run, and the very next step — the `[` — ends it.  Nothing downstream can see
-- it again.
#guard (List.range 8).map (fun n => parkAt "a: 1\n&p [b]\n" n)
  == ["run=none park=none",
      "run=body@0,0 pred=no-slot park=none",
      "run=none park=none",
      "run=body@0,3 pred=slot park=none",
      "run=prop@1,0 pred=no-slot park=1,0",
      "run=none park=none",
      "run=body@1,4 pred=no-slot park=none",
      "run=none park=none"]

/-! ## §4  What the field would cost, and where it stops

`pendingProps.h_route` is the run's stream closure, and it is spent in three
places.  Two of them could pay a `danglingNodePos? sc = none` premise and the
third cannot:

| consumer | what it has |
|---|---|
| `PendingNode.close_with_ssl` | `h_nd`, item 157's own parameter — free |
| `accum_content_pending` (the run's extension and its ride into content) | the NEXT park's premise, one push later |
| `accum_flow_open_depth0` (the ride into a flow collection) | nothing: §3's park is live there |

The flow consumer is §3's own input read from the accumulation's side.  It can
be paid only by giving that arm the opaque resume instead of the props route,
which is a different item's decision, not a lemma.

The second consumer has its own obstacle, and it is a fact about the token
array rather than about the grammar.  A property run's reading transports
across a BODY push — the walk-back reaches the same run start — but not across
a PROPERTY push, because the start moves: -/

#guard scanOk "&a\n!t &b x\n" == "SCAN-OK"
#guard parseOk "&a\n!t &b x\n" == "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 3"

-- `&a⏎!t &b x`: at step 2 the token run starts at the `&a` on line 0, because
-- `trailingNodeRun?` walks back over properties and has no line filter; at step
-- 3 the third property pushes the start down to the `!t` on line 1.  So the
-- reading at the park and the reading one push later are not the same reading,
-- and a premise stated as `danglingNodePos? sc = none` does not relay through
-- the run's own extension.
#guard (List.range 5).map (fun n => parkAt "&a\n!t &b x\n" n)
  == ["run=none park=none",
      "run=prop@0,0 pred=no-slot park=none",
      "run=prop@0,0 pred=no-slot park=none",
      "run=prop@1,0 pred=no-slot park=none",
      "run=prop@1,0 pred=no-slot park=none"]

-- The same three properties on ONE line are scanner-refused — §6.9 admits one
-- anchor and one tag — so the shape above exists only because the run crossed a
-- break, and `trailingPropertyRunOnLine`'s line filter is what lets it.
#guard scanOk "&a !t &b x\n" == "SCAN-ERR L4YAML.ScanError.invalidNodeProperties '&' 0 6"

/-! ## §5  What the next item needs

The gate's right disjunct is unchanged in size and sharper in name: what is
missing at `&`/`!` is the park's own FIELD, not a refutation.  Landing it needs
three things this item has measured rather than assumed:

1. a premise shape that relays through a property push — `danglingNodePos? sc =
   none` does not, by §4's witness;
2. `pendingBlockContent.h_closable` guarded as `pendingContent.h_closable`
   already is, since the run's ride into an ENTRY parks there — its only
   consumer is `close_with_ssl`, which carries `h_nd` already;
3. a decision about the flow ride: the opaque resume (`scannerDrop`, which
   `pendingFlow` already takes) in place of the props route whenever the park
   is dangling — or §3's hole closed in the scanner, which would make the two
   refusals agree at the position they already agree on. -/

end L4YAML.Tests.Guards.PropsParkDangling
