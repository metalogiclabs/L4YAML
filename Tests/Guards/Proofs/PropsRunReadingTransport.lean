import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The `[96]` run's reading, transported — and the gate's one unpayable site
    (DOCS item 160)

Item 159 left the property lane in two pieces and named the first as "a premise
shape for `pendingProps.h_route` that relays through a PROPERTY push".  This
file is that piece, run: the relay is built, and the gate it was meant to buy
is measured to the SITE.

**What the gate would be.**  `pendingProps.h_route` is the run's stream
closure.  Guarding it with `danglingNodePos? sc = none` — the face
`pendingContent` has carried since item 157 and `pendingBlockContent` since item
159 — is what would let `ContentRouteGate` lose its right disjunct, and with it
the last CHARACTER residue in the content landing's bare-document route.

**What it costs, exactly.**  Guarding the field and building the module names
**23** spend sites, and they fall in four classes:

| class | sites | pays with |
|---|---|---|
| the park's close (`PendingNode.close_with_ssl`) | 1 | `h_nd`, its own parameter |
| the landing producers (`content_dispatch_routed` and its four siblings) | 10 | the gate itself, once the right disjunct is gone |
| the run's rides — its extension and its content (`accum_content_pending`) | 11 | the RELAY, below |
| the run's ride into a FLOW COLLECTION (`accum_flow_open_depth0`) | 1 | **nothing** |

**The relay, in three pushes.**  A park's own last token is a `[96]` property,
so every push onto it is the case item 158's push lemmas exclude, and the three
that can happen do three different things (§1).  A BODY preserves the reading; a
PROPERTY moves its start; a flow COLLECTION preserves it, but only through its
close, and only by item 159's third arm.

**The site that cannot pay** is the flow ride, and §3 is why: it is not a park
whose reading could be read differently, it is a closure with no scanner state
in it at all.  `FlowBaseRoutes.value` is built at the OPEN and spent at the
CLOSE, and the reading only becomes available at the close.  So the gate belongs
on that field, and what it needs is the walk's own answer — which is the flow
stack's to supply. -/

namespace L4YAML.Tests.Guards.PropsRunReadingTransport

open L4YAML L4YAML.Scanner L4YAML.Proofs.StreamAccum

private def posStr : Option YamlPos → String
  | some p => s!"{p.line},{p.col}"
  | none => "none"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

private def stepTo (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | k + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepTo s' k
    | _ => none

/-- The run reading after `n` steps: what kind of token the trailing run starts
    with, where it sits, and the verdict `danglingNodePos?` takes off it. -/
private def stepAt (input : String) (n : Nat) : String :=
  match stepTo ((ScannerState.mk' input).emit .streamStart) n with
  | none => "—"
  | some s =>
    match trailingNodeRun? s.tokens with
    | none => s!"run=none park={posStr (danglingNodePos? s)}"
    | some (st, _) =>
      let t := s.tokens[st]!
      let k := if t.val.isNodeProperty then "prop"
               else if t.val.isNodeBody then "body"
               else if t.val.isFlowOpen then "open"
               else if t.val.isFlowClose then "close" else "other"
      s!"run={k}@{t.pos.line},{t.pos.col} park={posStr (danglingNodePos? s)}"

private def walk (input : String) (n : Nat) : String :=
  String.intercalate " ; " ((List.range n).map (stepAt input))

/-! ## §1  The three pushes onto a `[96]` park

### A BODY preserves the reading

`a: 1⏎&p b`: the park after `&p` reads `1,0`, and so does the park after the
scalar it takes as its content.  The walk-back crosses the property and reaches
the same start, which is why §9.2's refusal rides a run into its own node. -/

#guard walk "a: 1\n&p b\n" 7
  == "run=none park=none ; run=body@0,0 park=none ; run=none park=none ; \
run=body@0,3 park=none ; run=prop@1,0 park=1,0 ; run=prop@1,0 park=1,0 ; —"

/-- The relay in the shape its consumer needs: a park's verdict is recovered
    from the verdict one BODY push later. -/
example {s s' : ScannerState} {c : Char} {i : Nat}
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (hna : c ≠ '&') (hnt : c ≠ '!')
    (hprev : prevRealIdx? s.tokens s.tokens.size = some i)
    (hiprop : s.tokens[i]!.val.isNodeProperty = true)
    (h_nd : danglingNodePos? s' = none) : danglingNodePos? s = none := by
  rw [← danglingNodePos?_dispatch_body_onProp hok hna hnt hprev hiprop]
  exact h_nd

/-! ### A PROPERTY moves the start

`&a⏎!t &b x`: at step 2 the run starts at the `&a` on line 0; at step 3 the
third property pushes the start down to the `!t` on line 1.  So the reading at
the park and the reading one push later are readings of DIFFERENT tokens, and a
premise stated as `danglingNodePos? sc = none` does not relay through a run's
own extension.  This is `PropsParkDangling` §4's witness, now with a lemma
under it. -/

#guard walk "&a\n!t &b x\n" 6
  == "run=none park=none ; run=prop@0,0 park=none ; run=prop@0,0 park=none ; \
run=prop@1,0 park=none ; run=prop@1,0 park=none ; —"

/-- Where the start goes: the PARK's own last token, not the pushed one. -/
example {s s' : ScannerState} {c : Char} {i : Nat}
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (hc : c = '&' ∨ c = '!')
    (hprev : prevRealIdx? s.tokens s.tokens.size = some i)
    (hiprop : s.tokens[i]!.val.isNodeProperty = true) :
    trailingNodeRun? s'.tokens = some (i, prevRealIdx? s.tokens i) :=
  trailingNodeRun?_dispatch_prop_onProp hok hc hprev hiprop

-- The move needs the run's two properties on DIFFERENT lines: three on one
-- line are refused by §6.9's own guard, and two are all a park ever holds.
#guard scanOk "&a !t &b x\n"
  == "SCAN-ERR L4YAML.ScanError.invalidNodeProperties '&' 0 6"
#guard (scanOk "&a !t x\n", parseOk "&a !t x\n") == ("SCAN-OK", "PARSE-OK")

/-! ### A flow COLLECTION preserves it — at the CLOSE

`a: 1⏎&p [b]`: the park after `&p` reads `1,0`; inside the collection there is
no reading at all (in flow); at the `]` the reading is `1,0` again.  That is
item 159's third arm — the close walked back to its open, then the `[96]`
walk-back from there — and it is what makes the collection's own close the
place the run's verdict can be spent. -/

#guard walk "a: 1\n&p [b]\n" 9
  == "run=none park=none ; run=body@0,0 park=none ; run=none park=none ; \
run=body@0,3 park=none ; run=prop@1,0 park=1,0 ; run=none park=none ; \
run=body@1,4 park=none ; run=prop@1,0 park=1,0 ; —"

/-- The same, as a lemma: the array at the close and the array at the park
    report the SAME run, given that the close finds its own open.  That
    hypothesis is the one thing this file cannot discharge — see §3. -/
example {a b : Array (Positioned YamlToken)} {i k : Nat}
    (hagree : ∀ j, j < b.size → a[j]! = b[j]!)
    (hbprev : prevRealIdx? b b.size = some k)
    (hbprop : b[k]!.val.isNodeProperty = true)
    (halast : prevRealIdx? a a.size = some i)
    (haclose : a[i]!.val.isFlowClose = true)
    (haopen : flowOpenIdx? a i = some b.size) :
    trailingNodeRun? a = trailingNodeRun? b :=
  trailingNodeRun?_flowClose_reads_park hagree hbprev hbprop halast haclose haopen

/-! ## §2  What the reading is read WITH

`danglingNodePos?` reads two slots — the run's start and its predecessor — and
`trailingNodeRun?_bounds` says both are below the array the reading was taken
on, in every one of the three arms.  That is what lets a reading be transported
by an agreement on a PREFIX, which is what all three pushes above are. -/

example {s t : ScannerState}
    (hflow : s.inFlow = t.inFlow) (hind : s.indents = t.indents)
    (hrun : trailingNodeRun? s.tokens = trailingNodeRun? t.tokens)
    (hagree : ∀ j, j < t.tokens.size → s.tokens[j]! = t.tokens[j]!) :
    danglingNodePos? s = danglingNodePos? t :=
  danglingNodePos?_congr hflow hind hrun hagree

example {ts : Array (Positioned YamlToken)} {st : Nat} {pred : Option Nat}
    (h : trailingNodeRun? ts = some (st, pred)) :
    st < ts.size ∧ pred = prevRealIdx? ts st :=
  trailingNodeRun?_bounds h

/-! ## §3  The site that cannot pay, and why it is not a park

`accum_flow_open_depth0`'s props arm builds `FlowBaseRoutes.value` — the
collection read as the enclosing construct's own node — by applying the park's
`h_route` to a grammar argument:

```
fun sp_ne sp_m h_content h_ssl =>
  h_route sp_m (flowInBlock_blockNode h_sep_run (SFlowNode.propsContent …) h_ssl)
```

Everything that closure receives is GRAMMAR.  There is no scanner state in it,
so a guard on `h_route` cannot be discharged inside it, and the open cannot
discharge it either: at the open the park really is dangling and really does
need the route.

**It needs it because the route is genuinely owed one step later.**  A dangling
`[96]` park that opens a collection has exactly two futures, and they take
different halves of the frame: -/

-- the collection heads an implicit KEY — LEGAL, and served by `resume.key`
#guard (scanOk "a: 1\n&p [b]: c\n", parseOk "a: 1\n&p [b]: c\n")
  == ("SCAN-OK", "PARSE-OK")
-- the collection closes as a VALUE — REFUSED, at the run's own start
#guard scanOk "a: 1\n&p [b]\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"

/-! So `resume.value`'s domain at a dangling park holds no accepted input, and
the refusal that empties it is read at the CLOSE — where §1's third measurement
says the verdict is the park's own, unchanged.  The gate therefore belongs on
`FlowBaseRoutes.value`, not on `pendingProps.h_route` alone, and what it is
missing is the hypothesis `trailingNodeRun?_flowClose_reads_park` takes:
`flowOpenIdx? a i = some b.size`, the statement that the close finds ITS open.

That is a fact about the token array's bracket balance, and the balance is
exactly what the flow stack indexes (`FlowOpenStack`'s kinds array mirrors
`sc.flowStack`).  Relating the two is the piece that is missing.

**And the trade is not available.**  Handing the arm the opaque resume instead
would widen `scannerDrop` over an input that is LEGAL — the first `#guard`
above — because the drop would be taken at the OPEN, before the `:` that
decides which half of the frame is spent.  Item 83 deleted the flow open's last
two drop rides; this would put one back, on accepted input. -/

/-! ## §4  What the next item needs

1. `flowOpenIdx? s_cl.tokens i = some s_park.tokens.size` at a depth-0 flow
   close — the bracket balance the flow stack already indexes, read on the
   token array.  With it, §1's third lemma turns the close's verdict into the
   park's, and `FlowBaseRoutes.value` can carry the gate.
2. Then `pendingProps.h_route` takes `danglingNodePos? sc = none`, its 23 sites
   pay as the table above says, and `ContentRouteGate` loses its right
   disjunct.
3. Behind both, the block landing's own half — `bareNodeRoute_or_refused`'s
   `h_op = true` branch.  Its `-` family is already refused by the scanner
   (`a: 1⏎- x` is `invalidBareDocument 1 0`, `k:⏎␣␣a: 1⏎␣␣- x` is `2,2`), so
   what is left there is the `:`/`?` family, which is LEGAL and routes through
   the key cascade — a CONSUMER to narrow, as item 156 said, not a guard. -/

#guard scanOk "a: 1\n- x\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard scanOk "k:\n  a: 1\n  - x\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 2"
#guard (scanOk "a: 1\n: v\n", parseOk "a: 1\n: v\n") == ("SCAN-OK", "PARSE-OK")
#guard (scanOk "a: 1\n? k\n", parseOk "a: 1\n? k\n") == ("SCAN-OK", "PARSE-OK")

end L4YAML.Tests.Guards.PropsRunReadingTransport
