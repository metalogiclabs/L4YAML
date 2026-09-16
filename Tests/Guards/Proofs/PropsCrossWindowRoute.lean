import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The crossed tail window, and the route that never needed the verdict
    (DOCS item 170)

Item 165's `[96]` length gate read a parent node's FULL property run, a break,
and the first implicit KEY's fresh run as ONE run, and refused 9KAX — found
when the test matrix ran again at item 169.  The narrowing is measured and
small: in block context the gate fires only when all three properties share
the cursor's line (`PropsRunLengthGate` §1 has the runtime).

The narrowing's PRICE is this file's subject.  With cross-line thirds
deferred, a `[96]` park's tail window can hold a property on an EARLIER line
below its tail (`PropsWindowCross`), and there item 165's verdict relay is not
hard but FALSE: §9.2's walk-back is capped at `[96]`'s arity, so a property
push SLIDES the window, and the park's verdict and the pushed state's are
readings of different columns.  §1 pins the refuting input at the runtime.

What replaces the relay is a route that never needed the verdict.  The gated
`h_route` exists so §9.2-dangling parks (`a: 1⏎&p b`) need no stream reading;
a park whose window CROSSED a break was born at a LANDED dispatch, and every
landed birth's route construction ignores the gate (`bareNodeRoute` is `[211]
implicitContinue`'s own unconditional reading; the marker's and suffix's slots
likewise).  So `pendingProps.h_routeX` carries that construction behind the
window as premise, the relay returns the window instead of the verdict, and a
same-line extension — the only other producer whose window premise is not
vacuous — REFUTES it, because its pushed tail and the token below share the
cursor's line.  §2 states the pieces at the proof's own types, §3 the record.
-/

namespace L4YAML.Tests.Guards.PropsCrossWindowRoute

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

/-- §9.2's verdict `n` tokens in. -/
private def dangAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match danglingNodePos? s with
    | none => "none"
    | some p => s!"some({p.line},{p.col})"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

/-! ## §1  The slide, at the runtime — and item 178's floor in front of it

When this file was written (item 170), `a:⏎!t⏎&b⏎␣␣!s &c x` scanned clean:
every landing passed §9.2's mid-stream check, the gate deferred every `&`/`!`,
and only `TokenParser` refused.  Five tokens in, the array ended `[.., &b, !s]`
and the window started at `&b` — column 0, AT the open level; one property
push later it started at `!s` — column 2, at no level.  So the pushed state's
verdict could not relay the park's, which is why `h_routeX` carries the window
instead.

Item 178's floor now stands IN FRONT of the slide for this family: the first
property lands at the awaiting level's own column, and the first BREAK after
it is `danglingNodePos?`'s own refusal (the slot-offered exemption no longer
covers a `[96]`-headed run), so the scan dies three tokens in — at the same
run start `TokenParser` used to name — and the sliding windows behind it are
no longer reachable states.  The verdict three tokens in is still the some
the relay could not carry, pinned below; what survives for the crossed-window
arms is the family with no offered slot in front — the ROOT's
(`&a⏎!t &b x`), where §9.2 reads `none` at every window (no level is open)
and the route never needed a verdict at all.  That shrinkage is the
crossed-window arms' own ledger row's to spend, not this file's. -/

#guard dangAt "a:\n!t\n&b\n  !s &c x\n" 3 == "some(1,0)"
#guard dangAt "a:\n!t\n&b\n  !s &c x\n" 5 == "no-state"
#guard scanOk "a:\n!t\n&b\n  !s &c x\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard parseOk "a:\n!t\n&b\n  !s &c x\n"
  == "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard dangAt "&a\n!t &b x\n" 2 == "none"
#guard dangAt "&a\n!t &b x\n" 4 == "none"
#guard scanOk "&a\n!t &b x\n" == "SCAN-OK"
#guard parseOk "&a\n!t &b x\n"
  == "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 3"

/-! ## §2  The pieces, at the proof's own types -/

/-- The relay returns what it finds: the verdict where the below-token is no
    property, the WINDOW where it is — with the gate's own pass saying the two
    tokens sit on different lines. -/
example {sc s_prep s_ad s' : ScannerState} {sp_scan : SurfPos} {c : Char}
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow_sc : sc.inFlow = false) (h_noflow_prep : s_prep.inFlow = false)
    (h_col0 : 0 < sp_scan.col)
    (h_nic : sc.needIndentCheck = false) (h_ska : sc.simpleKeyAllowed = false)
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    (h_prop : ∃ k, prevRealIdx? sc.tokens sc.tokens.size = some k ∧
      sc.tokens[k]!.val.isNodeProperty = true ∧
      sc.tokens[k]!.pos.line = sc.line)
    (h_ad_tok : s_ad.tokens = s_prep.tokens) (h_ad_ind : s_ad.indents = s_prep.indents)
    (h_ad_flow : s_ad.inFlow = s_prep.inFlow) (h_ad_line : s_ad.line = sc.line)
    (hc : c = '&' ∨ c = '!')
    (h_full : propertyRunFull s_ad = false)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s') :
    (danglingNodePos? s' = none → danglingNodePos? sc = none) ∨
      PropsWindowCross sc.tokens :=
  propsPark_dangling_of_prop h_corr h_pre h_noflow_sc h_noflow_prep h_col0 h_nic h_ska
    h_dn h_prop h_ad_tok h_ad_ind h_ad_flow h_ad_line hc h_full h_dispatch

/-- …and the window's consumer: given the park's `h_routeX`, the extension
    builds the new park's route on EITHER disjunct — the composition the two
    `&`/`!` arms write. -/
example {sc s' : ScannerState} {sp_start sp_node : SurfPos} {n : Nat}
    (h_route : danglingNodePos? sc = none →
      ∀ sp_m, SBlockNode n .blockIn sp_node sp_m → SLYamlStream sp_start sp_m)
    (h_routeX : PropsWindowCross sc.tokens →
      ∀ sp_m, SBlockNode n .blockIn sp_node sp_m → SLYamlStream sp_start sp_m)
    (h_rel : (danglingNodePos? s' = none → danglingNodePos? sc = none) ∨
      PropsWindowCross sc.tokens) :
    danglingNodePos? s' = none →
      ∀ sp_m, SBlockNode n .blockIn sp_node sp_m → SLYamlStream sp_start sp_m :=
  match h_rel with
  | Or.inl h_nd_rel => fun h_nd => h_route (h_nd_rel h_nd)
  | Or.inr h_cross => fun _ => h_routeX h_cross

/-- A same-line extension refutes the window it would otherwise owe: its
    pushed tail and the run token below it share the cursor's line. -/
example {s_ad s' sc : ScannerState} {p : Positioned YamlToken}
    (htok_ad : s_ad.tokens = sc.tokens)
    (h_tokens : s'.tokens = s_ad.tokens.push p)
    (hp_real : p.val ≠ .placeholder)
    (hp_line : p.pos.line = sc.line)
    (h_prop : ∃ k, prevRealIdx? sc.tokens sc.tokens.size = some k ∧
      sc.tokens[k]!.val.isNodeProperty = true ∧
      sc.tokens[k]!.pos.line = sc.line) :
    ¬ PropsWindowCross s'.tokens :=
  propsWindowCross_push_refute htok_ad h_tokens hp_real hp_line h_prop

/-! ## §3  The record

* **The field costs every producer nothing.**  The two routed births hand
  `fun cross => h_route (Or.inr cross)` — `content_dispatch_routed`'s widened
  route premise, whose every provider was already premise-ignoring
  (`fun _ => bareNodeRoute …`, `fun _ => mkroute`, `fun _ => nodocNodeRoute …`,
  the `---` park's own closer) or serves the crossed arm with the same
  `bareNodeRoute` its gated arm falls back to.  The six entry/value producers
  re-hand their own unconditional routes.  The two extensions refute the
  premise (`propsWindowCross_push_refute`).

* **No refusal weakens.**  The gated `h_route` and both `_or_refused`
  refinements are untouched; `ContentRouteGate` is unchanged.  What the
  crossed arm serves is `[211] implicitContinue`'s own over-approximate
  reading, the same one every landed birth already hands the gated route.

* **The gate stays as measured.**  This item's runtime is item 170's narrowed
  `propertyRunFull` alone; the slide is a fact about §9.2's READER
  (`trailingNodeRun?`'s `[96]`-arity cap), not about the gate, and it was
  reachable under NO earlier gate only because the length-only form refused
  the whole family first — 9KAX with it. -/

end L4YAML.Tests.Guards.PropsCrossWindowRoute
