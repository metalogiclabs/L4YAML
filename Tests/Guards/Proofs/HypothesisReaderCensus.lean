import Tests.Guards.Proofs.ArmSpendCensus

/-!
# The reader census: which premises are READ, and which are carried (item 225)

Item 224 built the SPEND CENSUS and closed with the question it was built to
ask, now askable of any premise: **which of β.5's remaining hypotheses have
readers, and which are carried?**  Its instrument could not be the one that
answers it.  The weakening probe loosens one binder, rebuilds, and reads the
errors — one build per binder.  That is why it was run on eight binders and not
on a library, and a question about "β.5's remaining hypotheses" is a question
about thousands.

This file moves the probe into the ENVIRONMENT.  For every binder of every
declaration it classifies the occurrences of that binder in the ELABORATED
proof term:

| verdict | what the term does with the binder |
|---|---|
| `READ` | eliminates it HERE — scrutinee of a recursor, `casesOn` or matcher, argument of a projection, a `.proj`, or applied to arguments |
| `RELAY` | hands it to another constant, and nothing else |
| `FIELD` | stores it in a constructor |
| `RETURN` | hands it back bare |
| `UNUSED` | does not mention it at all |
| `ETA` | the proof term does not BIND it — see §1 |

One walk of the module, ten seconds, every binder.

## §2's calibration is the reason to believe any of it

Item 224's eight rebuild verdicts are ground truth for eight of these binders,
and the census reproduces all eight — one `READ` (`colon_fires_implicit_key`),
seven not, and `block_dispatch_deferred` named `FIELD`, which is the mechanism
item 224 had to read off the error text by hand ("CONDUIT → `PendingNode.
pendingFlow`'s field").  Eight agreements at one build instead of eight.

## What it says about the three premises the mandate named

* **`content_dispatch_routed`'s optional contexts are all read.**  Five of the
  six — `h_keyctx`, `h_suffixctx`, `h_nodocctx`, `h_markerctx`, `h_propsctx` —
  are eliminated in the lemma's own term.  The sixth, `h_ref` (item 144's fifth
  arm), is a RELAY, and §5 chases it: it is eliminated one hop on, inside
  `rootMapRoute_or_refused` and `rootMapRouteF_or_refused`, where the left
  disjunct refutes the `h_op = false` branch outright.  **Not carried.**
* **R3's seven productions cannot be priced by readership, and §6 proves why.**
  `KeyPackPunt.dedent` and `.noKeyContext` are NULLARY, so `KeyPackPunt sc` is
  inhabited at every state — `punt_is_unconditional` — and therefore any
  consumer that takes `A ∨ KeyPackPunt sc` as a premise proves its conclusion
  without it (`punt_premise_buys_nothing`).  There is nothing to read, not
  because the census cannot see it but because the type carries none.  The
  price of a punt is the CASE SPLIT it forces, which is what
  `scripts/punt_reason_price.py` already measures; the two instruments are
  asking the only question available.
* **Item 183's flip order** is where `h_ref`'s readers live:
  `rootMapRoute_or_refused` and `rootMapRouteF_or_refused` are two of the flip's
  five definitions, so the premise the flip's REFUTABLE halves carry is read at
  every one of its four call sites.

**The rule this item adds: a premise has no reader for two different reasons,
and only one of them is about proofs.**  It can be threaded and never
eliminated — which the census measures — or its TYPE can be unconditionally
inhabited, which no census of terms can see and which one `example` settles.
R3's seven productions are the second kind.

## The debt this instrument carries, exhibited in §7

A relay's chase terminates inside the callee, and there the census cannot tell
a READ from a RE-STATEMENT: `Or.elim h f g` hands the decision to the caller's
own alternatives and `Or.imp_left f h` decides nothing, and BOTH are a relay at
the call site terminating in `Or.casesOn` one hop on.  §7 pins the two with the
same verdict, so the limit is machine-exhibited rather than asserted.
-/

namespace Tests.Guards.HypothesisReaderCensus

set_option autoImplicit false

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus

/-! ## §1  The instrument

The one delicate point is the telescope.  A lemma's TYPE keeps producing
`forall` binders past the end of its premise list whenever its conclusion is
itself a function — `rootMapRoute_or_refused` has thirteen leading foralls and
eleven lambdas, and the last two are `∀ sp_v, SBlockMapEntry k sp_key sp_v →`,
part of what it CONCLUDES.  So the telescope to peel is the shorter of the two,
and a binder the value never binds gets no verdict at all rather than a guessed
one: that is the `ETA` lane, and it is exactly the conclusion's own binders. -/

/-- What one occurrence of a binder does where it stands. -/
inductive Use where
  | elim (g : Name) (idx : Nat)
  | applied
  | projd
  | relay (g : Name) (idx : Nat)
  | field (g : Name) (idx : Nat)
  | bare
  | inTy
deriving Inhabited, BEq

/-- The struct-argument index of a projection function, read off the
    environment rather than off a list of projection names. -/
def projIdx (env : Environment) (g : Name) : Option Nat :=
  (env.getProjectionFnInfo? g).map (fun i => i.numParams)

def isCtor (env : Environment) (g : Name) : Bool :=
  match env.find? g with | some (.ctorInfo _) => true | _ => false

/-- What a term IS, for the purposes of the walk: the sub-term that carries it,
    plus whatever the peel discarded, which is still walked so that no
    occurrence can vanish.

    **Item 226 added this seam and it is not decoration.**  This item's walk
    peels NOTHING (`noPeel`), and that is why §5 below reports nine premises it
    cannot land in the library: `Or.imp` and an over-applied `Eq.ndrec` are
    PIPES — item 213 named them and item 215's `peelPipe` taught the SUPPLY
    census to see through them — and a walk that stops at a pipe reports the
    pipe.  `Tests.Guards.PremiseNecessityCensus` supplies the pipe peel and
    lands all nine. -/
abbrev Peel := Expr → Expr × Array Expr

/-- Item 225's peel: a term is itself. -/
def noPeel : Peel := fun e => (e, #[])

/-- Every occurrence of the binder whose de Bruijn index is `tgt` at depth 0.
    `d` is the extra binder depth, so the variable is `tgt + d`; `hasLooseBVar`
    prunes every subterm that cannot contain it. -/
partial def usesWith (peel : Peel) (env : Environment) (tgt : Nat) :
    Nat → Expr → Array Use → Array Use
  | d, e, acc =>
    if !e.hasLooseBVar (tgt + d) then acc else
    match e with
    | .bvar _ => acc.push .bare
    | .mdata _ b => usesWith peel env tgt d b acc
    | .proj _ _ s => if s == .bvar (tgt + d) then acc.push .projd
                     else usesWith peel env tgt d s acc
    | .lam _ t b _ =>
        let acc := if t.hasLooseBVar (tgt + d) then acc.push .inTy else acc
        usesWith peel env tgt (d + 1) b acc
    | .forallE _ t b _ =>
        let acc := if t.hasLooseBVar (tgt + d) then acc.push .inTy else acc
        usesWith peel env tgt (d + 1) b acc
    | .letE _ t v b _ =>
        let acc := if t.hasLooseBVar (tgt + d) then acc.push .inTy else acc
        let acc := usesWith peel env tgt d v acc
        usesWith peel env tgt (d + 1) b acc
    | .app .. =>
        let (hd, hside) := peel e
        if hd != e then
          let acc := hside.foldl (fun a x => usesWith peel env tgt d x a) acc
          usesWith peel env tgt d hd acc
        else Id.run do
          let f := e.getAppFn
          let args := e.getAppArgs
          let mut acc := acc
          if f == .bvar (tgt + d) then acc := acc.push .applied
          else acc := usesWith peel env tgt d f acc
          for k in [0:args.size] do
            let (a, side) := peel args[k]!
            for x in side do acc := usesWith peel env tgt d x acc
            if a == .bvar (tgt + d) then
              match f with
              | .const g _ =>
                  if majorOf env g == some k then acc := acc.push (.elim g k)
                  else if projIdx env g == some k then acc := acc.push (.elim g k)
                  else if isCtor env g then acc := acc.push (.field g k)
                  else acc := acc.push (.relay g k)
              | _ => acc := acc.push .bare
            else acc := usesWith peel env tgt d a acc
          return acc
    | _ => acc

/-- Item 225's walk: `usesWith` with nothing peeled. -/
def uses (env : Environment) (tgt : Nat) :
    Nat → Expr → Array Use → Array Use := usesWith noPeel env tgt

/-- The uses of binder `i` of `c`, or `none` when the proof term does not bind
    it (the `ETA` lane). -/
def binderUsesWith (peel : Peel) (env : Environment) (c : Name) (i : Nat) :
    Option (Array Use) := do
  let ci ← env.find? c
  let v ← ci.value? (allowOpaque := true)
  let (_, n) := optBinders ci.type
  guard (i < n)
  let m := min n (lamDepth v)
  guard (i < m)
  let mut body := v
  for _ in [0:m] do
    body := match body with | .lam _ _ b _ => b | x => x
  return usesWith peel env (m - 1 - i) 0 body #[]

def binderUses (env : Environment) (c : Name) (i : Nat) : Option (Array Use) :=
  binderUsesWith noPeel env c i

/-- The verdict: what the binder does inside THIS declaration's own term. -/
def direct (us : Array Use) : String :=
  if us.isEmpty then "UNUSED"
  else if us.any (fun u => match u with
        | .elim .. => true | .applied => true | .projd => true | _ => false)
    then "READ"
  else if us.any (fun u => match u with | .relay .. => true | _ => false)
    then "RELAY"
  else if us.any (fun u => match u with | .field .. => true | _ => false)
    then "FIELD"
  else if us.any (fun u => match u with | .bare => true | _ => false)
    then "RETURN"
  else "TYPE"

def verdictWith (peel : Peel) (env : Environment) (c : Name) (i : Nat) : String :=
  match binderUsesWith peel env c i with | none => "ETA" | some us => direct us

def verdict (env : Environment) (c : Name) (i : Nat) : String :=
  verdictWith noPeel env c i

/-- A hygienic binder name is not a name; print one underscore for all of them
    so a pin does not move when the elaborator renumbers (item 221's lesson). -/
def shownName (n : Name) : String :=
  let s := n.toString
  if (s.splitOn "_@").length > 1 || (s.splitOn "._hyg").length > 1 then "_" else s

/-- Chase a RELAY chain to the sites it terminates at.  The terminal is printed
    verbatim — `KIND@const#idx` — and NOT collapsed into a verdict, because §7
    shows the collapse is not available. -/
partial def chaseWith (peel : Peel) (env : Environment) (fuel : Nat)
    (seen : Std.HashSet String) (c : Name) (i : Nat) : Std.HashSet String :=
  let k := s!"{c}#{i}"
  if fuel == 0 then (({} : Std.HashSet String).insert "FUEL")
  else if seen.contains k then {}
  else
    let seen := seen.insert k
    match binderUsesWith peel env c i with
    | none =>
        if isCtor env c then (({} : Std.HashSet String).insert s!"FIELD@{k}")
        else if isMechanism env c then (({} : Std.HashSet String).insert s!"SPLIT@{k}")
        else (({} : Std.HashSet String).insert s!"ETA@{k}")
    | some us =>
        if us.isEmpty then (({} : Std.HashSet String).insert s!"UNUSED@{k}")
        else Id.run do
          let mut out : Std.HashSet String := {}
          for u in us do
            match u with
            | .elim g j => out := out.insert s!"ELIM@{c}#{i}>{g}#{j}"
            | .applied => out := out.insert s!"APPLIED@{k}"
            | .projd => out := out.insert s!"PROJ@{k}"
            | .field g j => out := out.insert s!"FIELD@{g}#{j}"
            | .bare => out := out.insert s!"RETURN@{k}"
            | .inTy => out := out.insert s!"TYPE@{k}"
            | .relay g j =>
                for t in chaseWith peel env (fuel - 1) seen g j do out := out.insert t
          return out

def chase (env : Environment) (fuel : Nat) (seen : Std.HashSet String)
    (c : Name) (i : Nat) : Std.HashSet String :=
  chaseWith noPeel env fuel seen c i

/-- A terminal inside our own library, as opposed to one inside core. -/
def isLibTerminal (t : String) : Bool :=
  ((t.splitOn "@").getD 1 "").startsWith "L4YAML"

/-- The `Prop` binders of `c`, by index and name. -/
def propBinders (c : Name) : CommandElabM (Array (Nat × Name)) :=
  liftTermElabM do
    let env ← getEnv
    let some ci := env.find? c | return #[]
    Meta.forallTelescope ci.type fun xs _ => do
      let mut out := #[]
      for k in [0:xs.size] do
        let x := xs[k]!
        if ← Meta.isProp (← Meta.inferType x) then
          out := out.push (k, (← x.fvarId!.getDecl).userName)
      return out

/-! ## §2  The calibration

Item 224 measured these sixteen by hand, eight of them by rebuild.  Those eight
are the ground truth: its table reads one READ and seven not, and it had to name
`block_dispatch_deferred`'s mechanism from the error text.  The census
reproduces the split and names the mechanism itself.

The eight LOOSE rows beneath are the other half of item 224's finding and the
census sees it too: four of them DO eliminate their arm — they read the FLAG,
which is the loose arm's whole left disjunct — while the conjunct's one reader
is `colon_fires_implicit_key` alone.  Disjoint readers, from the term. -/

def expectedCalibration : List String :=
  [ "FIELD block_dispatch_deferred#5 (h_arm)",
    "RELAY block_dispatch_deferred_stamp_offcol#8 (h_arm)",
    "RELAY block_dispatch_deferred_stamp_nopack#7 (h_arm)",
    "RELAY block_dispatch_deferred_inline#7 (h_arm)",
    "RELAY accum_block_on_closeThenBlock#17 (h_park)",
    "READ colon_fires_implicit_key#11 (h_arm)",
    "RELAY accum_block_on_pendingContent#23 (h_park)",
    "RELAY accum_block_on_pendingBlockContent#25 (h_park)",
    "RELAY accum_block_on_noPending#13 (h_arm)",
    "RELAY accum_content_on_noPending#14 (h_park)",
    "READ flowKeyRoute_of_open#14 (h_park)",
    "RELAY flowKeyRoute_of_root#9 (h_park)",
    "RELAY keyctx_of_preprocess#11 (h_park)",
    "READ landing_or_park_save#6 (h_park)",
    "READ landing_or_park_ska#6 (h_park)",
    "READ preprocess_flow_thread#9 (h_park)" ]

run_cmd do
  let env ← getEnv
  let rows : List (Name × Nat × Name) :=
    [ (``block_dispatch_deferred, 5, `h_arm),
      (``block_dispatch_deferred_stamp_offcol, 8, `h_arm),
      (``block_dispatch_deferred_stamp_nopack, 7, `h_arm),
      (``block_dispatch_deferred_inline, 7, `h_arm),
      (``accum_block_on_closeThenBlock, 17, `h_park),
      (``colon_fires_implicit_key, 11, `h_arm),
      (``accum_block_on_pendingContent, 23, `h_park),
      (``accum_block_on_pendingBlockContent, 25, `h_park),
      (``accum_block_on_noPending, 13, `h_arm),
      (``accum_content_on_noPending, 14, `h_park),
      (``flowKeyRoute_of_open, 14, `h_park),
      (``flowKeyRoute_of_root, 9, `h_park),
      (``keyctx_of_preprocess, 11, `h_park),
      (``landing_or_park_save, 6, `h_park),
      (``landing_or_park_ska, 6, `h_park),
      (``preprocess_flow_thread, 9, `h_park) ]
  let got := rows.map (fun (c, i, bn) =>
    s!"{verdict env c i} {c.getString!}#{i} ({bn})")
  if got != expectedCalibration then
    throwError "the CALIBRATION moved.\nexpected:\n{
      String.intercalate "\n" expectedCalibration}\ngot:\n{
      String.intercalate "\n" got}"

/-! ## §3  The module census

`StreamAccum`'s own `Prop` binders, by verdict.  `RELAY` is the majority lane
by a factor of two over `READ`, which is the shape a threaded invariant has and
the reason a spend census could not be a signature census.

`UNUSED` is the lane a reader expects to be full and it is nearly empty — and
the reason is worth recording, because it is not a fact about this library.
Lean's own `unusedVariables` linter already gates it, and seven of the nine
rows are spelled with a leading underscore precisely to silence it.  **The
cheap end of "carried" is already enforced by the toolchain; the expensive end
— threaded and never eliminated — is not, and that is the lane this census
adds.** -/

def expectedModuleTally : String :=
  "constants=1124 decls=945 eta=364 FIELD=154 READ=1016 RELAY=1997 RETURN=48 UNUSED=9"

def expectedUnused : List String :=
  [ "block_dispatch_deferred_inline#10 (_h_res)",
    "block_dispatch_deferred_stamp_nopack#10 (_h_src)",
    "block_dispatch_deferred_stamp_nopack#11 (_h_indent)",
    "block_dispatch_deferred_stamp_nopack#12 (_h_park)",
    "block_dispatch_deferred_stamp_offcol#11 (_h_src)",
    "block_dispatch_deferred_stamp_offcol#12 (_h_indent)",
    "block_dispatch_deferred_stamp_offcol#13 (_h_ne)",
    "flowKeyPack_of_close#10 (_)",
    "question_open_map#15 (_h_noflow_disp)" ]

run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let mut names : Array Name := #[]
  for (nm, _) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    names := names.push nm
  let mut tally : Std.HashMap String Nat := {}
  let mut unused : Array String := #[]
  let mut eta := 0
  let mut decls := 0
  for c in names do
    let pbs ← propBinders c
    if pbs.isEmpty then continue
    decls := decls + 1
    for (i, bn) in pbs do
      match binderUses env c i with
      | none => eta := eta + 1
      | some us =>
          let d := direct us
          tally := tally.insert d ((tally.getD d 0) + 1)
          if d == "UNUSED" then
            unused := unused.push s!"{c.getString!}#{i} ({shownName bn})"
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let got := s!"constants={names.size} decls={decls} eta={eta} {body}"
  if got != expectedModuleTally then
    throwError "the MODULE CENSUS moved.\nexpected: {expectedModuleTally}\ngot:      {got}"
  let gotU := (unused.qsort (· < ·)).toList
  if gotU != expectedUnused then
    throwError "the UNUSED lane moved.\nexpected ({expectedUnused.length}):\n{
      String.intercalate "\n" expectedUnused}\ngot ({gotU.length}):\n{
      String.intercalate "\n" gotU}"

/-! ## §4  The optional contexts, read rather than supplied

Items 212–218 censused the `_ ∨ True` premises by SUPPLY — who pays, who
declines, what relays.  Nothing there asked who READS one when it is paid, and
this is that census over the same population, with the matcher auxiliaries that
inherit their parents' binders filtered out so the denominator is declarations. -/

def expectedOptTally : String := "total=163 ETA=34 READ=85 RELAY=44"

/-- The six item 212 enumerated, by verdict.  Five are read in
    `content_dispatch_routed`'s own term; `h_ref` alone relays, and §5 says
    where it lands. -/
def expectedContentDispatch : List String :=
  [ "READ content_dispatch_routed#18 (h_keyctx)",
    "READ content_dispatch_routed#20 (h_suffixctx)",
    "READ content_dispatch_routed#21 (h_nodocctx)",
    "READ content_dispatch_routed#22 (h_markerctx)",
    "RELAY content_dispatch_routed#24 (h_ref)",
    "READ content_dispatch_routed#25 (h_propsctx)" ]

run_cmd do
  let env ← getEnv
  let mut tally : Std.HashMap String Nat := {}
  let mut total := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    if isMechanism env nm then continue
    for (i, _) in (optBinders ci.type).1 do
      total := total + 1
      let v := verdict env nm i
      tally := tally.insert v ((tally.getD v 0) + 1)
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let got := s!"total={total} {body}"
  if got != expectedOptTally then
    throwError "the OPTIONAL-CONTEXT census moved.\nexpected: {expectedOptTally}\ngot:      {got}"
  let rows := (optBinders (env.find? ``content_dispatch_routed).get!.type).1
  let gotC := rows.toList.map (fun (i, bn) =>
    s!"{verdict env ``content_dispatch_routed i} content_dispatch_routed#{i} ({bn})")
  if gotC != expectedContentDispatch then
    throwError "content_dispatch_routed's contexts moved.\nexpected:\n{
      String.intercalate "\n" expectedContentDispatch}\ngot:\n{
      String.intercalate "\n" gotC}"

/-! ## §5  The chase, and the nine premises ~~it cannot land in the library~~
    **a PIPE-BLIND chase cannot land**

~~Of the forty-four relayed optional premises, nine reach no elimination inside
`L4YAML` at all: every terminal of their chase is a core combinator.  That is
NOT a verdict of "carried" — §7 is why — but it is the shortlist, and it is
where a reader looking for a carried premise should look first.~~

**Item 226: the shortlist is a measurement of THIS walk's blind spot, not of
the library.**  `chase` here runs at `noPeel`, and five of the nine terminate
at `Or.imp#6` or at an over-applied `Eq.ndrec` — both PIPES, both named by item
213 and both seen through by the supply census since item 215.  With the same
`pipeArg` list peeled, ALL NINE land, and two of them land on a LIBRARY
elimination, which is exactly what the struck sentence denied.  The nine rows
below are kept and still pinned, because a blind spot that is pinned at a
number is one a later walk can be held against; `Tests.Guards.PremiseNecessityCensus`
pins where each of them actually goes.

`h_ref` is deliberately not on it.  Its chase lands twice in the library, at
`rootMapRoute_or_refused` and `rootMapRouteF_or_refused` — two of item 183's
five flip definitions — where the left disjunct is spent to refute the
`h_op = false` branch outright.  A premise read only in refutation is exactly
the shape item 224 found at the arm's one reader, one workstream over.  (Its
third terminal, `SPLIT@Eq.ndrec#9`, is the pipe: item 226 peels it and two
remain.) -/

def expectedCoreTerminal : List String :=
  [ "accum_block_on_pendingBlock#28 (h_seqF_old)",
    "accum_block_on_pendingBlockContent#33 (h_seqF_old)",
    "accum_block_on_pendingContent#31 (h_seqF168)",
    "accum_content_on_pendingMapValue_indented#14 (h_ncol_old)",
    "colon_open_map#24 (h_cov_in)",
    "flowKeyRoute_of_root#19 (h_tail143)",
    "indicator_open_map#26 (h_ref_land)",
    "question_open_map#23 (h_cov_in)",
    "question_open_map#24 (h_cov_nil)" ]

/-- Where `h_ref` is eliminated, named. -/
def expectedRefTerminals : List String :=
  [ "ELIM@L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused.match_1_1#4",
    "ELIM@L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused.match_1_1#4",
    "SPLIT@Eq.ndrec#9" ]

run_cmd do
  let env ← getEnv
  let mut core : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    if isMechanism env nm then continue
    for (i, bn) in (optBinders ci.type).1 do
      if verdict env nm i != "RELAY" then continue
      let ts := chase env 30 {} nm i
      if ts.toList.all (fun t => !isLibTerminal t) then
        core := core.push s!"{nm.getString!}#{i} ({shownName bn})"
  let got := (core.qsort (· < ·)).toList
  if got != expectedCoreTerminal then
    throwError "the CORE-TERMINAL shortlist moved.\nexpected ({expectedCoreTerminal.length}):\n{
      String.intercalate "\n" expectedCoreTerminal}\ngot ({got.length}):\n{
      String.intercalate "\n" got}"
  let refT := (chase env 30 {} ``content_dispatch_routed 24).toList.mergeSort
    (fun a b => a < b)
  if refT != expectedRefTerminals then
    throwError "h_ref's terminals moved.\nexpected:\n{
      String.intercalate "\n" expectedRefTerminals}\ngot:\n{
      String.intercalate "\n" refT}"

/-! ## §6  The premise no census of terms can price

R3's remaining debt is seven PRODUCTIONS of two `KeyPackPunt` reasons, and the
reader census does not apply to them — not because the instrument is short, but
because the reasons carry nothing.  `dedent` and `noKeyContext` are nullary, so
the type is inhabited at every state, so a premise of that shape constrains
nothing and a consumer that takes one proves its conclusion without it.

**A premise has no reader for two different reasons, and only one of them is
about proofs.** -/

/-- The two unpayable reasons are argument-free; the two payable ones are not. -/
def expectedPuntFields : String :=
  "tab=2 dedent=0 implicitValue=3 noKeyContext=0"

run_cmd do
  let env ← getEnv
  let got := String.intercalate " " ([``KeyPackPunt.tab, ``KeyPackPunt.dedent,
      ``KeyPackPunt.implicitValue, ``KeyPackPunt.noKeyContext].map (fun c =>
    match env.find? c with
    | some (.ctorInfo cv) => s!"{c.getString!}={cv.numFields}"
    | _ => s!"{c.getString!}=?"))
  if got != expectedPuntFields then
    throwError "KeyPackPunt's field counts moved.\nexpected: {
      expectedPuntFields}\ngot:      {got}"

/-- **`KeyPackPunt sc` is inhabited at every state.**  This is the whole of R3's
    seven productions as a proposition: while `dedent` stands, producing one is
    free. -/
lemma punt_is_unconditional (sc : ScannerState) : KeyPackPunt sc := .dedent

/-- …so a consumer that takes a punt as a premise proves its goal without it. -/
lemma punt_premise_buys_nothing {sc : ScannerState} {P : Prop}
    (k : KeyPackPunt sc → P) : P := k (punt_is_unconditional sc)

/-- …and the same for the disjunction the productions actually hand over, which
    is the shape item 223's §3 exhibited at one call site and this states for
    every consumer there will ever be. -/
lemma punt_disjunct_buys_nothing {sc : ScannerState} {A P : Prop}
    (k : A ∨ KeyPackPunt sc → P) : P := k (Or.inr (punt_is_unconditional sc))

/-! ## §7  What ~~the census~~ **a pipe-blind census** cannot decide, exhibited

A `RELAY` chase terminates inside the callee.  Two relays with the same
terminal can be opposite things: `Or.elim` hands the decision back to the
caller's own alternatives, so the caller READS; `Or.imp_left` rebuilds a weaker
disjunction and decides nothing.  Both are an argument to a constant at the
call site, and both are eliminated by `Or.casesOn` one hop on.

The pin below states that the census gives them the same verdict.  That is the
limit, machine-exhibited: a terminal-based reading of the chase would call the
re-statement a read, which is why §5 publishes terminals and stops.

~~…which is why the `RELAY` lane's rows are a shortlist and not a verdict.~~
**Item 226 decided it, and the answer was already in the repo.**  `Or.imp_left`
is a PIPE; peel it and `restates_by_imp` reads `RETURN` — the premise IS the
conclusion, weakened — while `reads_by_elim` still reads `RELAY` into a
constant that eliminates.  The two exhibits below are kept and still pinned at
the SAME verdict, because that pin is what says this walk is the blind one;
`PremiseNecessityCensus` pins them apart. -/

lemma reads_by_elim {a b c : Prop} (h : a ∨ b) (f : a → c) (g : b → c) : c :=
  h.elim f g

lemma restates_by_imp {a b c : Prop} (h : a ∨ b) (f : a → c) : c ∨ b :=
  h.imp_left f

def expectedIndistinguishable : String :=
  "reads_by_elim#3=RELAY restates_by_imp#3=RELAY"

run_cmd do
  let env ← getEnv
  let got := s!"reads_by_elim#3={verdict env ``reads_by_elim 3} restates_by_imp#3={
    verdict env ``restates_by_imp 3}"
  if got != expectedIndistinguishable then
    throwError "§7's two relays are no longer indistinguishable.\nexpected: {
      expectedIndistinguishable}\ngot:      {got}"

end Tests.Guards.HypothesisReaderCensus
