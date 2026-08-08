/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Production.PreprocessProduction
import L4YAML.Proofs.Scanner.ScanStrictCoupling
import L4YAML.Proofs.Production.StructureProduction
import L4YAML.Proofs.Production.NodeProduction
import L4YAML.Proofs.Scanner.FlowAdjacency
import L4YAML.Proofs.Scanner.BlockScalarFlowGuard
import L4YAML.Proofs.Scanner.ScannerFlowCollection
import L4YAML.Proofs.Scanner.ScannerFlowStackPreservation
import L4YAML.Proofs.Scanner.ScannerAllowDirectives

/-! # Stream Grammar Accumulator (Layer 4d + 4e: Lagging Grammar with Block Stack)

    Threads a grammar accumulator through `scanLoop` alongside `ScannerSurfCorr`,
    narrowing the sorry in `scan_content_gives_stream` to per-dispatch lemmas.

    ## Architecture: The Lagging Invariant with Block Stack

    Scanner token boundaries don't align with grammar production boundaries
    (see DOCS.md, "Code-proof architecture mismatch"). Grammar productions like `SBlockNode.flowInBlock` require
    prefix (`SSeparate`) + content (`SFlowNode`) + postfix (`SSLComments`), but
    the postfix is consumed during the NEXT token's preprocessing.

    Additionally, block collections (`SBlockSeqEntries`, `SBlockMapEntries`) span
    multiple `scanNextToken` calls. A block sequence `- a\n- b` involves ≥4 tokens.
    The scanner tracks this via an indent stack; the grammar needs a corresponding
    `BlockStack`.

    The fix: a **four-component state** (the "lagging quad"):

        ∀ token step:
          SLYamlStream sp_start sp_gram  ∧      -- grammar up to here
          BlockStack sp_gram sp_block    ∧      -- nested block collections
          PendingNode false sp_start sp_block sp_scan   ∧      -- immediate pending state
          ScannerSurfCorr sc sp_scan            -- scanner ahead

    At each step:
    1. Preprocessing of token N+1 provides `SSLComments` to close token N
    2. `unwindIndents` may pop `BlockStack` levels (forming `SBlockNode`)
    3. `pushSequenceIndent`/`pushMappingIndent` may push `BlockStack` levels
    4. Content dispatch of token N+1 opens a new `PendingNode`
    At EOF, the final `BlockStack` is fully unwound and `PendingNode` closed.

    ## Sorry narrowing

    Five per-dispatch sorry lemmas (§1a–§1e), each architecturally provable.
    The composition layer (§1f, §2, §3, §5) is fully proven by delegation.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.StreamAccum

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.BlockScalarFlowGuard
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScanStrictCoupling
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.StructureCoupling
open L4YAML.Proofs.PreprocessProduction
open L4YAML.Proofs.StructureProduction
open L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.ScalarProduction
open L4YAML.Proofs.NodeProduction
open L4YAML.CharPredicates
open L4YAML.Proofs.FlowAdjacency

/-! ## §0a PendingNode — Immediate Pending State

    Tracks the gap between the `BlockStack` top (`sp_block`) and the scanner
    position (`sp_scan`). This gap contains the most recent token's characters
    that haven't yet been incorporated into either a block collection entry
    or a standalone grammar production.

    When the next preprocessing step provides `SSLComments`, the pending node
    is "closed" — incorporated into the grammar — and the state advances.

    **Evidence-bearing design (v0.4.7):** Structural pending variants carry
    grammar markers directly (`SCDirectivesEnd` for `---`, `SCDocumentEnd` for `...`).
    These are constructed at dispatch time using `_prod` theorems and consumed
    when preprocessing provides SSLComments — the marker plus SSLComments compose
    directly into `SLExplicitDocument` or `SLDocumentSuffix` without any closure.
    Other pending variants retain `h_closable` closures for now. -/

inductive PendingNode : Bool → SurfPos → SurfPos → SurfPos → Prop where
  /-- No pending gap. Block stack top and scanner at same position.
      Occurs at stream start, between documents, after document suffixes
      whose trailing SSLComments has already been absorbed, and at the
      start of a new block collection level (before any entry content). -/
  | noPending (sp_start sp : SurfPos) : PendingNode false sp_start sp sp
  /-- Content token scanned (scalar, anchor, alias, tag).
      The gap sp_block → sp_scan contains SSeparate + content.
      Awaiting SSLComments sp_scan sp' to close into SBlockNode.
      `h_closable` constructs the stream extension using grammar evidence
      and the stream captured at dispatch time. The `SLYamlStream sp_start`
      is captured inside the closure, not passed at consumption time. -/
  | pendingContent (sp_start sp_block sp_scan : SurfPos)
      (h_closable : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        SLYamlStream sp_start sp_mid) :
      PendingNode false sp_start sp_block sp_scan
  /-- Document end `...` scanned. The gap contains SCDocumentEnd.
      Awaiting SSLComments to form SLDocumentSuffix.
      Carries the marker directly for compositional consumption. -/
  | pendingDocEnd (sp_start sp_block sp_scan : SurfPos)
      (h_marker : SCDocumentEnd sp_block sp_scan) :
      PendingNode false sp_start sp_block sp_scan
  /-- Document start `---` scanned. The gap contains SCDirectivesEnd
      (possibly preceded by directives). Awaiting content or SSLComments
      to complete the document.
      `h_doc_builder` abstracts whether this is an explicit document
      (standalone `---`) or a directive document (`%YAML` ... `---`).
      Given content evidence after `---`, it produces `SLAnyDocument`. -/
  | pendingDocStart (sp_start sp_block sp_scan : SurfPos)
      (h_doc_builder : ∀ sp_end,
        GAlt SLBareDocument (GSeq SENode SSLComments) sp_scan sp_end →
        SLAnyDocument sp_block sp_end) :
      PendingNode false sp_start sp_block sp_scan
  /-- Directive `%` scanned. The gap contains directive content.
      Awaiting next `%` (accumulate) or `---` (form directive document).
      Carries an accumulator that, given SSLComments, produces
      `GPlus SLDirective` covering all directives so far.
      Captures the stream at the point before the first directive.
      Does NOT carry h_closable — cannot close directives without
      `---` (SCDirectivesEnd), which has not yet been scanned.
      Closing is deferred to the `---` transition (→ pendingDocStart).

      **Fix B (grammar completeness)**: this is the only `true`-indexed
      constructor. The `Bool` index couples the pending kind to the
      scanner's `directivesPresent` flag in the accumulation invariant,
      making "directives closed without `---`" provably unreachable
      (the scanner errors first). -/
  | pendingDirective (sp_start sp_block sp_scan : SurfPos)
      (h_dir_acc : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        GPlus SLDirective sp_block sp_mid)
      (h_stream : SLYamlStream sp_start sp_block) :
      PendingNode true sp_start sp_block sp_scan
  /-- Flow indicator scanned (`]`, `}`, `,`), or deferred block dispatch.
      Carries stream at block level. Closing requires grammar composition
      (flow collection + SSLComments) — deferred to consumption site. -/
  | pendingFlow (sp_start sp_block sp_scan : SurfPos)
      (h_stream : SLYamlStream sp_start sp_block) :
      PendingNode false sp_start sp_block sp_scan
  /-- Content token scanned INSIDE a block entry (e.g., `- "hello"`).
      Like `pendingContent`, but additionally carries entry-level evidence
      via `h_closable_entry`. When this content is closed and a new `-`
      follows at the same level, `h_closable_entry` returns accumulated
      `SBlockSeqEntries` + continuation for further snocing. -/
  | pendingBlockContent (sp_start sp_block sp_scan : SurfPos) (n : Nat)
      (h_closable : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        SLYamlStream sp_start sp_mid)
      (h_closable_entry : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        ∃ sp_first,
          SBlockSeqEntries n sp_first sp_mid ∧
          (∀ sp_end, SBlockSeqEntries n sp_first sp_end → SLYamlStream sp_start sp_end)) :
      PendingNode false sp_start sp_block sp_scan
  /-- Block indicator scanned (`-`, `?`, `:`).
      The gap sp_block → sp_scan contains the indicator character.
      The block nesting is tracked separately by `BlockStack`.
      `h_close` takes the entry CONTENT as `SBlockNode` and produces the
      stream. For empty entries (no content follows), the caller provides
      `SBlockNode.emptyNode ... h_ssl`; for content entries, the caller
      provides `SBlockNode.flowInBlock ...` etc. The closure captures
      entry opener evidence (indent, dash/key/value, preprocessing) and
      the stream at the dispatch point.
      `h_close_entry` is the **entry-level** variant: instead of producing
      the full stream, it returns the accumulated `SBlockSeqEntries` and a
      continuation that can produce the stream from any extended entries.
      This enables same-level `-` to snoc new entries via
      `SBlockSeqEntries_snoc` without closing the sequence. -/
  | pendingBlock (sp_start sp_block sp_scan : SurfPos)
      (h_close : ∀ sp_mid,
        SBlockNode 0 .blockIn sp_scan sp_mid →
        SLYamlStream sp_start sp_mid)
      (h_close_entry : ∀ sp_mid,
        SBlockNode 0 .blockIn sp_scan sp_mid →
        ∃ sp_first,
          SBlockSeqEntries 0 sp_first sp_mid ∧
          (∀ sp_end, SBlockSeqEntries 0 sp_first sp_end → SLYamlStream sp_start sp_end)) :
      PendingNode false sp_start sp_block sp_scan

/-! ## §0b BlockStack — Nested Block Collection Accumulator

    Tracks partially-accumulated block collections being built across
    multiple `scanNextToken` calls. Mirrors the scanner's indent stack
    (minus the sentinel entry at column -1).

    Each level records:
    - `col`: The column where this block collection starts (matching
      scanner's `IndentEntry.column`)
    - Whether it's a sequence or mapping (matching `IndentEntry.isSequence`)
    - Position boundaries for this nesting level's character coverage

    The actual grammar types are:
    - `SBlockSeqEntries n` (`single | cons`): entries for block sequences
    - `SBlockMapEntries n` (`single | cons`): entries for block mappings
    - `SBlockNode.blockSeq`: wraps `SBlockSeqEntries` with `GOpt props + SSLComments`
    - `SBlockNode.blockMap`: wraps `SBlockMapEntries` with `GOpt props + SSLComments`

    **Protocol (mirrors scanner's indent stack operations):**

    - **Push** (`pushSequenceIndent`/`pushMappingIndent`): When `col > currentIndent`,
      a new indent entry is pushed and `.blockSequenceStart`/`.blockMappingStart`
      is emitted. `BlockStack` gets a corresponding `.seqLevel`/`.mapLevel`.

    - **Pop** (`unwindIndents` in preprocessing): When content moves to a lower
      column, indent entries are popped and `.blockEnd` tokens emitted. Each pop
      finalizes the block collection into `SBlockNode.blockSeq`/`.blockMap`,
      potentially extending `SLYamlStream`.

    - **Same-level entry** (e.g., second `-` at same indent): The current level's
      accumulated entries grow by one (`SBlockSeqEntries.cons` / `SBlockMapEntries.cons`).
      No push/pop occurs.

    Each `seqLevel`/`mapLevel` carries a compositional closure
    `h_closable` that can extend the stream from the stack's outer
    boundary (`sp`) through all accumulated block content to the
    level's top (`sp'`). This avoids requiring explicit grammar
    witnesses (`SBlockSeqEntries`, `SBlockMapEntries`) at this stage —
    those are constructed inside the closure when the closure is
    provided (future work). -/

inductive BlockStack : SurfPos → SurfPos → Prop where
  /-- No active block collections. At document level or stream start. -/
  | nil (sp : SurfPos) : BlockStack sp sp
  /-- Block sequence being accumulated at column `col`.
      Outer stack covers sp → sp_mid. This level's character coverage
      is sp_mid → sp'. Entries will form `SBlockSeqEntries (seqSpaces n c)`
      where `n` is determined by `col`.
      `h_closable`: given any stream ending at `sp`, extends it to `sp'`
      by incorporating the inner stack + this level's accumulated entries. -/
  | seqLevel (col : Int) (sp sp_mid sp' : SurfPos) :
      BlockStack sp sp_mid →
      (∀ (sp_start : SurfPos), SLYamlStream sp_start sp → SLYamlStream sp_start sp') →
      BlockStack sp sp'
  /-- Block mapping being accumulated at column `col`.
      Entries will form `SBlockMapEntries n`.
      `h_closable`: given any stream ending at `sp`, extends it to `sp'`
      by incorporating the inner stack + this level's accumulated entries. -/
  | mapLevel (col : Int) (sp sp_mid sp' : SurfPos) :
      BlockStack sp sp_mid →
      (∀ (sp_start : SurfPos), SLYamlStream sp_start sp → SLYamlStream sp_start sp') →
      BlockStack sp sp'

/-! ## §0b' FlowStack — Flow Level Marker

    Trivial position-identity type bridging BlockStack and PendingNode.
    FlowStack.nil is the only constructor — flow collection evidence
    (open brackets, entries) is deferred to PendingNode.pendingFlow
    and close_with_ssl.

    FlowStack sits between BlockStack and PendingNode in the position chain:
    `SLYamlStream → BlockStack → FlowStack → PendingNode → ScannerSurfCorr`

    After 4z.1: FlowStack is always nil. All flow indicator evidence
    (`GLit '['`, `GLit '{'`) is captured in PendingNode.pendingFlow
    and composed at consumption time via close_with_ssl. -/

inductive FlowStack : SurfPos → SurfPos → Prop where
  /-- No active flow collections. At block level or stream start. -/
  | nil (sp : SurfPos) : FlowStack sp sp

/-- Absorb both BlockStack and FlowStack into the stream.
    FlowStack is always nil (4z.1), so this only handles BlockStack. -/
lemma absorb_stacks (sp_start sp_gram sp_block sp_flow : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow) : SLYamlStream sp_start sp_flow := by
  cases h_flow with
  | nil =>
    cases h_stack with
    | nil => exact h_stream
    | seqLevel _ _ _ _ _ h_cl_b => exact h_cl_b sp_start h_stream
    | mapLevel _ _ _ _ _ h_cl_b => exact h_cl_b sp_start h_stream

/-! ## §0c Helpers for §1a (EOF Stream Extension)

    Two helpers needed to discharge the `nil + noPending + col=0` case of §1a:
    1. `preprocess_none_ssl_comments_col0`: unfolds `scanNextToken_preprocess`,
       shows only `!hasMore` path fires, delegates to `skipToContent_eof_ssl_comments_col0`
    2. `ssl_comments_extend_stream`: converts `SSLComments` → `GStar SLComment`
       → `SLDocumentPrefix` → extends `SLYamlStream` via `implicitContinue`

    Together these prove: at col=0, preprocessing EOF extends the stream. -/

/-- When `scanNextToken_preprocess` returns `none` (EOF) and the scanner
    is at col=0, the remaining characters form `SSLComments`. -/
lemma preprocess_none_ssl_comments_col0 (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SSLComments sp sp_final ∧ sp_final.chars = [] := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    split at hok
    · -- !s_content.hasMore → EOF on skipToContent (the only reachable path)
      rename_i h_notMore
      have heof : ¬s_content.hasMore := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_notMore
        exact fun h => by simp [h] at h_notMore
      exact skipToContent_eof_ssl_comments_col0 sc sp s_content hcorr hcol
        (show skipToContent sc = .ok s_content by unfold skipToContent; exact h_skip) heof
    · -- s_content.hasMore: all branches return (some ...) or error, not none.
      -- Proof: unwindIndents/saveSimpleKey preserve offset/input, so peek? is
      -- still some (since hasMore). The peek?=none branches are absurd.
      rename_i h_hasMore
      split at hok
      · split at hok
        · simp at hok
        · split at hok
          · rename_i h_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none; dsimp only [] at h_peek_none
            unfold unwindIndents at h_peek_none
            simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd,
              unwindIndentsLoop_input] at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_hasMore
              simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok
      · split at hok
        · simp at hok
        · split at hok
          · rename_i h_no_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_hasMore
              simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok

-- General version: no col=0 requirement.
lemma preprocess_none_ssl_comments (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SSLComments sp sp_final ∧ sp_final.chars = [] := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    split at hok
    · rename_i h_notMore
      have heof : ¬s_content.hasMore := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_notMore
        exact fun h => by simp [h] at h_notMore
      exact skipToContent_eof_ssl_comments sc sp s_content hcorr
        (show skipToContent sc = .ok s_content by unfold skipToContent; exact h_skip) heof
    · rename_i h_hasMore
      split at hok
      · split at hok
        · simp at hok
        · split at hok
          · rename_i h_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none; dsimp only [] at h_peek_none
            unfold unwindIndents at h_peek_none
            simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd,
              unwindIndentsLoop_input] at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_hasMore
              simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok
      · split at hok
        · simp at hok
        · split at hok
          · rename_i h_no_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_hasMore
              simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok

/-- Prepend trailing whitespace into `SSLComments`.

    Bridges the gap between a grammar endpoint (e.g., end of `SNsPlain`)
    and the scanner state endpoint (past trailing WS consumed by the scanner).
    The trailing WS becomes part of `s-b-comment → s-separate-in-line`
    per YAML 1.2.2 §6.5.

    Used by `accum_content_pending` for plain scalars, where the scanner
    advances past trailing whitespace that the grammar doesn't cover. -/
lemma white_prepend_SSLComments {sp sp' sp_mid : SurfPos}
    (h_ws : GStar SSWhite sp sp')
    (h_ssl : SSLComments sp' sp_mid) :
    SSLComments sp sp_mid := by
  cases h_ws with
  | nil => exact h_ssl
  | cons _ sp_w _ h_first h_rest =>
    -- Non-empty WS: build GPlus SSWhite sp sp' for SSeparateInLine
    have h_gplus : GPlus SSWhite sp sp' := GPlus.mk sp sp_w sp' h_first h_rest
    cases h_ssl
    case withComment s₁ h_sbc h_lcomments =>
      cases h_sbc
      case withSep s₂ s₃ h_sep h_opt h_break =>
        -- Concatenate our WS with existing SSeparateInLine
        cases h_sep
        case whites h_gplus' =>
          -- Combine GPlus: ours + theirs
          have h_combined : GPlus SSWhite sp s₂ :=
            GPlus_extend_GStar h_gplus (GPlus_to_GStar h_gplus')
          exact SSLComments.withComment sp s₁ sp_mid
            (SSBComment.withSep sp s₂ s₃ s₁
              (SSeparateInLine.whites sp s₂ h_combined) h_opt h_break)
            h_lcomments
        case startOfLine =>
          -- Their sep is identity (s₂ = sp'), use our WS directly
          exact SSLComments.withComment sp s₁ sp_mid
            (SSBComment.withSep sp sp' s₃ s₁
              (SSeparateInLine.whites sp sp' h_gplus) h_opt h_break)
            h_lcomments
      case noSep h_break =>
        -- No existing sep: add our WS as sep
        exact SSLComments.withComment sp s₁ sp_mid
          (SSBComment.withSep sp sp' sp' s₁
            (SSeparateInLine.whites sp sp' h_gplus) (GOpt.none _) h_break)
          h_lcomments
    case startOfLine chars h_lcomments =>
      -- startOfLine requires col=0, but non-empty WS forces col ≥ 1
      exfalso
      have h1 := sswhite_col_succ sp sp_w h_first
      have h2 := gstar_sswhite_col_ge sp_w ⟨chars, 0⟩ h_rest
      simp at h2
      omega

/-- Extend `SLYamlStream` with `SSLComments`.

    `SSLComments` → `GStar SLComment` → `SLDocumentPrefix.comments`
    → `SLYamlStream.implicitContinue` with no explicit document. -/
lemma ssl_comments_extend_stream
    (sp_start sp sp_final : SurfPos)
    (h_stream : SLYamlStream sp_start sp)
    (h_ssl : SSLComments sp sp_final) :
    SLYamlStream sp_start sp_final := by
  have h_gstar := SSLComments_to_GStar sp sp_final h_ssl
  exact SLYamlStream.implicitContinue sp_start sp sp_final sp_final sp_final
    h_stream
    (GStar.cons sp sp_final sp_final (SLDocumentPrefix.comments sp sp_final h_gstar) (GStar.nil _))
    (GOpt.none _)
    (GStar.nil _)

/-- Extend `SLYamlStream` with a top-level flow sequence node + trailing comments.

    The grammatical replacement for `scannerDrop`'s job (Fix A, Piece 2/3): a
    completed `[...]` scanned at document level is a bare-document flow node —
    `s-l+flow-in-block` [195] with zero-width leading separation (`.flowOut`,
    start-of-line) and the trailing `s-l-comments` — hence an `SLBareDocument`
    that extends the stream via `implicitContinue`. No opaque gap; the flow
    content `sp_block → sp_flow` is a real `SFlowSequence` derivation. -/
lemma flowSeq_extends_stream
    (sp_start sp_block sp_flow sp_final : SurfPos)
    (h_stream : SLYamlStream sp_start sp_block)
    (h_flow : SFlowSequence 0 .flowOut sp_block sp_flow)
    (h_ssl : SSLComments sp_flow sp_final) :
    SLYamlStream sp_start sp_final :=
  SLYamlStream.implicitContinue sp_start sp_block sp_block sp_final sp_final
    h_stream (GStar.nil _)
    (GOpt.some sp_block sp_final
      (SLAnyDocument.bare sp_block sp_final
        (SLBareDocument.mk sp_block sp_final
          (SBlockNode.flowInBlock 0 .blockIn sp_block sp_block sp_flow sp_final
            (SSeparateLines.inline 0 sp_block sp_block (SSeparateInLine.startOfLine sp_block))
            (SFlowNode.content 0 .flowOut sp_block sp_flow
              (SFlowContent.flowSeq 0 .flowOut sp_block sp_flow h_flow))
            h_ssl))))
    (GStar.nil _)

/-- Extend `SLYamlStream` with a top-level flow mapping node + trailing comments.
    The `{...}` analogue of `flowSeq_extends_stream`. -/
lemma flowMap_extends_stream
    (sp_start sp_block sp_flow sp_final : SurfPos)
    (h_stream : SLYamlStream sp_start sp_block)
    (h_flow : SFlowMapping 0 .flowOut sp_block sp_flow)
    (h_ssl : SSLComments sp_flow sp_final) :
    SLYamlStream sp_start sp_final :=
  SLYamlStream.implicitContinue sp_start sp_block sp_block sp_final sp_final
    h_stream (GStar.nil _)
    (GOpt.some sp_block sp_final
      (SLAnyDocument.bare sp_block sp_final
        (SLBareDocument.mk sp_block sp_final
          (SBlockNode.flowInBlock 0 .blockIn sp_block sp_block sp_flow sp_final
            (SSeparateLines.inline 0 sp_block sp_block (SSeparateInLine.startOfLine sp_block))
            (SFlowNode.content 0 .flowOut sp_block sp_flow
              (SFlowContent.flowMap 0 .flowOut sp_block sp_flow h_flow))
            h_ssl))))
    (GStar.nil _)

/-! ## §0c' FlowOpenStack — open flow-collection accumulation (Fix A, Piece 2 / Stage B)

    The invariant component carrying the state of ≥1 OPEN flow collections
    (`sc.flowLevel > 0`). Indexed by depth (= `sc.flowLevel`, for the coupling)
    and by the outer boundary `sp_before` (where the outermost flow started — the
    enclosing context's stream/block ends here) through `sp_cur` (current scan
    position).

    **Per-frame state (B.4 corrected design).** Each open frame carries a full
    `SeqFrame`/`MapFrame` — `between` (a `PartialFlow*`: empty / closeable entries /
    held-after-comma) or `mid` (a `PendingFlow*Entry`: a key/node scanned, entry not
    yet committed). B.1 carried only a between-entries `PartialFlow*` per frame,
    which cannot represent a colon-pending parent hosting a nested value (`{a: [b]}`)
    — every frame, not just the innermost, needs the full state. (The `entries`
    between-state is a genuine rest position: after a nested value closes, e.g. the
    `[b]` in `{a: [b], c}`, the parent rests in `entries` before the next `,`/`}`.)

    **Closure-injection nesting.** A nested frame does NOT store its parent stack
    explicitly; it carries `inject`, a closure built at push time from the parent's
    then-known state, that folds THIS frame's completed node into the parent
    (mirrors `BlockStack.seqLevel`'s `h_close`). The pop is then uniform: close the
    top frame to an `SFlowNode`, then apply `resume` (base, depth 1 → `SLYamlStream`)
    or `inject` (nest, depth d+1 → parent stack). Contexts line up:
    `inFlowCtx .flowOut = inFlowCtx .flowIn = .flowIn`, so every interior node is
    `.flowIn` and only the outermost is `.flowOut` (what `resume` expects).

    The **base** carries a generic `resume` closure that connects the completed
    outermost flow node to `SLYamlStream`. This is what makes the flow↔context
    interaction uniform:
    - top-level flow (`[1,2,3]` as a document): `resume` = `topLevelFlowResumeSep`;
    - block-nested flow (`key: [1,2]`): `resume node ssl = pendingBlock.h_close
      (SBlockNode.flowInBlock … node ssl)`;
    - explicit-document flow (`--- [1,2]`): `resume` routes through
      `pendingDocStart.h_doc_builder` (`GAlt.left ∘ SLBareDocument.mk`).
    (`resume` takes the outer flow node at `.flowOut`, which both `flowInBlock`
    and the bare-document node use.) -/

/-- **Frame tail (9b(ii))** — the class of the last real token the scanner emitted
    into the frame, coarsened to exactly the three cases its two flow guards
    distinguish:

    * `.sep`   — a flow-open indicator (`[`, `{`) or an entry separator (`,`);
                 the frame is `empty` or `held`. `scanFlowEntry` REJECTS a
                 following `,` here (`[,`, `,,` — `invalidFlowEntry`).
    * `.colon` — a `:` (a value is awaited: `{a: `, `[a: `, `{: `).
    * `.value` — a token that completes a flow value (`scalar`, `alias`, `]`,
                 `}` — `YamlToken.completesFlowValue`); the frame holds a
                 finished entry or key. `scanNextToken_checkFlowAdjacency`
                 REJECTS a following node here (`[[a][b]]`, `["a""b"]`).

    Indexing the frames by this class is what lets those two scanner rejections
    refute the degenerate frame shapes: `holdComma` needs `≠ .sep`,
    `receiveNode` needs `≠ .value`. The accumulation invariant pins the index to
    `tailOf sc.tokens`. -/
inductive FrameTail where
  | sep
  | colon
  | value
  deriving DecidableEq, Repr

/-- The frame tail a token dictates. The three `.sep` tokens are exactly the ones
    `scanFlowEntry` rejects a following `,` after; `.value` is exactly
    `YamlToken.completesFlowValue`, which `scanNextToken_checkFlowAdjacency`
    rejects a following node after. -/
def FrameTail.ofToken : YamlToken → FrameTail
  | .flowSequenceStart => .sep
  | .flowMappingStart => .sep
  | .flowEntry => .sep
  | t => if t.completesFlowValue then .value else .colon

/-- The frame tail the scanner's token history dictates. Inside a flow the array
    is never empty (the opening bracket is in it), so the `none` fallback is
    unreachable; `.colon` is the class neither flow guard rejects. -/
def tailOf (tokens : Array (Positioned YamlToken)) : FrameTail :=
  match lastRealTokenVal? tokens with
  | some t => FrameTail.ofToken t
  | none => .colon

/-- Reading off a freshly pushed real token. -/
lemma tailOf_push {tokens : Array (Positioned YamlToken)} {p : Positioned YamlToken}
    (h : p.val ≠ .placeholder) :
    tailOf (tokens.push p) = FrameTail.ofToken p.val ∧ LastTokenReal (tokens.push p) := by
  refine ⟨?_, lastTokenReal_push h⟩
  unfold tailOf
  rw [lastRealTokenVal_push h]

/-- **9b(ii), adjacency side.** `.value` is exactly "the last real token completes
    a flow value", the state `scanNextToken_checkFlowAdjacency` refuses to start a
    node from. -/
lemma tailOf_ne_value {tokens : Array (Positioned YamlToken)}
    (h : ∀ t, lastRealTokenVal? tokens = some t → t.completesFlowValue = false) :
    tailOf tokens ≠ .value := by
  unfold tailOf
  cases hl : lastRealTokenVal? tokens with
  | none => simp
  | some tok =>
    have hc := h tok hl
    simp only []
    unfold FrameTail.ofToken
    split <;> simp_all

/-- **9b(ii), comma side.** `.sep` is exactly "the last real token is `[`, `{` or
    `,`", the state `scanFlowEntry` refuses a `,` after. -/
lemma tailOf_ne_sep {tokens : Array (Positioned YamlToken)}
    (h : ∀ t, lastRealTokenVal? tokens = some t →
      ¬(t = .flowSequenceStart ∨ t = .flowMappingStart ∨ t = .flowEntry)) :
    tailOf tokens ≠ .sep := by
  unfold tailOf
  cases hl : lastRealTokenVal? tokens with
  | none => simp
  | some tok =>
    have hc := h tok hl
    simp only []
    unfold FrameTail.ofToken
    split <;> (try simp_all)
    split <;> simp

/-- The state of one open flow SEQUENCE frame, indexed by its `FrameTail`. The
    seven shapes are the constructors of `PartialFlowSeq` (`between`: empty /
    closeable entries / held-after-comma) and `PendingFlowSeqEntry` (`mid`: a
    node scanned, awaiting `:`, `,`, or close), inlined so each one can name its
    own tail class — a packaged `PartialFlowSeq` would hide which constructor
    built it, and the tail is exactly that information. -/
inductive SeqFrame (n : Nat) (c : YamlContext) : FrameTail → SurfPos → SurfPos → Prop where
  /-- Nothing scanned since `[`. -/
  | betweenEmpty (sp : SurfPos) : SeqFrame n c .sep sp sp
  /-- Closeable entries, no trailing comma. -/
  | betweenEntries (sp sp' : SurfPos) (h : SFlowSeqEntries n c sp sp')
      (hcl : FlowSeqEntriesCloseable h) : SeqFrame n c .value sp sp'
  /-- Entries plus a trailing `,`. -/
  | betweenHeld (sp sp_e sp_c sp' : SurfPos) (h : SFlowSeqEntries n c sp sp_e)
      (hcl : FlowSeqEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : SeqFrame n c .sep sp sp'
  /-- A node scanned: a plain entry, or a pair key if `:` follows. -/
  | midNode (sp sp_d sp' : SurfPos) (pre : FlowSeqPrefix n c sp sp_d)
      (hnode : SFlowNode n c sp_d sp') : SeqFrame n c .value sp sp'
  /-- Pair `:` scanned, value awaited (`[a: `). -/
  | midColon (sp sp_d sp_k sp_s sp' : SurfPos) (pre : FlowSeqPrefix n c sp sp_d)
      (hkey : SFlowNode n c sp_d sp_k) (hsep : GOpt (SSeparate n c) sp_k sp_s)
      (hcolon : GLit ':' sp_s sp') : SeqFrame n c .colon sp sp'
  /-- Explicit `? key` scanned (`[? a`). -/
  | midExplicitKey (sp sp_q sp_qe sp_k0 sp' : SurfPos) (pre : FlowSeqPrefix n c sp sp_q)
      (hq : GLit '?' sp_q sp_qe) (hqsep : SSeparate n c sp_qe sp_k0)
      (hkey : SFlowNode n c sp_k0 sp') : SeqFrame n c .value sp sp'
  /-- Explicit `? key :` scanned, value awaited. -/
  | midExplicitColon (sp sp_q sp_qe sp_k0 sp_k sp_s sp' : SurfPos)
      (pre : FlowSeqPrefix n c sp sp_q) (hq : GLit '?' sp_q sp_qe)
      (hqsep : SSeparate n c sp_qe sp_k0) (hkey : SFlowNode n c sp_k0 sp_k)
      (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
      SeqFrame n c .colon sp sp'

/-- The state of one open flow MAPPING frame (see `SeqFrame`; the extra shape is
    the empty-key pair `{: `). -/
inductive MapFrame (n : Nat) (c : YamlContext) : FrameTail → SurfPos → SurfPos → Prop where
  /-- Nothing scanned since `{`. -/
  | betweenEmpty (sp : SurfPos) : MapFrame n c .sep sp sp
  /-- Closeable entries, no trailing comma. -/
  | betweenEntries (sp sp' : SurfPos) (h : SFlowMapEntries n c sp sp')
      (hcl : FlowMapEntriesCloseable h) : MapFrame n c .value sp sp'
  /-- Entries plus a trailing `,`. -/
  | betweenHeld (sp sp_e sp_c sp' : SurfPos) (h : SFlowMapEntries n c sp sp_e)
      (hcl : FlowMapEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : MapFrame n c .sep sp sp'
  /-- A key node scanned, awaiting `:` or a bare close (`{a}`). -/
  | midKey (sp sp_d sp' : SurfPos) (pre : FlowMapPrefix n c sp sp_d)
      (hkey : SFlowNode n c sp_d sp') : MapFrame n c .value sp sp'
  /-- Mapping `:` scanned, value awaited (`{a: `). -/
  | midColon (sp sp_d sp_k sp_s sp' : SurfPos) (pre : FlowMapPrefix n c sp sp_d)
      (hkey : SFlowNode n c sp_d sp_k) (hsep : GOpt (SSeparate n c) sp_k sp_s)
      (hcolon : GLit ':' sp_s sp') : MapFrame n c .colon sp sp'
  /-- Explicit `? key` scanned (`{? a`). -/
  | midExplicitKey (sp sp_q sp_qe sp_k0 sp' : SurfPos) (pre : FlowMapPrefix n c sp sp_q)
      (hq : GLit '?' sp_q sp_qe) (hqsep : SSeparate n c sp_qe sp_k0)
      (hkey : SFlowNode n c sp_k0 sp') : MapFrame n c .value sp sp'
  /-- Explicit `? key :` scanned, value awaited. -/
  | midExplicitColon (sp sp_q sp_qe sp_k0 sp_k sp_s sp' : SurfPos)
      (pre : FlowMapPrefix n c sp sp_q) (hq : GLit '?' sp_q sp_qe)
      (hqsep : SSeparate n c sp_qe sp_k0) (hkey : SFlowNode n c sp_k0 sp_k)
      (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
      MapFrame n c .colon sp sp'
  /-- Empty-key `:` scanned, value awaited (`{: `). -/
  | midEmptyColon (sp sp_s sp' : SurfPos) (pre : FlowMapPrefix n c sp sp_s)
      (hcolon : GLit ':' sp_s sp') : MapFrame n c .colon sp sp'

/-- **Kinds index (9b(i))**. Besides its depth, `FlowOpenStack` is indexed by the
    *kinds* of its open frames — exactly the scanner's `flowStack` (`true` = a
    sequence opened by `[`, `false` = a mapping opened by `{`), outermost first,
    so the base frames are `#[true]`/`#[false]` and each nest `push`es its own
    marker. The accumulation invariant pins that index to `sc.flowStack`, which
    turns the scanner's 9a flow-close kind check (`flowStack.back? = some true`
    for `]`, `some false` for `}`) into a statement about the top FRAME: a `]`
    reaching a `mapBase`/`mapNest` top is the scan-rejected `{a]`, and a `}`
    reaching a `seqBase`/`seqNest` top is `[a}`. Without it those four arms are
    locally unrefutable — the grammar side alone cannot see which bracket the
    scanner is closing. -/
inductive FlowOpenStack (sp_start : SurfPos) :
    Nat → Array Bool → FrameTail → SurfPos → SurfPos → Prop where
  /-- Outermost open flow sequence (depth 1). The outer boundary `sp_before`
      (where the enclosing context's derivation ends) is DECOUPLED from the
      bracket position `sp_br` — mirroring `seqNest`'s `sp_before0` vs `sp_par`.
      Any leading separation `sp_before → sp_br` is captured inside `resume`
      (its grammar slot depends on the enclosing context: bare document /
      block value / explicit document). -/
  | seqBase (sp_before sp_br sp_open sp_es sp_cur : SurfPos) (tl : FrameTail)
      (resume : ∀ sp_ne sp_mid, SFlowNode 0 .flowOut sp_br sp_ne →
                SSLComments sp_ne sp_mid → SLYamlStream sp_start sp_mid)
      (h_open : GLit '[' sp_br sp_open)
      (h_sep : GOpt (SSeparate 0 .flowOut) sp_open sp_es)
      (st : SeqFrame 0 (inFlowCtx .flowOut) tl sp_es sp_cur) :
      FlowOpenStack sp_start 1 #[true] tl sp_before sp_cur
  /-- Outermost open flow mapping (depth 1; see `seqBase` on `sp_before`/`sp_br`). -/
  | mapBase (sp_before sp_br sp_open sp_es sp_cur : SurfPos) (tl : FrameTail)
      (resume : ∀ sp_ne sp_mid, SFlowNode 0 .flowOut sp_br sp_ne →
                SSLComments sp_ne sp_mid → SLYamlStream sp_start sp_mid)
      (h_open : GLit '{' sp_br sp_open)
      (h_sep : GOpt (SSeparate 0 .flowOut) sp_open sp_es)
      (st : MapFrame 0 (inFlowCtx .flowOut) tl sp_es sp_cur) :
      FlowOpenStack sp_start 1 #[false] tl sp_before sp_cur
  /-- A nested open flow sequence (depth d+1) inside a receptive parent. The
      `inject` closure folds this frame's completed `.flowIn` node into the parent
      stack (built at push time from the parent's then-known state). -/
  | seqNest (d : Nat) (ks : Array Bool) (tl : FrameTail)
      (sp_before0 sp_par sp_open sp_es sp_cur : SurfPos)
      (inject : ∀ sp_ne, SFlowNode 0 .flowIn sp_par sp_ne →
                FlowOpenStack sp_start d ks .value sp_before0 sp_ne)
      (h_open : GLit '[' sp_par sp_open)
      (h_sep : GOpt (SSeparate 0 .flowIn) sp_open sp_es)
      (st : SeqFrame 0 (inFlowCtx .flowIn) tl sp_es sp_cur) :
      FlowOpenStack sp_start (d + 1) (ks.push true) tl sp_before0 sp_cur
  /-- A nested open flow mapping (depth d+1). -/
  | mapNest (d : Nat) (ks : Array Bool) (tl : FrameTail)
      (sp_before0 sp_par sp_open sp_es sp_cur : SurfPos)
      (inject : ∀ sp_ne, SFlowNode 0 .flowIn sp_par sp_ne →
                FlowOpenStack sp_start d ks .value sp_before0 sp_ne)
      (h_open : GLit '{' sp_par sp_open)
      (h_sep : GOpt (SSeparate 0 .flowIn) sp_open sp_es)
      (st : MapFrame 0 (inFlowCtx .flowIn) tl sp_es sp_cur) :
      FlowOpenStack sp_start (d + 1) (ks.push false) tl sp_before0 sp_cur

-- NB (B.4): the base-close helpers `flowSeqBase_closeToStream` /
-- `flowMapBase_closeToStream` (B.1) took a between-entries `p : PartialFlow*` and
-- closed it directly. With the corrected per-frame `SeqFrame`/`MapFrame` state, the
-- close must first complete any `mid` entry (sep-sensitive; its exact separator
-- signature is only pinned by how the accum step threads scan positions). Rebuilt
-- in B.4b alongside `accum_flow_pending`.

/-- The base `resume` for a TOP-LEVEL flow document node: the completed flow node
    is a bare document that extends the stream (via `implicitContinue`). The
    leading separation `sp_mid → sp_br` (from the stream's endpoint to the
    bracket) rides in the bare document's `flowInBlock` separator slot — the
    zero-width `SSeparateLines.inline ∘ startOfLine` recovers the old
    stream-at-the-bracket special case. -/
lemma topLevelFlowResumeSep {sp_start sp_mid sp_br : SurfPos}
    (h_stream : SLYamlStream sp_start sp_mid)
    (h_sep : SSeparateLines 0 sp_mid sp_br) :
    ∀ sp_ne sp_m, SFlowNode 0 .flowOut sp_br sp_ne →
      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m :=
  fun sp_ne sp_m h_node h_ssl =>
    SLYamlStream.implicitContinue sp_start sp_mid sp_mid sp_m sp_m
      h_stream (GStar.nil _)
      (GOpt.some sp_mid sp_m
        (SLAnyDocument.bare sp_mid sp_m
          (SLBareDocument.mk sp_mid sp_m
            (SBlockNode.flowInBlock 0 .blockIn sp_mid sp_br sp_ne sp_m
              h_sep h_node h_ssl))))
      (GStar.nil _)

/-! ### §0c'' FlowOpenStack push operations + depth-indexed FlowStackB (Stage B)

    The Stage-B accumulation invariant replaces the trivial nil-only `FlowStack`
    with `FlowStackB`, indexed by *depth* and by the open frames' *kinds*. The
    depth index is coupled to the scanner's `flowLevel` (nil ↔ flowLevel 0; open
    at depth d ↔ flowLevel d), so the accum steps can branch on flow-interior vs.
    document handling without a separate coupling conjunct; the kinds index is
    coupled to `flowStack` itself (9b(i)), which is what makes the scanner's
    flow-close kind check visible to the grammar side. `absorb_stacksB` fires
    only at depth 0. -/

/-- `FlowOpenStack` always has positive depth (the base constructors are depth 1). -/
lemma FlowOpenStack_depth_pos {sp_start : SurfPos} {d : Nat} {ks : Array Bool}
    {tl : FrameTail} {a b : SurfPos} (h : FlowOpenStack sp_start d ks tl a b) : d ≥ 1 := by
  cases h <;> omega

-- NB (B.4): the nested-push helpers `pushSeq`/`pushMap` (B.1) attached a child
-- frame onto an explicit `below : FlowOpenStack`. With closure-injection nesting the
-- child instead carries an `inject` closure built from the parent's then-known state
-- (between → child becomes key/entry ⇒ `midKey`/`midNode`; `midColon` →
-- child becomes value ⇒ `appendMapEntryFrame`/`appendSeqEntryFrame`). That closure is
-- state-dependent, so the push is rebuilt in B.4b where the parent state is in hand.

/-- Depth-indexed flow stack carrying the open-flow accumulator (Stage B).
    Replaces the trivial nil-only `FlowStack`. `nil` (depth 0) means no flow
    is open; `open` (depth d ≥ 1) carries a `FlowOpenStack`. -/
inductive FlowStackB (sp_start : SurfPos) :
    Nat → Array Bool → FrameTail → SurfPos → SurfPos → Prop where
  /-- No flow open. The frame-tail index is unconstrained: with no frame there is
      nothing for the scanner's token history to describe, so every depth-0 accum
      step can re-establish the invariant at whatever tail its own token history
      happens to read (`FlowStackB.retail`). -/
  | nil (sp : SurfPos) (tl : FrameTail) : FlowStackB sp_start 0 #[] tl sp sp
  | open (d : Nat) (ks : Array Bool) (tl : FrameTail) (sp_block sp_cur : SurfPos)
      (h : FlowOpenStack sp_start d ks tl sp_block sp_cur) :
      FlowStackB sp_start d ks tl sp_block sp_cur

/-- Re-index a depth-0 (necessarily `nil`) flow stack at any frame tail. -/
lemma FlowStackB.retail {sp_start : SurfPos} {ks : Array Bool} {tl tl' : FrameTail}
    {a b : SurfPos} (h : FlowStackB sp_start 0 ks tl a b) :
    FlowStackB sp_start 0 ks tl' a b := by
  cases h with
  | nil => exact .nil _ _
  | «open» _ _ _ _ _ hfo => exact absurd (FlowOpenStack_depth_pos hfo) (by omega)

/-- At depth 0 the kinds index is empty: the `open` constructor needs a positive
    depth. This is what lets a depth-0 accum step discharge the `flowStack`
    component of the invariant it must re-establish. -/
lemma FlowStackB.kinds_nil_of_depth_zero {sp_start : SurfPos} {ks : Array Bool}
    {tl : FrameTail} {a b : SurfPos} (h : FlowStackB sp_start 0 ks tl a b) : ks = #[] := by
  cases h with
  | nil => rfl
  | «open» _ _ _ _ _ hfo => exact absurd (FlowOpenStack_depth_pos hfo) (by omega)

/-- At depth 0 the accumulator is `nil`, so its two position indices coincide. -/
lemma FlowStackB.pos_eq_of_depth_zero {sp_start : SurfPos} {ks : Array Bool}
    {tl : FrameTail} {a b : SurfPos} (h : FlowStackB sp_start 0 ks tl a b) : a = b := by
  cases h with
  | nil => rfl
  | «open» _ _ _ _ _ hfo => exact absurd (FlowOpenStack_depth_pos hfo) (by omega)

/-- Recover the open accumulator at positive depth. -/
lemma FlowStackB.open_of_succ {sp_start : SurfPos} {d : Nat} {ks : Array Bool}
    {tl : FrameTail} {a b : SurfPos} (h : FlowStackB sp_start (d + 1) ks tl a b) :
    FlowOpenStack sp_start (d + 1) ks tl a b := by
  cases h with | «open» _ _ _ _ _ hfo => exact hfo

/-- Absorb BlockStack + a CLOSED (`nil`, depth 0) `FlowStackB` into the stream.
    The `open` case is vacuous at depth 0 (`FlowOpenStack` has positive depth). -/
lemma absorb_stacksB (sp_start sp_gram sp_block sp_flow : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    {ks : Array Bool} {tl : FrameTail}
    (h_flow : FlowStackB sp_start 0 ks tl sp_block sp_flow) : SLYamlStream sp_start sp_flow := by
  cases h_flow with
  | nil =>
    cases h_stack with
    | nil => exact h_stream
    | seqLevel _ _ _ _ _ h_cl_b => exact h_cl_b sp_start h_stream
    | mapLevel _ _ _ _ _ h_cl_b => exact h_cl_b sp_start h_stream
  | «open» _ _ _ _ _ h => exact absurd (FlowOpenStack_depth_pos h) (by omega)

/-- Open the OUTERMOST flow SEQUENCE `[` (nil → depth-1 open), given the base
    `resume` closure for the enclosing context (top-level / block value /
    explicit document). The bracket sits at `sp_br`; the outer boundary
    `sp_before` (where the enclosing derivation ends) is free — any gap
    `sp_before → sp_br` lives inside `resume`. -/
lemma FlowStackB.openSeqBase {sp_start sp_before sp_br sp_open sp_es : SurfPos}
    (resume : ∀ sp_ne sp_m, SFlowNode 0 .flowOut sp_br sp_ne →
              SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m)
    (h_open : GLit '[' sp_br sp_open)
    (h_sep : GOpt (SSeparate 0 .flowOut) sp_open sp_es) :
    FlowStackB sp_start 1 #[true] .sep sp_before sp_es :=
  .open 1 #[true] .sep sp_before sp_es
    (.seqBase sp_before sp_br sp_open sp_es sp_es .sep resume h_open h_sep
      (.betweenEmpty sp_es))

/-- Open the outermost flow MAPPING `{` (nil → depth-1 open). -/
lemma FlowStackB.openMapBase {sp_start sp_before sp_br sp_open sp_es : SurfPos}
    (resume : ∀ sp_ne sp_m, SFlowNode 0 .flowOut sp_br sp_ne →
              SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m)
    (h_open : GLit '{' sp_br sp_open)
    (h_sep : GOpt (SSeparate 0 .flowOut) sp_open sp_es) :
    FlowStackB sp_start 1 #[false] .sep sp_before sp_es :=
  .open 1 #[false] .sep sp_before sp_es
    (.mapBase sp_before sp_br sp_open sp_es sp_es .sep resume h_open h_sep
      (.betweenEmpty sp_es))

/-- Close any PendingNode to SLYamlStream using SSLComments evidence.

    Centralizes the per-constructor closing strategies that were previously
    duplicated across `eof_pending`, `accum_structural_pending`,
    `accum_flow_pending`, `accum_block_pending`, and `accum_content_pending`
    (Wadler-style Pattern 6: parametric closing).

    Each constructor contributes only its closing strategy:
    - `noPending`: stream at `sp_block = sp_scan`, extend past SSLComments
    - `pendingContent`/`pendingFlow`/`pendingBlockContent`: delegate to `h_closable`
    - `pendingDocEnd`: build `SLDocumentSuffix` + `SLYamlStream.suffixContinue`
    - `pendingDocStart`: apply `h_doc_builder` + `SLYamlStream.implicitContinue`
    - `pendingBlock`: close with `SBlockNode.emptyNode` via `h_close`
    (`pendingDirective` is `true`-indexed and cannot occur here — Fix B) -/
lemma PendingNode.close_with_ssl
    {sp_start sp_block sp_scan sp_mid : SurfPos}
    (h_pending : PendingNode false sp_start sp_block sp_scan)
    (h_stream : SLYamlStream sp_start sp_block)
    (h_ssl : SSLComments sp_scan sp_mid) :
    SLYamlStream sp_start sp_mid := by
  cases h_pending with
  | noPending =>
    exact ssl_comments_extend_stream sp_start sp_block sp_mid h_stream h_ssl
  | pendingContent =>
    rename_i h_closable
    exact h_closable sp_mid h_ssl
  | pendingFlow =>
    -- Absorb opaque scanner content (flow/block indicators) via scannerDrop.
    exact SLYamlStream.scannerDrop sp_start sp_block sp_scan sp_mid h_stream h_ssl
  | pendingBlockContent =>
    rename_i _ h_closable _
    exact h_closable sp_mid h_ssl
  | pendingDocEnd =>
    rename_i h_marker
    exact SLYamlStream.suffixContinue sp_start sp_block sp_mid sp_mid sp_mid sp_mid
      h_stream (GPlus.mk sp_block sp_mid sp_mid
        (SLDocumentSuffix.mk sp_block sp_scan sp_mid h_marker h_ssl) (GStar.nil _))
      (GStar.nil _) (GOpt.none _) (GStar.nil _)
  | pendingDocStart =>
    rename_i h_doc_builder
    exact SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
      h_stream (GStar.nil _)
      (GOpt.some sp_block sp_mid
        (h_doc_builder sp_mid
          (GAlt.right sp_scan sp_mid
            (GSeq.mk sp_scan sp_scan sp_mid (GEps.mk sp_scan) h_ssl))))
      (GStar.nil _)
  | pendingBlock =>
    rename_i h_close _
    exact h_close sp_mid (SBlockNode.emptyNode 0 .blockIn sp_scan sp_mid h_ssl)

/-! ## §0d Preprocessing → SSLComments for `some` result at col=0

    When `scanNextToken_preprocess` returns `some (s_prep, c)` and the
    scanner starts at col=0, the characters consumed by `skipToContent`
    form `SSLComments`. This is the key building block for closing pending
    nodes: the SSLComments is provided to `h_closable` of the previous
    `PendingNode` to extend the stream.

    The `sp_mid` returned is the SSLComments boundary (where comment lines
    end), and `sp_prep` is the scanner's final position (which may be past
    `sp_mid` due to trailing whitespace from the last `skipToContent` iteration). -/

/-- When preprocessing returns `some` at col=0, extract `SSLComments` from the
    consumed characters plus `ScannerSurfCorr` for the resulting state. -/
lemma preprocess_some_ssl_comments_col0 (sc : ScannerState) (sp : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_mid sp_ws sp_prep, SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
                      GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp_prep ∧
                      ScannerSurfCorr s_prep sp_prep ∧
                      (sp_prep = sp_ws ∨ s_prep.peek? = none) := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, hcorr_sc, h_pk⟩ :=
      skipToContent_startOfLine_comments_prod sc sp s_content hcorr hcol h_skip
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            have hcorr2 := unwindIndents_corr_exact s_content sp_sc hcorr_sc (↑s_content.col)
            have hcorr3 : ScannerSurfCorr
                { (unwindIndents s_content ↑s_content.col) with
                  needIndentCheck := false } sp_sc :=
              ⟨hcorr2.chars_from, hcorr2.col_eq, hcorr2.end_eq, hcorr2.input_prefix, hcorr2.indent_cols_nonneg⟩
            exact ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, saveSimpleKey_corr _ sp_sc hcorr3,
                   h_pk.imp_right (fun h => by
                     rw [saveSimpleKey_peek]; unfold ScannerState.peek? unwindIndents
                     simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd, unwindIndentsLoop_input]
                     unfold ScannerState.peek? at h; exact h)⟩
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            exact ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, saveSimpleKey_corr _ sp_sc hcorr_sc,
                   h_pk.imp_right (fun h => by rw [saveSimpleKey_peek]; exact h)⟩

/-- When `scanNextToken_preprocess` returns `some (s_prep, c)`, the resulting
    scanner state has `s_prep.peek? = some c`. This follows from the definition's
    final `match s.peek? with | some c => return some (s, c)`. -/
lemma preprocess_some_peek {sc s_prep : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.peek? = some c := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok  -- skipToContent
  · simp at hok
  · split at hok  -- hasMore
    · simp at hok
    · split at hok  -- indent handling
      all_goals (  -- both indent branches have identical structure
        split at hok  -- trailing content check
        <;> (try simp at hok)  -- error case
        <;> (split at hok  -- peek? match
          <;> (try simp at hok)  -- none case
          <;> (obtain ⟨h1, h2⟩ := hok; subst h1; subst h2; assumption)))

-- The preprocessing character is never a line break. This follows from
-- `skipToContentLoop` continuing past breaks and only stopping at non-break chars.
lemma preprocess_some_not_break {sc s_prep : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    isLineBreakBool c = false := by
  have hpeek := preprocess_some_peek hok  -- s_prep.peek? = some c
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    split at hok
    · simp at hok
    · -- Derive s_content.peek? = some c by tracing peek? preservation
      -- through unwindIndents + saveSimpleKey + indent handling
      have h_sc_peek : s_content.peek? = some c := by
        split at hok  -- indent handling (two branches)
        all_goals (
          split at hok  -- trailing content check
          <;> (try simp at hok)
          <;> (split at hok  -- peek? match
            <;> (try simp at hok)
            <;> (obtain ⟨h1, _⟩ := hok; subst h1
                 first
                 | (-- indent branch: strip saveSimpleKey + unwindIndents
                    rw [saveSimpleKey_peek] at hpeek
                    unfold ScannerState.peek? unwindIndents at hpeek
                    simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd,
                      unwindIndentsLoop_input] at hpeek
                    exact hpeek)
                 | (-- no-indent branch: strip saveSimpleKey only
                    rw [saveSimpleKey_peek] at hpeek; exact hpeek))))
      exact skipToContent_peek_not_break sc s_content c h_skip h_sc_peek

/-- Preprocessing at col=0 with content character produces `SSeparateLines 0`.

    This wraps `preprocess_some_ssl_comments_col0` by converting
    `SSLComments + GStar SSWhite` into `SSeparateLines.commented 0`
    using `SFlowLinePrefix 0` (zero-indent + optional whitespace).

    **GOpt.some case**: When `preprocess_some_ssl_comments_col0` returns
    `GOpt.some (SCNbCommentText)`, the scanner consumed a `#` comment in the
    final `skipToContentLoop` iteration. This case is unreachable when
    `scanNextToken_preprocess` returns `some (s_prep, c)` because:
    - After `collectCommentTextLoop`, `peek?` returns break or EOF
      (by `collectCommentTextLoop_stops_at_break_or_eof`)
    - But `scanNextToken_preprocess` returned content, meaning `peek?` found
      a non-break character (the loop's stopping condition)
    - These are contradictory

    The contradiction requires connecting the scanner's `peek?` through
    `skipToContentComment` → `unwindIndents` → `saveSimpleKey` state
    preservation chain. Currently deferred as a non-structural sorry. -/
lemma preprocess_some_separate_lines_0 (sc : ScannerState) (sp : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_prep, SSeparateLines 0 sp sp_prep ∧ ScannerSurfCorr s_prep sp_prep := by
  obtain ⟨sp_mid, sp_ws, sp_prep, h_ssl, hcol_mid, h_ws, h_cmt, hcorr_out, h_pk⟩ :=
    preprocess_some_ssl_comments_col0 sc sp s_prep c hcorr hcol hok
  -- Resolve the peek disjunction: sp_prep = sp_ws (since peek? ≠ none)
  have h_eq : sp_prep = sp_ws := by
    cases h_pk with
    | inl h => exact h
    | inr h => rw [preprocess_some_peek hok] at h; cases h
  cases h_cmt with
  | none =>
    -- GOpt.none: sp_ws = sp_prep. Build SSeparateLines.commented 0.
    exact ⟨sp_ws,
      SSeparateLines.commented 0 sp sp_mid sp_ws h_ssl
        (SFlowLinePrefix.mk 0 sp_mid sp_mid sp_ws (SIndent.zero sp_mid)
          (ScalarProduction.gstar_sswhite_to_gopt_sep h_ws)),
      h_eq ▸ hcorr_out⟩
  | some _ h =>
    -- GOpt.some: unreachable — SCNbCommentText sp_ws sp_ws is impossible
    have : SCNbCommentText sp_ws sp_ws := h_eq ▸ h
    exact absurd this (scNbCommentText_irrefl sp_ws)

/-- General-column version of `preprocess_some_ssl_comments_col0`.
    When preprocessing returns `some`, extract `SSLComments` disjunction plus
    `GStar SSWhite` and `ScannerSurfCorr`. No col=0 requirement. -/
lemma preprocess_some_ssl_comments_anyCol (sc : ScannerState) (sp : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_mid sp_ws sp_prep,
      (SSLComments sp sp_mid ∧ sp_mid.col = 0 ∨ sp_mid = sp) ∧
      GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp_prep ∧
      ScannerSurfCorr s_prep sp_prep ∧
      (sp_prep = sp_ws ∨ s_prep.peek? = none) := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    obtain ⟨sp_mid, sp_ws, sp_sc, h_disj, hws, hcmt, hcorr_sc, h_pk⟩ :=
      skipToContent_anyCol_prod sc sp s_content hcorr h_skip
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            have hcorr2 := unwindIndents_corr_exact s_content sp_sc hcorr_sc (↑s_content.col)
            have hcorr3 : ScannerSurfCorr
                { (unwindIndents s_content ↑s_content.col) with
                  needIndentCheck := false } sp_sc :=
              ⟨hcorr2.chars_from, hcorr2.col_eq, hcorr2.end_eq, hcorr2.input_prefix, hcorr2.indent_cols_nonneg⟩
            exact ⟨sp_mid, sp_ws, sp_sc, h_disj, hws, hcmt, saveSimpleKey_corr _ sp_sc hcorr3,
                   h_pk.imp_right (fun h => by
                     rw [saveSimpleKey_peek]; unfold ScannerState.peek? unwindIndents
                     simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd, unwindIndentsLoop_input]
                     unfold ScannerState.peek? at h; exact h)⟩
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            exact ⟨sp_mid, sp_ws, sp_sc, h_disj, hws, hcmt, saveSimpleKey_corr _ sp_sc hcorr_sc,
                   h_pk.imp_right (fun h => by rw [saveSimpleKey_peek]; exact h)⟩

/-- General-column `SSeparateLines 0` from preprocessing with content.
    Works at any starting column — uses nil `SSLComments` when no break consumed,
    and `SIndent 0` (zero-width) which has no column requirement. -/
lemma preprocess_some_separate_0_anyCol (sc : ScannerState) (sp : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_prep, SSeparateLines 0 sp sp_prep ∧ ScannerSurfCorr s_prep sp_prep := by
  obtain ⟨sp_mid, sp_ws, sp_prep, h_disj, h_ws, h_cmt, hcorr_out, h_pk⟩ :=
    preprocess_some_ssl_comments_anyCol sc sp s_prep c hcorr hok
  -- Resolve the peek disjunction: sp_prep = sp_ws (since peek? ≠ none)
  have h_eq : sp_prep = sp_ws := by
    cases h_pk with
    | inl h => exact h
    | inr h => rw [preprocess_some_peek hok] at h; cases h
  cases h_cmt with
  | none =>
    cases h_disj with
    | inl h_ssl_col =>
      exact ⟨sp_ws,
        SSeparateLines.commented 0 sp sp_mid sp_ws h_ssl_col.1
          (SFlowLinePrefix.mk 0 sp_mid sp_mid sp_ws (SIndent.zero sp_mid)
            (ScalarProduction.gstar_sswhite_to_gopt_sep h_ws)),
        h_eq ▸ hcorr_out⟩
    | inr h_mid_eq =>
      rw [h_mid_eq] at h_ws
      -- No break consumed (sp_mid = sp). Build SSeparateInLine from GStar SSWhite.
      exact ⟨sp_ws,
        SSeparateLines.inline 0 sp sp_ws
          (GStar_SSWhite_to_SSeparateInLine sp sp_ws h_ws),
        h_eq ▸ hcorr_out⟩
  | some _ h =>
    -- GOpt.some: unreachable — SCNbCommentText sp_ws sp_ws is impossible
    have : SCNbCommentText sp_ws sp_ws := h_eq ▸ h
    exact absurd this (scNbCommentText_irrefl sp_ws)

/-- Flow-open threading: when preprocessing returns `some`, either a CLOSE POINT
    exists — `SSLComments sp_scan sp_mid` (a line break was crossed, or col-0
    zero-width start-of-line) followed by residual whitespace to the content
    char — or no break was crossed at col ≠ 0 (the prior construct cannot be
    closed here; the whitespace evidence still covers the full gap).
    Used by `accum_flow_open_depth0` to close the incoming pending before a
    depth-0 `[`/`{` and to place the residual separation in the fresh bare
    document's separator slot. -/
lemma preprocess_flow_thread (sc : ScannerState) (sp_scan sp_prep : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    (∃ sp_mid, SSLComments sp_scan sp_mid ∧ GStar SSWhite sp_mid sp_prep) ∨
    (sp_scan.col ≠ 0 ∧ GStar SSWhite sp_scan sp_prep) := by
  obtain ⟨sp_mid, sp_ws, sp_gap, h_disj, hws, _, hcorr_gap, h_pk⟩ :=
    preprocess_some_ssl_comments_anyCol sc sp_scan s_prep c h_corr h_preprocess
  have h_gap_eq : sp_gap = sp_prep := ScannerSurfCorr_unique hcorr_gap hcorr_prep
  have h_ws_eq : sp_ws = sp_prep := by
    cases h_pk with
    | inl h => exact h.symm.trans h_gap_eq
    | inr h => rw [preprocess_some_peek h_preprocess] at h; cases h
  rw [h_ws_eq] at hws
  cases h_disj with
  | inl h => exact Or.inl ⟨sp_mid, h.1, hws⟩
  | inr h_eq =>
    rw [h_eq] at hws
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨chars, colv⟩ := sp_scan
      have hc0 : colv = 0 := hcol
      subst hc0
      exact Or.inl ⟨⟨chars, 0⟩, SSLComments.startOfLine chars ⟨chars, 0⟩ (GStar.nil _), hws⟩
    · exact Or.inr ⟨hcol, hws⟩

/-! ## §1 Per-Dispatch Grammar Accumulator Lemmas

    Each dispatcher has a sorry lemma that:
    1. Closes the previous `PendingNode` using `SSLComments` from preprocessing
    2. May pop `BlockStack` levels if `unwindIndents` fired (dedent)
    3. May push `BlockStack` levels if `pushSequenceIndent`/`pushMappingIndent` fired
    4. Opens a new `PendingNode` for the dispatched token
    5. Extends `SLYamlStream` as needed (dedent closures, document boundaries)

    ### §1a Preprocessing + EOF

    When `scanNextToken_preprocess` returns `none`, the scanner reached EOF.
    Close all pending state — unwind entire BlockStack, close PendingNode,
    and finalize the stream.

    **Proven case**: `BlockStack.nil` + `PendingNode.noPending` (any column).
    Uses `preprocess_none_ssl_comments` → `ssl_comments_extend_stream`.

    **Sorry case**: non-nil stack/pending (from §1b–§1e).
    The non-nil stack/pending cases are downstream of §1b–§1e sorry. -/

-- Helper: handles all PendingNode cases for EOF given stream at sp_block.
lemma eof_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode false sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  obtain ⟨sp_final, h_ssl, h_empty⟩ :=
    preprocess_none_ssl_comments sc sp_scan h_corr h_preprocess
  exact ⟨sp_final, h_pending.close_with_ssl h_stream_block h_ssl, h_empty⟩

lemma preprocessing_eof_extends_stream (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    {ks : Array Bool} {tl : FrameTail}
    (h_flow : FlowStackB sp_start 0 ks tl sp_block sp_flow)
    (h_pending : PendingNode false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  exact eof_pending sc sp_start sp_flow sp_scan
    (absorb_stacksB sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
    h_pending h_corr h_preprocess

-- Helper: `ScannerSurfCorr` is preserved by the `allowDirectives` flag update
-- used between structural dispatch and block/flow/content dispatch.
lemma corr_of_allowDirectives_update {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr
      (if sc.allowDirectives then
        { sc with allowDirectives := false, documentEverStarted := true }
      else sc) sp := by
  split
  · exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  · exact hcorr

-- Helper (B.4β): the `allowDirectives` flag update between structural dispatch
-- and block/flow/content dispatch touches neither `flowLevel` nor `tokens`.
lemma allowDirectives_update_flowLevel (s : ScannerState) :
    (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true }
    else s).flowLevel = s.flowLevel := by
  split <;> rfl

-- Helper (9b(i)): the same update leaves `flowStack` alone.
lemma allowDirectives_update_flowStack (s : ScannerState) :
    (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true }
    else s).flowStack = s.flowStack := by
  split <;> rfl

/-- Helper (β.3): the same update always LANDS on `allowDirectives = false` —
    the `then` branch sets it, the `else` branch is taken only when it is already
    false. This is what makes "a directive cannot appear inside an open flow"
    provable: every flow indicator, block indicator and content token is
    dispatched AFTER this update, so any state that opened a flow has the flag
    cleared, and `scanDirective` rejects on `!allowDirectives`. -/
lemma allowDirectives_update_false (s : ScannerState) :
    (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true }
    else s).allowDirectives = false := by
  split
  · rfl
  · rename_i h; simpa using h

-- Helper (B.4β): `scanNextToken_preprocess` preserves `flowLevel`. Replicated
-- from `EmitterScannability.preprocess_preserves_flowLevel` (that module is not
-- in this file's import closure) via the reachable `ScannerCorrectness.*`
-- primitives (skipToContent / unwindIndents / saveSimpleKey).
lemma preprocess_preserves_flowLevel (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    s1.flowLevel = s.flowLevel := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_fl_skip := ScannerCorrectness.skipToContent_preserves_flowLevel s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [ScannerCorrectness.saveSimpleKey_preserves_flowLevel]
            show (unwindIndents s_skip s_skip.col).flowLevel = s.flowLevel
            rw [ScannerCorrectness.unwindIndents_preserves_flowLevel]; exact h_fl_skip
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [ScannerCorrectness.saveSimpleKey_preserves_flowLevel]; exact h_fl_skip

/-! ### §1b Preprocessing + Structural Dispatch

    `scanNextToken_dispatchStructural` handles `---`, `...`, `%`-directives.
    Preprocessing provides SSLComments to close the previous pending node.
    If indent levels decreased, BlockStack pops accordingly.
    The structural token opens a new pending state.

    **Proven case**: `BlockStack.nil` + `PendingNode.noPending`.
    No pending to close. Structural dispatch preserves corr via
    `dispatchStructural_corr`. Opens appropriate pending state. -/

-- Helper: structural dispatch preserves `ScannerSurfCorr` on `some` paths.
lemma dispatchStructural_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_dispatchStructural sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- Flow indent guard
  split at hok
  · split at hok
    · simp at hok
    · -- passes guard; fall through
      split at hok
      · simp at hok  -- documentMarkerInFlow error
      · split at hok
        · have h := Except.ok.inj hok; injection h with h; subst h
          exact scanDocumentStart_corr sc sp hcorr
        · split at hok
          · split at hok
            · simp at hok
            · rename_i s_de hde
              have h := Except.ok.inj hok; injection h with h; subst h
              exact scanDocumentEnd_corr sc sp hcorr s_de hde
          · split at hok
            · split at hok
              · simp at hok
              · rename_i s_dir hdir
                have h := Except.ok.inj hok; injection h with h; subst h
                exact scanDirective_corr sc sp hcorr s_dir hdir
            · simp at hok  -- none case
  · -- not inFlow or indent ok; same dispatch
    split at hok
    · simp at hok
    · split at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanDocumentStart_corr sc sp hcorr
      · split at hok
        · split at hok
          · simp at hok
          · rename_i s_de hde
            have h := Except.ok.inj hok; injection h with h; subst h
            exact scanDocumentEnd_corr sc sp hcorr s_de hde
        · split at hok
          · split at hok
            · simp at hok
            · rename_i s_dir hdir
              have h := Except.ok.inj hok; injection h with h; subst h
              exact scanDirective_corr sc sp hcorr s_dir hdir
          · simp at hok  -- none

-- Helper (4f.2): structural dispatch at a position produces marker evidence.
-- Every `.ok (some _)` branch of `scanNextToken_dispatchStructural` requires
-- `s.col = 0`, and the marker is either `SCDirectivesEnd` (for `---`) or
-- `SCDocumentEnd` (for `...`). Directive (`%`) produces pendingDirective
-- with `h_dir_acc` closure from `scanDirective_prod`.
lemma structural_dispatch_to_pending
    (s_prep s' : ScannerState) (c : Char) (sp_start sp : SurfPos)
    (hcorr : ScannerSurfCorr s_prep sp)
    (hpeek : s_prep.peek? = some c)
    (h_stream : SLYamlStream sp_start sp)
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp' b', sp.col = 0 ∧ PendingNode b' sp_start sp sp' ∧
      (b' = true → s'.directivesPresent = true) ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchStructural at h_dispatch
  simp only [bind, Except.bind, pure, Except.pure] at h_dispatch
  -- Reusable subproof for document-start branches
  suffices doc_start_tac : ∀ (hat : atDocumentStart s_prep = true)
      (hcol_s : s_prep.col = 0) (_ : s' = scanDocumentStart s_prep),
      ∃ sp' b', sp.col = 0 ∧ PendingNode b' sp_start sp sp' ∧
        (b' = true → s'.directivesPresent = true) ∧ ScannerSurfCorr s' sp' by
    -- Reusable subproof for document-end branches
    suffices doc_end_tac : ∀ (hat : atDocumentEnd s_prep = true)
        (s_de : ScannerState) (hde : scanDocumentEnd s_prep = .ok s_de)
        (_ : s' = s_de),
        ∃ sp' b', sp.col = 0 ∧ PendingNode b' sp_start sp sp' ∧
          (b' = true → s'.directivesPresent = true) ∧ ScannerSurfCorr s' sp' by
      -- Dispatch case splitting
      split at h_dispatch
      · split at h_dispatch
        · simp at h_dispatch
        · split at h_dispatch
          · simp at h_dispatch
          · split at h_dispatch
            · -- atDocumentStart (inFlow)
              rename_i _ _ _ h_cond
              rw [Bool.and_eq_true] at h_cond
              have h := Except.ok.inj h_dispatch; injection h with h
              exact doc_start_tac h_cond.2 (beq_iff_eq.mp h_cond.1) h.symm
            · -- atDocumentEnd (inFlow): use by_cases to preserve condition
              by_cases h_docEnd : (s_prep.col == 0 && atDocumentEnd s_prep) = true
              · rw [if_pos h_docEnd] at h_dispatch
                rw [Bool.and_eq_true] at h_docEnd
                split at h_dispatch
                · simp at h_dispatch
                · rename_i s_de hde
                  have h := Except.ok.inj h_dispatch; injection h with h
                  exact doc_end_tac h_docEnd.2 s_de hde h.symm
              · rw [if_neg h_docEnd] at h_dispatch
                by_cases h_dir : (c == '%' && s_prep.col == 0) = true
                · rw [if_pos h_dir] at h_dispatch
                  rw [Bool.and_eq_true] at h_dir
                  split at h_dispatch
                  · simp at h_dispatch
                  · rename_i s_dir h_dir_ok
                    have h := Except.ok.inj h_dispatch; injection h with h; subst h
                    have hcol : sp.col = 0 := by rw [hcorr.col_eq]; exact beq_iff_eq.mp h_dir.2
                    have hpeek_pct : s_prep.peek? = some '%' := by
                      rw [show c = '%' from beq_iff_eq.mp h_dir.1] at hpeek; exact hpeek
                    obtain ⟨rest, sp_dir, hchars, hgstar, hcorr_dir, h_at_break⟩ :=
                      scanDirective_prod s_prep sp hcorr hpeek_pct s_dir h_dir_ok
                    refine ⟨sp_dir, true, hcol,
                      PendingNode.pendingDirective sp_start sp sp_dir
                        (fun sp_mid hssl => ?_)
                        h_stream,
                      fun _ => scanDirective_directivesPresent h_dir_ok,
                      hcorr_dir⟩
                    obtain ⟨sp_chars, sp_col⟩ := sp
                    subst hchars
                    exact GPlus.mk _ sp_mid sp_mid
                      (SLDirective.mk rest sp_col sp_dir sp_mid hgstar hssl) (GStar.nil _)
                · rw [if_neg h_dir] at h_dispatch
                  simp at h_dispatch
      · split at h_dispatch
        · simp at h_dispatch
        · split at h_dispatch
          · -- atDocumentStart (not inFlow)
            rename_i _ _ h_cond
            rw [Bool.and_eq_true] at h_cond
            have h := Except.ok.inj h_dispatch; injection h with h
            exact doc_start_tac h_cond.2 (beq_iff_eq.mp h_cond.1) h.symm
          · -- atDocumentEnd (not inFlow): use by_cases to preserve condition
            by_cases h_docEnd : (s_prep.col == 0 && atDocumentEnd s_prep) = true
            · rw [if_pos h_docEnd] at h_dispatch
              rw [Bool.and_eq_true] at h_docEnd
              split at h_dispatch
              · simp at h_dispatch
              · rename_i s_de hde
                have h := Except.ok.inj h_dispatch; injection h with h
                exact doc_end_tac h_docEnd.2 s_de hde h.symm
            · rw [if_neg h_docEnd] at h_dispatch
              by_cases h_dir : (c == '%' && s_prep.col == 0) = true
              · rw [if_pos h_dir] at h_dispatch
                rw [Bool.and_eq_true] at h_dir
                split at h_dispatch
                · simp at h_dispatch
                · rename_i s_dir h_dir_ok
                  have h := Except.ok.inj h_dispatch; injection h with h; subst h
                  have hcol : sp.col = 0 := by rw [hcorr.col_eq]; exact beq_iff_eq.mp h_dir.2
                  have hpeek_pct : s_prep.peek? = some '%' := by
                    rw [show c = '%' from beq_iff_eq.mp h_dir.1] at hpeek; exact hpeek
                  obtain ⟨rest, sp_dir, hchars, hgstar, hcorr_dir, h_at_break⟩ :=
                    scanDirective_prod s_prep sp hcorr hpeek_pct s_dir h_dir_ok
                  refine ⟨sp_dir, true, hcol,
                    PendingNode.pendingDirective sp_start sp sp_dir
                      (fun sp_mid hssl => ?_)
                      h_stream,
                    fun _ => scanDirective_directivesPresent h_dir_ok,
                    hcorr_dir⟩
                  obtain ⟨sp_chars, sp_col⟩ := sp
                  subst hchars
                  exact GPlus.mk _ sp_mid sp_mid
                    (SLDirective.mk rest sp_col sp_dir sp_mid hgstar hssl) (GStar.nil _)
              · rw [if_neg h_dir] at h_dispatch
                simp at h_dispatch
    -- Proof of doc_end_tac
    intro hat s_de hde h_eq; subst h_eq
    obtain ⟨rest, hchars, hcol⟩ := atDocumentEnd_chars s_prep sp hcorr hat
    obtain ⟨sp', h_marker, hcorr'⟩ := scanDocumentEnd_prod s_prep sp hcorr rest hchars hcol s' hde
    exact ⟨sp', false, hcol, PendingNode.pendingDocEnd sp_start sp sp' h_marker,
           fun h => Bool.noConfusion h, hcorr'⟩
  -- Proof of doc_start_tac
  intro hat hcol_s h_eq; subst h_eq
  have hcol : sp.col = 0 := by rw [hcorr.col_eq]; exact hcol_s
  obtain ⟨rest, hchars, _⟩ := atDocumentStart_chars s_prep sp hcorr hat
  obtain ⟨sp', h_marker, hcorr'⟩ := scanDocumentStart_prod s_prep sp hcorr rest hchars hcol
  exact ⟨sp', false, hcol,
    PendingNode.pendingDocStart sp_start sp sp'
      (fun sp_end h_content =>
        SLAnyDocument.explicit sp sp_end
          (SLExplicitDocument.withContent sp sp' sp_end h_marker h_content)),
    fun h => Bool.noConfusion h, hcorr'⟩

-- Every `.ok (some _)` branch of `scanNextToken_dispatchStructural` requires
-- `s.col = 0`. Standalone lemma breaking the circular dependency in
-- `dispatch_new_pending` (where `structural_dispatch_to_pending` needs
-- `SLYamlStream` which needs `sp_mid = sp_prep` which needs `sp.col = 0`).
lemma dispatchStructural_col0
    (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    s.col = 0 := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- inFlow
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · -- atDocumentStart
          rename_i _ _ _ h_cond
          rw [Bool.and_eq_true] at h_cond; exact beq_iff_eq.mp h_cond.1
        · by_cases hde : (s.col == 0 && atDocumentEnd s) = true
          · rw [Bool.and_eq_true] at hde; exact beq_iff_eq.mp hde.1
          · rw [if_neg hde] at h
            by_cases hdi : (c == '%' && s.col == 0) = true
            · rw [Bool.and_eq_true] at hdi; exact beq_iff_eq.mp hdi.2
            · rw [if_neg hdi] at h; simp at h
  · -- not inFlow
    split at h
    · simp at h
    · split at h
      · -- atDocumentStart
        rename_i _ _ h_cond
        rw [Bool.and_eq_true] at h_cond; exact beq_iff_eq.mp h_cond.1
      · by_cases hde : (s.col == 0 && atDocumentEnd s) = true
        · rw [Bool.and_eq_true] at hde; exact beq_iff_eq.mp hde.1
        · rw [if_neg hde] at h
          by_cases hdi : (c == '%' && s.col == 0) = true
          · rw [Bool.and_eq_true] at hdi; exact beq_iff_eq.mp hdi.2
          · rw [if_neg hdi] at h; simp at h

-- Helper (Fix B): the SSLComments midpoint coincides with the corr position
-- when structural dispatch succeeded (it requires col = 0; whitespace or a
-- comment after a col-0 midpoint would move the column past 0).
lemma structural_gap_collapse
    (s_prep s' : ScannerState) (c : Char)
    (sp_mid sp_ws sp_gap sp_prep : SurfPos)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_gap : ScannerSurfCorr s_prep sp_gap)
    (hcol_mid : sp_mid.col = 0)
    (hws : GStar SSWhite sp_mid sp_ws)
    (hcmt : GOpt SCNbCommentText sp_ws sp_gap)
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    sp_mid = sp_prep := by
  have h_gap_eq : sp_gap = sp_prep := ScannerSurfCorr_unique hcorr_gap hcorr_prep
  have hcol_prep : sp_prep.col = 0 := by
    rw [hcorr_prep.col_eq]; exact dispatchStructural_col0 s_prep s' c h_dispatch
  have hcol_gap : sp_gap.col = 0 := h_gap_eq ▸ hcol_prep
  cases hcmt with
  | none =>
    have h1 : sp_ws = sp_mid := gstar_sswhite_col_eq_nil sp_mid sp_ws (by omega) hws
    exact h1.symm.trans h_gap_eq
  | some =>
    rename_i hc
    exfalso; have := scnb_comment_col_gt sp_ws sp_gap hc; omega

/-- Structural dispatch with an open directive run (Fix B).

    The pending directives `GPlus SLDirective sp_block sp_prep` are resolved
    by the incoming structural token:
    - `---` forms a **directive document** ([209] `l-directive-document`)
      via a `pendingDocStart` whose builder wraps the accumulated directives
      in `SLDirectiveDocument`;
    - `%` extends the run (`GPlus_snoc`) into a new `pendingDirective`;
    - `...` is impossible: `scanDocumentEnd` errors when `directivesPresent`
      is set, contradicting the pending↔flag coupling. -/
lemma structural_dispatch_after_directives
    (s_prep s' : ScannerState) (c : Char) (sp_start sp_block sp_prep : SurfPos)
    (hcorr : ScannerSurfCorr s_prep sp_prep)
    (hpeek : s_prep.peek? = some c)
    (h_stream : SLYamlStream sp_start sp_block)
    (h_dirs : GPlus SLDirective sp_block sp_prep)
    (h_dp : s_prep.directivesPresent = true)
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp' b', PendingNode b' sp_start sp_block sp' ∧
      (b' = true → s'.directivesPresent = true) ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchStructural at h_dispatch
  simp only [bind, Except.bind, pure, Except.pure] at h_dispatch
  suffices doc_start_tac : ∀ (hat : atDocumentStart s_prep = true)
      (hcol_s : s_prep.col = 0) (_ : s' = scanDocumentStart s_prep),
      ∃ sp' b', PendingNode b' sp_start sp_block sp' ∧
        (b' = true → s'.directivesPresent = true) ∧ ScannerSurfCorr s' sp' by
    suffices doc_end_tac : ∀ (s_de : ScannerState)
        (hde : scanDocumentEnd s_prep = .ok s_de) (_ : s' = s_de),
        ∃ sp' b', PendingNode b' sp_start sp_block sp' ∧
          (b' = true → s'.directivesPresent = true) ∧ ScannerSurfCorr s' sp' by
      suffices dir_tac : ∀ (s_dir : ScannerState)
          (h_dir_ok : scanDirective s_prep = .ok s_dir) (_ : s' = s_dir)
          (hpeek_pct : s_prep.peek? = some '%'),
          ∃ sp' b', PendingNode b' sp_start sp_block sp' ∧
            (b' = true → s'.directivesPresent = true) ∧ ScannerSurfCorr s' sp' by
        split at h_dispatch
        · split at h_dispatch
          · simp at h_dispatch
          · split at h_dispatch
            · simp at h_dispatch
            · split at h_dispatch
              · -- atDocumentStart (inFlow)
                rename_i _ _ _ h_cond
                rw [Bool.and_eq_true] at h_cond
                have h := Except.ok.inj h_dispatch; injection h with h
                exact doc_start_tac h_cond.2 (beq_iff_eq.mp h_cond.1) h.symm
              · by_cases h_docEnd : (s_prep.col == 0 && atDocumentEnd s_prep) = true
                · rw [if_pos h_docEnd] at h_dispatch
                  split at h_dispatch
                  · simp at h_dispatch
                  · rename_i s_de hde
                    have h := Except.ok.inj h_dispatch; injection h with h
                    exact doc_end_tac s_de hde h.symm
                · rw [if_neg h_docEnd] at h_dispatch
                  by_cases h_dir : (c == '%' && s_prep.col == 0) = true
                  · rw [if_pos h_dir] at h_dispatch
                    rw [Bool.and_eq_true] at h_dir
                    split at h_dispatch
                    · simp at h_dispatch
                    · rename_i s_dir h_dir_ok
                      have h := Except.ok.inj h_dispatch; injection h with h
                      exact dir_tac s_dir h_dir_ok h.symm
                        (by rw [show c = '%' from beq_iff_eq.mp h_dir.1] at hpeek; exact hpeek)
                  · rw [if_neg h_dir] at h_dispatch
                    simp at h_dispatch
        · split at h_dispatch
          · simp at h_dispatch
          · split at h_dispatch
            · -- atDocumentStart (not inFlow)
              rename_i _ _ h_cond
              rw [Bool.and_eq_true] at h_cond
              have h := Except.ok.inj h_dispatch; injection h with h
              exact doc_start_tac h_cond.2 (beq_iff_eq.mp h_cond.1) h.symm
            · by_cases h_docEnd : (s_prep.col == 0 && atDocumentEnd s_prep) = true
              · rw [if_pos h_docEnd] at h_dispatch
                split at h_dispatch
                · simp at h_dispatch
                · rename_i s_de hde
                  have h := Except.ok.inj h_dispatch; injection h with h
                  exact doc_end_tac s_de hde h.symm
              · rw [if_neg h_docEnd] at h_dispatch
                by_cases h_dir : (c == '%' && s_prep.col == 0) = true
                · rw [if_pos h_dir] at h_dispatch
                  rw [Bool.and_eq_true] at h_dir
                  split at h_dispatch
                  · simp at h_dispatch
                  · rename_i s_dir h_dir_ok
                    have h := Except.ok.inj h_dispatch; injection h with h
                    exact dir_tac s_dir h_dir_ok h.symm
                      (by rw [show c = '%' from beq_iff_eq.mp h_dir.1] at hpeek; exact hpeek)
                · rw [if_neg h_dir] at h_dispatch
                  simp at h_dispatch
      -- dir_tac: extend the directive run
      intro s_dir h_dir_ok h_eq hpeek_pct; subst h_eq
      obtain ⟨rest, sp_dir, hchars, hgstar, hcorr_dir, _⟩ :=
        scanDirective_prod s_prep sp_prep hcorr hpeek_pct _ h_dir_ok
      refine ⟨sp_dir, true,
        PendingNode.pendingDirective sp_start sp_block sp_dir
          (fun sp_mid hssl => GPlus_snoc h_dirs ?_)
          h_stream,
        fun _ => scanDirective_directivesPresent h_dir_ok,
        hcorr_dir⟩
      obtain ⟨sp_chars, sp_col⟩ := sp_prep
      subst hchars
      exact SLDirective.mk rest sp_col sp_dir sp_mid hgstar hssl
    -- doc_end_tac: vacuous under Fix B (scanDocumentEnd errors on pending directives)
    intro s_de hde _
    exact absurd h_dp (by simp [scanDocumentEnd_ok_directivesPresent hde])
  -- doc_start_tac: the directives form an SLDirectiveDocument
  intro hat hcol_s h_eq; subst h_eq
  have hcol : sp_prep.col = 0 := by rw [hcorr.col_eq]; exact hcol_s
  obtain ⟨rest, hchars, _⟩ := atDocumentStart_chars s_prep sp_prep hcorr hat
  obtain ⟨sp', h_marker, hcorr'⟩ := scanDocumentStart_prod s_prep sp_prep hcorr rest hchars hcol
  exact ⟨sp', false,
    PendingNode.pendingDocStart sp_start sp_block sp'
      (fun sp_end h_content =>
        SLAnyDocument.directive sp_block sp_end
          (SLDirectiveDocument.mk sp_block sp_prep sp_end h_dirs
            (SLExplicitDocument.withContent sp_prep sp' sp_end h_marker h_content))),
    fun h => Bool.noConfusion h, hcorr'⟩

-- Helper (4f.3): gap closure + dispatch → PendingNode at SSLComments midpoint.
-- Factors out the shared pattern: close the position gap between sp_mid (SSLComments
-- endpoint) and sp_prep (ScannerSurfCorr position) using col=0 evidence, then
-- construct the new PendingNode with correctly unified positions.
lemma dispatch_new_pending
    (s_prep s' : ScannerState) (c : Char)
    (sp_start sp_mid sp_ws sp_gap sp_prep sp_scan' : SurfPos)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_gap : ScannerSurfCorr s_prep sp_gap)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (hcol_mid : sp_mid.col = 0)
    (hws : GStar SSWhite sp_mid sp_ws)
    (hcmt : GOpt SCNbCommentText sp_ws sp_gap)
    (h_stream_mid : SLYamlStream sp_start sp_mid)
    (hpeek : s_prep.peek? = some c)
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ b', PendingNode b' sp_start sp_mid sp_scan' ∧
      (b' = true → s'.directivesPresent = true) := by
  have h_mid_prep : sp_mid = sp_prep :=
    structural_gap_collapse s_prep s' c sp_mid sp_ws sp_gap sp_prep
      hcorr_prep hcorr_gap hcol_mid hws hcmt h_dispatch
  have h_stream_prep : SLYamlStream sp_start sp_prep := h_mid_prep ▸ h_stream_mid
  obtain ⟨sp_disp, b', _, h_pending_new, h_flag, hcorr_disp⟩ :=
    structural_dispatch_to_pending s_prep s' c sp_start sp_prep hcorr_prep hpeek h_stream_prep h_dispatch
  have h_disp_eq : sp_disp = sp_scan' := ScannerSurfCorr_unique hcorr_disp hcorr_result
  rw [← h_mid_prep, h_disp_eq] at h_pending_new
  exact ⟨b', h_pending_new, h_flag⟩

-- Helper: handles all PendingNode cases given a stream at sp_block.
-- Factored out so nil, seqLevel, and mapLevel all delegate here.
lemma accum_structural_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char) {b : Bool}
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode b sp_start sp_block sp_scan)
    (h_dir_flag : b = true → sc.directivesPresent = true)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan' b',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode b' sp_start sp_flow' sp_scan' ∧
      (b' = true → s'.directivesPresent = true) ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  obtain ⟨sp_scan', hcorr_result⟩ :=
    dispatchStructural_corr s_prep sp_prep c hcorr_prep h_dispatch
  have hpeek : s_prep.peek? = some c := preprocess_some_peek h_preprocess
  cases b with
  | false =>
    -- Capture closing strategy before case-split (Pattern 6: parametric closing)
    have h_close_pending : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid :=
      fun sp_mid h_ssl => h_pending.close_with_ssl h_stream_block h_ssl
    -- All false-indexed constructors share the same pattern: extract
    -- SSLComments → close pending to stream → dispatch_new_pending.
    have main : ∀ (h_close : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid),
        ∃ sp_gram' sp_block' sp_flow' sp_scan' b',
          SLYamlStream sp_start sp_gram' ∧
          BlockStack sp_gram' sp_block' ∧
          FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
          PendingNode b' sp_start sp_flow' sp_scan' ∧
          (b' = true → s'.directivesPresent = true) ∧
          ScannerSurfCorr s' sp_scan' := by
      intro h_close
      by_cases hcol : sp_scan.col = 0
      · obtain ⟨sp_mid, sp_ws, sp_gap, h_ssl, hcol_mid, hws, hcmt, hcorr_gap, _⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        have h_stream_mid : SLYamlStream sp_start sp_mid := h_close sp_mid h_ssl
        obtain ⟨b', h_pend_new, h_flag⟩ :=
          dispatch_new_pending s_prep s' c sp_start sp_mid sp_ws sp_gap sp_prep sp_scan'
            hcorr_prep hcorr_gap hcorr_result hcol_mid hws hcmt h_stream_mid hpeek h_dispatch
        exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', b', h_stream_mid, BlockStack.nil sp_mid,
               FlowStackB.nil sp_mid .sep, h_pend_new, h_flag, hcorr_result⟩
      · -- col≠0: structural dispatch requires col=0, so SSLComments must exist.
        obtain ⟨sp_mid, sp_ws, sp_gap, h_disj, hws, hcmt, hcorr_gap, _⟩ :=
          preprocess_some_ssl_comments_anyCol sc sp_scan s_prep c h_corr h_preprocess
        have ⟨h_ssl, hcol_mid⟩ : SSLComments sp_scan sp_mid ∧ sp_mid.col = 0 := by
          cases h_disj with
          | inl h => exact h
          | inr h_eq =>
            exfalso
            have h_gap_eq := ScannerSurfCorr_unique hcorr_gap hcorr_prep
            rw [h_eq] at hws; rw [h_gap_eq] at hcmt
            have h_col0 : sp_prep.col = 0 := by
              rw [hcorr_prep.col_eq]; exact dispatchStructural_col0 s_prep s' c h_dispatch
            have h1 := gstar_sswhite_col_ge _ _ hws
            have h2 : sp_prep.col ≥ sp_ws.col := by
              cases hcmt <;> (first | omega | (rename_i h_c; have := scnb_comment_col_gt _ _ h_c; omega))
            omega
        have h_stream_mid : SLYamlStream sp_start sp_mid := h_close sp_mid h_ssl
        obtain ⟨b', h_pend_new, h_flag⟩ :=
          dispatch_new_pending s_prep s' c sp_start sp_mid sp_ws sp_gap sp_prep sp_scan'
            hcorr_prep hcorr_gap hcorr_result hcol_mid hws hcmt h_stream_mid hpeek h_dispatch
        exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', b', h_stream_mid, BlockStack.nil sp_mid,
               FlowStackB.nil sp_mid .sep, h_pend_new, h_flag, hcorr_result⟩
    exact main h_close_pending
  | true =>
    cases h_pending with
    | pendingDirective =>
      rename_i h_stream_old h_dir_acc_old
      -- Fix B: resolve the open directive run against the structural token.
      have h_dp_prep : s_prep.directivesPresent = true := by
        rw [preprocess_some_directivesPresent h_preprocess]; exact h_dir_flag rfl
      have h_after : ∀ (sp_mid : SurfPos), SSLComments sp_scan sp_mid → sp_mid.col = 0 →
          (∀ (sp_ws sp_gap : SurfPos), GStar SSWhite sp_mid sp_ws →
            GOpt SCNbCommentText sp_ws sp_gap → ScannerSurfCorr s_prep sp_gap →
          ∃ sp_gram' sp_block' sp_flow' sp_scan' b',
            SLYamlStream sp_start sp_gram' ∧
            BlockStack sp_gram' sp_block' ∧
            FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
            PendingNode b' sp_start sp_flow' sp_scan' ∧
            (b' = true → s'.directivesPresent = true) ∧
            ScannerSurfCorr s' sp_scan') := by
        intro sp_mid h_ssl hcol_mid sp_ws sp_gap hws hcmt hcorr_gap
        have h_mid_prep : sp_mid = sp_prep :=
          structural_gap_collapse s_prep s' c sp_mid sp_ws sp_gap sp_prep
            hcorr_prep hcorr_gap hcol_mid hws hcmt h_dispatch
        have h_dirs : GPlus SLDirective sp_block sp_prep :=
          h_mid_prep ▸ h_dir_acc_old sp_mid h_ssl
        obtain ⟨sp', b', h_pend', h_flag', hcorr'⟩ :=
          structural_dispatch_after_directives s_prep s' c sp_start sp_block sp_prep
            hcorr_prep hpeek h_stream_old h_dirs h_dp_prep h_dispatch
        have h_sp_eq : sp' = sp_scan' := ScannerSurfCorr_unique hcorr' hcorr_result
        exact ⟨sp_block, sp_block, sp_block, sp_scan', b', h_stream_old,
               BlockStack.nil sp_block, FlowStackB.nil sp_block .sep, h_sp_eq ▸ h_pend', h_flag',
               hcorr_result⟩
      by_cases hcol : sp_scan.col = 0
      · obtain ⟨sp_mid, sp_ws, sp_gap, h_ssl, hcol_mid, hws, hcmt, hcorr_gap, _⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        exact h_after sp_mid h_ssl hcol_mid sp_ws sp_gap hws hcmt hcorr_gap
      · obtain ⟨sp_mid, sp_ws, sp_gap, h_disj, hws, hcmt, hcorr_gap, _⟩ :=
          preprocess_some_ssl_comments_anyCol sc sp_scan s_prep c h_corr h_preprocess
        have ⟨h_ssl, hcol_mid⟩ : SSLComments sp_scan sp_mid ∧ sp_mid.col = 0 := by
          cases h_disj with
          | inl h => exact h
          | inr h_eq =>
            exfalso
            have h_gap_eq := ScannerSurfCorr_unique hcorr_gap hcorr_prep
            rw [h_eq] at hws; rw [h_gap_eq] at hcmt
            have h_col0 : sp_prep.col = 0 := by
              rw [hcorr_prep.col_eq]; exact dispatchStructural_col0 s_prep s' c h_dispatch
            have h1 := gstar_sswhite_col_ge _ _ hws
            have h2 : sp_prep.col ≥ sp_ws.col := by
              cases hcmt <;> (first | omega | (rename_i h_c; have := scnb_comment_col_gt _ _ h_c; omega))
            omega
        exact h_after sp_mid h_ssl hcol_mid sp_ws sp_gap hws hcmt hcorr_gap

lemma accum_step_structural (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char) {b : Bool}
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStackB sp_start sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow)
    (h_pending : PendingNode b sp_start sp_flow sp_scan)
    (h_dir_flag : b = true → sc.directivesPresent = true)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      GStar SSWhite sp_flow sp_scan ∧ LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan' b',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' ∧
      PendingNode b' sp_start sp_flow' sp_scan' ∧
      (b' = true → s'.directivesPresent = true) ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        GStar SSWhite sp_flow' sp_scan' ∧ LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
  -- B.4β: the flow stack is indexed by the scanner's `flowLevel`.
  rcases Nat.eq_zero_or_pos sc.flowLevel with h0 | hpos
  · -- depth 0 (no open flow collection): the existing depth-0 proof.
    rw [h0] at h_flow
    have h_lvl : s'.flowLevel = 0 := by
      rw [ScannerCorrectness.dispatchStructural_preserves_flowLevel s_prep c s' h_dispatch,
          preprocess_preserves_flowLevel sc s_prep c h_preprocess, h0]
    have h_ks : s'.flowStack = #[] := by
      rw [ScannerFlowStack.dispatchStructural_preserves_flowStack s_prep c s' h_dispatch,
          ScannerFlowStack.preprocess_preserves_flowStack sc s_prep c h_preprocess]
      exact h_flow.kinds_nil_of_depth_zero
    rw [h_lvl, h_ks]
    obtain ⟨g', bl', fl', sn', b', q1, q2, q3, q4, q5, q6⟩ :=
      accum_structural_pending sc sp_start sp_flow sp_scan s_prep s' c
        (absorb_stacksB sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
        h_pending h_dir_flag h_corr h_preprocess h_dispatch
    exact ⟨g', bl', fl', sn', b', q1, q2, q3.retail, q4, q5, q6, fun h => absurd h (by omega)⟩
  · -- ═══ DEPTH ≥ 1: VACUOUS. ═══
    -- `scanNextToken_dispatchStructural` has no success arm inside a flow; see
    -- `ScannerAllowDirectives.dispatchStructural_inFlow_no_success`. The
    -- `allowDirectives = false` it needs is the invariant's third component,
    -- transported across preprocessing.
    exact absurd h_dispatch
      (ScannerAllowDirectives.dispatchStructural_inFlow_no_success s_prep s' c
        (by unfold ScannerState.inFlow; simp
            rw [preprocess_preserves_flowLevel sc s_prep c h_preprocess]; omega)
        (by rw [ScannerAllowDirectives.preprocess_preserves_allowDirectives sc s_prep c h_preprocess]
            exact (h_interior hpos).2.2))

/-! ### §1c Preprocessing + Flow Indicator Dispatch

    `scanNextToken_dispatchFlowIndicators` handles `[`, `]`, `{`, `}`, `,`.
    All flow indicators produce `FlowStack.nil` + `PendingNode.pendingFlow`,
    deferring flow collection grammar to `close_with_ssl` (4z.1).

    **Architecture (4z.1):** `new_flow_state` returns `FlowStack.nil` +
    `PendingNode.pendingFlow` for ALL flow characters. The `GLit` bracket
    evidence from `[`/`{` scanning is not stored — it can be recovered from
    dispatch + corr theorems at consumption time if needed. -/

-- Helper: flow indicator dispatch preserves `ScannerSurfCorr` on `some` paths.
lemma dispatchFlowIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_dispatchFlowIndicators sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  replace hok := peel_flowAdj hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- c == '['
  split at hok
  · have h := Except.ok.inj hok; injection h with h; subst h
    exact scanFlowSequenceStart_corr sc sp hcorr
  -- c == ']'
  · split at hok
    · split at hok
      · simp at hok  -- flowEndOutsideFlow
      · split at hok
        · simp at hok  -- flowStack kind-check mismatch
        · -- validateFlowClose is Except Unit, split on it
          split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h; subst h
            exact scanFlowSequenceEnd_corr sc sp hcorr
    -- c == '{'
    · split at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanFlowMappingStart_corr sc sp hcorr
      -- c == '}'
      · split at hok
        · split at hok
          · simp at hok  -- flowEndOutsideFlow
          · split at hok
            · simp at hok  -- flowStack kind-check mismatch
            · split at hok
              · simp at hok
              · have h := Except.ok.inj hok; injection h with h; subst h
                exact scanFlowMappingEnd_corr sc sp hcorr
        -- c == ','
        · split at hok
          · split at hok
            · simp at hok  -- flowEndOutsideFlow
            · split at hok
              · simp at hok
              · rename_i s_fe hfe
                have h := Except.ok.inj hok; injection h with h; subst h
                exact scanFlowEntry_corr sc sp hcorr s_fe hfe
          -- none (fallthrough)
          · simp at hok

-- Helper: handles all PendingNode cases for flow dispatch given stream at sp_block.
lemma accum_flow_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode false sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  obtain ⟨sp_scan', hcorr_result⟩ :=
    dispatchFlowIndicators_corr _ sp_prep c (corr_of_allowDirectives_update hcorr_prep) h_dispatch
  -- All flow indicators produce FlowStack.nil + PendingNode.pendingFlow (4z.1).
  -- GLit bracket evidence is not stored; deferred to close_with_ssl.
  have new_flow_state : ∀ (sp_mid : SurfPos) (h_str_mid : SLYamlStream sp_start sp_mid),
      ∃ sp_flow', FlowStackB sp_start 0 #[] .sep sp_mid sp_flow' ∧ PendingNode false sp_start sp_flow' sp_scan' := by
    intro sp_mid h_str_mid
    exact ⟨sp_mid, FlowStackB.nil sp_mid .sep,
           PendingNode.pendingFlow sp_start sp_mid sp_scan' h_str_mid⟩
  -- Capture closing strategy before case-split (Pattern 6: parametric closing)
  have h_close_pending : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid :=
    fun sp_mid h_ssl => h_pending.close_with_ssl h_stream_block h_ssl
  cases h_pending with
  | noPending =>
    obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_block h_stream_block
    exact ⟨sp_block, sp_block, sp_flow', sp_scan', h_stream_block,
           BlockStack.nil sp_block, h_flow', h_pend', hcorr_result⟩
  | pendingDocEnd _
  | pendingDocStart _
  | pendingContent _
  | pendingFlow _
  | pendingBlockContent _ _ _
  | pendingBlock _ _ =>
    all_goals (
      by_cases hcol : sp_scan.col = 0
      · obtain ⟨sp_mid, _, _, h_ssl, _, _, _, _, _⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        have h_stream_mid := h_close_pending sp_mid h_ssl
        obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_mid h_stream_mid
        exact ⟨sp_mid, sp_mid, sp_flow', sp_scan',
               h_stream_mid,
               BlockStack.nil sp_mid, h_flow', h_pend', hcorr_result⟩
      · -- col≠0: use anyCol, close pending if SSLComments available.
        obtain ⟨sp_mid, _, _, h_disj, _, _, _, _⟩ :=
          preprocess_some_ssl_comments_anyCol sc sp_scan s_prep c h_corr h_preprocess
        cases h_disj with
        | inl h_ssl_col =>
          obtain ⟨h_ssl, _⟩ := h_ssl_col
          have h_stream_mid := h_close_pending sp_mid h_ssl
          obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_mid h_stream_mid
          exact ⟨sp_mid, sp_mid, sp_flow', sp_scan',
                 h_stream_mid,
                 BlockStack.nil sp_mid, h_flow', h_pend', hcorr_result⟩
        | inr h_mid_eq =>
          exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                 BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
                 PendingNode.pendingFlow sp_start sp_block sp_scan' h_stream_block,
                 hcorr_result⟩)

/-! ### §1c' Flow-open GLit production (B.4β.2)

    `scanFlowSequenceStart`/`scanFlowMappingStart` emit the bracket token and
    advance one char. These `_prod` helpers recover the literal-bracket grammar
    evidence (`GLit '[' sp sp'` / `GLit '{' sp sp'`) at the *specific* post-bracket
    position, plus the corr and the `flowLevel + 1` fact — the analog of
    `scanBlockEntry_prod` for the flow-open indicators. Used by `accum_step_flow`
    to build the `FlowOpenStack` `h_open` field when opening/pushing a flow. -/

lemma scanFlowSequenceStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '[') :
    ∃ sp', GLit '[' sp sp' ∧ ScannerSurfCorr (scanFlowSequenceStart sc) sp'
           ∧ (scanFlowSequenceStart sc).flowLevel = sc.flowLevel + 1 := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_, ?_⟩
  · unfold scanFlowSequenceStart
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr
        (({ sc with simpleKey := { possible := false } }).emit .flowSequenceStart)
        ⟨'[' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    have hcorr_adv := advance_non_newline_corr
      (({ sc with simpleKey := { possible := false } }).emit .flowSequenceStart)
      '[' rest hcorr_emit hmore (by decide) (by decide)
    exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq,
           hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
  · unfold scanFlowSequenceStart
    simp only [ScannerCorrectness.advance_preserves_flowLevel,
               ScannerCorrectness.emit_preserves_flowLevel]

lemma scanFlowMappingStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '{') :
    ∃ sp', GLit '{' sp sp' ∧ ScannerSurfCorr (scanFlowMappingStart sc) sp'
           ∧ (scanFlowMappingStart sc).flowLevel = sc.flowLevel + 1 := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_, ?_⟩
  · unfold scanFlowMappingStart
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr
        (({ sc with simpleKey := { possible := false } }).emit .flowMappingStart)
        ⟨'{' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    have hcorr_adv := advance_non_newline_corr
      (({ sc with simpleKey := { possible := false } }).emit .flowMappingStart)
      '{' rest hcorr_emit hmore (by decide) (by decide)
    exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq,
           hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
  · unfold scanFlowMappingStart
    simp only [ScannerCorrectness.advance_preserves_flowLevel,
               ScannerCorrectness.emit_preserves_flowLevel]

/-- Flow-close analog of `scanFlowSequenceStart_prod`: `GLit ']'`, post-`]`
    corr, and the `flowLevel` decrement (at positive depth). -/
lemma scanFlowSequenceEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ']')
    (hpos : sc.flowLevel > 0) :
    ∃ sp', GLit ']' sp sp' ∧ ScannerSurfCorr (scanFlowSequenceEnd sc) sp'
           ∧ (scanFlowSequenceEnd sc).flowLevel = sc.flowLevel - 1 := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_, ?_⟩
  · unfold scanFlowSequenceEnd
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr (sc.emit .flowSequenceEnd) ⟨']' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    have hcorr_adv := advance_non_newline_corr (sc.emit .flowSequenceEnd)
      ']' rest hcorr_emit hmore (by decide) (by decide)
    exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq,
           hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
  · unfold scanFlowSequenceEnd
    simp only [ScannerCorrectness.advance_preserves_flowLevel,
               ScannerCorrectness.emit_preserves_flowLevel]
    split <;> omega

/-- Flow-close analog for `}` (see `scanFlowSequenceEnd_prod`). -/
lemma scanFlowMappingEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '}')
    (hpos : sc.flowLevel > 0) :
    ∃ sp', GLit '}' sp sp' ∧ ScannerSurfCorr (scanFlowMappingEnd sc) sp'
           ∧ (scanFlowMappingEnd sc).flowLevel = sc.flowLevel - 1 := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_, ?_⟩
  · unfold scanFlowMappingEnd
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr (sc.emit .flowMappingEnd) ⟨'}' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    have hcorr_adv := advance_non_newline_corr (sc.emit .flowMappingEnd)
      '}' rest hcorr_emit hmore (by decide) (by decide)
    exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq,
           hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
  · unfold scanFlowMappingEnd
    simp only [ScannerCorrectness.advance_preserves_flowLevel,
               ScannerCorrectness.emit_preserves_flowLevel]
    split <;> omega

/-- Flow-entry analog: from a successful `scanFlowEntry`, `GLit ','`, post-`,`
    corr, and `flowLevel` preservation. -/
lemma scanFlowEntry_prod (sc : ScannerState) (sp : SurfPos) {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ',')
    (hok : scanFlowEntry sc = .ok s') :
    ∃ sp', GLit ',' sp sp' ∧ ScannerSurfCorr s' sp' ∧ s'.flowLevel = sc.flowLevel := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have hcorr_emit : ScannerSurfCorr (sc.emit .flowEntry) ⟨',' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr (sc.emit .flowEntry)
    ',' rest hcorr_emit hmore (by decide) (by decide)
  unfold scanFlowEntry at hok
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
  split at hok
  · split at hok
    · simp at hok
    · have hs := Except.ok.inj hok
      subst hs
      exact ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col,
             ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq,
              hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩,
             by simp only [ScannerCorrectness.advance_preserves_flowLevel,
                           ScannerCorrectness.emit_preserves_flowLevel]⟩
  · have hs := Except.ok.inj hok
    subst hs
    exact ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col,
           ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq,
            hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩,
           by simp only [ScannerCorrectness.advance_preserves_flowLevel,
                         ScannerCorrectness.emit_preserves_flowLevel]⟩

/-! ### §1c''a Flow-interior frame transitions (B.4β.2 depth ≥ 1)

    The per-frame algebra consumed by the depth-≥1 arms of `accum_step_flow`
    (and, in β.3, by the interior content steps). Sep-threading rule: each
    step consumes its OWN leading separation `sp_flow → sp_prep`
    (`preprocess_some_separate_0_anyCol`), which these helpers fold into the
    grammar slot of the construct built by the PREVIOUS step — the innermost
    entry's trailing `GOpt` (`SFlowSeqEntries_extendSep`), a `held` frame's
    post-comma slot, the collection's post-bracket slot, or a `colonPending`'s
    mandatory `:`→value separation. All folds are total via the §9
    separator-composition algebra (PreprocessProduction).

    Residues (deliberate `sorry`s, all one root cause): frame shapes that the
    scanner REJECTS (leading/consecutive comma via `invalidFlowEntry`,
    separator-less adjacent nodes via `checkFlowAdjacency`) are locally
    unrefutable — the accumulation invariant does not yet couple the top
    frame's shape to the scanner's token history (`lastRealTokenVal?`). That
    coupling is item 9a/9b territory (with the flow-close KIND strictening);
    until then those arms are typed holes. -/

/-- Close a flow-SEQUENCE frame with `]`, folding the close step's leading
    separation into the frame (mid entries complete with an empty tail:
    `[a:]`, `[? a]`, …). `h_lead_out`/`h_lead_in` are the same separation at
    the outer/entry context (literal contexts at the call sites make both
    defeq to `SSeparateLines 0`). -/
lemma SeqFrame.closeWithSep {c_out : YamlContext} {tl : FrameTail}
    {sp_br sp_open sp_es sp_flow sp_prep sp_tok : SurfPos}
    (h_open : GLit '[' sp_br sp_open)
    (h_sep : GOpt (SSeparate 0 c_out) sp_open sp_es)
    (st : SeqFrame 0 (inFlowCtx c_out) tl sp_es sp_flow)
    (h_lead_out : SSeparate 0 c_out sp_flow sp_prep)
    (h_lead_in : SSeparate 0 (inFlowCtx c_out) sp_flow sp_prep)
    (h_close : GLit ']' sp_prep sp_tok) :
    SFlowSequence 0 c_out sp_br sp_tok := by
  cases st
  · -- betweenEmpty: `[]`
    exact PartialFlowSeq.closeSeq h_open (GOpt_SSeparate_extend h_sep h_lead_out)
      (.empty sp_prep) h_close
  · -- betweenEntries: `[a]`
    rename_i h hcl
    obtain ⟨h', hcl'⟩ := SFlowSeqEntries_extendSep hcl h_lead_in
    exact PartialFlowSeq.closeSeq h_open h_sep (.entries _ _ h' hcl') h_close
  · -- betweenHeld: `[a,]`
    rename_i hcomma h hcl hsep
    exact PartialFlowSeq.closeSeq h_open h_sep
      (.held _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend hsep h_lead_in)) h_close
  · -- midNode: `[a]`, the node still mid-entry
    rename_i pre hnode
    exact PartialFlowSeq.closeSeq h_open h_sep
      (pre.appendEntry (.node _ _ _ _ hnode) (.some _ _ h_lead_in)) h_close
  · -- midColon: `[a:]`
    rename_i hkey hsep pre hcolon
    exact PartialFlowSeq.closeSeq h_open h_sep
      (PendingFlowSeqEntry.finishPairEmpty pre hkey hsep hcolon (.some _ _ h_lead_in)) h_close
  · -- midExplicitKey: `[? a]`
    rename_i hq hqsep pre hkey
    exact PartialFlowSeq.closeSeq h_open h_sep
      (PendingFlowSeqEntry.finishExplicitKeyOnly pre hq hqsep hkey (.some _ _ h_lead_in)) h_close
  · -- midExplicitColon: `[? a:]`
    rename_i hq hqsep hkey hsep pre hcolon
    exact PartialFlowSeq.closeSeq h_open h_sep
      (PendingFlowSeqEntry.finishExplicitPairEmpty pre hq hqsep hkey hsep hcolon
        (.some _ _ h_lead_in)) h_close

/-- Close a flow-MAPPING frame with `}` (see `SeqFrame.closeWithSep`; mid
    entries complete with an empty value: `{a}`, `{a:}`, `{? a}`, `{:}`, …). -/
lemma MapFrame.closeWithSep {c_out : YamlContext} {tl : FrameTail}
    {sp_br sp_open sp_es sp_flow sp_prep sp_tok : SurfPos}
    (h_open : GLit '{' sp_br sp_open)
    (h_sep : GOpt (SSeparate 0 c_out) sp_open sp_es)
    (st : MapFrame 0 (inFlowCtx c_out) tl sp_es sp_flow)
    (h_lead_out : SSeparate 0 c_out sp_flow sp_prep)
    (h_lead_in : SSeparate 0 (inFlowCtx c_out) sp_flow sp_prep)
    (h_close : GLit '}' sp_prep sp_tok) :
    SFlowMapping 0 c_out sp_br sp_tok := by
  cases st
  · -- betweenEmpty: `{}`
    exact PartialFlowMap.closeMap h_open (GOpt_SSeparate_extend h_sep h_lead_out)
      (.empty sp_prep) h_close
  · -- betweenEntries: `{a: b}`
    rename_i h hcl
    obtain ⟨h', hcl'⟩ := SFlowMapEntries_extendSep hcl h_lead_in
    exact PartialFlowMap.closeMap h_open h_sep (.entries _ _ h' hcl') h_close
  · -- betweenHeld: `{a: b,}`
    rename_i hcomma h hcl hsep
    exact PartialFlowMap.closeMap h_open h_sep
      (.held _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend hsep h_lead_in)) h_close
  · -- midKey: `{a}`
    rename_i pre hkey
    exact PartialFlowMap.closeMap h_open h_sep
      (PendingFlowMapEntry.finishBareKey pre hkey (.some _ _ h_lead_in)) h_close
  · -- midColon: `{a:}`
    rename_i hkey hsep pre hcolon
    exact PartialFlowMap.closeMap h_open h_sep
      (PendingFlowMapEntry.finishEmpty pre hkey hsep hcolon (.some _ _ h_lead_in)) h_close
  · -- midExplicitKey: `{? a}`
    rename_i hq hqsep pre hkey
    exact PartialFlowMap.closeMap h_open h_sep
      (PendingFlowMapEntry.finishExplicitKeyOnly pre hq hqsep hkey (.some _ _ h_lead_in)) h_close
  · -- midExplicitColon: `{? a:}`
    rename_i hq hqsep hkey hsep pre hcolon
    exact PartialFlowMap.closeMap h_open h_sep
      (PendingFlowMapEntry.finishExplicitEmpty pre hq hqsep hkey hsep hcolon
        (.some _ _ h_lead_in)) h_close
  · -- midEmptyColon: `{:}`
    rename_i pre hcolon
    exact PartialFlowMap.closeMap h_open h_sep
      (PendingFlowMapEntry.finishEmptyKeyEmpty pre hcolon (.some _ _ h_lead_in)) h_close

/-! ### Frame-valued entry snocs

    `FlowSeqPrefix.appendEntry` (and the `PendingFlow*.finish*` wrappers over it)
    returns an opaque `PartialFlow*`, which hides which constructor was built.
    The frame-valued forms below keep that visible in the type —
    `append*EntryFrame` always lands in `entries` (tail `.value`),
    `append*EntryHeldFrame` always in `held` (tail `.sep`) — which is exactly the
    information the 9b(ii) coupling needs. They replace `appendEntryHeld` and the
    `finish*Value` family in `NodeProduction`, whose only consumers were the two
    frame transitions below. -/

/-- Snoc a completed seq entry + trailing separator onto a prefix, landing in the
    `.value`-tailed `betweenEntries` frame. -/
lemma appendSeqEntryFrame {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    (pre : FlowSeqPrefix n c sp sp_d)
    (h_entry : SFlowSeqEntry n c sp_d sp_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    SeqFrame n c .value sp sp' := by
  cases pre with
  | init =>
      exact .betweenEntries _ _ (SFlowSeqEntries_single h_entry h_sep)
        (SFlowSeqEntries_single_closeable h_entry h_sep)
  | cons _ _ _ h hcl hcomma hsep =>
      exact .betweenEntries _ _ (SFlowSeqEntries_snoc hcl hcomma hsep h_entry h_sep)
        (SFlowSeqEntries_snoc_closeable hcl hcomma hsep h_entry h_sep)

/-- Snoc a completed map entry + trailing separator onto a prefix (see
    `appendSeqEntryFrame`). -/
lemma appendMapEntryFrame {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_d)
    (h_entry : SFlowMapEntry n c sp_d sp_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    MapFrame n c .value sp sp' := by
  cases pre with
  | init =>
      exact .betweenEntries _ _ (SFlowMapEntries_single h_entry h_sep)
        (SFlowMapEntries_single_closeable h_entry h_sep)
  | cons _ _ _ h hcl hcomma hsep =>
      exact .betweenEntries _ _ (SFlowMapEntries_snoc hcl hcomma hsep h_entry h_sep)
        (SFlowMapEntries_snoc_closeable hcl hcomma hsep h_entry h_sep)

/-- Snoc a completed seq entry, its trailing separator, and an immediately
    following `,` onto a prefix, landing in the `.sep`-tailed `betweenHeld`
    frame (the comma-transition analog of `appendSeqEntryFrame`). -/
lemma appendSeqEntryHeldFrame {n : Nat} {c : YamlContext}
    {sp sp_d sp_e sp_x sp_c sp' : SurfPos}
    (pre : FlowSeqPrefix n c sp sp_d)
    (h_entry : SFlowSeqEntry n c sp_d sp_e) (h_sep_tr : GOpt (SSeparate n c) sp_e sp_x)
    (hcomma : GLit ',' sp_x sp_c) (h_sep_post : GOpt (SSeparate n c) sp_c sp') :
    SeqFrame n c .sep sp sp' := by
  cases pre with
  | init =>
      exact .betweenHeld _ _ _ _ (SFlowSeqEntries_single h_entry h_sep_tr)
        (SFlowSeqEntries_single_closeable h_entry h_sep_tr) hcomma h_sep_post
  | cons _ _ _ h hcl hcomma₀ hsep₀ =>
      exact .betweenHeld _ _ _ _ (SFlowSeqEntries_snoc hcl hcomma₀ hsep₀ h_entry h_sep_tr)
        (SFlowSeqEntries_snoc_closeable hcl hcomma₀ hsep₀ h_entry h_sep_tr) hcomma h_sep_post

/-- Snoc a completed map entry + `,` onto a prefix (see
    `appendSeqEntryHeldFrame`). -/
lemma appendMapEntryHeldFrame {n : Nat} {c : YamlContext}
    {sp sp_d sp_e sp_x sp_c sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_d)
    (h_entry : SFlowMapEntry n c sp_d sp_e) (h_sep_tr : GOpt (SSeparate n c) sp_e sp_x)
    (hcomma : GLit ',' sp_x sp_c) (h_sep_post : GOpt (SSeparate n c) sp_c sp') :
    MapFrame n c .sep sp sp' := by
  cases pre with
  | init =>
      exact .betweenHeld _ _ _ _ (SFlowMapEntries_single h_entry h_sep_tr)
        (SFlowMapEntries_single_closeable h_entry h_sep_tr) hcomma h_sep_post
  | cons _ _ _ h hcl hcomma₀ hsep₀ =>
      exact .betweenHeld _ _ _ _ (SFlowMapEntries_snoc hcl hcomma₀ hsep₀ h_entry h_sep_tr)
        (SFlowMapEntries_snoc_closeable hcl hcomma₀ hsep₀ h_entry h_sep_tr) hcomma h_sep_post

/-- `,` transition on a flow-SEQUENCE frame: finish any mid entry (trailing
    sep = this step's leading sep) and land in `betweenHeld`.

    **9b(ii)**: the degenerate incoming shapes — `betweenEmpty` (a leading comma,
    `[,`) and `betweenHeld` (consecutive commas, `,,`) — are exactly the frames
    `scanFlowEntry` rejects with `invalidFlowEntry`, and exactly the `.sep`-tailed
    ones. `h_tail` is that scanner guard, transported through the tail index. -/
lemma SeqFrame.holdComma {c : YamlContext} {tl : FrameTail}
    {sp_es sp_flow sp_prep sp_tok : SurfPos}
    (st : SeqFrame 0 c tl sp_es sp_flow)
    (h_tail : tl ≠ .sep)
    (h_lead : SSeparate 0 c sp_flow sp_prep)
    (hcomma : GLit ',' sp_prep sp_tok) :
    SeqFrame 0 c .sep sp_es sp_tok := by
  cases st
  · -- betweenEmpty: leading comma `[,`.
    exact absurd rfl h_tail
  · rename_i h hcl
    obtain ⟨h', hcl'⟩ := SFlowSeqEntries_extendSep hcl h_lead
    exact .betweenHeld _ _ _ _ h' hcl' hcomma (GOpt.none sp_tok)
  · -- betweenHeld: consecutive commas `,,`.
    exact absurd rfl h_tail
  · rename_i pre hnode
    exact appendSeqEntryHeldFrame pre (.node _ _ _ _ hnode)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  · rename_i hkey hsep pre hcolon
    exact appendSeqEntryHeldFrame pre (.pairEmpty _ _ _ _ _ _ hkey hsep hcolon)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  · rename_i hq hqsep pre hkey
    exact appendSeqEntryHeldFrame pre
      (.explicitPairKeyOnly _ _ _ _ _ _ hq hqsep hkey)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  · rename_i hq hqsep hkey hsep pre hcolon
    exact appendSeqEntryHeldFrame pre
      (.explicitPairEmpty _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)

/-- `,` transition on a flow-MAPPING frame (see `SeqFrame.holdComma`; mid
    entries finish with an empty value: `{a,`, `{a:,`, `{? a,`, `{:,`). -/
lemma MapFrame.holdComma {c : YamlContext} {tl : FrameTail}
    {sp_es sp_flow sp_prep sp_tok : SurfPos}
    (st : MapFrame 0 c tl sp_es sp_flow)
    (h_tail : tl ≠ .sep)
    (h_lead : SSeparate 0 c sp_flow sp_prep)
    (hcomma : GLit ',' sp_prep sp_tok) :
    MapFrame 0 c .sep sp_es sp_tok := by
  cases st
  · -- betweenEmpty: leading comma `{,`.
    exact absurd rfl h_tail
  · rename_i h hcl
    obtain ⟨h', hcl'⟩ := SFlowMapEntries_extendSep hcl h_lead
    exact .betweenHeld _ _ _ _ h' hcl' hcomma (GOpt.none sp_tok)
  · -- betweenHeld: consecutive commas.
    exact absurd rfl h_tail
  · rename_i pre hkey
    exact appendMapEntryHeldFrame pre (.bareKey _ _ _ _ hkey)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  · rename_i hkey hsep pre hcolon
    exact appendMapEntryHeldFrame pre
      (.implicitEmpty _ _ _ _ _ _ hkey hsep hcolon)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  · rename_i hq hqsep pre hkey
    exact appendMapEntryHeldFrame pre
      (.explicitKeyOnly _ _ _ _ _ _ hq hqsep hkey)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  · rename_i hq hqsep hkey hsep pre hcolon
    exact appendMapEntryHeldFrame pre
      (.explicitEmpty _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  · rename_i pre hcolon
    exact appendMapEntryHeldFrame pre (.emptyKeyEmpty _ _ _ _ hcolon)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)

/-- Fold a completed `.flowIn` node (starting after this step's leading
    separation) into the SAME-depth open stack: the top frame transitions
    `between → mid` (the node is a new entry/key) or `mid …Colon → between` (the
    node is the awaited value). THE central interior receiver — the nested push
    builds its `inject` from this, and the β.3 content steps will consume it
    directly.

    **9b(ii)**: the adjacency-rejected shapes — a node directly after a completed
    entry or key (`[[a][b]]`, `["a""b"]`) — are exactly the `.value`-tailed
    frames, which is what `scanNextToken_checkFlowAdjacency` refuses to dispatch a
    node-start character from. `h_tail` is that scanner guard. The result is
    always `.value`: a node has just completed. -/
lemma FlowOpenStack.receiveNode {sp_start : SurfPos} {D : Nat} {ks : Array Bool}
    {tl : FrameTail} {sp_block sp_flow sp_prep : SurfPos}
    (h_fos : FlowOpenStack sp_start D ks tl sp_block sp_flow)
    (h_tail : tl ≠ .value)
    (h_lead : SSeparateLines 0 sp_flow sp_prep) :
    ∀ sp_ne, SFlowNode 0 .flowIn sp_prep sp_ne →
      FlowOpenStack sp_start D ks .value sp_block sp_ne := by
  intro sp_ne h_node
  cases h_fos
  · -- seqBase
    rename_i resume h_open h_sep st
    cases st
    · exact .seqBase _ _ _ _ _ _ resume h_open (GOpt_SSeparate_extend h_sep h_lead)
        (.midNode _ _ _ (.init sp_prep) h_node)
    · exact absurd rfl h_tail
    · rename_i hcomma₀ h hcl hsep₀
      exact .seqBase _ _ _ _ _ _ resume h_open h_sep
        (.midNode _ _ _
          (.cons _ _ _ _ h hcl hcomma₀ (GOpt_SSeparate_extend hsep₀ h_lead)) h_node)
    · exact absurd rfl h_tail
    · rename_i hkey hsep pre hcolon
      exact .seqBase _ _ _ _ _ _ resume h_open h_sep
        (appendSeqEntryFrame pre (.pairValue _ _ _ _ _ _ _ _ hkey hsep hcolon h_lead h_node)
          (GOpt.none sp_ne))
    · exact absurd rfl h_tail
    · rename_i hq hqsep hkey hsep pre hcolon
      exact .seqBase _ _ _ _ _ _ resume h_open h_sep
        (appendSeqEntryFrame pre
          (.explicitPairValue _ _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon h_lead h_node)
          (GOpt.none sp_ne))
  · -- mapBase
    rename_i resume h_open h_sep st
    cases st
    · exact .mapBase _ _ _ _ _ _ resume h_open (GOpt_SSeparate_extend h_sep h_lead)
        (.midKey _ _ _ (.init sp_prep) h_node)
    · exact absurd rfl h_tail
    · rename_i hcomma₀ h hcl hsep₀
      exact .mapBase _ _ _ _ _ _ resume h_open h_sep
        (.midKey _ _ _
          (.cons _ _ _ _ h hcl hcomma₀ (GOpt_SSeparate_extend hsep₀ h_lead)) h_node)
    · exact absurd rfl h_tail
    · rename_i hkey hsep pre hcolon
      exact .mapBase _ _ _ _ _ _ resume h_open h_sep
        (appendMapEntryFrame pre (.implicitValue _ _ _ _ _ _ _ _ hkey hsep hcolon h_lead h_node)
          (GOpt.none sp_ne))
    · exact absurd rfl h_tail
    · rename_i hq hqsep hkey hsep pre hcolon
      exact .mapBase _ _ _ _ _ _ resume h_open h_sep
        (appendMapEntryFrame pre
          (.explicitValue _ _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon h_lead h_node)
          (GOpt.none sp_ne))
    · rename_i pre hcolon
      exact .mapBase _ _ _ _ _ _ resume h_open h_sep
        (appendMapEntryFrame pre (.emptyKeyValue _ _ _ _ _ _ hcolon h_lead h_node)
          (GOpt.none sp_ne))
  · -- seqNest (NB: `cases` floats the recursive `inject` closure to
    -- second-to-last — the context order is h_open, h_sep, inject, st)
    rename_i h_open h_sep inject st
    cases st
    · exact .seqNest _ _ _ _ _ _ _ _ inject h_open (GOpt_SSeparate_extend h_sep h_lead)
        (.midNode _ _ _ (.init sp_prep) h_node)
    · exact absurd rfl h_tail
    · rename_i hcomma₀ h hcl hsep₀
      exact .seqNest _ _ _ _ _ _ _ _ inject h_open h_sep
        (.midNode _ _ _
          (.cons _ _ _ _ h hcl hcomma₀ (GOpt_SSeparate_extend hsep₀ h_lead)) h_node)
    · exact absurd rfl h_tail
    · rename_i hkey hsep pre hcolon
      exact .seqNest _ _ _ _ _ _ _ _ inject h_open h_sep
        (appendSeqEntryFrame pre (.pairValue _ _ _ _ _ _ _ _ hkey hsep hcolon h_lead h_node)
          (GOpt.none sp_ne))
    · exact absurd rfl h_tail
    · rename_i hq hqsep hkey hsep pre hcolon
      exact .seqNest _ _ _ _ _ _ _ _ inject h_open h_sep
        (appendSeqEntryFrame pre
          (.explicitPairValue _ _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon h_lead h_node)
          (GOpt.none sp_ne))
  · -- mapNest (same field reorder as seqNest)
    rename_i h_open h_sep inject st
    cases st
    · exact .mapNest _ _ _ _ _ _ _ _ inject h_open (GOpt_SSeparate_extend h_sep h_lead)
        (.midKey _ _ _ (.init sp_prep) h_node)
    · exact absurd rfl h_tail
    · rename_i hcomma₀ h hcl hsep₀
      exact .mapNest _ _ _ _ _ _ _ _ inject h_open h_sep
        (.midKey _ _ _
          (.cons _ _ _ _ h hcl hcomma₀ (GOpt_SSeparate_extend hsep₀ h_lead)) h_node)
    · exact absurd rfl h_tail
    · rename_i hkey hsep pre hcolon
      exact .mapNest _ _ _ _ _ _ _ _ inject h_open h_sep
        (appendMapEntryFrame pre (.implicitValue _ _ _ _ _ _ _ _ hkey hsep hcolon h_lead h_node)
          (GOpt.none sp_ne))
    · exact absurd rfl h_tail
    · rename_i hq hqsep hkey hsep pre hcolon
      exact .mapNest _ _ _ _ _ _ _ _ inject h_open h_sep
        (appendMapEntryFrame pre
          (.explicitValue _ _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon h_lead h_node)
          (GOpt.none sp_ne))
    · rename_i pre hcolon
      exact .mapNest _ _ _ _ _ _ _ _ inject h_open h_sep
        (appendMapEntryFrame pre (.emptyKeyValue _ _ _ _ _ _ hcolon h_lead h_node)
          (GOpt.none sp_ne))

/-! ### §1c'' Depth-0 flow OPEN — per-pending resume dispatch (B.4β.2)

    A depth-0 `[`/`{` turns the closed flow stack into a depth-1 `FlowOpenStack`.
    The base frame's `resume` closure decides how the eventually-completed flow
    node re-enters the stream derivation, and the right closure depends on the
    incoming `PendingNode`:

    * `noPending` — the flow is a fresh bare document; the leading separation
      `sp_scan → sp_prep` rides in the bare document's `flowInBlock` separator
      slot (`preprocess_some_separate_0_anyCol`, any column, break or not).
    * `pendingContent`/`pendingDocEnd`/`pendingBlockContent`/`pendingFlow` —
      close the prior pending across the leading `SSLComments`
      (`preprocess_flow_thread`), then open a fresh bare document as above,
      the residual whitespace in the separator slot. When NO break was crossed
      at col ≠ 0 the prior construct cannot be closed (`SSLComments` needs a
      break or col 0) — deferred residue (expected vacuous: an inline flow open
      directly after an unclosed same-line construct, e.g. `"foo" [a]`).
    * `pendingDocStart` — the flow is the explicit document's OWN node: route
      the completed node through `h_doc_builder` (`GAlt.left ∘ SLBareDocument.mk
      ∘ flowInBlock`), keeping ONE document. Faithful for `--- [a]`.
    * `pendingBlock` — the flow is the block entry's value: route through
      `h_close ∘ flowInBlock`; the derivation keeps the block entry open, so
      `key: [a]` stays ONE document — THE case that previously rode on
      `scannerDrop`. (Green for `n = 0`, which is what every producer pins.)

    The open itself is uniform (`mk` abstracts `openSeqBase`/`openMapBase`,
    closing over the bracket's `GLit`): the new interior `PendingNode` is
    `noPending sp_open` (interior invariant: inside a flow the pending gap is
    empty — the frame's `st` carries all mid-entry state), and the frame's
    `h_sep := GOpt.none` (post-bracket separation is deferred to the first
    entry step). The stream/stack witnesses vary per route: the fresh-document
    routes re-anchor at the close point with nil stacks; the `pendingBlock`
    route KEEPS the incoming stream and `BlockStack` (the entry stays open,
    its resolution captured in `resume`). -/

lemma accum_flow_open_depth0 (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan sp_prep sp_open : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode false sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_open : ScannerSurfCorr s' sp_open)
    (h_fl1 : s'.flowLevel = 1)
    (h_real : LastTokenReal s'.tokens)
    (h_ad : s'.allowDirectives = false)
    (mk : ∀ (sp_before : SurfPos),
        (∀ sp_ne sp_m, SFlowNode 0 .flowOut sp_prep sp_ne →
         SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m) →
        FlowStackB sp_start 1 s'.flowStack (tailOf s'.tokens) sp_before sp_open) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        GStar SSWhite sp_flow' sp_scan' ∧ LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
  rw [h_fl1]
  have h_stream_block : SLYamlStream sp_start sp_block :=
    absorb_stacksB sp_start sp_gram sp_block sp_block h_stream h_stack (FlowStackB.nil sp_block .sep)
  have h_close_pending : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid :=
    fun sp_mid h_ssl => h_pending.close_with_ssl h_stream_block h_ssl
  -- Shared fresh-bare-document route for the closeable pendings (Pattern 6).
  have main : (∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid) →
      ∃ sp_gram' sp_block' sp_flow' sp_scan',
        SLYamlStream sp_start sp_gram' ∧
        BlockStack sp_gram' sp_block' ∧
        FlowStackB sp_start 1 s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' ∧
        PendingNode false sp_start sp_flow' sp_scan' ∧
        ScannerSurfCorr s' sp_scan' ∧
        ((1 : Nat) ≥ 1 →
          GStar SSWhite sp_flow' sp_scan' ∧ LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
    intro h_close
    rcases preprocess_flow_thread sc sp_scan sp_prep s_prep c h_corr hcorr_prep h_preprocess with
      ⟨sp_mid, h_ssl, hws⟩ | ⟨hcol, hws⟩
    · have h_stream_mid : SLYamlStream sp_start sp_mid := h_close sp_mid h_ssl
      exact ⟨sp_mid, sp_mid, sp_open, sp_open, h_stream_mid, BlockStack.nil sp_mid,
             mk sp_mid (topLevelFlowResumeSep h_stream_mid
               (SSeparateLines.inline 0 sp_mid sp_prep
                 (GStar_SSWhite_to_SSeparateInLine sp_mid sp_prep hws))),
             PendingNode.noPending sp_start sp_open, hcorr_open, fun _ => ⟨GStar.nil _, h_real, h_ad⟩⟩
    · -- col ≠ 0 AND no line break before the bracket: the prior construct
      -- cannot be closed here (`SSLComments` needs a break or col 0). Reachable
      -- only by an inline flow open directly after an unclosed same-line
      -- construct (e.g. `"foo" [a]`), which is invalid YAML — two nodes in one
      -- document.
      --
      -- NOT refutable by `checkFlowAdjacency`: that guard is gated on
      -- `s.inFlow`, and this is the depth-0 open, where it is a no-op. The
      -- vacuity has to come from the depth-0 side — the pending node that is
      -- still open at `col ≠ 0` with no break is precisely `simpleKey.possible`,
      -- so the coupling wanted is `PendingNode`-shape ↔ `sc.simpleKey`, the
      -- depth-0 analogue of 9b(ii)'s `FrameTail` ↔ `tailOf sc.tokens`.
      sorry
  cases h_pending with
  | noPending =>
    -- Nothing to close: the leading separation rides in the fresh bare
    -- document's separator slot directly (any column, break or not).
    obtain ⟨sp_gap, h_sep, hcorr_gap⟩ :=
      preprocess_some_separate_0_anyCol sc _ s_prep c h_corr h_preprocess
    have h_pe : sp_gap = sp_prep := ScannerSurfCorr_unique hcorr_gap hcorr_prep
    subst h_pe
    exact ⟨_, _, sp_open, sp_open, h_stream_block, BlockStack.nil _,
           mk _ (topLevelFlowResumeSep h_stream_block h_sep),
           PendingNode.noPending sp_start sp_open, hcorr_open, fun _ => ⟨GStar.nil _, h_real, h_ad⟩⟩
  | pendingContent => exact main h_close_pending
  | pendingDocEnd => exact main h_close_pending
  | pendingFlow => exact main h_close_pending
  | pendingBlockContent => exact main h_close_pending
  | pendingDocStart =>
    rename_i h_doc_builder
    obtain ⟨sp_gap, h_sep0, hcorr_gap⟩ :=
      preprocess_some_separate_0_anyCol sc sp_scan s_prep c h_corr h_preprocess
    have h_pe : sp_gap = sp_prep := ScannerSurfCorr_unique hcorr_gap hcorr_prep
    have h_sep : SSeparateLines 0 sp_scan sp_prep := h_pe ▸ h_sep0
    exact ⟨sp_block, sp_block, sp_open, sp_open, h_stream_block, BlockStack.nil sp_block,
           mk sp_block (fun sp_ne sp_m h_node h_ssl =>
             SLYamlStream.implicitContinue sp_start sp_block sp_block sp_m sp_m
               h_stream_block (GStar.nil _)
               (GOpt.some sp_block sp_m
                 (h_doc_builder sp_m (GAlt.left sp_scan sp_m
                   (SLBareDocument.mk sp_scan sp_m
                     (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_ne sp_m
                       h_sep h_node h_ssl)))))
               (GStar.nil _)),
           PendingNode.noPending sp_start sp_open, hcorr_open, fun _ => ⟨GStar.nil _, h_real, h_ad⟩⟩
  | pendingBlock =>
    -- 9b(iii): `pendingBlock` now pins its indent to 0 (every producer in this
    -- file builds the zero-indent-normalized entry), so the flow node the open
    -- stack's `resume` supplies — an `SFlowNode 0` — fits `flowInBlock` directly.
    rename_i h_close _
    obtain ⟨sp_gap, h_sep0, hcorr_gap⟩ :=
      preprocess_some_separate_0_anyCol sc sp_scan s_prep c h_corr h_preprocess
    have h_pe : sp_gap = sp_prep := ScannerSurfCorr_unique hcorr_gap hcorr_prep
    have h_sep : SSeparateLines 0 sp_scan sp_prep := h_pe ▸ h_sep0
    exact ⟨sp_gram, sp_block, sp_open, sp_open, h_stream, h_stack,
           mk sp_block (fun sp_ne sp_m h_node h_ssl =>
             h_close sp_m (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_ne sp_m
               h_sep h_node h_ssl)),
           PendingNode.noPending sp_start sp_open, hcorr_open, fun _ => ⟨GStar.nil _, h_real, h_ad⟩⟩

/-! ### §1c''b Token-history readings of the flow dispatch (9b(ii))

    Each flow indicator emits exactly one real token and then advances, so the
    post-dispatch `tailOf` reading is fixed: `[`, `{` and `,` leave `.sep`;
    `]` and `}` leave `.value` (both close tokens complete a flow value).
    Preprocessing in between adds only `saveSimpleKey` reservation placeholders,
    which `lastRealTokenVal?` skips — provided the array already ended in a real
    token, which is what the invariant's `LastTokenReal` conjunct carries. -/

lemma scanFlowSequenceStart_tokens (s : ScannerState) :
    (scanFlowSequenceStart s).tokens =
      s.tokens.push { pos := s.currentPos, val := .flowSequenceStart } := by
  unfold scanFlowSequenceStart
  simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit]
  rfl

lemma scanFlowMappingStart_tokens (s : ScannerState) :
    (scanFlowMappingStart s).tokens =
      s.tokens.push { pos := s.currentPos, val := .flowMappingStart } := by
  unfold scanFlowMappingStart
  simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit]
  rfl

lemma scanFlowSequenceEnd_tokens (s : ScannerState) :
    (scanFlowSequenceEnd s).tokens =
      s.tokens.push { pos := s.currentPos, val := .flowSequenceEnd } := by
  unfold scanFlowSequenceEnd
  simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit]

lemma scanFlowMappingEnd_tokens (s : ScannerState) :
    (scanFlowMappingEnd s).tokens =
      s.tokens.push { pos := s.currentPos, val := .flowMappingEnd } := by
  unfold scanFlowMappingEnd
  simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit]

lemma scanFlowEntry_tokens {s s' : ScannerState} (h : scanFlowEntry s = .ok s') :
    s'.tokens = s.tokens.push { pos := s.currentPos, val := .flowEntry } := by
  unfold scanFlowEntry at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · injection h with h; rw [← h]
      simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit]
  · injection h with h; rw [← h]
    simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit]

/-- After `[` the frame's tail is `.sep`, and the array ends real. -/
lemma tailOf_scanFlowSequenceStart (s : ScannerState) :
    tailOf (scanFlowSequenceStart s).tokens = .sep ∧
    LastTokenReal (scanFlowSequenceStart s).tokens := by
  rw [scanFlowSequenceStart_tokens]; exact tailOf_push (by simp)

/-- After `{` the frame's tail is `.sep`. -/
lemma tailOf_scanFlowMappingStart (s : ScannerState) :
    tailOf (scanFlowMappingStart s).tokens = .sep ∧
    LastTokenReal (scanFlowMappingStart s).tokens := by
  rw [scanFlowMappingStart_tokens]; exact tailOf_push (by simp)

/-- After `]` the parent frame's tail is `.value`: `]` completes a flow value. -/
lemma tailOf_scanFlowSequenceEnd (s : ScannerState) :
    tailOf (scanFlowSequenceEnd s).tokens = .value ∧
    LastTokenReal (scanFlowSequenceEnd s).tokens := by
  rw [scanFlowSequenceEnd_tokens]; exact tailOf_push (by simp)

/-- After `}` the parent frame's tail is `.value`. -/
lemma tailOf_scanFlowMappingEnd (s : ScannerState) :
    tailOf (scanFlowMappingEnd s).tokens = .value ∧
    LastTokenReal (scanFlowMappingEnd s).tokens := by
  rw [scanFlowMappingEnd_tokens]; exact tailOf_push (by simp)

/-- After `,` the frame's tail is `.sep`. -/
lemma tailOf_scanFlowEntry {s s' : ScannerState} (h : scanFlowEntry s = .ok s') :
    tailOf s'.tokens = .sep ∧ LastTokenReal s'.tokens := by
  rw [scanFlowEntry_tokens h]; exact tailOf_push (by simp)

/-! ### §1c''c `allowDirectives` survives the flow dispatch (β.3)

    None of the five indicators touches the flag, so `allowDirectives = false` —
    established once by `allowDirectives_update_false` before the dispatch —
    reaches the post-state unchanged. That is what carries the "no directive
    inside an open flow" half of the interior invariant across a step. -/

open L4YAML.Proofs.ScannerAllowDirectives (advance_preserves_allowDirectives)

lemma scanFlowSequenceStart_allowDirectives (s : ScannerState) :
    (scanFlowSequenceStart s).allowDirectives = s.allowDirectives := by
  unfold scanFlowSequenceStart
  simp only [advance_preserves_allowDirectives, ScannerState.emit]

lemma scanFlowMappingStart_allowDirectives (s : ScannerState) :
    (scanFlowMappingStart s).allowDirectives = s.allowDirectives := by
  unfold scanFlowMappingStart
  simp only [advance_preserves_allowDirectives, ScannerState.emit]

lemma scanFlowSequenceEnd_allowDirectives (s : ScannerState) :
    (scanFlowSequenceEnd s).allowDirectives = s.allowDirectives := by
  unfold scanFlowSequenceEnd
  simp only [advance_preserves_allowDirectives, ScannerState.emit]

lemma scanFlowMappingEnd_allowDirectives (s : ScannerState) :
    (scanFlowMappingEnd s).allowDirectives = s.allowDirectives := by
  unfold scanFlowMappingEnd
  simp only [advance_preserves_allowDirectives, ScannerState.emit]

lemma scanFlowEntry_allowDirectives {s s' : ScannerState} (h : scanFlowEntry s = .ok s') :
    s'.allowDirectives = s.allowDirectives := by
  unfold scanFlowEntry at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · injection h with h; rw [← h]
      simp only [advance_preserves_allowDirectives, ScannerState.emit]
  · injection h with h; rw [← h]
    simp only [advance_preserves_allowDirectives, ScannerState.emit]

/-- Post-dispatch reading, uniform over the five indicators. -/
lemma tailOf_of_emitted {tokens : Array (Positioned YamlToken)} {p : Positioned YamlToken}
    {tokens' : Array (Positioned YamlToken)} {tok : YamlToken}
    (hp : p.val = tok) (ht : tokens' = tokens.push p) (h_ne : tok ≠ .placeholder) :
    tailOf tokens' = FrameTail.ofToken tok ∧ LastTokenReal tokens' := by
  subst ht; subst hp
  exact tailOf_push h_ne

/-- The `allowDirectives` update between structural and flow dispatch is a pure
    flag flip: the token history is untouched. -/
lemma allowDirectives_update_tokens (s : ScannerState) :
    (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true }
    else s).tokens = s.tokens := by
  split <;> rfl

/-- Inside a flow, preprocessing leaves the last real token alone: `skipToContent`
    emits nothing, `unwindIndents` is gated off by `inFlow`, and `saveSimpleKey`'s
    two reservation placeholders are exactly what `lastRealTokenVal?` skips. -/
lemma preprocess_preserves_lastRealTokenVal_inFlow (s s1 : ScannerState) (c : Char)
    (h_flow : 0 < s.flowLevel) (hr : LastTokenReal s.tokens)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    lastRealTokenVal? s1.tokens = lastRealTokenVal? s.tokens := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_tok_skip := ScannerCorrectness.skipToContent_preserves_tokens s s_skip h_skip
    have h_fl_skip := ScannerCorrectness.skipToContent_preserves_flowLevel s s_skip h_skip
    have h_inflow : s_skip.inFlow = true := by
      unfold ScannerState.inFlow; rw [h_fl_skip]; simp; omega
    split at h
    · simp at h
    · split at h
      · -- the `unwindIndents` arm needs `¬inFlow`, which a positive flow level rules out
        rename_i hcond
        exact absurd hcond (by simp [h_inflow])
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [saveSimpleKey_preserves_lastRealTokenVal _ (by rw [h_tok_skip]; exact hr),
                h_tok_skip]

lemma accum_step_flow (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStackB sp_start sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow)
    (h_pending : PendingNode false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      GStar SSWhite sp_flow sp_scan ∧ LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        GStar SSWhite sp_flow' sp_scan' ∧ LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
  -- B.4β.2 (RED CORE): flow dispatch changes `flowLevel`. `[`/`{` push a real
  -- depth-≥1 `FlowOpenStack`, `]`/`}` pop, `,` holds. This skeleton pins the
  -- dispatch case structure (validated against the scanner error semantics); each
  -- production case is a precisely-typed hole. Full design: DOCS § Fix A B.4β.2.
  --
  -- The dispatch runs on `s_ad` = the allowDirectives-updated preprocessed state,
  -- whose `flowLevel` equals `sc.flowLevel`.
  rcases Nat.eq_zero_or_pos sc.flowLevel with h0 | hpos
  · -- ═══ DEPTH 0 (no flow open): only `[`/`{` reach `.ok (some s')`; the closing
    -- and separator indicators error at `flowLevel = 0`. ═══
    rw [h0] at h_flow  -- `FlowStackB sp_start 0 #[] .sep …` = nil
    have h_ad0 : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).flowLevel = 0 :=
      ((allowDirectives_update_flowLevel s_prep).trans
        (preprocess_preserves_flowLevel sc s_prep c h_preprocess)).trans h0
    -- 9b(i): at depth 0 the kinds index is empty, so a `[`/`{` open lands the
    -- scanner's `flowStack` on exactly `#[true]`/`#[false]`.
    have h_ad_ks0 : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).flowStack = #[] :=
      ((allowDirectives_update_flowStack s_prep).trans
        (ScannerFlowStack.preprocess_preserves_flowStack sc s_prep c h_preprocess)).trans
        h_flow.kinds_nil_of_depth_zero
    unfold scanNextToken_dispatchFlowIndicators at h_dispatch
    replace h_dispatch := peel_flowAdj h_dispatch
    simp only [bind, Except.bind, pure, Except.pure] at h_dispatch
    split at h_dispatch
    · -- c == '[' : OPEN flow SEQUENCE, depth 0 → 1 (s'.flowLevel = sc.flowLevel + 1 = 1).
      -- The `_prod` helper recovers the `GLit '['`, the post-bracket corr, and
      -- `flowLevel + 1`; `accum_flow_open_depth0` dispatches the per-pending
      -- `resume` (fresh bare document / block value / explicit document).
      rename_i heq
      have hc : c = '[' := by simpa using heq
      subst hc
      obtain ⟨sp_prep, hcorr_prep⟩ :=
        scanNextToken_preprocess_corr sc sp_scan h_corr s_prep '[' h_preprocess
      have hpeek_disp : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).peek? = some '[' := by
        have hpk := preprocess_some_peek h_preprocess
        split
        · show s_prep.peek? = some '['; exact hpk
        · exact hpk
      obtain ⟨sp_open, h_open, hcorr_open, h_fl⟩ :=
        scanFlowSequenceStart_prod _ sp_prep (corr_of_allowDirectives_update hcorr_prep) hpeek_disp
      have hs := Option.some.inj (Except.ok.inj h_dispatch)
      subst hs
      have h_pos := h_flow.pos_eq_of_depth_zero
      subst h_pos
      exact accum_flow_open_depth0 sc sp_start sp_gram _ sp_scan sp_prep sp_open
        s_prep _ '[' h_stream h_stack h_pending h_corr h_preprocess hcorr_prep
        hcorr_open (by rw [h_fl, h_ad0]) (tailOf_scanFlowSequenceStart _).2
        ((scanFlowSequenceStart_allowDirectives _).trans (allowDirectives_update_false s_prep))
        (fun _ resume => by
          rw [ScannerFlowCollection.scanFlowSequenceStart_pushes_true, h_ad_ks0,
              (tailOf_scanFlowSequenceStart _).1,
              show (#[] : Array Bool).push true = #[true] from rfl]
          exact FlowStackB.openSeqBase resume h_open (GOpt.none sp_open))
    · split at h_dispatch
      · -- c == ']' at depth 0: `if flowLevel == 0 then .error` — flowLevel = 0 ⇒ error.
        rw [h_ad0] at h_dispatch; simp at h_dispatch
      · split at h_dispatch
        · -- c == '{' : OPEN flow MAPPING, depth 0 → 1 (mirror of `[` with openMapBase).
          rename_i heq
          have hc : c = '{' := by simpa using heq
          subst hc
          obtain ⟨sp_prep, hcorr_prep⟩ :=
            scanNextToken_preprocess_corr sc sp_scan h_corr s_prep '{' h_preprocess
          have hpeek_disp : (if s_prep.allowDirectives then
              { s_prep with allowDirectives := false, documentEverStarted := true }
            else s_prep).peek? = some '{' := by
            have hpk := preprocess_some_peek h_preprocess
            split
            · show s_prep.peek? = some '{'; exact hpk
            · exact hpk
          obtain ⟨sp_open, h_open, hcorr_open, h_fl⟩ :=
            scanFlowMappingStart_prod _ sp_prep (corr_of_allowDirectives_update hcorr_prep) hpeek_disp
          have hs := Option.some.inj (Except.ok.inj h_dispatch)
          subst hs
          have h_pos := h_flow.pos_eq_of_depth_zero
          subst h_pos
          exact accum_flow_open_depth0 sc sp_start sp_gram _ sp_scan sp_prep sp_open
            s_prep _ '{' h_stream h_stack h_pending h_corr h_preprocess hcorr_prep
            hcorr_open (by rw [h_fl, h_ad0]) (tailOf_scanFlowMappingStart _).2
            ((scanFlowMappingStart_allowDirectives _).trans (allowDirectives_update_false s_prep))
            (fun _ resume => by
              rw [ScannerFlowCollection.scanFlowMappingStart_pushes_false, h_ad_ks0,
                  (tailOf_scanFlowMappingStart _).1,
                  show (#[] : Array Bool).push false = #[false] from rfl]
              exact FlowStackB.openMapBase resume h_open (GOpt.none sp_open))
        · split at h_dispatch
          · -- c == '}' at depth 0: error (flowLevel == 0).
            rw [h_ad0] at h_dispatch; simp at h_dispatch
          · split at h_dispatch
            · -- c == ',' at depth 0: error (flowLevel == 0).
              rw [h_ad0] at h_dispatch; simp at h_dispatch
            · -- fallthrough: dispatch returns `.ok none`, not `.ok (some s')`.
              simp at h_dispatch
  · -- ═══ DEPTH ≥ 1 (inside ≥1 open flow collections). ═══
    -- Interior invariant (`h_interior`): the pending gap is empty — every
    -- mid-entry state lives in the top `FlowOpenStack` frame's `st`. Each arm
    -- consumes its OWN leading separation `sp_flow → sp_prep` and threads it
    -- through the §1c''a frame transitions (`receiveNode` / `closeWithSep` /
    -- `holdComma`). Kind-mismatched closes (`]` on a map frame, `}` on a seq
    -- frame) are scan-ACCEPTED today (no bracket-kind check in the scanner) —
    -- those arms are the item-9a residues (flow-close kind strictening + the
    -- `sc.flowStack` kind coupling).
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 := ⟨sc.flowLevel - 1, by omega⟩
    have h_real_sc : LastTokenReal sc.tokens := (h_interior hpos).2.1
    -- β.3: the accumulation's flow endpoint may sit a whitespace run BEHIND the
    -- scanner cursor (a flow-interior plain scalar ends its production before the
    -- whitespace `collectPlainScalarLoop` then consumes).  The step's leading
    -- separation is derived at the cursor and walked back to the endpoint, which
    -- is where the frame's pending `GOpt (SSeparate 0 c)` slot expects it.
    have h_white : GStar SSWhite sp_flow sp_scan := (h_interior hpos).1
    obtain ⟨sp_prep, h_lead0, hcorr_prep⟩ :=
      preprocess_some_separate_0_anyCol sc sp_scan s_prep c h_corr h_preprocess
    have h_lead : SSeparateLines 0 sp_flow sp_prep :=
      SSeparateLines_prepend_white h_white h_lead0
    have h_ad_fl : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).flowLevel = sc.flowLevel :=
      (allowDirectives_update_flowLevel s_prep).trans
        (preprocess_preserves_flowLevel sc s_prep c h_preprocess)
    -- 9b(i)/(ii): name the kinds and frame-tail indices so `cases` on the frame
    -- stack substitutes them, and carry the scanner-side equations
    -- `s_ad.flowStack = ks` / `tailOf s_ad.tokens = tl` alongside. The tail one
    -- rides on `LastTokenReal sc.tokens`: preprocessing's `saveSimpleKey` may
    -- push two reservation placeholders, and `lastRealTokenVal?` skips exactly
    -- those two only when the array already ended in a real token.
    obtain ⟨ks, hks⟩ : ∃ ks, sc.flowStack = ks := ⟨_, rfl⟩
    obtain ⟨tl, htl⟩ : ∃ tl, tailOf sc.tokens = tl := ⟨_, rfl⟩
    have h_ad_ks : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).flowStack = ks :=
      ((allowDirectives_update_flowStack s_prep).trans
        (ScannerFlowStack.preprocess_preserves_flowStack sc s_prep c h_preprocess)).trans hks
    have h_ad_tl : tailOf (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).tokens = tl := by
      unfold tailOf
      rw [allowDirectives_update_tokens,
          preprocess_preserves_lastRealTokenVal_inFlow sc s_prep c (by omega) h_real_sc
            h_preprocess]
      rw [← htl]; rfl
    have h_ad_inflow : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).inFlow = true := by
      unfold ScannerState.inFlow; rw [h_ad_fl]; simp; omega
    rw [hd, hks, htl] at h_flow
    have h_fos := h_flow.open_of_succ
    unfold scanNextToken_dispatchFlowIndicators at h_dispatch
    have h_adj := flowAdj_ok_of_dispatch_ok h_dispatch
    replace h_dispatch := peel_flowAdj h_dispatch
    simp only [bind, Except.bind, pure, Except.pure] at h_dispatch
    -- Abstract the allowDirectives-updated state so the dispatch splits land
    -- on the flowLevel/validate/scanFlowEntry decision points (not on the
    -- update `if` itself).
    have hcorr_ad := corr_of_allowDirectives_update hcorr_prep
    have hpeek_ad : (if s_prep.allowDirectives = true then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).peek? = s_prep.peek? := by split <;> rfl
    generalize h_ad_def : (if s_prep.allowDirectives = true then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep) = s_ad at h_dispatch h_adj
    rw [h_ad_def] at h_ad_fl h_ad_ks h_ad_tl h_ad_inflow hcorr_ad hpeek_ad
    -- β.3: the dispatch runs AFTER the `allowDirectives` update, so the flag is
    -- already cleared here; none of the five indicators touches it, which is how
    -- the interior invariant's "no directive inside an open flow" half survives.
    have h_ad_false : s_ad.allowDirectives = false := by
      rw [← h_ad_def]; exact allowDirectives_update_false s_prep
    split at h_dispatch
    · -- '[': NESTED PUSH, depth d+1 → d+2. The child seq frame's `inject` is
      -- `receiveNode` on the parent (folding the eventual child node + this
      -- step's leading sep into the parent frame).
      rename_i heq
      have hc : c = '[' := by simpa using heq
      subst hc
      obtain ⟨sp_tok, h_open_lit, hcorr_tok, h_fl⟩ :=
        scanFlowSequenceStart_prod s_ad sp_prep hcorr_ad
          (hpeek_ad.trans (preprocess_some_peek h_preprocess))
      have hs := Option.some.inj (Except.ok.inj h_dispatch)
      subst hs
      -- 9b(ii): a `[` is a node start, so the adjacency check having passed says
      -- the previous real token did not complete a flow value — the parent frame
      -- is receptive.
      have h_tail : tl ≠ .value := by
        rw [← h_ad_tl]
        exact tailOf_ne_value
          (notCompletes_of_checkFlowAdjacency_ok h_adj h_ad_inflow ⟨by decide, by decide,
            by decide, by decide⟩)
      rw [h_fl, h_ad_fl, hd,
          ScannerFlowCollection.scanFlowSequenceStart_pushes_true, h_ad_ks,
          (tailOf_scanFlowSequenceStart _).1]
      exact ⟨sp_gram, sp_block, sp_tok, sp_tok, h_stream, h_stack,
        .open (d + 1 + 1) (ks.push true) .sep sp_block sp_tok
          (.seqNest (d + 1) ks .sep sp_block sp_prep sp_tok sp_tok sp_tok
            (FlowOpenStack.receiveNode h_fos h_tail h_lead) h_open_lit (GOpt.none sp_tok)
            (.betweenEmpty sp_tok)),
        PendingNode.noPending sp_start sp_tok, hcorr_tok,
        fun _ => ⟨GStar.nil _, (tailOf_scanFlowSequenceStart _).2,
          (scanFlowSequenceStart_allowDirectives _).trans h_ad_false⟩⟩
    · split at h_dispatch
      · -- ']': POP, depth d+1 → d.
        rename_i heq
        have hc : c = ']' := by simpa using heq
        subst hc
        split at h_dispatch
        · -- flowLevel == 0 arm: h_dispatch is an error.
          simp at h_dispatch
        · split at h_dispatch
          · -- flowStack kind-check mismatch (9a strictening): error.
            simp at h_dispatch
          · -- 9a's kind check passed, so the scanner's innermost open marker is a
            -- SEQUENCE; 9b(i)'s kinds index transports that to the top FRAME.
            rename_i h_kind
            have h_back : ks.back? = some true := by
              rw [← h_ad_ks]; simpa using h_kind
            split at h_dispatch
            · -- validateFlowClose errored: h_dispatch is an error.
              simp at h_dispatch
            · have h_ad_pos : s_ad.flowLevel > 0 := by rw [h_ad_fl, hd]; omega
              obtain ⟨sp_tok, h_close_lit, hcorr_tok, h_fl⟩ :=
                scanFlowSequenceEnd_prod s_ad sp_prep hcorr_ad
                  (hpeek_ad.trans (preprocess_some_peek h_preprocess)) h_ad_pos
              have hs := Option.some.inj (Except.ok.inj h_dispatch)
              subst hs
              have h_fl' : (scanFlowSequenceEnd s_ad).flowLevel = d := by
                rw [h_fl, h_ad_fl, hd]; omega
              rw [h_fl', ScannerFlowCollection.scanFlowSequenceEnd_pops, h_ad_ks,
                  (tailOf_scanFlowSequenceEnd _).1]
              cases h_fos
              · -- seqBase (d = 0): close the outermost seq; the completed node
                -- re-enters the stream via `resume`, parked as `pendingContent`
                -- until the next step's SSLComments.
                rename_i resume h_open h_sep st
                have h_seq := SeqFrame.closeWithSep h_open h_sep st h_lead h_lead h_close_lit
                rw [show (#[true] : Array Bool).pop = #[] from rfl]
                exact ⟨sp_gram, sp_block, sp_block, sp_tok, h_stream, h_stack,
                  FlowStackB.nil sp_block _,
                  PendingNode.pendingContent sp_start sp_block sp_tok
                    (fun sp_m h_ssl => resume sp_tok sp_m
                      (SFlowNode.content _ _ _ _ (SFlowContent.flowSeq _ _ _ _ h_seq)) h_ssl),
                  hcorr_tok, fun h => absurd h (by omega)⟩
              · -- mapBase + ']': kind-mismatched close (`{a]`). REFUTED (9a+9b(i)):
                -- the scanner only reaches this dispatch with `flowStack.back? =
                -- some true`, but a mapping base frame pins the kinds index to
                -- `#[false]`.
                simp at h_back
              · -- seqNest (d ≥ 1): close the nested seq and fold it into the
                -- parent via `inject`.
                rename_i h_open h_sep inject st
                have h_seq := SeqFrame.closeWithSep h_open h_sep st h_lead h_lead h_close_lit
                rw [Array.pop_push]
                exact ⟨sp_gram, sp_block, sp_tok, sp_tok, h_stream, h_stack,
                  .open _ _ _ sp_block sp_tok (inject sp_tok
                    (SFlowNode.content _ _ _ _ (SFlowContent.flowSeq _ _ _ _ h_seq))),
                  PendingNode.noPending sp_start sp_tok, hcorr_tok,
                  fun _ => ⟨GStar.nil _, (tailOf_scanFlowSequenceEnd _).2,
                    (scanFlowSequenceEnd_allowDirectives _).trans h_ad_false⟩⟩
              · -- mapNest + ']': kind-mismatched close (`{a]` nested). REFUTED.
                simp at h_back
      · split at h_dispatch
        · -- '{': NESTED PUSH, depth d+1 → d+2 (mirror of '[').
          rename_i heq
          have hc : c = '{' := by simpa using heq
          subst hc
          obtain ⟨sp_tok, h_open_lit, hcorr_tok, h_fl⟩ :=
            scanFlowMappingStart_prod s_ad sp_prep hcorr_ad
              (hpeek_ad.trans (preprocess_some_peek h_preprocess))
          have hs := Option.some.inj (Except.ok.inj h_dispatch)
          subst hs
          have h_tail : tl ≠ .value := by
            rw [← h_ad_tl]
            exact tailOf_ne_value
              (notCompletes_of_checkFlowAdjacency_ok h_adj h_ad_inflow ⟨by decide, by decide,
                by decide, by decide⟩)
          rw [h_fl, h_ad_fl, hd,
              ScannerFlowCollection.scanFlowMappingStart_pushes_false, h_ad_ks,
              (tailOf_scanFlowMappingStart _).1]
          exact ⟨sp_gram, sp_block, sp_tok, sp_tok, h_stream, h_stack,
            .open (d + 1 + 1) (ks.push false) .sep sp_block sp_tok
              (.mapNest (d + 1) ks .sep sp_block sp_prep sp_tok sp_tok sp_tok
                (FlowOpenStack.receiveNode h_fos h_tail h_lead) h_open_lit (GOpt.none sp_tok)
                (.betweenEmpty sp_tok)),
            PendingNode.noPending sp_start sp_tok, hcorr_tok,
            fun _ => ⟨GStar.nil _, (tailOf_scanFlowMappingStart _).2,
              (scanFlowMappingStart_allowDirectives _).trans h_ad_false⟩⟩
        · split at h_dispatch
          · -- '}': POP, depth d+1 → d (mirror of ']').
            rename_i heq
            have hc : c = '}' := by simpa using heq
            subst hc
            split at h_dispatch
            · simp at h_dispatch
            · split at h_dispatch
              · -- flowStack kind-check mismatch (9a strictening): error.
                simp at h_dispatch
              · -- 9a's kind check passed: the innermost open marker is a MAPPING.
                rename_i h_kind
                have h_back : ks.back? = some false := by
                  rw [← h_ad_ks]; simpa using h_kind
                split at h_dispatch
                · simp at h_dispatch
                · have h_ad_pos : s_ad.flowLevel > 0 := by rw [h_ad_fl, hd]; omega
                  obtain ⟨sp_tok, h_close_lit, hcorr_tok, h_fl⟩ :=
                    scanFlowMappingEnd_prod s_ad sp_prep hcorr_ad
                      (hpeek_ad.trans (preprocess_some_peek h_preprocess)) h_ad_pos
                  have hs := Option.some.inj (Except.ok.inj h_dispatch)
                  subst hs
                  have h_fl' : (scanFlowMappingEnd s_ad).flowLevel = d := by
                    rw [h_fl, h_ad_fl, hd]; omega
                  rw [h_fl', ScannerFlowCollection.scanFlowMappingEnd_pops, h_ad_ks,
                      (tailOf_scanFlowMappingEnd _).1]
                  cases h_fos
                  · -- seqBase + '}': kind-mismatched close (`[a}`). REFUTED
                    -- (9a+9b(i)): a sequence base frame pins the index to `#[true]`.
                    simp at h_back
                  · -- mapBase (d = 0): close the outermost map via `resume`.
                    rename_i resume h_open h_sep st
                    have h_map := MapFrame.closeWithSep h_open h_sep st h_lead h_lead h_close_lit
                    rw [show (#[false] : Array Bool).pop = #[] from rfl]
                    exact ⟨sp_gram, sp_block, sp_block, sp_tok, h_stream, h_stack,
                      FlowStackB.nil sp_block _,
                      PendingNode.pendingContent sp_start sp_block sp_tok
                        (fun sp_m h_ssl => resume sp_tok sp_m
                          (SFlowNode.content _ _ _ _ (SFlowContent.flowMap _ _ _ _ h_map)) h_ssl),
                      hcorr_tok, fun h => absurd h (by omega)⟩
                  · -- seqNest + '}': kind-mismatched close (`[a}` nested). REFUTED.
                    simp at h_back
                  · -- mapNest (d ≥ 1): close the nested map, fold via `inject`.
                    rename_i h_open h_sep inject st
                    have h_map := MapFrame.closeWithSep h_open h_sep st h_lead h_lead h_close_lit
                    rw [Array.pop_push]
                    exact ⟨sp_gram, sp_block, sp_tok, sp_tok, h_stream, h_stack,
                      .open _ _ _ sp_block sp_tok (inject sp_tok
                        (SFlowNode.content _ _ _ _ (SFlowContent.flowMap _ _ _ _ h_map))),
                      PendingNode.noPending sp_start sp_tok, hcorr_tok,
                      fun _ => ⟨GStar.nil _, (tailOf_scanFlowMappingEnd _).2,
                        (scanFlowMappingEnd_allowDirectives _).trans h_ad_false⟩⟩
          · split at h_dispatch
            · -- ',': HOLD, depth unchanged — finish any mid entry (trailing
              -- sep = this step's leading sep), land the frame in `held`.
              rename_i heq
              have hc : c = ',' := by simpa using heq
              subst hc
              split at h_dispatch
              · simp at h_dispatch
              · split at h_dispatch
                · simp at h_dispatch
                · rename_i s_fe hfe
                  have hs := Option.some.inj (Except.ok.inj h_dispatch)
                  subst hs
                  obtain ⟨sp_tok, h_comma_lit, hcorr_tok, h_fl⟩ :=
                    scanFlowEntry_prod s_ad sp_prep hcorr_ad
                      (hpeek_ad.trans (preprocess_some_peek h_preprocess)) hfe
                  have h_fl' : s_fe.flowLevel = d + 1 := by rw [h_fl, h_ad_fl, hd]
                  have h_ks' : s_fe.flowStack = ks := by
                    rw [ScannerFlowCollection.scanFlowEntry_preserves_flowStack s_ad s_fe hfe,
                        h_ad_ks]
                  -- 9b(ii): `scanFlowEntry` having succeeded says the previous real
                  -- token was neither a flow-open indicator nor another `,`, so the
                  -- frame is not in a `.sep` tail (`[,`, `,,` are the rejected shapes).
                  have h_tail : tl ≠ .sep := by
                    rw [← h_ad_tl]; exact tailOf_ne_sep (notSepTok_of_scanFlowEntry_ok hfe)
                  rw [h_fl', h_ks', (tailOf_scanFlowEntry hfe).1]
                  cases h_fos
                  · rename_i resume h_open h_sep st
                    exact ⟨sp_gram, sp_block, sp_tok, sp_tok, h_stream, h_stack,
                      .open _ _ _ sp_block sp_tok (.seqBase _ _ _ _ _ _ resume h_open h_sep
                        (st.holdComma h_tail h_lead h_comma_lit)),
                      PendingNode.noPending sp_start sp_tok, hcorr_tok,
                      fun _ => ⟨GStar.nil _, (tailOf_scanFlowEntry hfe).2,
                        (scanFlowEntry_allowDirectives hfe).trans h_ad_false⟩⟩
                  · rename_i resume h_open h_sep st
                    exact ⟨sp_gram, sp_block, sp_tok, sp_tok, h_stream, h_stack,
                      .open _ _ _ sp_block sp_tok (.mapBase _ _ _ _ _ _ resume h_open h_sep
                        (st.holdComma h_tail h_lead h_comma_lit)),
                      PendingNode.noPending sp_start sp_tok, hcorr_tok,
                      fun _ => ⟨GStar.nil _, (tailOf_scanFlowEntry hfe).2,
                        (scanFlowEntry_allowDirectives hfe).trans h_ad_false⟩⟩
                  · rename_i h_open h_sep inject st
                    exact ⟨sp_gram, sp_block, sp_tok, sp_tok, h_stream, h_stack,
                      .open _ _ _ sp_block sp_tok (.seqNest _ _ _ _ _ _ _ _ inject h_open h_sep
                        (st.holdComma h_tail h_lead h_comma_lit)),
                      PendingNode.noPending sp_start sp_tok, hcorr_tok,
                      fun _ => ⟨GStar.nil _, (tailOf_scanFlowEntry hfe).2,
                        (scanFlowEntry_allowDirectives hfe).trans h_ad_false⟩⟩
                  · rename_i h_open h_sep inject st
                    exact ⟨sp_gram, sp_block, sp_tok, sp_tok, h_stream, h_stack,
                      .open _ _ _ sp_block sp_tok (.mapNest _ _ _ _ _ _ _ _ inject h_open h_sep
                        (st.holdComma h_tail h_lead h_comma_lit)),
                      PendingNode.noPending sp_start sp_tok, hcorr_tok,
                      fun _ => ⟨GStar.nil _, (tailOf_scanFlowEntry hfe).2,
                        (scanFlowEntry_allowDirectives hfe).trans h_ad_false⟩⟩
            · -- fallthrough: dispatch returns `.ok none`, not `.ok (some s')`.
              simp at h_dispatch

/-! ### §1d Preprocessing + Block Indicator Dispatch

    `scanNextToken_dispatchBlockIndicators` handles `-`, `?`, `:`.
    This is the core of block collection accumulation:

    1. Preprocessing may unwind indent levels → BlockStack pops
    2. `pushSequenceIndent`/`pushMappingIndent` may push → BlockStack pushes
    3. The indicator character is consumed → pendingBlock

    **Scanner → BlockStack correspondence:**
    - `scanBlockEntry` calls `pushSequenceIndent s s.col`:
      If `col > currentIndent` → `.seqLevel col` pushed onto BlockStack
    - `scanKey` calls `pushMappingIndent s s.col`:
      If `col > currentIndent` → `.mapLevel col` pushed onto BlockStack
    - `scanValue` calls `scanValuePrepare` which may retroactively emit
      `.blockMappingStart` → `.mapLevel` pushed if needed

    **Proven case**: `BlockStack.nil` + `PendingNode.noPending`.
    No pending to close. Block indicator opens `pendingBlock`. -/

-- Helper: block indicator dispatch preserves `ScannerSurfCorr` on `some` paths.
lemma dispatchBlockIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_dispatchBlockIndicators sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- c == '-' && !inFlow && isBlockEntryCandidate
  split at hok
  · split at hok
    · simp at hok
    · rename_i s_be hbe
      have h := Except.ok.inj hok; injection h with h; subst h
      exact scanBlockEntry_corr sc sp hcorr s_be hbe
  -- c == '?' && isKeyCandidate
  · split at hok
    · split at hok
      · simp at hok
      · rename_i s_k hk
        have h := Except.ok.inj hok; injection h with h; subst h
        exact scanKey_corr sc sp hcorr s_k hk
    -- c == ':' && isValueCandidate
    · split at hok
      · split at hok
        · simp at hok
        · rename_i s_v hv
          have h := Except.ok.inj hok; injection h with h; subst h
          exact scanValue_corr sc sp hcorr s_v hv
      -- none (fallthrough)
      · simp at hok

-- Block entry dispatch full production: GLit '-' + GNot SNsChar + ScannerSurfCorr.
-- Unfolds dispatchBlockIndicators for the '-' case. The result includes:
-- 1) A literal dash character
-- 2) Negative lookahead: the char after '-' is not ns-char
-- 3) Scanner/surface correspondence after the dash
lemma dispatchBlockEntry_full_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '-')
    (hok : scanNextToken_dispatchBlockIndicators sc '-' = .ok (some s')) :
    ∃ sp', GLit '-' sp sp' ∧ GNot SNsChar sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- '-' == '-' && ... is true: enter scanBlockEntry path
    rename_i h_entry_cond
    have h_candidate : isBlockEntryCandidate sc = true := by
      simp [Bool.and_eq_true] at h_entry_cond; exact h_entry_cond.2
    split at hok
    · simp at hok
    · rename_i s_be hbe
      have h := Except.ok.inj hok; injection h with h; subst h
      obtain ⟨sp', h_lit, hcorr'⟩ := scanBlockEntry_prod sc ⟨'-' :: rest, sc.col⟩
        hcorr hpeek s_be hbe
      cases h_lit
      exact ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col,
             blockEntryCandidate_gnot sc rest sc.col hcorr h_candidate, hcorr'⟩
  · -- First branch failed: '-' ≠ '?' and '-' ≠ ':' means remaining dispatch returns none
    have hq : ('-' == '?' : Bool) = false := by native_decide
    have hc : ('-' == ':' : Bool) = false := by native_decide
    simp only [hq, hc, Bool.false_and, if_neg Bool.false_ne_true] at hok
    simp at hok

/-! #### Wadler-style per-constructor theorems for block dispatch (Layer 4o/4x)

    Each theorem handles one substantial `PendingNode` constructor case for
    `accum_block_pending`. The main theorem delegates to these after the
    shared preamble (corr extraction + `h_close_pending`). Non-proven
    branches (cons/c≠'-'/col≠0/n≠0) delegate to `block_dispatch_deferred`. -/

-- Deferred sorry: constructs pendingFlow with stream evidence.
-- Concentrates all block-dispatch catch-all sorry into close_with_ssl.
-- Called for: whitespace-before-dash (cons), non-dash indicators (c≠'-'),
-- col≠0 no-break, and n≠0 pending cases.
lemma block_dispatch_deferred
    (sp_start sp_X sp_scan' : SurfPos) (s' : ScannerState)
    (h_stream : SLYamlStream sp_start sp_X)
    (hcorr : ScannerSurfCorr s' sp_scan') :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' :=
  ⟨sp_X, sp_X, sp_X, sp_scan', h_stream,
   BlockStack.nil sp_X, FlowStackB.nil sp_X .sep,
   PendingNode.pendingFlow sp_start sp_X sp_scan' h_stream,
   hcorr⟩

-- Block dispatch with noPending: fresh block entry.
-- Handles '-' at col=0 with full closures; non-proven branches delegate
-- to block_dispatch_deferred.
lemma accum_block_on_noPending
    (sc : ScannerState) (sp_start sp_block : SurfPos)
    (s_prep s' : ScannerState) (c : Char) (sp_prep sp_scan' : SurfPos)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (h_corr : ScannerSurfCorr sc sp_block)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  by_cases hcol : sp_block.col = 0
  · by_cases hc : c = '-'
    · subst hc
      have hpeek_disp : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).peek? = some '-' := by
        have := preprocess_some_peek h_preprocess
        split
        · show s_prep.peek? = some '-'; exact this
        · exact this
      obtain ⟨sp_dash, h_dash, h_gnot, hcorr_dash⟩ :=
        dispatchBlockEntry_full_prod _ sp_prep
          (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
      have hsp_dash_eq := ScannerSurfCorr_unique hcorr_dash hcorr_result
      rw [hsp_dash_eq] at h_dash h_gnot
      obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl_pre, hcol_mid, hws, hcmt, hcorr_sc, h_pk⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_block s_prep '-' h_corr hcol h_preprocess
      have hsp_sc_eq := ScannerSurfCorr_unique hcorr_sc hcorr_prep
      subst hsp_sc_eq
      cases hws with
      | nil =>
        cases hcmt with
        | none =>
          exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                 BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
                 PendingNode.pendingBlock sp_start sp_block sp_scan'
                   (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                     have h_indented :=
                       SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                     have h_entry :=
                       SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' sp_scan' sp_final
                         (SIndent.zero sp_mid) h_dash h_gnot h_indented
                     have h_block :=
                       SBlockNode.blockSeq 0 .blockIn sp_block sp_block sp_mid sp_final
                         (GOpt.none sp_block) h_ssl_pre h_entry
                     have h_bare := SLBareDocument.mk sp_block sp_final h_block
                     SLYamlStream.implicitContinue sp_start sp_block sp_block sp_final sp_final
                       h_stream_block (GStar.nil _)
                       (GOpt.some sp_block sp_final
                         (SLAnyDocument.bare sp_block sp_final h_bare))
                       (GStar.nil _))
                   (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                     have h_indented :=
                       SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                     have h_entry :=
                       SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' sp_scan' sp_final
                         (SIndent.zero sp_mid) h_dash h_gnot h_indented
                     ⟨sp_mid, h_entry, fun sp_end h_entries =>
                       have h_block :=
                         SBlockNode.blockSeq 0 .blockIn sp_block sp_block sp_mid sp_end
                           (GOpt.none sp_block) h_ssl_pre h_entries
                       have h_bare := SLBareDocument.mk sp_block sp_end h_block
                       SLYamlStream.implicitContinue sp_start sp_block sp_block sp_end sp_end
                         h_stream_block (GStar.nil _)
                         (GOpt.some sp_block sp_end
                           (SLAnyDocument.bare sp_block sp_end h_bare))
                         (GStar.nil _)⟩),
                 hcorr_result⟩
        | some =>
          rename_i hc
          have h_eq := h_pk.resolve_right (by simp [preprocess_some_peek h_preprocess])
          exact absurd (h_eq ▸ hc) (scNbCommentText_irrefl sp_mid)
      | cons =>
        exact block_dispatch_deferred sp_start sp_block sp_scan' s' h_stream_block hcorr_result
    · exact block_dispatch_deferred sp_start sp_block sp_scan' s' h_stream_block hcorr_result
  · exact block_dispatch_deferred sp_start sp_block sp_scan' s' h_stream_block hcorr_result

-- Block dispatch after closing old pending: '-' at col=0 opens new block sequence.
-- Shared by pendingContent and pendingFlow constructors.
lemma accum_block_on_closeThenBlock
    (sc : ScannerState) (sp_start sp_block_ctx sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char) (sp_prep sp_scan' : SurfPos)
    (h_close_pending : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid)
    (h_stream_fallback : SLYamlStream sp_start sp_block_ctx)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  by_cases hcol : sp_scan.col = 0
  · by_cases hc : c = '-'
    · subst hc
      obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, hcorr_sc, h_pk⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep '-' h_corr hcol h_preprocess
      have hsp_sc_eq := ScannerSurfCorr_unique hcorr_sc hcorr_prep
      subst hsp_sc_eq
      have h_stream_new := h_close_pending sp_mid h_ssl
      cases hws with
      | nil =>
        cases hcmt with
        | none =>
          have hpeek_disp : (if s_prep.allowDirectives then
              { s_prep with allowDirectives := false, documentEverStarted := true }
            else s_prep).peek? = some '-' := by
            have := preprocess_some_peek h_preprocess
            split
            · show s_prep.peek? = some '-'; exact this
            · exact this
          obtain ⟨sp_dash, h_dash, h_gnot, hcorr_dash⟩ :=
            dispatchBlockEntry_full_prod _ sp_mid
              (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
          have hsp_dash_eq := ScannerSurfCorr_unique hcorr_dash hcorr_result
          rw [hsp_dash_eq] at h_dash h_gnot
          have hcol_eq : sp_mid = ⟨sp_mid.chars, 0⟩ := by
            cases sp_mid; simp at hcol_mid; simp [hcol_mid]
          have h_ssl_zero : SSLComments sp_mid sp_mid :=
            hcol_eq ▸ SSLComments.startOfLine sp_mid.chars ⟨sp_mid.chars, 0⟩
              (GStar.nil ⟨sp_mid.chars, 0⟩)
          exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream_new,
                 BlockStack.nil sp_mid, FlowStackB.nil sp_mid .sep,
                 PendingNode.pendingBlock sp_start sp_mid sp_scan'
                   (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                     have h_indented :=
                       SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                     have h_entry :=
                       SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' sp_scan' sp_final
                         (SIndent.zero sp_mid) h_dash h_gnot h_indented
                     have h_block :=
                       SBlockNode.blockSeq 0 .blockIn sp_mid sp_mid sp_mid sp_final
                         (GOpt.none sp_mid) h_ssl_zero h_entry
                     have h_bare := SLBareDocument.mk sp_mid sp_final h_block
                     SLYamlStream.implicitContinue sp_start sp_mid sp_mid sp_final sp_final
                       h_stream_new (GStar.nil _)
                       (GOpt.some sp_mid sp_final
                         (SLAnyDocument.bare sp_mid sp_final h_bare))
                       (GStar.nil _))
                   (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                     have h_indented :=
                       SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                     have h_entry :=
                       SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' sp_scan' sp_final
                         (SIndent.zero sp_mid) h_dash h_gnot h_indented
                     ⟨sp_mid, h_entry, fun sp_end h_entries =>
                       have h_block :=
                         SBlockNode.blockSeq 0 .blockIn sp_mid sp_mid sp_mid sp_end
                           (GOpt.none sp_mid) h_ssl_zero h_entries
                       have h_bare := SLBareDocument.mk sp_mid sp_end h_block
                       SLYamlStream.implicitContinue sp_start sp_mid sp_mid sp_end sp_end
                         h_stream_new (GStar.nil _)
                         (GOpt.some sp_mid sp_end
                           (SLAnyDocument.bare sp_mid sp_end h_bare))
                         (GStar.nil _)⟩),
                 hcorr_result⟩
        | some =>
          rename_i hc
          have h_eq := h_pk.resolve_right (by simp [preprocess_some_peek h_preprocess])
          exact absurd (h_eq ▸ hc) (scNbCommentText_irrefl sp_mid)
      | cons =>
        exact block_dispatch_deferred sp_start sp_mid sp_scan' s' h_stream_new hcorr_result
    · obtain ⟨sp_mid, _, _, h_ssl, _, _, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      exact block_dispatch_deferred sp_start sp_mid sp_scan' s'
        (h_close_pending sp_mid h_ssl) hcorr_result
  · obtain ⟨sp_mid, _, _, h_disj, _, _, _, _⟩ :=
      preprocess_some_ssl_comments_anyCol sc sp_scan s_prep c h_corr h_preprocess
    cases h_disj with
    | inl h_ssl_col =>
      exact block_dispatch_deferred sp_start sp_mid sp_scan' s'
        (h_close_pending sp_mid h_ssl_col.1) hcorr_result
    | inr h_mid_eq =>
      subst h_mid_eq
      exact block_dispatch_deferred sp_start sp_block_ctx sp_scan' s'
        h_stream_fallback hcorr_result

-- Block dispatch with pendingBlockContent: accumulate entries via h_entry_old.
lemma accum_block_on_pendingBlockContent
    (sc : ScannerState) (sp_start sp_block sp_block_ctx sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char) (sp_prep sp_scan' : SurfPos)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_close_pending : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid)
    (h_stream_fallback : SLYamlStream sp_start sp_block_ctx)
    (h_closable : ∀ (sp : SurfPos), SSLComments sp_scan sp → SLYamlStream sp_start sp)
    (h_entry_old : ∀ (sp : SurfPos), SSLComments sp_scan sp →
      ∃ sp_first, SBlockSeqEntries 0 sp_first sp ∧
        ∀ (sp_end : SurfPos), SBlockSeqEntries 0 sp_first sp_end →
          SLYamlStream sp_start sp_end)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  by_cases hcol : sp_scan.col = 0
  · by_cases hc : c = '-'
    · subst hc
      obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, hcorr_sc, h_pk⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep '-' h_corr hcol h_preprocess
      have hsp_sc_eq := ScannerSurfCorr_unique hcorr_sc hcorr_prep
      subst hsp_sc_eq
      cases hws with
      | nil =>
        cases hcmt with
        | none =>
          have hpeek_disp : (if s_prep.allowDirectives then
              { s_prep with allowDirectives := false, documentEverStarted := true }
            else s_prep).peek? = some '-' := by
            have := preprocess_some_peek h_preprocess
            split
            · show s_prep.peek? = some '-'; exact this
            · exact this
          obtain ⟨sp_dash2, h_dash2, h_gnot2, hcorr_dash2⟩ :=
            dispatchBlockEntry_full_prod _ sp_mid
              (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
          have hsp_dash2_eq := ScannerSurfCorr_unique hcorr_dash2 hcorr_result
          rw [hsp_dash2_eq] at h_dash2 h_gnot2
          obtain ⟨sp_first, h_entries_old, h_cont⟩ :=
            h_entry_old sp_mid h_ssl
          exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                 BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
                 PendingNode.pendingBlock sp_start sp_block sp_scan'
                   (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                     have h_indented :=
                       SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                     h_cont sp_final (SBlockSeqEntries_snoc h_entries_old
                       (SIndent.zero sp_mid) h_dash2 h_gnot2 h_indented))
                   (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                     have h_indented :=
                       SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                     ⟨sp_first, SBlockSeqEntries_snoc h_entries_old
                       (SIndent.zero sp_mid) h_dash2 h_gnot2 h_indented, h_cont⟩),
                 hcorr_result⟩
        | some =>
          rename_i hc
          have h_eq := h_pk.resolve_right (by simp [preprocess_some_peek h_preprocess])
          exact absurd (h_eq ▸ hc) (scNbCommentText_irrefl sp_mid)
      | cons =>
        exact block_dispatch_deferred sp_start sp_mid sp_scan' s'
          (h_close_pending sp_mid h_ssl) hcorr_result
    · obtain ⟨sp_mid, _, _, h_ssl, _, _, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      exact block_dispatch_deferred sp_start sp_mid sp_scan' s'
        (h_close_pending sp_mid h_ssl) hcorr_result
  · obtain ⟨sp_mid, _, _, h_disj, _, _, _, _⟩ :=
      preprocess_some_ssl_comments_anyCol sc sp_scan s_prep c h_corr h_preprocess
    cases h_disj with
    | inl h_ssl_col =>
      exact block_dispatch_deferred sp_start sp_mid sp_scan' s'
        (h_close_pending sp_mid h_ssl_col.1) hcorr_result
    | inr h_mid_eq =>
      subst h_mid_eq
      exact block_dispatch_deferred sp_start sp_block_ctx sp_scan' s'
        h_stream_fallback hcorr_result

-- Block dispatch with pendingBlock: accumulate entries via h_close_entry_old.
lemma accum_block_on_pendingBlock
    (sc : ScannerState) (sp_start sp_block sp_block_ctx sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char) (sp_prep sp_scan' : SurfPos)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_close_pending : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid)
    (h_stream_fallback : SLYamlStream sp_start sp_block_ctx)
    (h_close_old : ∀ (sp : SurfPos), SBlockNode 0 .blockIn sp_scan sp → SLYamlStream sp_start sp)
    (h_close_entry_old : ∀ (sp : SurfPos), SBlockNode 0 .blockIn sp_scan sp →
      ∃ sp_first, SBlockSeqEntries 0 sp_first sp ∧
        ∀ (sp_end : SurfPos), SBlockSeqEntries 0 sp_first sp_end →
          SLYamlStream sp_start sp_end)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  by_cases hcol : sp_scan.col = 0
  · by_cases hc : c = '-'
    · subst hc
      obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, hcorr_sc, h_pk⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep '-' h_corr hcol h_preprocess
      have hsp_sc_eq := ScannerSurfCorr_unique hcorr_sc hcorr_prep
      subst hsp_sc_eq
      have h_node_old : SBlockNode 0 .blockIn sp_scan sp_mid :=
        SBlockNode.emptyNode 0 .blockIn sp_scan sp_mid h_ssl
      cases hws with
      | nil =>
        cases hcmt with
        | none =>
          have hpeek_disp : (if s_prep.allowDirectives then
              { s_prep with allowDirectives := false, documentEverStarted := true }
            else s_prep).peek? = some '-' := by
            have := preprocess_some_peek h_preprocess
            split
            · show s_prep.peek? = some '-'; exact this
            · exact this
          obtain ⟨sp_dash2, h_dash2, h_gnot2, hcorr_dash2⟩ :=
            dispatchBlockEntry_full_prod _ sp_mid
              (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
          have hsp_dash2_eq := ScannerSurfCorr_unique hcorr_dash2 hcorr_result
          rw [hsp_dash2_eq] at h_dash2 h_gnot2
          obtain ⟨sp_first, h_entries_old, h_cont⟩ :=
            h_close_entry_old sp_mid h_node_old
          exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                 BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
                 PendingNode.pendingBlock sp_start sp_block sp_scan'
                   (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                     have h_indented :=
                       SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                     h_cont sp_final (SBlockSeqEntries_snoc h_entries_old
                       (SIndent.zero sp_mid) h_dash2 h_gnot2 h_indented))
                   (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                     have h_indented :=
                       SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                     ⟨sp_first, SBlockSeqEntries_snoc h_entries_old
                       (SIndent.zero sp_mid) h_dash2 h_gnot2 h_indented, h_cont⟩),
                 hcorr_result⟩
        | some =>
          rename_i hc
          have h_eq := h_pk.resolve_right (by simp [preprocess_some_peek h_preprocess])
          exact absurd (h_eq ▸ hc) (scNbCommentText_irrefl sp_mid)
      | cons =>
        exact block_dispatch_deferred sp_start sp_mid sp_scan' s'
          (h_close_pending sp_mid h_ssl) hcorr_result
    · obtain ⟨sp_mid, _, _, h_ssl, _, _, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      exact block_dispatch_deferred sp_start sp_mid sp_scan' s'
        (h_close_pending sp_mid h_ssl) hcorr_result
  · obtain ⟨sp_mid, _, _, h_disj, _, _, _, _⟩ :=
      preprocess_some_ssl_comments_anyCol sc sp_scan s_prep c h_corr h_preprocess
    cases h_disj with
    | inl h_ssl_col =>
      exact block_dispatch_deferred sp_start sp_mid sp_scan' s'
        (h_close_pending sp_mid h_ssl_col.1) hcorr_result
    | inr h_mid_eq =>
      subst h_mid_eq
      exact block_dispatch_deferred sp_start sp_block_ctx sp_scan' s'
        h_stream_fallback hcorr_result

-- Helper: handles all PendingNode cases for block dispatch given stream at sp_block.
lemma accum_block_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode false sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  obtain ⟨sp_scan', hcorr_result⟩ :=
    dispatchBlockIndicators_corr _ sp_prep c (corr_of_allowDirectives_update hcorr_prep) h_dispatch
  -- Capture closing strategy before case-split (Pattern 6: parametric closing)
  have h_close_pending : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid :=
    fun sp_mid h_ssl => h_pending.close_with_ssl h_stream_block h_ssl
  cases h_pending with
  | noPending =>
    exact accum_block_on_noPending sc sp_start sp_block s_prep s' c sp_prep sp_scan'
      h_stream_block hcorr_prep hcorr_result h_corr h_preprocess h_dispatch
  | pendingDocEnd _
  | pendingDocStart _ =>
    all_goals
      exact accum_block_on_closeThenBlock sc sp_start sp_block sp_scan s_prep s' c sp_prep sp_scan'
        h_close_pending h_stream_block hcorr_prep hcorr_result h_corr h_preprocess h_dispatch
  | pendingContent _
  | pendingFlow _ =>
    all_goals
      exact accum_block_on_closeThenBlock sc sp_start sp_block sp_scan s_prep s' c sp_prep sp_scan'
        h_close_pending h_stream_block hcorr_prep hcorr_result h_corr h_preprocess h_dispatch
  | pendingBlockContent =>
    rename_i n_old h_closable h_entry_old
    by_cases hn : n_old = 0
    · subst hn
      exact accum_block_on_pendingBlockContent sc sp_start sp_block sp_block sp_scan s_prep s' c
        sp_prep sp_scan' h_stream_block h_close_pending h_stream_block h_closable h_entry_old
        hcorr_prep hcorr_result h_corr h_preprocess h_dispatch
    · exact block_dispatch_deferred sp_start sp_block sp_scan' s' h_stream_block hcorr_result
  | pendingBlock =>
    rename_i h_close_old h_close_entry_old
    exact accum_block_on_pendingBlock sc sp_start sp_block sp_block sp_scan s_prep s' c sp_prep
      sp_scan' h_stream_block h_close_pending h_stream_block h_close_old h_close_entry_old
      hcorr_prep hcorr_result h_corr h_preprocess h_dispatch

lemma accum_step_block (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStackB sp_start sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow)
    (h_pending : PendingNode false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      GStar SSWhite sp_flow sp_scan ∧ LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        GStar SSWhite sp_flow' sp_scan' ∧ LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
  -- B.4β: the flow stack is indexed by the scanner's `flowLevel`.
  rcases Nat.eq_zero_or_pos sc.flowLevel with h0 | hpos
  · -- depth 0 (no open flow collection): the existing depth-0 proof.
    rw [h0] at h_flow
    have h_lvl : s'.flowLevel = 0 := by
      rw [ScannerCorrectness.dispatchBlockIndicators_preserves_flowLevel _ c s' h_dispatch,
          allowDirectives_update_flowLevel s_prep,
          preprocess_preserves_flowLevel sc s_prep c h_preprocess, h0]
    have h_ks : s'.flowStack = #[] := by
      rw [ScannerFlowStack.dispatchBlockIndicators_preserves_flowStack _ c s' h_dispatch,
          allowDirectives_update_flowStack s_prep,
          ScannerFlowStack.preprocess_preserves_flowStack sc s_prep c h_preprocess]
      exact h_flow.kinds_nil_of_depth_zero
    rw [h_lvl, h_ks]
    obtain ⟨g', bl', fl', sn', q1, q2, q3, q4, q5⟩ :=
      accum_block_pending sc sp_start sp_flow sp_scan s_prep s' c
        (absorb_stacksB sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
        h_pending h_corr h_preprocess h_dispatch
    exact ⟨g', bl', fl', sn', q1, q2, q3.retail, q4, q5, fun h => absurd h (by omega)⟩
  · -- ═══ DEPTH ≥ 1: three arms, one free and two needing frame vocabulary. ═══
    --  * `-` is REFUTED for free: `dispatchBlockIndicators` guards it with
    --    `!s.inFlow`, and `s_ad.inFlow = true` here.
    --  * `:` (`isValueCandidate`) is the flow-map/flow-pair value transition. It
    --    needs a `receiveColon` frame transition `.value → .colon` on both
    --    `SeqFrame` and `MapFrame` (landing in `midColon`), lifted over the four
    --    `FlowOpenStack` arms exactly as `holdComma`/`receiveNode` are. The
    --    scanner side is already visible: `tl = .value` is what `midNode`/`midKey`
    --    record, and `isValueCandidate` fires only after a saved simple key.
    --  * `?` (`isKeyCandidate`) has NO frame shape yet: `midExplicitKey` already
    --    carries the key node, but `scanKey` emits only the `?`. This needs a
    --    FOURTH `FrameTail` value (`?` seen, key awaited) plus one constructor
    --    per frame — the same inline-the-shape move as 9b(ii).
    sorry

/-! ### §1e Preprocessing + Content Dispatch

    `scanNextToken_dispatchContent` handles all content tokens:
    `&` anchor, `*` alias, `!` tag, `|`/`>` block scalar, `"` double-quoted,
    `'` single-quoted, plain scalar. Never returns `none`.

    When inside an active BlockStack, the content token contributes to the
    current block entry's `SBlockIndented` component. The BlockStack itself
    doesn't change — only PendingNode transitions to pendingContent.

    **Helper**: `dispatchContent_corr` proves that all content dispatch paths
    preserve `ScannerSurfCorr`. This factors out the dispatch analysis from
    the per-case proofs below.

    **Proven case**: `BlockStack.nil` + `PendingNode.noPending`.
    No pending to close — stream unchanged, opens `pendingContent`.
    This is the primary path for the first content token in any document. -/

-- Helper: content dispatch preserves `ScannerSurfCorr` on all `.ok` paths.
-- Unfolds `scanNextToken_dispatchContent`, splits on character checks,
-- and delegates to per-scanner `_corr` theorems.
lemma dispatchContent_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- c == '&' (anchor)
  split at hok
  · split at hok   -- item 9e: the property-run guard
    · simp at hok
    generalize h_anch : scanAnchorOrAlias sc true = anch_result at hok
    cases anch_result with
    | error => simp at hok
    | ok s_anch =>
      change Except.ok _ = Except.ok s' at hok
      have h := Except.ok.inj hok; subst h
      obtain ⟨sp', hcorr'⟩ := scanAnchorOrAlias_corr sc sp hcorr true s_anch h_anch
      exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  -- c == '*' (alias)
  · split at hok
    · split at hok   -- item 9e: the property-run guard
      · simp at hok
      split at hok
      · simp at hok  -- undefinedAlias error
      · -- hok has redundant match wrapper from Except.bind; reduce it
        generalize h_alias : scanAnchorOrAlias sc false = alias_result at hok
        cases alias_result with
        | error => simp at hok
        | ok s_val =>
          try dsimp only [] at hok
          have h := Except.ok.inj hok; subst h
          exact scanAnchorOrAlias_corr sc sp hcorr false s_val h_alias
    -- c == '!' (tag)
    · split at hok
      · split at hok   -- item 9e: the property-run guard
        · simp at hok
        generalize h_tag : scanTag sc = tag_result at hok
        cases tag_result with
        | error => simp at hok
        | ok s_val =>
          try dsimp only [] at hok
          have h := Except.ok.inj hok; subst h
          exact scanTag_corr sc sp hcorr s_val h_tag
      -- c == '|' || c == '>' (block scalar)
      · split at hok
        · -- scanBlockScalar returns directly, under the item-9c `!inFlow` guard
          exact scanBlockScalar_corr sc sp hcorr (peel_blockScalarGuard hok)
        -- c == '"' (double-quoted)
        · split at hok
          · split at hok
            · simp at hok
            · rename_i s_dq hdq
              have h := Except.ok.inj hok; subst h
              obtain ⟨sp', hcorr'⟩ := scanDoubleQuoted_corr sc sp hcorr hdq
              -- simpleKey endLine update preserves corr
              split
              · exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq,
                              hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
              · exact ⟨sp', hcorr'⟩
          -- c == '\'' (single-quoted)
          · split at hok
            · split at hok
              · simp at hok
              · rename_i s_sq hsq
                have h := Except.ok.inj hok; subst h
                obtain ⟨sp', hcorr'⟩ := scanSingleQuoted_corr sc sp hcorr hsq
                split
                · exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq,
                                hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
                · exact ⟨sp', hcorr'⟩
            -- canStartPlainScalarBool (plain scalar)
            · split at hok
              · -- scanPlainScalar returns directly
                exact scanPlainScalar_corr sc sp hcorr hok
              -- error: unexpectedChar
              · simp at hok

-- Content dispatch for double-quoted: returns `SCDoubleQuoted 0 .blockIn` grammar evidence.
-- Needed for Layer 4i h_closable composition (quoted scalar → SBlockNode → stream).
-- Unfolds `scanNextToken_dispatchContent` for `c = '"'`, applies `scanDoubleQuoted_prod`,
-- and handles the simpleKey endLine update that follows.
lemma dispatchContent_doubleQuoted_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '"')
    (hok : scanNextToken_dispatchContent sc '"' = .ok s') :
    ∃ sp', SCDoubleQuoted 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- Skip false character checks: '&', '*', '!', '|'/'>'
  split at hok
  · rename_i h_eq; exact absurd h_eq (by decide)
  · split at hok
    · rename_i h_eq; exact absurd h_eq (by decide)
    · split at hok
      · rename_i h_eq; exact absurd h_eq (by decide)
      · split at hok
        · rename_i h_eq; exact absurd h_eq (by decide)
        · -- '"' == '"' = true: this branch
          split at hok
          · split at hok  -- bind on scanDoubleQuoted
            · simp at hok
            · rename_i s_dq hdq
              have h := Except.ok.inj hok; subst h
              obtain ⟨sp', h_gram, hcorr'⟩ :=
                scanDoubleQuoted_prod sc sp hcorr hpeek hdq
              exact ⟨sp', h_gram, by
                -- simpleKey endLine update preserves ScannerSurfCorr
                split
                · exact ⟨hcorr'.chars_from, hcorr'.col_eq,
                         hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩
                · exact hcorr'⟩
          · rename_i h_neq; exact absurd rfl h_neq

-- Content dispatch for single-quoted: returns `SCSingleQuoted 0 .blockIn` grammar evidence.
lemma dispatchContent_singleQuoted_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '\'')
    (hok : scanNextToken_dispatchContent sc '\'' = .ok s') :
    ∃ sp', SCSingleQuoted 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq; exact absurd h_eq (by decide)
  · split at hok
    · rename_i h_eq; exact absurd h_eq (by decide)
    · split at hok
      · rename_i h_eq; exact absurd h_eq (by decide)
      · split at hok
        · rename_i h_eq; exact absurd h_eq (by decide)
        · split at hok
          · rename_i h_eq; exact absurd h_eq (by decide)
          · -- '\'' == '\'' = true: this branch
            split at hok
            · split at hok  -- bind on scanSingleQuoted
              · simp at hok
              · rename_i s_sq hsq
                have h := Except.ok.inj hok; subst h
                obtain ⟨sp', h_gram, hcorr'⟩ :=
                  scanSingleQuoted_prod sc sp hcorr hpeek hsq
                exact ⟨sp', h_gram, by
                  split
                  · exact ⟨hcorr'.chars_from, hcorr'.col_eq,
                           hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩
                  · exact hcorr'⟩
            · rename_i h_neq; exact absurd rfl h_neq

-- Content dispatch for alias: returns `SFlowNode 0 ctx` grammar evidence in ANY
-- context.  Alias is context-free: `SCNsAliasNode` has no `n`/`c` dependency, so
-- `alias_flowNode` lifts directly to any desired context.  β.3's flow-interior
-- step instantiates `ctx := .flowIn`, the depth-0 steps `.flowOut`.
-- Since A10 Except conversion, `.ok` guarantees non-empty name unconditionally.
lemma dispatchContent_alias_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} (ctx : YamlContext)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '*')
    (hok : scanNextToken_dispatchContent sc '*' = .ok s') :
    ∃ sp', SFlowNode 0 ctx sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- Skip '&' check
  split at hok
  · rename_i h_eq; exact absurd h_eq (by decide)
  · -- '*' == '*' = true: this branch
    split at hok
    · -- Item 9e: the property-run guard (`&a *x` has no derivation)
      split at hok
      · simp at hok
      -- Inside '*' branch: handle definedAnchors check
      split at hok
      · -- !(definedAnchors.any ...) = true → .error, but we have .ok
        simp at hok
      · -- definedAnchors found → return scanAnchorOrAlias s false
        generalize h_alias : scanAnchorOrAlias sc false = alias_result at hok
        cases alias_result with
        | error => simp at hok
        | ok s_anch =>
          try dsimp only [] at hok
          simp only [Except.ok.injEq] at hok; subst hok
          obtain ⟨sp', h_alias, hcorr'⟩ :=
            scanAnchorOrAlias_aliasNode_prod sc sp hcorr hpeek s_anch h_alias
          exact ⟨sp', alias_flowNode h_alias, hcorr'⟩
    · rename_i h_neq; exact absurd rfl h_neq

-- Content dispatch for block scalar: returns `SCLLiteral 0 ∨ SCLFolded 0` grammar evidence.
lemma dispatchContent_blockScalar_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hchar : c = '|' ∨ c = '>')
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp', (SCLLiteral 0 sp sp' ∨ SCLFolded 0 sp sp') ∧ ScannerSurfCorr s' sp' := by
  cases hchar with
  | inl h_lit =>
    subst h_lit
    unfold scanNextToken_dispatchContent at hok
    simp only [bind, Except.bind, pure, Except.pure] at hok
    -- Skip '&', '*', '!' checks
    split at hok
    · rename_i h_eq; exact absurd h_eq (by decide)
    · split at hok
      · rename_i h_eq; exact absurd h_eq (by decide)
      · split at hok
        · rename_i h_eq; exact absurd h_eq (by decide)
        · -- '|' == '|' || '|' == '>' = true
          split at hok
          · -- scanBlockScalar returns directly, under the item-9c `!inFlow` guard
            exact scanBlockScalar_prod sc sp hcorr (Or.inl hpeek) (peel_blockScalarGuard hok)
          · rename_i h_neq; exact absurd rfl h_neq
  | inr h_fld =>
    subst h_fld
    unfold scanNextToken_dispatchContent at hok
    simp only [bind, Except.bind, pure, Except.pure] at hok
    split at hok
    · rename_i h_eq; exact absurd h_eq (by decide)
    · split at hok
      · rename_i h_eq; exact absurd h_eq (by decide)
      · split at hok
        · rename_i h_eq; exact absurd h_eq (by decide)
        · split at hok
          · -- scanBlockScalar returns directly, under the item-9c `!inFlow` guard
            exact scanBlockScalar_prod sc sp hcorr (Or.inr hpeek) (peel_blockScalarGuard hok)
          · rename_i h_neq; exact absurd rfl h_neq

-- If structural dispatch returns .ok none, the scanner is not at a document boundary
-- when col=0.  This follows from the definition: the none path skips all doc marker
-- checks, meaning atDocumentStart and atDocumentEnd were both false.
lemma dispatchStructural_none_not_doc_boundary
    {s : ScannerState} {c : Char}
    (h : scanNextToken_dispatchStructural s c = .ok none)
    (hcol : s.col = 0) : atDocumentBoundary s = false := by
  -- Strategy: case-split on atDocumentBoundary itself.
  -- In the true case, atDocumentStart or atDocumentEnd is true,
  -- which forces dispatchStructural to return .ok (some _) or .error,
  -- contradicting .ok none.
  cases h_ab : atDocumentBoundary s with
  | false => rfl
  | true =>
    exfalso
    unfold atDocumentBoundary at h_ab
    unfold scanNextToken_dispatchStructural at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    -- Case-split on atDocumentStart/End to resolve conditions in h
    cases h_as : atDocumentStart s <;> cases h_ae : atDocumentEnd s <;> simp_all <;>
      repeat (first | exact absurd (Except.ok.inj h) nofun | simp at h | split at h)

-- Content dispatch for plain scalar: returns `SFlowNode 0 .flowOut` grammar
-- evidence with separate grammar and scanner endpoints.
-- The grammar covers `sp → sp_gram` (plain scalar content), trailing WS
-- covers `sp_gram → sp'` (whitespace consumed by scanner but not in grammar),
-- and `ScannerSurfCorr s' sp'` tracks the scanner position.
-- Both the grammar and trailing WS are sorry'd pending `collectPlainScalarLoop_prod`.
lemma dispatchContent_plainScalar_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hnotAmpersand : c ≠ '&') (hnotStar : c ≠ '*') (hnotBang : c ≠ '!')
    (hnotPipe : c ≠ '|') (hnotGt : c ≠ '>') (hnotDQ : c ≠ '"') (hnotSQ : c ≠ '\'')
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp_gram sp', SFlowNode 0 .flowOut sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- Skip all character checks before plain scalar
  split at hok
  · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotAmpersand
  · split at hok
    · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotStar
    · split at hok
      · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotBang
      · split at hok
        · rename_i h_eq
          -- c == '|' || c == '>' = true
          have h_or := Bool.or_eq_true_iff.mp h_eq
          cases h_or with
          | inl h => exact absurd (beq_iff_eq.mp h) hnotPipe
          | inr h => exact absurd (beq_iff_eq.mp h) hnotGt
        · split at hok
          · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotDQ
          · split at hok
            · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotSQ
            · -- canStartPlainScalarBool branch: either plain scalar succeeds or error
              split at hok
              · -- canStartPlainScalarBool = true: scanPlainScalar returns directly
                exact scanPlainScalar_to_flowNode sc sp hcorr hpeek
                  (by assumption)
                  h_not_doc
                  (by assumption)
              · -- canStartPlainScalarBool = false: .error
                simp at hok

-- The `.flowIn` twin (β.3).  Same walk down `scanNextToken_dispatchContent`;
-- only the final production differs, and it is NOT a lift: `flowIn` forbids the
-- `,[]{}` that `flowOut` admits, so `SNsPlain 0 .flowOut` does not imply
-- `SNsPlain 0 .flowIn`.  `scanPlainScalar` already collects under the
-- `sc.inFlow` rules, so `scanPlainScalar_to_flowNode_flowIn` reads the same
-- scan at its native context.
lemma dispatchContent_plainScalar_flowIn_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (h_inflow : sc.inFlow = true)
    (hnotAmpersand : c ≠ '&') (hnotStar : c ≠ '*') (hnotBang : c ≠ '!')
    (hnotPipe : c ≠ '|') (hnotGt : c ≠ '>') (hnotDQ : c ≠ '"') (hnotSQ : c ≠ '\'')
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp_gram sp', SFlowNode 0 .flowIn sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotAmpersand
  · split at hok
    · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotStar
    · split at hok
      · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotBang
      · split at hok
        · rename_i h_eq
          have h_or := Bool.or_eq_true_iff.mp h_eq
          cases h_or with
          | inl h => exact absurd (beq_iff_eq.mp h) hnotPipe
          | inr h => exact absurd (beq_iff_eq.mp h) hnotGt
        · split at hok
          · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotDQ
          · split at hok
            · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hnotSQ
            · split at hok
              · exact scanPlainScalar_to_flowNode_flowIn sc sp hcorr hpeek
                  (by assumption) h_inflow h_not_doc (by assumption)
              · simp at hok

-- Content dispatch for anchor: returns `SFlowNode 0 ctx` grammar evidence in ANY
-- context.  Anchor `&name` produces `SCNsAnchorProperty` → `SCNsProperties.anchorFirst`
-- → `SFlowNode.propsEmpty`; the property itself carries no context, and the
-- trailing separator is `GOpt.none`, so every context is equally derivable.
-- Since A10 Except conversion, `.ok` guarantees non-empty name unconditionally.
lemma dispatchContent_anchor_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} (ctx : YamlContext)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '&')
    (hok : scanNextToken_dispatchContent sc '&' = .ok s') :
    ∃ sp', SFlowNode 0 ctx sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- '&' == '&' = true: anchor branch
  split at hok
  · -- Item 9e: the property-run guard (`&a &b` has no derivation)
    split at hok
    · simp at hok
    generalize h_anch : scanAnchorOrAlias sc true = anch_result at hok
    cases anch_result with
    | error => simp at hok
    | ok s_anch =>
      change Except.ok _ = Except.ok s' at hok
      have h := Except.ok.inj hok; subst h
      obtain ⟨sp', h_anchor, hcorr'⟩ :=
        scanAnchorOrAlias_anchorProp_prod sc sp hcorr hpeek s_anch h_anch
      exact ⟨sp', SFlowNode.propsEmpty 0 ctx sp sp'
        (SCNsProperties.anchorFirst 0 ctx sp sp' sp' h_anchor (GOpt.none _)),
        ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  · rename_i h_neq; exact absurd rfl h_neq

-- Content dispatch for tag: returns `SFlowNode 0 ctx` grammar evidence in ANY
-- context (same context-freedom as the anchor case).
-- Tag `!` produces `SCNsTagProperty` → `SCNsProperties.tagFirst` → `SFlowNode.propsEmpty`.
-- Secondary tag `!!suffix` is fully proven. Verbatim and named tags are sorry'd.
lemma dispatchContent_tag_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} (ctx : YamlContext)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '!')
    (hok : scanNextToken_dispatchContent sc '!' = .ok s') :
    ∃ sp', SFlowNode 0 ctx sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- Skip '&' check
  split at hok
  · rename_i h_eq; exact absurd h_eq (by decide)
  · -- Skip '*' check
    split at hok
    · rename_i h_eq; exact absurd h_eq (by decide)
    · -- '!' == '!' = true: tag branch
      split at hok
      · -- Item 9e: the property-run guard (`!t !u` has no derivation)
        split at hok
        · simp at hok
        generalize h_tag : scanTag sc = tag_result at hok
        cases tag_result with
        | error => simp at hok
        | ok s_tag =>
          simp only [Except.ok.injEq] at hok; subst hok
          by_cases hpeek2 : sc.advance.peek? = some '!'
          · -- Secondary tag `!!suffix`: fully proven
            obtain ⟨sp', h_tag_prop, hcorr'⟩ := scanTag_secondary_prod sc sp hcorr hpeek hpeek2 s_tag h_tag
            exact ⟨sp', SFlowNode.propsEmpty 0 ctx sp sp'
              (SCNsProperties.tagFirst 0 ctx sp sp' sp' h_tag_prop (GOpt.none _)),
              ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
          · -- Verbatim `!<uri>` or named `!handle!suffix` or non-specific `!`:
            obtain ⟨sp', h_tag_prop, hcorr'⟩ := scanTag_nonSecondary_prod sc sp hcorr hpeek hpeek2 s_tag h_tag
            exact ⟨sp', SFlowNode.propsEmpty 0 ctx sp sp'
              (SCNsProperties.tagFirst 0 ctx sp sp' sp' h_tag_prop (GOpt.none _)),
              ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
      · rename_i h_neq; exact absurd rfl h_neq

-- Unified content evidence extraction (Wadler-style "theorems for free").
-- All content dispatch paths either produce `SFlowNode 0 .flowOut` (flow content:
-- double-quoted, single-quoted, alias, plain) or `SCLLiteral 0 ∨ SCLFolded 0`
-- (block scalar). Returns separate grammar and scanner endpoints with trailing
-- WS evidence bridging them. For non-plain-scalar paths, the WS is trivial
-- (`GStar.nil`); for plain scalars, it covers the trailing whitespace gap.
-- Proven ONCE, used by all PendingNode constructors.
lemma dispatchContent_evidence (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp_gram sp',
      (SFlowNode 0 .flowOut sp sp_gram ∨ (SCLLiteral 0 sp sp_gram ∨ SCLFolded 0 sp sp_gram)) ∧
      GStar SSWhite sp_gram sp' ∧
      ScannerSurfCorr s' sp' := by
  by_cases hc_dq : c = '"'
  · subst hc_dq
    obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_doubleQuoted_prod sc sp hcorr hpeek hok
    exact ⟨sp', sp', Or.inl (SFlowNode_doubleQ_ctx_lift h_gram (by decide) (by decide)),
           GStar.nil _, hcorr'⟩
  · by_cases hc_sq : c = '\''
    · subst hc_sq
      obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_singleQuoted_prod sc sp hcorr hpeek hok
      exact ⟨sp', sp', Or.inl (SFlowNode_singleQ_ctx_lift h_gram (by decide) (by decide)),
             GStar.nil _, hcorr'⟩
    · by_cases hc_alias : c = '*'
      · subst hc_alias
        obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_alias_prod sc sp .flowOut hcorr hpeek hok
        exact ⟨sp', sp', Or.inl h_gram, GStar.nil _, hcorr'⟩
      · by_cases hc_bs : c = '|' ∨ c = '>'
        · obtain ⟨sp', h_gram, hcorr'⟩ :=
            dispatchContent_blockScalar_prod sc sp hcorr hpeek hc_bs hok
          exact ⟨sp', sp', Or.inr h_gram, GStar.nil _, hcorr'⟩
        · -- Remaining cases: '&' (anchor), '!' (tag), plain scalar, error
          have hnotPipe : c ≠ '|' := fun h => hc_bs (Or.inl h)
          have hnotGt : c ≠ '>' := fun h => hc_bs (Or.inr h)
          by_cases hc_amp : c = '&'
          · -- Anchor: SCNsAnchorProperty → SCNsProperties.anchorFirst → SFlowNode.propsEmpty
            subst hc_amp
            obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_anchor_prod sc sp .flowOut hcorr hpeek hok
            exact ⟨sp', sp', Or.inl h_gram, GStar.nil _, hcorr'⟩
          · by_cases hc_bang : c = '!'
            · -- Tag: SCNsTagProperty → SCNsProperties.tagFirst → SFlowNode.propsEmpty
              subst hc_bang
              obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_tag_prod sc sp .flowOut hcorr hpeek hok
              exact ⟨sp', sp', Or.inl h_gram, GStar.nil _, hcorr'⟩
            · -- Plain scalar (or error — but .ok means it succeeded)
              obtain ⟨sp_gram, sp', h_gram, h_ws, hcorr'⟩ :=
                dispatchContent_plainScalar_prod sc sp hcorr hpeek
                  hc_amp hc_alias hc_bang hnotPipe hnotGt hc_dq hc_sq h_not_doc hok
              exact ⟨sp_gram, sp', Or.inl h_gram, h_ws, hcorr'⟩

/-- **β.3's flow-interior content evidence.**  The `.flowIn` sibling of
    `dispatchContent_evidence`, for a content dispatch that ran with
    `sc.inFlow = true` — the shape `ns-flow-seq-entry` [139] / `ns-flow-map-entry`
    [142] consume, since [137]/[140] wrap their entries in `in-flow(c)`.

    Two differences from the `.flowOut` original, both forced:

    * **No block-scalar disjunct.**  `c-l+literal` [170] and `c-l+folded` [174]
      are reachable only through `s-l+block-node` [196]; `ns-flow-content` [158]
      has no literal/folded arm.  Item 9c made that a scanner rejection, so
      `dispatchContent_not_blockScalar_of_inFlow` refutes the header characters
      outright rather than leaving a disjunct the caller cannot discharge.
    * **The plain-scalar arm is a native production, not a lift.**  `flowIn`
      forbids the `,[]{}` that `flowOut` admits, so containment runs the wrong
      way and a `.flowOut` plain scalar does NOT lift.  `scanPlainScalar` already
      collects with the `s.inFlow` rules, so the `.flowIn` core
      (`scanPlainScalar_to_flowNode_flowIn`) is the same walk read at its native
      context.  The quoted, alias, anchor and tag arms are context-free or lift
      freely between non-key contexts. -/
lemma dispatchContent_evidence_flowIn (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (h_inflow : sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp_gram sp',
      SFlowNode 0 .flowIn sp sp_gram ∧
      GStar SSWhite sp_gram sp' ∧
      ScannerSurfCorr s' sp' := by
  -- Item 9c: inside a flow the block-scalar arm cannot have fired.
  obtain ⟨hnotPipe, hnotGt⟩ :=
    Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow h_inflow hok
  by_cases hc_dq : c = '"'
  · subst hc_dq
    obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_doubleQuoted_prod sc sp hcorr hpeek hok
    exact ⟨sp', sp', SFlowNode_doubleQ_ctx_lift h_gram (by decide) (by decide),
           GStar.nil _, hcorr'⟩
  · by_cases hc_sq : c = '\''
    · subst hc_sq
      obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_singleQuoted_prod sc sp hcorr hpeek hok
      exact ⟨sp', sp', SFlowNode_singleQ_ctx_lift h_gram (by decide) (by decide),
             GStar.nil _, hcorr'⟩
    · by_cases hc_alias : c = '*'
      · subst hc_alias
        obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_alias_prod sc sp .flowIn hcorr hpeek hok
        exact ⟨sp', sp', h_gram, GStar.nil _, hcorr'⟩
      · by_cases hc_amp : c = '&'
        · subst hc_amp
          obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_anchor_prod sc sp .flowIn hcorr hpeek hok
          exact ⟨sp', sp', h_gram, GStar.nil _, hcorr'⟩
        · by_cases hc_bang : c = '!'
          · subst hc_bang
            obtain ⟨sp', h_gram, hcorr'⟩ := dispatchContent_tag_prod sc sp .flowIn hcorr hpeek hok
            exact ⟨sp', sp', h_gram, GStar.nil _, hcorr'⟩
          · exact dispatchContent_plainScalar_flowIn_prod sc sp hcorr hpeek h_inflow
              hc_amp hc_alias hc_bang hnotPipe hnotGt hc_dq hc_sq h_not_doc hok

/-! #### Extracted content-dispatch per-constructor theorems

    Each theorem handles one substantial `PendingNode` constructor case for
    `accum_content_pending`. The main theorem delegates to these after the
    shared preamble. Trivial-close constructors and `pendingDirective`
    remain inline. -/

-- Content dispatch with stream at sp_block and separator already constructed.
-- Shared by accum_content_on_noPending (SSeparateLines.commented) and
-- accum_content_pending's transition-close arms (SSeparateLines.inline).
lemma content_dispatch_after_close
    (sp_start sp_block : SurfPos)
    (s_prep s' : ScannerState) (c : Char) (sp_prep sp_scan' : SurfPos)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_sep : SSeparateLines 0 sp_block sp_prep)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false)
    (hpeek : s_prep.peek? = some c)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  have hpeek_disp : (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).peek? = some c := by
    split
    · show s_prep.peek? = some c; exact hpeek
    · exact hpeek
  obtain ⟨sp_gram, sp_ev, h_ev, h_trailing_ws, hcorr_ev⟩ :=
      dispatchContent_evidence _ sp_prep c
      (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_not_doc h_dispatch
  have hsp_ev_eq := ScannerSurfCorr_unique hcorr_ev hcorr_result
  rw [hsp_ev_eq] at h_trailing_ws hcorr_ev
  cases h_ev with
  | inl h_flow =>
    exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
           BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
           PendingNode.pendingContent sp_start sp_block sp_scan'
             (fun sp_mid h_ssl =>
               have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
               have h_blockNode :=
                 flowInBlock_blockNode h_sep h_flow h_ssl_ext
               have h_bare := SLBareDocument.mk sp_block sp_mid h_blockNode
               SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
                 h_stream_block (GStar.nil _)
                 (GOpt.some sp_block sp_mid
                   (SLAnyDocument.bare sp_block sp_mid h_bare))
                 (GStar.nil _)),
           hcorr_result⟩
  | inr h_block =>
    exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
           BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
           PendingNode.pendingContent sp_start sp_block sp_scan'
             (fun sp_mid h_ssl =>
               have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
               have h_blockNode : SBlockNode 0 .blockIn sp_block sp_gram :=
                 h_block.elim
                   (fun h_lit => literal_blockNode h_sep (GOpt.none sp_prep) h_lit)
                   (fun h_fld => folded_blockNode h_sep (GOpt.none sp_prep) h_fld)
               have h_bare := SLBareDocument.mk sp_block sp_gram h_blockNode
               have h_stream' := SLYamlStream.implicitContinue
                 sp_start sp_block sp_block sp_gram sp_gram
                 h_stream_block (GStar.nil _)
                 (GOpt.some sp_block sp_gram
                   (SLAnyDocument.bare sp_block sp_gram h_bare))
                 (GStar.nil _)
               ssl_comments_extend_stream sp_start sp_gram sp_mid h_stream' h_ssl_ext),
           hcorr_result⟩

-- Content dispatch with noPending: build separate lines + grammar evidence.
lemma accum_content_on_noPending
    (sc : ScannerState) (sp_start sp_block : SurfPos)
    (s_prep s' : ScannerState) (c : Char) (sp_prep sp_scan' : SurfPos)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (h_corr : ScannerSurfCorr sc sp_block)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  by_cases hcol : sp_block.col = 0
  · obtain ⟨sp_sep, h_sep, hcorr_sep⟩ :=
      preprocess_some_separate_lines_0 sc sp_block s_prep c h_corr hcol h_preprocess
    have hsp_eq := ScannerSurfCorr_unique hcorr_prep hcorr_sep; subst hsp_eq
    have hpeek : s_prep.peek? = some c := preprocess_some_peek h_preprocess
    have hpeek_disp : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).peek? = some c := by
      split
      · show s_prep.peek? = some c; exact hpeek
      · exact hpeek
    obtain ⟨sp_gram, sp_ev, h_ev, h_trailing_ws, hcorr_ev⟩ :=
        dispatchContent_evidence _ sp_prep c
        (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_not_doc h_dispatch
    have hsp_ev_eq := ScannerSurfCorr_unique hcorr_ev hcorr_result
    rw [hsp_ev_eq] at h_trailing_ws hcorr_ev
    cases h_ev with
    | inl h_flow =>
      exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
             BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
             PendingNode.pendingContent sp_start sp_block sp_scan'
               (fun sp_mid h_ssl =>
                 have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
                 have h_blockNode :=
                   flowInBlock_blockNode h_sep h_flow h_ssl_ext
                 have h_bare := SLBareDocument.mk sp_block sp_mid h_blockNode
                 SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
                   h_stream_block (GStar.nil _)
                   (GOpt.some sp_block sp_mid
                     (SLAnyDocument.bare sp_block sp_mid h_bare))
                   (GStar.nil _)),
             hcorr_result⟩
    | inr h_block =>
      exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
             BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
             PendingNode.pendingContent sp_start sp_block sp_scan'
               (fun sp_mid h_ssl =>
                 have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
                 have h_blockNode : SBlockNode 0 .blockIn sp_block sp_gram :=
                   h_block.elim
                     (fun h_lit => literal_blockNode h_sep (GOpt.none sp_prep) h_lit)
                     (fun h_fld => folded_blockNode h_sep (GOpt.none sp_prep) h_fld)
                 have h_bare := SLBareDocument.mk sp_block sp_gram h_blockNode
                 have h_stream' := SLYamlStream.implicitContinue
                   sp_start sp_block sp_block sp_gram sp_gram
                   h_stream_block (GStar.nil _)
                   (GOpt.some sp_block sp_gram
                     (SLAnyDocument.bare sp_block sp_gram h_bare))
                   (GStar.nil _)
                 ssl_comments_extend_stream sp_start sp_gram sp_mid h_stream' h_ssl_ext),
             hcorr_result⟩
  · -- col≠0: use preprocess_some_separate_0_anyCol (no column requirement).
    obtain ⟨sp_sep, h_sep, hcorr_sep⟩ :=
      preprocess_some_separate_0_anyCol sc sp_block s_prep c h_corr h_preprocess
    have hsp_eq := ScannerSurfCorr_unique hcorr_prep hcorr_sep; subst hsp_eq
    have hpeek : s_prep.peek? = some c := preprocess_some_peek h_preprocess
    have hpeek_disp : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).peek? = some c := by
      split
      · show s_prep.peek? = some c; exact hpeek
      · exact hpeek
    obtain ⟨sp_gram, sp_ev, h_ev, h_trailing_ws, hcorr_ev⟩ :=
        dispatchContent_evidence _ sp_prep c
        (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_not_doc h_dispatch
    have hsp_ev_eq := ScannerSurfCorr_unique hcorr_ev hcorr_result
    rw [hsp_ev_eq] at h_trailing_ws hcorr_ev
    cases h_ev with
    | inl h_flow =>
      exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
             BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
             PendingNode.pendingContent sp_start sp_block sp_scan'
               (fun sp_mid h_ssl =>
                 have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
                 have h_blockNode :=
                   flowInBlock_blockNode h_sep h_flow h_ssl_ext
                 have h_bare := SLBareDocument.mk sp_block sp_mid h_blockNode
                 SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
                   h_stream_block (GStar.nil _)
                   (GOpt.some sp_block sp_mid
                     (SLAnyDocument.bare sp_block sp_mid h_bare))
                   (GStar.nil _)),
             hcorr_result⟩
    | inr h_block =>
      exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
             BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
             PendingNode.pendingContent sp_start sp_block sp_scan'
               (fun sp_mid h_ssl =>
                 have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
                 have h_blockNode : SBlockNode 0 .blockIn sp_block sp_gram :=
                   h_block.elim
                     (fun h_lit => literal_blockNode h_sep (GOpt.none sp_prep) h_lit)
                     (fun h_fld => folded_blockNode h_sep (GOpt.none sp_prep) h_fld)
                 have h_bare := SLBareDocument.mk sp_block sp_gram h_blockNode
                 have h_stream' := SLYamlStream.implicitContinue
                   sp_start sp_block sp_block sp_gram sp_gram
                   h_stream_block (GStar.nil _)
                   (GOpt.some sp_block sp_gram
                     (SLAnyDocument.bare sp_block sp_gram h_bare))
                   (GStar.nil _)
                 ssl_comments_extend_stream sp_start sp_gram sp_mid h_stream' h_ssl_ext),
             hcorr_result⟩

-- Content dispatch with pendingBlock: compose content inside block entry.
lemma accum_content_on_pendingBlock
    (sc : ScannerState) (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char) (sp_prep sp_scan' : SurfPos)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_close_old : ∀ (sp : SurfPos), SBlockNode 0 .blockIn sp_scan sp → SLYamlStream sp_start sp)
    (h_close_entry_old : ∀ (sp : SurfPos), SBlockNode 0 .blockIn sp_scan sp →
      ∃ sp_first, SBlockSeqEntries 0 sp_first sp ∧
        ∀ (sp_end : SurfPos), SBlockSeqEntries 0 sp_first sp_end →
          SLYamlStream sp_start sp_end)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep', h_sep, hcorr_sep⟩ :=
    preprocess_some_separate_0_anyCol sc sp_scan s_prep c h_corr h_preprocess
  have hsp_eq := ScannerSurfCorr_unique hcorr_prep hcorr_sep; subst hsp_eq
  have hpeek : s_prep.peek? = some c := preprocess_some_peek h_preprocess
  have hpeek_disp : (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).peek? = some c := by
    split
    · show s_prep.peek? = some c; exact hpeek
    · exact hpeek
  obtain ⟨sp_gram, sp_ev, h_ev, h_trailing_ws, hcorr_ev⟩ :=
      dispatchContent_evidence _ sp_prep c
      (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_not_doc h_dispatch
  have hsp_ev_eq := ScannerSurfCorr_unique hcorr_ev hcorr_result
  rw [hsp_ev_eq] at h_trailing_ws hcorr_ev
  cases h_ev with
  | inl h_flow =>
    exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
           BlockStack.nil sp_block, FlowStackB.nil sp_block .sep,
           PendingNode.pendingBlockContent sp_start sp_block sp_scan' 0
             (fun sp_final h_ssl =>
               have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
               h_close_old sp_final
                 (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_gram sp_final
                   h_sep h_flow h_ssl_ext))
             (fun sp_final h_ssl =>
               have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
               h_close_entry_old sp_final
                 (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_gram sp_final
                   h_sep h_flow h_ssl_ext)),
           hcorr_result⟩
  | inr h_block =>
    have h_blockNode : SBlockNode 0 .blockIn sp_scan sp_gram :=
      h_block.elim
        (fun h_lit => literal_blockNode h_sep (GOpt.none sp_prep) h_lit)
        (fun h_fld => folded_blockNode h_sep (GOpt.none sp_prep) h_fld)
    have h_stream' : SLYamlStream sp_start sp_gram :=
      h_close_old sp_gram h_blockNode
    exact ⟨sp_gram, sp_gram, sp_gram, sp_scan', h_stream',
           BlockStack.nil sp_gram, FlowStackB.nil sp_gram .sep,
           PendingNode.pendingContent sp_start sp_gram sp_scan'
             (fun sp_final h_ssl =>
               have h_ssl_ext := white_prepend_SSLComments h_trailing_ws h_ssl
               ssl_comments_extend_stream sp_start sp_gram sp_final h_stream' h_ssl_ext),
           hcorr_result⟩

-- Helper: handles all PendingNode cases for content dispatch given stream at sp_block.
lemma accum_content_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode false sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 #[] .sep sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  obtain ⟨sp_scan', hcorr_result⟩ :=
    dispatchContent_corr _ sp_prep c (corr_of_allowDirectives_update hcorr_prep) h_dispatch
  -- Capture closing strategy before case-split (Pattern 6: parametric closing).
  -- Each transition case can close old pending to stream in one call.
  have h_close_pending : ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid :=
    fun sp_mid h_ssl => h_pending.close_with_ssl h_stream_block h_ssl
  cases h_pending with
  | noPending =>
    exact accum_content_on_noPending sc sp_start sp_block s_prep s' c sp_prep sp_scan'
      h_stream_block hcorr_prep hcorr_result h_corr h_preprocess h_not_doc h_dispatch
  | pendingDocEnd _
  | pendingDocStart _
  | pendingContent _
  | pendingFlow _
  | pendingBlockContent _ _ _ =>
    all_goals (
      by_cases hcol : sp_scan.col = 0
      · obtain ⟨sp_mid, sp_ws, sp_prep2, h_ssl, hcol_mid, h_ws, h_cmt, hcorr_prep2, h_pk⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        have hsp_eq2 := ScannerSurfCorr_unique hcorr_prep hcorr_prep2; subst hsp_eq2
        have h_eq : sp_prep = sp_ws := by
          cases h_pk with
          | inl h => exact h
          | inr h => rw [preprocess_some_peek h_preprocess] at h; cases h
        subst h_eq
        have h_stream_mid := h_close_pending sp_mid h_ssl
        have h_sep := SSeparateLines.inline 0 sp_mid sp_prep
          (GStar_SSWhite_to_SSeparateInLine sp_mid sp_prep h_ws)
        exact content_dispatch_after_close sp_start sp_mid s_prep s' c sp_prep sp_scan'
          h_stream_mid h_sep hcorr_prep hcorr_result h_not_doc
          (preprocess_some_peek h_preprocess) h_dispatch
      · -- col≠0: use anyCol, close pending if SSLComments available.
        obtain ⟨sp_mid, sp_ws, sp_prep2, h_disj, h_ws, h_cmt, hcorr_prep2, h_pk⟩ :=
          preprocess_some_ssl_comments_anyCol sc sp_scan s_prep c h_corr h_preprocess
        have hsp_eq2 := ScannerSurfCorr_unique hcorr_prep hcorr_prep2; subst hsp_eq2
        cases h_disj with
        | inl h_ssl_col =>
          obtain ⟨h_ssl, hcol_mid⟩ := h_ssl_col
          have h_eq : sp_prep = sp_ws := by
            cases h_pk with
            | inl h => exact h
            | inr h => rw [preprocess_some_peek h_preprocess] at h; cases h
          subst h_eq
          have h_stream_mid := h_close_pending sp_mid h_ssl
          have h_sep := SSeparateLines.inline 0 sp_mid sp_prep
            (GStar_SSWhite_to_SSeparateInLine sp_mid sp_prep h_ws)
          exact content_dispatch_after_close sp_start sp_mid s_prep s' c sp_prep sp_scan'
            h_stream_mid h_sep hcorr_prep hcorr_result h_not_doc
            (preprocess_some_peek h_preprocess) h_dispatch
        | inr h_mid_eq =>
          exact block_dispatch_deferred sp_start sp_block sp_scan' s' h_stream_block hcorr_result)
  | pendingBlock =>
    rename_i h_close_old h_close_entry_old
    exact accum_content_on_pendingBlock sc sp_start sp_block sp_scan s_prep s' c sp_prep sp_scan'
      h_stream_block h_close_old h_close_entry_old
      hcorr_prep hcorr_result h_corr h_preprocess h_not_doc h_dispatch

lemma accum_step_content (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStackB sp_start sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow)
    (h_pending : PendingNode false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      GStar SSWhite sp_flow sp_scan ∧ LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s')
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' ∧
      PendingNode false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        GStar SSWhite sp_flow' sp_scan' ∧ LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
  -- B.4β: the flow stack is indexed by the scanner's `flowLevel`.
  rcases Nat.eq_zero_or_pos sc.flowLevel with h0 | hpos
  · -- depth 0 (no open flow collection): the existing depth-0 proof.
    rw [h0] at h_flow
    have h_lvl : s'.flowLevel = 0 := by
      rw [ScannerCorrectness.dispatchContent_preserves_flowLevel _ c s' h_dispatch,
          allowDirectives_update_flowLevel s_prep,
          preprocess_preserves_flowLevel sc s_prep c h_preprocess, h0]
    have h_ks : s'.flowStack = #[] := by
      rw [ScannerFlowStack.dispatchContent_preserves_flowStack _ c s' h_dispatch,
          allowDirectives_update_flowStack s_prep,
          ScannerFlowStack.preprocess_preserves_flowStack sc s_prep c h_preprocess]
      exact h_flow.kinds_nil_of_depth_zero
    rw [h_lvl, h_ks]
    obtain ⟨g', bl', fl', sn', q1, q2, q3, q4, q5⟩ :=
      accum_content_pending sc sp_start sp_flow sp_scan s_prep s' c
        (absorb_stacksB sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
        h_pending h_corr h_preprocess h_not_doc h_dispatch
    exact ⟨g', bl', fl', sn', q1, q2, q3.retail, q4, q5, fun h => absurd h (by omega)⟩
  · -- ═══ DEPTH ≥ 1: BLOCKED on a scanner-strictness gap, not on proof work. ═══
    -- The route is `FlowOpenStack.receiveNode` (sorry-free, and its `tl ≠ .value`
    -- premise is already discharged by `checkFlowAdjacency`), fed by a `.flowIn`
    -- twin of `dispatchContent_evidence`. Two obstructions, in order:
    --
    --  1. `dispatchContent_evidence` produces `SFlowNode 0 .flowOut`, and the
    --     containment runs the WRONG way for plain scalars: `flowIn` forbids the
    --     `,[]{}` that `flowOut` admits, so a `flowOut` production does not lift.
    --     The scanner already collects with `s.inFlow` rules, so the twin is a
    --     re-aim of the same walk, not new analysis.
    --
    --  2. **The blocker.** That evidence also offers `SCLLiteral ∨ SCLFolded`,
    --     and inside a flow there is nothing to refute it with: the scanner
    --     ACCEPTS `[a, |\n  x\n]` and `{k: |\n  x\n}` (probed 2026-08-06, both
    --     scan clean at 15 tokens), while `SFlowContent` has no literal/folded
    --     constructor — flow content is plain / flowSeq / flowMap / singleQ /
    --     doubleQ only. Block scalars are block-context productions ([170]/[174],
    --     reachable only from `s-l+block-node`), so this input is invalid YAML
    --     that the scanner lets through. This arm is therefore UNPROVABLE as the
    --     scanner stands; it is an item-9a-class strictening (reject `|`/`>` when
    --     `s.inFlow` in `scanNextToken_dispatchContent`), and needs the same
    --     probe-matrix validation 9a had before the proof can consume it.
    sorry

/-! ### §1f Composition: Per-Dispatch → Full accum_step

    Unfold `scanNextToken`, split on preprocessing and dispatch results,
    and delegate to the per-dispatch sorry lemmas above. -/

lemma scanNextToken_accum_step (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s' : ScannerState) {b : Bool}
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStackB sp_start sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow)
    (h_pending : PendingNode b sp_start sp_flow sp_scan)
    (h_dir_flag : b = true → sc.directivesPresent = true)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      GStar SSWhite sp_flow sp_scan ∧ LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_ok : scanNextToken sc = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan' b',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' ∧
      PendingNode b' sp_start sp_flow' sp_scan' ∧
      (b' = true → s'.directivesPresent = true) ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        GStar SSWhite sp_flow' sp_scan' ∧ LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · exact absurd (Except.ok.inj h_ok) nofun
    · rename_i s_pre c_pre h_pre
      -- Capture structural dispatch result for h_not_doc derivation in content branch
      generalize h_str_eq : scanNextToken_dispatchStructural s_pre c_pre = str_res at h_ok
      split at h_ok
      · simp at h_ok
      · split at h_ok
        · rename_i s_str
          have h := Except.ok.inj h_ok; injection h with h; subst h
          exact accum_step_structural sc sp_start sp_gram sp_block sp_flow sp_scan s_pre s_str c_pre
            h_stream h_stack h_flow h_pending h_dir_flag h_corr h_interior h_pre h_str_eq
        · -- Pending-directives check (Fix B) — pure check, no state change
          split at h_ok
          · simp at h_ok
          · -- the check passed ⇒ no pending directives ⇒ b = false
            rename_i u_chk h_chk
            have h_ndp : s_pre.directivesPresent = false := by
              cases hdp : s_pre.directivesPresent
              · rfl
              · exfalso
                unfold scanNextToken_checkNoPendingDirectives at h_chk
                rw [hdp] at h_chk
                simp at h_chk
            have hb : b = false := by
              cases b
              · rfl
              · exact absurd (h_dir_flag rfl)
                  (by rw [← preprocess_some_directivesPresent h_pre, h_ndp]; simp)
            subst hb
            -- Past structural dispatch: allowDirectives update
            split at h_ok
            · simp at h_ok
            · -- scanNextToken_checkBlockFlowIndent — pure check, no state change
              split at h_ok
              · simp at h_ok
              · split at h_ok
                · rename_i s_flow_out h_flow_disp
                  have h := Except.ok.inj h_ok; injection h with h; subst h
                  obtain ⟨g', bl', fl', sn', q1, q2, q3, q4, q5, q6⟩ :=
                    accum_step_flow sc sp_start sp_gram sp_block sp_flow sp_scan s_pre s_flow_out c_pre
                      h_stream h_stack h_flow h_pending h_corr h_interior h_pre h_flow_disp
                  exact ⟨g', bl', fl', sn', false, q1, q2, q3, q4, fun h => Bool.noConfusion h, q5, q6⟩
                · split at h_ok
                  · simp at h_ok
                  · split at h_ok
                    · rename_i s_blk h_blk
                      have h := Except.ok.inj h_ok; injection h with h; subst h
                      obtain ⟨g', bl', fl', sn', q1, q2, q3, q4, q5, q6⟩ :=
                        accum_step_block sc sp_start sp_gram sp_block sp_flow sp_scan s_pre s_blk c_pre
                          h_stream h_stack h_flow h_pending h_corr h_interior h_pre h_blk
                      exact ⟨g', bl', fl', sn', false, q1, q2, q3, q4, fun h => Bool.noConfusion h, q5, q6⟩
                    · split at h_ok
                      · simp at h_ok
                      · rename_i s_cnt h_cnt
                        have h := Except.ok.inj h_ok; injection h with h; subst h
                        -- Derive h_not_doc: structural dispatch returned none on s_pre,
                        -- so s_pre is not at a document boundary when col=0.
                        -- The allowDirectives update preserves col and boundary checks.
                        have h_not_doc : (if s_pre.allowDirectives then
                              { s_pre with allowDirectives := false, documentEverStarted := true }
                            else s_pre).col = 0 →
                          atDocumentBoundary (if s_pre.allowDirectives then
                              { s_pre with allowDirectives := false, documentEverStarted := true }
                            else s_pre) = false := by
                          split
                          · intro hcol
                            have : atDocumentBoundary
                              { s_pre with allowDirectives := false, documentEverStarted := true }
                              = atDocumentBoundary s_pre := by
                              unfold atDocumentBoundary atDocumentStart atDocumentEnd
                                ScannerState.peekAt?; rfl
                            rw [this]
                            exact dispatchStructural_none_not_doc_boundary h_str_eq hcol
                          · exact dispatchStructural_none_not_doc_boundary h_str_eq
                        obtain ⟨g', bl', fl', sn', q1, q2, q3, q4, q5, q6⟩ :=
                          accum_step_content sc sp_start sp_gram sp_block sp_flow sp_scan s_pre s_cnt c_pre
                            h_stream h_stack h_flow h_pending h_corr h_interior h_pre h_cnt h_not_doc
                        exact ⟨g', bl', fl', sn', false, q1, q2, q3, q4, fun h => Bool.noConfusion h, q5, q6⟩

/-! ## §2 EOF Step: scanNextToken returns none

    When `scanNextToken` returns `.ok none`, the only code path is through
    `scanNextToken_preprocess` returning `none` (EOF detected).
    All BlockStack levels are unwound and PendingNode closed. -/

lemma scanNextToken_none_stream (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStackB sp_start sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow)
    (h_pending : PendingNode false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_fl0 : sc.flowLevel = 0)
    (h_ok : scanNextToken sc = .ok none) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  -- An open flow at EOF is not this lemma's case: `scanLoop` rejects it with
  -- `unterminatedFlowCollection` BEFORE reaching here, so the caller supplies
  -- `h_fl0`. (`scanNextToken sc = .ok none` on its own does NOT rule the case
  -- out — `[a, b` reaches EOF happily; it is the loop's post-check that fails.)
  rw [h_fl0] at h_flow
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · rename_i h_pre
      exact preprocessing_eof_extends_stream sc sp_start sp_gram sp_block sp_flow sp_scan
        h_stream h_stack h_flow h_pending h_corr h_pre
    · split at h_ok
      · simp at h_ok
      · split at h_ok
        · exact absurd (Except.ok.inj h_ok) nofun
        · -- pending-directives check (Fix B)
          split at h_ok
          · simp at h_ok
          · split at h_ok
            · simp at h_ok
            · split at h_ok
              · simp at h_ok
              · split at h_ok
                · exact absurd (Except.ok.inj h_ok) nofun
                · split at h_ok
                  · simp at h_ok
                  · split at h_ok
                    · exact absurd (Except.ok.inj h_ok) nofun
                    · split at h_ok
                      · simp at h_ok
                      · exact absurd (Except.ok.inj h_ok) nofun

/-! ## §3 scanLoop with Grammar Accumulation

    Fuel induction threading the lagging quad:
    `SLYamlStream`, `BlockStack`, `PendingNode`, and `ScannerSurfCorr`. -/

lemma scanLoop_grammar_prod (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (fuel : Nat) (tokens : Array (Positioned YamlToken)) {b : Bool}
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStackB sp_start sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow)
    (h_pending : PendingNode b sp_start sp_flow sp_scan)
    (h_dir_flag : b = true → sc.directivesPresent = true)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      GStar SSWhite sp_flow sp_scan ∧ LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_ok : scanLoop sc fuel = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  induction fuel generalizing sc sp_gram sp_block sp_flow sp_scan tokens b with
  | zero => simp [scanLoop] at h_ok
  | succ fuel' ih =>
    simp only [scanLoop] at h_ok
    split at h_ok
    · -- scanNextToken = .error → contradicts .ok
      simp at h_ok
    · -- scanNextToken = .ok none → EOF
      rename_i h_none
      -- §7.4 unterminated-flow check: `.ok tokens` means it did NOT fire, which
      -- is exactly the `sc.flowLevel = 0` the EOF lemma needs. An open flow at
      -- EOF (`[a, b`) is rejected HERE, not inside `scanNextToken`.
      split at h_ok
      · simp at h_ok
      rename_i h_fl_not_pos
      have h_fl0 : sc.flowLevel = 0 := by omega
      -- Directive check (Fix B): its passing forces b = false via the coupling
      split at h_ok
      · simp at h_ok
      · rename_i h_no_dir
        have hb : b = false := by
          cases b
          · rfl
          · exact absurd (h_dir_flag rfl) h_no_dir
        subst hb
        -- Scanner reached EOF — unwind BlockStack, close PendingNode, finalize stream
        exact scanNextToken_none_stream sc sp_start sp_gram sp_block sp_flow sp_scan
          h_stream h_stack h_flow h_pending h_corr h_fl0 h_none
    · -- scanNextToken = .ok (some s') → one step + recurse
      rename_i s_next h_next
      obtain ⟨sp_gram', sp_block', sp_flow', sp_scan', b', h_stream', h_stack', h_flow',
              h_pending', h_flag', h_corr', h_interior'⟩ :=
        scanNextToken_accum_step sc sp_start sp_gram sp_block sp_flow sp_scan s_next
          h_stream h_stack h_flow h_pending h_dir_flag h_corr h_interior h_next
      exact ih s_next sp_gram' sp_block' sp_flow' sp_scan' tokens
        h_stream' h_stack' h_flow' h_pending' h_flag' h_corr' h_interior' h_ok

/-! ## §4 Initial Stream + BOM Handling

    Establish the initial `SLYamlStream` and `ScannerSurfCorr` for `scan`.
    The initial state has `BlockStack.nil` and `PendingNode.noPending` —
    no grammar gap, no active block collections. -/

/-- BOM at position 0: `'\uFEFF'` gives `SLDocumentPrefix.bom`. -/
lemma bom_advance_gives_prefix (input : String) (sp : SurfPos)
    (h_corr : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart) sp)
    (h_peek : ((ScannerState.mk' input).emit .streamStart).peek? = some '\uFEFF') :
    ∃ sp', SLDocumentPrefix sp sp' ∧
           ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart).advance sp' := by
  have h_more := peek_some_hasMore _ _ h_peek
  obtain ⟨rest, h_chars⟩ := peek_some_chars _ sp '\uFEFF' h_corr h_peek
  have h_col := h_corr.col_eq
  have h_sp_eq : sp = ⟨'\uFEFF' :: rest, 0⟩ := by
    cases sp with | mk cs cl =>
    dsimp only [] at h_chars h_col ⊢
    subst h_chars
    have : cl = 0 := by
      rw [h_col]; unfold ScannerState.emit ScannerState.mk'; rfl
    subst this; rfl
  subst h_sp_eq
  -- After advancing past BOM, we're at ⟨rest, 1⟩ with col = 1
  have h_adv := advance_non_newline_corr
    ((ScannerState.mk' input).emit .streamStart) '\uFEFF' rest
    h_corr h_more (by decide) (by decide)
  exact ⟨⟨rest, 1⟩,
         SLDocumentPrefix.bom rest 0 ⟨rest, 1⟩ (GStar.nil _),
         h_adv⟩

/-- Initial stream: at position 0, the empty stream is valid. -/
lemma initial_stream_and_prefix (input : String) :
    ∃ sp, SLYamlStream ⟨input.toList, 0⟩ sp ∧
          ScannerSurfCorr
            (match (ScannerState.mk' input |>.emit .streamStart).peek? with
             | some '\uFEFF' => (ScannerState.mk' input |>.emit .streamStart).advance
             | _ => ScannerState.mk' input |>.emit .streamStart) sp := by
  have h_chars := CouplingBridge.chars_from_zero_toList input
  have h_init := initial_corr input input.toList h_chars
  have h_emit : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart)
      ⟨input.toList, 0⟩ :=
    ⟨h_init.chars_from, h_init.col_eq, h_init.end_eq, h_init.input_prefix, h_init.indent_cols_nonneg⟩
  split
  · -- BOM present
    rename_i h_peek
    obtain ⟨sp', h_prefix, h_corr'⟩ := bom_advance_gives_prefix input _ h_emit h_peek
    -- prefix gives SLDocumentPrefix, wrap in SLYamlStream.single
    exact ⟨sp',
      SLYamlStream.single ⟨input.toList, 0⟩ sp' sp' sp'
        (GStar.cons _ sp' _ h_prefix (GStar.nil _))
        (GOpt.none _) (GStar.nil _),
      h_corr'⟩
  · -- No BOM
    exact ⟨⟨input.toList, 0⟩,
      SLYamlStream.single _ _ _ _ (GStar.nil _) (GOpt.none _) (GStar.nil _),
      h_emit⟩

/-! ## §5 Top-Level Composition: scan → SLYamlStream

    Compose initial stream + scanLoop_grammar_prod to prove scan_content_gives_stream.
    Initial state uses `BlockStack.nil` and `PendingNode.noPending` — no gap. -/

lemma scan_content_gives_stream_v2
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
                           sp_final.chars = [] := by
  unfold scan at h
  simp only [] at h
  obtain ⟨sp, h_stream, h_corr⟩ := initial_stream_and_prefix input
  refine scanLoop_grammar_prod _ ⟨input.toList, 0⟩ sp sp sp sp _ tokens
    h_stream (BlockStack.nil sp) ?_ (PendingNode.noPending ⟨input.toList, 0⟩ sp)
    (fun hb => Bool.noConfusion hb) h_corr
    (fun hge => absurd hge (by
      -- the seed scanner is at flow level 0, so the flow-interior conjunct is vacuous
      split <;>
        simp [advance_flowLevel, ScannerCorrectness.emit_preserves_flowLevel,
          ScannerState.mk']))
    h
  -- B.4β: the initial scanner has `flowLevel = 0` (fresh `mk'`, `emit`/`advance`
  -- preserve it), so the empty flow stack is `nil` (depth 0); its frame-tail
  -- index is free (9b(ii)).
  split
  · rw [advance_flowLevel, ScannerCorrectness.advance_preserves_flowStack,
        ScannerCorrectness.emit_preserves_flowStack]
    exact FlowStackB.nil sp _
  · rw [ScannerCorrectness.emit_preserves_flowStack]
    exact FlowStackB.nil sp _

/-! ## §6 Gap Analysis (historical — file is sorry-free)

    This section dates from the Layer 4x consolidation, when four proof
    obligations remained open here; all have since been discharged (the
    file builds clean, and its chain feeds the proven Group-7 capstones).
    The lagging quint (SLYamlStream + BlockStack + FlowStack + PendingNode +
    ScannerSurfCorr) correctly models the multi-token protocol.

    **v0.4.9 Architecture: FlowStack (Layer 4h.1)**

    FlowStack tracks flow collection nesting between BlockStack and
    PendingNode. Position chain:
    ```
    SLYamlStream sp_start sp_gram
      → BlockStack sp_gram sp_block
        → FlowStack sp_block sp_flow
          → PendingNode false sp_start sp_flow sp_scan
            → ScannerSurfCorr sc sp_scan
    ```
    `absorb_stacks` composes both stacks via h_closable (3×3 = 9 cases),
    simplifying each `accum_step_*` theorem from 3-case BlockStack split
    to a single delegation call.

    Non-trivial `PendingNode` variants carry `h_closable`:
    ```
    h_closable : ∀ sp_mid,
      SSLComments sp_scan sp_mid →
      SLYamlStream sp_start sp_mid
    ```
    The stream `SLYamlStream sp_start sp_block` is captured inside the
    closure at construction time. `sp_start` is a type index on PendingNode.
    This closure is constructed at dispatch time and consumed when the next
    preprocessing step supplies SSLComments (EOF or next token).

    **Proven branches (v0.4.9):**

    `preprocessing_eof_extends_stream` (§1a):
    - `nil + nil + noPending + col=0`: FULLY PROVEN ✅
    - `nil + nil + pendingX + col=0` (all 6 variants): PROVEN ✅ via h_closable
    - `nil + nil + noPending + col≠0`: sorry (BOM edge case)
    - `nil + nil + pendingX + col≠0`: sorry (BOM edge case)
    - `seqLevel | mapLevel` (BlockStack or FlowStack): absorbed by `absorb_stacks`

    `accum_step_structural/block/content` (§1b, §1d, §1e):
    - `absorbed + noPending`: PROVEN ✅ (stream unchanged, new PendingNode opened)
      h_closable in the new PendingNode is `sorry` — requires grammar
      composition from `_prod` theorems (see below)
    - `absorbed + pendingX + col=0` (all 6 variants): PROVEN ✅ (old pending
      closed via `preprocess_some_ssl_comments_col0` + h_closable). New
      PendingNode opened with h_closable sorry (same root cause as noPending).
    - `absorbed + pendingX + col≠0`: sorry (preprocessing SSLComments not
      available at non-zero column — flow context or BOM edge case)
    - BlockStack/FlowStack levels: absorbed by `absorb_stacks` (no case split)

    `accum_step_flow` (§1c) — character-dependent FlowStack (4h.2):
    - `absorbed + noPending + c='['`: PROVEN ✅ FlowStack.flowSeqLevel pushed,
      PendingNode.noPending (clean state inside flow). FlowStack h_closable sorry.
    - `absorbed + noPending + c='{'`: PROVEN ✅ FlowStack.flowMapLevel pushed.
    - `absorbed + noPending + other`: PROVEN ✅ FlowStack.nil, PendingNode.pendingFlow sorry.
    - `absorbed + pendingX + col=0 + c='['/'{'`: PROVEN ✅ FlowStack level pushed.
    - `absorbed + pendingX + col=0 + other`: PROVEN ✅ FlowStack.nil, PendingNode.pendingFlow sorry.
    - `absorbed + pendingX + col≠0`: sorry (same BOM root cause)

    **Sorry root causes (3 independent):**

    1. **h_closable construction** (§1b–§1e noPending): The `fun sp_mid h_ssl => sorry`
       in PendingNode construction (§1b,§1d,§1e) and `fun _ h_str => sorry` in
       FlowStack construction (§1c, for `[`/`{`). Requires `dispatchContent_prod`
       composition: scanner _prod → SFlowNode (n+1) .flowOut → SBlockNode.flowInBlock
       → stream ext via `SLYamlStream.implicitContinue` (now accepts bare documents
       via `GOpt SLAnyDocument`). Blocked on 4i: _prod theorems give
       `SFlowNode 0 .blockIn` but flowInBlock needs `SFlowNode (n+1) .flowOut`.

    2. **BOM col≠0** (§1a): SSeparateInLine requires s-white+ or start-of-line.
       After BOM at col=1 with bare break, neither applies. Genuine YAML grammar
       formalization limitation (not a proof gap).

    3. **Stack operations**: Now handled by `absorb_stacks`. Former BlockStack
       case splits (seqLevel/mapLevel) are fully absorbed — no sorry needed.

    **Dispatch _corr helpers (all PROVEN):**
    - `dispatchStructural_corr` (§1b): structural dispatch → ScannerSurfCorr
    - `dispatchFlowIndicators_corr` (§1c): flow dispatch → ScannerSurfCorr
    - `dispatchBlockIndicators_corr` (§1d): block dispatch → ScannerSurfCorr
    - `dispatchContent_corr` (§1e): content dispatch → ScannerSurfCorr
    - `corr_of_allowDirectives_update`: allowDirectives flag preservation

    **Composition chain (PROVEN):**
    - `scanNextToken_accum_step` (§1f): unfolds scanNextToken, dispatches
    - `scanNextToken_none_stream` (§2): EOF path
    - `scanLoop_grammar_prod` (§3): fuel induction with lagging quint
    - `scan_content_gives_stream_v2` (§5): top-level entry point

    **New helper (v0.4.8):**
    - `preprocess_some_ssl_comments_col0` (§0d): PROVEN ✅. Extracts
      SSLComments from `scanNextToken_preprocess` when col=0, threading
      ScannerSurfCorr through skipToContent → unwindIndents → saveSimpleKey.

    Total sorry declarations: 6 (in §1a–§1e).
    Total sorry source sites: 24 (8 in §1a + 4×4 in §1b–§1e).
    New in v0.4.7: 6 EOF pending cases at col=0 PROVEN via h_closable.
    New in v0.4.8: 24 pending-at-col=0 cases (6×4 dispatch) PROVEN for
      old-pending closure; h_closable for new PendingNode remains sorry
      (same root cause as noPending h_closable).
    New in v0.4.9: FlowStack added as 5th invariant component. absorb_stacks
      eliminates all BlockStack/FlowStack case splits (3×3 → 1 call).
      Each accum_step_* simplified from 3-case to 1-line. §3 comment
      updated: lagging quad → lagging quint.
    New in v0.4.9 (4h.2): Flow dispatch §1c now character-dependent.
      `[`/`{` push FlowStack level (flowSeqLevel/flowMapLevel with sorry
      h_closable) + PendingNode.noPending. `]`/`}`/`,` produce FlowStack.nil
      + PendingNode.pendingFlow sorry. Entry accumulation (4h.3) and flow
      finalization (4h.4) blocked on 4i (context parameter lifting).
    New in v0.4.10: SLYamlStream.implicitContinue now takes GOpt SLAnyDocument
      (matching spec [211]) instead of GOpt SLExplicitDocument. This unblocks
      bare document stream extension. PendingNode refactored to capture sp_start
      as a type index; h_closable simplified from `∀ sp_start sp_mid, SLYamlStream
      sp_start sp_block → SSLComments ... → ...` to `∀ sp_mid, SSLComments ... → ...`
      with the stream captured inside the closure at construction time.
-/

end L4YAML.Proofs.StreamAccum
