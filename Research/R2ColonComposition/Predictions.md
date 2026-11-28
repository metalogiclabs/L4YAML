# Compose scanner ownership and the explicit-colon continuation

Parent continuation evidence: 801aa32c222fa8590c91dff70950027232e19ace.
Ownership evidence: 7f7357ad10be9ad3d04372422b32f2119004dd24.
Starting diagnostic StreamAccum SHA256:
819993c47d13b998e91e6c1c757499d83c63c69ff5a951cbced23dcfabf1e831.

Intended chain: successful scanValue -> own-column exclusion ->
colon_open_map_explicit -> stored SlotValues / NodeValues ->
accum_block_pending -> scanLoop_grammar_prod / scan_content_gives_stream_v2
(Blueprint 7.3 / 7.2). This is an isolated diagnostic, not production qualification.

1. Preserve both existing informative faces. The negative explicit-entry
   face must retain NotQuestionPark AND TopUnmarked; the positive face must
   retain its NodeValues. The wide h_vslot must retain EntryValues.
2. Successful block colon ownership permits a nonempty smaller-mark domain.
   Verify actual nested and root states, fuel 0/1/2, empty input, omission,
   non-nil siblings and a question negative control before proving composition.
3. An incoming whole entry continuation, the actual colon, and scanner
   exclusion should construct both the outgoing wide continuation and a
   node continuation retaining the consumed mapping's arbitrary sibling tail.
4. Inspect whether the actual explicit-colon producer/callers possess that
   incoming family. No new external premise counts as a funded producer;
   expose every missing supplier at its real call site, without a fallback.
5. The old h_slot only returns a stream. Exclusion cannot manufacture an
   ancestor family from that result. Preserve any compiler evidence that
   distinguishes a genuinely funded composition from an interface relocation.
6. Preserve all unrelated diagnostic demands, exact sources and failures.
   Compare actual producer axiom profiles; no sorryAx on any claimed proof.
   No critical retirement, whole build, native qualification or PR mutation
   is predicted. Reuse the already qualified #384 tree without rebuilding it.
