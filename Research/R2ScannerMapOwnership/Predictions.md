# Actual scanner ownership for the joint context migration

Heath Sanchez · 2026-11-28

Objective: complete the eight-residual continuation migration and qualification.
Current production integration head 1383fa62; current checked research source
00c21991 / e2d86f8c. Parallel 688e4052 has the same positive source bytes and an
accepted invariant/flow prefix. Its active R2JointFrames work is reused rather
than duplicated. This lane owns scanner map ownership and actual node births.

Before mutation: R2JointFrames.Context.entries needs MarkedMaps in addition to
existing Sound.slots. Sound.slots proves size alignment and nonnegative marked
columns, but does not state that a marked indent is a map. The only mark writer
is scanKey; its existing scanKeyValidate rejects a question at a sequence's own
width. Preprocess and every other dispatch preserve marks or erase them.

Predictions:
1. Initialized scanner schedules, fuel 0/1/2, flow and document resets satisfy
   map ownership; a deliberately marked sequence fails the independent check.
2. Existing scanKey_top_not_sequence plus the actual push decision pays the
   mark-writing case; no new scanner flag or assumed reachability is required.
3. Generic push/pop/erase lemmas plus existing array preservation facts prove
   ownership through preprocessing and all actual dispatches.
4. A token-step theorem can be seeded at mk' and carried with existing Sound,
   ColFloor, sentinel and monotonicity facts. A conditional family premise is
   not payment of this scanner property.
5. The joint-context grammar work remains separate until its actual production
   writers compile; eight labels / seven critical positions are unchanged until
   a complete migration and fresh census establish a reduction.

Capstone path: actual scanner ownership → joint-context projection → real
node/entry producers → accumulation → scanLoop_grammar_prod /
scan_content_gives_stream_v2 (Blueprint 7.3 / 7.2).
