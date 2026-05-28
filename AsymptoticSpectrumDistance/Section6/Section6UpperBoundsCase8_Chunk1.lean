/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Case 8 Baumert check — chunk 1 / 4

Runs `native_decide` on the first 16 of 64 `v0` values. Built in parallel
with chunks 2-4 to amortise the ~26-min serial cost.
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase8_Common

set_option linter.style.nativeDecide false

namespace Section6

/-- Chunk 1 of the Case 8 layer search: no valid `v0` in the first 16 of
    `verts83` admits a complete 8-layer configuration. -/
def case8_chunk1 : Bool :=
  !(vs_chunk1_case8.any innerSearch_v0_case8)

-- The 13-level nested `vs.any` in `innerSearch_v0_case8` blows past both
-- the default recursion depth (during elaboration) and the default heartbeat
-- budget (during `native_decide` reduction). Same family of limits as the
-- working Mixed52_114_114 / Mixed83_114_114 chunk lemmas.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
theorem case8_chunk1_true : case8_chunk1 = true := by native_decide

end Section6
