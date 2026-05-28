/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed52_83_114 Baumert check — chunk 1 / 4

Runs `native_decide` on the first 22 of 88 `s01` values. Built in parallel
with chunks 2-4 to amortise the ~21-min serial cost.
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed52_83_114_Common

set_option linter.style.nativeDecide false

namespace Section6

/-- Chunk 1 of the Mixed52_83_114 layer search: no valid `s01` in the first
    22 of `verts83_114_v2` admits a complete 5-layer configuration. -/
def caseMixed52_83_114_chunk1 : Bool :=
  !(vs_chunk1_83_114.any innerSearch_s01_83_114)

-- The 11-level nested `vs.any` in `innerSearch_s01_83_114` blows past both
-- the default recursion depth (during elaboration) and the default heartbeat
-- budget (during `native_decide` reduction). Same family of limits as the
-- working Mixed52_114_114 / Mixed83_114_114 chunk lemmas.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
theorem caseMixed52_83_114_chunk1_true :
    caseMixed52_83_114_chunk1 = true := by native_decide

end Section6
