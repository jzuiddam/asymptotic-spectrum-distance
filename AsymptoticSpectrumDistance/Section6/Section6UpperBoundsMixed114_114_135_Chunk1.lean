/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed114_114_135 Baumert check — chunk 1 / 4

Runs `native_decide` on the first 30 of 121 `s1` values. Built in parallel
with chunks 2-4 to amortise the ~24-min serial cost.
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed114_114_135_Common

set_option linter.style.nativeDecide false

namespace Section6

/-- Chunk 1 of the Mixed114_114_135 layer search: no valid `s1` in the first
    30 of `verts114_114` admits a complete 13-layer configuration. -/
def caseMixed114_114_135_chunk1 : Bool :=
  !(vs_chunk1_114_114_135.any innerSearch_s1_114_114_135)

-- The 13-level nested `vs.any` in `innerSearch_s1_114_114_135` blows past
-- both the default recursion depth (during elaboration) and the default
-- heartbeat budget (during `native_decide` reduction). Same limits as the
-- pre-chunking `caseMixed114_114_135_check_true`.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
theorem caseMixed114_114_135_chunk1_true :
    caseMixed114_114_135_chunk1 = true := by native_decide

end Section6
