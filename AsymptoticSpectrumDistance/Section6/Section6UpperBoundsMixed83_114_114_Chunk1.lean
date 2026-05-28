/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed83_114_114 Baumert check — chunk 1 / 8
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Common

set_option linter.style.nativeDecide false

namespace Section6

def caseMixed83_114_114_chunk1 : Bool :=
  !(vs_chunk1_83_114_114.any innerSearch_v10_114_114)

-- The 12-level nested `vs.any` in `innerSearch_v10_114_114` blows past both
-- the default recursion depth (during elaboration) and the default heartbeat
-- budget (during `native_decide` reduction). Same limits as the pre-chunking
-- `caseMixed83_114_114_check_true`.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
theorem caseMixed83_114_114_chunk1_true :
    caseMixed83_114_114_chunk1 = true := by native_decide

end Section6
