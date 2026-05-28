/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed114_114_135 Baumert check — chunk 2 / 4
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed114_114_135_Common

set_option linter.style.nativeDecide false

namespace Section6

def caseMixed114_114_135_chunk2 : Bool :=
  !(vs_chunk2_114_114_135.any innerSearch_s1_114_114_135)

-- See Chunk1 for the rationale on these limits.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
theorem caseMixed114_114_135_chunk2_true :
    caseMixed114_114_135_chunk2 = true := by native_decide

end Section6
