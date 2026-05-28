/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed52_114_114 Baumert check — chunk 4 / 8
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed52_114_114_Common

set_option linter.style.nativeDecide false

namespace Section6

def caseMixed52_114_114_chunk4 : Bool :=
  !(vs_chunk4_114_114.any innerSearch_s01_114_114)

-- See Chunk1 for the rationale on these limits.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 32000000 in
theorem caseMixed52_114_114_chunk4_true :
    caseMixed52_114_114_chunk4 = true := by native_decide

end Section6
