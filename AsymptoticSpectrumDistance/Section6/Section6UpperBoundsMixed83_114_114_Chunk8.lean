/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed83_114_114 Baumert check — chunk 8 / 8 (trailing remainder)
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Common

set_option linter.style.nativeDecide false

namespace Section6

def caseMixed83_114_114_chunk8 : Bool :=
  !(vs_chunk8_83_114_114.any innerSearch_v10_114_114)

-- See Chunk1 for the rationale on these limits.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
theorem caseMixed83_114_114_chunk8_true :
    caseMixed83_114_114_chunk8 = true := by native_decide

end Section6
