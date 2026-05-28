/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Case 8 Baumert check — chunk 3 / 4
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase8_Common

set_option linter.style.nativeDecide false

namespace Section6

def case8_chunk3 : Bool :=
  !(vs_chunk3_case8.any innerSearch_v0_case8)

-- See Chunk1 for the rationale on these limits.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
theorem case8_chunk3_true : case8_chunk3 = true := by native_decide

end Section6
