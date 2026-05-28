/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{11/4} ⊠ E_{11/4} ⊠ E_{13/5}) ≤ 12

Exhaustive layer search verifying that no 13-layer configuration with sizes
(1,1,1,1,1,1,1,1,1,1,1,1,1) and `s0 = (0,0)` exists in E_{11/4}². This rules
out α = 13 (the nested floor bound), establishing α ≤ 12 for
E_{11/4}² ⊠ E_{13/5}.

This is needed for the disc proof of paper Theorem 6.9 case 11 — the
(11/4, 11/4, 11/4) discontinuity at α₃ = 13 — where the per-disc-point
candidate refinement leaves the multiset {(11,4), (11,4), (13,5)} as a
hard candidate.

## Slicing analysis

Slice by the E_{13/5} coordinate: 13 layers in E_{11/4}² (121 verts, α = 5).
For each clique {i, …, i+4} of E_{13/5} (5 consecutive vertices, all pairwise
distances ≤ 4 < 5), the union of five adjacent layers is an IS in
K₅ ⊠ E_{11/4}², with cardinality bounded by α(E_{11/4}²) = 5. 5-window sum ≤ 5.

Suppose total = 13. Sum of 13 cyclic 5-window sums = 5·13 = 65, max 13·5 = 65,
slack 0. Tight: every 5-window sums to exactly 5. Combined with cyclic
windows giving |Sᵢ| = |Sᵢ₊₅|, and gcd(5,13)=1, all |Sᵢ| equal. Then
13·|Sᵢ| = 13, so |Sᵢ| = 1 for all i. Sizes are forced to (1,…,1).

Up to translation in `Z₁₁ × Z₁₁` (a symmetry of E_{11/4}²), WLOG the
unique element of layer 0 is `(0, 0)`. This factors out 121 and makes the
`native_decide` search tractable.

## Architecture: 4-way chunked native_decide

The single `native_decide` over the 13-layer search runs ~24 min wall on a
fast machine. We split the outer `s1` loop into four chunks across companion
files `Section6UpperBoundsMixed114_114_135_Chunk{1,2,3,4}.lean`, each
carrying its own `native_decide`. Lake compiles them in parallel; this file
aggregates the four chunk lemmas into the original
`caseMixed114_114_135_check_true`. Shared helpers live in
`Section6UpperBoundsMixed114_114_135_Common.lean`.

## Reference

Direct analogue of `Section6UpperBoundsMixed83_114_135.lean` with the inner
graph E_{11/4}² (121 verts) instead of E_{8/3} ⊠ E_{11/4} (88 verts).

## Main result

- `caseMixed114_114_135_check_true`: the layer search returns `true`
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed114_114_135_Common
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed114_114_135_Chunk1
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed114_114_135_Chunk2
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed114_114_135_Chunk3
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed114_114_135_Chunk4

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Layer search for E_{11/4} ⊠ E_{11/4} ⊠ E_{13/5}

Layer sizes: (1,1,1,1,1,1,1,1,1,1,1,1,1) over the 13 layers indexed by E_{13/5}.
WLOG `s0 = (0, 0)` by `Z₁₁ × Z₁₁` translation.

Implementation note: defined as `!(verts114_114.any innerSearch_s1_114_114_135)`
rather than an inline nested-`vs.any` closure, so the chunked combining proof
does not need to perform deep defeq on the full 13-level nesting. Downstream
callers that previously did `unfold caseMixed114_114_135_check` now need an
additional `unfold innerSearch_s1_114_114_135` step. -/
def caseMixed114_114_135_check : Bool :=
  !(verts114_114.any innerSearch_s1_114_114_135)

theorem caseMixed114_114_135_check_true :
    caseMixed114_114_135_check = true := by
  have h1 : vs_chunk1_114_114_135.any innerSearch_s1_114_114_135 = false := by
    have := caseMixed114_114_135_chunk1_true
    simpa [caseMixed114_114_135_chunk1, Bool.not_eq_true'] using this
  have h2 : vs_chunk2_114_114_135.any innerSearch_s1_114_114_135 = false := by
    have := caseMixed114_114_135_chunk2_true
    simpa [caseMixed114_114_135_chunk2, Bool.not_eq_true'] using this
  have h3 : vs_chunk3_114_114_135.any innerSearch_s1_114_114_135 = false := by
    have := caseMixed114_114_135_chunk3_true
    simpa [caseMixed114_114_135_chunk3, Bool.not_eq_true'] using this
  have h4 : vs_chunk4_114_114_135.any innerSearch_s1_114_114_135 = false := by
    have := caseMixed114_114_135_chunk4_true
    simpa [caseMixed114_114_135_chunk4, Bool.not_eq_true'] using this
  unfold caseMixed114_114_135_check
  rw [← chunks_partition_114_114_135, List.any_append, List.any_append,
      List.any_append, h1, h2, h3, h4]
  rfl

end Section6
