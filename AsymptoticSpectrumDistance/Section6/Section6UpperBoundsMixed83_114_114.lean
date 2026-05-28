/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{8/3} ⊠ E_{11/4} ⊠ E_{11/4}) ≤ 12

Exhaustive layer search verifying that no 8-layer configuration with sizes
(1,2,1,2,2,1,2,2) and `v0 = (0,0)` exists in E_{11/4}². This rules out
α = 13 (the nested floor bound), establishing α ≤ 12 for
E_{8/3} ⊠ E_{11/4}².

This is needed for the disc proof of paper Theorem 6.9 case 11 — the
(11/4, 11/4, 11/4) discontinuity at α₃ = 13 — where the per-disc-point
candidate refinement leaves the multiset {(8,3), (11,4), (11,4)} as a
hard candidate.

## Slicing analysis

Slice by the E_{8/3} coordinate: 8 layers in E_{11/4}² (121 verts, α = 5).
For each 3-clique {i, i+1, i+2} of E_{8/3}, the union of three adjacent
layers is an IS in K₃ ⊠ E_{11/4}², with cardinality bounded by α(E_{11/4}²)
= 5. 3-window sum ≤ 5.

Suppose total = 13. Sum of 8 cyclic 3-window sums = 3·13 = 39, max 8·5 = 40,
slack 1. The IP is identical to case 8: sizes are forced to a rotation of
(1,2,1,2,2,1,2,2).

Up to translation in `Z₁₁ × Z₁₁`, WLOG the unique element of layer 0 is
`(0, 0)`. This factors out 121 and makes the `native_decide` search
tractable.

## Architecture: 8-way chunked native_decide

The single `native_decide` over the 8-layer search runs ~29 min wall on a
fast machine. We split the outer `v10` loop into eight chunks across
companion files `Section6UpperBoundsMixed83_114_114_Chunk{1,…,8}.lean`,
each carrying its own `native_decide`. Lake compiles them in parallel; this
file aggregates the eight chunk lemmas into the original
`caseMixed83_114_114_check_true`. Shared helpers live in
`Section6UpperBoundsMixed83_114_114_Common.lean`.

## Reference

Direct analogue of `Section6UpperBoundsMixed83_83_114.lean` with the inner
graph E_{11/4}² (121 verts) instead of E_{8/3} ⊠ E_{11/4} (88 verts).

## Main result

- `caseMixed83_114_114_check_true`: the layer search returns `true`
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Common
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Chunk1
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Chunk2
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Chunk3
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Chunk4
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Chunk5
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Chunk6
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Chunk7
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114_Chunk8

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Layer search for E_{8/3} ⊠ E_{11/4}² (slice by E_{8/3})

Layer sizes: (1,2,1,2,2,1,2,2) over 8 layers indexed by E_{8/3}.
WLOG `v0 = (0, 0)` by `Z₁₁ × Z₁₁` translation.

Implementation note: defined as `!(verts114_114'.any innerSearch_v10_114_114)`
rather than an inline nested-`vs.any` closure, so the chunked combining proof
does not need to perform deep defeq on the full 12-level nesting. Downstream
callers that previously did `unfold caseMixed83_114_114_check` now need an
additional `unfold innerSearch_v10_114_114` step. -/
def caseMixed83_114_114_check : Bool :=
  !(verts114_114'.any innerSearch_v10_114_114)

theorem caseMixed83_114_114_check_true :
    caseMixed83_114_114_check = true := by
  have h1 : vs_chunk1_83_114_114.any innerSearch_v10_114_114 = false := by
    have := caseMixed83_114_114_chunk1_true
    simpa [caseMixed83_114_114_chunk1, Bool.not_eq_true'] using this
  have h2 : vs_chunk2_83_114_114.any innerSearch_v10_114_114 = false := by
    have := caseMixed83_114_114_chunk2_true
    simpa [caseMixed83_114_114_chunk2, Bool.not_eq_true'] using this
  have h3 : vs_chunk3_83_114_114.any innerSearch_v10_114_114 = false := by
    have := caseMixed83_114_114_chunk3_true
    simpa [caseMixed83_114_114_chunk3, Bool.not_eq_true'] using this
  have h4 : vs_chunk4_83_114_114.any innerSearch_v10_114_114 = false := by
    have := caseMixed83_114_114_chunk4_true
    simpa [caseMixed83_114_114_chunk4, Bool.not_eq_true'] using this
  have h5 : vs_chunk5_83_114_114.any innerSearch_v10_114_114 = false := by
    have := caseMixed83_114_114_chunk5_true
    simpa [caseMixed83_114_114_chunk5, Bool.not_eq_true'] using this
  have h6 : vs_chunk6_83_114_114.any innerSearch_v10_114_114 = false := by
    have := caseMixed83_114_114_chunk6_true
    simpa [caseMixed83_114_114_chunk6, Bool.not_eq_true'] using this
  have h7 : vs_chunk7_83_114_114.any innerSearch_v10_114_114 = false := by
    have := caseMixed83_114_114_chunk7_true
    simpa [caseMixed83_114_114_chunk7, Bool.not_eq_true'] using this
  have h8 : vs_chunk8_83_114_114.any innerSearch_v10_114_114 = false := by
    have := caseMixed83_114_114_chunk8_true
    simpa [caseMixed83_114_114_chunk8, Bool.not_eq_true'] using this
  unfold caseMixed83_114_114_check
  rw [← chunks_partition_83_114_114, List.any_append, List.any_append,
      List.any_append, List.any_append, List.any_append, List.any_append,
      List.any_append, h1, h2, h3, h4, h5, h6, h7, h8]
  rfl

end Section6
