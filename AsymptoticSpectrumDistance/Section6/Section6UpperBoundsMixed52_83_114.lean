/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{5/2} ⊠ E_{8/3} ⊠ E_{11/4}) ≤ 11

Exhaustive layer search verifying that no 5-layer configuration with sizes
(2, 2, 3, 2, 3) and `s00 = (0, 0)` exists in E_{8/3} ⊠ E_{11/4}. This rules
out α = 12 (the nested floor bound), establishing α ≤ 11 for
E_{5/2} ⊠ E_{8/3} ⊠ E_{11/4}.

## Slicing analysis

Slice by the E_{5/2} coordinate: 5 layers in E_{8/3} ⊠ E_{11/4}
(88 verts each, α = 5). For each edge {i, i+1} of E_{5/2}, the union of two
adjacent layers is an IS in K₂ ⊠ E_{8/3} ⊠ E_{11/4}, which has α =
α(E_{8/3} ⊠ E_{11/4}) = 5. Adjacent pair sum ≤ 5.

Suppose total = 12. Sum of 5 cyclic edge-pair sums = 2·12 = 24, max 5·5 = 25,
slack 1. Up to rotation, sizes are forced to (2, 2, 3, 2, 3).

Up to translation in `Z₈ × Z₁₁` (a symmetry of E_{8/3} ⊠ E_{11/4}), WLOG the
first element of layer 0 is `(0, 0)`. This factors out 88 and makes the
`native_decide` search tractable.

## Architecture: 4-way chunked native_decide

The single `native_decide` over the 5-layer search runs ~21 min wall on a
fast machine. We split the outer `s01` loop into four chunks across companion
files `Section6UpperBoundsMixed52_83_114_Chunk{1,2,3,4}.lean`, each carrying
its own `native_decide`. Lake compiles them in parallel; this file aggregates
the four chunk lemmas into the original `caseMixed52_83_114_check_true`.
Shared helpers (graph predicates, `innerSearch_s01_83_114`, chunk lists,
partition proof) live in `Section6UpperBoundsMixed52_83_114_Common.lean`.

## Reference

Direct analogue of `Section6UpperBoundsMixed52_52_114.lean`'s
`caseMixed52_52_114_check`, with the inner graph swapped from
E_{5/2} ⊠ E_{11/4} (55 verts) to E_{8/3} ⊠ E_{11/4} (88 verts) and the
translation symmetry adjusted to `Z₈ × Z₁₁`.

## Main result

- `caseMixed52_83_114_check_true`: the layer search returns `true`
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed52_83_114_Common
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed52_83_114_Chunk1
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed52_83_114_Chunk2
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed52_83_114_Chunk3
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed52_83_114_Chunk4

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Layer search for E_{5/2} ⊠ (E_{8/3} ⊠ E_{11/4})

Layer sizes: (2, 2, 3, 2, 3) over the 5 layers indexed by the outer E_{5/2}.
WLOG `s00 = (0, 0)` by `Z₈ × Z₁₁` translation.

Implementation note: defined as `!(verts83_114_v2.any innerSearch_s01_83_114)`
rather than an inline nested-`vs.any` closure, so the chunked combining proof
does not need to perform deep defeq on the full 11-level nesting. Downstream
callers that previously did `unfold caseMixed52_83_114_check` now need an
additional `unfold innerSearch_s01_83_114` step. -/

/-- Mixed Baumert layer search: no valid 5-layer configuration with sizes
    (2, 2, 3, 2, 3) and `s00 = (0, 0)` exists in E_{8/3} ⊠ E_{11/4}.

    Layer 0 (size 2): s00 = (0,0), s01
    Layer 1 (size 2): s10, s11
    Layer 2 (size 3): s20, s21, s22
    Layer 3 (size 2): s30, s31
    Layer 4 (size 3): s40, s41, s42

    Cross-layer adjacency in C₅: {0,1}, {1,2}, {2,3}, {3,4}, {4,0}. -/
def caseMixed52_83_114_check : Bool :=
  !(verts83_114_v2.any innerSearch_s01_83_114)

theorem caseMixed52_83_114_check_true :
    caseMixed52_83_114_check = true := by
  have h1 : vs_chunk1_83_114.any innerSearch_s01_83_114 = false := by
    have := caseMixed52_83_114_chunk1_true
    simpa [caseMixed52_83_114_chunk1, Bool.not_eq_true'] using this
  have h2 : vs_chunk2_83_114.any innerSearch_s01_83_114 = false := by
    have := caseMixed52_83_114_chunk2_true
    simpa [caseMixed52_83_114_chunk2, Bool.not_eq_true'] using this
  have h3 : vs_chunk3_83_114.any innerSearch_s01_83_114 = false := by
    have := caseMixed52_83_114_chunk3_true
    simpa [caseMixed52_83_114_chunk3, Bool.not_eq_true'] using this
  have h4 : vs_chunk4_83_114.any innerSearch_s01_83_114 = false := by
    have := caseMixed52_83_114_chunk4_true
    simpa [caseMixed52_83_114_chunk4, Bool.not_eq_true'] using this
  unfold caseMixed52_83_114_check
  rw [← chunks_partition_83_114, List.any_append, List.any_append,
      List.any_append, h1, h2, h3, h4]
  rfl

end Section6
