/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{8/3} ⊠ E_{8/3} ⊠ E_{11/4}) ≤ 12

Exhaustive layer search verifying that no 8-layer configuration with sizes
(1,2,1,2,2,1,2,2) and `v0 = (0,0)` exists in E_{8/3} ⊠ E_{11/4}. This rules
out α = 13 (the nested floor bound), establishing α ≤ 12 for
E_{8/3}² ⊠ E_{11/4}.

This is needed for the disc proof of paper Theorem 6.9 case 11 — the
(11/4, 11/4, 11/4) discontinuity at α₃ = 13 — where the per-disc-point
candidate refinement leaves the multiset {(8,3), (8,3), (11,4)} as a hard
candidate.

## Slicing analysis

Slice by an E_{8/3} coordinate: 8 layers in E_{8/3} ⊠ E_{11/4} (88 verts,
α = 5). For each 3-clique {i, i+1, i+2} of E_{8/3}, the union of three
adjacent layers is an IS in K₃ ⊠ E_{8/3} ⊠ E_{11/4}, with cardinality
bounded by α(E_{8/3} ⊠ E_{11/4}) = 5. 3-window sum ≤ 5.

Suppose total = 13. Sum of 8 cyclic 3-window sums = 3·13 = 39, max 8·5 = 40,
slack 1. The IP is identical to case 8 (`ip_solutions`/`canonical_sizes`):
sizes are forced to a rotation of (1,2,1,2,2,1,2,2).

Up to translation in `Z₈ × Z₁₁` (a symmetry of E_{8/3} ⊠ E_{11/4}), WLOG
the unique element of layer 0 is `(0, 0)`. This factors out 88 and makes
the `native_decide` search tractable.

## Reference

Direct analogue of `Section6UpperBoundsCase8.lean`'s `case8_check` with the
inner graph E_{8/3} ⊠ E_{11/4} (88 verts) instead of E_{8/3}² (64 verts).

## Main result

- `caseMixed83_83_114_check_true`: the layer search returns `true`
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`. -/
private def distRawN83_83_114 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-! ## Layer search for E_{8/3}² ⊠ E_{11/4} (slice by an E_{8/3})

Layer sizes: (1,2,1,2,2,1,2,2) over 8 layers indexed by (an) E_{8/3}.
WLOG `v0 = (0, 0)` by `Z₈ × Z₁₁` translation. -/

/-- Cross-layer non-adjacency in E_{8/3} ⊠ E_{11/4}: returns `true` iff the
    pair `a, b` in `Fin 8 × Fin 11` is NOT adjacent in E_{8/3} ⊠ E_{11/4}. -/
def crossNonAdj83_114' (a b : Fin 8 × Fin 11) : Bool :=
  !((a.1 == b.1 || distRawN83_83_114 8 a.1 b.1 < 3) &&
    (a.2 == b.2 || distRawN83_83_114 11 a.2 b.2 < 4))

/-- All 88 vertices of E_{8/3} ⊠ E_{11/4}. -/
def verts83_114' : List (Fin 8 × Fin 11) :=
  (List.finRange 8).flatMap fun i => (List.finRange 11).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith83_114' (v : Fin 8 × Fin 11) (prev : List (Fin 8 × Fin 11)) :
    Bool :=
  prev.all fun w => crossNonAdj83_114' v w

/-- Encode a pair for ordering (to break symmetry in size-2 layers). -/
def enc83_114' (v : Fin 8 × Fin 11) : ℕ := v.1.val * 11 + v.2.val

/-- Mixed Baumert layer search for case 11 / bound #5: no valid 8-layer
    configuration with sizes (1,2,1,2,2,1,2,2) and `v0 = (0, 0)` exists in
    E_{8/3} ⊠ E_{11/4}. -/
def caseMixed83_83_114_check : Bool :=
  let vs := verts83_114'
  let v0 : Fin 8 × Fin 11 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  !(vs.any fun v10 =>
      crossNonAdj83_114' v10 v0 &&
    vs.any fun v11 =>
      enc83_114' v10 < enc83_114' v11 && crossNonAdj83_114' v10 v11 &&
      crossNonAdj83_114' v11 v0 &&
    vs.any fun v2 =>
      compatWith83_114' v2 [v0, v10, v11] &&
    vs.any fun v30 =>
      compatWith83_114' v30 [v10, v11, v2] &&
    vs.any fun v31 =>
      enc83_114' v30 < enc83_114' v31 && crossNonAdj83_114' v30 v31 &&
      compatWith83_114' v31 [v10, v11, v2] &&
    vs.any fun v40 =>
      compatWith83_114' v40 [v2, v30, v31] &&
    vs.any fun v41 =>
      enc83_114' v40 < enc83_114' v41 && crossNonAdj83_114' v40 v41 &&
      compatWith83_114' v41 [v2, v30, v31] &&
    vs.any fun v5 =>
      compatWith83_114' v5 [v30, v31, v40, v41] &&
    vs.any fun v60 =>
      compatWith83_114' v60 [v40, v41, v5, v0] &&
    vs.any fun v61 =>
      enc83_114' v60 < enc83_114' v61 && crossNonAdj83_114' v60 v61 &&
      compatWith83_114' v61 [v40, v41, v5, v0] &&
    vs.any fun v70 =>
      compatWith83_114' v70 [v5, v60, v61, v0, v10, v11] &&
    vs.any fun v71 =>
      enc83_114' v70 < enc83_114' v71 && crossNonAdj83_114' v70 v71 &&
      compatWith83_114' v71 [v5, v60, v61, v0, v10, v11])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 32000000 in
-- WLOG `v0 = (0, 0)` cuts the outer loop by 88×, making the search tractable.
theorem caseMixed83_83_114_check_true : caseMixed83_83_114_check = true := by
  native_decide

/-- Every element of `Fin 8 × Fin 11` is in `verts83_114'`. -/
theorem mem_verts83_114' (v : Fin 8 × Fin 11) : v ∈ verts83_114' := by
  simp only [verts83_114', List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
