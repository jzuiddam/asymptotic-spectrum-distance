/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{9/4} ⊠ E_{9/4} ⊠ E_{5/2}) ≤ 8

Exhaustive layer search verifying that no 9-layer configuration with sizes
(1,1,1,1,1,1,1,1,1) and `s0 = (0,0)` exists in E_{9/4} ⊠ E_{5/2}. This rules
out α = 9 (the nested floor bound), establishing α ≤ 8 for E_{9/4}² ⊠ E_{5/2}.

This is needed for the disc proof of paper Theorem 6.9 case 9 — the
(9/4, 7/3, 5/2) discontinuity at α₃ = 9 — where the per-disc-point candidate
refinement leaves the multiset {(9,4), (9,4), (5,2)} as a hard candidate.

## Slicing analysis

Slice by the first E_{9/4} coordinate: 9 layers in E_{9/4} ⊠ E_{5/2}
(45 verts each, α = 4). For each clique {i, i+1, i+2, i+3} of E_{9/4}
(distance ≤ 3, all ≤ 4-1 = 3 so cliques up to size 4), the union of four
adjacent layers is an IS in K₄ ⊠ E_{9/4} ⊠ E_{5/2}, with cardinality bounded
by α(E_{9/4} ⊠ E_{5/2}) = 4. 4-window sum ≤ 4.

Suppose total = 9. Sum of 9 cyclic 4-window sums = 4·9 = 36, max 9·4 = 36,
slack 0. Tight: every 4-window sums to exactly 4. Combined with cyclic
windows giving |Sᵢ| = |Sᵢ₊₄|, and gcd(4,9)=1, all |Sᵢ| equal. Then
9·|Sᵢ| = 9, so |Sᵢ| = 1 for all i. Sizes are forced to (1,...,1).

Up to translation in `Z₉ × Z₅` (a symmetry of E_{9/4} ⊠ E_{5/2}), WLOG the
unique element of layer 0 is `(0, 0)`. This factors out 45 and makes the
`native_decide` search tractable.

## Reference

Direct analogue of `Section6UpperBoundsMixed52_83_83.lean` with the inner graph
swapped from E_{8/3}² (64 verts) to E_{9/4} ⊠ E_{5/2} (45 verts) and the
outer slicing adjusted to the C₉ structure (4-clique constraints instead of
2-clique edges).

## Main result

- `caseMixed94_check_true`: the layer search returns `true`
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`.
Agrees with `distMod n` on `ZMod n` when `ZMod n = Fin n`. -/
private def distRawN (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-! ## Layer search for E_{9/4}² ⊠ E_{5/2}

Layer sizes: (1,1,1,1,1,1,1,1,1) over the 9 layers indexed by E_{9/4}.
WLOG `s0 = (0, 0)` by `Z₉ × Z₅` translation. -/

/-- Cross-layer non-adjacency in E_{9/4} ⊠ E_{5/2}: returns `true` iff the pair
    `a, b` in `Fin 9 × Fin 5` is NOT adjacent in E_{9/4} ⊠ E_{5/2}. Does not
    shortcut on equality (different layers' equal points are 3-D adjacent). -/
def crossNonAdj94_52 (a b : Fin 9 × Fin 5) : Bool :=
  !((a.1 == b.1 || distRawN 9 a.1 b.1 < 4) &&
    (a.2 == b.2 || distRawN 5 a.2 b.2 < 2))

/-- All 45 vertices of E_{9/4} ⊠ E_{5/2}. -/
def verts94_52 : List (Fin 9 × Fin 5) :=
  (List.finRange 9).flatMap fun i => (List.finRange 5).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith94_52 (v : Fin 9 × Fin 5) (prev : List (Fin 9 × Fin 5)) : Bool :=
  prev.all fun w => crossNonAdj94_52 v w

/-- Mixed Baumert layer search for case 9: no valid 9-layer configuration with
    sizes (1,1,1,1,1,1,1,1,1) and `s0 = (0, 0)` exists in E_{9/4} ⊠ E_{5/2}.

    Layer i (size 1): single vertex `s_i ∈ Fin 9 × Fin 5`, with `s_0 = (0, 0)`.
    Cross-layer adjacency in C₉: layers i, j are adjacent iff |i - j| ≤ 3
    (cyclic distance in Z₉ is < 4). -/
def caseMixed94_check : Bool :=
  let vs := verts94_52
  let s0 : Fin 9 × Fin 5 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  -- s_0 must be checked against later layers via compatWith94_52
  -- C₉-distance ≤ 3 pairs: (0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),
  --   (3,4),(3,5),(3,6),(4,5),(4,6),(4,7),(5,6),(5,7),(5,8),
  --   (6,7),(6,8),(6,0),(7,8),(7,0),(7,1),(8,0),(8,1),(8,2)
  -- For each new layer i, compat against layers max(0, i-3)..i-1
  -- and layers > i wrap around.
  -- Forward placement: layer i constrained against layers i-3, i-2, i-1.
  -- Then at the end we also need to enforce wraparound: 6,7,8 vs 0,1,2.
  !(vs.any fun s1 =>
    crossNonAdj94_52 s1 s0 &&
    vs.any fun s2 =>
      compatWith94_52 s2 [s0, s1] &&
    vs.any fun s3 =>
      compatWith94_52 s3 [s0, s1, s2] &&
    vs.any fun s4 =>
      compatWith94_52 s4 [s1, s2, s3] &&
    vs.any fun s5 =>
      compatWith94_52 s5 [s2, s3, s4] &&
    vs.any fun s6 =>
      -- s6 vs layers 3,4,5 (forward) and s6 vs s0 (wraparound, dist 3)
      compatWith94_52 s6 [s3, s4, s5, s0] &&
    vs.any fun s7 =>
      -- s7 vs layers 4,5,6 and wraparound vs s0, s1 (distances 2, 3 cyclically)
      compatWith94_52 s7 [s4, s5, s6, s0, s1] &&
    vs.any fun s8 =>
      -- s8 vs layers 5,6,7 and wraparound vs s0, s1, s2
      compatWith94_52 s8 [s5, s6, s7, s0, s1, s2])

set_option maxRecDepth 2048 in
set_option maxHeartbeats 16000000 in
-- WLOG `s0 = (0, 0)` cuts the outer loop by 45×, making the search tractable.
theorem caseMixed94_check_true : caseMixed94_check = true := by native_decide

/-- Every element of `Fin 9 × Fin 5` is in `verts94_52`. -/
theorem mem_verts94_52 (v : Fin 9 × Fin 5) : v ∈ verts94_52 := by
  simp only [verts94_52, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
