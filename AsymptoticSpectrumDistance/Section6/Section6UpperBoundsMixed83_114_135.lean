/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{8/3} ⊠ E_{11/4} ⊠ E_{13/5}) ≤ 12

Exhaustive layer search verifying that no 13-layer configuration with sizes
(1,1,1,1,1,1,1,1,1,1,1,1,1) and `s0 = (0,0)` exists in E_{8/3} ⊠ E_{11/4}.
This rules out α = 13 (the nested floor bound), establishing α ≤ 12 for
E_{8/3} ⊠ E_{11/4} ⊠ E_{13/5}.

This is needed for the disc proof of paper Theorem 6.9 case 11 — the
(11/4, 11/4, 11/4) discontinuity at α₃ = 13 — where the per-disc-point
candidate refinement leaves the multiset {(8,3), (11,4), (13,5)} as a hard
candidate.

## Slicing analysis

Slice by the E_{13/5} coordinate: 13 layers in E_{8/3} ⊠ E_{11/4} (88 verts,
α = 5). For each clique {i, i+1, …, i+4} of E_{13/5} (5 consecutive vertices,
all pairwise distances ≤ 4 < 5), the union of five adjacent layers is an IS in
K₅ ⊠ E_{8/3} ⊠ E_{11/4}, with cardinality bounded by α(E_{8/3} ⊠ E_{11/4}) = 5.
5-window sum ≤ 5.

Suppose total = 13. Sum of 13 cyclic 5-window sums = 5·13 = 65, max 13·5 = 65,
slack 0. Tight: every 5-window sums to exactly 5. Combined with cyclic
windows giving |Sᵢ| = |Sᵢ₊₅|, and gcd(5,13)=1, all |Sᵢ| equal. Then
13·|Sᵢ| = 13, so |Sᵢ| = 1 for all i. Sizes are forced to (1,…,1).

Up to translation in `Z₈ × Z₁₁` (a symmetry of E_{8/3} ⊠ E_{11/4}), WLOG the
unique element of layer 0 is `(0, 0)`. This factors out 88 and makes the
`native_decide` search tractable.

## Reference

Direct analogue of `Section6UpperBoundsMixed94_94_52.lean` with the inner
graph E_{8/3} ⊠ E_{11/4} (88 verts, 5-clique constraints) instead of
E_{9/4} ⊠ E_{5/2} (45 verts, 4-clique constraints).

## Main result

- `caseMixed83_114_135_check_true`: the layer search returns `true`
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`.
Agrees with `distMod n` on `ZMod n` when `ZMod n = Fin n`. -/
private def distRawN83_114 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-! ## Layer search for E_{8/3} ⊠ E_{11/4} ⊠ E_{13/5}

Layer sizes: (1,1,1,1,1,1,1,1,1,1,1,1,1) over the 13 layers indexed by E_{13/5}.
WLOG `s0 = (0, 0)` by `Z₈ × Z₁₁` translation. -/

/-- Cross-layer non-adjacency in E_{8/3} ⊠ E_{11/4}: returns `true` iff the
    pair `a, b` in `Fin 8 × Fin 11` is NOT adjacent in E_{8/3} ⊠ E_{11/4}.
    Does not shortcut on equality (different layers' equal points are 3-D
    adjacent). -/
def crossNonAdj83_114 (a b : Fin 8 × Fin 11) : Bool :=
  !((a.1 == b.1 || distRawN83_114 8 a.1 b.1 < 3) &&
    (a.2 == b.2 || distRawN83_114 11 a.2 b.2 < 4))

/-- All 88 vertices of E_{8/3} ⊠ E_{11/4}. -/
def verts83_114 : List (Fin 8 × Fin 11) :=
  (List.finRange 8).flatMap fun i => (List.finRange 11).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith83_114 (v : Fin 8 × Fin 11) (prev : List (Fin 8 × Fin 11)) : Bool :=
  prev.all fun w => crossNonAdj83_114 v w

/-- Mixed Baumert layer search for case 11 / bound #7: no valid 13-layer
    configuration with sizes (1,...,1) and `s0 = (0, 0)` exists in
    E_{8/3} ⊠ E_{11/4}.

    Layer i (size 1): single vertex `s_i ∈ Fin 8 × Fin 11`, with `s_0 = (0, 0)`.
    Cross-layer adjacency in C₁₃: layers i, j are adjacent iff cyclic
    distance ≤ 4 (cyclic distance in Z₁₃ is < 5). -/
def caseMixed83_114_135_check : Bool :=
  let vs := verts83_114
  let s0 : Fin 8 × Fin 11 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  -- For each new layer i ≥ 1, compat against prior layers at cyclic dist ≤ 4.
  -- Forward placement: layer i (1 ≤ i ≤ 4) compat against layers 0..i-1
  --                   layer i (5 ≤ i ≤ 12) compat against layers i-4..i-1
  -- Wraparound: for i ≥ 9, additionally compat against layers 0..i-9.
  !(vs.any fun s1 =>
    crossNonAdj83_114 s1 s0 &&
    vs.any fun s2 =>
      compatWith83_114 s2 [s0, s1] &&
    vs.any fun s3 =>
      compatWith83_114 s3 [s0, s1, s2] &&
    vs.any fun s4 =>
      compatWith83_114 s4 [s0, s1, s2, s3] &&
    vs.any fun s5 =>
      compatWith83_114 s5 [s1, s2, s3, s4] &&
    vs.any fun s6 =>
      compatWith83_114 s6 [s2, s3, s4, s5] &&
    vs.any fun s7 =>
      compatWith83_114 s7 [s3, s4, s5, s6] &&
    vs.any fun s8 =>
      compatWith83_114 s8 [s4, s5, s6, s7] &&
    vs.any fun s9 =>
      -- s9 vs layers 5,6,7,8 (forward) and s9 vs s0 (wrap, dist 4)
      compatWith83_114 s9 [s5, s6, s7, s8, s0] &&
    vs.any fun s10 =>
      -- s10 vs layers 6,7,8,9 and wrap vs s0,s1
      compatWith83_114 s10 [s6, s7, s8, s9, s0, s1] &&
    vs.any fun s11 =>
      -- s11 vs layers 7,8,9,10 and wrap vs s0,s1,s2
      compatWith83_114 s11 [s7, s8, s9, s10, s0, s1, s2] &&
    vs.any fun s12 =>
      -- s12 vs layers 8,9,10,11 and wrap vs s0,s1,s2,s3
      compatWith83_114 s12 [s8, s9, s10, s11, s0, s1, s2, s3])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 32000000 in
-- WLOG `s0 = (0, 0)` cuts the outer loop by 88×, making the search tractable.
theorem caseMixed83_114_135_check_true : caseMixed83_114_135_check = true := by
  native_decide

/-- Every element of `Fin 8 × Fin 11` is in `verts83_114`. -/
theorem mem_verts83_114 (v : Fin 8 × Fin 11) : v ∈ verts83_114 := by
  simp only [verts83_114, List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
