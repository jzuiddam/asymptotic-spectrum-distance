/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{11/4} ⊠ E_{13/5} ⊠ E_{13/5}) ≤ 12

Exhaustive layer search verifying that no 13-layer configuration with sizes
(1,1,1,1,1,1,1,1,1,1,1,1,1) and `s0 = (0,0)` exists in
E_{11/4} ⊠ E_{13/5}. This rules out α = 13 (the nested floor bound),
establishing α ≤ 12 for E_{11/4} ⊠ E_{13/5}².

This is needed for the disc proof of paper Theorem 6.9 case 11 — the
(11/4, 11/4, 11/4) discontinuity at α₃ = 13 — where the per-disc-point
candidate refinement leaves the multiset {(11,4), (13,5), (13,5)} as a
hard candidate.

## Slicing analysis

Slice by an E_{13/5} coordinate: 13 layers in E_{11/4} ⊠ E_{13/5}
(143 verts, α = 5). For each clique {i, …, i+4} of E_{13/5}, the union of
five adjacent layers is an IS in K₅ ⊠ E_{11/4} ⊠ E_{13/5}, with cardinality
bounded by α(E_{11/4} ⊠ E_{13/5}) = 5. 5-window sum ≤ 5.

Suppose total = 13. Sum of 13 cyclic 5-window sums = 5·13 = 65, max 13·5 = 65,
slack 0. As in bounds #7 and #8, every 5-window sums exactly to 5,
gcd(5,13)=1 forces all sizes equal, so each = 1.

Up to translation in `Z₁₁ × Z₁₃` (a symmetry of E_{11/4} ⊠ E_{13/5}), WLOG
the unique element of layer 0 is `(0, 0)`. This factors out 143 and makes
the `native_decide` search tractable.

## Reference

Direct analogue of `Section6UpperBoundsMixed114_114_135.lean` with the inner
graph E_{11/4} ⊠ E_{13/5} (143 verts) instead of E_{11/4}² (121 verts).

## Main result

- `caseMixed114_135_135_check_true`: the layer search returns `true`
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`. -/
private def distRawN114_135 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-! ## Layer search for E_{11/4} ⊠ E_{13/5} ⊠ E_{13/5}

Layer sizes: (1,1,1,1,1,1,1,1,1,1,1,1,1) over the 13 layers indexed by
the (outer) E_{13/5}. WLOG `s0 = (0, 0)` by `Z₁₁ × Z₁₃` translation. -/

/-- Cross-layer non-adjacency in E_{11/4} ⊠ E_{13/5}: returns `true` iff
    the pair `a, b` in `Fin 11 × Fin 13` is NOT adjacent in
    E_{11/4} ⊠ E_{13/5}. -/
def crossNonAdj114_135 (a b : Fin 11 × Fin 13) : Bool :=
  !((a.1 == b.1 || distRawN114_135 11 a.1 b.1 < 4) &&
    (a.2 == b.2 || distRawN114_135 13 a.2 b.2 < 5))

/-- All 143 vertices of E_{11/4} ⊠ E_{13/5}. -/
def verts114_135 : List (Fin 11 × Fin 13) :=
  (List.finRange 11).flatMap fun i => (List.finRange 13).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith114_135 (v : Fin 11 × Fin 13) (prev : List (Fin 11 × Fin 13)) :
    Bool :=
  prev.all fun w => crossNonAdj114_135 v w

/-- Mixed Baumert layer search for case 11 / bound #9: no valid 13-layer
    configuration with sizes (1,...,1) and `s0 = (0, 0)` exists in
    E_{11/4} ⊠ E_{13/5}. -/
def caseMixed114_135_135_check : Bool :=
  let vs := verts114_135
  let s0 : Fin 11 × Fin 13 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  !(vs.any fun s1 =>
    crossNonAdj114_135 s1 s0 &&
    vs.any fun s2 =>
      compatWith114_135 s2 [s0, s1] &&
    vs.any fun s3 =>
      compatWith114_135 s3 [s0, s1, s2] &&
    vs.any fun s4 =>
      compatWith114_135 s4 [s0, s1, s2, s3] &&
    vs.any fun s5 =>
      compatWith114_135 s5 [s1, s2, s3, s4] &&
    vs.any fun s6 =>
      compatWith114_135 s6 [s2, s3, s4, s5] &&
    vs.any fun s7 =>
      compatWith114_135 s7 [s3, s4, s5, s6] &&
    vs.any fun s8 =>
      compatWith114_135 s8 [s4, s5, s6, s7] &&
    vs.any fun s9 =>
      compatWith114_135 s9 [s5, s6, s7, s8, s0] &&
    vs.any fun s10 =>
      compatWith114_135 s10 [s6, s7, s8, s9, s0, s1] &&
    vs.any fun s11 =>
      compatWith114_135 s11 [s7, s8, s9, s10, s0, s1, s2] &&
    vs.any fun s12 =>
      compatWith114_135 s12 [s8, s9, s10, s11, s0, s1, s2, s3])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 128000000 in
-- WLOG `s0 = (0, 0)` cuts the outer loop by 143×, making the search tractable.
theorem caseMixed114_135_135_check_true : caseMixed114_135_135_check = true := by
  native_decide

/-- Every element of `Fin 11 × Fin 13` is in `verts114_135`. -/
theorem mem_verts114_135 (v : Fin 11 × Fin 13) : v ∈ verts114_135 := by
  simp only [verts114_135, List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
