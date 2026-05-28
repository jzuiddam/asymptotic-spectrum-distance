/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{5/2} ⊠ E_{5/2} ⊠ E_{11/4}) ≤ 11

Exhaustive layer search verifying that no 5-layer configuration with sizes
(2, 2, 3, 2, 3) and `s00 = (0, 0)` exists in E_{5/2} ⊠ E_{11/4}. This rules
out α = 12 (the nested floor bound), establishing α ≤ 11 for
E_{5/2} ⊠ E_{5/2} ⊠ E_{11/4}.

## Slicing analysis

Slice by the first E_{5/2} coordinate: 5 layers in E_{5/2} ⊠ E_{11/4}
(55 verts each, α = 5). For each edge {i, i+1} of E_{5/2}, the union of two
adjacent layers is an IS in K₂ ⊠ E_{5/2} ⊠ E_{11/4}, which has α =
α(E_{5/2} ⊠ E_{11/4}) = 5. Adjacent pair sum ≤ 5.

Suppose total = 12. Sum of 5 cyclic edge-pair sums = 2·12 = 24, max 5·5 = 25,
slack 1. Up to rotation, sizes are forced to (2, 2, 3, 2, 3).

Up to translation in `Z₅ × Z₁₁` (a symmetry of E_{5/2} ⊠ E_{11/4}), WLOG the
first element of layer 0 is `(0, 0)`. This factors out 55 and makes the
`native_decide` search tractable.

## Reference

Direct analogue of `Section6UpperBoundsMixed52_83_83.lean`'s
`caseMixed_check`, with the inner graph swapped from E_{8/3}² (64 verts) to
E_{5/2} ⊠ E_{11/4} (55 verts) and the translation symmetry adjusted to
Z₅ × Z₁₁.

## Main result

- `caseMixed52_52_114_check_true`: the layer search returns `true`
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`.
Agrees with `distMod n` on `ZMod n` when `ZMod n = Fin n`. -/
private def distRawMix52_52_114 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-! ## Layer search for E_{5/2} ⊠ (E_{5/2} ⊠ E_{11/4})

Layer sizes: (2, 2, 3, 2, 3) over the 5 layers indexed by the outer E_{5/2}.
WLOG `s00 = (0, 0)` by `Z₅ × Z₁₁` translation. -/

/-- Cross-layer non-adjacency in E_{5/2} ⊠ E_{11/4}: returns `true` iff the
    pair `a, b` in `Fin 5 × Fin 11` is NOT adjacent in E_{5/2} ⊠ E_{11/4}.
    Does not shortcut on equality (different layers' equal points are 3-D
    adjacent). -/
def crossNonAdj52_114 (a b : Fin 5 × Fin 11) : Bool :=
  !((a.1 == b.1 || distRawMix52_52_114 5 a.1 b.1 < 2) &&
    (a.2 == b.2 || distRawMix52_52_114 11 a.2 b.2 < 4))

/-- All 55 vertices of E_{5/2} ⊠ E_{11/4}. -/
def verts52_114 : List (Fin 5 × Fin 11) :=
  (List.finRange 5).flatMap fun i => (List.finRange 11).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith52_114 (v : Fin 5 × Fin 11) (prev : List (Fin 5 × Fin 11)) : Bool :=
  prev.all fun w => crossNonAdj52_114 v w

/-- Encode a pair for ordering (to break symmetry within a layer). -/
def enc52_114 (v : Fin 5 × Fin 11) : ℕ := v.1.val * 11 + v.2.val

/-- Mixed Baumert layer search: no valid 5-layer configuration with sizes
    (2, 2, 3, 2, 3) and `s00 = (0, 0)` exists in E_{5/2} ⊠ E_{11/4}.

    Layer 0 (size 2): s00 = (0,0), s01
    Layer 1 (size 2): s10, s11
    Layer 2 (size 3): s20, s21, s22
    Layer 3 (size 2): s30, s31
    Layer 4 (size 3): s40, s41, s42

    Cross-layer adjacency in C₅: {0,1}, {1,2}, {2,3}, {3,4}, {4,0}. -/
def caseMixed52_52_114_check : Bool :=
  let vs := verts52_114
  let s00 : Fin 5 × Fin 11 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  !(vs.any fun s01 =>
    enc52_114 s00 < enc52_114 s01 && crossNonAdj52_114 s00 s01 &&
    vs.any fun s10 =>
      compatWith52_114 s10 [s00, s01] &&
    vs.any fun s11 =>
      enc52_114 s10 < enc52_114 s11 && crossNonAdj52_114 s10 s11 &&
      compatWith52_114 s11 [s00, s01] &&
    vs.any fun s20 =>
      compatWith52_114 s20 [s10, s11] &&
    vs.any fun s21 =>
      enc52_114 s20 < enc52_114 s21 && crossNonAdj52_114 s20 s21 &&
      compatWith52_114 s21 [s10, s11] &&
    vs.any fun s22 =>
      enc52_114 s21 < enc52_114 s22 &&
      crossNonAdj52_114 s20 s22 &&
      crossNonAdj52_114 s21 s22 &&
      compatWith52_114 s22 [s10, s11] &&
    vs.any fun s30 =>
      compatWith52_114 s30 [s20, s21, s22] &&
    vs.any fun s31 =>
      enc52_114 s30 < enc52_114 s31 && crossNonAdj52_114 s30 s31 &&
      compatWith52_114 s31 [s20, s21, s22] &&
    vs.any fun s40 =>
      compatWith52_114 s40 [s30, s31, s00, s01] &&
    vs.any fun s41 =>
      enc52_114 s40 < enc52_114 s41 && crossNonAdj52_114 s40 s41 &&
      compatWith52_114 s41 [s30, s31, s00, s01] &&
    vs.any fun s42 =>
      enc52_114 s41 < enc52_114 s42 &&
      crossNonAdj52_114 s40 s42 &&
      crossNonAdj52_114 s41 s42 &&
      compatWith52_114 s42 [s30, s31, s00, s01])

set_option maxRecDepth 2048 in
set_option maxHeartbeats 16000000 in
-- WLOG `s00 = (0, 0)` cuts the outer loop by 55×, bringing the cost back to
-- the order of the 5o2_8o3_8o3 mixed check.
theorem caseMixed52_52_114_check_true : caseMixed52_52_114_check = true := by native_decide

/-- Every element of `Fin 5 × Fin 11` is in `verts52_114`. -/
theorem mem_verts52_114 (v : Fin 5 × Fin 11) : v ∈ verts52_114 := by
  simp only [verts52_114, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
