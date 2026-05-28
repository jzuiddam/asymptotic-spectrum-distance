/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Mixed-multiset Computational Check: α(E_{5/2} ⊠ E_{8/3} ⊠ E_{8/3}) ≤ 11

Exhaustive layer search verifying that no 5-layer configuration with sizes
(2, 2, 3, 2, 3) and `s00 = (0,0)` exists in E_{8/3}². This rules out α = 12
(the nested floor bound), establishing α ≤ 11 for E_{5/2} ⊠ E_{8/3}².

This is needed for the disc proof of paper Theorem 6.9 case 8 — the
(8/3, 8/3, 8/3) discontinuity point — where the per-disc-point candidate
refinement leaves the multiset {(5,2), (8,3), (8,3)} as a hard candidate.

## Slicing analysis

Slice by the E_{5/2} coordinate: 5 layers in E_{8/3}² (64 verts each, α = 5).
For each edge {i, i+1} of E_{5/2}, the union of two adjacent layers is an IS
in K₂ ⊠ E_{8/3}², which has α = α(E_{8/3}²) = 5. Adjacent pair sum ≤ 5.

Suppose total = 12. Sum of 5 cyclic edge-pair sums = 2·12 = 24, max 5·5 = 25,
slack 1. Up to rotation, sizes are forced to (2, 2, 3, 2, 3).

Up to translation in `Z₈ × Z₈` (a symmetry of E_{8/3}²), WLOG the first
element of layer 0 is `(0, 0)`. This factors out 64 and makes the
`native_decide` search tractable.

## Reference

Direct analogue of `Section6UpperBoundsCase7.lean`'s `case7_direct_check`,
with the inner graph swapped from E_{5/2} ⊠ E_{8/3} (40 verts) to E_{8/3}²
(64 verts) and the translation symmetry fixed to bring `s00` to `(0, 0)`.

## Main result

- `caseMixed_check_true`: the layer search returns `true`
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`.
Agrees with `distMod n` on `ZMod n` when `ZMod n = Fin n`. -/
private def distRawM (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-! ## Layer search for E_{5/2} ⊠ E_{8/3}²

Layer sizes: (2, 2, 3, 2, 3) over the 5 layers indexed by E_{5/2}.
WLOG `s00 = (0, 0)` by `Z₈ × Z₈` translation. -/

/-- Cross-layer non-adjacency in E_{8/3}²: returns `true` iff the pair `a, b`
    in `Fin 8 × Fin 8` is NOT adjacent in E_{8/3}². Does not shortcut on
    equality (different layers' equal points are 3-D adjacent). -/
def crossNonAdj83sq (a b : Fin 8 × Fin 8) : Bool :=
  !((a.1 == b.1 || distRawM 8 a.1 b.1 < 3) &&
    (a.2 == b.2 || distRawM 8 a.2 b.2 < 3))

/-- All 64 vertices of E_{8/3}². -/
def verts83sq : List (Fin 8 × Fin 8) :=
  (List.finRange 8).flatMap fun i => (List.finRange 8).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith83sq (v : Fin 8 × Fin 8) (prev : List (Fin 8 × Fin 8)) : Bool :=
  prev.all fun w => crossNonAdj83sq v w

/-- Encode a pair for ordering (to break symmetry within a layer). -/
def enc83sq (v : Fin 8 × Fin 8) : ℕ := v.1.val * 8 + v.2.val

/-- Mixed Baumert layer search: no valid 5-layer configuration with sizes
    (2, 2, 3, 2, 3) and `s00 = (0, 0)` exists in E_{8/3}².

    Layer 0 (size 2): s00 = (0,0), s01
    Layer 1 (size 2): s10, s11
    Layer 2 (size 3): s20, s21, s22
    Layer 3 (size 2): s30, s31
    Layer 4 (size 3): s40, s41, s42

    Cross-layer adjacency in C₅: {0,1}, {1,2}, {2,3}, {3,4}, {4,0}. -/
def caseMixed_check : Bool :=
  let vs := verts83sq
  let s00 : Fin 8 × Fin 8 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  !(vs.any fun s01 =>
    enc83sq s00 < enc83sq s01 && crossNonAdj83sq s00 s01 &&
    vs.any fun s10 =>
      compatWith83sq s10 [s00, s01] &&
    vs.any fun s11 =>
      enc83sq s10 < enc83sq s11 && crossNonAdj83sq s10 s11 &&
      compatWith83sq s11 [s00, s01] &&
    vs.any fun s20 =>
      compatWith83sq s20 [s10, s11] &&
    vs.any fun s21 =>
      enc83sq s20 < enc83sq s21 && crossNonAdj83sq s20 s21 &&
      compatWith83sq s21 [s10, s11] &&
    vs.any fun s22 =>
      enc83sq s21 < enc83sq s22 &&
      crossNonAdj83sq s20 s22 &&
      crossNonAdj83sq s21 s22 &&
      compatWith83sq s22 [s10, s11] &&
    vs.any fun s30 =>
      compatWith83sq s30 [s20, s21, s22] &&
    vs.any fun s31 =>
      enc83sq s30 < enc83sq s31 && crossNonAdj83sq s30 s31 &&
      compatWith83sq s31 [s20, s21, s22] &&
    vs.any fun s40 =>
      compatWith83sq s40 [s30, s31, s00, s01] &&
    vs.any fun s41 =>
      enc83sq s40 < enc83sq s41 && crossNonAdj83sq s40 s41 &&
      compatWith83sq s41 [s30, s31, s00, s01] &&
    vs.any fun s42 =>
      enc83sq s41 < enc83sq s42 &&
      crossNonAdj83sq s40 s42 &&
      crossNonAdj83sq s41 s42 &&
      compatWith83sq s42 [s30, s31, s00, s01])

set_option maxRecDepth 2048 in
set_option maxHeartbeats 16000000 in
-- WLOG `s00 = (0, 0)` cuts the outer loop by 64×, bringing the cost back to
-- the order of case 7's direct check (40 verts × 12 positions, ~30s).
theorem caseMixed_check_true : caseMixed_check = true := by native_decide

/-- Every element of `Fin 8 × Fin 8` is in `verts83sq`. -/
theorem mem_verts83sq (v : Fin 8 × Fin 8) : v ∈ verts83sq := by
  simp only [verts83sq, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
