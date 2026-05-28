/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shared helpers for the chunked Mixed52_83_114 Baumert check

The full layer search in `Section6UpperBoundsMixed52_83_114.lean` runs a single
`native_decide` over a 5-layer combinatorial enumeration on `Fin 8 × Fin 11`
(88 vertices). The serial cost is ~21 min wall time.

To parallelise, the outer `s01` loop is split into chunks. Each chunk lives in
its own file, so Lake compiles them in parallel. This file holds the pieces
shared across chunks:

* `distRawMix52_83_114`, `crossNonAdj83_114_v2`, `verts83_114_v2`,
  `compatWith83_114_v2`, `enc83_114_v2`, `mem_verts83_114_v2`
  — graph helpers, hoisted from the original `Section6UpperBoundsMixed52_83_114.lean`.
* `innerSearch_s01_83_114` — the per-`s01` inner search, extracted as a named
  function (defeq to the inline closure in the original
  `caseMixed52_83_114_check`).
* `vs_chunk1_83_114` … `vs_chunk4_83_114` — a 4-way partition of
  `verts83_114_v2` via `List.take` / `List.drop` (22 elements per chunk).
* `chunks_partition_83_114` — `vs_chunk1 ++ vs_chunk2 ++ vs_chunk3 ++ vs_chunk4
  = verts83_114_v2`, provable by `decide`.
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`. -/
private def distRawMix52_83_114 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-- Cross-layer non-adjacency in E_{8/3} ⊠ E_{11/4}: returns `true` iff the
    pair `a, b` in `Fin 8 × Fin 11` is NOT adjacent in E_{8/3} ⊠ E_{11/4}.
    Does not shortcut on equality (different layers' equal points are 3-D
    adjacent). -/
def crossNonAdj83_114_v2 (a b : Fin 8 × Fin 11) : Bool :=
  !((a.1 == b.1 || distRawMix52_83_114 8 a.1 b.1 < 3) &&
    (a.2 == b.2 || distRawMix52_83_114 11 a.2 b.2 < 4))

/-- All 88 vertices of E_{8/3} ⊠ E_{11/4}. -/
def verts83_114_v2 : List (Fin 8 × Fin 11) :=
  (List.finRange 8).flatMap fun i => (List.finRange 11).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith83_114_v2 (v : Fin 8 × Fin 11) (prev : List (Fin 8 × Fin 11)) : Bool :=
  prev.all fun w => crossNonAdj83_114_v2 v w

/-- Encode a pair for ordering (to break symmetry within a layer). -/
def enc83_114_v2 (v : Fin 8 × Fin 11) : ℕ := v.1.val * 11 + v.2.val

/-- The per-`s01` inner search, extracted from `caseMixed52_83_114_check`.
    Definitionally equal to the inner closure in the original definition,
    so the original proof structure (and the `Bridge52_83_114` unfold-based
    contradiction) is preserved. -/
def innerSearch_s01_83_114 (s01 : Fin 8 × Fin 11) : Bool :=
  let vs := verts83_114_v2
  let s00 : Fin 8 × Fin 11 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  enc83_114_v2 s00 < enc83_114_v2 s01 && crossNonAdj83_114_v2 s00 s01 &&
  vs.any fun s10 =>
    compatWith83_114_v2 s10 [s00, s01] &&
  vs.any fun s11 =>
    enc83_114_v2 s10 < enc83_114_v2 s11 && crossNonAdj83_114_v2 s10 s11 &&
    compatWith83_114_v2 s11 [s00, s01] &&
  vs.any fun s20 =>
    compatWith83_114_v2 s20 [s10, s11] &&
  vs.any fun s21 =>
    enc83_114_v2 s20 < enc83_114_v2 s21 && crossNonAdj83_114_v2 s20 s21 &&
    compatWith83_114_v2 s21 [s10, s11] &&
  vs.any fun s22 =>
    enc83_114_v2 s21 < enc83_114_v2 s22 &&
    crossNonAdj83_114_v2 s20 s22 &&
    crossNonAdj83_114_v2 s21 s22 &&
    compatWith83_114_v2 s22 [s10, s11] &&
  vs.any fun s30 =>
    compatWith83_114_v2 s30 [s20, s21, s22] &&
  vs.any fun s31 =>
    enc83_114_v2 s30 < enc83_114_v2 s31 && crossNonAdj83_114_v2 s30 s31 &&
    compatWith83_114_v2 s31 [s20, s21, s22] &&
  vs.any fun s40 =>
    compatWith83_114_v2 s40 [s30, s31, s00, s01] &&
  vs.any fun s41 =>
    enc83_114_v2 s40 < enc83_114_v2 s41 && crossNonAdj83_114_v2 s40 s41 &&
    compatWith83_114_v2 s41 [s30, s31, s00, s01] &&
  vs.any fun s42 =>
    enc83_114_v2 s41 < enc83_114_v2 s42 &&
    crossNonAdj83_114_v2 s40 s42 &&
    crossNonAdj83_114_v2 s41 s42 &&
    compatWith83_114_v2 s42 [s30, s31, s00, s01]

/-! ## 4-way partition of the s01 search space (22 elements per chunk) -/

/-- First quarter of `verts83_114_v2`. -/
def vs_chunk1_83_114 : List (Fin 8 × Fin 11) := verts83_114_v2.take 22
/-- Second quarter. -/
def vs_chunk2_83_114 : List (Fin 8 × Fin 11) := (verts83_114_v2.drop 22).take 22
/-- Third quarter. -/
def vs_chunk3_83_114 : List (Fin 8 × Fin 11) := (verts83_114_v2.drop 44).take 22
/-- Fourth quarter. -/
def vs_chunk4_83_114 : List (Fin 8 × Fin 11) := verts83_114_v2.drop 66

/-- The four chunks partition `verts83_114_v2`. -/
theorem chunks_partition_83_114 :
    vs_chunk1_83_114 ++ vs_chunk2_83_114 ++ vs_chunk3_83_114 ++ vs_chunk4_83_114
      = verts83_114_v2 := by
  decide

/-- Every element of `Fin 8 × Fin 11` is in `verts83_114_v2`. -/
theorem mem_verts83_114_v2 (v : Fin 8 × Fin 11) : v ∈ verts83_114_v2 := by
  simp only [verts83_114_v2, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
