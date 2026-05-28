/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shared helpers for the chunked Mixed52_114_114 Baumert check

The full layer search in `Section6UpperBoundsMixed52_114_114.lean` runs a single
giant `native_decide` over a 5-layer combinatorial enumeration on `Fin 11 × Fin 11`
(121 vertices). The serial cost is ~60–90 minutes wall time.

To parallelise, the outer `s01` loop is split into chunks. Each chunk lives in
its own file, so Lake compiles them in parallel. This file holds the pieces
shared across chunks:

* `innerSearch_s01_114_114` — the per-`s01` inner search, extracted as a named
  function (defeq to the inline closure in the original
  `caseMixed52_114_114_check`).
* `vs_chunk1` … `vs_chunk8` — an 8-way partition of `verts114_114_v2` via
  `List.take` / `List.drop` (15 elements per chunk, with chunk 8 holding the
  trailing remainder).
* `chunks_partition` — `vs_chunk1 ++ … ++ vs_chunk8 = verts114_114_v2`,
  provable by `decide`.
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper (re-exported for chunk files) -/

/-- Circular distance mod n, computable on `Fin n`. -/
def distRawMix52_114_114 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-- Cross-layer non-adjacency in E_{11/4} ⊠ E_{11/4}: returns `true` iff the
    pair `a, b` in `Fin 11 × Fin 11` is NOT adjacent in E_{11/4} ⊠ E_{11/4}. -/
def crossNonAdj114_114_v2 (a b : Fin 11 × Fin 11) : Bool :=
  !((a.1 == b.1 || distRawMix52_114_114 11 a.1 b.1 < 4) &&
    (a.2 == b.2 || distRawMix52_114_114 11 a.2 b.2 < 4))

/-- All 121 vertices of E_{11/4} ⊠ E_{11/4}. -/
def verts114_114_v2 : List (Fin 11 × Fin 11) :=
  (List.finRange 11).flatMap fun i => (List.finRange 11).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith114_114_v2 (v : Fin 11 × Fin 11) (prev : List (Fin 11 × Fin 11)) :
    Bool :=
  prev.all fun w => crossNonAdj114_114_v2 v w

/-- Encode a pair for ordering (to break symmetry within a layer). -/
def enc114_114_v2 (v : Fin 11 × Fin 11) : ℕ := v.1.val * 11 + v.2.val

/-- The per-`s01` inner search, extracted from `caseMixed52_114_114_check`.
    Definitionally equal to the inner closure in the original definition,
    so the original proof structure (and the `Bridge52_114_114` unfold-based
    contradiction) is preserved. -/
def innerSearch_s01_114_114 (s01 : Fin 11 × Fin 11) : Bool :=
  let vs := verts114_114_v2
  let s00 : Fin 11 × Fin 11 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  enc114_114_v2 s00 < enc114_114_v2 s01 && crossNonAdj114_114_v2 s00 s01 &&
  vs.any fun s10 =>
    compatWith114_114_v2 s10 [s00, s01] &&
  vs.any fun s11 =>
    enc114_114_v2 s10 < enc114_114_v2 s11 && crossNonAdj114_114_v2 s10 s11 &&
    compatWith114_114_v2 s11 [s00, s01] &&
  vs.any fun s20 =>
    compatWith114_114_v2 s20 [s10, s11] &&
  vs.any fun s21 =>
    enc114_114_v2 s20 < enc114_114_v2 s21 && crossNonAdj114_114_v2 s20 s21 &&
    compatWith114_114_v2 s21 [s10, s11] &&
  vs.any fun s22 =>
    enc114_114_v2 s21 < enc114_114_v2 s22 &&
    crossNonAdj114_114_v2 s20 s22 &&
    crossNonAdj114_114_v2 s21 s22 &&
    compatWith114_114_v2 s22 [s10, s11] &&
  vs.any fun s30 =>
    compatWith114_114_v2 s30 [s20, s21, s22] &&
  vs.any fun s31 =>
    enc114_114_v2 s30 < enc114_114_v2 s31 && crossNonAdj114_114_v2 s30 s31 &&
    compatWith114_114_v2 s31 [s20, s21, s22] &&
  vs.any fun s40 =>
    compatWith114_114_v2 s40 [s30, s31, s00, s01] &&
  vs.any fun s41 =>
    enc114_114_v2 s40 < enc114_114_v2 s41 && crossNonAdj114_114_v2 s40 s41 &&
    compatWith114_114_v2 s41 [s30, s31, s00, s01] &&
  vs.any fun s42 =>
    enc114_114_v2 s41 < enc114_114_v2 s42 &&
    crossNonAdj114_114_v2 s40 s42 &&
    crossNonAdj114_114_v2 s41 s42 &&
    compatWith114_114_v2 s42 [s30, s31, s00, s01]

/-! ## 8-way partition of the s01 search space (15 elements per chunk) -/

/-- Chunk 1 of `verts114_114_v2`: first 15 elements. -/
def vs_chunk1_114_114 : List (Fin 11 × Fin 11) :=
  verts114_114_v2.take 15

/-- Chunk 2 of `verts114_114_v2`. -/
def vs_chunk2_114_114 : List (Fin 11 × Fin 11) :=
  (verts114_114_v2.drop 15).take 15

/-- Chunk 3 of `verts114_114_v2`. -/
def vs_chunk3_114_114 : List (Fin 11 × Fin 11) :=
  (verts114_114_v2.drop 30).take 15

/-- Chunk 4 of `verts114_114_v2`. -/
def vs_chunk4_114_114 : List (Fin 11 × Fin 11) :=
  (verts114_114_v2.drop 45).take 15

/-- Chunk 5 of `verts114_114_v2`. -/
def vs_chunk5_114_114 : List (Fin 11 × Fin 11) :=
  (verts114_114_v2.drop 60).take 15

/-- Chunk 6 of `verts114_114_v2`. -/
def vs_chunk6_114_114 : List (Fin 11 × Fin 11) :=
  (verts114_114_v2.drop 75).take 15

/-- Chunk 7 of `verts114_114_v2`. -/
def vs_chunk7_114_114 : List (Fin 11 × Fin 11) :=
  (verts114_114_v2.drop 90).take 15

/-- Chunk 8 of `verts114_114_v2`: trailing remainder (16 elements, since 121 = 7·15 + 16). -/
def vs_chunk8_114_114 : List (Fin 11 × Fin 11) :=
  verts114_114_v2.drop 105

/-- The eight chunks partition `verts114_114_v2`. -/
theorem chunks_partition_114_114 :
    vs_chunk1_114_114 ++ vs_chunk2_114_114 ++ vs_chunk3_114_114 ++ vs_chunk4_114_114
      ++ vs_chunk5_114_114 ++ vs_chunk6_114_114 ++ vs_chunk7_114_114
      ++ vs_chunk8_114_114 = verts114_114_v2 := by
  decide

/-- Every element of `Fin 11 × Fin 11` is in `verts114_114_v2`. -/
theorem mem_verts114_114_v2 (v : Fin 11 × Fin 11) : v ∈ verts114_114_v2 := by
  simp only [verts114_114_v2, List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
