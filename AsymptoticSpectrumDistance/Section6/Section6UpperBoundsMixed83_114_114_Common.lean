/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shared helpers for the chunked Mixed83_114_114 Baumert check

Companion to `Section6UpperBoundsMixed52_114_114_Common.lean`; same chunking
strategy applied to the 8-layer α(E_{8/3} ⊠ E_{11/4}²) ≤ 12 search. The serial
`native_decide` for this file takes ~29 min wall; splitting the outer `v10`
loop into 8 chunks lets Lake compile them in parallel.

This file holds the shared pieces:

* `innerSearch_v10_114_114` — the per-`v10` inner search, extracted as a named
  function (defeq to the inline closure in the original
  `caseMixed83_114_114_check`).
* `vs_chunk{1,…,8}_83_114_114` — an 8-way partition of `verts114_114'` via
  `List.take` / `List.drop` (15 elements per chunk, with chunk 8 holding the
  trailing remainder).
* `chunks_partition_83_114_114` — `vs_chunk1 ++ … ++ vs_chunk8 = verts114_114'`,
  provable by `decide`.
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper (re-exported for chunk files) -/

/-- Circular distance mod n, computable on `Fin n`. -/
def distRawN83_114_114 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-- Cross-layer non-adjacency in E_{11/4}². -/
def crossNonAdj114_114' (a b : Fin 11 × Fin 11) : Bool :=
  !((a.1 == b.1 || distRawN83_114_114 11 a.1 b.1 < 4) &&
    (a.2 == b.2 || distRawN83_114_114 11 a.2 b.2 < 4))

/-- All 121 vertices of E_{11/4}². -/
def verts114_114' : List (Fin 11 × Fin 11) :=
  (List.finRange 11).flatMap fun i => (List.finRange 11).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith114_114' (v : Fin 11 × Fin 11) (prev : List (Fin 11 × Fin 11)) :
    Bool :=
  prev.all fun w => crossNonAdj114_114' v w

/-- Encode a pair for ordering. -/
def enc114_114' (v : Fin 11 × Fin 11) : ℕ := v.1.val * 11 + v.2.val

/-- The per-`v10` inner search, extracted from `caseMixed83_114_114_check`.
    Defeq to the inner closure in the original definition. -/
def innerSearch_v10_114_114 (v10 : Fin 11 × Fin 11) : Bool :=
  let vs := verts114_114'
  let v0 : Fin 11 × Fin 11 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  crossNonAdj114_114' v10 v0 &&
  vs.any fun v11 =>
    enc114_114' v10 < enc114_114' v11 && crossNonAdj114_114' v10 v11 &&
    crossNonAdj114_114' v11 v0 &&
  vs.any fun v2 =>
    compatWith114_114' v2 [v0, v10, v11] &&
  vs.any fun v30 =>
    compatWith114_114' v30 [v10, v11, v2] &&
  vs.any fun v31 =>
    enc114_114' v30 < enc114_114' v31 && crossNonAdj114_114' v30 v31 &&
    compatWith114_114' v31 [v10, v11, v2] &&
  vs.any fun v40 =>
    compatWith114_114' v40 [v2, v30, v31] &&
  vs.any fun v41 =>
    enc114_114' v40 < enc114_114' v41 && crossNonAdj114_114' v40 v41 &&
    compatWith114_114' v41 [v2, v30, v31] &&
  vs.any fun v5 =>
    compatWith114_114' v5 [v30, v31, v40, v41] &&
  vs.any fun v60 =>
    compatWith114_114' v60 [v40, v41, v5, v0] &&
  vs.any fun v61 =>
    enc114_114' v60 < enc114_114' v61 && crossNonAdj114_114' v60 v61 &&
    compatWith114_114' v61 [v40, v41, v5, v0] &&
  vs.any fun v70 =>
    compatWith114_114' v70 [v5, v60, v61, v0, v10, v11] &&
  vs.any fun v71 =>
    enc114_114' v70 < enc114_114' v71 && crossNonAdj114_114' v70 v71 &&
    compatWith114_114' v71 [v5, v60, v61, v0, v10, v11]

/-! ## 8-way partition of the v10 search space (15 elements per chunk) -/

/-- Chunk 1 of `verts114_114'`: first 15 elements. -/
def vs_chunk1_83_114_114 : List (Fin 11 × Fin 11) := verts114_114'.take 15
/-- Chunk 2 of `verts114_114'`. -/
def vs_chunk2_83_114_114 : List (Fin 11 × Fin 11) := (verts114_114'.drop 15).take 15
/-- Chunk 3 of `verts114_114'`. -/
def vs_chunk3_83_114_114 : List (Fin 11 × Fin 11) := (verts114_114'.drop 30).take 15
/-- Chunk 4 of `verts114_114'`. -/
def vs_chunk4_83_114_114 : List (Fin 11 × Fin 11) := (verts114_114'.drop 45).take 15
/-- Chunk 5 of `verts114_114'`. -/
def vs_chunk5_83_114_114 : List (Fin 11 × Fin 11) := (verts114_114'.drop 60).take 15
/-- Chunk 6 of `verts114_114'`. -/
def vs_chunk6_83_114_114 : List (Fin 11 × Fin 11) := (verts114_114'.drop 75).take 15
/-- Chunk 7 of `verts114_114'`. -/
def vs_chunk7_83_114_114 : List (Fin 11 × Fin 11) := (verts114_114'.drop 90).take 15
/-- Chunk 8 of `verts114_114'`: trailing remainder (16 elements, since 121 = 7·15 + 16). -/
def vs_chunk8_83_114_114 : List (Fin 11 × Fin 11) := verts114_114'.drop 105

/-- The eight chunks partition `verts114_114'`. -/
theorem chunks_partition_83_114_114 :
    vs_chunk1_83_114_114 ++ vs_chunk2_83_114_114 ++ vs_chunk3_83_114_114
        ++ vs_chunk4_83_114_114 ++ vs_chunk5_83_114_114 ++ vs_chunk6_83_114_114
        ++ vs_chunk7_83_114_114 ++ vs_chunk8_83_114_114 = verts114_114' := by
  decide

/-- Every element of `Fin 11 × Fin 11` is in `verts114_114'`. -/
theorem mem_verts114_114' (v : Fin 11 × Fin 11) : v ∈ verts114_114' := by
  simp only [verts114_114', List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
