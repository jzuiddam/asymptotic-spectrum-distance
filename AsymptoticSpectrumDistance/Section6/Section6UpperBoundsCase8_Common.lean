/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shared helpers for the chunked Case 8 Baumert check

The full layer search in `Section6UpperBoundsCase8.lean` runs a single
`native_decide` over an 8-layer combinatorial enumeration on `Fin 8 × Fin 8`
(64 vertices). The serial cost is ~26 min wall time.

To parallelise, the outer `v0` loop is split into chunks. Each chunk lives in
its own file, so Lake compiles them in parallel. This file holds the pieces
shared across chunks:

* `distRaw`, `crossNonAdj83`, `verts83`, `compatWith83`, `enc83`, `mem_verts83`
  — graph helpers, hoisted from `Section6UpperBoundsCase8.lean`.
* `innerSearch_v0_case8` — the per-`v0` inner search, extracted as a named
  function (defeq to the inline closure in the original `case8_check`).
* `vs_chunk1_case8` … `vs_chunk4_case8` — a 4-way partition of `verts83` via
  `List.take` / `List.drop` (16 elements per chunk).
* `chunks_partition_case8` — `vs_chunk1 ++ vs_chunk2 ++ vs_chunk3 ++ vs_chunk4
  = verts83`, provable by `decide`.
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`. -/
private def distRaw (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-- Cross-layer non-adjacency in E_{8/3}²: returns `true` iff the pair a, b is
    NOT adjacent in E_{8/3}². Does NOT shortcut on equal points: when a = b but
    they come from different layers (distance 1 or 2 in E_{8/3}), the
    corresponding 3D points in E_{8/3}³ ARE adjacent. -/
def crossNonAdj83 (a b : Fin 8 × Fin 8) : Bool :=
  !((a.1 == b.1 || distRaw 8 a.1 b.1 < 3) &&
    (a.2 == b.2 || distRaw 8 a.2 b.2 < 3))

/-- All 64 vertices of E_{8/3}². -/
def verts83 : List (Fin 8 × Fin 8) :=
  (List.finRange 8).flatMap fun i => (List.finRange 8).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith83 (v : Fin 8 × Fin 8) (prev : List (Fin 8 × Fin 8)) : Bool :=
  prev.all fun w => crossNonAdj83 v w

/-- Encode a pair for ordering (to break symmetry in size-2 layers). -/
def enc83 (v : Fin 8 × Fin 8) : ℕ := v.1.val * 8 + v.2.val

/-- The per-`v0` inner search, extracted from `case8_check`. Definitionally
    equal to the inner closure in the original definition, so the original
    `Bridge8o3_8o3_8o3` unfold-based contradiction is preserved. -/
def innerSearch_v0_case8 (v0 : Fin 8 × Fin 8) : Bool :=
  let vs := verts83
  vs.any fun v10 =>
    crossNonAdj83 v10 v0 &&
  vs.any fun v11 =>
    enc83 v10 < enc83 v11 && crossNonAdj83 v10 v11 &&
    crossNonAdj83 v11 v0 &&
  vs.any fun v2 =>
    !(v2 == v0) && !(v2 == v10) && !(v2 == v11) &&
    compatWith83 v2 [v0, v10, v11] &&
  vs.any fun v30 =>
    compatWith83 v30 [v10, v11, v2] &&
  vs.any fun v31 =>
    enc83 v30 < enc83 v31 && crossNonAdj83 v30 v31 &&
    compatWith83 v31 [v10, v11, v2] &&
  vs.any fun v40 =>
    compatWith83 v40 [v2, v30, v31] &&
  vs.any fun v41 =>
    enc83 v40 < enc83 v41 && crossNonAdj83 v40 v41 &&
    compatWith83 v41 [v2, v30, v31] &&
  vs.any fun v5 =>
    compatWith83 v5 [v30, v31, v40, v41] &&
  vs.any fun v60 =>
    compatWith83 v60 [v40, v41, v5, v0] &&
  vs.any fun v61 =>
    enc83 v60 < enc83 v61 && crossNonAdj83 v60 v61 &&
    compatWith83 v61 [v40, v41, v5, v0] &&
  vs.any fun v70 =>
    compatWith83 v70 [v5, v60, v61, v0, v10, v11] &&
  vs.any fun v71 =>
    enc83 v70 < enc83 v71 && crossNonAdj83 v70 v71 &&
    compatWith83 v71 [v5, v60, v61, v0, v10, v11]

/-! ## 4-way partition of the v0 search space (16 elements per chunk) -/

/-- First quarter of `verts83`. -/
def vs_chunk1_case8 : List (Fin 8 × Fin 8) := verts83.take 16
/-- Second quarter of `verts83`. -/
def vs_chunk2_case8 : List (Fin 8 × Fin 8) := (verts83.drop 16).take 16
/-- Third quarter of `verts83`. -/
def vs_chunk3_case8 : List (Fin 8 × Fin 8) := (verts83.drop 32).take 16
/-- Fourth quarter of `verts83`. -/
def vs_chunk4_case8 : List (Fin 8 × Fin 8) := verts83.drop 48

/-- The four chunks partition `verts83`. -/
theorem chunks_partition_case8 :
    vs_chunk1_case8 ++ vs_chunk2_case8 ++ vs_chunk3_case8 ++ vs_chunk4_case8
      = verts83 := by
  decide

/-- Every element of `Fin 8 × Fin 8` is in `verts83`. -/
theorem mem_verts83 (v : Fin 8 × Fin 8) : v ∈ verts83 := by
  simp only [verts83, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
