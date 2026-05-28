/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shared helpers for the chunked Mixed114_114_135 Baumert check

Companion to `Section6UpperBoundsMixed83_114_114_Common.lean`; same chunking
strategy applied to the 13-layer α(E_{11/4}² ⊠ E_{13/5}) ≤ 12 search. The
serial `native_decide` for this file takes ~24 min wall; splitting the outer
`s1` loop into 4 chunks lets Lake compile them in parallel.

This file holds the shared pieces:

* `innerSearch_s1_114_114_135` — the per-`s1` inner search, extracted as a
  named function (defeq to the inline closure in the original
  `caseMixed114_114_135_check`).
* `vs_chunk{1,2,3,4}_114_114_135` — a 4-way partition of `verts114_114` via
  `List.take` / `List.drop` (30 / 30 / 30 / 31 elements).
* `chunks_partition_114_114_135` —
  `vs_chunk1 ++ vs_chunk2 ++ vs_chunk3 ++ vs_chunk4 = verts114_114`,
  provable by `decide`.
* `mem_verts114_114` — every element of `Fin 11 × Fin 11` is in `verts114_114`.
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper (re-exported for chunk files) -/

/-- Circular distance mod n, computable on `Fin n`. -/
def distRawN114_114 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-- Cross-layer non-adjacency in E_{11/4}²: returns `true` iff the pair
    `a, b` in `Fin 11 × Fin 11` is NOT adjacent in E_{11/4}². -/
def crossNonAdj114_114 (a b : Fin 11 × Fin 11) : Bool :=
  !((a.1 == b.1 || distRawN114_114 11 a.1 b.1 < 4) &&
    (a.2 == b.2 || distRawN114_114 11 a.2 b.2 < 4))

/-- All 121 vertices of E_{11/4}². -/
def verts114_114 : List (Fin 11 × Fin 11) :=
  (List.finRange 11).flatMap fun i => (List.finRange 11).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith114_114 (v : Fin 11 × Fin 11) (prev : List (Fin 11 × Fin 11)) :
    Bool :=
  prev.all fun w => crossNonAdj114_114 v w

/-- The per-`s1` inner search, extracted from `caseMixed114_114_135_check`.
    Defeq to the inner closure in the original definition. -/
def innerSearch_s1_114_114_135 (s1 : Fin 11 × Fin 11) : Bool :=
  let vs := verts114_114
  let s0 : Fin 11 × Fin 11 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  crossNonAdj114_114 s1 s0 &&
  vs.any fun s2 =>
    compatWith114_114 s2 [s0, s1] &&
  vs.any fun s3 =>
    compatWith114_114 s3 [s0, s1, s2] &&
  vs.any fun s4 =>
    compatWith114_114 s4 [s0, s1, s2, s3] &&
  vs.any fun s5 =>
    compatWith114_114 s5 [s1, s2, s3, s4] &&
  vs.any fun s6 =>
    compatWith114_114 s6 [s2, s3, s4, s5] &&
  vs.any fun s7 =>
    compatWith114_114 s7 [s3, s4, s5, s6] &&
  vs.any fun s8 =>
    compatWith114_114 s8 [s4, s5, s6, s7] &&
  vs.any fun s9 =>
    compatWith114_114 s9 [s5, s6, s7, s8, s0] &&
  vs.any fun s10 =>
    compatWith114_114 s10 [s6, s7, s8, s9, s0, s1] &&
  vs.any fun s11 =>
    compatWith114_114 s11 [s7, s8, s9, s10, s0, s1, s2] &&
  vs.any fun s12 =>
    compatWith114_114 s12 [s8, s9, s10, s11, s0, s1, s2, s3]

/-! ## 4-way partition of the s1 search space -/

/-- First quarter of `verts114_114`. -/
def vs_chunk1_114_114_135 : List (Fin 11 × Fin 11) := verts114_114.take 30
/-- Second quarter. -/
def vs_chunk2_114_114_135 : List (Fin 11 × Fin 11) := (verts114_114.drop 30).take 30
/-- Third quarter. -/
def vs_chunk3_114_114_135 : List (Fin 11 × Fin 11) := (verts114_114.drop 60).take 30
/-- Fourth quarter (trailing remainder, 31 elements). -/
def vs_chunk4_114_114_135 : List (Fin 11 × Fin 11) := verts114_114.drop 90

/-- The four chunks partition `verts114_114`. -/
theorem chunks_partition_114_114_135 :
    vs_chunk1_114_114_135 ++ vs_chunk2_114_114_135 ++ vs_chunk3_114_114_135
        ++ vs_chunk4_114_114_135 = verts114_114 := by
  decide

/-- Every element of `Fin 11 × Fin 11` is in `verts114_114`. -/
theorem mem_verts114_114 (v : Fin 11 × Fin 11) : v ∈ verts114_114 := by
  simp only [verts114_114, List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
