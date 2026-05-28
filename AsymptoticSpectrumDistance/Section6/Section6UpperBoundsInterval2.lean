/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Baumert Computational Check: α(C₅³) ≠ 11

Exhaustive layer-assignment search over all 7 size vector classes for C₅³,
verifying that no valid 5-layer configuration with total size 11 exists.
This rules out α = 11 (combined with monotonicity gives α ≤ 10).

This is the direct analogue of [BMRRS, Theorem 4]: α(C₅³) ≠ 11, 12.

[BMRRS] L. D. Baumert, R. J. McEliece, E. Rodemich, H. C. Rumsey, R. Stanley,
        H. Taylor, "A Combinatorial Packing Problem", 1971.

See `Section6UpperBounds.lean` for the full method description and how this
computational check fits into the overall proof.

## Main result

- `case52_check_true`: the case C₅² Baumert search returns `true`
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper

`distRaw` computes the same value as `distMod` but operates on `Fin n` rather than
`ZMod n`, making it computable for `native_decide`. For concrete small `n`,
`ZMod n = Fin n` definitionally, so `distRaw` and `distMod` agree on all pairs. -/

/-- Circular distance mod n, computable on `Fin n`.
Agrees with `distMod n` on `ZMod n` when `ZMod n = Fin n` (i.e., for concrete n). -/
def distRaw (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-! ## C₅² Case: α(E_{5/2}² ⊠ E_{5/2}²) ≤ 10

**Context**: Monotonicity gives α(C₅³) ≤ 11 (from α(C₅²) = 5 via nested floor).
We rule out α = 11 by exhaustive layer-assignment search.

**Graph**: C₅³ has 125 vertices (Fin 5 × Fin 5 × Fin 5).
Slicing by the first C₅ coordinate gives 5 layers in C₅².
Since α(C₅²) = 5 (from direct computation), each adjacent pair of layers
contributes ≤ 5 to the total. With 5 edges in C₅ and total 11, we have
2·11 = 22 ≤ 5·5 = 25 with slack 3. This forces 7 possible size vector
classes (up to rotation by Z₅ action):

1. (4,1,1,4,1) - two opposite size-4 layers
2. (4,1,2,3,1) - mixed sizes with pair constraint
3. (4,1,3,2,1) - variant of (2) under rotation
4. (3,2,3,2,1) - alternating pattern
5. (3,2,3,1,2) - different alternation
6. (3,1,3,2,2) - third pattern
7. (3,2,2,2,2) - uniform-ish sizes

**Vertex representation**: Each vertex of C₅² is (Fin 5 × Fin 5).
Adjacency in C₅: distRaw(5, i, j) < 2 means |i - j| ≡ 1 (mod 5).

**Layer adjacency**: Layers i, j of C₅³ are adjacent iff distRaw(5, i, j) < 2.
Layer i and i+1 are adjacent for each i.

**Fiber bound**: For each edge {i, i+1} in C₅, we have |Sᵢ| + |Sᵢ₊₁| ≤ 5. -/

/-- All 25 vertices of C₅². -/
def verts52 : List (Fin 5 × Fin 5) :=
  (List.finRange 5).flatMap fun i => (List.finRange 5).map fun j => (i, j)

/-- Cross-layer non-adjacency in C₅²: returns `true` iff (a₁, a₂) and (b₁, b₂)
    are NOT adjacent in C₅². Adjacency means both coordinates have distance < 2. -/
def crossNonAdj52 (a b : Fin 5 × Fin 5) : Bool :=
  !((distRaw 5 a.1 b.1 < 2) && (distRaw 5 a.2 b.2 < 2))

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith52 (v : Fin 5 × Fin 5) (prev : List (Fin 5 × Fin 5)) : Bool :=
  prev.all fun w => crossNonAdj52 v w

/-- Encode a pair for ordering (to break symmetry in size≥2 layers). -/
def enc52 (v : Fin 5 × Fin 5) : ℕ := v.1.val * 5 + v.2.val

/-! ## Case 1: Size vector (4,1,1,4,1)

Layer sizes: 0→4, 1→1, 2→1, 3→4, 4→1
Pair constraints: |S₀|+|S₁|=5, |S₁|+|S₂|=2, |S₂|+|S₃|=5, |S₃|+|S₄|=5, |S₄|+|S₀|=5
-/

def case52_check1 : Bool :=
  let vs := verts52
  !(vs.any fun v00 =>
    vs.any fun v01 =>
      enc52 v00 < enc52 v01 && crossNonAdj52 v00 v01 &&
    vs.any fun v02 =>
      enc52 v01 < enc52 v02 && crossNonAdj52 v00 v02 && crossNonAdj52 v01 v02 &&
    vs.any fun v03 =>
      enc52 v02 < enc52 v03 && crossNonAdj52 v00 v03 &&
      crossNonAdj52 v01 v03 && crossNonAdj52 v02 v03 &&
    vs.any fun v1 =>
      compatWith52 v1 [v00, v01, v02, v03] &&
    vs.any fun v2 =>
      compatWith52 v2 [v1] &&
    vs.any fun v30 =>
      compatWith52 v30 [v2] &&
    vs.any fun v31 =>
      enc52 v30 < enc52 v31 && crossNonAdj52 v30 v31 &&
      compatWith52 v31 [v2] &&
    vs.any fun v32 =>
      enc52 v31 < enc52 v32 && crossNonAdj52 v30 v32 && crossNonAdj52 v31 v32 &&
      compatWith52 v32 [v2] &&
    vs.any fun v33 =>
      enc52 v32 < enc52 v33 && crossNonAdj52 v30 v33 &&
      crossNonAdj52 v31 v33 && crossNonAdj52 v32 v33 &&
      compatWith52 v33 [v2] &&
    vs.any fun v4 =>
      compatWith52 v4 [v30, v31, v32, v33, v00, v01, v02, v03])

/-! ## Case 2: Size vector (4,1,2,3,1)

Layer sizes: 0→4, 1→1, 2→2, 3→3, 4→1
Pair constraints: |S₀|+|S₁|=5, |S₁|+|S₂|=3, |S₂|+|S₃|=5, |S₃|+|S₄|=4, |S₄|+|S₀|=5
-/

def case52_check2 : Bool :=
  let vs := verts52
  !(vs.any fun v00 =>
    vs.any fun v01 =>
      enc52 v00 < enc52 v01 && crossNonAdj52 v00 v01 &&
    vs.any fun v02 =>
      enc52 v01 < enc52 v02 && crossNonAdj52 v00 v02 && crossNonAdj52 v01 v02 &&
    vs.any fun v03 =>
      enc52 v02 < enc52 v03 && crossNonAdj52 v00 v03 &&
      crossNonAdj52 v01 v03 && crossNonAdj52 v02 v03 &&
    vs.any fun v1 =>
      compatWith52 v1 [v00, v01, v02, v03] &&
    vs.any fun v20 =>
      compatWith52 v20 [v1] &&
    vs.any fun v21 =>
      enc52 v20 < enc52 v21 && crossNonAdj52 v20 v21 &&
      compatWith52 v21 [v1] &&
    vs.any fun v30 =>
      compatWith52 v30 [v20, v21] &&
    vs.any fun v31 =>
      enc52 v30 < enc52 v31 && crossNonAdj52 v30 v31 &&
      compatWith52 v31 [v20, v21] &&
    vs.any fun v32 =>
      enc52 v31 < enc52 v32 && crossNonAdj52 v30 v32 && crossNonAdj52 v31 v32 &&
      compatWith52 v32 [v20, v21] &&
    vs.any fun v4 =>
      compatWith52 v4 [v30, v31, v32, v00, v01, v02, v03])

/-! ## Case 3: Size vector (4,1,3,2,1)

Layer sizes: 0→4, 1→1, 2→3, 3→2, 4→1
Pair constraints: |S₀|+|S₁|=5, |S₁|+|S₂|=4, |S₂|+|S₃|=5, |S₃|+|S₄|=3, |S₄|+|S₀|=5
-/

def case52_check3 : Bool :=
  let vs := verts52
  !(vs.any fun v00 =>
    vs.any fun v01 =>
      enc52 v00 < enc52 v01 && crossNonAdj52 v00 v01 &&
    vs.any fun v02 =>
      enc52 v01 < enc52 v02 && crossNonAdj52 v00 v02 && crossNonAdj52 v01 v02 &&
    vs.any fun v03 =>
      enc52 v02 < enc52 v03 && crossNonAdj52 v00 v03 &&
      crossNonAdj52 v01 v03 && crossNonAdj52 v02 v03 &&
    vs.any fun v1 =>
      compatWith52 v1 [v00, v01, v02, v03] &&
    vs.any fun v20 =>
      compatWith52 v20 [v1] &&
    vs.any fun v21 =>
      enc52 v20 < enc52 v21 && crossNonAdj52 v20 v21 &&
      compatWith52 v21 [v1] &&
    vs.any fun v22 =>
      enc52 v21 < enc52 v22 && crossNonAdj52 v20 v22 && crossNonAdj52 v21 v22 &&
      compatWith52 v22 [v1] &&
    vs.any fun v30 =>
      compatWith52 v30 [v20, v21, v22] &&
    vs.any fun v31 =>
      enc52 v30 < enc52 v31 && crossNonAdj52 v30 v31 &&
      compatWith52 v31 [v20, v21, v22] &&
    vs.any fun v4 =>
      compatWith52 v4 [v30, v31, v00, v01, v02, v03])

/-! ## Case 4: Size vector (3,2,3,2,1)

Layer sizes: 0→3, 1→2, 2→3, 3→2, 4→1
Pair constraints: |S₀|+|S₁|=5, |S₁|+|S₂|=5, |S₂|+|S₃|=5, |S₃|+|S₄|=3, |S₄|+|S₀|=4
-/

def case52_check4 : Bool :=
  let vs := verts52
  !(vs.any fun v00 =>
    vs.any fun v01 =>
      enc52 v00 < enc52 v01 && crossNonAdj52 v00 v01 &&
    vs.any fun v02 =>
      enc52 v01 < enc52 v02 && crossNonAdj52 v00 v02 && crossNonAdj52 v01 v02 &&
    vs.any fun v10 =>
      compatWith52 v10 [v00, v01, v02] &&
    vs.any fun v11 =>
      enc52 v10 < enc52 v11 && crossNonAdj52 v10 v11 &&
      compatWith52 v11 [v00, v01, v02] &&
    vs.any fun v20 =>
      compatWith52 v20 [v10, v11] &&
    vs.any fun v21 =>
      enc52 v20 < enc52 v21 && crossNonAdj52 v20 v21 &&
      compatWith52 v21 [v10, v11] &&
    vs.any fun v22 =>
      enc52 v21 < enc52 v22 && crossNonAdj52 v20 v22 && crossNonAdj52 v21 v22 &&
      compatWith52 v22 [v10, v11] &&
    vs.any fun v30 =>
      compatWith52 v30 [v20, v21, v22] &&
    vs.any fun v31 =>
      enc52 v30 < enc52 v31 && crossNonAdj52 v30 v31 &&
      compatWith52 v31 [v20, v21, v22] &&
    vs.any fun v4 =>
      compatWith52 v4 [v30, v31, v00, v01, v02])

/-! ## Case 5: Size vector (3,2,3,1,2)

Layer sizes: 0→3, 1→2, 2→3, 3→1, 4→2
Pair constraints: |S₀|+|S₁|=5, |S₁|+|S₂|=5, |S₂|+|S₃|=4, |S₃|+|S₄|=3, |S₄|+|S₀|=5
-/

def case52_check5 : Bool :=
  let vs := verts52
  !(vs.any fun v00 =>
    vs.any fun v01 =>
      enc52 v00 < enc52 v01 && crossNonAdj52 v00 v01 &&
    vs.any fun v02 =>
      enc52 v01 < enc52 v02 && crossNonAdj52 v00 v02 && crossNonAdj52 v01 v02 &&
    vs.any fun v10 =>
      compatWith52 v10 [v00, v01, v02] &&
    vs.any fun v11 =>
      enc52 v10 < enc52 v11 && crossNonAdj52 v10 v11 &&
      compatWith52 v11 [v00, v01, v02] &&
    vs.any fun v20 =>
      compatWith52 v20 [v10, v11] &&
    vs.any fun v21 =>
      enc52 v20 < enc52 v21 && crossNonAdj52 v20 v21 &&
      compatWith52 v21 [v10, v11] &&
    vs.any fun v22 =>
      enc52 v21 < enc52 v22 && crossNonAdj52 v20 v22 && crossNonAdj52 v21 v22 &&
      compatWith52 v22 [v10, v11] &&
    vs.any fun v3 =>
      compatWith52 v3 [v20, v21, v22] &&
    vs.any fun v40 =>
      compatWith52 v40 [v3, v00, v01, v02] &&
    vs.any fun v41 =>
      enc52 v40 < enc52 v41 && crossNonAdj52 v40 v41 &&
      compatWith52 v41 [v3, v00, v01, v02])

/-! ## Case 6: Size vector (3,1,3,2,2)

Layer sizes: 0→3, 1→1, 2→3, 3→2, 4→2
Pair constraints: |S₀|+|S₁|=4, |S₁|+|S₂|=4, |S₂|+|S₃|=5, |S₃|+|S₄|=4, |S₄|+|S₀|=5
-/

def case52_check6 : Bool :=
  let vs := verts52
  !(vs.any fun v00 =>
    vs.any fun v01 =>
      enc52 v00 < enc52 v01 && crossNonAdj52 v00 v01 &&
    vs.any fun v02 =>
      enc52 v01 < enc52 v02 && crossNonAdj52 v00 v02 && crossNonAdj52 v01 v02 &&
    vs.any fun v1 =>
      compatWith52 v1 [v00, v01, v02] &&
    vs.any fun v20 =>
      compatWith52 v20 [v1] &&
    vs.any fun v21 =>
      enc52 v20 < enc52 v21 && crossNonAdj52 v20 v21 &&
      compatWith52 v21 [v1] &&
    vs.any fun v22 =>
      enc52 v21 < enc52 v22 && crossNonAdj52 v20 v22 && crossNonAdj52 v21 v22 &&
      compatWith52 v22 [v1] &&
    vs.any fun v30 =>
      compatWith52 v30 [v20, v21, v22] &&
    vs.any fun v31 =>
      enc52 v30 < enc52 v31 && crossNonAdj52 v30 v31 &&
      compatWith52 v31 [v20, v21, v22] &&
    vs.any fun v40 =>
      compatWith52 v40 [v30, v31, v00, v01, v02] &&
    vs.any fun v41 =>
      enc52 v40 < enc52 v41 && crossNonAdj52 v40 v41 &&
      compatWith52 v41 [v30, v31, v00, v01, v02])

/-! ## Case 7: Size vector (3,2,2,2,2)

Layer sizes: 0→3, 1→2, 2→2, 3→2, 4→2
Pair constraints: |S₀|+|S₁|=5, |S₁|+|S₂|=4, |S₂|+|S₃|=4, |S₃|+|S₄|=4, |S₄|+|S₀|=5
-/

def case52_check7 : Bool :=
  let vs := verts52
  !(vs.any fun v00 =>
    vs.any fun v01 =>
      enc52 v00 < enc52 v01 && crossNonAdj52 v00 v01 &&
    vs.any fun v02 =>
      enc52 v01 < enc52 v02 && crossNonAdj52 v00 v02 && crossNonAdj52 v01 v02 &&
    vs.any fun v10 =>
      compatWith52 v10 [v00, v01, v02] &&
    vs.any fun v11 =>
      enc52 v10 < enc52 v11 && crossNonAdj52 v10 v11 &&
      compatWith52 v11 [v00, v01, v02] &&
    vs.any fun v20 =>
      compatWith52 v20 [v10, v11] &&
    vs.any fun v21 =>
      enc52 v20 < enc52 v21 && crossNonAdj52 v20 v21 &&
      compatWith52 v21 [v10, v11] &&
    vs.any fun v30 =>
      compatWith52 v30 [v20, v21] &&
    vs.any fun v31 =>
      enc52 v30 < enc52 v31 && crossNonAdj52 v30 v31 &&
      compatWith52 v31 [v20, v21] &&
    vs.any fun v40 =>
      compatWith52 v40 [v30, v31, v00, v01, v02] &&
    vs.any fun v41 =>
      enc52 v40 < enc52 v41 && crossNonAdj52 v40 v41 &&
      compatWith52 v41 [v30, v31, v00, v01, v02])

/-! ## Combined check for all 7 size vectors

This is the main computational check: we verify that NO valid configuration
exists for ANY of the 7 rotation-class representatives.
-/

def case52_check : Bool :=
  case52_check1 && case52_check2 && case52_check3 && case52_check4 &&
  case52_check5 && case52_check6 && case52_check7

set_option maxRecDepth 2048 in
set_option maxHeartbeats 8000000 in
-- The layer-assignment backtracking search over 25 vertices and 7 size vectors
-- requires elevated recursion depth and heartbeats.
theorem case52_check_true : case52_check = true := by native_decide

/-- Every element of Fin 5 × Fin 5 is in `verts52`. -/
theorem mem_verts52 (v : Fin 5 × Fin 5) : v ∈ verts52 := by
  simp only [verts52, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
