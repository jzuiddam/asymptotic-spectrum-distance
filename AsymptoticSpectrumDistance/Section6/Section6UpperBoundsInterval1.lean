/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Baumert Computational Check: α(E_{7/3}³) ≠ 9

Exhaustive layer search verifying that no valid 7-layer configuration with
sizes (1,2,1,1,2,1,1) exists in E_{7/3}². This rules out α = 9
(the nested floor bound), establishing α ≤ 8.

This is directly analogous to the proof of [BMRRS, Lemma 3] (α(C₁₃³) ≤ 252),
which slices into 13 layers, derives forced packing sizes, and obtains a
structural contradiction.

[BMRRS] L. D. Baumert, R. J. McEliece, E. Rodemich, H. C. Rumsey, R. Stanley,
        H. Taylor, "A Combinatorial Packing Problem", 1971.

See `Section6UpperBounds.lean` for the full method description and how this
computational check fits into the overall proof.

## Main result

- `case73_check_true`: the case E_{7/3}³ Baumert layer search returns `true`
-/

import Mathlib.Data.List.FinRange

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Computable distance helper -/

/-- Circular distance mod n, computable on `Fin n`.
Agrees with `distMod n` on `ZMod n` when `ZMod n = Fin n`
(i.e., for concrete n). -/
private def distRaw73 (a b : Fin 7) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (7 - diff)

/-! ## Case: α(E_{7/3}³) ≤ 8

**Context**: The nested floor bound gives α ≤ 9. We rule out α = 9 by the
slicing technique of [BMRRS, Lemma 3].

**Graph**: E_{7/3}³ has 7³ = 343 vertices. Slicing by the first E_{7/3}
coordinate gives 7 layers in E_{7/3}² (49 vertices each). Since α(E_{7/3}²)
= 4, and each 3-clique {i,i+1,i+2} of E_{7/3} gives a fiber constraint
|Sᵢ| + |Sᵢ₊₁| + |Sᵢ₊₂| ≤ 4, the integer program with total 9 and
7 clique constraints (sum 3·9 = 27, capacity 7·4 = 28, slack 1) forces
the unique solution (1,2,1,1,2,1,1) up to rotation of Z₇.

**Layer adjacency** (layers i,j adjacent when distRaw(7,i,j) < 3):
- Layer 0 adj to: 1,2,5,6
- Layer 1 adj to: 0,2,3,6
- Layer 2 adj to: 0,1,3,4
- Layer 3 adj to: 1,2,4,5
- Layer 4 adj to: 2,3,5,6
- Layer 5 adj to: 3,4,6,0
- Layer 6 adj to: 4,5,0,1

**Exhaustive search**: We verify by backtracking that no valid assignment of
vertices to layers exists with sizes (1,2,1,1,2,1,1), checking cross-layer
non-adjacency for all pairs in adjacent layers (distance 1 or 2 in E_{7/3}).

Assign layers in order 0,1,2,3,4,5,6:
- Layer 0 (size 1): v0 — no prior constraints
- Layer 1 (size 2): v10,v11 — compat with [v0]
- Layer 2 (size 1): v2 — compat with [v0, v10, v11]
- Layer 3 (size 1): v3 — compat with [v10, v11, v2]
- Layer 4 (size 2): v40,v41 — compat with [v2, v3]
- Layer 5 (size 1): v5 — compat with [v3, v40, v41, v0]
- Layer 6 (size 1): v6 — compat with [v40, v41, v5, v0, v10, v11]
-/

/-- Cross-layer non-adjacency in E_{7/3}²: returns `true` iff the pair a, b is
    NOT adjacent in E_{7/3}². -/
def crossNonAdj73 (a b : Fin 7 × Fin 7) : Bool :=
  !((distRaw73 a.1 b.1 < 3) && (distRaw73 a.2 b.2 < 3))

/-- All 49 vertices of E_{7/3}². -/
def verts73 : List (Fin 7 × Fin 7) :=
  (List.finRange 7).flatMap fun i => (List.finRange 7).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith73 (v : Fin 7 × Fin 7) (prev : List (Fin 7 × Fin 7)) : Bool :=
  prev.all fun w => crossNonAdj73 v w

/-- Encode a pair for ordering (to break symmetry in size-2 layers). -/
def enc73 (v : Fin 7 × Fin 7) : ℕ := v.1.val * 7 + v.2.val

/-- Baumert layer search for E_{7/3}³ with sizes (1,2,1,1,2,1,1).

    Returns `true` iff no valid assignment exists. The variables v0,...,v6
    represent vertices assigned to layers 0-6 with sizes (1,2,1,1,2,1,1).
    For size-2 layers, `enc73` ordering breaks symmetry. The `compatWith73`
    checks enforce cross-layer non-adjacency for all pairs in adjacent
    layers (distance 1 or 2 in E_{7/3}). -/
def case73_check : Bool :=
  let vs := verts73
  !(vs.any fun v0 =>                         -- Layer 0 (size 1)
    vs.any fun v10 =>                        -- Layer 1 (size 2)
      crossNonAdj73 v10 v0 &&
    vs.any fun v11 =>
      enc73 v10 < enc73 v11 && crossNonAdj73 v10 v11 &&
      crossNonAdj73 v11 v0 &&
    vs.any fun v2 =>                         -- Layer 2 (size 1)
      compatWith73 v2 [v0, v10, v11] &&
    vs.any fun v3 =>                         -- Layer 3 (size 1)
      compatWith73 v3 [v10, v11, v2] &&
    vs.any fun v40 =>                        -- Layer 4 (size 2)
      compatWith73 v40 [v2, v3] &&
    vs.any fun v41 =>
      enc73 v40 < enc73 v41 && crossNonAdj73 v40 v41 &&
      compatWith73 v41 [v2, v3] &&
    vs.any fun v5 =>                         -- Layer 5 (size 1)
      compatWith73 v5 [v3, v40, v41, v0] &&
    vs.any fun v6 =>                         -- Layer 6 (size 1)
      compatWith73 v6 [v40, v41, v5, v0, v10, v11])

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
-- The backtracking search over 49 vertices requires elevated heartbeats.
theorem case73_check_true : case73_check = true := by native_decide

end Section6
