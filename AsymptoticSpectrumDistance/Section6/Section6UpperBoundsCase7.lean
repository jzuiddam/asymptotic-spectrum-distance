/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Case 7 Computational Check: α(E_{5/2}² ⊠ E_{8/3}) ≠ 12

Exhaustive chain search over maximal independent sets of E_{5/2} ⊠ E_{8/3},
verifying that no valid chain of 4 max ISs exists. This rules out α = 12
(the nested floor bound), establishing α ≤ 11.

This is the direct analogue of the chain search in
[BMRRS, Computation] (α(C₇³) ≠ 35) and
[BMRRS, Theorem 4] (α(C₅³) ≠ 11, 12).

[BMRRS] L. D. Baumert, R. J. McEliece, E. Rodemich, H. C. Rumsey, R. Stanley,
        H. Taylor, "A Combinatorial Packing Problem", 1971.

See `Section6UpperBounds.lean` for the full method description and how this
computational check fits into the overall proof.

## Main result

- `case7_check_true`: the case 7 Baumert chain search returns `true`
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
def distRaw7 (n : ℕ) (a b : Fin n) : ℕ :=
  let diff := if a.val ≥ b.val then a.val - b.val else b.val - a.val
  min diff (n - diff)

/-! ## Case 7: α(E_{5/2}² ⊠ E_{8/3}) ≤ 11

**Context**: The nested floor bound (iterated [BMRRS, Lemma 2]) gives α ≤ 12.
We rule out α = 12 by the chain search technique of [BMRRS, Computation].

**Graph**: E_{5/2} ⊠ (E_{5/2} ⊠ E_{8/3}) has 5·5·8 = 200 vertices.
Slicing by the first E_{5/2} coordinate gives 5 layers in E_{5/2} ⊠ E_{8/3}.
Since α(E_{5/2} ⊠ E_{8/3}) = 5 (from `theorem_6_5`), each adjacent pair of
layers contributes ≤ 5 to the total. With 5 edges in C₅ and total 12, we get
2·12 = 24 ≤ 5·5, so each edge-pair must contribute exactly 5 (slack 1 forces
sizes (2,3,2,3,2) or (3,2,3,2,2) up to rotation). Each adjacent pair forms a
max IS of E_{5/2} ⊠ E_{8/3}.

**Max ISs**: A max IS of size 5 in E_{5/2} ⊠ E_{8/3} (40 vertices) is a function
f : Z₅ → Z₈ such that for adjacent i,j in E_{5/2}, we have f(i) ≠ f(j) and
distMod(8, f(i), f(j)) ≥ 3. There are exactly 80 such functions.
(Analogous to the 980 maximal packings of the 7²-torus in [BMRRS, Computation].)

**Chain search**: We search over all 80⁴ chains (f₁,f₂,f₃,f₄) representing 4
consecutive pairs of layers, with overlap patterns forced by the layer sizes.
No valid chain exists. (Analogous to [BMRRS, Computation]: "the configuration
forced on P₆ at this point never was a 10 packing.") -/

/-- Cross-layer non-adjacency in E_{5/2} ⊠ E_{8/3}: returns `true` iff the pair
    (a1,a2), (b1,b2) is NOT adjacent in the strong product. Does NOT shortcut on
    equal points: when (a1,a2) = (b1,b2) but they come from different layers,
    the corresponding 3D points ARE adjacent (they differ in the slicing coordinate). -/
def crossNonAdj52_83 (a1 b1 : Fin 5) (a2 b2 : Fin 8) : Bool :=
  !((a1 == b1 || distRaw7 5 a1 b1 < 2) &&
    (a2 == b2 || distRaw7 8 a2 b2 < 3))

/-- All 80 max ISs of E_{5/2} ⊠ E_{8/3}, represented as functions Fin 5 → Fin 8.
    Each function f assigns to vertex i ∈ Z₅ a value f(i) ∈ Z₈ such that for
    adjacent i,j in E_{5/2} (i.e., distMod(5,i,j) < 2, i.e., |i-j| = 1 mod 5),
    we have f(i) ≠ f(j) and distMod(8,f(i),f(j)) ≥ 3.
    (Analogous to [BMRRS, Computation]: the 980 maximal packings of the 7²-torus.) -/
private def maxISs52_83 : List (Fin 5 → Fin 8) :=
  let all := (List.finRange 8).flatMap fun v0 =>
    (List.finRange 8).flatMap fun v1 =>
    (List.finRange 8).flatMap fun v2 =>
    (List.finRange 8).flatMap fun v3 =>
    (List.finRange 8).map fun v4 =>
      fun i : Fin 5 => match i with
        | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3 | 4 => v4
  all.filter fun f =>
    (List.finRange 5).all fun i =>
      (List.finRange 5).all fun j =>
        i == j || distRaw7 5 i j ≥ 2 ||
        (!(f i == f j) && distRaw7 8 (f i) (f j) ≥ 3)

/-- Case 7 Baumert chain search: no valid chain of 4 max ISs exists.

Suppose an IS of size 12 exists in E_{5/2} ⊠ (E_{5/2} ⊠ E_{8/3}). Slicing by
the first E_{5/2} coordinate gives layers S₀,...,S₄ with sizes summing to 12 and
each adjacent pair summing to ≤ 5 = α(E_{5/2} ⊠ E_{8/3}). The slack-1 integer
program forces each adjacent pair (Sᵢ ∪ Sᵢ₊₁) to be a max IS of size 5.

Representing each max IS as f : Z₅ → Z₈, the overlap between consecutive pairs
is determined by which coordinates agree/disagree. We search over all 80⁴ chains
(f₁,f₂,f₃,f₄) with the forced overlap pattern (3 agreements, then alternating).

This is the direct analogue of [BMRRS, Computation]: "a fairly simple computer
search program was written which first selected five cubes from P₀ and then in
turn inserted as P₁ each of the 980 packings having those five cubes." -/
def case7_check : Bool :=
  !(maxISs52_83.any fun f₁ =>
    maxISs52_83.any fun f₂ =>
      let agree := (List.finRange 5).countP fun i => f₁ i == f₂ i
      agree == 3 &&
      maxISs52_83.any fun f₃ =>
        (List.finRange 5).all (fun i =>
          if f₁ i == f₂ i then !(f₂ i == f₃ i)
          else f₂ i == f₃ i) &&
        maxISs52_83.any fun f₄ =>
          (List.finRange 5).all (fun i =>
            if f₁ i == f₂ i then f₃ i == f₄ i
            else !(f₃ i == f₄ i)) &&
          (List.finRange 5).all fun i₁ =>
            (List.finRange 5).all fun i₂ =>
              (f₁ i₁ == f₂ i₁) || (f₁ i₂ == f₂ i₂) ||
              crossNonAdj52_83 i₁ i₂ (f₁ i₁) (f₄ i₂))

set_option maxRecDepth 1024 in
set_option maxHeartbeats 800000 in
-- The chain search iterates over 80⁴ combinations, requiring elevated heartbeats.
theorem case7_check_true : case7_check = true := by native_decide

/-! ## Direct layer-assignment check for Case 7

This is an alternative check that directly searches over all possible layer assignments
(like `case8_check`) rather than using the chain-of-max-ISs approach of `case7_check`.
The connection to the abstract IS is simpler: we only need to extract witnesses from
each layer and check cross-layer non-adjacency.

Layer sizes: (2,2,3,2,3) for layers 0,1,2,3,4 in C₅ ⊠ E_{8/3}.
Cross-layer adjacency: layers i,j are adjacent in C₅ when distMod(5,i,j) = 1,
i.e., edges {0,1}, {1,2}, {2,3}, {3,4}, {4,0}. -/

/-- All 40 vertices of E_{5/2} ⊠ E_{8/3}. -/
def verts52_83 : List (Fin 5 × Fin 8) :=
  (List.finRange 5).flatMap fun i => (List.finRange 8).map fun j => (i, j)

/-- Check strict cross-layer non-adjacency against all elements of a list. -/
def compatWith52_83 (v : Fin 5 × Fin 8) (prev : List (Fin 5 × Fin 8)) : Bool :=
  prev.all fun w => crossNonAdj52_83 v.1 w.1 v.2 w.2

/-- Encode a pair for ordering (to break symmetry in size≥2 layers). -/
def enc52_83 (v : Fin 5 × Fin 8) : ℕ := v.1.val * 8 + v.2.val

/-- Case 7 direct layer-assignment check: no valid 5-layer configuration with
    sizes (2,2,3,2,3) exists in E_{5/2} ⊠ E_{8/3}.

    Layer 0 (size 2): s00, s01
    Layer 1 (size 2): s10, s11
    Layer 2 (size 3): s20, s21, s22
    Layer 3 (size 2): s30, s31
    Layer 4 (size 3): s40, s41, s42

    Cross-layer adjacency in C₅: {0,1}, {1,2}, {2,3}, {3,4}, {4,0}.
    Each layer-i element must be `crossNonAdj52_83` with all elements of
    adjacent layers. -/
def case7_direct_check : Bool :=
  let vs := verts52_83
  !(vs.any fun s00 =>
    vs.any fun s01 =>
      enc52_83 s00 < enc52_83 s01 && crossNonAdj52_83 s00.1 s01.1 s00.2 s01.2 &&
    vs.any fun s10 =>
      compatWith52_83 s10 [s00, s01] &&
    vs.any fun s11 =>
      enc52_83 s10 < enc52_83 s11 && crossNonAdj52_83 s10.1 s11.1 s10.2 s11.2 &&
      compatWith52_83 s11 [s00, s01] &&
    vs.any fun s20 =>
      compatWith52_83 s20 [s10, s11] &&
    vs.any fun s21 =>
      enc52_83 s20 < enc52_83 s21 && crossNonAdj52_83 s20.1 s21.1 s20.2 s21.2 &&
      compatWith52_83 s21 [s10, s11] &&
    vs.any fun s22 =>
      enc52_83 s21 < enc52_83 s22 &&
      crossNonAdj52_83 s20.1 s22.1 s20.2 s22.2 &&
      crossNonAdj52_83 s21.1 s22.1 s21.2 s22.2 &&
      compatWith52_83 s22 [s10, s11] &&
    vs.any fun s30 =>
      compatWith52_83 s30 [s20, s21, s22] &&
    vs.any fun s31 =>
      enc52_83 s30 < enc52_83 s31 && crossNonAdj52_83 s30.1 s31.1 s30.2 s31.2 &&
      compatWith52_83 s31 [s20, s21, s22] &&
    vs.any fun s40 =>
      compatWith52_83 s40 [s30, s31, s00, s01] &&
    vs.any fun s41 =>
      enc52_83 s40 < enc52_83 s41 && crossNonAdj52_83 s40.1 s41.1 s40.2 s41.2 &&
      compatWith52_83 s41 [s30, s31, s00, s01] &&
    vs.any fun s42 =>
      enc52_83 s41 < enc52_83 s42 &&
      crossNonAdj52_83 s40.1 s42.1 s40.2 s42.2 &&
      crossNonAdj52_83 s41.1 s42.1 s41.2 s42.2 &&
      compatWith52_83 s42 [s30, s31, s00, s01])

set_option maxHeartbeats 4000000 in
-- Layer-assignment backtracking search over 40 vertices requires elevated heartbeats.
theorem case7_direct_check_true : case7_direct_check = true := by native_decide

/-- Every element of Fin 5 × Fin 8 is in `verts52_83`. -/
theorem mem_verts52_83 (v : Fin 5 × Fin 8) : v ∈ verts52_83 := by
  simp only [verts52_83, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v.1, ⟨v.2, Prod.ext rfl rfl⟩⟩

end Section6
