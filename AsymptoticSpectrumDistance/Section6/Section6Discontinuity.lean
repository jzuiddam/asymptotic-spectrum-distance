/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Discontinuities of α₃

Formalises the notion of (extremal) discontinuity of `α₃` from
[de Boer, Buys, Zuiddam] §6 (paper line 2740–2741).

## Main definitions

* `Section6.alpha3 v` : `α(E_{p₁/q₁} ⊠ E_{p₂/q₂} ⊠ E_{p₃/q₃})` as a function
  of a triple of `(p, q)` pairs.
* `Section6.lePerm u v` : permutation-aware product order — `u ≤ₚ v` iff some
  permutation of `u` is pointwise (rationally) `≤ v`.
* `Section6.ltPerm u v` : strict version, `u ≤ₚ v ∧ ¬ v ≤ₚ u`.
* `Section6.IsDiscontinuity v` : `v` is a strict-extremal discontinuity, i.e.,
  `∀ u <ₚ v, α₃ u < α₃ v`.

These definitions are used in `Section6Discontinuity*.lean` to prove
that each of the 12 listed points in Theorem 6.9 is a discontinuity.
-/
import AsymptoticSpectrumDistance.Section6.Section6Diagonal
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityAlpha2

open ShannonCapacity AsymptoticSpectrumGraphs AsymptoticSpectrumDistance

namespace Section6

/-- A triple of fraction-graph parameters `(pᵢ, qᵢ) ∈ ℕ+ × ℕ+`, indexed by
    `Fin 3`. The intended interpretation is the rational triple
    `(p₀/q₀, p₁/q₁, p₂/q₂)`. -/
abbrev FracTriple := Fin 3 → ℕ+ × ℕ+

/-- The `i`-th coordinate of a `FracTriple` viewed as a rational. -/
def FracTriple.toRat (v : FracTriple) (i : Fin 3) : ℚ :=
  ((v i).1 : ℚ) / ((v i).2 : ℚ)

/-- `α₃(p₀/q₀, p₁/q₁, p₂/q₂) := α(E_{p₀/q₀} ⊠ E_{p₁/q₁} ⊠ E_{p₂/q₂})`. -/
noncomputable def alpha3 (v : FracTriple) : ℕ :=
  (fractionGraph (v 0).1 (v 0).2 ⊠
    fractionGraph (v 1).1 (v 1).2 ⊠
    fractionGraph (v 2).1 (v 2).2).indepNum

/-- Permutation-aware product order on `FracTriple`s, comparing coordinates
    as rationals: `u ≤ₚ v` iff there is a permutation `σ : Equiv.Perm (Fin 3)`
    such that `(u (σ i)).toRat ≤ (v i).toRat` for every `i`.
    Paper line 2740. -/
def lePerm (u v : FracTriple) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    ∀ i, FracTriple.toRat u (σ i) ≤ FracTriple.toRat v i

/-- Strict version: `u <ₚ v` iff `lePerm u v ∧ ¬ lePerm v u`. -/
def ltPerm (u v : FracTriple) : Prop := lePerm u v ∧ ¬ lePerm v u

/-- A `FracTriple` `v` is *valid* if each coordinate `(p, q)` satisfies the
    fraction-graph condition `2·q ≤ p` (equivalently `v.toRat i ≥ 2`). The
    paper restricts `α_k` to `ℚ_{≥2}^k`; this predicate carves out that domain. -/
def Valid (v : FracTriple) : Prop := ∀ i, 2 * (v i).2 ≤ (v i).1

/-- A `FracTriple` `v` is a *(strict-extremal) discontinuity* of `α₃` if
    every strictly smaller *valid* `u` (in the permutation order `<ₚ`) has
    strictly smaller `α₃` value. Paper line 2740–2741, restricted to
    `ℚ_{≥2}^3`. -/
def IsDiscontinuity (v : FracTriple) : Prop :=
  ∀ u, Valid u → ltPerm u v → alpha3 u < alpha3 v

/-! ## Helpers -/

/-- Any `Valid` `FracTriple` has each coordinate's rational value `≥ 2`. -/
lemma toRat_ge_two_of_valid {u : FracTriple} (hu : Valid u) (i : Fin 3) :
    (2 : ℚ) ≤ FracTriple.toRat u i := by
  have h := hu i
  unfold FracTriple.toRat
  rw [le_div_iff₀ (by exact_mod_cast (u i).2.pos : (0 : ℚ) < ((u i).2 : ℚ))]
  exact_mod_cast h

/-- Each coordinate of a `Valid` `FracTriple` is positive as a rational. -/
lemma toRat_pos_of_valid {u : FracTriple} (hu : Valid u) (i : Fin 3) :
    (0 : ℚ) < FracTriple.toRat u i :=
  lt_of_lt_of_le (by norm_num) (toRat_ge_two_of_valid hu i)

/-- Chibar real bound: `α₃(u) ≤ u₀.toRat · u₁.toRat · u₂.toRat` (as reals),
    derived from `nested_floor_three` and `⌊x⌋₊ ≤ x`. Requires `Valid u`. -/
lemma alpha3_le_prod_real {u : FracTriple} (hu : Valid u) :
    (alpha3 u : ℝ) ≤
      ((FracTriple.toRat u 0 : ℝ) *
       (FracTriple.toRat u 1 : ℝ) *
       (FracTriple.toRat u 2 : ℝ)) := by
  -- Bound `α₃(u)` by `nested_floor_three` (right-associated form via assoc).
  have h := nested_floor_three (u 0).1 (u 0).2 (u 1).1 (u 1).2 (u 2).1 (u 2).2
    (u 0).2.pos (hu 0) (u 1).2.pos (hu 1) (u 2).2.pos (hu 2)
  -- Convert `alpha3 u` to right-assoc form, then chain the bound.
  have hassoc : alpha3 u =
      (fractionGraph (u 0).1 (u 0).2 ⊠
        (fractionGraph (u 1).1 (u 1).2 ⊠ fractionGraph (u 2).1 (u 2).2)).indepNum := by
    change ((fractionGraph (u 0).1 (u 0).2 ⊠ fractionGraph (u 1).1 (u 1).2) ⊠
          fractionGraph (u 2).1 (u 2).2).indepNum = _
    exact ShannonCapacity.indepNum_strongProduct_assoc _ _ _
  rw [hassoc]
  -- Chain `⌊x⌋₊ ≤ x` three times.
  have hp0 : (0 : ℝ) ≤ ((u 0).1 : ℝ) / (u 0).2 := by positivity
  have hp1 : (0 : ℝ) ≤ ((u 1).1 : ℝ) / (u 1).2 := by positivity
  have hp2 : (0 : ℝ) ≤ ((u 2).1 : ℝ) / (u 2).2 := by positivity
  have hf2 : (⌊((u 2).1 : ℝ) / (u 2).2⌋₊ : ℝ) ≤ ((u 2).1 : ℝ) / (u 2).2 :=
    Nat.floor_le hp2
  have hf1 : (⌊((u 1).1 : ℝ) / (u 1).2 *
                ⌊((u 2).1 : ℝ) / (u 2).2⌋₊⌋₊ : ℝ) ≤
             ((u 1).1 : ℝ) / (u 1).2 * (((u 2).1 : ℝ) / (u 2).2) := by
    refine le_trans (Nat.floor_le ?_) ?_
    · positivity
    · exact mul_le_mul_of_nonneg_left hf2 hp1
  have hf0 : ((⌊((u 0).1 : ℝ) / (u 0).2 *
                ⌊((u 1).1 : ℝ) / (u 1).2 *
                  ⌊((u 2).1 : ℝ) / (u 2).2⌋₊⌋₊⌋₊ : ℕ) : ℝ) ≤
             (((u 0).1 : ℝ) / (u 0).2) *
               (((u 1).1 : ℝ) / (u 1).2 * (((u 2).1 : ℝ) / (u 2).2)) := by
    refine le_trans (Nat.floor_le ?_) ?_
    · positivity
    · exact mul_le_mul_of_nonneg_left hf1 hp0
  -- Cast and conclude.
  have htoRat : ((FracTriple.toRat u 0 : ℝ) *
                  (FracTriple.toRat u 1 : ℝ) *
                  (FracTriple.toRat u 2 : ℝ)) =
                (((u 0).1 : ℝ) / (u 0).2) *
                  (((u 1).1 : ℝ) / (u 1).2 * (((u 2).1 : ℝ) / (u 2).2)) := by
    simp [FracTriple.toRat]; ring
  rw [htoRat]
  exact le_trans (by exact_mod_cast h) hf0

/-! ## Discontinuity proofs for the 12 points of Theorem 6.9 -/

/-- The triple `(2, 2, 2)`. -/
def triple222 : FracTriple := ![(2, 1), (2, 1), (2, 1)]

/-- The triple `(2, 2, 3)`. -/
def triple223 : FracTriple := ![(2, 1), (2, 1), (3, 1)]

/-- The triple `(2, 3, 3)`. -/
def triple233 : FracTriple := ![(2, 1), (3, 1), (3, 1)]

/-- The triple `(3, 3, 3)`. -/
def triple333 : FracTriple := ![(3, 1), (3, 1), (3, 1)]

/-- Product of `u.toRat` over `Fin 3` is invariant under permutation. -/
lemma prod_toRat_perm_invariant (u : FracTriple) (σ : Equiv.Perm (Fin 3)) :
    ((FracTriple.toRat u (σ 0) : ℝ) * (FracTriple.toRat u (σ 1) : ℝ) *
      (FracTriple.toRat u (σ 2) : ℝ)) =
    ((FracTriple.toRat u 0 : ℝ) * (FracTriple.toRat u 1 : ℝ) *
      (FracTriple.toRat u 2 : ℝ)) := by
  have h := Equiv.Perm.prod_comp σ Finset.univ
    (fun i => (FracTriple.toRat u i : ℝ)) (by simp)
  simp [Fin.prod_univ_succ] at h
  linarith [h]

/-- `α₃(2, 2, 3) = 12`. -/
lemma alpha3_triple223_eq : alpha3 triple223 = 12 := by
  change ((fractionGraph 2 1 ⊠ fractionGraph 2 1) ⊠ fractionGraph 3 1).indepNum = 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_2_2_3

/-- `α₃(2, 3, 3) = 18`. -/
lemma alpha3_triple233_eq : alpha3 triple233 = 18 := by
  change ((fractionGraph 2 1 ⊠ fractionGraph 3 1) ⊠ fractionGraph 3 1).indepNum = 18
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_2_3_3

/-- `α₃(3, 3, 3) = 27`. -/
lemma alpha3_triple333_eq : alpha3 triple333 = 27 := by
  change ((fractionGraph 3 1 ⊠ fractionGraph 3 1) ⊠ fractionGraph 3 1).indepNum = 27
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_3_3_3

/-! ## Case 5: `(2, 5/2, 5/2) = 10` via integer-peel from `α₂(5/2, 5/2)` -/

/-- The triple `(2, 5/2, 5/2)`. -/
def triple_2_5o2_5o2 : FracTriple := ![(2, 1), (5, 2), (5, 2)]

/-- `α₃(2, 5/2, 5/2) = 10`. From `α(E_2 ⊠ G) = 2 · α(G)` with
    `G = E_{5/2} ⊠ E_{5/2}`, whose independence number is `5` by
    `alpha2_pair5o2_5o2_eq`. -/
lemma alpha3_triple_2_5o2_5o2_eq : alpha3 triple_2_5o2_5o2 = 10 := by
  change ((fractionGraph 2 1 ⊠ fractionGraph 5 2) ⊠ fractionGraph 5 2).indepNum = 10
  rw [ShannonCapacity.indepNum_strongProduct_assoc,
      indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  have h5 : (fractionGraph 5 2 ⊠ fractionGraph 5 2).indepNum = 5 := alpha2_pair5o2_5o2_eq
  rw [h5]

/-! ## Case 6: `(5/2, 5/2, 3) = 15` via Hales-at-slot + `α₂(5/2, 5/2)` -/

/-- The triple `(5/2, 5/2, 3)`. -/
def triple_5o2_5o2_3 : FracTriple := ![(5, 2), (5, 2), (3, 1)]

/-- `α₃(5/2, 5/2, 3) = 15`. From `α(G ⊠ E_3) = 3 · α(G)` (integer factor on the
    last factor via outer commutativity) with `G = E_{5/2} ⊠ E_{5/2}` of
    independence number 5. -/
lemma alpha3_triple_5o2_5o2_3_eq : alpha3 triple_5o2_5o2_3 = 15 := by
  change ((fractionGraph 5 2 ⊠ fractionGraph 5 2) ⊠ fractionGraph 3 1).indepNum = 15
  rw [indepNum_strongProduct_comm]
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega)]
  have h5 : (fractionGraph 5 2 ⊠ fractionGraph 5 2).indepNum = 5 := alpha2_pair5o2_5o2_eq
  rw [h5]

end Section6
