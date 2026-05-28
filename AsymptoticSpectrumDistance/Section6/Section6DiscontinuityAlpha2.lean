/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# α₂ machinery for the discontinuity formalism

`α₂(p₁/q₁, p₂/q₂) = α(E_{p₁/q₁} ⊠ E_{p₂/q₂})`. The 2-factor formula
(`Section6.theorem_6_5`) determines `α₂` exactly. The 4 discontinuities of `α₂`
on `(ℚ ∩ [2,3])²` (up to permutation) are:

  α₂(2, 2) = 4
  α₂(2, 3) = 6
  α₂(3, 3) = 9
  α₂(5/2, 5/2) = 5

Each is proved here as `IsDiscontinuity₂`. These feed into the integer-peel
lemma to derive 6 of the 12 α₃ discontinuities of Theorem 6.9.
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6IntegerFactor
import AsymptoticSpectrumDistance.Section3.FractionGraphsDefs
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum

open ShannonCapacity AsymptoticSpectrumGraphs AsymptoticSpectrumDistance

namespace Section6

/-! ## α₂ machinery -/

/-- A pair of fraction-graph parameters indexed by `Fin 2`. -/
abbrev FracPair := Fin 2 → ℕ+ × ℕ+

/-- The `i`-th coordinate of a `FracPair` viewed as a rational. -/
def FracPair.toRat (v : FracPair) (i : Fin 2) : ℚ :=
  ((v i).1 : ℚ) / ((v i).2 : ℚ)

/-- `α₂(p₀/q₀, p₁/q₁) := α(E_{p₀/q₀} ⊠ E_{p₁/q₁})`. -/
noncomputable def alpha2 (v : FracPair) : ℕ :=
  (fractionGraph (v 0).1 (v 0).2 ⊠ fractionGraph (v 1).1 (v 1).2).indepNum

/-- Permutation-aware product order on `FracPair`s. -/
def lePerm₂ (u v : FracPair) : Prop :=
  ∃ σ : Equiv.Perm (Fin 2),
    ∀ i, FracPair.toRat u (σ i) ≤ FracPair.toRat v i

/-- Strict version. -/
def ltPerm₂ (u v : FracPair) : Prop := lePerm₂ u v ∧ ¬ lePerm₂ v u

/-- `Valid₂ v` iff each coord satisfies `2·q ≤ p`. -/
def Valid₂ (v : FracPair) : Prop := ∀ i, 2 * (v i).2 ≤ (v i).1

/-- `v` is a discontinuity of `α₂` on `ℚ_{≥2}^2`. -/
def IsDiscontinuity₂ (v : FracPair) : Prop :=
  ∀ u, Valid₂ u → ltPerm₂ u v → alpha2 u < alpha2 v

/-! ## Helpers -/

lemma toRat_ge_two_of_valid₂ {u : FracPair} (hu : Valid₂ u) (i : Fin 2) :
    (2 : ℚ) ≤ FracPair.toRat u i := by
  have h := hu i
  unfold FracPair.toRat
  rw [le_div_iff₀ (by exact_mod_cast (u i).2.pos : (0 : ℚ) < ((u i).2 : ℚ))]
  exact_mod_cast h

lemma toRat_pos_of_valid₂ {u : FracPair} (hu : Valid₂ u) (i : Fin 2) :
    (0 : ℚ) < FracPair.toRat u i :=
  lt_of_lt_of_le (by norm_num) (toRat_ge_two_of_valid₂ hu i)

/-- The pair `(2, 2)`. -/
def pair22 : FracPair := ![(2, 1), (2, 1)]

/-- The pair `(2, 3)`. -/
def pair23 : FracPair := ![(2, 1), (3, 1)]

/-- The pair `(3, 3)`. -/
def pair33 : FracPair := ![(3, 1), (3, 1)]

/-- `α₂(2, 3) = 6`. -/
lemma alpha2_pair23_eq : alpha2 pair23 = 6 := by
  change (fractionGraph 2 1 ⊠ fractionGraph 3 1).indepNum = 6
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  rw [fractionGraph_one_indepNum 3 (by omega)]


/-- `α₂(3, 3) = 9`. -/
lemma alpha2_pair33_eq : alpha2 pair33 = 9 := by
  change (fractionGraph 3 1 ⊠ fractionGraph 3 1).indepNum = 9
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega)]
  rw [fractionGraph_one_indepNum 3 (by omega)]

/-! ## The (5/2, 5/2) discontinuity

This is the only α₂-discontinuity that is not handled by the chibar
(real product) bound: `(5/2)² = 25/4 = 6.25` so `⌊25/4⌋ = 6 ≥ 5`. We need the
sharper *nested floor* bound (Lemma 6.5 / `theorem_6_5`):
`α₂(p₀/q₀, p₁/q₁) = min(⌊p₀/q₀ · ⌊p₁/q₁⌋⌋, ⌊p₁/q₁ · ⌊p₀/q₀⌋⌋)`.

For `u <ₚ (5/2, 5/2)` with both coords in `[2, 5/2]`, both `⌊p_i/q_i⌋ = 2`,
and a strict drop at one coord gives a strict drop in the corresponding
nested-floor expression below `⌊5⌋ = 5`. Combine with strong-product
commutativity to handle either coord. -/

/-- The pair `(5/2, 5/2)`. -/
def pair5o2_5o2 : FracPair := ![(5, 2), (5, 2)]

/-- Bridge: cast of `FracPair.toRat` from ℚ to ℝ equals direct ℝ-valued ratio. -/
private lemma toRat_cast_real (v : FracPair) (i : Fin 2) :
    ((FracPair.toRat v i : ℚ) : ℝ) = ((v i).1 : ℝ) / ((v i).2 : ℝ) := by
  unfold FracPair.toRat
  push_cast
  ring

/-- `α₂(5/2, 5/2) = 5`, via `theorem_6_5`. -/
lemma alpha2_pair5o2_5o2_eq : alpha2 pair5o2_5o2 = 5 := by
  change (fractionGraph 5 2 ⊠ fractionGraph 5 2).indepNum = 5
  rw [theorem_6_5 5 2 5 2 (by omega) (by omega) (by omega) (by omega)]
  have hf1 : ⌊((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)⌋₊ = 2 := by
    have heq : (((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = (5 : ℝ) / 2 := by push_cast; ring
    rw [heq]
    apply (Nat.floor_eq_iff (by norm_num)).mpr
    refine ⟨by norm_num, by norm_num⟩
  rw [hf1]
  have hf2 : ⌊((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)⌋₊ = 5 := by
    have heq : ((((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) * ((2 : ℕ) : ℝ)) = (5 : ℝ) := by
      push_cast; ring
    rw [heq]
    simp
  rw [hf2]
  simp

/-- ℝ-valued ratio of a valid `FracPair` coordinate is in `[2, ∞)`. -/
private lemma ratio_ge_two {u : FracPair} (hu : Valid₂ u) (i : Fin 2) :
    (2 : ℝ) ≤ ((u i).1 : ℝ) / ((u i).2 : ℝ) := by
  rw [← toRat_cast_real]
  have := toRat_ge_two_of_valid₂ hu i
  exact_mod_cast this

/-- ℝ-valued ratio: ≤ 5/2 in ℚ implies ≤ 5/2 in ℝ. -/
private lemma ratio_le_5o2_real {u : FracPair} (i : Fin 2)
    (h : FracPair.toRat u i ≤ 5 / 2) :
    ((u i).1 : ℝ) / ((u i).2 : ℝ) ≤ 5 / 2 := by
  rw [← toRat_cast_real]
  have h' : ((FracPair.toRat u i : ℚ) : ℝ) ≤ ((5 / 2 : ℚ) : ℝ) := by exact_mod_cast h
  have hcast : ((5 / 2 : ℚ) : ℝ) = (5 : ℝ) / 2 := by push_cast; ring
  linarith

/-- ℝ-valued ratio: < 5/2 in ℚ implies < 5/2 in ℝ. -/
private lemma ratio_lt_5o2_real {u : FracPair} (i : Fin 2)
    (h : FracPair.toRat u i < 5 / 2) :
    ((u i).1 : ℝ) / ((u i).2 : ℝ) < 5 / 2 := by
  rw [← toRat_cast_real]
  have h' : ((FracPair.toRat u i : ℚ) : ℝ) < ((5 / 2 : ℚ) : ℝ) := by exact_mod_cast h
  have hcast : ((5 / 2 : ℚ) : ℝ) = (5 : ℝ) / 2 := by push_cast; ring
  linarith

/-- Floor of `p/q` in ℝ equals `2` whenever `p/q ∈ [2, 5/2]` (forces `< 3`). -/
private lemma floor_eq_two_of_in_2_5o2 {u : FracPair} (hu : Valid₂ u) (i : Fin 2)
    (h : FracPair.toRat u i ≤ 5 / 2) :
    ⌊((u i).1 : ℝ) / ((u i).2 : ℝ)⌋₊ = 2 := by
  have h_ge_real := ratio_ge_two hu i
  have h_le_real := ratio_le_5o2_real i h
  have h_lt_real : ((u i).1 : ℝ) / ((u i).2 : ℝ) < 3 := by linarith
  apply (Nat.floor_eq_iff (by linarith)).mpr
  refine ⟨by exact_mod_cast h_ge_real, ?_⟩
  change ((u i).1 : ℝ) / ((u i).2 : ℝ) < ((2 : ℕ) : ℝ) + 1
  push_cast
  linarith

/-- Key bound: if `u 0` is strictly less than `5/2` and `u 1 ≤ 5/2`, then
    `alpha2 u ≤ 4`. Comes from `nested_floor_two` with inner floor = 2 and
    outer expression `⌊2 · u₀.toRat⌋ < ⌊5⌋ = 5`. -/
private lemma alpha2_le_four_of_lt_left {u : FracPair} (hu : Valid₂ u)
    (h0 : FracPair.toRat u 0 < 5 / 2)
    (h1 : FracPair.toRat u 1 ≤ 5 / 2) :
    alpha2 u ≤ 4 := by
  have hbound := nested_floor_two (u 0).1 (u 0).2 (u 1).1 (u 1).2
    (u 0).2.pos (hu 0) (u 1).2.pos (hu 1)
  rw [floor_eq_two_of_in_2_5o2 hu 1 h1] at hbound
  have h0_real := ratio_lt_5o2_real 0 h0
  have hprod_lt : ((u 0).1 : ℝ) / ((u 0).2 : ℝ) * 2 < 5 := by linarith
  have hfloor_lt : ⌊((u 0).1 : ℝ) / ((u 0).2 : ℝ) * ((2 : ℕ) : ℝ)⌋₊ < 5 := by
    have heq : (((u 0).1 : ℝ) / ((u 0).2 : ℝ) * ((2 : ℕ) : ℝ)) =
               ((u 0).1 : ℝ) / ((u 0).2 : ℝ) * 2 := by push_cast; ring
    rw [heq]
    exact (Nat.floor_lt (by positivity)).mpr (by exact_mod_cast hprod_lt)
  -- hbound has shape ⌊_ * (↑2 : ℝ)⌋₊ where 2 is ℕ-cast.
  change alpha2 u ≤ ⌊((u 0).1 : ℝ) / ((u 0).2 : ℝ) * ((2 : ℕ) : ℝ)⌋₊ at hbound
  omega

/-- `(5/2, 5/2)` is a discontinuity of `α₂`.
    Combines `alpha2_le_four_of_lt_left` with `indepNum_strongProduct_comm`
    so that *either* a strict drop at coord 0 or coord 1 gives `α₂ u ≤ 4`. -/
theorem alpha2_5o2_5o2_isDiscontinuity : IsDiscontinuity₂ pair5o2_5o2 := by
  intro u hu_valid hlt
  obtain ⟨⟨σ, hσ⟩, hnle⟩ := hlt
  have h_v_const : ∀ j, FracPair.toRat pair5o2_5o2 j = 5 / 2 := by
    intro j; fin_cases j <;> simp [FracPair.toRat, pair5o2_5o2]
  -- Both coords ≤ 5/2 (target is constant 5/2 — permutation drops out).
  have h_le : ∀ i, FracPair.toRat u i ≤ 5 / 2 := by
    intro i
    have h := hσ (σ.symm i)
    rw [σ.apply_symm_apply i] at h
    rw [h_v_const (σ.symm i)] at h
    exact h
  have h_le0 := h_le 0
  have h_le1 := h_le 1
  -- Strict drop somewhere: ¬lePerm v u with τ = 1 gives ∃ i, u.toRat i < 5/2.
  have h_some_lt :
      FracPair.toRat u 0 < 5 / 2 ∨ FracPair.toRat u 1 < 5 / 2 := by
    by_contra h_both
    push_neg at h_both
    obtain ⟨h_ge0, h_ge1⟩ := h_both
    apply hnle
    refine ⟨1, ?_⟩
    intro i
    fin_cases i
    · change FracPair.toRat pair5o2_5o2 0 ≤ FracPair.toRat u 0
      rw [h_v_const 0]; exact h_ge0
    · change FracPair.toRat pair5o2_5o2 1 ≤ FracPair.toRat u 1
      rw [h_v_const 1]; exact h_ge1
  rw [alpha2_pair5o2_5o2_eq]
  rcases h_some_lt with h0_lt | h1_lt
  · have := alpha2_le_four_of_lt_left hu_valid h0_lt h_le1
    omega
  · -- Use commutativity: alpha2 u = alpha2 (swap u).
    have hswap : alpha2 u = alpha2 (![u 1, u 0] : FracPair) := by
      change (fractionGraph (u 0).1 (u 0).2 ⊠ fractionGraph (u 1).1 (u 1).2).indepNum =
             (fractionGraph (u 1).1 (u 1).2 ⊠ fractionGraph (u 0).1 (u 0).2).indepNum
      exact indepNum_strongProduct_comm _ _
    rw [hswap]
    have hu_swap : Valid₂ (![u 1, u 0] : FracPair) := by
      intro i; fin_cases i
      · exact hu_valid 1
      · exact hu_valid 0
    have h0_swap : FracPair.toRat (![u 1, u 0] : FracPair) 0 < 5 / 2 := h1_lt
    have h1_swap : FracPair.toRat (![u 1, u 0] : FracPair) 1 ≤ 5 / 2 := h_le0
    have := alpha2_le_four_of_lt_left hu_swap h0_swap h1_swap
    omega


end Section6
