/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section2.ShannonCapacityBound
import AsymptoticSpectrumDistance.Section3.FractionGraphs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Data.Rat.Lemmas

/-!
# Convergence of Fraction Graphs

This file proves the Section-3 convergence theorems for fraction graphs in the
asymptotic spectrum distance:
1. Right-continuity: p_n/q_n → a/b from above implies E_{p_n/q_n} → E_{a/b}
2. Cauchy at irrationals: p_n/q_n → r (irrational) implies E_{p_n/q_n} is Cauchy
3. Non-completeness of finite graphs

The Section-4 circle-graph-limit theorems (Theorem 4.11, Theorem 4.12 TFAE,
sequential-closure equality) historically lived in this file but have been
relocated to `Section4/CircleGraphLimits.lean` so that Section 3 no longer
depends on Section 4 (matching the paper's dependency direction).

## Main results

* `fractionGraph_rightContinuous` : Right-continuity of spectral functions on E_{p/q}
* `fractionGraph_convergence_from_above` : Convergence from above to any fraction graph
* `fractionGraph_cauchy_irrational` : Cauchy sequences for irrational limits
* `fractionGraph_no_finite_limit` : Non-completeness of finite graphs
* `right_continuous`, `right_continuous_alpha`, `right_continuous_shannonCapacity`,
  `right_continuous_uniform` : ℕ+-form wrappers used by Main.lean.
* `sup_eq_inf_irrational_alpha`, `sup_eq_inf_irrational_shannonCapacity`,
  `distance_to_limit_irrational`, `no_finite_limit_existential`,
  `convergence_from_above`, `cauchy_irrational` : ℕ+-form wrappers used by Main.lean.

## References

* [de Boer, Buys, Zuiddam] Sections 3.2, 3.3
-/

namespace AsymptoticSpectrumDistance

open Universality FractionGraphBasic AsymptoticSpectrumGraphs SimpleGraph ShannonCapacity

/-! ### Convergence from Above -/

/-- Theorem 3.7(b): The right-continuity is uniform over all F ∈ X.
    For any ε > 0, there exists δ > 0 such that for all p/q with
    a/b ≤ p/q < a/b + δ, we have |F(E_{p/q}) - F(E_{a/b})| < ε for all F ∈ X.

    Proof: Use the Stern-Brocot successor (e, f) of (a, b) to construct a sequence
    p_n = e + n*a, q_n = f + n*b that approaches a/b from above.
    Each p_n/q_n is a Stern-Brocot neighbor of a/b, so we can use the distance bound.
    For any p/q between a/b and p_N/q_N, use monotonicity to bound the distance. -/
theorem fractionGraph_rightContinuous_uniform (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (h2b : 2 * b ≤ a) (hcoprime : Nat.Coprime a b) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ) (hp : 0 < p),
      (0 < q) → (2 * q ≤ p) →
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
      haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
      asympSpecDistance (FractionGraph' p q) (FractionGraph' a b) < ε := by
  intro ε hε
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  have ha_ge_2 : 2 ≤ a := by omega
  -- Step 1: Get the Stern-Brocot successor (e, f) of (a, b)
  obtain ⟨e, f, he_pos, hf_pos, hef_rel, hef_gt⟩ :=
    sternBrocotSuccessor_exists a b ha_ge_2 hb hcoprime
  -- Step 2: Define the sequence p_n = e + n*a, q_n = f + n*b
  -- Each satisfies p_n * b - q_n * a = e*b - f*a = 1
  -- Step 3: Find N such that a/(e + N*a - 1) < ε
  -- We need e + N*a - 1 > a/ε, so N > (a/ε - e + 1)/a
  have hbound : ∃ N : ℕ, 1 ≤ N ∧ (a : ℝ) / (e + N * a - 1) < ε := by
    -- For large N, e + N*a - 1 is arbitrarily large, so a/(e + N*a - 1) → 0
    have ha_pos' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
    -- First show (n * a) → ∞
    have h_na_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) * a) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_const ha_pos' tendsto_natCast_atTop_atTop
    -- Then (n * a + e) → ∞ (same as e + n * a)
    have h_ena_atTop : Filter.Tendsto (fun n : ℕ => (e : ℝ) + n * a) Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * a + e) Filter.atTop Filter.atTop :=
        Filter.Tendsto.atTop_add h_na_atTop tendsto_const_nhds
      convert h1 using 1
      ext n
      ring
    -- Then (e + n * a - 1) → ∞
    have h_denom_atTop : Filter.Tendsto (fun n : ℕ => (e : ℝ) + n * a - 1)
        Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun n : ℕ => (e : ℝ) + n * a + (-1)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.atTop_add h_ena_atTop tendsto_const_nhds
      refine Filter.Tendsto.congr ?_ h1
      intro n
      ring
    -- So 1/(e + n * a - 1) → 0
    have h_inv : Filter.Tendsto (fun n : ℕ => (e + n * a - 1 : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      Filter.Tendsto.inv_tendsto_atTop h_denom_atTop
    -- And a/(e + n * a - 1) → 0
    have htend : Filter.Tendsto (fun n : ℕ => (a : ℝ) / (e + n * a - 1))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (a : ℝ) * ((e : ℝ) + n * a - 1)⁻¹)
          Filter.atTop (nhds ((a : ℝ) * 0)) := by
        apply Filter.Tendsto.const_mul
        exact h_inv
      simp only [mul_zero] at h1
      refine Filter.Tendsto.congr ?_ h1
      intro n
      rw [div_eq_mul_inv]
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend ε hε
    use N + 1
    constructor
    · omega
    have hspec := hN (N + 1) (by omega)
    rw [Real.dist_eq, sub_zero] at hspec
    -- e + (N + 1) * a > 1 since e ≥ 1 and (N + 1) * a ≥ a ≥ 2
    have hpN_gt : e + (N + 1) * a > 1 := by
      have he_ge : e ≥ 1 := he_pos
      have hNa_ge : (N + 1) * a ≥ a := Nat.le_mul_of_pos_left a (Nat.succ_pos N)
      omega
    have hdenom_pos : (0 : ℝ) < e + (N + 1) * a - 1 := by
      have h1 : (1 : ℕ) < e + (N + 1) * a := hpN_gt
      have h2 : (1 : ℝ) < e + (N + 1) * a := by exact_mod_cast h1
      linarith
    have hdiv_pos : 0 < (a : ℝ) / (e + (N + 1) * a - 1) := div_pos ha_pos' hdenom_pos
    -- Normalize cast: ↑(N + 1) → ↑N + 1
    simp only [Nat.cast_add, Nat.cast_one] at hspec ⊢
    rw [abs_of_pos hdiv_pos] at hspec
    exact hspec
  obtain ⟨N, hN_ge_1, hN_bound⟩ := hbound
  -- Step 4: Define p_N = e + N*a, q_N = f + N*b
  set pN := e + N * a with hpN_def
  set qN := f + N * b with hqN_def
  -- Step 5: Set δ = p_N/q_N - a/b = 1/(b * q_N)
  have hqN_pos : 0 < qN := by
    simp only [hqN_def]
    omega
  have hpN_pos : 0 < pN := by
    simp only [hpN_def]
    omega
  have hδ_val : (pN : ℚ) / qN - (a : ℚ) / b = 1 / (b * qN) := by
    have hb_pos' : (0 : ℚ) < b := Nat.cast_pos.mpr hb
    have hqN_pos' : (0 : ℚ) < qN := Nat.cast_pos.mpr hqN_pos
    have hb_ne : (b : ℚ) ≠ 0 := ne_of_gt hb_pos'
    have hqN_ne : (qN : ℚ) ≠ 0 := ne_of_gt hqN_pos'
    -- pN * b - qN * a = (e + N*a)*b - (f + N*b)*a = eb + Nab - fa - Nab = eb - fa = 1
    have heq : pN * b - qN * a = 1 := by
      simp only [hpN_def, hqN_def]
      -- (e + N * a) * b - (f + N * b) * a = e * b - f * a = 1
      -- From hef_rel: e * b - f * a = 1
      have h4 : e * b = f * a + 1 := by omega
      -- Show (e + N * a) * b = (f + N * b) * a + 1
      have h5 : (e + N * a) * b = (f + N * b) * a + 1 := by
        have lhs : (e + N * a) * b = e * b + N * a * b := by ring
        have rhs : (f + N * b) * a = f * a + N * b * a := by ring
        rw [lhs, rhs, h4]
        ring
      omega
    field_simp
    -- Goal: pN * b - qN * a = 1 (after field_simp normalizes)
    -- We have heq : pN * b - qN * a = 1
    have hpN_b_ge : pN * b ≥ qN * a := by omega
    have h_cast : (pN : ℚ) * b - qN * a = ↑(pN * b - qN * a) := by
      rw [Nat.cast_sub hpN_b_ge]
      push_cast
      ring
    rw [h_cast, heq]
    norm_num
  use 1 / (b * qN)
  constructor
  · -- δ > 0
    have hbqN_pos : (0 : ℚ) < b * qN := by
      exact mul_pos (Nat.cast_pos.mpr hb) (Nat.cast_pos.mpr hqN_pos)
    exact one_div_pos.mpr hbqN_pos
  intro p q hp hq_pos h2q hab hdiff
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
  -- Step 6: Show p/q ≤ pN/qN
  have hpq_le_pNqN : (p : ℚ) / q ≤ (pN : ℚ) / qN := by
    have h1 : (p : ℚ) / q - (a : ℚ) / b < 1 / (b * qN) := hdiff
    have h2 : (a : ℚ) / b ≤ (p : ℚ) / q := hab
    -- From hδ_val: pN / qN = a / b + 1 / (b * qN)
    have hpN_qN : (pN : ℚ) / qN = (a : ℚ) / b + 1 / (b * qN) := by linarith [hδ_val]
    -- We have: p / q - a / b < 1 / (b * qN)
    -- So: p / q < a / b + 1 / (b * qN) = pN / qN
    linarith
  -- Step 7: If p/q = a/b, distance is 0
  by_cases heq_ab : (p : ℚ) / q = (a : ℚ) / b
  · -- p/q = a/b means p = a and q = b (up to common factor)
    -- Since p, q and a, b are all positive and the fractions are equal,
    -- we have p * b = q * a
    have hpb_qa : p * b = q * a := by
      have hb_pos' : (0 : ℚ) < b := Nat.cast_pos.mpr hb
      have hq_pos' : (0 : ℚ) < q := Nat.cast_pos.mpr hq_pos
      have hdiv : (p : ℚ) / q = (a : ℚ) / b := heq_ab
      have h : (p : ℚ) * b = q * a := by
        field_simp at hdiv
        linarith
      exact_mod_cast h
    -- When p*b = q*a (equal fractions), sandwich p/q between a/b and pN/qN
    -- and use monotonicity to bound the distance by ε
    haveI : NeZero pN := ⟨Nat.pos_iff_ne_zero.mp hpN_pos⟩
    -- First prove 2 * qN ≤ pN (needed for fractionGraph_ordering)
    have h2qN : 2 * qN ≤ pN := by
      simp only [hpN_def, hqN_def]
      have h2f_le_e : 2 * f ≤ e := by
        have heb : e * b = f * a + 1 := by omega
        have h2fb_le_eb : 2 * f * b ≤ e * b := by
          calc 2 * f * b = f * (2 * b) := by ring
            _ ≤ f * a := Nat.mul_le_mul_left f h2b
            _ ≤ f * a + 1 := Nat.le_succ _
            _ = e * b := heb.symm
        exact Nat.le_of_mul_le_mul_right h2fb_le_eb hb
      calc 2 * (f + N * b)
          = 2 * f + N * (2 * b) := by ring
        _ ≤ e + N * a := by
            have h2 : N * (2 * b) ≤ N * a := Nat.mul_le_mul_left N h2b
            omega
    calc asympSpecDistance (FractionGraph' p q) (FractionGraph' a b)
        ≤ asympSpecDistance (FractionGraph' pN qN) (FractionGraph' a b) := by
          -- Show element-wise: for all φ, |φ(E_{p/q}) - φ(E_{a/b})| ≤ |φ(E_{pN/qN}) - φ(E_{a/b})|
          simp only [asympSpecDistance, spectralDistanceSet]
          apply csSup_le
          · -- Nonemptiness
            obtain ⟨φ₀⟩ := spectralPoint_nonempty
            exact ⟨|φ₀.eval (FractionGraph' p q) - φ₀.eval (FractionGraph' a b)|, φ₀, rfl⟩
          · -- Upper bound
            intro x ⟨φ, hφ⟩
            rw [hφ]
            -- Get cohomomorphism chain from fraction ordering
            have hab_cohom :=
              (fractionGraph_ordering a b p q hb hq_pos h2b h2q).mp hab
            have hpq_pN_cohom :=
              (fractionGraph_ordering p q pN qN hq_pos hqN_pos h2q h2qN).mp hpq_le_pNqN
            -- By monotonicity: φ(E_{a/b}) ≤ φ(E_{p/q}) ≤ φ(E_{pN/qN})
            have h1 : φ.eval (FractionGraph' a b) ≤ φ.eval (FractionGraph' p q) :=
              φ.mono_cohom (FractionGraph' a b) (FractionGraph' p q) hab_cohom
            have h2 : φ.eval (FractionGraph' p q) ≤ φ.eval (FractionGraph' pN qN) :=
              φ.mono_cohom (FractionGraph' p q) (FractionGraph' pN qN) hpq_pN_cohom
            -- So difference is non-negative and bounded
            have hdiff_nonneg :
                0 ≤ φ.eval (FractionGraph' p q) - φ.eval (FractionGraph' a b) := by linarith
            have hdiff_pN_nonneg :
                0 ≤ φ.eval (FractionGraph' pN qN) - φ.eval (FractionGraph' a b) := by
              linarith
            rw [abs_of_nonneg hdiff_nonneg]
            -- Show the distance is in the sup set
            have hmem : |φ.eval (FractionGraph' pN qN) - φ.eval (FractionGraph' a b)| ∈
                {x | ∃ ψ : SpectralPoint, x = |ψ.eval (FractionGraph' pN qN) -
                  ψ.eval (FractionGraph' a b)|} := ⟨φ, rfl⟩
            have hbdd : BddAbove {x | ∃ ψ : SpectralPoint, x = |ψ.eval (FractionGraph' pN qN) -
                ψ.eval (FractionGraph' a b)|} := asympSpecDistance_bdd_above _ _
            have hsup_bound := le_csSup hbdd hmem
            rw [abs_of_nonneg hdiff_pN_nonneg] at hsup_bound
            linarith
      _ ≤ (a : ℝ) / (pN - 1) := by
          -- Use the Stern-Brocot distance bound
          haveI : NeZero pN := ⟨Nat.pos_iff_ne_zero.mp hpN_pos⟩
          have h2qN : 2 * qN ≤ pN := by
            simp only [hpN_def, hqN_def]
            -- Need: 2 * (f + N * b) ≤ e + N * a
            -- From 2 * b ≤ a and e * b - f * a = 1, we get 2 * f ≤ e
            have h2f_le_e : 2 * f ≤ e := by
              -- From e * b = f * a + 1 and 2 * b ≤ a
              have heb : e * b = f * a + 1 := by omega
              have h2fb_le_eb : 2 * f * b ≤ e * b := by
                calc 2 * f * b = f * (2 * b) := by ring
                  _ ≤ f * a := Nat.mul_le_mul_left f h2b
                  _ ≤ f * a + 1 := Nat.le_succ _
                  _ = e * b := heb.symm
              exact Nat.le_of_mul_le_mul_right h2fb_le_eb hb
            -- Now: 2 * (f + N * b) = 2f + 2Nb ≤ e + Na
            calc 2 * (f + N * b)
                = 2 * f + N * (2 * b) := by ring
              _ ≤ e + N * a := by
                  have h2 : N * (2 * b) ≤ N * a := Nat.mul_le_mul_left N h2b
                  omega
          have hpN_gt_a : a < pN := by
            simp only [hpN_def]
            -- a < e + N * a iff 0 < e + (N - 1) * a, which holds since e ≥ 1, N ≥ 1
            have hNa_ge_a : N * a ≥ a := Nat.le_mul_of_pos_left a hN_ge_1
            omega
          have hqN_gt_b : b < qN := by
            simp only [hqN_def]
            -- b < f + N * b iff 0 < f + (N - 1) * b, which holds since f ≥ 1, N ≥ 1
            have hNb_ge_b : N * b ≥ b := Nat.le_mul_of_pos_left b hN_ge_1
            omega
          have hneighbor : pN * b - qN * a = 1 := by
            simp only [hpN_def, hqN_def]
            -- (e + N * a) * b - (f + N * b) * a = e * b - f * a = 1
            have h4 : e * b = f * a + 1 := by omega
            have h5 : (e + N * a) * b = (f + N * b) * a + 1 := by
              have lhs : (e + N * a) * b = e * b + N * a * b := by ring
              have rhs : (f + N * b) * a = f * a + N * b * a := by ring
              rw [lhs, rhs, h4]
              ring
            omega
          have hN_bound' : (a : ℝ) / (pN - 1) < ε := by
            simp only [hpN_def] at hN_bound ⊢
            convert hN_bound using 2
            -- (e + N * a : ℝ) - 1 = e + N * a - 1
            simp only [Nat.cast_add, Nat.cast_mul]
          exact fractionGraph_distance_bound pN qN a b hqN_pos hb h2qN h2b
            hpN_gt_a hqN_gt_b hneighbor
      _ < ε := by
          simp only [hpN_def] at hN_bound ⊢
          convert hN_bound using 2
          simp only [Nat.cast_add, Nat.cast_mul]
  · -- p/q > a/b strictly
    have hpq_gt_ab : (a : ℚ) / b < (p : ℚ) / q := lt_of_le_of_ne hab (Ne.symm heq_ab)
    -- Use that p/q is between a/b and pN/qN, so distance is bounded by d(E_{pN/qN}, E_{a/b})
    haveI : NeZero pN := ⟨Nat.pos_iff_ne_zero.mp hpN_pos⟩
    -- First prove 2 * qN ≤ pN (needed for fractionGraph_ordering)
    have h2qN : 2 * qN ≤ pN := by
      simp only [hpN_def, hqN_def]
      have h2f_le_e : 2 * f ≤ e := by
        have heb : e * b = f * a + 1 := by omega
        have h2fb_le_eb : 2 * f * b ≤ e * b := by
          calc 2 * f * b = f * (2 * b) := by ring
            _ ≤ f * a := Nat.mul_le_mul_left f h2b
            _ ≤ f * a + 1 := Nat.le_succ _
            _ = e * b := heb.symm
        exact Nat.le_of_mul_le_mul_right h2fb_le_eb hb
      calc 2 * (f + N * b)
          = 2 * f + N * (2 * b) := by ring
        _ ≤ e + N * a := by
            have h2 : N * (2 * b) ≤ N * a := Nat.mul_le_mul_left N h2b
            omega
    calc asympSpecDistance (FractionGraph' p q) (FractionGraph' a b)
        ≤ asympSpecDistance (FractionGraph' pN qN) (FractionGraph' a b) := by
          -- Same monotonicity argument as first branch
          simp only [asympSpecDistance, spectralDistanceSet]
          apply csSup_le
          · obtain ⟨φ₀⟩ := spectralPoint_nonempty
            exact ⟨|φ₀.eval (FractionGraph' p q) - φ₀.eval (FractionGraph' a b)|, φ₀, rfl⟩
          · intro x ⟨φ, hφ⟩
            rw [hφ]
            have hab_cohom := (fractionGraph_ordering a b p q hb hq_pos h2b h2q).mp hab
            have hpq_pN_cohom :=
              (fractionGraph_ordering p q pN qN hq_pos hqN_pos h2q h2qN).mp hpq_le_pNqN
            have h1 : φ.eval (FractionGraph' a b) ≤ φ.eval (FractionGraph' p q) :=
              φ.mono_cohom (FractionGraph' a b) (FractionGraph' p q) hab_cohom
            have h2 : φ.eval (FractionGraph' p q) ≤ φ.eval (FractionGraph' pN qN) :=
              φ.mono_cohom (FractionGraph' p q) (FractionGraph' pN qN) hpq_pN_cohom
            have hdiff_nonneg :
                0 ≤ φ.eval (FractionGraph' p q) - φ.eval (FractionGraph' a b) := by
              linarith
            have hdiff_pN_nonneg :
                0 ≤ φ.eval (FractionGraph' pN qN) - φ.eval (FractionGraph' a b) := by
              linarith
            rw [abs_of_nonneg hdiff_nonneg]
            have hmem : |φ.eval (FractionGraph' pN qN) - φ.eval (FractionGraph' a b)| ∈
                {x | ∃ ψ : SpectralPoint, x = |ψ.eval (FractionGraph' pN qN) -
                  ψ.eval (FractionGraph' a b)|} := ⟨φ, rfl⟩
            have hbdd : BddAbove {x | ∃ ψ : SpectralPoint,
                x = |ψ.eval (FractionGraph' pN qN) -
                  ψ.eval (FractionGraph' a b)|} := asympSpecDistance_bdd_above _ _
            have hsup_bound := le_csSup hbdd hmem
            rw [abs_of_nonneg hdiff_pN_nonneg] at hsup_bound
            linarith
      _ ≤ (a : ℝ) / (pN - 1) := by
          haveI : NeZero pN := ⟨Nat.pos_iff_ne_zero.mp hpN_pos⟩
          have h2qN' : 2 * qN ≤ pN := by
            simp only [hpN_def, hqN_def]
            have h2f_le_e : 2 * f ≤ e := by
              have heb : e * b = f * a + 1 := by omega
              have h2fb_le_eb : 2 * f * b ≤ e * b := by
                calc 2 * f * b = f * (2 * b) := by ring
                  _ ≤ f * a := Nat.mul_le_mul_left f h2b
                  _ ≤ f * a + 1 := Nat.le_succ _
                  _ = e * b := heb.symm
              exact Nat.le_of_mul_le_mul_right h2fb_le_eb hb
            calc 2 * (f + N * b)
                = 2 * f + N * (2 * b) := by ring
              _ ≤ e + N * a := by
                  have h2 : N * (2 * b) ≤ N * a := Nat.mul_le_mul_left N h2b
                  omega
          have hpN_gt_a : a < pN := by
            simp only [hpN_def]
            -- a < e + N * a iff 0 < e + (N - 1) * a, which holds since e ≥ 1, N ≥ 1
            have hNa_ge_a : N * a ≥ a := Nat.le_mul_of_pos_left a hN_ge_1
            omega
          have hqN_gt_b : b < qN := by
            simp only [hqN_def]
            -- b < f + N * b iff 0 < f + (N - 1) * b, which holds since f ≥ 1, N ≥ 1
            have hNb_ge_b : N * b ≥ b := Nat.le_mul_of_pos_left b hN_ge_1
            omega
          have hneighbor : pN * b - qN * a = 1 := by
            simp only [hpN_def, hqN_def]
            have h4 : e * b = f * a + 1 := by omega
            have h5 : (e + N * a) * b = (f + N * b) * a + 1 := by
              have lhs : (e + N * a) * b = e * b + N * a * b := by ring
              have rhs : (f + N * b) * a = f * a + N * b * a := by ring
              rw [lhs, rhs, h4]
              ring
            omega
          exact fractionGraph_distance_bound pN qN a b hqN_pos hb h2qN h2b
            hpN_gt_a hqN_gt_b hneighbor
      _ < ε := by
          simp only [hpN_def] at hN_bound ⊢
          convert hN_bound using 2
          simp only [Nat.cast_add, Nat.cast_mul]

/-- Theorem 3.7(a): For any spectral function F ∈ X ∪ {α, Θ}, the map
    p/q ↦ F(E_{p/q}) is right-continuous.

    This follows from the uniform version (Theorem 3.7(b)) via spectralPoint_dist_le. -/
theorem fractionGraph_rightContinuous (φ : SpectralPoint) :
    ∀ (a b : ℕ) (ha : 0 < a) (_hb : 0 < b) (_h2b : 2 * b ≤ a) (_hcoprime : Nat.Coprime a b),
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ) (hp : 0 < p),
      (0 < q) → (2 * q ≤ p) →
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
      haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
      |φ.eval (FractionGraph' p q) - φ.eval (FractionGraph' a b)| < ε := by
  intro a b ha hb h2b hcoprime ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := fractionGraph_rightContinuous_uniform a b ha hb h2b hcoprime ε hε
  use δ, hδ_pos
  intro p q hp hq_pos h2q hab hdiff
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  have hspec := hδ p q hp hq_pos h2q hab hdiff
  calc |φ.eval (FractionGraph' p q) - φ.eval (FractionGraph' a b)|
      ≤ asympSpecDistance (FractionGraph' p q) (FractionGraph' a b) :=
          spectralPoint_dist_le _ _ φ
    _ < ε := hspec

/-- Theorem 3.7(c): If p_n/q_n converges to a/b from above, then
    E_{p_n/q_n} converges to E_{a/b} in asymptotic spectrum distance.

    This follows from the uniform right-continuity (Theorem 3.7(b)). -/
theorem fractionGraph_convergence_from_above (a b : ℕ) [NeZero a]
    (hb : 0 < b) (h2b : 2 * b ≤ a) (hcoprime : Nat.Coprime a b)
    (ps qs : ℕ → ℕ) [∀ n, NeZero (ps n)]
    (hqs_pos : ∀ n, 0 < qs n)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hfrom_above : ∀ n, (a : ℚ) / b ≤ (ps n : ℚ) / qs n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℚ) / qs n) Filter.atTop (nhds ((a : ℚ) / b))) :
    ConvergesTo (fun n => FractionGraph' (ps n) (qs n)) (FractionGraph' a b) := by
  unfold ConvergesTo
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Use uniform right-continuity to get δ
  have ha_pos : 0 < a := NeZero.pos a
  obtain ⟨δ, hδ_pos, hδ⟩ := fractionGraph_rightContinuous_uniform a b ha_pos hb h2b hcoprime ε hε
  -- Since ps n / qs n → a/b, eventually |ps n / qs n - a/b| < δ
  rw [Metric.tendsto_atTop] at hconv
  have hδ_pos' : (0 : ℝ) < δ := by exact_mod_cast hδ_pos
  obtain ⟨N, hN⟩ := hconv δ hδ_pos'
  use N
  intro n hn
  -- Need to show dist(E_{ps n / qs n}, E_{a/b}) < ε
  have hps_pos : 0 < ps n := NeZero.pos (ps n)
  have hdist_rat := hN n hn
  rw [Rat.dist_eq] at hdist_rat
  -- Apply uniform right-continuity
  have hfrom_above_n := hfrom_above n
  have hdiff : (ps n : ℚ) / qs n - (a : ℚ) / b < δ := by
    have h := abs_lt.mp hdist_rat
    have h2 := h.2
    -- h2 : ↑((ps n : ℚ) / (qs n)) - ↑((a : ℚ) / b) < ↑δ  in ℝ
    rw [← Rat.cast_sub] at h2
    -- Now h2 : ↑((ps n : ℚ) / (qs n) - (a : ℚ) / b) < ↑δ
    exact_mod_cast h2
  have hspec := hδ (ps n) (qs n) hps_pos (hqs_pos n) (h2qs n) hfrom_above_n hdiff
  rw [Real.dist_0_eq_abs, abs_of_nonneg (asympSpecDistance_nonneg _ _)]
  exact hspec

/-- If two graphs have cohomomorphisms in both directions, their asymptotic
    spectrum distance is zero. -/
theorem asympSpecDistance_eq_zero_of_mutual_cohom (G H : Graph)
    (hGH : G.graph ≤_G H.graph) (hHG : H.graph ≤_G G.graph) :
    asympSpecDistance G H = 0 := by
  apply le_antisymm _ (asympSpecDistance_nonneg G H)
  rw [asympSpecDistance]
  apply csSup_le
  · exact ⟨_, chibar_spectralPoint, rfl⟩
  · rintro x ⟨φ, rfl⟩
    have h1 := φ.mono_cohom G H hGH
    have h2 := φ.mono_cohom H G hHG
    simp [abs_le]; constructor <;> linarith

/-- Theorem 3.7 (without coprimality): If p_n/q_n → a/b from above with
    a/b ≥ 2, then E_{p_n/q_n} converges to E_{a/b}. -/
theorem fractionGraph_convergence_from_above' (a b : ℕ)
    (hb : 0 < b) (h2b : 2 * b ≤ a)
    (ps qs : ℕ → ℕ)
    (hqs_pos : ∀ n, 0 < qs n)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hfrom_above : ∀ n, (a : ℚ) / b ≤ (ps n : ℚ) / qs n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℚ) / qs n) Filter.atTop
      (nhds ((a : ℚ) / b))) :
    haveI : NeZero a := ⟨by omega⟩
    haveI : ∀ n, NeZero (ps n) := fun n => ⟨by have := hqs_pos n; have := h2qs n; omega⟩
    ConvergesTo (fun n => FractionGraph' (ps n) (qs n))
      (FractionGraph' a b) := by
  haveI : NeZero a := ⟨by omega⟩
  haveI : ∀ n, NeZero (ps n) := fun n => ⟨by have := hqs_pos n; have := h2qs n; omega⟩
  -- Reduce to coprime case
  set g := Nat.gcd a b
  set a' := a / g
  set b' := b / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left b (NeZero.pos a)
  have ha'_pos : 0 < a' := Nat.div_pos (Nat.le_of_dvd (NeZero.pos a) (Nat.gcd_dvd_left a b)) hg_pos
  have hb'_pos : 0 < b' := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg_pos
  have ha_eq : a = a' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left a b)).symm
  have hb_eq : b = b' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right a b)).symm
  have h2b' : 2 * b' ≤ a' :=
    Nat.le_of_mul_le_mul_right (by nlinarith [ha_eq, hb_eq]) hg_pos
  have hcoprime : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hg_pos
  have hab_eq : (a : ℚ) / b = (a' : ℚ) / b' := by
    rw [ha_eq, hb_eq, Nat.cast_mul, Nat.cast_mul]
    field_simp
  haveI : NeZero a' := ⟨Nat.pos_iff_ne_zero.mp ha'_pos⟩
  -- Apply coprime version to get convergence to E_{a'/b'}
  have hconv' : ConvergesTo (fun n => FractionGraph' (ps n) (qs n))
      (FractionGraph' a' b') :=
    fractionGraph_convergence_from_above a' b' hb'_pos h2b' hcoprime ps qs
      hqs_pos h2qs (fun n => hab_eq ▸ hfrom_above n) (hab_eq ▸ hconv)
  -- E_{a/b} and E_{a'/b'} have distance 0 (mutual cohomomorphisms via ordering)
  have hle1 : (a' : ℚ) / b' ≤ (a : ℚ) / b := le_of_eq hab_eq.symm
  have hle2 : (a : ℚ) / b ≤ (a' : ℚ) / b' := le_of_eq hab_eq
  have hcohom1 := (fractionGraph_ordering a' b' a b hb'_pos hb h2b' h2b).mp hle1
  have hcohom2 := (fractionGraph_ordering a b a' b' hb hb'_pos h2b h2b').mp hle2
  have hdist_zero := asympSpecDistance_eq_zero_of_mutual_cohom
    (FractionGraph' a' b') (FractionGraph' a b)
    (by simpa using hcohom1) (by simpa using hcohom2)
  -- Transfer convergence: d(Gs n, E_{a/b}) = d(Gs n, E_{a'/b'}) since d(a/b, a'/b') = 0
  have hdist_zero' : asympSpecDistance (FractionGraph' a b) (FractionGraph' a' b') = 0 :=
    (asympSpecDistance_symm _ _).trans hdist_zero
  have heq : ∀ n, asympSpecDistance (FractionGraph' (ps n) (qs n)) (FractionGraph' a b) =
      asympSpecDistance (FractionGraph' (ps n) (qs n)) (FractionGraph' a' b') := by
    intro n
    apply le_antisymm
    · linarith [asympSpecDistance_triangle (FractionGraph' (ps n) (qs n))
        (FractionGraph' a' b') (FractionGraph' a b),
        asympSpecDistance_nonneg (FractionGraph' (ps n) (qs n)) (FractionGraph' a' b')]
    · linarith [asympSpecDistance_triangle (FractionGraph' (ps n) (qs n))
        (FractionGraph' a b) (FractionGraph' a' b'),
        asympSpecDistance_nonneg (FractionGraph' (ps n) (qs n)) (FractionGraph' a b)]
  unfold ConvergesTo at hconv' ⊢
  exact (Filter.Tendsto.congr (fun n => (heq n).symm) hconv')

/-! ### Construction of Converging Sequence -/

/-- Given coprime a, b with a/b ≥ 2, there exists a sequence p_n, q_n
    that converges to a/b from above.

    Construction: Find a', b' with a'·b - b'·a = 1 using extended Euclidean algorithm.
    Then p_n = a' + a·n, q_n = b' + b·n gives p_n·b - q_n·a = 1, so p_n/q_n > a/b
    and p_n/q_n → a/b as n → ∞. -/
theorem convergingSequence_exists (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (_hcoprime : Nat.Coprime a b) (h2 : 2 * b ≤ a) :
    ∃ pq : ℕ → ℕ × ℕ,
      (∀ n, 0 < (pq n).1 ∧ 0 < (pq n).2) ∧
      (∀ n, 2 * (pq n).2 ≤ (pq n).1) ∧
      (∀ n, (a : ℚ) / b < ((pq n).1 : ℚ) / (pq n).2) ∧
      Filter.Tendsto (fun n => ((pq n).1 : ℚ) / (pq n).2) Filter.atTop (nhds ((a : ℚ) / b)) := by
  -- Simple construction: p_n = a*(n+1) + 1, q_n = b*(n+1)
  -- Then p_n * b - q_n * a = b > 0, so p_n/q_n > a/b
  -- And p_n/q_n → a/b as n → ∞
  use fun n => (a * (n + 1) + 1, b * (n + 1))
  constructor
  · -- Positivity: p_n > 0 and q_n > 0
    intro n
    constructor
    · -- a * (n + 1) + 1 > 0
      have : a * (n + 1) ≥ 0 := Nat.zero_le _
      omega
    · -- b * (n + 1) > 0
      exact Nat.mul_pos hb (Nat.succ_pos n)
  constructor
  · -- 2 * q_n ≤ p_n: 2 * b * (n+1) ≤ a * (n+1) + 1
    intro n
    simp only
    -- 2 * b ≤ a, so 2 * b * (n+1) ≤ a * (n+1) ≤ a * (n+1) + 1
    calc 2 * (b * (n + 1))
        = (2 * b) * (n + 1) := by ring
      _ ≤ a * (n + 1) := Nat.mul_le_mul_right (n + 1) h2
      _ ≤ a * (n + 1) + 1 := Nat.le_succ _
  constructor
  · -- p_n/q_n > a/b
    intro n
    simp only
    have hb_pos : (0 : ℚ) < b := Nat.cast_pos.mpr hb
    have hqn_pos : (0 : ℚ) < (b * (n + 1) : ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hb (Nat.succ_pos n))
    rw [div_lt_div_iff₀ hb_pos hqn_pos]
    -- Need: a * (b * (n + 1)) < (a * (n + 1) + 1) * b
    push_cast
    ring_nf
    -- a * b * (n + 1) < a * b * (n + 1) + b
    have : (0 : ℚ) < b := hb_pos
    linarith
  · -- Convergence: (a * (n+1) + 1) / (b * (n+1)) → a/b
    have hb_pos : (0 : ℚ) < b := Nat.cast_pos.mpr hb
    have ha_pos : (0 : ℚ) < a := Nat.cast_pos.mpr ha
    -- Rewrite: (a * (n+1) + 1) / (b * (n+1)) = a/b + 1/(b * (n+1))
    have heq : ∀ n : ℕ, ((a * (n + 1) + 1 : ℕ) : ℚ) / ((b * (n + 1) : ℕ) : ℚ) =
        (a : ℚ) / b + 1 / ((b : ℚ) * ((n : ℚ) + 1)) := by
      intro n
      have hbn_pos : (0 : ℚ) < (b * (n + 1) : ℕ) :=
        Nat.cast_pos.mpr (Nat.mul_pos hb (Nat.succ_pos n))
      have hbn_ne : ((b * (n + 1) : ℕ) : ℚ) ≠ 0 := ne_of_gt hbn_pos
      have hb_ne : (b : ℚ) ≠ 0 := ne_of_gt hb_pos
      have hn1_ne : (n : ℚ) + 1 ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    simp_rw [heq]
    -- Show a/b + 1/(b*(n+1)) → a/b, i.e., 1/(b*(n+1)) → 0
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℚ) / ((b : ℚ) * ((n : ℚ) + 1)))
        Filter.atTop (nhds 0) := by
      have htend_n1 : Filter.Tendsto (fun n : ℕ => (n : ℚ) + 1)
          Filter.atTop Filter.atTop := by
        have h1 : Filter.Tendsto (fun n : ℕ => (n : ℚ)) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop
        have h2 : Filter.Tendsto (fun _ : ℕ => (1 : ℚ)) Filter.atTop (nhds 1) :=
          tendsto_const_nhds
        exact h1.atTop_add h2
      have htend : Filter.Tendsto (fun n : ℕ => ((n : ℚ) + 1) * (b : ℚ))
          Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_mul_const hb_pos
        exact htend_n1
      have htend' : Filter.Tendsto (fun n : ℕ => (b : ℚ) * ((n : ℚ) + 1))
          Filter.atTop Filter.atTop := by
        have : (fun n : ℕ => (b : ℚ) * ((n : ℚ) + 1)) =
            (fun n : ℕ => ((n : ℚ) + 1) * (b : ℚ)) := by
          ext n; ring
        rw [this]
        exact htend
      have hinv : Filter.Tendsto (fun n : ℕ => ((b : ℚ) * ((n : ℚ) + 1))⁻¹)
          Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp htend'
      convert hinv using 1
      ext n
      rw [one_div]
    have h2 := Filter.Tendsto.const_add ((a : ℚ) / b) h1
    simp only [add_zero] at h2
    exact h2

/-- Given coprime a, b with a/b ≥ 2, construct the sequence p_n, q_n
    that converges to a/b from above with p_n q' - q_n p' = 1. -/
noncomputable def convergingSequence (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcoprime : Nat.Coprime a b) (h2 : 2 * b ≤ a) :
    { pq : ℕ → ℕ × ℕ //
      (∀ n, 0 < (pq n).1 ∧ 0 < (pq n).2) ∧
      (∀ n, 2 * (pq n).2 ≤ (pq n).1) ∧
      (∀ n, (a : ℚ) / b < ((pq n).1 : ℚ) / (pq n).2) ∧
      Filter.Tendsto (fun n => ((pq n).1 : ℚ) / (pq n).2) Filter.atTop (nhds ((a : ℚ) / b)) } :=
  ⟨(convergingSequence_exists a b ha hb hcoprime h2).choose,
   (convergingSequence_exists a b ha hb hcoprime h2).choose_spec⟩

/-! ### Cauchy Sequences for Irrational Limits -/

/-- Continued fraction convergents of a real converge to the real number. -/
theorem tendsto_convergent_real (r : ℝ) :
    Filter.Tendsto (fun n => (r.convergent n : ℝ)) Filter.atTop (nhds r) := by
  have hconv := GenContFract.of_convergence (v := r)
  have hfun :
      (fun n => (GenContFract.of r).convs n) = fun n => (r.convergent n : ℝ) := by
    funext n
    simpa using (Real.convs_eq_convergent r n)
  simpa [hfun] using hconv

theorem convergent_gt_two_eventually (r : ℝ) (hr : 2 < r) :
    ∀ᶠ n in Filter.atTop, (2 : ℝ) < (r.convergent n : ℝ) := by
  have hconv := tendsto_convergent_real r
  have hpos : 0 < r - 2 := by linarith
  rcases (Metric.tendsto_atTop.1 hconv) (r - 2) hpos with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ?_
  refine ⟨N, ?_⟩
  intro n hn
  have hn' := hN n hn
  clear hN
  rw [Real.dist_eq] at hn'
  have hlt : r - (r - 2) < (r.convergent n : ℝ) := by
    have : (r.convergent n : ℝ) - r > -(r - 2) := by
      have := abs_lt.mp hn'
      linarith
    linarith
  linarith

theorem convergent_gt_two_eventually_nat (r : ℝ) (hr : 2 < r) :
    ∃ N : ℕ, ∀ n ≥ N, (2 : ℝ) < (r.convergent n : ℝ) := by
  have h := convergent_gt_two_eventually r hr
  rcases (Filter.eventually_atTop.1 h) with ⟨N, hN⟩
  exact ⟨N, hN⟩

private theorem stream_some_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    ∃ ifp : GenContFract.IntFractPair ℝ,
      GenContFract.IntFractPair.stream r n = some ifp ∧ ifp.fr ≠ 0 := by
  by_cases hnone : GenContFract.IntFractPair.stream r n = none
  · cases n with
    | zero =>
        have hnone' := hnone
        simp [GenContFract.IntFractPair.stream_zero] at hnone'
    | succ n =>
        have hterm : (GenContFract.of r).TerminatedAt n :=
          (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 hnone
        have hterminates : (GenContFract.of r).Terminates := ⟨n, hterm⟩
        rcases (GenContFract.terminates_iff_rat r).1 hterminates with ⟨q, hq⟩
        exact (False.elim ((hirr.ne_rat q) hq))
  · have hsome : ∃ ifp, GenContFract.IntFractPair.stream r n = some ifp := by
      cases hstream : GenContFract.IntFractPair.stream r n with
      | none => exact False.elim (hnone hstream)
      | some ifp => exact ⟨ifp, rfl⟩
    rcases hsome with ⟨ifp, hstream⟩
    refine ⟨ifp, hstream, ?_⟩
    by_contra hfr
    have hnone' : GenContFract.IntFractPair.stream r (n + 1) = none :=
      GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero hstream hfr
    have hterm : (GenContFract.of r).TerminatedAt n :=
      (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 hnone'
    have hterminates : (GenContFract.of r).Terminates := ⟨n, hterm⟩
    rcases (GenContFract.terminates_iff_rat r).1 hterminates with ⟨q, hq⟩
    exact (False.elim ((hirr.ne_rat q) hq))

theorem not_terminatedAt_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    ¬(GenContFract.of r).TerminatedAt n := by
  intro hterm
  have hnone :
      GenContFract.IntFractPair.stream r (n + 1) = none :=
    (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).1 hterm
  rcases stream_some_of_irrational r hirr (n + 1) with ⟨ifp, hsome, _⟩
  have hnone' := hnone
  simp [hsome] at hnone'

private theorem contsAux_b_pos_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    0 < ((GenContFract.of r).contsAux (n + 1)).b := by
  have hcond : n + 1 ≤ 1 ∨ ¬(GenContFract.of r).TerminatedAt (n - 1) := by
    cases n with
    | zero =>
        left
        simp
    | succ n =>
        right
        have hnot : ¬(GenContFract.of r).TerminatedAt n :=
          not_terminatedAt_of_irrational r hirr n
        simpa using hnot
  have hfib_le :
      (Nat.fib (n + 1) : ℝ) ≤ ((GenContFract.of r).contsAux (n + 1)).b := by
    simpa using (GenContFract.fib_le_of_contsAux_b (v := r) (n := n + 1) hcond)
  have hfib_pos : 0 < (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.2 (Nat.succ_pos _)
  exact lt_of_lt_of_le hfib_pos hfib_le

private theorem convs_even_lt_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    (GenContFract.of r).convs (2 * n) < r := by
  rcases stream_some_of_irrational r hirr (2 * n) with ⟨ifp, hstream, hfr_ne⟩
  let g := GenContFract.of r
  let B := (g.contsAux (2 * n + 1)).b
  let pB := (g.contsAux (2 * n)).b
  have hsub :
      r - g.convs (2 * n) = (-1) ^ (2 * n) / (B * (ifp.fr⁻¹ * B + pB)) := by
    simpa [g, B, pB, hfr_ne] using
      (GenContFract.sub_convs_eq (v := r) (n := 2 * n) hstream)
  have hB_pos : 0 < B := by
    simpa [g, B] using contsAux_b_pos_of_irrational r hirr (2 * n)
  have hpB_nonneg : 0 ≤ pB := by
    simpa [g, pB] using (GenContFract.zero_le_of_contsAux_b (v := r) (n := 2 * n))
  have hifp_pos : 0 < ifp.fr := by
    have hnonneg := GenContFract.IntFractPair.nth_stream_fr_nonneg (v := r)
      (n := 2 * n) hstream
    exact lt_of_le_of_ne hnonneg (by symm; exact hfr_ne)
  have hsum_pos : 0 < ifp.fr⁻¹ * B + pB := by
    have hmul_pos : 0 < ifp.fr⁻¹ * B := by
      exact mul_pos (inv_pos.mpr hifp_pos) hB_pos
    exact add_pos_of_pos_of_nonneg hmul_pos hpB_nonneg
  have hden_pos : 0 < B * (ifp.fr⁻¹ * B + pB) := by
    exact mul_pos hB_pos hsum_pos
  have hsub' :
      r - g.convs (2 * n) = (1 : ℝ) / (B * (ifp.fr⁻¹ * B + pB)) := by
    simpa [pow_mul] using hsub
  have hpos : 0 < r - g.convs (2 * n) := by
    have : 0 < (1 : ℝ) / (B * (ifp.fr⁻¹ * B + pB)) := by
      exact one_div_pos.mpr hden_pos
    simpa [hsub'] using this
  linarith

private theorem convs_odd_gt_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    r < (GenContFract.of r).convs (2 * n + 1) := by
  rcases stream_some_of_irrational r hirr (2 * n + 1) with ⟨ifp, hstream, hfr_ne⟩
  let g := GenContFract.of r
  let B := (g.contsAux (2 * n + 2)).b
  let pB := (g.contsAux (2 * n + 1)).b
  have hsub :
      r - g.convs (2 * n + 1) =
        (-1) ^ (2 * n + 1) / (B * (ifp.fr⁻¹ * B + pB)) := by
    simpa [g, B, pB, hfr_ne] using
      (GenContFract.sub_convs_eq (v := r) (n := 2 * n + 1) hstream)
  have hB_pos : 0 < B := by
    simpa [g, B] using contsAux_b_pos_of_irrational r hirr (2 * n + 1)
  have hpB_nonneg : 0 ≤ pB := by
    simpa [g, pB] using
      (GenContFract.zero_le_of_contsAux_b (v := r) (n := 2 * n + 1))
  have hifp_pos : 0 < ifp.fr := by
    have hnonneg := GenContFract.IntFractPair.nth_stream_fr_nonneg (v := r)
      (n := 2 * n + 1) hstream
    exact lt_of_le_of_ne hnonneg (by symm; exact hfr_ne)
  have hsum_pos : 0 < ifp.fr⁻¹ * B + pB := by
    have hmul_pos : 0 < ifp.fr⁻¹ * B := by
      exact mul_pos (inv_pos.mpr hifp_pos) hB_pos
    exact add_pos_of_pos_of_nonneg hmul_pos hpB_nonneg
  have hden_pos : 0 < B * (ifp.fr⁻¹ * B + pB) := by
    exact mul_pos hB_pos hsum_pos
  have hsub' :
      r - g.convs (2 * n + 1) =
        (-1 : ℝ) / (B * (ifp.fr⁻¹ * B + pB)) := by
    simpa [pow_add, pow_mul] using hsub
  have hneg : r - g.convs (2 * n + 1) < 0 := by
    have hneg1 : (-1 : ℝ) < 0 := by norm_num
    have hdiv : (-1 : ℝ) / (B * (ifp.fr⁻¹ * B + pB)) < 0 := by
      exact div_neg_of_neg_of_pos hneg1 hden_pos
    simpa [hsub'] using hdiv
  linarith

theorem convergent_even_lt_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    (r.convergent (2 * n) : ℝ) < r := by
  have hconv :
      (GenContFract.of r).convs (2 * n) = (r.convergent (2 * n) : ℝ) := by
    simpa using (Real.convs_eq_convergent r (2 * n))
  simpa [hconv] using convs_even_lt_irrational r hirr n

theorem convergent_odd_gt_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    r < (r.convergent (2 * n + 1) : ℝ) := by
  have hconv :
      (GenContFract.of r).convs (2 * n + 1) =
        (r.convergent (2 * n + 1) : ℝ) := by
    simpa using (Real.convs_eq_convergent r (2 * n + 1))
  simpa [hconv] using convs_odd_gt_irrational r hirr n

noncomputable def convergentNum (r : ℝ) (n : ℕ) : ℤ :=
  (r.convergent n).num

noncomputable def convergentDen (r : ℝ) (n : ℕ) : ℕ :=
  (r.convergent n).den

theorem convergent_num_den (r : ℝ) (n : ℕ) :
    (convergentNum r n : ℚ) / (convergentDen r n : ℚ) = r.convergent n := by
  simpa [convergentNum, convergentDen] using (Rat.num_div_den (r.convergent n))

theorem convergent_num_den_coprime (r : ℝ) (n : ℕ) :
    Nat.Coprime (Int.natAbs (r.convergent n).num) (r.convergent n).den := by
  simpa using (r.convergent n).reduced

theorem convergent_cast_eq_nums_div_dens (r : ℝ) (n : ℕ) :
    (r.convergent n : ℝ) =
      (GenContFract.of r).nums n / (GenContFract.of r).dens n := by
  have hconv : (GenContFract.of r).convs n = (r.convergent n : ℝ) := by
    simpa using (Real.convs_eq_convergent r n)
  have hconv' :
      (GenContFract.of r).convs n =
        (GenContFract.of r).nums n / (GenContFract.of r).dens n := by
    simpa using (GenContFract.conv_eq_num_div_den (g := GenContFract.of r) (n := n))
  exact hconv.symm.trans hconv'


theorem nums_dens_det_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    (GenContFract.of r).nums n * (GenContFract.of r).dens (n + 1) -
      (GenContFract.of r).dens n * (GenContFract.of r).nums (n + 1) =
        (-1) ^ (n + 1) := by
  have hnot : ¬(GenContFract.of r).TerminatedAt n :=
    not_terminatedAt_of_irrational r hirr n
  simpa using (SimpContFract.determinant (s := SimpContFract.of r) (n := n) hnot)

private theorem nums_int_pair_of_irrational (r : ℝ) (hirr : Irrational r) :
    ∀ n,
      (∃ z : ℤ, (GenContFract.of r).nums n = (z : ℝ)) ∧
      (∃ z : ℤ, (GenContFract.of r).nums (n + 1) = (z : ℝ)) := by
  classical
  refine Nat.rec ?base ?step
  · -- n = 0
    have h0 :
        (GenContFract.of r).nums 0 = (⌊r⌋ : ℝ) := by
      simp [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
    have hnot0 : ¬(GenContFract.of r).TerminatedAt 0 :=
      not_terminatedAt_of_irrational r hirr 0
    have hnone0 : (GenContFract.of r).s.get? 0 ≠ none := by
      simpa [GenContFract.terminatedAt_iff_s_none] using hnot0
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp hnone0
    have hgp_a : gp.a = (1 : ℝ) := by
      simpa using
        (GenContFract.of_partNum_eq_one
          (v := r)
          (n := 0)
          (a := gp.a)
          (GenContFract.partNum_eq_s_a (g := GenContFract.of r) (n := 0) hgp))
    obtain ⟨z_b, hz_b⟩ :=
      GenContFract.exists_int_eq_of_partDen
        (v := r)
        (n := 0)
        (b := gp.b)
        (GenContFract.partDen_eq_s_b (g := GenContFract.of r) (n := 0) hgp)
    have h1 :
        (GenContFract.of r).nums 1 = ((z_b * ⌊r⌋ + 1 : ℤ) : ℝ) := by
      have hfirst :
          (GenContFract.of r).nums 1 = gp.b * (GenContFract.of r).h + gp.a := by
        simpa using
          (GenContFract.first_num_eq (g := GenContFract.of r) (gp := gp) (zeroth_s_eq := hgp))
      simp [hfirst, hz_b, hgp_a, GenContFract.of_h_eq_floor]
    exact ⟨⟨⌊r⌋, h0⟩, ⟨z_b * ⌊r⌋ + 1, h1⟩⟩
  · -- inductive step
    intro n ih
    rcases ih with ⟨⟨z_n, hz_n⟩, ⟨z_n1, hz_n1⟩⟩
    have hnot : ¬(GenContFract.of r).TerminatedAt (n + 1) :=
      not_terminatedAt_of_irrational r hirr (n + 1)
    have hnone : (GenContFract.of r).s.get? (n + 1) ≠ none := by
      simpa [GenContFract.terminatedAt_iff_s_none] using hnot
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp hnone
    have hgp_a : gp.a = (1 : ℝ) := by
      simpa using
        (GenContFract.of_partNum_eq_one
          (v := r)
          (n := n + 1)
          (a := gp.a)
          (GenContFract.partNum_eq_s_a (g := GenContFract.of r) (n := n + 1) hgp))
    obtain ⟨z_b, hz_b⟩ :=
      GenContFract.exists_int_eq_of_partDen
        (v := r)
        (n := n + 1)
        (b := gp.b)
        (GenContFract.partDen_eq_s_b (g := GenContFract.of r) (n := n + 1) hgp)
    have hrec :
        (GenContFract.of r).nums (n + 2) =
          gp.b * (GenContFract.of r).nums (n + 1) +
            gp.a * (GenContFract.of r).nums n := by
      simpa using
        (GenContFract.nums_recurrence (g := GenContFract.of r) (n := n) (gp := gp)
          (succ_nth_s_eq := hgp) (nth_num_eq := rfl) (succ_nth_num_eq := rfl))
    have hnext :
        (GenContFract.of r).nums (n + 2) = ((z_b * z_n1 + z_n : ℤ) : ℝ) := by
      -- rewrite recurrence using the integer casts
      simp [hrec, hz_b, hgp_a, hz_n, hz_n1]
    exact ⟨⟨z_n1, hz_n1⟩, ⟨z_b * z_n1 + z_n, hnext⟩⟩

private theorem dens_int_pair_of_irrational (r : ℝ) (hirr : Irrational r) :
    ∀ n,
      (∃ z : ℤ, (GenContFract.of r).dens n = (z : ℝ)) ∧
      (∃ z : ℤ, (GenContFract.of r).dens (n + 1) = (z : ℝ)) := by
  classical
  refine Nat.rec ?base ?step
  · -- n = 0
    have h0 : (GenContFract.of r).dens 0 = (1 : ℝ) := by
      simp [GenContFract.zeroth_den_eq_one]
    have hnot0 : ¬(GenContFract.of r).TerminatedAt 0 :=
      not_terminatedAt_of_irrational r hirr 0
    have hnone0 : (GenContFract.of r).s.get? 0 ≠ none := by
      simpa [GenContFract.terminatedAt_iff_s_none] using hnot0
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp hnone0
    obtain ⟨z_b, hz_b⟩ :=
      GenContFract.exists_int_eq_of_partDen
        (v := r)
        (n := 0)
        (b := gp.b)
        (GenContFract.partDen_eq_s_b (g := GenContFract.of r) (n := 0) hgp)
    have h1 : (GenContFract.of r).dens 1 = (z_b : ℝ) := by
      have hfirst :
          (GenContFract.of r).dens 1 = gp.b := by
        exact
          GenContFract.first_den_eq (g := GenContFract.of r) (gp := gp) (zeroth_s_eq := hgp)
      simp [hfirst, hz_b]
    have h0' : (GenContFract.of r).dens 0 = ((1 : ℤ) : ℝ) := by
      simp [h0]
    exact ⟨⟨1, h0'⟩, ⟨z_b, h1⟩⟩
  · -- inductive step
    intro n ih
    rcases ih with ⟨⟨z_n, hz_n⟩, ⟨z_n1, hz_n1⟩⟩
    have hnot : ¬(GenContFract.of r).TerminatedAt (n + 1) :=
      not_terminatedAt_of_irrational r hirr (n + 1)
    have hnone : (GenContFract.of r).s.get? (n + 1) ≠ none := by
      simpa [GenContFract.terminatedAt_iff_s_none] using hnot
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp hnone
    have hgp_a : gp.a = (1 : ℝ) := by
      simpa using
        (GenContFract.of_partNum_eq_one
          (v := r)
          (n := n + 1)
          (a := gp.a)
          (GenContFract.partNum_eq_s_a (g := GenContFract.of r) (n := n + 1) hgp))
    obtain ⟨z_b, hz_b⟩ :=
      GenContFract.exists_int_eq_of_partDen
        (v := r)
        (n := n + 1)
        (b := gp.b)
        (GenContFract.partDen_eq_s_b (g := GenContFract.of r) (n := n + 1) hgp)
    have hrec :
        (GenContFract.of r).dens (n + 2) =
          gp.b * (GenContFract.of r).dens (n + 1) +
            gp.a * (GenContFract.of r).dens n := by
      simpa using
        (GenContFract.dens_recurrence (g := GenContFract.of r) (n := n) (gp := gp)
          (succ_nth_s_eq := hgp) (nth_den_eq := rfl) (succ_nth_den_eq := rfl))
    have hnext :
        (GenContFract.of r).dens (n + 2) = ((z_b * z_n1 + z_n : ℤ) : ℝ) := by
      simp [hrec, hz_b, hgp_a, hz_n, hz_n1]
    exact ⟨⟨z_n1, hz_n1⟩, ⟨z_b * z_n1 + z_n, hnext⟩⟩

theorem nums_int_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    ∃ z : ℤ, (GenContFract.of r).nums n = (z : ℝ) :=
  (nums_int_pair_of_irrational r hirr n).1

theorem dens_int_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    ∃ z : ℤ, (GenContFract.of r).dens n = (z : ℝ) :=
  (dens_int_pair_of_irrational r hirr n).1

theorem nums_dens_det_irrational_int (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    ∃ A B A1 B1 : ℤ,
      (GenContFract.of r).nums n = (A : ℝ) ∧
      (GenContFract.of r).dens n = (B : ℝ) ∧
      (GenContFract.of r).nums (n + 1) = (A1 : ℝ) ∧
      (GenContFract.of r).dens (n + 1) = (B1 : ℝ) ∧
      A * B1 - B * A1 = (-1) ^ (n + 1) := by
  rcases nums_int_of_irrational r hirr n with ⟨A, hA⟩
  rcases dens_int_of_irrational r hirr n with ⟨B, hB⟩
  rcases nums_int_of_irrational r hirr (n + 1) with ⟨A1, hA1⟩
  rcases dens_int_of_irrational r hirr (n + 1) with ⟨B1, hB1⟩
  have hdet := nums_dens_det_irrational r hirr n
  have hdet' : ((A * B1 - B * A1 : ℤ) : ℝ) = (-1) ^ (n + 1) := by
    simpa [hA, hB, hA1, hB1] using hdet
  have hdetZ : A * B1 - B * A1 = (-1) ^ (n + 1) := by
    exact_mod_cast hdet'
  exact ⟨A, B, A1, B1, hA, hB, hA1, hB1, hdetZ⟩

theorem dens_pos_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    0 < (GenContFract.of r).dens n := by
  have hpos := contsAux_b_pos_of_irrational r hirr n
  have hden :
      (GenContFract.of r).dens n = ((GenContFract.of r).contsAux (n + 1)).b := by
    calc
      (GenContFract.of r).dens n = ((GenContFract.of r).conts n).b := by
        simpa using (GenContFract.den_eq_conts_b (g := GenContFract.of r) (n := n))
      _ = ((GenContFract.of r).contsAux (n + 1)).b := by
        simpa using
          congrArg (fun p => p.b)
            (GenContFract.nth_cont_eq_succ_nth_contAux (g := GenContFract.of r) (n := n))
  simpa [hden] using hpos

theorem dens_ge_fib_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    (Nat.fib (n + 1) : ℝ) ≤ (GenContFract.of r).dens n := by
  have hcond : n + 1 ≤ 1 ∨ ¬(GenContFract.of r).TerminatedAt (n - 1) := by
    cases n with
    | zero =>
        left
        simp
    | succ n =>
        right
        have hnot : ¬(GenContFract.of r).TerminatedAt n :=
          not_terminatedAt_of_irrational r hirr n
        simpa using hnot
  have hfib_le :
      (Nat.fib (n + 1) : ℝ) ≤ ((GenContFract.of r).contsAux (n + 1)).b := by
    simpa using (GenContFract.fib_le_of_contsAux_b (v := r) (n := n + 1) hcond)
  have hden :
      (GenContFract.of r).dens n = ((GenContFract.of r).contsAux (n + 1)).b := by
    calc
      (GenContFract.of r).dens n = ((GenContFract.of r).conts n).b := by
        simpa using (GenContFract.den_eq_conts_b (g := GenContFract.of r) (n := n))
      _ = ((GenContFract.of r).contsAux (n + 1)).b := by
        simpa using
          congrArg (fun p => p.b)
            (GenContFract.nth_cont_eq_succ_nth_contAux (g := GenContFract.of r) (n := n))
  simpa [hden] using hfib_le

theorem dens_lt_succ_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    (GenContFract.of r).dens (n + 1) < (GenContFract.of r).dens (n + 2) := by
  have hnot : ¬(GenContFract.of r).TerminatedAt (n + 1) :=
    not_terminatedAt_of_irrational r hirr (n + 1)
  have hnone : (GenContFract.of r).s.get? (n + 1) ≠ none := by
    simpa [GenContFract.terminatedAt_iff_s_none] using hnot
  obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp hnone
  have hgp_a : gp.a = 1 := by
    exact GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a (g := GenContFract.of r)
      (n := n + 1) hgp)
  have hgp_b_ge : (1 : ℝ) ≤ gp.b := by
    have hpartDen : (GenContFract.of r).partDens.get? (n + 1) = some gp.b := by
      simpa using
        (GenContFract.partDen_eq_s_b (g := GenContFract.of r) (n := n + 1) hgp)
    simpa using (GenContFract.of_one_le_get?_partDen (v := r) (n := n + 1) hpartDen)
  have hrec :
      (GenContFract.of r).dens (n + 2) =
        gp.b * (GenContFract.of r).dens (n + 1) +
          gp.a * (GenContFract.of r).dens n := by
    simpa using
      (GenContFract.dens_recurrence (g := GenContFract.of r) (n := n) (gp := gp)
        (succ_nth_s_eq := hgp) (nth_den_eq := rfl) (succ_nth_den_eq := rfl))
  have hpos : 0 < (GenContFract.of r).dens n :=
    dens_pos_of_irrational r hirr n
  have hlt :
      (GenContFract.of r).dens (n + 1) <
        gp.b * (GenContFract.of r).dens (n + 1) +
          gp.a * (GenContFract.of r).dens n := by
    have hmul_ge : (GenContFract.of r).dens (n + 1) ≤
        gp.b * (GenContFract.of r).dens (n + 1) := by
      have hden_pos : 0 ≤ (GenContFract.of r).dens (n + 1) := by
        exact le_of_lt (dens_pos_of_irrational r hirr (n + 1))
      have hgp_b_ge' : (1 : ℝ) ≤ gp.b := hgp_b_ge
      calc
        (GenContFract.of r).dens (n + 1)
            = (1 : ℝ) * (GenContFract.of r).dens (n + 1) := by ring
        _ ≤ gp.b * (GenContFract.of r).dens (n + 1) := by
            exact mul_le_mul_of_nonneg_right hgp_b_ge' hden_pos
    have hgp_a_pos : 0 < (gp.a : ℝ) := by
      simp [hgp_a]
    have hsum_pos : 0 < gp.a * (GenContFract.of r).dens n := by
      exact mul_pos hgp_a_pos hpos
    exact lt_of_le_of_lt hmul_ge (lt_add_of_pos_right _ hsum_pos)
  simpa [hrec] using hlt

theorem two_mul_dens_lt_nums_of_convergent_gt_two (r : ℝ) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent n : ℝ)) :
    2 * (GenContFract.of r).dens n < (GenContFract.of r).nums n := by
  have hconv := convergent_cast_eq_nums_div_dens r n
  have hgt' :
      (2 : ℝ) < (GenContFract.of r).nums n / (GenContFract.of r).dens n := by
    simpa [hconv] using hgt
  have hden_pos := dens_pos_of_irrational r hirr n
  have hden_ne : (GenContFract.of r).dens n ≠ 0 := ne_of_gt hden_pos
  have hmul := (mul_lt_mul_of_pos_right hgt' hden_pos)
  -- Clear denominators using positivity of the denominator.
  simpa [div_eq_mul_inv, mul_assoc, hden_ne] using hmul

theorem dens_int_pos_of_irrational (r : ℝ) (hirr : Irrational r) (n : ℕ) :
    ∃ B : ℤ, (GenContFract.of r).dens n = (B : ℝ) ∧ 0 < B := by
  rcases dens_int_of_irrational r hirr n with ⟨B, hB⟩
  have hposR : 0 < (B : ℝ) := by
    simpa [hB] using dens_pos_of_irrational r hirr n
  have hposZ : 0 < B := by
    exact_mod_cast hposR
  exact ⟨B, hB, hposZ⟩

private theorem two_mul_dens_int_lt_nums_of_convergent_gt_two (r : ℝ) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent n : ℝ)) :
    ∃ A B : ℤ,
      (GenContFract.of r).nums n = (A : ℝ) ∧
      (GenContFract.of r).dens n = (B : ℝ) ∧
      0 < B ∧ 2 * B < A := by
  rcases nums_int_of_irrational r hirr n with ⟨A, hA⟩
  rcases dens_int_pos_of_irrational r hirr n with ⟨B, hB, hBpos⟩
  have hltR := two_mul_dens_lt_nums_of_convergent_gt_two r hirr n hgt
  have hltR' : (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
    simpa [hA, hB] using hltR
  have hltZ : 2 * B < A := by
    exact_mod_cast hltR'
  exact ⟨A, B, hA, hB, hBpos, hltZ⟩

theorem convergent_nat_data_of_gt_two (r : ℝ) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent n : ℝ)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2 * b ≤ a ∧
      (r.convergent n : ℝ) = (a : ℝ) / b ∧
      Nat.fib (n + 1) ≤ b := by
  rcases two_mul_dens_int_lt_nums_of_convergent_gt_two r hirr n hgt with
    ⟨A, B, hA, hB, hBpos, hltZ⟩
  have hApos : 0 < A := by
    have : 0 < 2 * B := by linarith
    exact lt_trans this hltZ
  have hA_nonneg : 0 ≤ A := le_of_lt hApos
  have hB_nonneg : 0 ≤ B := le_of_lt hBpos
  set a : ℕ := Int.toNat A
  set b : ℕ := Int.toNat B
  have hA_nat : (a : ℤ) = A := by
    simp [a, Int.toNat_of_nonneg hA_nonneg]
  have hB_nat : (b : ℤ) = B := by
    simp [b, Int.toNat_of_nonneg hB_nonneg]
  have ha_pos : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha_zero
    have : (a : ℤ) = 0 := by simp [ha_zero]
    have : A = 0 := by simpa [hA_nat] using this
    exact (ne_of_gt hApos) this
  have hb_pos : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro hb_zero
    have : (b : ℤ) = 0 := by simp [hb_zero]
    have : B = 0 := by simpa [hB_nat] using this
    exact (ne_of_gt hBpos) this
  have hltZ' : (2 * b : ℤ) < a := by
    have : (2 * b : ℤ) = 2 * B := by
      simp [hB_nat]
    have : (a : ℤ) = A := hA_nat
    simpa [this, hB_nat] using hltZ
  have hltNat : 2 * b < a := by
    exact_mod_cast hltZ'
  have hratio : (r.convergent n : ℝ) = (a : ℝ) / b := by
    have hconv := convergent_cast_eq_nums_div_dens r n
    have hA_real : (a : ℝ) = (A : ℝ) := by
      exact_mod_cast hA_nat
    have hB_real : (b : ℝ) = (B : ℝ) := by
      exact_mod_cast hB_nat
    calc
      (r.convergent n : ℝ) = (A : ℝ) / (B : ℝ) := by
        simpa [hA, hB] using hconv
      _ = (a : ℝ) / b := by
        simp [hA_real, hB_real]
  have hfib_le : (Nat.fib (n + 1) : ℝ) ≤ (B : ℝ) := by
    have hden := dens_ge_fib_of_irrational r hirr n
    simpa [hB] using hden
  have hfib_le_nat : Nat.fib (n + 1) ≤ b := by
    have hB_real : (b : ℝ) = (B : ℝ) := by
      exact_mod_cast hB_nat
    have hfib_le' : (Nat.fib (n + 1) : ℝ) ≤ (b : ℝ) := by
      simpa [hB_real] using hfib_le
    exact_mod_cast hfib_le'
  exact ⟨a, b, ha_pos, hb_pos, le_of_lt hltNat, hratio, hfib_le_nat⟩

theorem even_odd_convergent_pair_data_large (r : ℝ) (hr : 2 < r)
    (hirr : Irrational r) (N : ℕ) :
    ∃ n a b a1 b1 : ℕ,
      0 < a ∧ 0 < b ∧ 0 < a1 ∧ 0 < b1 ∧
      2 * b ≤ a ∧ 2 * b1 ≤ a1 ∧
      (r.convergent (2 * n) : ℝ) = (a : ℝ) / b ∧
      (r.convergent (2 * n + 1) : ℝ) = (a1 : ℝ) / b1 ∧
      a1 * b - b1 * a = 1 ∧ b < b1 ∧ N ≤ a1 ∧ N ≤ 2 * n := by
  classical
  rcases convergent_gt_two_eventually_nat r hr with ⟨N0, hN0⟩
  set n : ℕ := max N0 (N + 5)
  have hgt_even : (2 : ℝ) < (r.convergent (2 * n) : ℝ) := by
    have hN0_le' : N0 ≤ 2 * n := by
      calc
        N0 ≤ n := le_max_left _ _
        _ ≤ 2 * n := by omega
    exact hN0 _ hN0_le'
  have hgt_odd : (2 : ℝ) < (r.convergent (2 * n + 1) : ℝ) := by
    have hN0_le' : N0 ≤ 2 * n + 1 := by
      calc
        N0 ≤ n := le_max_left _ _
        _ ≤ 2 * n + 1 := by omega
    exact hN0 _ hN0_le'
  rcases nums_dens_det_irrational_int r hirr (2 * n) with
    ⟨A, B, A1, B1, hA, hB, hA1, hB1, hdet⟩
  have hBposR : 0 < (B : ℝ) := by
    simpa [hB] using dens_pos_of_irrational r hirr (2 * n)
  have hBpos : 0 < B := by exact_mod_cast hBposR
  have hB1posR : 0 < (B1 : ℝ) := by
    simpa [hB1] using dens_pos_of_irrational r hirr (2 * n + 1)
  have hB1pos : 0 < B1 := by exact_mod_cast hB1posR
  have hlt_even :
      (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
    have hltR := two_mul_dens_lt_nums_of_convergent_gt_two r hirr (2 * n) hgt_even
    simpa [hA, hB] using hltR
  have hlt_odd :
      (2 : ℝ) * (B1 : ℝ) < (A1 : ℝ) := by
    have hltR := two_mul_dens_lt_nums_of_convergent_gt_two r hirr (2 * n + 1) hgt_odd
    simpa [hA1, hB1] using hltR
  have hlt_evenZ : 2 * B < A := by exact_mod_cast hlt_even
  have hlt_oddZ : 2 * B1 < A1 := by exact_mod_cast hlt_odd
  have hApos : 0 < A := by
    have h2Bpos : 0 < 2 * B := by nlinarith
    exact lt_trans h2Bpos hlt_evenZ
  have hA1pos : 0 < A1 := by
    have h2Bpos : 0 < 2 * B1 := by nlinarith
    exact lt_trans h2Bpos hlt_oddZ
  set a : ℕ := Int.toNat A
  set b : ℕ := Int.toNat B
  set a1 : ℕ := Int.toNat A1
  set b1 : ℕ := Int.toNat B1
  have hA_nat : (a : ℤ) = A := by
    have hA_nonneg : 0 ≤ A := le_of_lt hApos
    simp [a, Int.toNat_of_nonneg hA_nonneg]
  have hB_nat : (b : ℤ) = B := by
    have hB_nonneg : 0 ≤ B := le_of_lt hBpos
    simp [b, Int.toNat_of_nonneg hB_nonneg]
  have hA1_nat : (a1 : ℤ) = A1 := by
    have hA1_nonneg : 0 ≤ A1 := le_of_lt hA1pos
    simp [a1, Int.toNat_of_nonneg hA1_nonneg]
  have hB1_nat : (b1 : ℤ) = B1 := by
    have hB1_nonneg : 0 ≤ B1 := le_of_lt hB1pos
    simp [b1, Int.toNat_of_nonneg hB1_nonneg]
  have ha_pos : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha_zero
    have : (a : ℤ) = 0 := by simp [ha_zero]
    have : A = 0 := by simpa [hA_nat] using this
    exact (ne_of_gt hApos) this
  have hb_pos : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro hb_zero
    have : (b : ℤ) = 0 := by simp [hb_zero]
    have : B = 0 := by simpa [hB_nat] using this
    exact (ne_of_gt hBpos) this
  have ha1_pos : 0 < a1 := by
    apply Nat.pos_of_ne_zero
    intro ha_zero
    have : (a1 : ℤ) = 0 := by simp [ha_zero]
    have : A1 = 0 := by simpa [hA1_nat] using this
    exact (ne_of_gt hA1pos) this
  have hb1_pos : 0 < b1 := by
    apply Nat.pos_of_ne_zero
    intro hb_zero
    have : (b1 : ℤ) = 0 := by simp [hb_zero]
    have : B1 = 0 := by simpa [hB1_nat] using this
    exact (ne_of_gt hB1pos) this
  have hltNat : 2 * b < a := by
    have hltZ' : (2 : ℤ) * (b : ℤ) < (a : ℤ) := by
      simpa [hA_nat, hB_nat] using hlt_evenZ
    exact_mod_cast hltZ'
  have hltNat1 : 2 * b1 < a1 := by
    have hltZ' : (2 : ℤ) * (b1 : ℤ) < (a1 : ℤ) := by
      simpa [hA1_nat, hB1_nat] using hlt_oddZ
    exact_mod_cast hltZ'
  have hratio : (r.convergent (2 * n) : ℝ) = (a : ℝ) / b := by
    have hconv := convergent_cast_eq_nums_div_dens r (2 * n)
    have hA_real : (a : ℝ) = (A : ℝ) := by exact_mod_cast hA_nat
    have hB_real : (b : ℝ) = (B : ℝ) := by exact_mod_cast hB_nat
    calc
      (r.convergent (2 * n) : ℝ) =
          (GenContFract.of r).nums (2 * n) / (GenContFract.of r).dens (2 * n) := hconv
      _ = (A : ℝ) / (B : ℝ) := by simp [hA, hB]
      _ = (a : ℝ) / b := by simp [hA_real, hB_real]
  have hratio1 : (r.convergent (2 * n + 1) : ℝ) = (a1 : ℝ) / b1 := by
    have hconv := convergent_cast_eq_nums_div_dens r (2 * n + 1)
    have hA_real : (a1 : ℝ) = (A1 : ℝ) := by exact_mod_cast hA1_nat
    have hB_real : (b1 : ℝ) = (B1 : ℝ) := by exact_mod_cast hB1_nat
    calc
      (r.convergent (2 * n + 1) : ℝ) =
          (GenContFract.of r).nums (2 * n + 1) / (GenContFract.of r).dens (2 * n + 1) := hconv
      _ = (A1 : ℝ) / (B1 : ℝ) := by simp [hA1, hB1]
      _ = (a1 : ℝ) / b1 := by simp [hA_real, hB_real]
  have hdetZ : A1 * B - B1 * A = 1 := by
    have hOdd : Odd (2 * n + 1) := by
      refine ⟨n, by ring⟩
    have hpow : (-1 : ℤ) ^ (2 * n + 1) = -1 := hOdd.neg_one_pow
    have hdet' : A * B1 - B * A1 = -1 := by simpa [hpow] using hdet
    linarith
  have hdetZ' : (a1 : ℤ) * (b : ℤ) - (b1 : ℤ) * (a : ℤ) = 1 := by
    simpa [hA_nat, hB_nat, hA1_nat, hB1_nat] using hdetZ
  have hleZ : (b1 : ℤ) * (a : ℤ) ≤ (a1 : ℤ) * (b : ℤ) := by linarith
  have hle : b1 * a ≤ a1 * b := by exact_mod_cast hleZ
  have hdetNat : a1 * b - b1 * a = 1 := by
    apply (Int.ofNat.inj _)
    simp [Int.ofNat_sub hle, hdetZ']
  have hb_lt : b < b1 := by
    have hden_lt : (GenContFract.of r).dens (2 * n) <
        (GenContFract.of r).dens (2 * n + 1) := by
      have hn_pos : 0 < n := by
        have hN5_pos : 0 < N + 5 := by omega
        exact lt_of_lt_of_le hN5_pos (le_max_right _ _)
      have hpos : 0 < 2 * n := by
        exact Nat.mul_pos (by omega) hn_pos
      have h1 : 2 * n - 1 + 1 = 2 * n := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hpos)
      have h2 : 2 * n - 1 + 2 = 2 * n + 1 := by
        calc
          2 * n - 1 + 2 = (2 * n - 1 + 1) + 1 := by omega
          _ = 2 * n + 1 := by simp [h1]
      simpa [h1, h2] using dens_lt_succ_of_irrational r hirr (2 * n - 1)
    have hB_lt : (B : ℝ) < (B1 : ℝ) := by
      simpa [hB, hB1] using hden_lt
    have hB_ltZ : B < B1 := by exact_mod_cast hB_lt
    have hB_ltNat : b < b1 := by
      have hB_nat' : (b : ℤ) = B := hB_nat
      have hB1_nat' : (b1 : ℤ) = B1 := hB1_nat
      have : (b : ℤ) < (b1 : ℤ) := by simpa [hB_nat', hB1_nat'] using hB_ltZ
      exact_mod_cast this
    exact hB_ltNat
  have hN_le_fib : N ≤ Nat.fib (2 * n + 2) := by
    have hN_le_n : N ≤ n := by
      have hN_le_N5 : N ≤ N + 5 := by omega
      exact le_trans hN_le_N5 (le_max_right _ _)
    have hN_le_n' : N ≤ 2 * n + 2 := by
      calc
        N ≤ n := hN_le_n
        _ ≤ 2 * n + 2 := by omega
    have hfib_ge : 2 * n + 2 ≤ Nat.fib (2 * n + 2) := by
      have hfive : 5 ≤ 2 * n + 2 := by omega
      exact Nat.le_fib_self hfive
    exact le_trans hN_le_n' hfib_ge
  have hfib_le_b1 : Nat.fib (2 * n + 2) ≤ b1 := by
    have hden := dens_ge_fib_of_irrational r hirr (2 * n + 1)
    have hden' : (Nat.fib (2 * n + 2) : ℝ) ≤ (B1 : ℝ) := by
      simpa [Nat.add_assoc, hB1] using hden
    have hB1_real : (b1 : ℝ) = (B1 : ℝ) := by exact_mod_cast hB1_nat
    have hfib_le' : (Nat.fib (2 * n + 2) : ℝ) ≤ (b1 : ℝ) := by
      simpa [hB1_real] using hden'
    exact_mod_cast hfib_le'
  have hN_le_b1 : N ≤ b1 := le_trans hN_le_fib hfib_le_b1
  have hN_le_a1 : N ≤ a1 := by
    have hb1_le_a1 : b1 ≤ a1 := by
      calc
        b1 ≤ 2 * b1 := by omega
        _ ≤ a1 := le_of_lt hltNat1
    exact le_trans hN_le_b1 hb1_le_a1
  exact ⟨n, a, b, a1, b1, ha_pos, hb_pos, ha1_pos, hb1_pos,
    le_of_lt hltNat, le_of_lt hltNat1, hratio, hratio1, hdetNat, hb_lt, hN_le_a1,
    by omega⟩

/-- Convergent pair data with `N ≤ a` (odd/even pair at indices `2n-1, 2n`).
    For irrational `r > 2`, returns a Stern-Brocot neighbor pair of convergent
    fractions with all denominators ≥ 1 and numerators ≥ `N`. -/
theorem odd_even_convergent_pair_data_large_both (r : ℝ) (hr : 2 < r)
    (hirr : Irrational r) (N : ℕ) :
    ∃ n a b a1 b1 : ℕ,
      0 < a ∧ 0 < b ∧ 0 < a1 ∧ 0 < b1 ∧
      2 * b ≤ a ∧ 2 * b1 ≤ a1 ∧
      (r.convergent (2 * n - 1) : ℝ) = (a : ℝ) / b ∧
      (r.convergent (2 * n) : ℝ) = (a1 : ℝ) / b1 ∧
      (a1 : ℤ) * b - (b1 : ℤ) * a = -1 ∧ b < b1 ∧ N ≤ a ∧ N ≤ a1 := by
  -- Set n = max N0 (N + 5) to ensure n ≥ N0 (so convergents are > 2) and n ≥ N + 5
  classical
  rcases convergent_gt_two_eventually_nat r hr with ⟨N0, hN0⟩
  set n : ℕ := max N0 (N + 5)
  have hn_pos : 0 < n := by
    have hN5_pos : 0 < N + 5 := by omega
    exact lt_of_lt_of_le hN5_pos (le_max_right _ _)
  have hidx : 2 * n - 1 + 1 = 2 * n := by omega
  have hgt_odd : (2 : ℝ) < (r.convergent (2 * n - 1) : ℝ) := by
    have hN0_le' : N0 ≤ 2 * n - 1 := by
      calc
        N0 ≤ n := le_max_left _ _
        _ ≤ 2 * n - 1 := by omega
    exact hN0 _ hN0_le'
  have hgt_even : (2 : ℝ) < (r.convergent (2 * n) : ℝ) := by
    have hN0_le' : N0 ≤ 2 * n := by
      calc
        N0 ≤ n := le_max_left _ _
        _ ≤ 2 * n := by omega
    exact hN0 _ hN0_le'
  rcases nums_dens_det_irrational_int r hirr (2 * n - 1) with
    ⟨A, B, A1, B1, hA, hB, hA1, hB1, hdet⟩
  have hA1' : (GenContFract.of r).nums (2 * n) = A1 := by simpa [hidx] using hA1
  have hB1' : (GenContFract.of r).dens (2 * n) = B1 := by simpa [hidx] using hB1
  have hBposR : 0 < (B : ℝ) := by simpa [hB] using dens_pos_of_irrational r hirr (2 * n - 1)
  have hBpos : 0 < B := by exact_mod_cast hBposR
  have hB1posR : 0 < (B1 : ℝ) := by
    have h := dens_pos_of_irrational r hirr (2 * n)
    simpa [hB1'] using h
  have hB1pos : 0 < B1 := by exact_mod_cast hB1posR
  have hlt_odd : (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
    have hltR := two_mul_dens_lt_nums_of_convergent_gt_two r hirr (2 * n - 1) hgt_odd
    simpa [hA, hB] using hltR
  have hlt_even : (2 : ℝ) * (B1 : ℝ) < (A1 : ℝ) := by
    have hltR := two_mul_dens_lt_nums_of_convergent_gt_two r hirr (2 * n) hgt_even
    simpa [hA1', hB1'] using hltR
  have hlt_oddZ : 2 * B < A := by exact_mod_cast hlt_odd
  have hlt_evenZ : 2 * B1 < A1 := by exact_mod_cast hlt_even
  have hApos : 0 < A := by
    have h2Bpos : 0 < 2 * B := by nlinarith
    exact lt_trans h2Bpos hlt_oddZ
  have hA1pos : 0 < A1 := by
    have h2Bpos : 0 < 2 * B1 := by nlinarith
    exact lt_trans h2Bpos hlt_evenZ
  set a : ℕ := Int.toNat A
  set b : ℕ := Int.toNat B
  set a1 : ℕ := Int.toNat A1
  set b1 : ℕ := Int.toNat B1
  have hA_nat : (a : ℤ) = A := Int.toNat_of_nonneg (le_of_lt hApos)
  have hB_nat : (b : ℤ) = B := Int.toNat_of_nonneg (le_of_lt hBpos)
  have hA1_nat : (a1 : ℤ) = A1 := Int.toNat_of_nonneg (le_of_lt hA1pos)
  have hB1_nat : (b1 : ℤ) = B1 := Int.toNat_of_nonneg (le_of_lt hB1pos)
  have ha_pos : 0 < a := by
    apply Nat.pos_of_ne_zero; intro ha_zero
    have h1 : (a : ℤ) = 0 := by simp [ha_zero]
    have : A = 0 := by simpa [hA_nat] using h1
    exact (ne_of_gt hApos) this
  have hb_pos : 0 < b := by
    apply Nat.pos_of_ne_zero; intro hb_zero
    have h1 : (b : ℤ) = 0 := by simp [hb_zero]
    have : B = 0 := by simpa [hB_nat] using h1
    exact (ne_of_gt hBpos) this
  have ha1_pos : 0 < a1 := by
    apply Nat.pos_of_ne_zero; intro ha_zero
    have h1 : (a1 : ℤ) = 0 := by simp [ha_zero]
    have : A1 = 0 := by simpa [hA1_nat] using h1
    exact (ne_of_gt hA1pos) this
  have hb1_pos : 0 < b1 := by
    apply Nat.pos_of_ne_zero; intro hb_zero
    have h1 : (b1 : ℤ) = 0 := by simp [hb_zero]
    have : B1 = 0 := by simpa [hB1_nat] using h1
    exact (ne_of_gt hB1pos) this
  have hltNat : 2 * b < a := by
    exact_mod_cast (by simpa [hA_nat, hB_nat] using hlt_oddZ : (2 : ℤ) * b < a)
  have hltNat1 : 2 * b1 < a1 := by
    exact_mod_cast (by simpa [hA1_nat, hB1_nat] using hlt_evenZ : (2 : ℤ) * b1 < a1)
  have hratio : (r.convergent (2 * n - 1) : ℝ) = (a : ℝ) / b := by
    have hconv := convergent_cast_eq_nums_div_dens r (2 * n - 1)
    have hA_real : (a : ℝ) = (A : ℝ) := by exact_mod_cast hA_nat
    have hB_real : (b : ℝ) = (B : ℝ) := by exact_mod_cast hB_nat
    simp only [hconv, hA, hB, hA_real, hB_real]
  have hratio1 : (r.convergent (2 * n) : ℝ) = (a1 : ℝ) / b1 := by
    have hconv := convergent_cast_eq_nums_div_dens r (2 * n)
    have hA_real : (a1 : ℝ) = (A1 : ℝ) := by exact_mod_cast hA1_nat
    have hB_real : (b1 : ℝ) = (B1 : ℝ) := by exact_mod_cast hB1_nat
    simp only [hconv, hA1', hB1', hA_real, hB_real]
  have hdetZ : A1 * B - B1 * A = -1 := by
    have hEven : Even (2 * n) := even_two_mul n
    have hpow : (-1 : ℤ) ^ (2 * n - 1 + 1) = 1 := by simp only [hidx, hEven.neg_one_pow]
    have hdet' : A * B1 - B * A1 = 1 := by simpa [hpow] using hdet
    linarith
  have hdetZ' : (a1 : ℤ) * (b : ℤ) - (b1 : ℤ) * (a : ℤ) = -1 := by
    simpa [hA_nat, hB_nat, hA1_nat, hB1_nat] using hdetZ
  have hb_lt : b < b1 := by
    have hden_lt : (GenContFract.of r).dens (2 * n - 1) <
        (GenContFract.of r).dens (2 * n - 1 + 1) := by
      have h1 : 2 * n - 1 - 1 + 1 = 2 * n - 1 := by omega
      have h2 : 2 * n - 1 - 1 + 2 = 2 * n - 1 + 1 := by omega
      simpa [h1, h2] using dens_lt_succ_of_irrational r hirr (2 * n - 1 - 1)
    have hB_lt : (B : ℝ) < (B1 : ℝ) := by simpa [hB, hB1] using hden_lt
    have hB_ltZ : B < B1 := by exact_mod_cast hB_lt
    exact_mod_cast (by simpa [hB_nat, hB1_nat] using hB_ltZ : (b : ℤ) < b1)
  -- N ≤ a via: N ≤ n ≤ 2n ≤ fib(2n) ≤ b ≤ a
  have hN_le_n : N ≤ n := le_trans (by omega : N ≤ N + 5) (le_max_right _ _)
  have hN_le_fib : N ≤ Nat.fib (2 * n) := by
    have hN_le_n' : N ≤ 2 * n := le_trans hN_le_n (by omega)
    have hfib_ge : 2 * n ≤ Nat.fib (2 * n) := Nat.le_fib_self (by omega : 5 ≤ 2 * n)
    exact le_trans hN_le_n' hfib_ge
  have hfib_le_b : Nat.fib (2 * n) ≤ b := by
    have hden := dens_ge_fib_of_irrational r hirr (2 * n - 1)
    have hden' : (Nat.fib (2 * n) : ℝ) ≤ (B : ℝ) := by
      have h : 2 * n - 1 + 1 = 2 * n := by omega
      simpa [h, hB] using hden
    exact_mod_cast (by simpa [(by exact_mod_cast hB_nat : (b : ℝ) = B)] using hden' :
      (Nat.fib (2 * n) : ℝ) ≤ b)
  have hN_le_b : N ≤ b := le_trans hN_le_fib hfib_le_b
  have hN_le_a : N ≤ a := le_trans hN_le_b (le_trans (by omega : b ≤ 2 * b) (le_of_lt hltNat))
  -- N ≤ a1 via: N ≤ n ≤ 2n+1 ≤ fib(2n+1) ≤ b1 ≤ a1
  have hN_le_fib1 : N ≤ Nat.fib (2 * n + 1) := by
    have hN_le_n' : N ≤ 2 * n + 1 := le_trans hN_le_n (by omega)
    have hfib_ge : 2 * n + 1 ≤ Nat.fib (2 * n + 1) := Nat.le_fib_self (by omega : 5 ≤ 2 * n + 1)
    exact le_trans hN_le_n' hfib_ge
  have hfib_le_b1 : Nat.fib (2 * n + 1) ≤ b1 := by
    have hden := dens_ge_fib_of_irrational r hirr (2 * n)
    have hden' : (Nat.fib (2 * n + 1) : ℝ) ≤ (B1 : ℝ) := by simpa [Nat.add_assoc, hB1'] using hden
    exact_mod_cast (by simpa [(by exact_mod_cast hB1_nat : (b1 : ℝ) = B1)] using hden' :
      (Nat.fib (2 * n + 1) : ℝ) ≤ b1)
  have hN_le_b1 : N ≤ b1 := le_trans hN_le_fib1 hfib_le_b1
  have hN_le_a1 : N ≤ a1 := le_trans hN_le_b1 (le_trans (by omega : b1 ≤ 2 * b1) (le_of_lt hltNat1))
  exact ⟨n, a, b, a1, b1, ha_pos, hb_pos, ha1_pos, hb1_pos,
    le_of_lt hltNat, le_of_lt hltNat1, hratio, hratio1, hdetZ', hb_lt, hN_le_a, hN_le_a1⟩

/-- Extended version of odd_even_convergent_pair_data_large_both that also returns:
    - n ≥ 5 (useful for predecessor computation)
    - nums/dens identification (a, b, a1, b1 are the actual numerators/denominators)
    - convergent > 2 witnesses for both indices -/
theorem odd_even_convergent_pair_data_large_both_ext (r : ℝ) (hr : 2 < r)
    (hirr : Irrational r) (N : ℕ) :
    ∃ n a b a1 b1 : ℕ,
      0 < a ∧ 0 < b ∧ 0 < a1 ∧ 0 < b1 ∧
      2 * b ≤ a ∧ 2 * b1 ≤ a1 ∧
      (r.convergent (2 * n - 1) : ℝ) = (a : ℝ) / b ∧
      (r.convergent (2 * n) : ℝ) = (a1 : ℝ) / b1 ∧
      (a1 : ℤ) * b - (b1 : ℤ) * a = -1 ∧ b < b1 ∧ N ≤ a ∧ N ≤ a1 ∧
      -- Extended properties:
      5 ≤ n ∧
      (2 : ℝ) < (r.convergent (2 * n - 1) : ℝ) ∧
      (2 : ℝ) < (r.convergent (2 * n) : ℝ) ∧
      (2 : ℝ) < (r.convergent (2 * n - 2) : ℝ) ∧
      (GenContFract.of r).nums (2 * n - 1) = (a : ℝ) ∧
      (GenContFract.of r).dens (2 * n - 1) = (b : ℝ) ∧
      (GenContFract.of r).nums (2 * n) = (a1 : ℝ) ∧
      (GenContFract.of r).dens (2 * n) = (b1 : ℝ) := by
  -- Same proof as odd_even_convergent_pair_data_large_both, returning more info
  classical
  rcases convergent_gt_two_eventually_nat r hr with ⟨N0, hN0⟩
  set n : ℕ := max N0 (N + 5)
  have hn_ge_5 : 5 ≤ n := le_trans (by omega : 5 ≤ N + 5) (le_max_right _ _)
  have hidx : 2 * n - 1 + 1 = 2 * n := by omega
  have hn_ge1 : 1 ≤ n := le_trans (by omega : 1 ≤ 5) hn_ge_5
  have hgt_odd : (2 : ℝ) < (r.convergent (2 * n - 1) : ℝ) := by
    have hN0_le_n : N0 ≤ n := le_max_left _ _
    have hn_le : n ≤ 2 * n - 1 := by omega
    have hN0_le' : N0 ≤ 2 * n - 1 := le_trans hN0_le_n hn_le
    exact hN0 _ hN0_le'
  have hgt_even : (2 : ℝ) < (r.convergent (2 * n) : ℝ) := by
    have hN0_le_n : N0 ≤ n := le_max_left _ _
    have hN0_le' : N0 ≤ 2 * n := le_trans hN0_le_n (by omega)
    exact hN0 _ hN0_le'
  have hgt_2n_minus_2 : (2 : ℝ) < (r.convergent (2 * n - 2) : ℝ) := by
    have hN0_le_n : N0 ≤ n := le_max_left _ _
    have hn_le : n ≤ 2 * n - 2 := by omega  -- works since n ≥ 5
    have hN0_le' : N0 ≤ 2 * n - 2 := le_trans hN0_le_n hn_le
    exact hN0 _ hN0_le'
  rcases nums_dens_det_irrational_int r hirr (2 * n - 1) with
    ⟨A, B, A1, B1, hA, hB, hA1, hB1, hdet⟩
  have hA1' : (GenContFract.of r).nums (2 * n) = A1 := by simpa [hidx] using hA1
  have hB1' : (GenContFract.of r).dens (2 * n) = B1 := by simpa [hidx] using hB1
  have hBposR : 0 < (B : ℝ) := by simpa [hB] using dens_pos_of_irrational r hirr (2 * n - 1)
  have hBpos : 0 < B := by exact_mod_cast hBposR
  have hB1posR : 0 < (B1 : ℝ) := by simpa [hB1'] using dens_pos_of_irrational r hirr (2 * n)
  have hB1pos : 0 < B1 := by exact_mod_cast hB1posR
  have hlt_odd : (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
    simpa [hA, hB] using two_mul_dens_lt_nums_of_convergent_gt_two r hirr (2 * n - 1) hgt_odd
  have hlt_even : (2 : ℝ) * (B1 : ℝ) < (A1 : ℝ) := by
    simpa [hA1', hB1'] using two_mul_dens_lt_nums_of_convergent_gt_two r hirr (2 * n) hgt_even
  have hlt_oddZ : 2 * B < A := by exact_mod_cast hlt_odd
  have hlt_evenZ : 2 * B1 < A1 := by exact_mod_cast hlt_even
  have hApos : 0 < A := lt_trans (by nlinarith : 0 < 2 * B) hlt_oddZ
  have hA1pos : 0 < A1 := lt_trans (by nlinarith : 0 < 2 * B1) hlt_evenZ
  set a : ℕ := Int.toNat A
  set b : ℕ := Int.toNat B
  set a1 : ℕ := Int.toNat A1
  set b1 : ℕ := Int.toNat B1
  have hA_nat : (a : ℤ) = A := Int.toNat_of_nonneg (le_of_lt hApos)
  have hB_nat : (b : ℤ) = B := Int.toNat_of_nonneg (le_of_lt hBpos)
  have hA1_nat : (a1 : ℤ) = A1 := Int.toNat_of_nonneg (le_of_lt hA1pos)
  have hB1_nat : (b1 : ℤ) = B1 := Int.toNat_of_nonneg (le_of_lt hB1pos)
  have ha_pos : 0 < a := by
    have : A.toNat ≠ 0 := by
      intro h
      have : A = 0 := by simp only [Int.toNat_eq_zero] at h; omega
      omega
    exact Nat.pos_of_ne_zero this
  have hb_pos : 0 < b := by
    have : B.toNat ≠ 0 := by
      intro h
      have : B = 0 := by simp only [Int.toNat_eq_zero] at h; omega
      omega
    exact Nat.pos_of_ne_zero this
  have ha1_pos : 0 < a1 := by
    have : A1.toNat ≠ 0 := by
      intro h
      have : A1 = 0 := by simp only [Int.toNat_eq_zero] at h; omega
      omega
    exact Nat.pos_of_ne_zero this
  have hb1_pos : 0 < b1 := by
    have : B1.toNat ≠ 0 := by
      intro h
      have : B1 = 0 := by simp only [Int.toNat_eq_zero] at h; omega
      omega
    exact Nat.pos_of_ne_zero this
  have hltNat : 2 * b < a := by
    have h : 2 * B < A := hlt_oddZ
    have h' : (2 * b : ℤ) < a := calc (2 * b : ℤ) = 2 * B := by rw [hB_nat]
      _ < A := h
      _ = a := hA_nat.symm
    omega
  have hltNat1 : 2 * b1 < a1 := by
    have h : 2 * B1 < A1 := hlt_evenZ
    have h' : (2 * b1 : ℤ) < a1 := calc (2 * b1 : ℤ) = 2 * B1 := by rw [hB1_nat]
      _ < A1 := h
      _ = a1 := hA1_nat.symm
    omega
  have hA_real : (a : ℝ) = (A : ℝ) := by exact_mod_cast hA_nat
  have hB_real : (b : ℝ) = (B : ℝ) := by exact_mod_cast hB_nat
  have hA1_real : (a1 : ℝ) = (A1 : ℝ) := by exact_mod_cast hA1_nat
  have hB1_real : (b1 : ℝ) = (B1 : ℝ) := by exact_mod_cast hB1_nat
  have hratio : (r.convergent (2 * n - 1) : ℝ) = (a : ℝ) / b := by
    simp only [convergent_cast_eq_nums_div_dens, hA, hB, hA_real, hB_real]
  have hratio1 : (r.convergent (2 * n) : ℝ) = (a1 : ℝ) / b1 := by
    simp only [convergent_cast_eq_nums_div_dens, hA1', hB1', hA1_real, hB1_real]
  have hdetZ' : (a1 : ℤ) * (b : ℤ) - (b1 : ℤ) * (a : ℤ) = -1 := by
    have hpow : (-1 : ℤ) ^ (2 * n - 1 + 1) = 1 := by simp only [hidx, (even_two_mul n).neg_one_pow]
    have hdet' : A * B1 - B * A1 = 1 := by simpa [hpow] using hdet
    simp only [hA_nat, hB_nat, hA1_nat, hB1_nat]; linarith
  have hb_lt : b < b1 := by
    have hden_lt := dens_lt_succ_of_irrational r hirr (2 * n - 1 - 1)
    have h1 : 2 * n - 1 - 1 + 1 = 2 * n - 1 := by omega
    have h2 : 2 * n - 1 - 1 + 2 = 2 * n := by omega
    have hB_lt : (B : ℝ) < (B1 : ℝ) := by simpa [h1, h2, hB, hB1'] using hden_lt
    exact_mod_cast (by simp only [hB_nat, hB1_nat]; exact_mod_cast hB_lt : (b : ℤ) < b1)
  have hN_le_n : N ≤ n := le_trans (by omega : N ≤ N + 5) (le_max_right _ _)
  have hN_le_a : N ≤ a := by
    have hfib_ge : 2 * n ≤ Nat.fib (2 * n) := Nat.le_fib_self (by omega : 5 ≤ 2 * n)
    have hfib_le_b : Nat.fib (2 * n) ≤ b := by
      have hden := dens_ge_fib_of_irrational r hirr (2 * n - 1)
      have hidx' : 2 * n - 1 + 1 = 2 * n := by omega
      have hden' : (Nat.fib (2 * n) : ℝ) ≤ (GenContFract.of r).dens (2 * n - 1) := by
        simp only [hidx'] at hden; exact hden
      have hden'' : (Nat.fib (2 * n) : ℝ) ≤ b := by
        calc (Nat.fib (2 * n) : ℝ) ≤ (GenContFract.of r).dens (2 * n - 1) := hden'
          _ = (B : ℝ) := hB
          _ = (b : ℝ) := hB_real.symm
      exact_mod_cast hden''
    omega
  have hN_le_a1 : N ≤ a1 := by
    have hfib_ge : 2 * n + 1 ≤ Nat.fib (2 * n + 1) := Nat.le_fib_self (by omega : 5 ≤ 2 * n + 1)
    have hfib_le_b1 : Nat.fib (2 * n + 1) ≤ b1 := by
      have hden := dens_ge_fib_of_irrational r hirr (2 * n)
      have hden' : (Nat.fib (2 * n + 1) : ℝ) ≤ b1 := by
        calc (Nat.fib (2 * n + 1) : ℝ) ≤ (GenContFract.of r).dens (2 * n) := hden
          _ = (B1 : ℝ) := hB1'
          _ = (b1 : ℝ) := hB1_real.symm
      exact_mod_cast hden'
    omega
  -- nums/dens identification
  have hnums_odd : (GenContFract.of r).nums (2 * n - 1) = (a : ℝ) := by simp [hA, hA_real]
  have hdens_odd : (GenContFract.of r).dens (2 * n - 1) = (b : ℝ) := by simp [hB, hB_real]
  have hnums_even : (GenContFract.of r).nums (2 * n) = (a1 : ℝ) := by simp [hA1', hA1_real]
  have hdens_even : (GenContFract.of r).dens (2 * n) = (b1 : ℝ) := by simp [hB1', hB1_real]
  exact ⟨n, a, b, a1, b1, ha_pos, hb_pos, ha1_pos, hb1_pos,
    le_of_lt hltNat, le_of_lt hltNat1, hratio, hratio1, hdetZ', hb_lt, hN_le_a, hN_le_a1,
    hn_ge_5, hgt_odd, hgt_even, hgt_2n_minus_2, hnums_odd, hdens_odd, hnums_even, hdens_even⟩

private lemma coprime_of_det_eq_one_left (a b a1 b1 : ℕ)
    (hdet : a1 * b - b1 * a = 1) : Nat.Coprime a b := by
  apply Nat.coprime_of_dvd
  intro d hd hda hdb
  have h1 : d ∣ a1 * b := hdb.mul_left a1
  have h2 : d ∣ b1 * a := hda.mul_left b1
  have h1' : (d : ℤ) ∣ (a1 * b : ℤ) := Int.ofNat_dvd.mpr h1
  have h2' : (d : ℤ) ∣ (b1 * a : ℤ) := Int.ofNat_dvd.mpr h2
  have hsub : (d : ℤ) ∣ ((a1 * b : ℤ) - (b1 * a : ℤ)) := dvd_sub h1' h2'
  have hconv : (a1 * b : ℤ) - (b1 * a : ℤ) = 1 := by
    have h' : a1 * b = b1 * a + 1 := by omega
    linarith
  rw [hconv] at hsub
  have hd1 : d = 1 := Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp hsub)
  have := hd.one_lt
  omega

private lemma coprime_of_det_eq_one_right (a b a1 b1 : ℕ)
    (hdet : a1 * b - b1 * a = 1) : Nat.Coprime a1 b1 := by
  apply Nat.coprime_of_dvd
  intro d hd hda hdb
  have h1 : d ∣ a1 * b := hda.mul_right b
  have h2 : d ∣ b1 * a := hdb.mul_right a
  have h1' : (d : ℤ) ∣ (a1 * b : ℤ) := Int.ofNat_dvd.mpr h1
  have h2' : (d : ℤ) ∣ (b1 * a : ℤ) := Int.ofNat_dvd.mpr h2
  have hsub : (d : ℤ) ∣ ((a1 * b : ℤ) - (b1 * a : ℤ)) := dvd_sub h1' h2'
  have hconv : (a1 * b : ℤ) - (b1 * a : ℤ) = 1 := by
    have h' : a1 * b = b1 * a + 1 := by omega
    linarith
  rw [hconv] at hsub
  have hd1 : d = 1 := Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp hsub)
  have := hd.one_lt
  omega

/- Theorem 3.14(a): For irrational r ≥ 2, the supremum from below equals
   the infimum from above:
   sup_{a/b < r} F(E_{a/b}) = inf_{a/b > r} F(E_{a/b}). -/
theorem fractionGraph_sup_eq_inf_irrational (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (φ : SpectralPoint) :
    -- sup_{a/b < r} F(E_{a/b}) = inf_{a/b > r} F(E_{a/b})
    sSup {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b < r ∧ x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} =
    sInf {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b > r ∧ x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} := by
  classical
  have hr' : 2 < r := by
    apply lt_of_le_of_ne hr
    intro h
    have : (r : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := ⟨2, by simp [h]⟩
    exact hirr this
  set Sbelow : Set ℝ := {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
    (a : ℝ) / b < r ∧ x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)}
  set Sabove : Set ℝ := {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
    (a : ℝ) / b > r ∧ x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)}
  change sSup Sbelow = sInf Sabove
  obtain ⟨n0, a0, b0, a1, b1, ha0, hb0, ha1, hb1, h2b0, h2b1, hratio0, hratio1,
      hdet0, hb0_lt, _, _⟩ := even_odd_convergent_pair_data_large r hr' hirr 1
  have hbelow_mem0 : φ.eval (@FractionGraph' a0 b0 ⟨Nat.pos_iff_ne_zero.mp ha0⟩) ∈ Sbelow := by
    have hlt : (r.convergent (2 * n0) : ℝ) < r :=
      convergent_even_lt_irrational r hirr n0
    exact ⟨a0, b0, ha0, hb0, h2b0, by simpa [hratio0] using hlt, rfl⟩
  have habove_mem0 : φ.eval (@FractionGraph' a1 b1 ⟨Nat.pos_iff_ne_zero.mp ha1⟩) ∈ Sabove := by
    have hgt' : r < (a1 : ℝ) / b1 := by
      calc
        r < (r.convergent (2 * n0 + 1) : ℝ) := convergent_odd_gt_irrational r hirr n0
        _ = (a1 : ℝ) / b1 := hratio1
    exact ⟨a1, b1, ha1, hb1, h2b1, hgt', rfl⟩
  have hbounded_above : BddAbove Sbelow := by
    refine ⟨φ.eval (@FractionGraph' a1 b1 ⟨Nat.pos_iff_ne_zero.mp ha1⟩), ?_⟩
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    rcases habove_mem0 with ⟨a', b', ha', hb', h2b', hgt, hval⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    haveI : NeZero a' := ⟨Nat.pos_iff_ne_zero.mp ha'⟩
    have hlt' : (a : ℝ) / b < (a' : ℝ) / b' := by linarith
    have hle : (a : ℚ) / b ≤ (a' : ℚ) / b' := by
      apply (Rat.cast_le (K := ℝ)).1
      simpa using (le_of_lt hlt')
    have hcohom := (fractionGraph_ordering a b a' b' hb hb' h2b h2b').mp hle
    have hcohom' :
        ∃ f, IsCohom (FractionGraph' a b).graph (FractionGraph' a' b').graph f := by
      simpa using hcohom
    simpa [hval] using φ.mono_cohom _ _ hcohom'
  have hbounded_below : BddBelow Sabove := by
    refine ⟨φ.eval (@FractionGraph' a0 b0 ⟨Nat.pos_iff_ne_zero.mp ha0⟩), ?_⟩
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h2b, hgt, rfl⟩
    rcases hbelow_mem0 with ⟨a', b', ha', hb', h2b', hlt, hval⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    haveI : NeZero a' := ⟨Nat.pos_iff_ne_zero.mp ha'⟩
    have hlt' : (a' : ℝ) / b' < (a : ℝ) / b := by linarith
    have hle : (a' : ℚ) / b' ≤ (a : ℚ) / b := by
      apply (Rat.cast_le (K := ℝ)).1
      simpa using (le_of_lt hlt')
    have hcohom := (fractionGraph_ordering a' b' a b hb' hb h2b' h2b).mp hle
    have hcohom' :
        ∃ f, IsCohom (FractionGraph' a' b').graph (FractionGraph' a b).graph f := by
      simpa using hcohom
    simpa [hval] using φ.mono_cohom _ _ hcohom'
  have hsup_le_inf : sSup Sbelow ≤ sInf Sabove := by
    have hbelow_nonempty : Sbelow.Nonempty := ⟨_, hbelow_mem0⟩
    have habove_nonempty : Sabove.Nonempty := ⟨_, habove_mem0⟩
    refine (csSup_le_iff hbounded_above hbelow_nonempty).2 ?_
    intro x hx
    refine (le_csInf_iff hbounded_below habove_nonempty).2 ?_
    intro y hy
    rcases hx with ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    rcases hy with ⟨a', b', ha', hb', h2b', hgt, rfl⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    haveI : NeZero a' := ⟨Nat.pos_iff_ne_zero.mp ha'⟩
    have hlt' : (a : ℝ) / b < (a' : ℝ) / b' := by linarith
    have hle : (a : ℚ) / b ≤ (a' : ℚ) / b' := by
      apply (Rat.cast_le (K := ℝ)).1
      simpa using (le_of_lt hlt')
    have hcohom := (fractionGraph_ordering a b a' b' hb hb' h2b h2b').mp hle
    have hcohom' :
        ∃ f, IsCohom (FractionGraph' a b).graph (FractionGraph' a' b').graph f := by
      simpa using hcohom
    exact φ.mono_cohom _ _ hcohom'
  have hle_add : ∀ ε > 0, sInf Sabove ≤ sSup Sbelow + ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_gt ((Nat.ceil r : ℝ) / ε)
    have hM_pos : 0 < M := by
      have : (0 : ℝ) < (M : ℝ) := by
        have h0 : (0 : ℝ) ≤ (Nat.ceil r : ℝ) / ε := by
          exact div_nonneg (by exact_mod_cast (Nat.zero_le _)) (le_of_lt hε)
        linarith
      exact_mod_cast this
    have hM_bound : (Nat.ceil r : ℝ) / (M : ℝ) < ε := by
      have hM'' : (Nat.ceil r : ℝ) / ε < (M : ℝ) := by exact_mod_cast hM
      have hM' : (Nat.ceil r : ℝ) < (M : ℝ) * ε := by
        exact (div_lt_iff₀ hε).1 hM''
      have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
      have hM'' : (Nat.ceil r : ℝ) < ε * (M : ℝ) := by
        simpa [mul_comm] using hM'
      exact (div_lt_iff₀ hM_pos').2 hM''
    obtain ⟨n, a, b, a1, b1, ha, hb, ha1, hb1, h2b, h2b1, hratio, hratio1,
      hdet, hb_lt, hN_le_a1, _⟩ :=
      even_odd_convergent_pair_data_large r hr' hirr (M + 1)
    have hlt : (r.convergent (2 * n) : ℝ) < r :=
      convergent_even_lt_irrational r hirr n
    have hgt : r < (r.convergent (2 * n + 1) : ℝ) :=
      convergent_odd_gt_irrational r hirr n
    have hbelow_mem : φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) ∈ Sbelow := by
      refine ⟨a, b, ha, hb, h2b, ?_, rfl⟩
      simpa [hratio] using hlt
    have habove_mem : φ.eval (@FractionGraph' a1 b1 ⟨Nat.pos_iff_ne_zero.mp ha1⟩) ∈ Sabove := by
      refine ⟨a1, b1, ha1, hb1, h2b1, ?_, rfl⟩
      calc
        r < (r.convergent (2 * n + 1) : ℝ) := hgt
        _ = (a1 : ℝ) / b1 := hratio1
    have hsup_ge : φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) ≤ sSup Sbelow :=
      le_csSup hbounded_above hbelow_mem
    have hinf_le : sInf Sabove ≤ φ.eval (@FractionGraph' a1 b1 ⟨Nat.pos_iff_ne_zero.mp ha1⟩) :=
      csInf_le hbounded_below habove_mem
    haveI : NeZero a1 := ⟨Nat.pos_iff_ne_zero.mp ha1⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    have hb_ltZ : (b : ℤ) < (b1 : ℤ) := by exact_mod_cast hb_lt
    have ha_posZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
    have hmul_lt : (b : ℤ) * (a : ℤ) < (b1 : ℤ) * (a : ℤ) :=
      mul_lt_mul_of_pos_right hb_ltZ ha_posZ
    have hdetZ : (a1 : ℤ) * (b : ℤ) = (b1 : ℤ) * (a : ℤ) + 1 := by
      have hle : b1 * a ≤ a1 * b := by omega
      have hdetZ' : (a1 : ℤ) * (b : ℤ) - (b1 : ℤ) * (a : ℤ) = 1 := by
        have hdetZ'' := congrArg (fun t : ℕ => (t : ℤ)) hdet
        simpa [Int.ofNat_sub hle] using hdetZ''
      linarith
    have hmul_lt' : (a : ℤ) * (b : ℤ) < (a1 : ℤ) * (b : ℤ) := by linarith [hdetZ, hmul_lt]
    have hb_nonneg : (0 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (Nat.zero_le b)
    have ha_ltZ : (a : ℤ) < (a1 : ℤ) :=
      lt_of_mul_lt_mul_right hmul_lt' hb_nonneg
    have ha_lt : a < a1 := by exact_mod_cast ha_ltZ
    have hbounds := fractionGraph_spectral_bounds a1 b1 a b hb1 hb h2b1 h2b ha_lt hb_lt hdet φ
    obtain ⟨hlo, hhi⟩ := hbounds
    have hdiff_nonneg :
        0 ≤ φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) := by linarith
    have ha1_gt : 1 < a1 := by omega
    have hdiff_bound :
        φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) ≤
          (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := by
      have : (a1 : ℝ) / (a1 - 1) - 1 = 1 / (a1 - 1) := by
        have hden_ne : (a1 : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) < a1 := by exact_mod_cast ha1_gt
          linarith
        field_simp [hden_ne]
        ring
      calc φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)
          ≤ (a1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) -
            φ.eval (FractionGraph' a b) := by linarith
        _ = ((a1 : ℝ) / (a1 - 1) - 1) * φ.eval (FractionGraph' a b) := by ring
        _ = (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := by rw [this]
    have hupper_bound : φ.eval (FractionGraph' a b) ≤ (Nat.ceil r : ℝ) := by
      have hceil : r ≤ (Nat.ceil r : ℝ) := by exact_mod_cast (Nat.le_ceil r)
      have hle' : (a : ℝ) / b ≤ (Nat.ceil r : ℝ) := by linarith [hlt, hceil]
      have hr_le : (a : ℚ) / b ≤ (Nat.ceil r : ℚ) / 1 := by
        apply (Rat.cast_le (K := ℝ)).1
        simpa using hle'
      have hceil_ge : 2 ≤ Nat.ceil r := by
        have hceil' : (2 : ℝ) ≤ (Nat.ceil r : ℝ) := le_trans hr hceil
        exact_mod_cast hceil'
      haveI : NeZero (Nat.ceil r) := ⟨by omega⟩
      have hcohom :=
        (fractionGraph_ordering a b (Nat.ceil r) 1 hb (by omega) h2b (by
          simpa using hceil_ge)).mp hr_le
      have hcohom' :
          ∃ f,
            IsCohom (FractionGraph' a b).graph
              (FractionGraph' (Nat.ceil r) 1).graph f := by
        simpa using hcohom
      have hmono :=
        φ.mono_cohom (FractionGraph' a b) (FractionGraph' (Nat.ceil r) 1) hcohom'
      have hbound := fractionGraph_spectral_le_vertices (Nat.ceil r) 1 (by omega) φ
      exact le_trans hmono hbound
    have hdiff_bound' :
        φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) ≤
          (Nat.ceil r : ℝ) / (a1 - 1) := by
      calc φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)
          ≤ (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := hdiff_bound
        _ ≤ (1 : ℝ) / (a1 - 1) * (Nat.ceil r : ℝ) := by
          apply mul_le_mul_of_nonneg_left hupper_bound
          have hden_pos : 0 < (a1 : ℝ) - 1 := by
            have ha1_ge : (1 : ℝ) < a1 := by exact_mod_cast (by omega : 1 < a1)
            linarith
          exact le_of_lt (one_div_pos.mpr hden_pos)
        _ = (Nat.ceil r : ℝ) / (a1 - 1) := by ring
    have hratio_bound : (Nat.ceil r : ℝ) / (a1 - 1) ≤ (Nat.ceil r : ℝ) / (M : ℝ) := by
      have hM_le : (M : ℝ) ≤ (a1 : ℝ) - 1 := by
        have hM1_le : M + 1 ≤ a1 := hN_le_a1
        have hM1_le' : (M : ℝ) + 1 ≤ (a1 : ℝ) := by exact_mod_cast hM1_le
        linarith
      have hnum_nonneg : (0 : ℝ) ≤ (Nat.ceil r : ℝ) := by
        exact_mod_cast (Nat.zero_le _)
      have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
      exact div_le_div_of_nonneg_left hnum_nonneg hM_pos' hM_le
    have hdiff_final :
        φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) ≤ ε := by
      calc φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)
          ≤ (Nat.ceil r : ℝ) / (a1 - 1) := hdiff_bound'
        _ ≤ (Nat.ceil r : ℝ) / (M : ℝ) := hratio_bound
        _ ≤ ε := le_of_lt hM_bound
    linarith
  apply le_antisymm
  · exact hsup_le_inf
  · apply _root_.le_of_forall_pos_le_add
    intro ε hε
    have h := hle_add ε hε
    linarith

/-- Theorem 3.14(a), `ℕ+` form: For irrational `r ≥ 2` and any spectral
    function `φ ∈ X`,
    `sup_{a/b < r} φ(E_{a/b}) = inf_{a/b > r} φ(E_{a/b})`,
    where the suprema/infima are indexed over `ℕ+ × ℕ+` pairs.

    Bridge from the underlying `fractionGraph_sup_eq_inf_irrational`
    (indexed over `ℕ × ℕ` with positivity hypotheses + `FractionGraph'`). -/
theorem fractionGraph_sup_eq_inf_irrational_pnat (r : ℝ) (hr : 2 ≤ r)
    (hirr : Irrational r) (φ : SpectralPoint) :
    sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
        x = φ (FractionGraph a b)} =
    sInf {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
        x = φ (FractionGraph a b)} := by
  have hbelow : {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
        x = φ (FractionGraph a b)} =
      {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b < r ∧
        x = φ (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} := by
    ext x; constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hlt, rfl⟩
      exact ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    · rintro ⟨a, b, ha, hb, h2b, hlt, rfl⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hlt, rfl⟩
  have habove : {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
        x = φ (FractionGraph a b)} =
      {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b > r ∧
        x = φ (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} := by
    ext x; constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hgt, rfl⟩
      exact ⟨a, b, ha, hb, h2b, hgt, rfl⟩
    · rintro ⟨a, b, ha, hb, h2b, hgt, rfl⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hgt, rfl⟩
  rw [hbelow, habove]
  exact fractionGraph_sup_eq_inf_irrational r hr hirr φ

/-- Theorem 3.14(b): Uniform continuity at irrationals.
    |F(E_{p/q}) - sup_{a/b < r} F(E_{a/b})| < ε uniformly for p/q near r.

    This states that for p/q near r, the asymptotic spectrum distance between
    E_{p/q} and the "limit graph at r" is small. -/
theorem fractionGraph_uniform_continuity_irrational (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p₁ q₁ p₂ q₂ : ℕ),
      ∀ (hp₁ : 0 < p₁) (hp₂ : 0 < p₂), 0 < q₁ → 0 < q₂ → 2 * q₁ ≤ p₁ → 2 * q₂ ≤ p₂ →
      |(p₁ : ℝ) / q₁ - r| < δ → |(p₂ : ℝ) / q₂ - r| < δ →
      haveI : NeZero p₁ := ⟨Nat.pos_iff_ne_zero.mp hp₁⟩
      haveI : NeZero p₂ := ⟨Nat.pos_iff_ne_zero.mp hp₂⟩
      asympSpecDistance (FractionGraph' p₁ q₁) (FractionGraph' p₂ q₂) < ε := by
  classical
  intro ε hε
  have hr' : 2 < r := by
    apply lt_of_le_of_ne hr
    intro h
    have : (r : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := ⟨2, by simp [h]⟩
    exact hirr this
  -- Pick M so that ceil(r)/M < ε.
  obtain ⟨M, hM⟩ := exists_nat_gt ((Nat.ceil r : ℝ) / ε)
  have hM_pos : 0 < M := by
    have : (0 : ℝ) < (M : ℝ) := by
      have h0 : (0 : ℝ) ≤ (Nat.ceil r : ℝ) / ε := by
        exact div_nonneg (by exact_mod_cast (Nat.zero_le _)) (le_of_lt hε)
      linarith
    exact_mod_cast this
  have hM_bound : (Nat.ceil r : ℝ) / (M : ℝ) < ε := by
    have hM'' : (Nat.ceil r : ℝ) / ε < (M : ℝ) := by exact_mod_cast hM
    have hM' : (Nat.ceil r : ℝ) < (M : ℝ) * ε := by
      exact (div_lt_iff₀ hε).1 hM''
    have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    have hM'' : (Nat.ceil r : ℝ) < ε * (M : ℝ) := by
      simpa [mul_comm] using hM'
    exact (div_lt_iff₀ hM_pos').2 hM''
  -- Choose a convergent pair around r with a1 ≥ M + 1.
  obtain ⟨n, a, b, a1, b1, ha, hb, ha1, hb1, h2b, h2b1, hratio, hratio1,
      hdet, hb_lt, hN_le_a1, _⟩ :=
    even_odd_convergent_pair_data_large r hr' hirr (M + 1)
  have hlt : (a : ℝ) / b < r := by
    have hlt' : (r.convergent (2 * n) : ℝ) < r :=
      convergent_even_lt_irrational r hirr n
    simpa [hratio] using hlt'
  have hgt : r < (a1 : ℝ) / b1 := by
    have hgt' : r < (r.convergent (2 * n + 1) : ℝ) :=
      convergent_odd_gt_irrational r hirr n
    calc
      r < (r.convergent (2 * n + 1) : ℝ) := hgt'
      _ = (a1 : ℝ) / b1 := by
            simpa [Real.convergent] using hratio1
  set δ : ℝ := min (r - (a : ℝ) / b) ((a1 : ℝ) / b1 - r)
  have hδ_pos : 0 < δ := by
    have hleft : 0 < r - (a : ℝ) / b := by linarith
    have hright : 0 < (a1 : ℝ) / b1 - r := by linarith
    exact lt_min hleft hright
  refine ⟨δ, hδ_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ hp₁ hp₂ hq₁ hq₂ h2q₁ h2q₂ hdist₁ hdist₂
  haveI : NeZero p₁ := ⟨Nat.pos_iff_ne_zero.mp hp₁⟩
  haveI : NeZero p₂ := ⟨Nat.pos_iff_ne_zero.mp hp₂⟩
  have hδ_le_left : δ ≤ r - (a : ℝ) / b := by
    exact min_le_left _ _
  have hδ_le_right : δ ≤ (a1 : ℝ) / b1 - r := by
    exact min_le_right _ _
  have h_between₁ : (a : ℝ) / b ≤ (p₁ : ℝ) / q₁ ∧ (p₁ : ℝ) / q₁ ≤ (a1 : ℝ) / b1 := by
    have hdist₁' := (abs_lt.mp hdist₁)
    have hlow : r - δ < (p₁ : ℝ) / q₁ := by linarith
    have hhigh : (p₁ : ℝ) / q₁ < r + δ := by linarith
    have hlow' : (a : ℝ) / b ≤ (p₁ : ℝ) / q₁ := by linarith
    have hhigh' : (p₁ : ℝ) / q₁ ≤ (a1 : ℝ) / b1 := by linarith
    exact ⟨hlow', hhigh'⟩
  have h_between₂ : (a : ℝ) / b ≤ (p₂ : ℝ) / q₂ ∧ (p₂ : ℝ) / q₂ ≤ (a1 : ℝ) / b1 := by
    have hdist₂' := (abs_lt.mp hdist₂)
    have hlow : r - δ < (p₂ : ℝ) / q₂ := by linarith
    have hhigh : (p₂ : ℝ) / q₂ < r + δ := by linarith
    have hlow' : (a : ℝ) / b ≤ (p₂ : ℝ) / q₂ := by linarith
    have hhigh' : (p₂ : ℝ) / q₂ ≤ (a1 : ℝ) / b1 := by linarith
    exact ⟨hlow', hhigh'⟩
  have hrat₁_le : (a : ℚ) / b ≤ (p₁ : ℚ) / q₁ := by
    apply (Rat.cast_le (K := ℝ)).1
    simpa using h_between₁.1
  have hrat₁_le' : (p₁ : ℚ) / q₁ ≤ (a1 : ℚ) / b1 := by
    apply (Rat.cast_le (K := ℝ)).1
    simpa using h_between₁.2
  have hrat₂_le : (a : ℚ) / b ≤ (p₂ : ℚ) / q₂ := by
    apply (Rat.cast_le (K := ℝ)).1
    simpa using h_between₂.1
  have hrat₂_le' : (p₂ : ℚ) / q₂ ≤ (a1 : ℚ) / b1 := by
    apply (Rat.cast_le (K := ℝ)).1
    simpa using h_between₂.2
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  haveI : NeZero a1 := ⟨Nat.pos_iff_ne_zero.mp ha1⟩
  -- Co-homomorphisms for ordering
  have hcohom₁ :
      ∃ f, IsCohom (FractionGraph' a b).graph (FractionGraph' p₁ q₁).graph f := by
    exact (fractionGraph_ordering a b p₁ q₁ hb hq₁ h2b h2q₁).mp hrat₁_le
  have hcohom₁' :
      ∃ f, IsCohom (FractionGraph' p₁ q₁).graph (FractionGraph' a1 b1).graph f := by
    exact (fractionGraph_ordering p₁ q₁ a1 b1 hq₁ hb1 h2q₁ h2b1).mp hrat₁_le'
  have hcohom₂ :
      ∃ f, IsCohom (FractionGraph' a b).graph (FractionGraph' p₂ q₂).graph f := by
    exact (fractionGraph_ordering a b p₂ q₂ hb hq₂ h2b h2q₂).mp hrat₂_le
  have hcohom₂' :
      ∃ f, IsCohom (FractionGraph' p₂ q₂).graph (FractionGraph' a1 b1).graph f := by
    exact (fractionGraph_ordering p₂ q₂ a1 b1 hq₂ hb1 h2q₂ h2b1).mp hrat₂_le'
  -- Bound the distance using the endpoints a/b < r < a1/b1.
  have hbound_endpoints :
      asympSpecDistance (FractionGraph' a1 b1) (FractionGraph' a b) ≤
        (Nat.ceil r : ℝ) / (a1 - 1) := by
    simp only [asympSpecDistance, spectralDistanceSet]
    apply csSup_le
    · obtain ⟨φ₀⟩ := spectralPoint_nonempty
      exact ⟨|φ₀.eval (FractionGraph' a1 b1) - φ₀.eval (FractionGraph' a b)|, φ₀, rfl⟩
    · intro x ⟨φ, hφ⟩
      rw [hφ]
      have ha_lt : a < a1 := by
        have hb_ltZ : (b : ℤ) < (b1 : ℤ) := by exact_mod_cast hb_lt
        have ha_posZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
        have hmul_lt : (b : ℤ) * (a : ℤ) < (b1 : ℤ) * (a : ℤ) :=
          mul_lt_mul_of_pos_right hb_ltZ ha_posZ
        have hdetZ : (a1 : ℤ) * (b : ℤ) = (b1 : ℤ) * (a : ℤ) + 1 := by
          have hle : b1 * a ≤ a1 * b := by omega
          have hdetZ' : (a1 : ℤ) * (b : ℤ) - (b1 : ℤ) * (a : ℤ) = 1 := by
            have hdetZ'' := congrArg (fun t : ℕ => (t : ℤ)) hdet
            simpa [Int.ofNat_sub hle] using hdetZ''
          linarith
        have hmul_lt' : (a : ℤ) * (b : ℤ) < (a1 : ℤ) * (b : ℤ) := by linarith [hdetZ, hmul_lt]
        have hb_nonneg : (0 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (Nat.zero_le b)
        exact_mod_cast (lt_of_mul_lt_mul_right hmul_lt' hb_nonneg)
      have hbounds := fractionGraph_spectral_bounds a1 b1 a b hb1 hb h2b1 h2b ha_lt hb_lt hdet φ
      obtain ⟨hlo, hhi⟩ := hbounds
      have hdiff_nonneg :
          0 ≤ φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) := by linarith
      rw [abs_of_nonneg hdiff_nonneg]
      have ha1_gt : 1 < a1 := by omega
      have hdiff_bound :
          φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) ≤
            (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := by
        have : (a1 : ℝ) / (a1 - 1) - 1 = 1 / (a1 - 1) := by
          have hden_ne : (a1 : ℝ) - 1 ≠ 0 := by
            have : (1 : ℝ) < a1 := by exact_mod_cast ha1_gt
            linarith
          field_simp [hden_ne]
          ring
        calc φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)
            ≤ (a1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) -
              φ.eval (FractionGraph' a b) := by linarith
          _ = ((a1 : ℝ) / (a1 - 1) - 1) * φ.eval (FractionGraph' a b) := by ring
          _ = (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := by rw [this]
      have hupper_bound : φ.eval (FractionGraph' a b) ≤ (Nat.ceil r : ℝ) := by
        have hceil : r ≤ (Nat.ceil r : ℝ) := by exact_mod_cast (Nat.le_ceil r)
        have hle' : (a : ℝ) / b ≤ (Nat.ceil r : ℝ) := by linarith [hlt, hceil]
        have hr_le : (a : ℚ) / b ≤ (Nat.ceil r : ℚ) / 1 := by
          apply (Rat.cast_le (K := ℝ)).1
          simpa using hle'
        have hceil_ge : 2 ≤ Nat.ceil r := by
          have hceil' : (2 : ℝ) ≤ (Nat.ceil r : ℝ) := le_trans hr hceil
          exact_mod_cast hceil'
        haveI : NeZero (Nat.ceil r) := ⟨by omega⟩
        have hcohom :=
          (fractionGraph_ordering a b (Nat.ceil r) 1 hb (by omega) h2b (by
            simpa using hceil_ge)).mp hr_le
        have hcohom' :
            ∃ f,
              IsCohom (FractionGraph' a b).graph
                (FractionGraph' (Nat.ceil r) 1).graph f := by
          simpa using hcohom
        have hmono :=
          φ.mono_cohom (FractionGraph' a b) (FractionGraph' (Nat.ceil r) 1) hcohom'
        have hbound := fractionGraph_spectral_le_vertices (Nat.ceil r) 1 (by omega) φ
        exact le_trans hmono hbound
      have hdiff_bound' :
          φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) ≤
            (Nat.ceil r : ℝ) / (a1 - 1) := by
        calc φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)
            ≤ (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := hdiff_bound
          _ ≤ (1 : ℝ) / (a1 - 1) * (Nat.ceil r : ℝ) := by
            apply mul_le_mul_of_nonneg_left hupper_bound
            have hden_pos : 0 < (a1 : ℝ) - 1 := by
              have ha1_ge : (1 : ℝ) < a1 := by exact_mod_cast (by omega : 1 < a1)
              linarith
            exact le_of_lt (one_div_pos.mpr hden_pos)
          _ = (Nat.ceil r : ℝ) / (a1 - 1) := by ring
      exact hdiff_bound'
  have hratio_bound : (Nat.ceil r : ℝ) / (a1 - 1) ≤ (Nat.ceil r : ℝ) / (M : ℝ) := by
    have hM_le : (M : ℝ) ≤ (a1 : ℝ) - 1 := by
      have hM1_le : M + 1 ≤ a1 := hN_le_a1
      have hM1_le' : (M : ℝ) + 1 ≤ (a1 : ℝ) := by exact_mod_cast hM1_le
      linarith
    have hnum_nonneg : (0 : ℝ) ≤ (Nat.ceil r : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    exact div_le_div_of_nonneg_left hnum_nonneg hM_pos' hM_le
  have hendpoint_lt :
      asympSpecDistance (FractionGraph' a1 b1) (FractionGraph' a b) < ε := by
    have hbound := le_trans hbound_endpoints hratio_bound
    exact lt_of_le_of_lt hbound hM_bound
  -- Use monotonicity to bound any two fractions between a/b and a1/b1.
  have hdist_le :
      asympSpecDistance (FractionGraph' p₁ q₁) (FractionGraph' p₂ q₂) ≤
        asympSpecDistance (FractionGraph' a1 b1) (FractionGraph' a b) := by
    simp only [asympSpecDistance, spectralDistanceSet]
    apply csSup_le
    · obtain ⟨φ₀⟩ := spectralPoint_nonempty
      exact ⟨|φ₀.eval (FractionGraph' p₁ q₁) - φ₀.eval (FractionGraph' p₂ q₂)|, φ₀, rfl⟩
    · intro x ⟨φ, hφ⟩
      rw [hφ]
      have hlo₁ : φ.eval (FractionGraph' a b) ≤ φ.eval (FractionGraph' p₁ q₁) := by
        exact (φ.mono_cohom _ _ hcohom₁)
      have hhi₁ : φ.eval (FractionGraph' p₁ q₁) ≤ φ.eval (FractionGraph' a1 b1) := by
        exact (φ.mono_cohom _ _ hcohom₁')
      have hlo₂ : φ.eval (FractionGraph' a b) ≤ φ.eval (FractionGraph' p₂ q₂) := by
        exact (φ.mono_cohom _ _ hcohom₂)
      have hhi₂ : φ.eval (FractionGraph' p₂ q₂) ≤ φ.eval (FractionGraph' a1 b1) := by
        exact (φ.mono_cohom _ _ hcohom₂')
      have h1 :
          φ.eval (FractionGraph' p₁ q₁) - φ.eval (FractionGraph' p₂ q₂) ≤
            φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) := by
        linarith [hhi₁, hlo₂]
      have h2 :
          φ.eval (FractionGraph' p₂ q₂) - φ.eval (FractionGraph' p₁ q₁) ≤
            φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) := by
        linarith [hhi₂, hlo₁]
      have hdiff_nonneg :
          0 ≤ φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) := by
        linarith [hhi₁, hlo₁]
      have hmem :
          |φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)| ∈
            spectralDistanceSet (FractionGraph' a1 b1) (FractionGraph' a b) :=
        ⟨φ, rfl⟩
      have hsup_ge :
          φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) ≤
            sSup (spectralDistanceSet (FractionGraph' a1 b1) (FractionGraph' a b)) := by
        have hsup :=
          le_csSup
            (asympSpecDistance_bdd_above (FractionGraph' a1 b1) (FractionGraph' a b))
            hmem
        simpa [abs_of_nonneg hdiff_nonneg] using hsup
      have hle_abs :
          |φ.eval (FractionGraph' p₁ q₁) - φ.eval (FractionGraph' p₂ q₂)| ≤
            φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) :=
        (abs_sub_le_iff.mpr ⟨h1, h2⟩)
      exact le_trans hle_abs hsup_ge
  exact lt_of_le_of_lt hdist_le hendpoint_lt

/-- Theorem 3.14(c): If p_n/q_n → r (irrational), then E_{p_n/q_n} is Cauchy.

    The Cauchy condition: for all ε > 0, there exists N such that for all n, m ≥ N,
    asympSpecDistance(E_{p_n/q_n}, E_{p_m/q_m}) < ε.

    Proof: Use uniform continuity at irrational r (Theorem 3.14(b)). -/
theorem fractionGraph_cauchy_irrational (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ps qs : ℕ → ℕ) [∀ n, NeZero (ps n)]
    (hqs_pos : ∀ n, 0 < qs n)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℝ) / qs n) Filter.atTop (nhds r)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      asympSpecDistance (FractionGraph' (ps n) (qs n))
                        (FractionGraph' (ps m) (qs m)) < ε := by
  intro ε hε
  -- Get δ from uniform continuity
  obtain ⟨δ, hδ_pos, hδ⟩ := fractionGraph_uniform_continuity_irrational r hr hirr ε hε
  -- Since ps n / qs n → r, eventually |ps n / qs n - r| < δ
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv δ hδ_pos
  use N
  intro n m hn hm
  have hps_pos_n : 0 < ps n := NeZero.pos (ps n)
  have hps_pos_m : 0 < ps m := NeZero.pos (ps m)
  have hdist_n := hN n hn
  have hdist_m := hN m hm
  rw [Real.dist_eq] at hdist_n hdist_m
  exact hδ (ps n) (qs n) (ps m) (qs m) hps_pos_n hps_pos_m
    (hqs_pos n) (hqs_pos m) (h2qs n) (h2qs m) hdist_n hdist_m

/-! ### Non-Completeness -/

/-- Helper: FractionGraph' and fractionGraphAsGraph are definitionally equal.
    This allows us to use `Universality.chilemma`. -/
theorem FractionGraph_eq_fractionGraphAsGraph (p q : ℕ) [NeZero p] :
    FractionGraph' p q = Universality.fractionGraphAsGraph p q := rfl

/-- χ̄_f(E_{p/q}) = p/q for fraction graphs.
    This follows from `Universality.chilemma`. -/
theorem chibar_spectralPoint_fractionGraph (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    AsymptoticSpectrumGraphs.chibar_spectralPoint.eval (FractionGraph' p q) = (p : ℝ) / q := by
  rw [FractionGraph_eq_fractionGraphAsGraph]
  exact Universality.chilemma p q hq h2q

theorem chibar_is_rational (G : Graph) :
    ∃ q : ℚ, AsymptoticSpectrumGraphs.chibar_spectralPoint.eval G = q := by
  classical
  by_cases hV : Nonempty G.V
  · haveI : Nonempty G.V := hV
    simpa [AsymptoticSpectrumGraphs.chibar_spectralPoint,
      AsymptoticSpectrumGraphs.fractionalCliqueCovering_finite,
        AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber_finite] using
      (AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber_rational (G := G.graph))
  · have hV' : IsEmpty G.V := by
      simpa [not_nonempty_iff] using hV
    haveI : IsEmpty G.V := hV'
    let emptycover : AsymptoticSpectrumGraphs.FractionalCliqueCover G.graph :=
      { cliques := ∅
        weights := fun _ => 0
        isClique := fun _ h => (Finset.notMem_empty _ h).elim
        nonneg := fun _ h => (Finset.notMem_empty _ h).elim
        covers := fun v => (hV'.false v).elim }
    have hinf_bdd :
        BddBelow (Set.range (fun c : AsymptoticSpectrumGraphs.FractionalCliqueCover G.graph =>
          c.totalWeight)) := by
      refine ⟨0, ?_⟩
      intro x ⟨c, hc⟩
      rw [← hc]
      exact c.totalWeight_nonneg
    have hle : AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber G.graph ≤ 0 := by
      unfold AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber
      apply ciInf_le_of_le hinf_bdd emptycover
      simp [AsymptoticSpectrumGraphs.FractionalCliqueCover.totalWeight, emptycover]
    have hge : 0 ≤ AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber G.graph := by
      haveI : Nonempty (AsymptoticSpectrumGraphs.FractionalCliqueCover G.graph) :=
        AsymptoticSpectrumGraphs.FractionalCliqueCover.exists_empty (G := G.graph) hV'
      exact AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber_nonneg (G := G.graph)
    have hzero : AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber G.graph = 0 :=
      le_antisymm hle hge
    refine ⟨0, ?_⟩
    simp [AsymptoticSpectrumGraphs.chibar_spectralPoint,
      AsymptoticSpectrumGraphs.fractionalCliqueCovering_finite,
        AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber_finite, hzero]

/-- If spectral values converge, then φ(G_n) → φ(limit G) for all spectral points.
    This follows from the definition of asymptotic spectrum distance. -/
theorem spectral_converges_pointwise (Gs : ℕ → Graph) (H : Graph)
    (hconv : ConvergesTo Gs H) (φ : SpectralPoint) :
    Filter.Tendsto (fun n => φ.eval (Gs n)) Filter.atTop (nhds (φ.eval H)) := by
  unfold ConvergesTo at hconv
  rw [Metric.tendsto_atTop] at hconv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  use N
  intro n hn
  rw [Real.dist_eq]
  have hdist := spectralPoint_dist_le (Gs n) H φ
  calc |φ.eval (Gs n) - φ.eval H|
      ≤ asympSpecDistance (Gs n) H := hdist
    _ < ε := by
        have h := hN n hn
        rw [Real.dist_0_eq_abs, abs_of_nonneg (asympSpecDistance_nonneg (Gs n) H)] at h
        exact h

/-- Corollary 3.16: There exist Cauchy sequences of fraction graphs with
    no finite graph as limit point.

    Proof: If p_n/q_n → r (irrational), then χ̄_f(E_{p_n/q_n}) = p_n/q_n → r.
    But χ̄_f(G) is rational for any finite graph G, contradicting convergence. -/
theorem fractionGraph_no_finite_limit (r : ℝ) (_hr : 2 ≤ r) (hirr : Irrational r)
    (ps qs : ℕ → ℕ) [∀ n, NeZero (ps n)]
    (hqs_pos : ∀ n, 0 < qs n)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℝ) / qs n) Filter.atTop (nhds r)) :
    ¬∃ G : Graph, ConvergesTo (fun n => FractionGraph' (ps n) (qs n)) G := by
  intro ⟨G, hconvG⟩
  -- Let φ = χ̄_f
  let φ := AsymptoticSpectrumGraphs.chibar_spectralPoint
  -- φ(E_{p_n/q_n}) → φ(G) by spectral convergence
  have hφ_conv := spectral_converges_pointwise
    (fun n => FractionGraph' (ps n) (qs n)) G hconvG φ
  -- φ(E_{p_n/q_n}) = p_n/q_n
  have hφ_val : ∀ n, φ.eval (FractionGraph' (ps n) (qs n)) = (ps n : ℝ) / (qs n) := by
    intro n
    exact chibar_spectralPoint_fractionGraph (ps n) (qs n) (hqs_pos n) (h2qs n)
  -- So p_n/q_n → φ(G)
  have hφ_conv' : Filter.Tendsto (fun n => (ps n : ℝ) / (qs n)) Filter.atTop (nhds (φ.eval G)) := by
    convert hφ_conv using 1
    ext n
    exact (hφ_val n).symm
  -- By uniqueness of limits: φ(G) = r
  have hφ_eq_r : φ.eval G = r := tendsto_nhds_unique hφ_conv' hconv
  -- But χ̄_f(G) is rational
  obtain ⟨q, hq⟩ := chibar_is_rational G
  -- So r is rational
  have hr_rat : r = (q : ℝ) := by
    rw [← hφ_eq_r, hq]
  -- This contradicts r being irrational
  have hq_rat : (q : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := ⟨q, rfl⟩
  rw [hr_rat] at hirr
  exact hirr hq_rat

/-! ### Right-continuity wrappers for `ℕ+` arguments (proofs of `main_right_continuous*`) -/

/-- Proof of `main_right_continuous`: Theorem 3.7(a) wrapper for `ℕ+`
    arguments. Drops the coprimality assumption by reducing `(a, b)` to its
    coprime form `(a', b') = (a / gcd(a, b), b / gcd(a, b))`. The two fraction
    graphs `E_{a/b}` and `E_{a'/b'}` admit mutual cohomomorphisms (same
    rational value), so `φ(E_{a/b}) = φ(E_{a'/b'})`. -/
theorem right_continuous (a b : ℕ+) (h2b : 2 * b ≤ a) (φ : SpectralPoint) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ+),
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      |φ (FractionGraph p q) - φ (FractionGraph a b)| < ε := by
  intro ε hε
  -- Reduce to the coprime case by dividing through by `d := gcd(a, b)`.
  set d : ℕ := Nat.gcd (a : ℕ) (b : ℕ) with hd_def
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left (b : ℕ) a.pos
  have hd_dvd_a : d ∣ (a : ℕ) := Nat.gcd_dvd_left _ _
  have hd_dvd_b : d ∣ (b : ℕ) := Nat.gcd_dvd_right _ _
  set a' : ℕ := (a : ℕ) / d with ha'_def
  set b' : ℕ := (b : ℕ) / d with hb'_def
  have ha'_pos : 0 < a' :=
    Nat.div_pos (Nat.le_of_dvd a.pos hd_dvd_a) hd_pos
  have hb'_pos : 0 < b' :=
    Nat.div_pos (Nat.le_of_dvd b.pos hd_dvd_b) hd_pos
  have ha_eq : (a : ℕ) = a' * d := (Nat.div_mul_cancel hd_dvd_a).symm
  have hb_eq : (b : ℕ) = b' * d := (Nat.div_mul_cancel hd_dvd_b).symm
  have h2b_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2b
  have h2b' : 2 * b' ≤ a' :=
    Nat.le_of_mul_le_mul_right (by nlinarith [ha_eq, hb_eq]) hd_pos
  have hcoprime' : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hd_pos
  have hab_eq : ((a : ℕ) : ℚ) / (b : ℕ) = (a' : ℚ) / b' := by
    rw [ha_eq, hb_eq, Nat.cast_mul, Nat.cast_mul]
    have hd_q : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    have hb'_q : ((b' : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hb'_pos.ne'
    field_simp
  haveI : NeZero a' := ⟨ha'_pos.ne'⟩
  -- Apply the coprime-only right-continuity at (a', b').
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    fractionGraph_rightContinuous φ a' b' ha'_pos hb'_pos h2b' hcoprime' ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro p q hab hdiff
  -- Derive `h2q : 2*q ≤ p` from `h2b` and `hab`:
  -- `2 = (2*b)/b ≤ a/b ≤ p/q`, hence `2*q ≤ p`.
  have h2q : 2 * q ≤ p := by
    have hb_pos_q : (0 : ℚ) < (b : ℕ) := by exact_mod_cast b.pos
    have hq_pos_q : (0 : ℚ) < (q : ℕ) := by exact_mod_cast q.pos
    have h2_le_ab : (2 : ℚ) ≤ ((a : ℕ+) : ℚ) / ((b : ℕ+) : ℚ) := by
      rw [le_div_iff₀ hb_pos_q]
      have : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2b
      exact_mod_cast this
    have h2_le_pq : (2 : ℚ) ≤ ((p : ℕ+) : ℚ) / ((q : ℕ+) : ℚ) := le_trans h2_le_ab hab
    rw [le_div_iff₀ hq_pos_q] at h2_le_pq
    have hnat : 2 * (q : ℕ) ≤ (p : ℕ) := by exact_mod_cast h2_le_pq
    exact_mod_cast hnat
  -- Translate `a/b ≤ p/q` and `p/q - a/b < δ` to the (a', b') frame.
  have hab' : ((a' : ℕ) : ℚ) / b' ≤ (p : ℚ) / q := by
    have h := hab
    rw [show ((a : ℕ+) : ℚ) = ((a : ℕ) : ℚ) from rfl,
        show ((b : ℕ+) : ℚ) = ((b : ℕ) : ℚ) from rfl] at h
    rw [hab_eq] at h
    exact h
  have hdiff' : (p : ℚ) / q - (a' : ℚ) / b' < δ := by
    have h := hdiff
    rw [show ((a : ℕ+) : ℚ) = ((a : ℕ) : ℚ) from rfl,
        show ((b : ℕ+) : ℚ) = ((b : ℕ) : ℚ) from rfl] at h
    rw [hab_eq] at h
    exact h
  -- φ-difference bound at (a', b').
  have hφ_diff' :
      |φ.eval (FractionGraph' (p : ℕ) q) - φ.eval (FractionGraph' a' b')| < ε :=
    hδ p q p.pos q.pos h2q hab' hdiff'
  -- `FractionGraph' (p : ℕ) q = FractionGraph p q` definitionally.
  have hF_p : (FractionGraph' (p : ℕ) q : Graph) = FractionGraph p q := rfl
  -- The fraction graphs `E_{a/b}` and `E_{a'/b'}` admit mutual
  -- cohomomorphisms, hence `φ(E_{a/b}) = φ(E_{a'/b'})` by `φ.mono_cohom`
  -- applied in both directions.
  have hle1 : (a' : ℚ) / b' ≤ ((a : ℕ) : ℚ) / (b : ℕ) := le_of_eq hab_eq.symm
  have hle2 : ((a : ℕ) : ℚ) / (b : ℕ) ≤ (a' : ℚ) / b' := le_of_eq hab_eq
  have hcohom1 :=
    (fractionGraph_ordering a' b' (a : ℕ) (b : ℕ) hb'_pos b.pos h2b' h2b_nat).mp hle1
  have hcohom2 :=
    (fractionGraph_ordering (a : ℕ) (b : ℕ) a' b' b.pos hb'_pos h2b_nat h2b').mp hle2
  have hφle1 : φ.eval (FractionGraph' a' b') ≤ φ.eval (FractionGraph a b) :=
    φ.mono_cohom (FractionGraph' a' b') (FractionGraph a b) (by simpa using hcohom1)
  have hφle2 : φ.eval (FractionGraph a b) ≤ φ.eval (FractionGraph' a' b') :=
    φ.mono_cohom (FractionGraph a b) (FractionGraph' a' b') (by simpa using hcohom2)
  have hφ_eq : φ.eval (FractionGraph' a' b') = φ.eval (FractionGraph a b) :=
    le_antisymm hφle1 hφle2
  -- Rewrite the (a', b') bound to (a, b), and `FractionGraph'` to `FractionGraph`.
  rw [hF_p, hφ_eq] at hφ_diff'
  exact hφ_diff'

/-- Proof of `main_right_continuous_alpha`: α-analogue of Theorem 3.7(a)
    wrapper for `ℕ+` arguments. The map `p/q ↦ ⌊p/q⌋` is locally constant
    just to the right of `a/b`; concretely, take
    `δ := (⌊a/b⌋ + 1) - a/b > 0` in ℚ; then for any `p/q ∈ [a/b, a/b + δ)`
    with `2q ≤ p`, we have `⌊p/q⌋ = ⌊a/b⌋`, hence
    `α(E_{p/q}) = α(E_{a/b})`. -/
theorem right_continuous_alpha (a b : ℕ+) (h2b : 2 * b ≤ a) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ+),
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      |((fractionGraph p q).indepNum : ℝ) -
        ((fractionGraph a b).indepNum : ℝ)| < ε := by
  intro ε hε
  -- Set δ := (⌊a/b⌋ + 1 : ℚ) - (a : ℚ)/b > 0.
  set N : ℕ := (a : ℕ) / (b : ℕ) with hN_def
  set δ : ℚ := ((N : ℚ) + 1) - (a : ℚ) / b with hδ_def
  have hb_pos : (0 : ℚ) < (b : ℕ) := by exact_mod_cast b.pos
  have hN_le_ab : ((N : ℚ)) ≤ (a : ℚ) / b := by
    rw [le_div_iff₀ hb_pos]
    have : N * (b : ℕ) ≤ (a : ℕ) := Nat.div_mul_le_self _ _
    exact_mod_cast this
  have hab_lt_N1 : (a : ℚ) / b < (N : ℚ) + 1 := by
    rw [div_lt_iff₀ hb_pos]
    have h := Nat.lt_div_mul_add (a := (a : ℕ)) b.pos
    -- h : a < a / b * b + b
    have : ((a : ℕ) : ℚ) < ((N * (b : ℕ) + (b : ℕ) : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; linarith
  refine ⟨δ, hδ_pos, ?_⟩
  intro p q hab_le hdiff
  -- Derive `h2q : 2*q ≤ p` from `h2b` and `hab_le`.
  have h2q : 2 * q ≤ p := by
    have hb_pos_q : (0 : ℚ) < (b : ℕ) := by exact_mod_cast b.pos
    have hq_pos_q : (0 : ℚ) < (q : ℕ) := by exact_mod_cast q.pos
    have h2_le_ab : (2 : ℚ) ≤ ((a : ℕ+) : ℚ) / ((b : ℕ+) : ℚ) := by
      rw [le_div_iff₀ hb_pos_q]
      have : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2b
      exact_mod_cast this
    have h2_le_pq : (2 : ℚ) ≤ ((p : ℕ+) : ℚ) / ((q : ℕ+) : ℚ) := le_trans h2_le_ab hab_le
    rw [le_div_iff₀ hq_pos_q] at h2_le_pq
    have hnat : 2 * (q : ℕ) ≤ (p : ℕ) := by exact_mod_cast h2_le_pq
    exact_mod_cast hnat
  -- Goal: |α(E_{p/q}) - α(E_{a/b})| < ε. We prove the two are equal.
  -- For p/q ∈ [a/b, N+1), Nat.div p q = N.
  have hpq_lt : (p : ℚ) / q < (N : ℚ) + 1 := by
    have : (p : ℚ) / q < (a : ℚ) / b + δ := by linarith
    rw [hδ_def] at this
    linarith
  have hpq_ge_N : ((N : ℚ)) ≤ (p : ℚ) / q := le_trans hN_le_ab hab_le
  have hq_pos_q : (0 : ℚ) < (q : ℕ) := by exact_mod_cast q.pos
  -- From p/q ≥ N: N * q ≤ p.
  have hNq_le_p : N * (q : ℕ) ≤ (p : ℕ) := by
    have h1 : (N : ℚ) * (q : ℕ) ≤ (p : ℕ) := by
      rw [le_div_iff₀ hq_pos_q] at hpq_ge_N
      exact_mod_cast hpq_ge_N
    exact_mod_cast h1
  -- From p/q < N+1: p < (N+1)*q.
  have hp_lt_N1q : (p : ℕ) < (N + 1) * (q : ℕ) := by
    have h1 : ((p : ℕ) : ℚ) < ((N + 1) * (q : ℕ) : ℕ) := by
      rw [div_lt_iff₀ hq_pos_q] at hpq_lt
      push_cast at hpq_lt ⊢
      linarith
    exact_mod_cast h1
  -- Conclude p / q = N.
  have hpq_div_eq : (p : ℕ) / (q : ℕ) = N := by
    have h_le : (p : ℕ) / (q : ℕ) ≤ N := by
      have := (Nat.div_lt_iff_lt_mul q.pos).mpr hp_lt_N1q
      omega
    have h_ge : N ≤ (p : ℕ) / (q : ℕ) := (Nat.le_div_iff_mul_le q.pos).mpr hNq_le_p
    omega
  -- And a/b is already such that Nat.div a b = N (by definition of N).
  -- So both indepNums equal N.
  have h2q_nat : 2 * (q : ℕ) ≤ (p : ℕ) := by exact_mod_cast h2q
  have h2b_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2b
  have hα_p : (fractionGraph p q).indepNum = N := by
    rw [fractionGraph_independenceNumber (p : ℕ) (q : ℕ) q.pos h2q_nat]
    exact hpq_div_eq
  have hα_a : (fractionGraph a b).indepNum = N := by
    rw [fractionGraph_independenceNumber (a : ℕ) (b : ℕ) b.pos h2b_nat]
  rw [hα_p, hα_a]
  simp [hε]

/-- Proof of `main_right_continuous_shannonCapacity`: Θ-analogue of
    Theorem 3.7(a) wrapper for `ℕ+` arguments. Composes the uniform
    right-continuity in distance with the 1-Lipschitz property of Shannon
    capacity (`shannonCapacity_dist_le`). Drops coprimality by reducing
    `(a, b)` to its coprime form `(a', b')`; the two fraction graphs admit
    mutual cohomomorphisms, so `d(E_{a/b}, E_{a'/b'}) = 0`. -/
theorem right_continuous_shannonCapacity (a b : ℕ+) (h2b : 2 * b ≤ a) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ+),
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      |shannonCapacity (FractionGraph p q) - shannonCapacity (FractionGraph a b)| < ε := by
  intro ε hε
  -- Reduce to the coprime case by dividing through by `d := gcd(a, b)`.
  set d : ℕ := Nat.gcd (a : ℕ) (b : ℕ) with hd_def
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left (b : ℕ) a.pos
  have hd_dvd_a : d ∣ (a : ℕ) := Nat.gcd_dvd_left _ _
  have hd_dvd_b : d ∣ (b : ℕ) := Nat.gcd_dvd_right _ _
  set a' : ℕ := (a : ℕ) / d with ha'_def
  set b' : ℕ := (b : ℕ) / d with hb'_def
  have ha'_pos : 0 < a' :=
    Nat.div_pos (Nat.le_of_dvd a.pos hd_dvd_a) hd_pos
  have hb'_pos : 0 < b' :=
    Nat.div_pos (Nat.le_of_dvd b.pos hd_dvd_b) hd_pos
  have ha_eq : (a : ℕ) = a' * d := (Nat.div_mul_cancel hd_dvd_a).symm
  have hb_eq : (b : ℕ) = b' * d := (Nat.div_mul_cancel hd_dvd_b).symm
  have h2b_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2b
  have h2b' : 2 * b' ≤ a' :=
    Nat.le_of_mul_le_mul_right (by nlinarith [ha_eq, hb_eq]) hd_pos
  have hcoprime' : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hd_pos
  have hab_eq : ((a : ℕ) : ℚ) / (b : ℕ) = (a' : ℚ) / b' := by
    rw [ha_eq, hb_eq, Nat.cast_mul, Nat.cast_mul]
    have hd_q : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    have hb'_q : ((b' : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hb'_pos.ne'
    field_simp
  haveI : NeZero a' := ⟨ha'_pos.ne'⟩
  -- Apply the coprime-only uniform right-continuity at (a', b').
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    fractionGraph_rightContinuous_uniform a' b' ha'_pos hb'_pos h2b' hcoprime' ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro p q hab hdiff
  -- Derive `h2q : 2*q ≤ p` from `h2b` and `hab`.
  have h2q : 2 * q ≤ p := by
    have hb_pos_q : (0 : ℚ) < (b : ℕ) := by exact_mod_cast b.pos
    have hq_pos_q : (0 : ℚ) < (q : ℕ) := by exact_mod_cast q.pos
    have h2_le_ab : (2 : ℚ) ≤ ((a : ℕ+) : ℚ) / ((b : ℕ+) : ℚ) := by
      rw [le_div_iff₀ hb_pos_q]
      have : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2b
      exact_mod_cast this
    have h2_le_pq : (2 : ℚ) ≤ ((p : ℕ+) : ℚ) / ((q : ℕ+) : ℚ) := le_trans h2_le_ab hab
    rw [le_div_iff₀ hq_pos_q] at h2_le_pq
    have hnat : 2 * (q : ℕ) ≤ (p : ℕ) := by exact_mod_cast h2_le_pq
    exact_mod_cast hnat
  -- Translate `a/b ≤ p/q` and `p/q - a/b < δ` to the (a', b') frame.
  have hab' : ((a' : ℕ) : ℚ) / b' ≤ (p : ℚ) / q := by
    have h := hab
    rw [show ((a : ℕ+) : ℚ) = ((a : ℕ) : ℚ) from rfl,
        show ((b : ℕ+) : ℚ) = ((b : ℕ) : ℚ) from rfl] at h
    rw [hab_eq] at h
    exact h
  have hdiff' : (p : ℚ) / q - (a' : ℚ) / b' < δ := by
    have h := hdiff
    rw [show ((a : ℕ+) : ℚ) = ((a : ℕ) : ℚ) from rfl,
        show ((b : ℕ+) : ℚ) = ((b : ℕ) : ℚ) from rfl] at h
    rw [hab_eq] at h
    exact h
  -- Distance bound at (a', b').
  have hdist' :
      asympSpecDistance (FractionGraph' (p : ℕ) q) (FractionGraph' a' b') < ε :=
    hδ p q p.pos q.pos h2q hab' hdiff'
  -- `FractionGraph' (p : ℕ) q = FractionGraph p q` definitionally.
  have hF_p : (FractionGraph' (p : ℕ) q : Graph) = FractionGraph p q := rfl
  -- The fraction graphs `E_{a/b}` and `E_{a'/b'}` admit mutual
  -- cohomomorphisms, hence `d(E_{a/b}, E_{a'/b'}) = 0`.
  have hle1 : (a' : ℚ) / b' ≤ ((a : ℕ) : ℚ) / (b : ℕ) := le_of_eq hab_eq.symm
  have hle2 : ((a : ℕ) : ℚ) / (b : ℕ) ≤ (a' : ℚ) / b' := le_of_eq hab_eq
  have hcohom1 :=
    (fractionGraph_ordering a' b' (a : ℕ) (b : ℕ) hb'_pos b.pos h2b' h2b_nat).mp hle1
  have hcohom2 :=
    (fractionGraph_ordering (a : ℕ) (b : ℕ) a' b' b.pos hb'_pos h2b_nat h2b').mp hle2
  have hdist_zero : asympSpecDistance (FractionGraph' a' b') (FractionGraph a b) = 0 := by
    apply asympSpecDistance_eq_zero_of_mutual_cohom
    · -- `(FractionGraph' a' b').graph = fractionGraph a' b'` and
      -- `(FractionGraph a b).graph = fractionGraph a b` both by `rfl`.
      simpa using hcohom1
    · simpa using hcohom2
  have hdist_zero' : asympSpecDistance (FractionGraph a b) (FractionGraph' a' b') = 0 :=
    (asympSpecDistance_symm _ _).trans hdist_zero
  -- Triangle inequality + zero distance gives
  -- `d(E_{p/q}, E_{a/b}) ≤ d(E_{p/q}, E_{a'/b'})`.
  have hdist :
      asympSpecDistance (FractionGraph p q) (FractionGraph a b) < ε := by
    have htri := asympSpecDistance_triangle
      (FractionGraph p q) (FractionGraph' a' b') (FractionGraph a b)
    have hsymm : asympSpecDistance (FractionGraph' a' b') (FractionGraph a b)
        = 0 := hdist_zero
    -- Rewrite `FractionGraph' p q` as `FractionGraph p q` in `hdist'`.
    rw [hF_p] at hdist'
    linarith
  -- Shannon capacity is 1-Lipschitz.
  calc |shannonCapacity (FractionGraph p q) - shannonCapacity (FractionGraph a b)|
      ≤ asympSpecDistance (FractionGraph p q) (FractionGraph a b) :=
        shannonCapacity_dist_le _ _
    _ < ε := hdist

/-- Proof of `main_right_continuous_uniform`: Theorem 3.7(b) wrapper for `ℕ+`
    arguments. Drops the coprimality assumption by reducing `(a, b)` to its
    coprime form `(a', b')`; the two fraction graphs admit mutual
    cohomomorphisms, so `d(E_{a/b}, E_{a'/b'}) = 0`. -/
theorem right_continuous_uniform (a b : ℕ+) (h2b : 2 * b ≤ a) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ+),
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      asympSpecDistance (FractionGraph p q) (FractionGraph a b) < ε := by
  intro ε hε
  -- Reduce to the coprime case by dividing through by `d := gcd(a, b)`.
  set d : ℕ := Nat.gcd (a : ℕ) (b : ℕ) with hd_def
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left (b : ℕ) a.pos
  have hd_dvd_a : d ∣ (a : ℕ) := Nat.gcd_dvd_left _ _
  have hd_dvd_b : d ∣ (b : ℕ) := Nat.gcd_dvd_right _ _
  set a' : ℕ := (a : ℕ) / d with ha'_def
  set b' : ℕ := (b : ℕ) / d with hb'_def
  have ha'_pos : 0 < a' :=
    Nat.div_pos (Nat.le_of_dvd a.pos hd_dvd_a) hd_pos
  have hb'_pos : 0 < b' :=
    Nat.div_pos (Nat.le_of_dvd b.pos hd_dvd_b) hd_pos
  have ha_eq : (a : ℕ) = a' * d := (Nat.div_mul_cancel hd_dvd_a).symm
  have hb_eq : (b : ℕ) = b' * d := (Nat.div_mul_cancel hd_dvd_b).symm
  have h2b_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2b
  have h2b' : 2 * b' ≤ a' :=
    Nat.le_of_mul_le_mul_right (by nlinarith [ha_eq, hb_eq]) hd_pos
  have hcoprime' : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hd_pos
  have hab_eq : ((a : ℕ) : ℚ) / (b : ℕ) = (a' : ℚ) / b' := by
    rw [ha_eq, hb_eq, Nat.cast_mul, Nat.cast_mul]
    have hd_q : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    have hb'_q : ((b' : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hb'_pos.ne'
    field_simp
  haveI : NeZero a' := ⟨ha'_pos.ne'⟩
  -- Apply the coprime-only uniform right-continuity at (a', b').
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    fractionGraph_rightContinuous_uniform a' b' ha'_pos hb'_pos h2b' hcoprime' ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro p q hab hdiff
  -- Derive `h2q : 2*q ≤ p` from `h2b` and `hab`.
  have h2q : 2 * q ≤ p := by
    have hb_pos_q : (0 : ℚ) < (b : ℕ) := by exact_mod_cast b.pos
    have hq_pos_q : (0 : ℚ) < (q : ℕ) := by exact_mod_cast q.pos
    have h2_le_ab : (2 : ℚ) ≤ ((a : ℕ+) : ℚ) / ((b : ℕ+) : ℚ) := by
      rw [le_div_iff₀ hb_pos_q]
      have : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2b
      exact_mod_cast this
    have h2_le_pq : (2 : ℚ) ≤ ((p : ℕ+) : ℚ) / ((q : ℕ+) : ℚ) := le_trans h2_le_ab hab
    rw [le_div_iff₀ hq_pos_q] at h2_le_pq
    have hnat : 2 * (q : ℕ) ≤ (p : ℕ) := by exact_mod_cast h2_le_pq
    exact_mod_cast hnat
  -- Translate `a/b ≤ p/q` and `p/q - a/b < δ` to the (a', b') frame.
  have hab' : ((a' : ℕ) : ℚ) / b' ≤ (p : ℚ) / q := by
    have h := hab
    rw [show ((a : ℕ+) : ℚ) = ((a : ℕ) : ℚ) from rfl,
        show ((b : ℕ+) : ℚ) = ((b : ℕ) : ℚ) from rfl] at h
    rw [hab_eq] at h
    exact h
  have hdiff' : (p : ℚ) / q - (a' : ℚ) / b' < δ := by
    have h := hdiff
    rw [show ((a : ℕ+) : ℚ) = ((a : ℕ) : ℚ) from rfl,
        show ((b : ℕ+) : ℚ) = ((b : ℕ) : ℚ) from rfl] at h
    rw [hab_eq] at h
    exact h
  -- Distance bound at (a', b').
  have hdist' :
      asympSpecDistance (FractionGraph' (p : ℕ) q) (FractionGraph' a' b') < ε :=
    hδ p q p.pos q.pos h2q hab' hdiff'
  -- `FractionGraph' (p : ℕ) q = FractionGraph p q` definitionally.
  have hF_p : (FractionGraph' (p : ℕ) q : Graph) = FractionGraph p q := rfl
  -- The fraction graphs `E_{a/b}` and `E_{a'/b'}` admit mutual
  -- cohomomorphisms, hence `d(E_{a/b}, E_{a'/b'}) = 0`.
  have hle1 : (a' : ℚ) / b' ≤ ((a : ℕ) : ℚ) / (b : ℕ) := le_of_eq hab_eq.symm
  have hle2 : ((a : ℕ) : ℚ) / (b : ℕ) ≤ (a' : ℚ) / b' := le_of_eq hab_eq
  have hcohom1 :=
    (fractionGraph_ordering a' b' (a : ℕ) (b : ℕ) hb'_pos b.pos h2b' h2b_nat).mp hle1
  have hcohom2 :=
    (fractionGraph_ordering (a : ℕ) (b : ℕ) a' b' b.pos hb'_pos h2b_nat h2b').mp hle2
  have hdist_zero : asympSpecDistance (FractionGraph' a' b') (FractionGraph a b) = 0 := by
    apply asympSpecDistance_eq_zero_of_mutual_cohom
    · simpa using hcohom1
    · simpa using hcohom2
  -- Triangle inequality + zero distance gives
  -- `d(E_{p/q}, E_{a/b}) < ε`.
  have htri := asympSpecDistance_triangle
    (FractionGraph p q) (FractionGraph' a' b') (FractionGraph a b)
  -- Rewrite `FractionGraph' p q` as `FractionGraph p q` in `hdist'`.
  rw [hF_p] at hdist'
  linarith

/-- Proof of `main_sup_eq_inf_irrational_alpha`: Theorem 3.14(a) for α.
    For irrational `r ≥ 2`,
    `sup_{a/b < r} α(E_{a/b}) = inf_{a/b > r} α(E_{a/b})`; both equal
    `⌊r⌋ : ℝ`. -/
theorem sup_eq_inf_irrational_alpha (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) :
    sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
        x = ((fractionGraph a b).indepNum : ℝ)} =
    sInf {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
        x = ((fractionGraph a b).indepNum : ℝ)} := by
  -- Strategy: both sides equal n := ⌊r⌋ as a real number.
  set n : ℕ := ⌊r⌋₊ with hn_def
  -- r > 2 (since r ≥ 2 and r irrational).
  have hr_gt_2 : (2 : ℝ) < r := by
    rcases lt_or_eq_of_le hr with h | h
    · exact h
    · exfalso; apply hirr; exact ⟨2, by simp [← h]⟩
  have hr_pos : (0 : ℝ) < r := by linarith
  have hn_le_r : (n : ℝ) ≤ r := Nat.floor_le (le_of_lt hr_pos)
  -- ⌊r⌋ ≥ 2 since r ≥ 2.
  have hn_ge_2 : 2 ≤ n :=
    Nat.le_floor (by exact_mod_cast hr : ((2 : ℕ) : ℝ) ≤ r)
  -- r is not an integer (since irrational), so ⌊r⌋ < r < ⌊r⌋ + 1.
  have hn_lt_r : (n : ℝ) < r := by
    rcases lt_or_eq_of_le hn_le_r with h | h
    · exact h
    · exfalso; apply hirr; exact ⟨n, by simp [← h]⟩
  have hr_lt_n1 : r < (n : ℝ) + 1 := Nat.lt_floor_add_one r
  have hn_pos : 0 < n := by omega
  -- A reusable lemma: for any a b : ℕ+ with 2*b ≤ a, the real α(E_{a/b}) cast
  -- equals (Nat.div a b : ℝ).
  have h_indep_eq : ∀ (a b : ℕ+), 2 * (b : ℕ) ≤ (a : ℕ) →
      ((fractionGraph a b).indepNum : ℝ) = (((a : ℕ) / (b : ℕ) : ℕ) : ℝ) := fun a b h => by
    rw [fractionGraph_independenceNumber (a : ℕ) (b : ℕ) b.pos h]
  -- a/b ≤ r ↔ (a : ℝ) / b ≤ r is the same since the coercion is via ℕ.
  -- Define the sup and inf sets explicitly.
  -- Below set:
  let S_below : Set ℝ := {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
      x = ((fractionGraph a b).indepNum : ℝ)}
  let S_above : Set ℝ := {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
      x = ((fractionGraph a b).indepNum : ℝ)}
  -- Lemma: for any a b ∈ ℕ+ with 2b ≤ a, ⌊a/b⌋ as natural ≤ a/b as real.
  have h_floor_le_real : ∀ (a b : ℕ+), (((a : ℕ) / (b : ℕ) : ℕ) : ℝ) ≤
      ((a : ℕ+) : ℝ) / ((b : ℕ+) : ℝ) := fun a b => by
    have hb_pos : (0 : ℝ) < ((b : ℕ+) : ℝ) := by exact_mod_cast b.pos
    rw [le_div_iff₀ hb_pos]
    have h1 : ((a : ℕ) / (b : ℕ) : ℕ) * (b : ℕ) ≤ (a : ℕ) := Nat.div_mul_le_self _ _
    have : ((((a : ℕ) / (b : ℕ) : ℕ) * (b : ℕ) : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by
      exact_mod_cast h1
    have hcast_a : ((a : ℕ+) : ℝ) = ((a : ℕ) : ℝ) := by simp
    have hcast_b : ((b : ℕ+) : ℝ) = ((b : ℕ) : ℝ) := by simp
    rw [hcast_a, hcast_b]
    calc (((a : ℕ) / (b : ℕ) : ℕ) : ℝ) * ((b : ℕ) : ℝ)
        = ((((a : ℕ) / (b : ℕ) : ℕ) * (b : ℕ) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((a : ℕ) : ℝ) := this
  -- Witness for the sup set: (n, 1).
  have h1_pos : (0 : ℕ) < 1 := Nat.one_pos
  have h2_one_le_n : 2 * (1 : ℕ) ≤ n := by omega
  have h_below_witness : (n : ℝ) ∈ S_below := by
    refine ⟨⟨n, hn_pos⟩, 1, ?_, ?_, ?_⟩
    · -- 2 * 1 ≤ ⟨n, _⟩ in ℕ+ — translate to ℕ.
      have h2_one_pnat : ((2 * (1 : ℕ+) : ℕ+) : ℕ) = 2 := rfl
      have hcast : (((⟨n, hn_pos⟩ : ℕ+) : ℕ)) = n := rfl
      change (2 * (1 : ℕ+)) ≤ ⟨n, hn_pos⟩
      have hpnat_le : ((2 * (1 : ℕ+) : ℕ+) : ℕ) ≤ ((⟨n, hn_pos⟩ : ℕ+) : ℕ) := by
        rw [h2_one_pnat, hcast]; exact hn_ge_2
      exact hpnat_le
    · -- (n : ℝ) / 1 < r
      change ((⟨n, hn_pos⟩ : ℕ+) : ℝ) / ((1 : ℕ+) : ℝ) < r
      simp only [PNat.val_ofNat, Nat.cast_one, div_one]
      exact hn_lt_r
    · -- x = α(E_{n/1}) = n.
      rw [h_indep_eq ⟨n, hn_pos⟩ 1 (by change 2 * 1 ≤ n; exact h2_one_le_n)]
      have hn1 : (⟨n, hn_pos⟩ : ℕ+).val / (1 : ℕ+).val = n := by
        change n / 1 = n; exact Nat.div_one n
      exact_mod_cast hn1.symm
  -- Sup ≤ n.
  have h_sup_le : sSup S_below ≤ (n : ℝ) := by
    apply csSup_le ⟨_, h_below_witness⟩
    rintro x ⟨a, b, h2ab, hab_lt_r, rfl⟩
    have h2ab_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2ab
    rw [h_indep_eq a b h2ab_nat]
    have h_floor_le : (((a : ℕ) / (b : ℕ) : ℕ) : ℝ) ≤ ((a : ℕ+) : ℝ) / ((b : ℕ+) : ℝ) :=
      h_floor_le_real a b
    have h_floor_le_r : (((a : ℕ) / (b : ℕ) : ℕ) : ℝ) ≤ r :=
      le_of_lt (lt_of_le_of_lt h_floor_le hab_lt_r)
    have h_floor_le_n : ((a : ℕ) / (b : ℕ) : ℕ) ≤ n :=
      Nat.le_floor h_floor_le_r
    exact_mod_cast h_floor_le_n
  -- Sup ≥ n: witness gives n in the set.
  have h_sup_bddAbove : BddAbove S_below := by
    refine ⟨(n : ℝ), ?_⟩
    rintro x ⟨a, b, h2ab, hab_lt_r, rfl⟩
    have h2ab_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2ab
    rw [h_indep_eq a b h2ab_nat]
    have h_floor_le : (((a : ℕ) / (b : ℕ) : ℕ) : ℝ) ≤ ((a : ℕ+) : ℝ) / ((b : ℕ+) : ℝ) :=
      h_floor_le_real a b
    have h_floor_le_r : (((a : ℕ) / (b : ℕ) : ℕ) : ℝ) ≤ r :=
      le_of_lt (lt_of_le_of_lt h_floor_le hab_lt_r)
    have h_floor_le_n : ((a : ℕ) / (b : ℕ) : ℕ) ≤ n :=
      Nat.le_floor h_floor_le_r
    exact_mod_cast h_floor_le_n
  have h_sup_ge : (n : ℝ) ≤ sSup S_below := le_csSup h_sup_bddAbove h_below_witness
  have h_sup_eq : sSup S_below = (n : ℝ) := le_antisymm h_sup_le h_sup_ge
  -- Above set: find a rational q ∈ (r, n+1).
  obtain ⟨q, hr_lt_q, hq_lt_n1⟩ := exists_rat_btwn hr_lt_n1
  have hq_pos : (0 : ℝ) < (q : ℝ) := lt_trans hr_pos hr_lt_q
  have hq_num_pos : 0 < q.num := by
    have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    have hnum_pos_real : (0 : ℝ) < (q.num : ℝ) := by
      have := hq_pos
      rw [Rat.cast_def] at this
      exact (div_pos_iff_of_pos_right hden_pos).mp this
    exact_mod_cast hnum_pos_real
  let aQ : ℕ+ := ⟨q.num.toNat, by
    have h : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (le_of_lt hq_num_pos)
    omega⟩
  let bQ : ℕ+ := ⟨q.den, q.pos⟩
  have haQ_val : (aQ : ℕ) = q.num.toNat := rfl
  have hbQ_val : (bQ : ℕ) = q.den := rfl
  have h_aQ_int : ((aQ : ℕ) : ℤ) = q.num := by
    rw [haQ_val]; exact Int.toNat_of_nonneg (le_of_lt hq_num_pos)
  have h_aQ_bQ_eq : ((aQ : ℕ+) : ℝ) / ((bQ : ℕ+) : ℝ) = (q : ℝ) := by
    have h1 : ((aQ : ℕ+) : ℝ) = (q.num : ℝ) := by
      show ((aQ : ℕ) : ℝ) = (q.num : ℝ)
      have : ((aQ : ℕ) : ℤ) = q.num := h_aQ_int
      exact_mod_cast this
    have h2 : ((bQ : ℕ+) : ℝ) = (q.den : ℝ) := by
      show ((bQ : ℕ) : ℝ) = (q.den : ℝ); rw [hbQ_val]
    rw [h1, h2, Rat.cast_def]
  have hbQ_pos_real : (0 : ℝ) < ((bQ : ℕ+) : ℝ) := by
    have := bQ.pos; exact_mod_cast this
  have h_above_aQbQ : ((aQ : ℕ+) : ℝ) / ((bQ : ℕ+) : ℝ) > r := by
    rw [h_aQ_bQ_eq]; exact hr_lt_q
  have h_aQ_bQ_lt_n1 : ((aQ : ℕ+) : ℝ) / ((bQ : ℕ+) : ℝ) < (n : ℝ) + 1 := by
    rw [h_aQ_bQ_eq]; exact hq_lt_n1
  -- 2 * bQ ≤ aQ since (aQ : ℝ) / bQ > r ≥ 2.
  have h2bQ_le_aQ : 2 * bQ ≤ aQ := by
    have h_gt_2 : ((aQ : ℕ+) : ℝ) / ((bQ : ℕ+) : ℝ) > 2 := lt_trans hr_gt_2 h_above_aQbQ
    rw [gt_iff_lt, lt_div_iff₀ hbQ_pos_real] at h_gt_2
    have h_nat : 2 * (bQ : ℕ) < (aQ : ℕ) := by
      have : (2 * ((bQ : ℕ+) : ℝ) : ℝ) < ((aQ : ℕ+) : ℝ) := h_gt_2
      have hcast : ((2 * (bQ : ℕ) : ℕ) : ℝ) < ((aQ : ℕ) : ℝ) := by
        push_cast
        have ha : ((aQ : ℕ+) : ℝ) = ((aQ : ℕ) : ℝ) := by simp
        have hb : ((bQ : ℕ+) : ℝ) = ((bQ : ℕ) : ℝ) := by simp
        rw [ha, hb] at this
        linarith
      exact_mod_cast hcast
    have h_pnat : 2 * (bQ : ℕ) ≤ (aQ : ℕ) := le_of_lt h_nat
    change ((2 * bQ : ℕ+) : ℕ) ≤ ((aQ : ℕ+) : ℕ)
    have : ((2 * bQ : ℕ+) : ℕ) = 2 * (bQ : ℕ) := rfl
    rw [this]; exact h_pnat
  -- Nat.div aQ bQ = n.
  have h2bQ_nat : 2 * (bQ : ℕ) ≤ (aQ : ℕ) := by exact_mod_cast h2bQ_le_aQ
  have h_div_aQ_bQ : (aQ : ℕ) / (bQ : ℕ) = n := by
    have h_lower : n * (bQ : ℕ) ≤ (aQ : ℕ) := by
      -- aQ/bQ > r > n ⇒ aQ > n*bQ.
      have h1 : (n : ℝ) * ((bQ : ℕ+) : ℝ) < ((aQ : ℕ+) : ℝ) := by
        have h_gt_n : ((aQ : ℕ+) : ℝ) / ((bQ : ℕ+) : ℝ) > (n : ℝ) :=
          lt_trans hn_lt_r h_above_aQbQ
        rw [gt_iff_lt, lt_div_iff₀ hbQ_pos_real] at h_gt_n
        linarith
      have h2 : ((n * (bQ : ℕ) : ℕ) : ℝ) < ((aQ : ℕ) : ℝ) := by
        have ha : ((aQ : ℕ+) : ℝ) = ((aQ : ℕ) : ℝ) := by simp
        have hb : ((bQ : ℕ+) : ℝ) = ((bQ : ℕ) : ℝ) := by simp
        rw [ha, hb] at h1
        push_cast; linarith
      have : n * (bQ : ℕ) < (aQ : ℕ) := by exact_mod_cast h2
      omega
    have h_upper : (aQ : ℕ) < (n + 1) * (bQ : ℕ) := by
      rw [div_lt_iff₀ hbQ_pos_real] at h_aQ_bQ_lt_n1
      have ha : ((aQ : ℕ+) : ℝ) = ((aQ : ℕ) : ℝ) := by simp
      have hb : ((bQ : ℕ+) : ℝ) = ((bQ : ℕ) : ℝ) := by simp
      rw [ha, hb] at h_aQ_bQ_lt_n1
      have : ((aQ : ℕ) : ℝ) < ((n + 1) * (bQ : ℕ) : ℕ) := by push_cast; linarith
      exact_mod_cast this
    have h_le : (aQ : ℕ) / (bQ : ℕ) ≤ n := by
      have := (Nat.div_lt_iff_lt_mul bQ.pos).mpr h_upper
      omega
    have h_ge : n ≤ (aQ : ℕ) / (bQ : ℕ) :=
      (Nat.le_div_iff_mul_le bQ.pos).mpr h_lower
    omega
  -- Witness for the above-set: ((aQ, bQ), n).
  have h_above_witness : (n : ℝ) ∈ S_above := by
    refine ⟨aQ, bQ, h2bQ_le_aQ, h_above_aQbQ, ?_⟩
    rw [h_indep_eq aQ bQ h2bQ_nat, h_div_aQ_bQ]
  -- For any (a, b) above r, α(E_{a/b}) ≥ n.
  have h_above_ge_n : ∀ (a b : ℕ+), 2 * b ≤ a → ((a : ℝ) / b > r) →
      (((a : ℕ) / (b : ℕ) : ℕ) : ℝ) ≥ (n : ℝ) := by
    intro a b h2ab hab_gt_r
    have h2ab_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2ab
    have hb_pos_real : (0 : ℝ) < ((b : ℕ+) : ℝ) := by
      have := b.pos; exact_mod_cast this
    have h_ab_gt_n : ((a : ℕ+) : ℝ) / ((b : ℕ+) : ℝ) > (n : ℝ) :=
      lt_trans hn_lt_r hab_gt_r
    rw [gt_iff_lt, lt_div_iff₀ hb_pos_real] at h_ab_gt_n
    have ha : ((a : ℕ+) : ℝ) = ((a : ℕ) : ℝ) := by simp
    have hb : ((b : ℕ+) : ℝ) = ((b : ℕ) : ℝ) := by simp
    rw [ha, hb] at h_ab_gt_n
    have h_nb_lt_a_nat : n * (b : ℕ) < (a : ℕ) := by
      have : ((n * (b : ℕ) : ℕ) : ℝ) < ((a : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h_nat_le : n ≤ (a : ℕ) / (b : ℕ) :=
      (Nat.le_div_iff_mul_le b.pos).mpr (le_of_lt h_nb_lt_a_nat)
    exact_mod_cast h_nat_le
  -- Inf ≥ n.
  have h_inf_ge : (n : ℝ) ≤ sInf S_above := by
    apply le_csInf ⟨_, h_above_witness⟩
    rintro x ⟨a, b, h2ab, hab_gt_r, rfl⟩
    rw [h_indep_eq a b (by exact_mod_cast h2ab)]
    exact h_above_ge_n a b h2ab hab_gt_r
  -- Inf ≤ n.
  have h_inf_bddBelow : BddBelow S_above := by
    refine ⟨(n : ℝ), ?_⟩
    rintro x ⟨a, b, h2ab, hab_gt_r, rfl⟩
    rw [h_indep_eq a b (by exact_mod_cast h2ab)]
    exact h_above_ge_n a b h2ab hab_gt_r
  have h_inf_le : sInf S_above ≤ (n : ℝ) := csInf_le h_inf_bddBelow h_above_witness
  have h_inf_eq : sInf S_above = (n : ℝ) := le_antisymm h_inf_le h_inf_ge
  change sSup S_below = sInf S_above
  rw [h_sup_eq, h_inf_eq]

/-- Proof of `main_sup_eq_inf_irrational_shannonCapacity`: Theorem 3.14(a) for Θ.
    For irrational `r ≥ 2`,
    `sup_{a/b < r} Θ(E_{a/b}) = inf_{a/b > r} Θ(E_{a/b})`.

    Proof strategy (Path B, via duality + 1-Lipschitz):
    * `sSup ≤ sInf`: monotonicity of Θ via cohomomorphism + iInf-monotonicity.
    * `sInf ≤ sSup`: uniform continuity at irrationals
      (`fractionGraph_uniform_continuity_irrational`) + 1-Lipschitz Θ
      (`shannonCapacity_dist_le`). -/
theorem sup_eq_inf_irrational_shannonCapacity (r : ℝ) (hr : 2 ≤ r)
    (hirr : Irrational r) :
    sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
        x = shannonCapacity (FractionGraph a b)} =
    sInf {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
        x = shannonCapacity (FractionGraph a b)} := by
  -- r > 2 (since r ≥ 2 and r irrational).
  have hr_gt_2 : (2 : ℝ) < r := by
    rcases lt_or_eq_of_le hr with h | h
    · exact h
    · exfalso; apply hirr; exact ⟨2, by simp [← h]⟩
  -- ⌊r⌋ ≥ 2.
  set n : ℕ := ⌊r⌋₊ with hn_def
  have hr_pos : (0 : ℝ) < r := by linarith
  have hn_le_r : (n : ℝ) ≤ r := Nat.floor_le (le_of_lt hr_pos)
  have hn_ge_2 : 2 ≤ n :=
    Nat.le_floor (by exact_mod_cast hr : ((2 : ℕ) : ℝ) ≤ r)
  have hn_lt_r : (n : ℝ) < r := by
    rcases lt_or_eq_of_le hn_le_r with h | h
    · exact h
    · exfalso; apply hirr; exact ⟨n, by simp [← h]⟩
  have hr_lt_n1 : r < (n : ℝ) + 1 := Nat.lt_floor_add_one r
  have hn_pos : 0 < n := by omega
  set S_below : Set ℝ := {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
      x = shannonCapacity (FractionGraph a b)}
  set S_above : Set ℝ := {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
      x = shannonCapacity (FractionGraph a b)}
  -- Witness for S_below: (n, 1).
  set aN : ℕ+ := ⟨n, hn_pos⟩ with haN_def
  set bN : ℕ+ := 1 with hbN_def
  have hN1_lt_r : ((aN : ℕ+) : ℝ) / ((bN : ℕ+) : ℝ) < r := by
    change ((n : ℕ) : ℝ) / ((1 : ℕ+) : ℝ) < r
    simp only [PNat.val_ofNat, Nat.cast_one, div_one]
    exact hn_lt_r
  have h2bN_le_aN : 2 * bN ≤ aN := by
    change ((2 * (1 : ℕ+) : ℕ+) : ℕ) ≤ ((aN : ℕ+) : ℕ)
    change 2 ≤ n
    exact hn_ge_2
  have h_below_witness : shannonCapacity (FractionGraph aN bN) ∈ S_below :=
    ⟨aN, bN, h2bN_le_aN, hN1_lt_r, rfl⟩
  -- Witness for S_above: find a rational q ∈ (r, n+1), use (q.num, q.den) as ℕ+.
  obtain ⟨q, hr_lt_q, hq_lt_n1⟩ := exists_rat_btwn hr_lt_n1
  have hq_pos : (0 : ℝ) < (q : ℝ) := lt_trans hr_pos hr_lt_q
  have hq_num_pos : 0 < q.num := by
    have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    have hnum_pos_real : (0 : ℝ) < (q.num : ℝ) := by
      have := hq_pos
      rw [Rat.cast_def] at this
      exact (div_pos_iff_of_pos_right hden_pos).mp this
    exact_mod_cast hnum_pos_real
  set aQ : ℕ+ := ⟨q.num.toNat, by
    have h : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (le_of_lt hq_num_pos)
    omega⟩ with haQ_def
  set bQ : ℕ+ := ⟨q.den, q.pos⟩ with hbQ_def
  have h_aQ_int : ((aQ : ℕ) : ℤ) = q.num :=
    Int.toNat_of_nonneg (le_of_lt hq_num_pos)
  have h_aQ_bQ_eq : ((aQ : ℕ+) : ℝ) / ((bQ : ℕ+) : ℝ) = (q : ℝ) := by
    have h1 : ((aQ : ℕ+) : ℝ) = (q.num : ℝ) := by
      show ((aQ : ℕ) : ℝ) = (q.num : ℝ)
      have : ((aQ : ℕ) : ℤ) = q.num := h_aQ_int
      exact_mod_cast this
    have h2 : ((bQ : ℕ+) : ℝ) = (q.den : ℝ) := by
      show ((bQ : ℕ) : ℝ) = (q.den : ℝ); rfl
    rw [h1, h2, Rat.cast_def]
  have hbQ_pos_real : (0 : ℝ) < ((bQ : ℕ+) : ℝ) := by
    have := bQ.pos; exact_mod_cast this
  have h_above_aQbQ : ((aQ : ℕ+) : ℝ) / ((bQ : ℕ+) : ℝ) > r := by
    rw [h_aQ_bQ_eq]; exact hr_lt_q
  have h2bQ_le_aQ : 2 * bQ ≤ aQ := by
    have h_gt_2 : ((aQ : ℕ+) : ℝ) / ((bQ : ℕ+) : ℝ) > 2 := lt_trans hr_gt_2 h_above_aQbQ
    rw [gt_iff_lt, lt_div_iff₀ hbQ_pos_real] at h_gt_2
    have h_nat : 2 * (bQ : ℕ) < (aQ : ℕ) := by
      have ha : ((aQ : ℕ+) : ℝ) = ((aQ : ℕ) : ℝ) := by simp
      have hb : ((bQ : ℕ+) : ℝ) = ((bQ : ℕ) : ℝ) := by simp
      rw [ha, hb] at h_gt_2
      have hcast : ((2 * (bQ : ℕ) : ℕ) : ℝ) < ((aQ : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast hcast
    change ((2 * bQ : ℕ+) : ℕ) ≤ ((aQ : ℕ+) : ℕ)
    have : ((2 * bQ : ℕ+) : ℕ) = 2 * (bQ : ℕ) := rfl
    rw [this]; exact le_of_lt h_nat
  have h_above_witness : shannonCapacity (FractionGraph aQ bQ) ∈ S_above :=
    ⟨aQ, bQ, h2bQ_le_aQ, h_above_aQbQ, rfl⟩
  -- Pointwise monotonicity: for any a/b < r < c/d (both with 2·denom ≤ num),
  -- Θ(E_{a/b}) ≤ Θ(E_{c/d}). Path via duality: cohomomorphism + iInf-monotonicity.
  have h_mono : ∀ (a b c d : ℕ+), 2 * b ≤ a → 2 * d ≤ c →
      (a : ℝ) / b < r → r < (c : ℝ) / d →
      shannonCapacity (FractionGraph a b) ≤ shannonCapacity (FractionGraph c d) := by
    intro a b c d h2ab h2cd hab hcd
    -- a/b ≤ c/d in ℚ.
    have hab_lt_cd_real : (a : ℝ) / b < (c : ℝ) / d := lt_trans hab hcd
    have hab_le_cd_rat : ((a : ℕ) : ℚ) / (b : ℕ) ≤ ((c : ℕ) : ℚ) / (d : ℕ) := by
      apply (Rat.cast_le (K := ℝ)).1
      push_cast
      have ha : ((a : ℕ+) : ℝ) = ((a : ℕ) : ℝ) := by simp
      have hb : ((b : ℕ+) : ℝ) = ((b : ℕ) : ℝ) := by simp
      have hc : ((c : ℕ+) : ℝ) = ((c : ℕ) : ℝ) := by simp
      have hd : ((d : ℕ+) : ℝ) = ((d : ℕ) : ℝ) := by simp
      rw [ha, hb, hc, hd] at hab_lt_cd_real
      linarith
    haveI : NeZero (a : ℕ) := ⟨a.pos.ne'⟩
    haveI : NeZero (c : ℕ) := ⟨c.pos.ne'⟩
    have h2ab_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2ab
    have h2cd_nat : 2 * (d : ℕ) ≤ (c : ℕ) := by exact_mod_cast h2cd
    -- Cohomomorphism E_{a/b} → E_{c/d} via the rational ordering.
    have hcohom : Cohom (fractionGraph (a : ℕ) b) (fractionGraph (c : ℕ) d) :=
      (fractionGraph_ordering (a : ℕ) b (c : ℕ) d b.pos d.pos h2ab_nat h2cd_nat).mp
        hab_le_cd_rat
    have hrel : graphStrassenPreorder.rel
        (GraphClass.mk (FractionGraph a b)) (GraphClass.mk (FractionGraph c d)) := by
      change Cohom (FractionGraph a b).graph (FractionGraph c d).graph
      exact hcohom
    -- Θ(E_{a/b}) ≤ Θ(E_{c/d}) via iInf-monotonicity.
    rw [shannonCapacity_eq_iInf_spectrum (FractionGraph a b),
        shannonCapacity_eq_iInf_spectrum (FractionGraph c d)]
    refine ciInf_mono ?_ ?_
    · refine ⟨0, ?_⟩
      rintro x ⟨ψ, rfl⟩
      exact AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_nonneg
        graphStrassenPreorder ψ _
    · intro ψ
      exact AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_mono
        graphStrassenPreorder ψ hrel
  -- BddAbove S_below by the above-witness value.
  have h_bddAbove_below : BddAbove S_below := by
    refine ⟨shannonCapacity (FractionGraph aQ bQ), ?_⟩
    rintro x ⟨a, b, h2ab, hab_lt_r, rfl⟩
    exact h_mono a b aQ bQ h2ab h2bQ_le_aQ hab_lt_r h_above_aQbQ
  -- BddBelow S_above by the below-witness value.
  have h_bddBelow_above : BddBelow S_above := by
    refine ⟨shannonCapacity (FractionGraph aN bN), ?_⟩
    rintro x ⟨c, d, h2cd, hcd_gt_r, rfl⟩
    exact h_mono aN bN c d h2bN_le_aN h2cd hN1_lt_r hcd_gt_r
  -- sSup S_below ≤ sInf S_above.
  have h_sup_le_inf : sSup S_below ≤ sInf S_above := by
    apply csSup_le ⟨_, h_below_witness⟩
    rintro x ⟨a, b, h2ab, hab_lt_r, rfl⟩
    apply le_csInf ⟨_, h_above_witness⟩
    rintro y ⟨c, d, h2cd, hcd_gt_r, rfl⟩
    exact h_mono a b c d h2ab h2cd hab_lt_r hcd_gt_r
  -- For any ε > 0: sInf S_above ≤ sSup S_below + ε.
  have h_inf_le_sup_eps : ∀ ε > 0, sInf S_above ≤ sSup S_below + ε := by
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      fractionGraph_uniform_continuity_irrational r hr hirr ε hε
    -- Find a/b ∈ (r - δ, r) and c/d ∈ (r, r + δ), both with 2b ≤ a, 2d ≤ c.
    -- For below: use convergent_pair_data infrastructure. But simpler:
    -- pick rationals q1 in (max (r - δ) (max ((n : ℝ)) 2), r) and
    -- q2 in (r, min (r + δ) ((n : ℝ) + 1)).
    have hδ' : 0 < δ / 2 := by linarith
    -- Lower endpoint for q1: must exceed max (r - δ) n.
    have hn_lt_r_delta : (n : ℝ) < r := hn_lt_r
    set L : ℝ := max (r - δ) (n : ℝ) with hL_def
    have hL_lt_r : L < r := by
      rw [hL_def]
      simp only [max_lt_iff]
      refine ⟨?_, hn_lt_r⟩
      linarith
    obtain ⟨q1, hq1_lo, hq1_hi⟩ := exists_rat_btwn hL_lt_r
    -- q1 > n ≥ 2, q1 > r - δ.
    have hq1_gt_n : (n : ℝ) < (q1 : ℝ) := by
      have : (n : ℝ) ≤ L := le_max_right _ _
      linarith
    have hq1_gt_r_sub_delta : r - δ < (q1 : ℝ) := by
      have : r - δ ≤ L := le_max_left _ _
      linarith
    have hq1_pos : (0 : ℝ) < (q1 : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_2
      linarith
    -- Upper endpoint for q2: must be less than min (r + δ) (n + 1).
    set U : ℝ := min (r + δ) ((n : ℝ) + 1) with hU_def
    have hr_lt_U : r < U := by
      rw [hU_def]
      simp only [lt_min_iff]
      refine ⟨?_, hr_lt_n1⟩
      linarith
    obtain ⟨q2, hq2_lo, hq2_hi⟩ := exists_rat_btwn hr_lt_U
    have hq2_lt_r_add_delta : (q2 : ℝ) < r + δ := by
      have : U ≤ r + δ := min_le_left _ _
      linarith
    have hq2_lt_n1 : (q2 : ℝ) < (n : ℝ) + 1 := by
      have : U ≤ (n : ℝ) + 1 := min_le_right _ _
      linarith
    have hq2_pos : (0 : ℝ) < (q2 : ℝ) := lt_trans hr_pos hq2_lo
    -- Build ℕ+ pairs from q1 and q2.
    have hq1_num_pos : 0 < q1.num := by
      have hden_pos : (0 : ℝ) < (q1.den : ℝ) := by exact_mod_cast q1.pos
      have hnum_pos_real : (0 : ℝ) < (q1.num : ℝ) := by
        have := hq1_pos
        rw [Rat.cast_def] at this
        exact (div_pos_iff_of_pos_right hden_pos).mp this
      exact_mod_cast hnum_pos_real
    have hq2_num_pos : 0 < q2.num := by
      have hden_pos : (0 : ℝ) < (q2.den : ℝ) := by exact_mod_cast q2.pos
      have hnum_pos_real : (0 : ℝ) < (q2.num : ℝ) := by
        have := hq2_pos
        rw [Rat.cast_def] at this
        exact (div_pos_iff_of_pos_right hden_pos).mp this
      exact_mod_cast hnum_pos_real
    set a1 : ℕ+ := ⟨q1.num.toNat, by
      have h : (q1.num.toNat : ℤ) = q1.num := Int.toNat_of_nonneg (le_of_lt hq1_num_pos)
      omega⟩ with ha1_def
    set b1 : ℕ+ := ⟨q1.den, q1.pos⟩ with hb1_def
    set a2 : ℕ+ := ⟨q2.num.toNat, by
      have h : (q2.num.toNat : ℤ) = q2.num := Int.toNat_of_nonneg (le_of_lt hq2_num_pos)
      omega⟩ with ha2_def
    set b2 : ℕ+ := ⟨q2.den, q2.pos⟩ with hb2_def
    have h_a1_b1_eq : ((a1 : ℕ+) : ℝ) / ((b1 : ℕ+) : ℝ) = (q1 : ℝ) := by
      have h1 : ((a1 : ℕ+) : ℝ) = (q1.num : ℝ) := by
        show ((a1 : ℕ) : ℝ) = (q1.num : ℝ)
        have : ((a1 : ℕ) : ℤ) = q1.num :=
          Int.toNat_of_nonneg (le_of_lt hq1_num_pos)
        exact_mod_cast this
      have h2 : ((b1 : ℕ+) : ℝ) = (q1.den : ℝ) := by
        show ((b1 : ℕ) : ℝ) = (q1.den : ℝ); rfl
      rw [h1, h2, Rat.cast_def]
    have h_a2_b2_eq : ((a2 : ℕ+) : ℝ) / ((b2 : ℕ+) : ℝ) = (q2 : ℝ) := by
      have h1 : ((a2 : ℕ+) : ℝ) = (q2.num : ℝ) := by
        show ((a2 : ℕ) : ℝ) = (q2.num : ℝ)
        have : ((a2 : ℕ) : ℤ) = q2.num :=
          Int.toNat_of_nonneg (le_of_lt hq2_num_pos)
        exact_mod_cast this
      have h2 : ((b2 : ℕ+) : ℝ) = (q2.den : ℝ) := by
        show ((b2 : ℕ) : ℝ) = (q2.den : ℝ); rfl
      rw [h1, h2, Rat.cast_def]
    have hb1_pos_real : (0 : ℝ) < ((b1 : ℕ+) : ℝ) := by
      have := b1.pos; exact_mod_cast this
    have hb2_pos_real : (0 : ℝ) < ((b2 : ℕ+) : ℝ) := by
      have := b2.pos; exact_mod_cast this
    -- a1/b1 < r and > n (so > 2).
    have h_a1b1_lt_r : ((a1 : ℕ+) : ℝ) / ((b1 : ℕ+) : ℝ) < r := by
      rw [h_a1_b1_eq]; exact hq1_hi
    have h_a1b1_gt_n : ((a1 : ℕ+) : ℝ) / ((b1 : ℕ+) : ℝ) > (n : ℝ) := by
      rw [h_a1_b1_eq]; exact hq1_gt_n
    -- a2/b2 > r and < n+1.
    have h_a2b2_gt_r : ((a2 : ℕ+) : ℝ) / ((b2 : ℕ+) : ℝ) > r := by
      rw [h_a2_b2_eq]; exact hq2_lo
    -- 2b1 ≤ a1 (since a1/b1 > n ≥ 2).
    have h2b1_le_a1 : 2 * b1 ≤ a1 := by
      have h_gt_2 : ((a1 : ℕ+) : ℝ) / ((b1 : ℕ+) : ℝ) > 2 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_2
        linarith
      rw [gt_iff_lt, lt_div_iff₀ hb1_pos_real] at h_gt_2
      have h_nat : 2 * (b1 : ℕ) < (a1 : ℕ) := by
        have ha : ((a1 : ℕ+) : ℝ) = ((a1 : ℕ) : ℝ) := by simp
        have hb : ((b1 : ℕ+) : ℝ) = ((b1 : ℕ) : ℝ) := by simp
        rw [ha, hb] at h_gt_2
        have hcast : ((2 * (b1 : ℕ) : ℕ) : ℝ) < ((a1 : ℕ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast hcast
      change ((2 * b1 : ℕ+) : ℕ) ≤ ((a1 : ℕ+) : ℕ)
      have : ((2 * b1 : ℕ+) : ℕ) = 2 * (b1 : ℕ) := rfl
      rw [this]; exact le_of_lt h_nat
    -- 2b2 ≤ a2 (since a2/b2 > r > 2).
    have h2b2_le_a2 : 2 * b2 ≤ a2 := by
      have h_gt_2 : ((a2 : ℕ+) : ℝ) / ((b2 : ℕ+) : ℝ) > 2 := lt_trans hr_gt_2 h_a2b2_gt_r
      rw [gt_iff_lt, lt_div_iff₀ hb2_pos_real] at h_gt_2
      have h_nat : 2 * (b2 : ℕ) < (a2 : ℕ) := by
        have ha : ((a2 : ℕ+) : ℝ) = ((a2 : ℕ) : ℝ) := by simp
        have hb : ((b2 : ℕ+) : ℝ) = ((b2 : ℕ) : ℝ) := by simp
        rw [ha, hb] at h_gt_2
        have hcast : ((2 * (b2 : ℕ) : ℕ) : ℝ) < ((a2 : ℕ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast hcast
      change ((2 * b2 : ℕ+) : ℕ) ≤ ((a2 : ℕ+) : ℕ)
      have : ((2 * b2 : ℕ+) : ℕ) = 2 * (b2 : ℕ) := rfl
      rw [this]; exact le_of_lt h_nat
    -- Uniform continuity bound.
    have h2b1_nat : 2 * (b1 : ℕ) ≤ (a1 : ℕ) := by exact_mod_cast h2b1_le_a1
    have h2b2_nat : 2 * (b2 : ℕ) ≤ (a2 : ℕ) := by exact_mod_cast h2b2_le_a2
    have h_dist1_r : |((a1 : ℕ) : ℝ) / (b1 : ℕ) - r| < δ := by
      rw [abs_sub_lt_iff]
      constructor
      · have ha : ((a1 : ℕ+) : ℝ) = ((a1 : ℕ) : ℝ) := by simp
        have hb : ((b1 : ℕ+) : ℝ) = ((b1 : ℕ) : ℝ) := by simp
        rw [← ha, ← hb]
        linarith
      · have ha : ((a1 : ℕ+) : ℝ) = ((a1 : ℕ) : ℝ) := by simp
        have hb : ((b1 : ℕ+) : ℝ) = ((b1 : ℕ) : ℝ) := by simp
        rw [← ha, ← hb, h_a1_b1_eq]
        linarith
    have h_dist2_r : |((a2 : ℕ) : ℝ) / (b2 : ℕ) - r| < δ := by
      rw [abs_sub_lt_iff]
      constructor
      · have ha : ((a2 : ℕ+) : ℝ) = ((a2 : ℕ) : ℝ) := by simp
        have hb : ((b2 : ℕ+) : ℝ) = ((b2 : ℕ) : ℝ) := by simp
        rw [← ha, ← hb, h_a2_b2_eq]
        linarith
      · have ha : ((a2 : ℕ+) : ℝ) = ((a2 : ℕ) : ℝ) := by simp
        have hb : ((b2 : ℕ+) : ℝ) = ((b2 : ℕ) : ℝ) := by simp
        rw [← ha, ← hb, h_a2_b2_eq]
        linarith
    have h_dist : asympSpecDistance (FractionGraph' (a1 : ℕ) b1) (FractionGraph' (a2 : ℕ) b2) < ε :=
      hδ (a1 : ℕ) b1 (a2 : ℕ) b2 a1.pos a2.pos b1.pos b2.pos
        h2b1_nat h2b2_nat h_dist1_r h_dist2_r
    -- FractionGraph' (a : ℕ) b = FractionGraph a b (definitionally).
    have hF_eq1 : FractionGraph' (a1 : ℕ) b1 = FractionGraph a1 b1 := rfl
    have hF_eq2 : FractionGraph' (a2 : ℕ) b2 = FractionGraph a2 b2 := rfl
    rw [hF_eq1, hF_eq2] at h_dist
    -- Θ is 1-Lipschitz.
    have hLip :=
      shannonCapacity_dist_le (FractionGraph a2 b2) (FractionGraph a1 b1)
    have h_diff_lt :
        shannonCapacity (FractionGraph a2 b2) -
          shannonCapacity (FractionGraph a1 b1) < ε := by
      calc shannonCapacity (FractionGraph a2 b2) - shannonCapacity (FractionGraph a1 b1)
          ≤ |shannonCapacity (FractionGraph a2 b2) - shannonCapacity (FractionGraph a1 b1)| :=
              le_abs_self _
        _ ≤ asympSpecDistance (FractionGraph a2 b2) (FractionGraph a1 b1) := hLip
        _ = asympSpecDistance (FractionGraph a1 b1) (FractionGraph a2 b2) :=
              asympSpecDistance_symm _ _
        _ < ε := h_dist
    -- Conclude.
    have h_a1b1_in : shannonCapacity (FractionGraph a1 b1) ∈ S_below :=
      ⟨a1, b1, h2b1_le_a1, h_a1b1_lt_r, rfl⟩
    have h_a2b2_in : shannonCapacity (FractionGraph a2 b2) ∈ S_above :=
      ⟨a2, b2, h2b2_le_a2, h_a2b2_gt_r, rfl⟩
    have h_inf_le_a2b2 : sInf S_above ≤ shannonCapacity (FractionGraph a2 b2) :=
      csInf_le h_bddBelow_above h_a2b2_in
    have h_a1b1_le_sup : shannonCapacity (FractionGraph a1 b1) ≤ sSup S_below :=
      le_csSup h_bddAbove_below h_a1b1_in
    linarith
  -- Conclude sInf S_above ≤ sSup S_below.
  have h_inf_le_sup : sInf S_above ≤ sSup S_below := by
    by_contra h
    push_neg at h
    set d := sInf S_above - sSup S_below
    have hd_pos : 0 < d := by simp [d]; linarith
    have := h_inf_le_sup_eps (d / 2) (by linarith)
    simp [d] at this
    linarith
  exact le_antisymm h_sup_le_inf h_inf_le_sup

/-- Proof of `main_distance_to_limit_irrational`: Theorem 3.14(b).
    For every `ε > 0` there is a `δ > 0` such that for every spectral
    function `φ ∈ X` and every fraction graph `E_{p/q}` with
    `|p/q − r| < δ`,
        `|sup_{a/b<r} φ(E_{a/b}) − φ(E_{p/q})| < ε`. -/
theorem distance_to_limit_irrational (r : ℝ) (hr : 2 ≤ r)
    (hirr : Irrational r) :
    ∀ ε > 0, ∃ δ > 0, ∀ (φ : SpectralPoint) (p q : ℕ+),
      2 * q ≤ p →
      |(p : ℝ) / q - r| < δ →
      |sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
                  x = φ (FractionGraph a b)}
       - φ (FractionGraph p q)| < ε := by
  intro ε hε
  -- r > 2 (since r ≥ 2 and r irrational).
  have hr_gt_2 : (2 : ℝ) < r := by
    rcases lt_or_eq_of_le hr with h | h
    · exact h
    · exfalso; apply hirr; exact ⟨2, by simp [← h]⟩
  -- ⌊r⌋ ≥ 2 and n < r < n + 1.
  set n : ℕ := ⌊r⌋₊ with hn_def
  have hr_pos : (0 : ℝ) < r := by linarith
  have hn_le_r : (n : ℝ) ≤ r := Nat.floor_le (le_of_lt hr_pos)
  have hn_ge_2 : 2 ≤ n :=
    Nat.le_floor (by exact_mod_cast hr : ((2 : ℕ) : ℝ) ≤ r)
  have hn_lt_r : (n : ℝ) < r := by
    rcases lt_or_eq_of_le hn_le_r with h | h
    · exact h
    · exfalso; apply hirr; exact ⟨n, by simp [← h]⟩
  have hr_lt_n1 : r < (n : ℝ) + 1 := Nat.lt_floor_add_one r
  -- Apply pairwise UC for ε/3 (helper from Section3/Convergence.lean).
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    fractionGraph_uniform_continuity_irrational r hr hirr (ε / 3) hε3
  refine ⟨δ, hδ_pos, ?_⟩
  intro φ p q h2q hpq_close
  -- Set up the sSup-set.
  set S_below : Set ℝ := {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
      x = φ (FractionGraph a b)}
  -- Build witnesses a₁/b₁ ∈ (max(r − δ, n), r) and a₂/b₂ ∈ (r, min(r + δ, n + 1)).
  -- Lower endpoint for q1: must exceed max (r − δ) n.
  set L : ℝ := max (r - δ) (n : ℝ) with hL_def
  have hL_lt_r : L < r := by
    rw [hL_def]
    simp only [max_lt_iff]
    exact ⟨by linarith, hn_lt_r⟩
  obtain ⟨q1, hq1_lo, hq1_hi⟩ := exists_rat_btwn hL_lt_r
  have hq1_gt_n : (n : ℝ) < (q1 : ℝ) := by
    have : (n : ℝ) ≤ L := le_max_right _ _
    linarith
  have hq1_gt_r_sub_delta : r - δ < (q1 : ℝ) := by
    have : r - δ ≤ L := le_max_left _ _
    linarith
  have hq1_pos : (0 : ℝ) < (q1 : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_2
    linarith
  -- Upper endpoint for q2: must be less than min (r + δ) (n + 1).
  set U : ℝ := min (r + δ) ((n : ℝ) + 1) with hU_def
  have hr_lt_U : r < U := by
    rw [hU_def]
    simp only [lt_min_iff]
    exact ⟨by linarith, hr_lt_n1⟩
  obtain ⟨q2, hq2_lo, hq2_hi⟩ := exists_rat_btwn hr_lt_U
  have hq2_lt_r_add_delta : (q2 : ℝ) < r + δ := by
    have : U ≤ r + δ := min_le_left _ _
    linarith
  have hq2_pos : (0 : ℝ) < (q2 : ℝ) := lt_trans hr_pos hq2_lo
  -- Build ℕ+ pairs from q1 and q2.
  have hq1_num_pos : 0 < q1.num := by
    have hden_pos : (0 : ℝ) < (q1.den : ℝ) := by exact_mod_cast q1.pos
    have hnum_pos_real : (0 : ℝ) < (q1.num : ℝ) := by
      have := hq1_pos
      rw [Rat.cast_def] at this
      exact (div_pos_iff_of_pos_right hden_pos).mp this
    exact_mod_cast hnum_pos_real
  have hq2_num_pos : 0 < q2.num := by
    have hden_pos : (0 : ℝ) < (q2.den : ℝ) := by exact_mod_cast q2.pos
    have hnum_pos_real : (0 : ℝ) < (q2.num : ℝ) := by
      have := hq2_pos
      rw [Rat.cast_def] at this
      exact (div_pos_iff_of_pos_right hden_pos).mp this
    exact_mod_cast hnum_pos_real
  set a1 : ℕ+ := ⟨q1.num.toNat, by
    have h : (q1.num.toNat : ℤ) = q1.num := Int.toNat_of_nonneg (le_of_lt hq1_num_pos)
    omega⟩ with ha1_def
  set b1 : ℕ+ := ⟨q1.den, q1.pos⟩ with hb1_def
  set a2 : ℕ+ := ⟨q2.num.toNat, by
    have h : (q2.num.toNat : ℤ) = q2.num := Int.toNat_of_nonneg (le_of_lt hq2_num_pos)
    omega⟩ with ha2_def
  set b2 : ℕ+ := ⟨q2.den, q2.pos⟩ with hb2_def
  have h_a1_b1_eq : ((a1 : ℕ+) : ℝ) / ((b1 : ℕ+) : ℝ) = (q1 : ℝ) := by
    have h1 : ((a1 : ℕ+) : ℝ) = (q1.num : ℝ) := by
      show ((a1 : ℕ) : ℝ) = (q1.num : ℝ)
      have : ((a1 : ℕ) : ℤ) = q1.num :=
        Int.toNat_of_nonneg (le_of_lt hq1_num_pos)
      exact_mod_cast this
    have h2 : ((b1 : ℕ+) : ℝ) = (q1.den : ℝ) := by
      show ((b1 : ℕ) : ℝ) = (q1.den : ℝ); rfl
    rw [h1, h2, Rat.cast_def]
  have h_a2_b2_eq : ((a2 : ℕ+) : ℝ) / ((b2 : ℕ+) : ℝ) = (q2 : ℝ) := by
    have h1 : ((a2 : ℕ+) : ℝ) = (q2.num : ℝ) := by
      show ((a2 : ℕ) : ℝ) = (q2.num : ℝ)
      have : ((a2 : ℕ) : ℤ) = q2.num :=
        Int.toNat_of_nonneg (le_of_lt hq2_num_pos)
      exact_mod_cast this
    have h2 : ((b2 : ℕ+) : ℝ) = (q2.den : ℝ) := by
      show ((b2 : ℕ) : ℝ) = (q2.den : ℝ); rfl
    rw [h1, h2, Rat.cast_def]
  have hb1_pos_real : (0 : ℝ) < ((b1 : ℕ+) : ℝ) := by
    have := b1.pos; exact_mod_cast this
  have hb2_pos_real : (0 : ℝ) < ((b2 : ℕ+) : ℝ) := by
    have := b2.pos; exact_mod_cast this
  have h_a1b1_lt_r : ((a1 : ℕ+) : ℝ) / ((b1 : ℕ+) : ℝ) < r := by
    rw [h_a1_b1_eq]; exact hq1_hi
  have h_a2b2_gt_r : ((a2 : ℕ+) : ℝ) / ((b2 : ℕ+) : ℝ) > r := by
    rw [h_a2_b2_eq]; exact hq2_lo
  -- 2b1 ≤ a1 (since a1/b1 > n ≥ 2).
  have h2b1_le_a1 : 2 * b1 ≤ a1 := by
    have h_gt_2 : ((a1 : ℕ+) : ℝ) / ((b1 : ℕ+) : ℝ) > 2 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_2
      rw [h_a1_b1_eq]; linarith
    rw [gt_iff_lt, lt_div_iff₀ hb1_pos_real] at h_gt_2
    have h_nat : 2 * (b1 : ℕ) < (a1 : ℕ) := by
      have ha : ((a1 : ℕ+) : ℝ) = ((a1 : ℕ) : ℝ) := by simp
      have hb : ((b1 : ℕ+) : ℝ) = ((b1 : ℕ) : ℝ) := by simp
      rw [ha, hb] at h_gt_2
      have hcast : ((2 * (b1 : ℕ) : ℕ) : ℝ) < ((a1 : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast hcast
    change ((2 * b1 : ℕ+) : ℕ) ≤ ((a1 : ℕ+) : ℕ)
    have : ((2 * b1 : ℕ+) : ℕ) = 2 * (b1 : ℕ) := rfl
    rw [this]; exact le_of_lt h_nat
  have h2b2_le_a2 : 2 * b2 ≤ a2 := by
    have h_gt_2 : ((a2 : ℕ+) : ℝ) / ((b2 : ℕ+) : ℝ) > 2 := lt_trans hr_gt_2 h_a2b2_gt_r
    rw [gt_iff_lt, lt_div_iff₀ hb2_pos_real] at h_gt_2
    have h_nat : 2 * (b2 : ℕ) < (a2 : ℕ) := by
      have ha : ((a2 : ℕ+) : ℝ) = ((a2 : ℕ) : ℝ) := by simp
      have hb : ((b2 : ℕ+) : ℝ) = ((b2 : ℕ) : ℝ) := by simp
      rw [ha, hb] at h_gt_2
      have hcast : ((2 * (b2 : ℕ) : ℕ) : ℝ) < ((a2 : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast hcast
    change ((2 * b2 : ℕ+) : ℕ) ≤ ((a2 : ℕ+) : ℕ)
    have : ((2 * b2 : ℕ+) : ℕ) = 2 * (b2 : ℕ) := rfl
    rw [this]; exact le_of_lt h_nat
  -- |a₁/b₁ − r| < δ and |a₂/b₂ − r| < δ.
  have h_dist1_r : |((a1 : ℕ+) : ℝ) / b1 - r| < δ := by
    rw [abs_sub_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [h_a1_b1_eq]; linarith
    · rw [h_a1_b1_eq]; linarith
  have h_dist2_r : |((a2 : ℕ+) : ℝ) / b2 - r| < δ := by
    rw [abs_sub_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [h_a2_b2_eq]; linarith
    · rw [h_a2_b2_eq]; linarith
  -- Pairwise UC: distance φ(p/q) ↔ φ(a₁/b₁) and φ(p/q) ↔ φ(a₂/b₂) is < ε/3.
  have h_dist_pq_a1b1 :
      asympSpecDistance (FractionGraph p q) (FractionGraph a1 b1) < ε / 3 :=
    hδ p q a1 b1 p.pos a1.pos q.pos b1.pos h2q h2b1_le_a1 hpq_close h_dist1_r
  have h_dist_pq_a2b2 :
      asympSpecDistance (FractionGraph p q) (FractionGraph a2 b2) < ε / 3 :=
    hδ p q a2 b2 p.pos a2.pos q.pos b2.pos h2q h2b2_le_a2 hpq_close h_dist2_r
  have h_phi_a1_close :
      |φ.eval (FractionGraph p q) - φ.eval (FractionGraph a1 b1)| < ε / 3 := by
    calc |φ.eval (FractionGraph p q) - φ.eval (FractionGraph a1 b1)|
        ≤ asympSpecDistance (FractionGraph p q) (FractionGraph a1 b1) :=
            spectralPoint_dist_le _ _ φ
      _ < ε / 3 := h_dist_pq_a1b1
  have h_phi_a2_close :
      |φ.eval (FractionGraph p q) - φ.eval (FractionGraph a2 b2)| < ε / 3 := by
    calc |φ.eval (FractionGraph p q) - φ.eval (FractionGraph a2 b2)|
        ≤ asympSpecDistance (FractionGraph p q) (FractionGraph a2 b2) :=
            spectralPoint_dist_le _ _ φ
      _ < ε / 3 := h_dist_pq_a2b2
  -- Bound S_below above by φ(E_{a₂/b₂}): every a/b < r with 2b ≤ a admits
  -- a cohomomorphism E_{a/b} → E_{a₂/b₂} (since a/b < r < a₂/b₂), so
  -- φ(E_{a/b}) ≤ φ(E_{a₂/b₂}).
  have h2b1_nat : 2 * (b1 : ℕ) ≤ (a1 : ℕ) := by exact_mod_cast h2b1_le_a1
  have h2b2_nat : 2 * (b2 : ℕ) ≤ (a2 : ℕ) := by exact_mod_cast h2b2_le_a2
  have h_phi_mono :
      ∀ (a b c d : ℕ+), 2 * b ≤ a → 2 * d ≤ c →
        (a : ℝ) / b ≤ (c : ℝ) / d →
        φ.eval (FractionGraph a b) ≤ φ.eval (FractionGraph c d) := by
    intro a b c d h2ab h2cd hab_le_cd
    have h2ab_nat : 2 * (b : ℕ) ≤ (a : ℕ) := by exact_mod_cast h2ab
    have h2cd_nat : 2 * (d : ℕ) ≤ (c : ℕ) := by exact_mod_cast h2cd
    -- a/b ≤ c/d in ℚ.
    have hab_le_cd_rat : ((a : ℕ) : ℚ) / (b : ℕ) ≤ ((c : ℕ) : ℚ) / (d : ℕ) := by
      apply (Rat.cast_le (K := ℝ)).1
      push_cast
      have ha : ((a : ℕ+) : ℝ) = ((a : ℕ) : ℝ) := by simp
      have hb : ((b : ℕ+) : ℝ) = ((b : ℕ) : ℝ) := by simp
      have hc : ((c : ℕ+) : ℝ) = ((c : ℕ) : ℝ) := by simp
      have hd : ((d : ℕ+) : ℝ) = ((d : ℕ) : ℝ) := by simp
      rw [ha, hb, hc, hd] at hab_le_cd
      linarith
    haveI : NeZero (a : ℕ) := ⟨a.pos.ne'⟩
    haveI : NeZero (c : ℕ) := ⟨c.pos.ne'⟩
    have hcohom : Cohom (fractionGraph (a : ℕ) b) (fractionGraph (c : ℕ) d) :=
      (fractionGraph_ordering (a : ℕ) b (c : ℕ) d b.pos d.pos h2ab_nat h2cd_nat).mp
        hab_le_cd_rat
    have hcohomG : (FractionGraph a b).graph ≤_G (FractionGraph c d).graph := hcohom
    have := evalGraph_mono_cohom hcohomG φ
    simpa [evalGraph] using this
  have h_bddAbove_S_below : BddAbove S_below := by
    refine ⟨φ.eval (FractionGraph a2 b2), ?_⟩
    rintro x ⟨a, b, h2ab, hab_lt_r, rfl⟩
    have hle : (a : ℝ) / b ≤ ((a2 : ℕ+) : ℝ) / b2 := by
      exact le_of_lt (lt_trans hab_lt_r h_a2b2_gt_r)
    have := h_phi_mono a b a2 b2 h2ab h2b2_le_a2 hle
    change φ.eval (FractionGraph a b) ≤ φ.eval (FractionGraph a2 b2)
    exact this
  -- a₁/b₁ contributes to S_below; thus φ(E_{a₁/b₁}) ≤ sSup S_below.
  have h_a1b1_in : φ.eval (FractionGraph a1 b1) ∈ S_below := by
    refine ⟨a1, b1, h2b1_le_a1, h_a1b1_lt_r, ?_⟩
    rfl
  have h_phi_a1_le_sup : φ.eval (FractionGraph a1 b1) ≤ sSup S_below :=
    le_csSup h_bddAbove_S_below h_a1b1_in
  -- sSup S_below ≤ φ(E_{a₂/b₂}): every member of S_below is ≤ φ(E_{a₂/b₂}).
  have h_sup_le_phi_a2 : sSup S_below ≤ φ.eval (FractionGraph a2 b2) := by
    apply csSup_le ⟨_, h_a1b1_in⟩
    rintro x ⟨a, b, h2ab, hab_lt_r, rfl⟩
    have hle : (a : ℝ) / b ≤ ((a2 : ℕ+) : ℝ) / b2 :=
      le_of_lt (lt_trans hab_lt_r h_a2b2_gt_r)
    exact h_phi_mono a b a2 b2 h2ab h2b2_le_a2 hle
  -- Combine: φ(E_{p/q}) − ε/3 < φ(E_{a₁/b₁}) ≤ sSup S_below ≤
  --   φ(E_{a₂/b₂}) < φ(E_{p/q}) + ε/3.
  have h1 : φ.eval (FractionGraph p q) - ε / 3 < sSup S_below := by
    have h := (abs_sub_lt_iff.mp h_phi_a1_close).1
    have hL : φ.eval (FractionGraph p q) - ε / 3 < φ.eval (FractionGraph a1 b1) := by
      linarith
    linarith
  have h2 : sSup S_below < φ.eval (FractionGraph p q) + ε / 3 := by
    have h := (abs_sub_lt_iff.mp h_phi_a2_close).2
    have hU : φ.eval (FractionGraph a2 b2) < φ.eval (FractionGraph p q) + ε / 3 := by
      linarith
    linarith
  -- Conclude.
  change |sSup S_below - φ.eval (FractionGraph p q)| < ε
  rw [abs_sub_lt_iff]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- Proof of `main_no_finite_limit_existential`: Corollary 3.16.
    There exists a Cauchy sequence of fraction graphs `E_{a_n/b_n}` that does
    not converge to any finite graph. Instantiates `fractionGraph_no_finite_limit`
    at the irrational `r = √2 + 2 ≥ 2` with the explicit ceiling-based sequence
    `q_n = n + 1`, `p_n = ⌈(n+1) · r⌉`. -/
theorem no_finite_limit_existential :
    ∃ (ps : ℕ → ℕ+) (qs : ℕ → ℕ+),
      (∀ n, 2 * qs n ≤ ps n) ∧
      (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        asympSpecDistance (FractionGraph (ps n) (qs n))
          (FractionGraph (ps m) (qs m)) < ε) ∧
      ¬ ∃ G : Graph, ConvergesTo
        (fun n => FractionGraph (ps n) (qs n)) G := by
  -- Set up the irrational target r = √2 + 2.
  set r : ℝ := Real.sqrt 2 + 2 with hr_def
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hr_ge : 2 ≤ r := by
    change (2 : ℝ) ≤ Real.sqrt 2 + 2; linarith
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr_ge
  have hirr : Irrational r := by
    have h1 : Irrational (Real.sqrt 2) := irrational_sqrt_two
    simpa [hr_def] using h1.add_natCast 2
  -- Define qs and ps.
  let qs : ℕ → ℕ+ := fun n => ⟨n + 1, Nat.succ_pos n⟩
  have hqsR : ∀ n, ((qs n : ℕ) : ℝ) = (n : ℝ) + 1 := by
    intro n; simp [qs]
  have hqsR_pos : ∀ n, (0 : ℝ) < ((qs n : ℕ) : ℝ) := by
    intro n; rw [hqsR]; exact_mod_cast Nat.succ_pos n
  have hcandidatePos : ∀ n, 0 < Nat.ceil (((qs n : ℕ) : ℝ) * r) := by
    intro n
    have hprod_pos : 0 < ((qs n : ℕ) : ℝ) * r := mul_pos (hqsR_pos n) hr_pos
    exact Nat.ceil_pos.mpr hprod_pos
  let ps : ℕ → ℕ+ := fun n =>
    ⟨Nat.ceil (((qs n : ℕ) : ℝ) * r), hcandidatePos n⟩
  -- Prove `2 * qs n ≤ ps n` as ℕ+ (= as ℕ).
  have h2qs : ∀ n, 2 * qs n ≤ ps n := by
    intro n
    -- Goal in ℕ: 2 * (qs n).val ≤ (ps n).val = ⌈qs n * r⌉₊
    change 2 * ((qs n : ℕ) : ℕ) ≤ Nat.ceil (((qs n : ℕ) : ℝ) * r)
    have h_mul_ge : (2 * ((qs n : ℕ) : ℝ)) ≤ ((qs n : ℕ) : ℝ) * r := by
      have := mul_le_mul_of_nonneg_left hr_ge (le_of_lt (hqsR_pos n))
      linarith
    have h_ceil_ge : (2 * ((qs n : ℕ) : ℝ)) ≤ Nat.ceil (((qs n : ℕ) : ℝ) * r) :=
      h_mul_ge.trans (Nat.le_ceil _)
    have : ((2 * (qs n : ℕ) : ℕ) : ℝ) ≤ ((Nat.ceil (((qs n : ℕ) : ℝ) * r) : ℕ) : ℝ) := by
      push_cast; exact h_ceil_ge
    exact_mod_cast this
  -- Prove p_n / q_n → r.
  have hconv : Filter.Tendsto (fun n => ((ps n : ℕ) : ℝ) / ((qs n : ℕ) : ℝ))
      Filter.atTop (nhds r) := by
    -- |p_n / q_n - r| ≤ 1 / q_n via |⌈x⌉ - x| ≤ 1
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Choose N so that 1 / (N+1) < ε.
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hNle => ?_⟩
    -- Show |ps n / qs n - r| < ε.
    have hqR : ((qs n : ℕ) : ℝ) = (n : ℝ) + 1 := hqsR n
    have hq_pos : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    -- Bound numerator difference.
    have hceil_lt : ((Nat.ceil (((qs n : ℕ) : ℝ) * r) : ℕ) : ℝ) <
        ((qs n : ℕ) : ℝ) * r + 1 :=
      Nat.ceil_lt_add_one (le_of_lt (mul_pos (hqsR_pos n) hr_pos))
    have hceil_ge : ((qs n : ℕ) : ℝ) * r ≤
        ((Nat.ceil (((qs n : ℕ) : ℝ) * r) : ℕ) : ℝ) := Nat.le_ceil _
    -- ps n value = ceil
    have hps_val : ((ps n : ℕ) : ℝ) = ((Nat.ceil (((qs n : ℕ) : ℝ) * r) : ℕ) : ℝ) := by
      simp [ps]
    -- |ps n / qs n - r| ≤ 1 / qs n
    have hdiff_bound :
        |((ps n : ℕ) : ℝ) / ((qs n : ℕ) : ℝ) - r| ≤ 1 / ((qs n : ℕ) : ℝ) := by
      rw [hps_val]
      have habs :
          |((Nat.ceil (((qs n : ℕ) : ℝ) * r) : ℕ) : ℝ) - ((qs n : ℕ) : ℝ) * r| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith
        · linarith
      have hrearr :
          ((Nat.ceil (((qs n : ℕ) : ℝ) * r) : ℕ) : ℝ) / ((qs n : ℕ) : ℝ) - r =
          (((Nat.ceil (((qs n : ℕ) : ℝ) * r) : ℕ) : ℝ) - ((qs n : ℕ) : ℝ) * r) /
          ((qs n : ℕ) : ℝ) := by
        field_simp
      rw [hrearr, abs_div, abs_of_pos (hqsR_pos n)]
      exact div_le_div_of_nonneg_right habs (le_of_lt (hqsR_pos n))
    -- Now 1 / qs n ≤ 1 / (N+1) < ε.
    have h1qn_le : 1 / ((qs n : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + 1) := by
      rw [hqR]
      apply one_div_le_one_div_of_le
      · exact_mod_cast Nat.succ_pos N
      · exact_mod_cast Nat.succ_le_succ hNle
    have h1N_lt : 1 / ((N : ℝ) + 1) < ε := by
      have := hN; push_cast at this; linarith
    have habs_lt : |((ps n : ℕ) : ℝ) / ((qs n : ℕ) : ℝ) - r| < ε :=
      lt_of_le_of_lt (hdiff_bound.trans h1qn_le) h1N_lt
    simpa [Real.dist_eq] using habs_lt
  refine ⟨ps, qs, h2qs, ?_, ?_⟩
  · -- Cauchy (delegate directly to `fractionGraph_cauchy_irrational` to avoid
    -- a Main-wrapper call cycle from inside Section3).
    haveI : ∀ n, NeZero (ps n).val := fun _ => ⟨(ps _).pos.ne'⟩
    exact fractionGraph_cauchy_irrational r hr_ge hirr
      (fun n => (ps n).val) (fun n => (qs n).val)
      (fun n => (qs n).pos) (fun n => h2qs n) hconv
  · -- No finite-graph limit (delegate to fractionGraph_no_finite_limit).
    haveI : ∀ n, NeZero (ps n).val := fun _ => ⟨(ps _).pos.ne'⟩
    exact fractionGraph_no_finite_limit r hr_ge hirr
      (fun n => (ps n).val) (fun n => (qs n).val)
      (fun n => (qs n).pos) (fun n => h2qs n) hconv

/-- Proof of `main_convergence_from_above`: Theorem 3.7(c).
    Adapter from the `ℕ+` paper-statement form to the underlying `ℕ`
    helper `fractionGraph_convergence_from_above'`, including derivation
    of the per-index `2 * qs n ≤ ps n` bound from `a/b ≥ 2` and
    `a/b ≤ ps n / qs n`. -/
theorem convergence_from_above (a b : ℕ+)
    (h2b : 2 * b ≤ a)
    (ps : ℕ → ℕ+) (qs : ℕ → ℕ+)
    (hfrom_above : ∀ n, (a : ℚ) / b ≤ (ps n : ℚ) / qs n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℚ) / qs n) Filter.atTop
      (nhds ((a : ℚ) / b))) :
    ConvergesTo (fun n => FractionGraph (ps n) (qs n))
      (FractionGraph a b) := by
  have h2qs : ∀ n, 2 * qs n ≤ ps n := by
    intro n
    have h := hfrom_above n
    have hab : (2 : ℚ) ≤ (a : ℚ) / b := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr b.pos)]; exact_mod_cast h2b
    have hpq : (2 : ℚ) ≤ (ps n : ℚ) / qs n := le_trans hab h
    rwa [le_div_iff₀ (Nat.cast_pos.mpr (qs n).pos), ← Nat.cast_ofNat,
      ← Nat.cast_mul, Nat.cast_le] at hpq
  exact fractionGraph_convergence_from_above' a b b.pos h2b
    (fun n => (ps n).val) (fun n => (qs n).val)
    (fun n => (qs n).pos) h2qs hfrom_above hconv

/-- Proof of `main_cauchy_irrational`: Theorem 3.14(c).
    Adapter from the `ℕ+` paper-statement form to the underlying `ℕ`
    helper `fractionGraph_cauchy_irrational`. -/
theorem cauchy_irrational (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ps : ℕ → ℕ+) (qs : ℕ → ℕ+)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℝ) / qs n) Filter.atTop
      (nhds r)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      asympSpecDistance (FractionGraph (ps n) (qs n))
        (FractionGraph (ps m) (qs m)) < ε := by
  haveI : ∀ n, NeZero (ps n).val := fun _ => ⟨(ps _).pos.ne'⟩
  exact fractionGraph_cauchy_irrational r hr hirr
    (fun n => (ps n).val) (fun n => (qs n).val)
    (fun n => (qs n).pos) (fun n => h2qs n) hconv


end AsymptoticSpectrumDistance
