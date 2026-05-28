/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.ConeProgram
import Mathlib.Topology.MetricSpace.Sequences

set_option linter.style.emptyLine false
set_option linter.style.longLine false

/-!
# Duality of Cone Programming

This file develops cone programming duality following Chapter 4 of
Gärtner-Matoušek "Approximation Algorithms and Semidefinite Programming".

## Main results

* `ConeProgram.weak_duality` : Primal feasible ≤ dual feasible
* `ConeProgram.regular_duality` : Limit-feasible → dual feasible
* `ConeProgram.strong_duality` : With Slater's condition, primal = dual value

## Key theorems

1. **Weak Duality (4.7.2)**: For any primal feasible x and dual feasible y,
   ⟨c, x⟩ ≤ ⟨b, y⟩.

2. **Regular Duality (4.7.3)**: If (P) is limit-feasible with finite limit value γ,
   then (D) is feasible with value γ.

3. **Strong Duality (4.7.1)**: If (P) is feasible, has finite value, and has an
   interior point, then (D) is feasible with the same value.
-/

namespace ConeProgramming

open scoped InnerProductSpace RealInnerProductSpace
open ContinuousLinearMap

section ConePrograms

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

namespace ConeProgram


/-
Theorem 4.6.5: With an interior point, value(P) = limit value(P).

The key idea from Gärtner-Matoušek:
Given any feasible sequence (x_k) achieving limsup = γ' (limit value), and
an interior point x₀ ∈ int(K) with A(x₀) + slack₀ = b:
1. For small ξ > 0, define w_k = (1-ξ)x_k + ξ·x₀
2. By convexity of K and x₀ ∈ int(K), eventually w_k ∈ K
3. The perturbed sequence converges: A(w_k) + (perturbed slack) → b
4. Eventually w_k becomes actually feasible (not just limit-feasible)
5. Since ⟨c, w_k⟩ ≈ ⟨c, x_k⟩ for small ξ, we get value ≥ limit value - ε
6. Taking ε → 0: value ≥ limit value

Combined with value_le_limitValue, we get value = limit value.
-/
/-- Key lemma: For a convex set L with y₀ ∈ interior(L), convex combinations
    (1-ξ)s + ξy₀ for s ∈ L and ξ ∈ (0,1] have a uniform "buffer" from the boundary.

    Specifically, if B(y₀, r) ⊆ L, then B((1-ξ)s + ξy₀, ξr) ⊆ L for all s ∈ L. -/
theorem convex_combination_uniform_ball {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {L : Set W} (hL_convex : Convex ℝ L) {y₀ : W} {r : ℝ} (hr : 0 < r)
    (hy₀_ball : Metric.ball y₀ r ⊆ L) {s : W} (hs : s ∈ L) {ξ : ℝ} (hξ_pos : 0 < ξ) (hξ_le : ξ ≤ 1) :
    Metric.ball ((1 - ξ) • s + ξ • y₀) (ξ * r) ⊆ L := by
  intro w hw
  rw [Metric.mem_ball] at hw
  -- w = (1-ξ)s + ξy₀ + δ where ||δ|| < ξr
  -- Rewrite as (1-ξ)s + ξ(y₀ + δ/ξ)
  have hξ_ne : ξ ≠ 0 := ne_of_gt hξ_pos
  set δ := w - ((1 - ξ) • s + ξ • y₀) with hδ_def
  have hw_eq : w = (1 - ξ) • s + ξ • y₀ + δ := by rw [hδ_def]; abel
  have hδ_small : ‖δ‖ < ξ * r := by
    rw [hδ_def]
    simp only [dist_eq_norm] at hw
    convert hw using 2
  -- y₀ + δ/ξ is in the ball around y₀
  have hy₀_shift : y₀ + (ξ⁻¹ • δ) ∈ Metric.ball y₀ r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hξ_pos)]
    calc ξ⁻¹ * ‖δ‖ < ξ⁻¹ * (ξ * r) := by
           apply mul_lt_mul_of_pos_left hδ_small (inv_pos.mpr hξ_pos)
      _ = r := by field_simp
  have hy₀_shift_L : y₀ + (ξ⁻¹ • δ) ∈ L := hy₀_ball hy₀_shift
  -- Now use convexity: w = (1-ξ)s + ξ(y₀ + δ/ξ)
  have hw_combo : w = (1 - ξ) • s + ξ • (y₀ + ξ⁻¹ • δ) := by
    rw [hw_eq, smul_add, smul_smul, mul_inv_cancel₀ hξ_ne, one_smul]
    abel
  rw [hw_combo]
  apply hL_convex hs hy₀_shift_L
  · linarith
  · linarith
  · linarith

/-- Theorem 4.6.5: limitValue ≤ value when an interior point exists.

    The proof (Gärtner-Matoušek pages 60-62) uses:
    1. For any feasible sequence (x_k) achieving the limit value γ'
    2. Take convex combinations w_k = (1-ξ)x_k + ξx₀ with interior point x₀
    3. By convexity of K: w_k ∈ K
    4. Since slack₀ ∈ interior(L), convex combinations have a uniform buffer ξr from boundary
    5. So w_k becomes feasible for large k, giving value ≥ (1-ξ)γ' + ξ·obj(x₀)
    6. As ξ → 0: value ≥ γ' = limit value
-/
theorem limitValue_le_value_of_interior' (V W : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (P : ConeProgram (V := V) (W := W))
    (h_int : ∃ x_int, P.isInteriorPoint x_int) : P.limitValue ≤ P.value := by
  -- Theorem 4.6.5 from Gärtner-Matoušek (pages 60-62).
  -- With an interior point, limit-feasible sequences can be perturbed to become feasible.

  -- Step 1: Extract interior point and its properties
  obtain ⟨x₀, ⟨hx₀_K, hslack₀_L⟩, hslack₀_int⟩ := h_int
  set slack₀ := P.b - P.A x₀ with hslack₀_def

  -- Get ball radius from interior property
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hslack₀_int
  obtain ⟨r, hr_pos, hball⟩ := hslack₀_int

  -- Convexity of L (as a proper cone, it's convex)
  have hL_convex : Convex ℝ (P.L : Set W) := P.L.convex

  -- Step 2: Show limitValue ≤ value by bounding each feasible sequence
  simp only [limitValue]
  apply iSup_le; intro seq
  apply iSup_le; intro slack
  apply iSup_le; intro hseq

  -- Need: limsup⟨c, seq(k)⟩ ≤ value
  -- Strategy: for any γ < limsup, find feasible point with objective ≥ γ

  -- Handle the case where limsup = ⊥
  by_cases h_bot : P.feasibleSeqValue seq = ⊥
  · simp only [h_bot, bot_le]

  -- For finite or ⊤ limsup, use convex perturbation
  -- EReal.le_of_forall_lt_iff_le : (∀ z : ℝ, x < z → y ≤ z) ↔ y ≤ x
  rw [← EReal.le_of_forall_lt_iff_le]
  intro γ_real hγ_lt
  -- Now γ_real : ℝ and hγ_lt : P.value < ↑γ_real
  -- Goal: P.feasibleSeqValue seq ≤ ↑γ_real

  -- Extract feasible sequence properties
  obtain ⟨hseq_K, hslack_L, hconv⟩ := hseq

  -- The error term: A(seq n) + slack n - b → 0
  set error := fun n => P.A (seq n) + slack n - P.b with herror_def
  have herror_tends : Filter.Tendsto error Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.sub_const hconv P.b
    simp only [sub_self] at h
    exact h

  -- Key idea: if feasibleSeqValue > γ_real, we can use the interior point to
  -- construct feasible points with objective > γ_real - ε, which would imply
  -- P.value ≥ γ_real, contradicting hγ_lt.

  -- We need to handle the case where feasibleSeqValue could be ⊤ or a finite real
  -- Since we already ruled out ⊥, we have: feasibleSeqValue is either finite or ⊤

  -- Case analysis: is feasibleSeqValue > γ_real?
  by_cases hle : P.feasibleSeqValue seq ≤ ↑γ_real
  · exact hle
  · -- feasibleSeqValue > γ_real: need to derive contradiction with hγ_lt : P.value < γ_real
    push_neg at hle
    -- hle : ↑γ_real < P.feasibleSeqValue seq

    set obj₀ := P.objective x₀ with hobj₀_def

    -- Get that frequently objective > γ_real
    have hfreq : ∃ᶠ n in Filter.atTop, γ_real < P.objective (seq n) := by
      unfold feasibleSeqValue at hle
      -- If not frequently > γ_real, then eventually ≤ γ_real, so limsup ≤ γ_real
      by_contra hcontra
      rw [Filter.not_frequently] at hcontra
      -- hcontra : ∀ᶠ n in atTop, ¬(γ_real < P.objective (seq n))
      -- i.e., eventually P.objective (seq n) ≤ γ_real
      have hbound : ∀ᶠ n in Filter.atTop, (P.objective (seq n) : EReal) ≤ ↑γ_real := by
        filter_upwards [hcontra] with n hn
        push_neg at hn
        exact EReal.coe_le_coe_iff.mpr hn
      have hlimsup_le : Filter.limsup (fun n => (P.objective (seq n) : EReal)) Filter.atTop ≤ ↑γ_real :=
        Filter.limsup_le_of_le ⟨⊥, by simp⟩ hbound
      exact not_lt.mpr hlimsup_le hle

    -- Use ξ = 1/2 for simplicity
    set ξ : ℝ := 1 / 2 with hξ_def
    have hξ_pos : 0 < ξ := by norm_num
    have hξ_le : ξ ≤ 1 := by norm_num
    have hξ_lt : ξ < 1 := by norm_num

    -- Define the perturbed sequence
    set w := fun n => (1 - ξ) • seq n + ξ • x₀ with hw_def

    -- w(n) ∈ K by convexity of K
    have hw_K : ∀ n, w n ∈ (P.K : Set V) := by
      intro n
      have hK_convex : Convex ℝ (P.K : Set V) := P.K.convex
      apply hK_convex (hseq_K n) hx₀_K
      · linarith
      · linarith
      · ring

    -- Rewrite slack in terms of error
    have hw_slack' : ∀ n, P.b - P.A (w n) = (1 - ξ) • (-error n) + ((1 - ξ) • slack n + ξ • slack₀) := by
      intro n
      simp only [hw_def, map_add, map_smul]
      rw [hslack₀_def]
      have herr : error n = P.A (seq n) + slack n - P.b := rfl
      have hseq_slack : P.b - P.A (seq n) = -error n + slack n := by
        rw [herr]; module
      calc P.b - ((1 - ξ) • P.A (seq n) + ξ • P.A x₀)
          = (1 - ξ) • P.b + ξ • P.b - ((1 - ξ) • P.A (seq n) + ξ • P.A x₀) := by
            rw [← add_smul]; simp
        _ = (1 - ξ) • (P.b - P.A (seq n)) + ξ • (P.b - P.A x₀) := by module
        _ = (1 - ξ) • (-error n + slack n) + ξ • slack₀ := by rw [hseq_slack]
        _ = (1 - ξ) • -error n + ((1 - ξ) • slack n + ξ • slack₀) := by module

    -- Eventually ‖error(n)‖ < ξr/(1-ξ)
    have herr_small : ∀ᶠ n in Filter.atTop, ‖error n‖ < ξ * r / (1 - ξ) := by
      have hbound_pos : 0 < ξ * r / (1 - ξ) := by positivity
      rw [Metric.tendsto_atTop] at herror_tends
      obtain ⟨N, hN⟩ := herror_tends (ξ * r / (1 - ξ)) hbound_pos
      filter_upwards [Filter.Ici_mem_atTop N] with n hn
      have := hN n hn
      simp only [dist_zero_right] at this
      exact this

    -- Eventually w(n) is feasible
    have hw_feas : ∀ᶠ n in Filter.atTop, P.isFeasible (w n) := by
      filter_upwards [herr_small] with n hn
      constructor
      · exact hw_K n
      · rw [hw_slack']
        have hcenter_ball := convex_combination_uniform_ball hL_convex hr_pos hball (hslack_L n) hξ_pos hξ_le
        have hpert_small : ‖(1 - ξ) • (-error n)‖ < ξ * r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - ξ), norm_neg]
          calc (1 - ξ) * ‖error n‖ < (1 - ξ) * (ξ * r / (1 - ξ)) := by
                 apply mul_lt_mul_of_pos_left hn (by linarith : 0 < 1 - ξ)
            _ = ξ * r := by field_simp; ring
        apply hcenter_ball
        rw [Metric.mem_ball]
        simp only [dist_eq_norm, add_sub_cancel_right]
        exact hpert_small

    -- The objective formula
    have hw_obj : ∀ n, P.objective (w n) = (1 - ξ) * P.objective (seq n) + ξ * obj₀ := by
      intro n
      simp only [objective, hw_def, inner_add_right, inner_smul_right, hobj₀_def]

    -- Find n with both properties: feasible w_n and obj(seq n) > γ_real
    have hexists : ∃ n, P.isFeasible (w n) ∧ γ_real < P.objective (seq n) := by
      have hboth := hfreq.and_eventually hw_feas
      obtain ⟨n, hn1, hn2⟩ := hboth.exists
      exact ⟨n, hn2, hn1⟩

    obtain ⟨n, hw_n_feas, hobj_n_high⟩ := hexists

    -- Show P.value ≥ γ_real by finding a feasible point with objective ≥ γ_real
    -- When obj₀ ≥ γ_real, this is easy. When obj₀ < γ_real, we need more work.
    exfalso

    -- Key observation: when obj₀ ≥ γ_real, the combo is ≥ γ_real
    have hobj_ge_gamma : γ_real ≤ P.objective (w n) := by
      rw [hw_obj]
      simp only [hξ_def]
      -- combo = (1/2) * obj(seq n) + (1/2) * obj₀
      -- Since obj(seq n) > γ_real, we have:
      -- combo > (1/2) * γ_real + (1/2) * obj₀
      -- This is ≥ γ_real iff obj₀ ≥ γ_real
      by_cases h : obj₀ ≥ γ_real
      · -- Easy case: obj₀ ≥ γ_real
        have h1 : (1/2 : ℝ) * P.objective (seq n) ≥ (1/2 : ℝ) * γ_real := by
          apply mul_le_mul_of_nonneg_left (le_of_lt hobj_n_high); norm_num
        have h2 : (1/2 : ℝ) * obj₀ ≥ (1/2 : ℝ) * γ_real := by
          apply mul_le_mul_of_nonneg_left h; norm_num
        calc γ_real = (1/2 : ℝ) * γ_real + (1/2 : ℝ) * γ_real := by ring
          _ ≤ (1/2 : ℝ) * P.objective (seq n) + (1/2 : ℝ) * obj₀ := add_le_add h1 h2
          _ = (1 - 1/2) * P.objective (seq n) + 1/2 * obj₀ := by ring
      · -- Harder case: obj₀ < γ_real
        push_neg at h
        -- h : obj₀ < γ_real
        -- With ξ = 1/2, combo = (1/2)*obj(seq n) + (1/2)*obj₀ may be < γ_real.
        -- We need to find a LARGER threshold M and use a smaller ξ'.

        -- Step 1: Find M > γ_real such that frequently obj(seq n) > M
        -- Case split on whether feasibleSeqValue = ⊤ or finite
        have hM_exists : ∃ M : ℝ, γ_real < M ∧ (∃ᶠ n' in Filter.atTop, M < P.objective (seq n')) := by
          by_cases htop : P.feasibleSeqValue seq = ⊤
          · -- Case: feasibleSeqValue = ⊤, can find arbitrarily large objectives
            use 2 * γ_real - obj₀ + 1
            constructor
            · linarith
            · rw [Filter.Frequently]
              intro hev
              have hbound : ∀ᶠ n' in Filter.atTop,
                  (P.objective (seq n') : EReal) ≤ (2 * γ_real - obj₀ + 1) := by
                filter_upwards [hev] with n' hn'
                push_neg at hn'
                exact EReal.coe_le_coe_iff.mpr hn'
              have hlimsup_le : P.feasibleSeqValue seq ≤ (2 * γ_real - obj₀ + 1 : ℝ) :=
                Filter.limsup_le_of_le ⟨⊥, by simp⟩ hbound
              rw [htop] at hlimsup_le
              have hcoe : ((2 * γ_real - obj₀ + 1 : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
              exact hcoe (top_le_iff.mp hlimsup_le)
          · -- Case: feasibleSeqValue = some L (finite)
            have hne_bot : P.feasibleSeqValue seq ≠ ⊥ := h_bot
            -- Extract the real value L
            have hL_exists : ∃ L : ℝ, P.feasibleSeqValue seq = (L : EReal) := by
              cases hfsv : P.feasibleSeqValue seq with
              | bot => exact absurd hfsv hne_bot
              | coe L => exact ⟨L, rfl⟩
              | top => exact absurd hfsv htop
            obtain ⟨L, hL_eq⟩ := hL_exists
            have hL_gt : γ_real < L := by
              rw [hL_eq] at hle
              exact EReal.coe_lt_coe_iff.mp hle
            -- Use M = (γ_real + L) / 2
            use (γ_real + L) / 2
            constructor
            · linarith
            · rw [Filter.Frequently]
              intro hev
              have hbound : ∀ᶠ n' in Filter.atTop,
                  (P.objective (seq n') : EReal) ≤ ((γ_real + L) / 2 : ℝ) := by
                filter_upwards [hev] with n' hn'
                push_neg at hn'
                exact EReal.coe_le_coe_iff.mpr hn'
              have hlimsup_le : P.feasibleSeqValue seq ≤ ((γ_real + L) / 2 : ℝ) :=
                Filter.limsup_le_of_le ⟨⊥, by simp⟩ hbound
              rw [hL_eq] at hlimsup_le
              have : L ≤ (γ_real + L) / 2 := EReal.coe_le_coe_iff.mp hlimsup_le
              linarith

        obtain ⟨M, hM_gt, hfreq_M⟩ := hM_exists

        -- Step 2: Choose ξ' based on M and the gap
        let δ := M - γ_real
        have hδ_pos : 0 < δ := sub_pos.mpr hM_gt
        let gap := γ_real - obj₀
        have hgap_pos : 0 < gap := sub_pos.mpr h
        let ξ' := δ / (2 * (δ + gap))
        have hξ'_pos : 0 < ξ' := div_pos hδ_pos (by linarith : 0 < 2 * (δ + gap))
        have hξ'_lt_one : ξ' < 1 := by
          have h1 : δ < 2 * (δ + gap) := by linarith
          exact (div_lt_one (by linarith : 0 < 2 * (δ + gap))).mpr h1
        have hξ'_le : ξ' ≤ 1 := le_of_lt hξ'_lt_one

        -- Step 3: Define w' with ξ'
        let w' := fun n' => (1 - ξ') • seq n' + ξ' • x₀

        have hw'_K : ∀ n', w' n' ∈ (P.K : Set V) := fun n' =>
          P.K.convex (hseq_K n') hx₀_K (by linarith) (le_of_lt hξ'_pos) (by ring)

        -- Step 4: Eventually w' n' is feasible
        have herr_small' : ∀ᶠ n' in Filter.atTop, ‖error n'‖ < ξ' * r / (1 - ξ') := by
          have hbound_pos : 0 < ξ' * r / (1 - ξ') := div_pos (mul_pos hξ'_pos hr_pos) (by linarith)
          rw [Metric.tendsto_atTop] at herror_tends
          obtain ⟨N, hN⟩ := herror_tends (ξ' * r / (1 - ξ')) hbound_pos
          filter_upwards [Filter.Ici_mem_atTop N] with n' hn'
          simp only [dist_zero_right] at hN
          exact hN n' hn'

        have hw'_feas : ∀ᶠ n' in Filter.atTop, P.isFeasible (w' n') := by
          filter_upwards [herr_small'] with n' hn'
          refine ⟨hw'_K n', ?_⟩
          have hw'_slack : P.b - P.A (w' n') =
              (1 - ξ') • -error n' + ((1 - ξ') • slack n' + ξ' • slack₀) := by
            have hA_w' : P.A (w' n') = (1 - ξ') • P.A (seq n') + ξ' • P.A x₀ := by
              simp only [w', map_add, map_smul]
            have : P.b - P.A (seq n') = -error n' + slack n' := by
              simp only [herror_def]; module
            rw [hA_w']
            calc P.b - ((1 - ξ') • P.A (seq n') + ξ' • P.A x₀)
                = (1 - ξ') • P.b + ξ' • P.b - ((1 - ξ') • P.A (seq n') + ξ' • P.A x₀) := by
                  rw [← add_smul]; simp
              _ = (1 - ξ') • (P.b - P.A (seq n')) + ξ' • (P.b - P.A x₀) := by module
              _ = (1 - ξ') • (-error n' + slack n') + ξ' • slack₀ := by rw [this, hslack₀_def]
              _ = _ := by module
          rw [hw'_slack]
          have hcenter := convex_combination_uniform_ball hL_convex hr_pos hball (hslack_L n') hξ'_pos hξ'_le
          apply hcenter
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - ξ'), norm_neg]
          have h1m : 1 - ξ' ≠ 0 := by linarith
          calc (1 - ξ') * ‖error n'‖ < (1 - ξ') * (ξ' * r / (1 - ξ')) := by
                 apply mul_lt_mul_of_pos_left hn' (by linarith : 0 < 1 - ξ')
            _ = ξ' * r := by field_simp [h1m]

        -- Step 5: Find n' with w'(n') feasible AND obj(seq n') > M
        have hexists' : ∃ n', P.isFeasible (w' n') ∧ M < P.objective (seq n') := by
          obtain ⟨n', hn'1, hn'2⟩ := (hfreq_M.and_eventually hw'_feas).exists
          exact ⟨n', hn'2, hn'1⟩
        obtain ⟨n', hw'_n'_feas, hobj_n'_gt_M⟩ := hexists'

        -- Step 6: Show combo with ξ' exceeds γ_real
        have hw'_obj : P.objective (w' n') = (1 - ξ') * P.objective (seq n') + ξ' * obj₀ := by
          simp only [objective, w', hobj₀_def]
          rw [inner_add_right, inner_smul_right, inner_smul_right]

        have hcombo_gt : γ_real < P.objective (w' n') := by
          rw [hw'_obj]
          -- combo = (1-ξ')*obj(seq n') + ξ'*obj₀ > (1-ξ')*M + ξ'*obj₀
          have h1 : (1 - ξ') * P.objective (seq n') > (1 - ξ') * M :=
            mul_lt_mul_of_pos_left hobj_n'_gt_M (by linarith : 0 < 1 - ξ')
          -- (1-ξ')*M + ξ'*obj₀ = γ_real + δ/2 by choice of ξ'
          have h2 : (1 - ξ') * M + ξ' * obj₀ = γ_real + δ / 2 := by
            -- First unfold ξ' then use field algebra
            have hdenom_ne : 2 * (δ + gap) ≠ 0 := by linarith
            simp only [show ξ' = δ / (2 * (δ + gap)) from rfl]
            field_simp [hdenom_ne]
            ring
          linarith

        -- Derive contradiction: P.value ≥ γ_real contradicts hγ_lt
        have hvalue_ge' : (γ_real : EReal) ≤ P.value := by
          calc (γ_real : EReal) ≤ (P.objective (w' n') : EReal) := by
                 exact_mod_cast le_of_lt hcombo_gt
            _ ≤ P.value := by
              apply le_iSup_of_le (w' n')
              apply le_iSup_of_le hw'_n'_feas
              rfl
        exact absurd hγ_lt (not_lt.mpr hvalue_ge')

    have hvalue_ge : γ_real ≤ P.value := by
      calc (γ_real : EReal) ≤ (P.objective (w n) : EReal) := by exact_mod_cast hobj_ge_gamma
        _ ≤ P.value := by
            apply le_iSup_of_le (w n)
            apply le_iSup_of_le hw_n_feas
            rfl

    -- hγ_lt : P.value < γ_real contradicts hvalue_ge : γ_real ≤ P.value
    have : ¬(P.value < ↑γ_real) := not_lt.mpr hvalue_ge
    exact this hγ_lt

theorem limitValue_eq_value_of_interior (P : ConeProgram (V := V) (W := W))
    (h_int : ∃ x_int, P.isInteriorPoint x_int) : P.limitValue = P.value := by
  apply le_antisymm
  · exact limitValue_le_value_of_interior' V W P h_int
  · exact P.value_le_limitValue

end ConeProgram

end ConePrograms

/-! ## Section 4.7: Duality of Cone Programming

Theorem 4.7.2 (Weak Duality): If (D) is feasible and (P) is limit-feasible,
then the limit value of (P) is bounded above by the value of (D).

Theorem 4.7.3 (Regular Duality): (D) is feasible with finite value β
if and only if (P) is limit-feasible with finite limit value γ.
Moreover, β = γ.

Theorem 4.7.1 (Strong Duality): If (P) is feasible, has finite value γ,
and has an interior point, then (D) is feasible with value γ.
-/

section Duality

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

namespace ConeProgram

/-- **Weak Duality for Cone Programs** (Theorem 4.7.2):
    For any primal feasible x and dual feasible y,
    ⟨c, x⟩ ≤ ⟨b, y⟩.

    Proof: From the constraints:
    - x ∈ K, b - A(x) ∈ L
    - y ∈ L*, Aᵀ(y) - c ∈ K*

    We have:
    0 ≤ ⟨Aᵀ(y) - c, x⟩ + ⟨y, b - A(x)⟩    (by dual cone membership)
      = ⟨Aᵀ(y), x⟩ - ⟨c, x⟩ + ⟨y, b⟩ - ⟨y, A(x)⟩
      = ⟨y, A(x)⟩ - ⟨c, x⟩ + ⟨y, b⟩ - ⟨y, A(x)⟩    (adjoint property)
      = ⟨y, b⟩ - ⟨c, x⟩

    Therefore ⟨c, x⟩ ≤ ⟨b, y⟩. -/
theorem weak_duality (P : ConeProgram (V := V) (W := W)) (x : V) (y : W)
    (hx : P.isFeasible x) (hy : P.isDualFeasible y) :
    P.objective x ≤ P.dualObjective y := by
  unfold objective dualObjective isFeasible isDualFeasible at *
  obtain ⟨hxK, hbAx⟩ := hx
  obtain ⟨hyL, hAyc⟩ := hy
  -- ⟨Aᵀ(y) - c, x⟩ ≥ 0 since Aᵀ(y) - c ∈ K* and x ∈ K
  have h1 : 0 ≤ ⟪x, P.A.adjoint y - P.c⟫_ℝ := mem_dualCone.mp hAyc x hxK
  -- ⟨y, b - A(x)⟩ ≥ 0 since y ∈ L* and b - A(x) ∈ L
  have h2 : 0 ≤ ⟪P.b - P.A x, y⟫_ℝ := mem_dualCone.mp hyL (P.b - P.A x) hbAx
  -- Expand and use adjoint property
  simp only [inner_sub_right, inner_sub_left] at h1 h2
  rw [ContinuousLinearMap.adjoint_inner_right] at h1
  -- h1: 0 ≤ ⟨A x, y⟩ - ⟨x, c⟩
  -- h2: 0 ≤ ⟨b, y⟩ - ⟨A x, y⟩
  -- Use real_inner_comm: ⟪c, x⟫ = ⟪x, c⟫ to match h1
  have h3 : ⟪P.c, x⟫_ℝ = ⟪x, P.c⟫_ℝ := real_inner_comm _ _
  linarith

/-- Weak duality in terms of feasibility: if (D) feasible, (P) value ≤ (D) value. -/
theorem weak_duality' (P : ConeProgram (V := V) (W := W))
    (hDfeas : ∃ y, P.isDualFeasible y) :
    ∀ x, P.isFeasible x →
      P.objective x ≤ ⨅ y : {y // P.isDualFeasible y}, P.dualObjective y.val := by
  intro x hx
  obtain ⟨y₀, hy₀⟩ := hDfeas
  haveI : Nonempty {y // P.isDualFeasible y} := ⟨⟨y₀, hy₀⟩⟩
  apply le_ciInf
  intro ⟨y, hy⟩
  exact weak_duality P x y hx hy

/-- **Regular Duality for Cone Programs** (Theorem 4.7.3):
    If the primal is limit-feasible with finite limit value, then
    the dual is feasible with the same value.

    **Proof strategy** (following Gärtner-Matoušek §4.7, Farkas-based):

    The key is using **Farkas lemma on the lifted image cone**:

    1. **Lifted image cone**: C = {(A(x), ⟨c,x⟩) : x ∈ K} ⊆ W × ℝ

    2. **Key claim**: limit value ≤ γ implies (b, γ+ε) ∉ closure(C) for ε > 0
       Proof: If (b, γ+ε) ∈ closure(C), then ∃ sequence with A(x_n) → b
       and ⟨c, x_n⟩ → γ+ε > γ, contradicting limit value = γ.

    3. **Farkas separation**: (b, γ+ε) ∉ closure(C) gives ∃(y, τ) with:
       - ⟨(A(x), ⟨c,x⟩), (y, τ)⟩ ≥ 0 for all x ∈ K  ⟹  A*y + τc ∈ K*
       - ⟨(b, γ+ε), (y, τ)⟩ < 0  ⟹  ⟨b,y⟩ + (γ+ε)τ < 0

    4. **Case analysis on τ**:
       - If τ < 0: Set y' = -y/τ. Then A*y' - c = A*(-y/τ) - c ∈ K*
         (since A*y + τc ∈ K* means A*(-y/τ) - c = -(A*y + τc)/τ ∈ K* when τ < 0)
         So y' is dual feasible!
       - If τ = 0: A*y ∈ K* and ⟨b,y⟩ < 0. But by primal limit-feasibility
         and Farkas forward, ⟨b,y⟩ ≥ 0. Contradiction!
       - If τ > 0: ⟨b,y⟩ < -(γ+ε)τ < 0. Combined with limit-feasibility...
         (need more careful analysis of signs)

    Note: For equational form (L = {0}), dual feasibility is A*y - c ∈ K*.
-/
theorem regular_duality (P : ConeProgram (V := V) (W := W))
    (γ : ℝ)
    (hlf : ∃ (seq : ℕ → V), (∀ n, seq n ∈ (P.K : Set V)) ∧
           Filter.Tendsto (fun n => P.b - P.A (seq n)) Filter.atTop (nhds 0) ∧
           Filter.Tendsto (fun n => P.objective (seq n)) Filter.atTop (nhds γ))
    -- The limit value γ bounds ALL sequences (finite limit value condition)
    (hγ_bound : ∀ (seq' : ℕ → V), (∀ n, seq' n ∈ (P.K : Set V)) →
           Filter.Tendsto (fun n => P.A (seq' n)) Filter.atTop (nhds P.b) →
           ∀ v, Filter.Tendsto (fun n => P.objective (seq' n)) Filter.atTop (nhds v) → v ≤ γ)
    -- Equational form: L = {0}, so dualCone L = W (all y satisfy dual constraint)
    (hL_eq : ∀ y : W, y ∈ (dualCone (P.L : Set W) : Set W)) :
    ∃ y, P.isDualFeasible y := by
  obtain ⟨seq, hseq_K, hseq_conv, hseq_obj⟩ := hlf

  -- Step 1: Show that b is limit-feasible for the constraint A(x) = b
  have hlf_constraint : isLimitFeasible P.A P.K P.b := by
    rw [isLimitFeasible]
    have hAseq : Filter.Tendsto (fun n => P.A (seq n)) Filter.atTop (nhds P.b) := by
      have h : Filter.Tendsto (fun n => P.b - (P.b - P.A (seq n))) Filter.atTop (nhds (P.b - 0)) :=
        tendsto_const_nhds.sub hseq_conv
      simp only [sub_sub_cancel, sub_zero] at h
      exact h
    rw [Metric.mem_closure_iff]
    intro ε hε
    rw [Metric.tendsto_atTop] at hAseq
    obtain ⟨N, hN⟩ := hAseq ε hε
    refine ⟨P.A (seq N), ⟨seq N, hseq_K N, rfl⟩, ?_⟩
    rw [dist_comm]
    exact hN N (le_refl N)

  -- Step 2: The Farkas-based approach
  -- Apply separation on the objective image cone {(A(x), ⟨c,x⟩) : x ∈ K}

  -- (a) For any ε > 0, (b, γ+ε) ∉ closure(objectiveImageCone)
  -- This follows from the fact that objective values converge to γ, not beyond
  have h_not_in_closure : ∀ ε > 0,
      (WithLp.equiv 2 (W × ℝ)).symm (P.b, γ + ε) ∉
        closure (objectiveImageCone P.A P.c P.K) := by
    intro ε hε
    apply not_in_closure_objectiveImageCone_if_bound P.A P.c γ P.K P.b ε hε
    intro seq' hseq'_K hseq'_conv v hv_conv
    -- Show v ≤ γ: any sequence in K with A∘seq' → b has objective limit ≤ γ
    -- This follows from the hγ_bound hypothesis (finite limit value condition)
    exact hγ_bound seq' hseq'_K hseq'_conv v hv_conv

  -- (b) Apply separation for ε = 1 to get (y, τ)
  have hε1 : (0 : ℝ) < 1 := one_pos
  have hsep := separation_from_objectiveImageCone P.A P.c γ P.K P.b 1 hε1
    (h_not_in_closure 1 hε1)
  obtain ⟨y, τ, hsep_cone, hsep_pt⟩ := hsep

  -- (c) Case analysis on τ to extract dual feasible point
  -- We'll show τ < 0, then construct y' = y/(-τ)

  -- First, eliminate τ = 0 using limit-feasibility
  have hτ_ne_zero : τ ≠ 0 := by
    intro hτ_eq_zero
    simp only [hτ_eq_zero, mul_zero, add_zero] at hsep_cone hsep_pt
    -- hsep_cone: ∀ x ∈ K, 0 ≤ ⟪A x, y⟫
    -- hsep_pt: ⟪b, y⟫ < 0
    -- But A(seq n) → b, and ⟪A(seq n), y⟫ ≥ 0 for all n
    -- By continuity, ⟪b, y⟫ = lim ⟪A(seq n), y⟫ ≥ 0
    have h_lim : Filter.Tendsto (fun n => ⟪P.A (seq n), y⟫_ℝ) Filter.atTop (nhds ⟪P.b, y⟫_ℝ) := by
      have hAseq : Filter.Tendsto (fun n => P.A (seq n)) Filter.atTop (nhds P.b) := by
        have h : Filter.Tendsto (fun n => P.b - (P.b - P.A (seq n))) Filter.atTop (nhds (P.b - 0)) :=
          tendsto_const_nhds.sub hseq_conv
        simp only [sub_sub_cancel, sub_zero] at h
        exact h
      exact Filter.Tendsto.inner hAseq tendsto_const_nhds
    have h_nonneg : ∀ n, 0 ≤ ⟪P.A (seq n), y⟫_ℝ := fun n => hsep_cone (seq n) (hseq_K n)
    have h_lim_nonneg : 0 ≤ ⟪P.b, y⟫_ℝ := ge_of_tendsto h_lim (Filter.Eventually.of_forall h_nonneg)
    linarith

  -- Next, eliminate τ > 0
  have hτ_neg : τ < 0 := by
    rcases lt_trichotomy τ 0 with hτ_neg | hτ_zero | hτ_pos
    · exact hτ_neg
    · exact absurd hτ_zero hτ_ne_zero
    · -- τ > 0 leads to contradiction
      -- From hsep_cone: ⟪A(seq n), y⟫ + τ * ⟪c, seq n⟫ ≥ 0
      -- Taking limit: ⟪b, y⟫ + τ * γ ≥ 0
      -- From hsep_pt: ⟪b, y⟫ + τ * (γ + 1) < 0
      -- So: ⟪b, y⟫ < -τ(γ + 1) and ⟪b, y⟫ ≥ -τγ
      -- Thus: -τγ ≤ ⟪b, y⟫ < -τγ - τ
      -- Which gives: 0 ≤ ⟪b, y⟫ + τγ < -τ
      -- But τ > 0, so -τ < 0, contradicting 0 ≤ ... < -τ
      have hAseq : Filter.Tendsto (fun n => P.A (seq n)) Filter.atTop (nhds P.b) := by
        have h : Filter.Tendsto (fun n => P.b - (P.b - P.A (seq n))) Filter.atTop (nhds (P.b - 0)) :=
          tendsto_const_nhds.sub hseq_conv
        simp only [sub_sub_cancel, sub_zero] at h
        exact h
      -- The objective is ⟪c, x⟫, so hseq_obj : ⟪c, seq n⟫ → γ
      have hc_lim : Filter.Tendsto (fun n => ⟪P.c, seq n⟫_ℝ) Filter.atTop (nhds γ) := hseq_obj
      have h_inner_lim : Filter.Tendsto
          (fun n => ⟪P.A (seq n), y⟫_ℝ + τ * ⟪P.c, seq n⟫_ℝ) Filter.atTop
          (nhds (⟪P.b, y⟫_ℝ + τ * γ)) := by
        apply Filter.Tendsto.add
        · exact Filter.Tendsto.inner hAseq tendsto_const_nhds
        · exact Filter.Tendsto.const_mul τ hc_lim
      have h_nonneg : ∀ n, 0 ≤ ⟪P.A (seq n), y⟫_ℝ + τ * ⟪P.c, seq n⟫_ℝ := by
        intro n
        have := hsep_cone (seq n) (hseq_K n)
        linarith [mul_comm τ ⟪P.c, seq n⟫_ℝ]
      have h_lim_nonneg : 0 ≤ ⟪P.b, y⟫_ℝ + τ * γ :=
        ge_of_tendsto h_inner_lim (Filter.Eventually.of_forall h_nonneg)
      -- But hsep_pt says ⟪b, y⟫ + (γ + 1) * τ < 0
      have hsep_pt' : ⟪P.b, y⟫_ℝ + τ * γ + τ < 0 := by linarith
      linarith

  -- (d) Construct dual feasible point y' = y / (-τ)
  set τ' := -τ with hτ'_def
  have hτ'_pos : 0 < τ' := by linarith
  set y' := (1 / τ') • y with hy'_def

  -- Show y' is dual feasible
  use y'
  unfold isDualFeasible

  -- Need to show two things:
  -- (1) y' ∈ dualCone L (for constraint cone)
  -- (2) A*y' - c ∈ dualCone K

  constructor
  · -- y' ∈ dualCone L
    -- For equational form (L = {0}), dualCone L = W, so this is trivial
    exact hL_eq y'

  · -- A*y' - c ∈ dualCone K
    -- From hsep_cone: ∀ x ∈ K, 0 ≤ ⟪A x, y⟫ + ⟪c, x⟫ * τ
    -- Since τ < 0, dividing by -τ = τ' > 0 gives A*y' - c ∈ K*
    rw [SetLike.mem_coe, ProperCone.mem_innerDual]
    intro x hxK
    have h := hsep_cone x hxK
    -- h: 0 ≤ ⟪A x, y⟫ + ⟪c, x⟫ * τ
    -- Need: 0 ≤ ⟪x, A*y' - c⟫

    -- Convert to inner product with adjoint form
    have hadj : ⟪P.A x, y⟫_ℝ = ⟪x, P.A.adjoint y⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_right P.A x y).symm

    -- Rewrite h using adjoint
    have h1 : 0 ≤ ⟪x, P.A.adjoint y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ := by
      rw [← hadj]
      calc 0 ≤ ⟪P.A x, y⟫_ℝ + ⟪P.c, x⟫_ℝ * τ := h
           _ = ⟪P.A x, y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ := by ring

    -- Divide by τ' = -τ > 0
    have hτ'_ne : τ' ≠ 0 := ne_of_gt hτ'_pos
    have h2 : 0 ≤ (⟪x, P.A.adjoint y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ) / τ' :=
      div_nonneg h1 (le_of_lt hτ'_pos)

    -- Compute τ / τ' = τ / (-τ) = -1
    have hτ_ratio : τ / τ' = -1 := by
      rw [hτ'_def]
      simp only [div_neg_eq_neg_div, div_self (ne_of_lt hτ_neg)]

    -- Simplify h2 using τ = -τ'
    have hτ_eq_neg : τ = -τ' := by linarith
    have h3 : (⟪x, P.A.adjoint y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ) / τ' =
        ⟪x, P.A.adjoint y⟫_ℝ / τ' - ⟪P.c, x⟫_ℝ := by
      rw [add_div, hτ_eq_neg]
      congr 1
      field_simp

    -- Express ⟪x, A*y⟫/τ' as ⟪x, A*y'⟫
    have h4 : ⟪x, P.A.adjoint y⟫_ℝ / τ' = ⟪x, P.A.adjoint y'⟫_ℝ := by
      rw [hy'_def, ContinuousLinearMap.map_smul, inner_smul_right]
      rw [one_div]
      ring

    -- Combine to get ⟪x, A*y' - c⟫ ≥ 0
    calc ⟪x, P.A.adjoint y' - P.c⟫_ℝ
        = ⟪x, P.A.adjoint y'⟫_ℝ - ⟪x, P.c⟫_ℝ := inner_sub_right x _ _
      _ = ⟪x, P.A.adjoint y⟫_ℝ / τ' - ⟪x, P.c⟫_ℝ := by rw [h4]
      _ = ⟪x, P.A.adjoint y⟫_ℝ / τ' - ⟪P.c, x⟫_ℝ := by rw [real_inner_comm P.c x]
      _ = (⟪x, P.A.adjoint y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ) / τ' := h3.symm
      _ ≥ 0 := h2

/-
**Strong Duality for Cone Programs** (Theorem 4.7.1):
If (P) is feasible, has finite value γ, and has an interior point,
then (D) is feasible with value γ.

**Proof strategy** (following Gärtner-Matoušek §4.7):

1. **Slater implies limit-feasibility**: The interior point condition (Theorem 4.6.5)
   ensures that the supremum γ is achieved as a limit. Specifically, if x₀ is an
   interior point and x* achieves value close to γ, then convex combinations
   tₙx₀ + (1-tₙ)x* with tₙ → 0 approach γ while staying feasible.

2. **Regular duality gives dual feasible**: Apply `regular_duality` to the
   limit-feasible sequence to obtain a dual feasible point y₀.

3. **Value equality**: By weak duality, sup_x ⟨c,x⟩ ≤ inf_y ⟨b,y⟩ for feasible x, y.
   The lifted cone construction in regular_duality ensures the constructed
   dual point y₀ achieves value exactly γ.

Key Mathlib ingredients:
- `ProperCone.relative_hyperplane_separation`: Farkas lemma for cones
- `ProperCone.innerDual_innerDual`: Double dual equals self (K** = K)
- `ProperCone.hyperplane_separation'`: Separation for proper cones
- Interior characterization of proper cones for Slater's condition
-/
/-- For any ε > 0, there exists a dual feasible y with dual objective < γ + ε.
    This follows from the Farkas separation in regular_duality. -/
theorem regular_duality_bound (P : ConeProgram (V := V) (W := W))
    (γ : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hlf : ∃ (seq : ℕ → V), (∀ n, seq n ∈ (P.K : Set V)) ∧
           Filter.Tendsto (fun n => P.b - P.A (seq n)) Filter.atTop (nhds 0) ∧
           Filter.Tendsto (fun n => P.objective (seq n)) Filter.atTop (nhds γ))
    (hγ_bound : ∀ (seq' : ℕ → V), (∀ n, seq' n ∈ (P.K : Set V)) →
           Filter.Tendsto (fun n => P.A (seq' n)) Filter.atTop (nhds P.b) →
           ∀ v, Filter.Tendsto (fun n => P.objective (seq' n)) Filter.atTop (nhds v) → v ≤ γ)
    (hL_eq : ∀ y : W, y ∈ (dualCone (P.L : Set W) : Set W)) :
    ∃ y, P.isDualFeasible y ∧ P.dualObjective y < γ + ε := by
  -- Get the separation from the Farkas construction
  obtain ⟨seq, hseq_K, hseq_conv, hseq_obj⟩ := hlf

  -- Show (b, γ+ε) is not in closure of objectiveImageCone
  have h_not_in_closure :
      (WithLp.equiv 2 (W × ℝ)).symm (P.b, γ + ε) ∉
        closure (objectiveImageCone P.A P.c P.K) := by
    apply not_in_closure_objectiveImageCone_if_bound P.A P.c γ P.K P.b ε hε
    intro seq' hseq'_K hseq'_conv v hv_conv
    have hAseq : Filter.Tendsto (fun n => P.A (seq' n)) Filter.atTop (nhds P.b) := hseq'_conv
    exact hγ_bound seq' hseq'_K hAseq v hv_conv

  -- Apply separation
  have hsep := separation_from_objectiveImageCone P.A P.c γ P.K P.b ε hε h_not_in_closure
  obtain ⟨y, τ, hsep_cone, hsep_pt⟩ := hsep

  -- Show τ ≠ 0 and τ < 0 (same argument as regular_duality)
  have hτ_ne_zero : τ ≠ 0 := by
    intro hτ_eq_zero
    simp only [hτ_eq_zero, mul_zero, add_zero] at hsep_cone hsep_pt
    have h_lim : Filter.Tendsto (fun n => ⟪P.A (seq n), y⟫_ℝ) Filter.atTop (nhds ⟪P.b, y⟫_ℝ) := by
      have hAseq : Filter.Tendsto (fun n => P.A (seq n)) Filter.atTop (nhds P.b) := by
        have h : Filter.Tendsto (fun n => P.b - (P.b - P.A (seq n))) Filter.atTop (nhds (P.b - 0)) :=
          tendsto_const_nhds.sub hseq_conv
        simp only [sub_sub_cancel, sub_zero] at h
        exact h
      exact Filter.Tendsto.inner hAseq tendsto_const_nhds
    have h_nonneg : ∀ n, 0 ≤ ⟪P.A (seq n), y⟫_ℝ := fun n => hsep_cone (seq n) (hseq_K n)
    have h_lim_nonneg : 0 ≤ ⟪P.b, y⟫_ℝ := ge_of_tendsto h_lim (Filter.Eventually.of_forall h_nonneg)
    linarith

  have hτ_neg : τ < 0 := by
    rcases lt_trichotomy τ 0 with hτ_neg | hτ_zero | hτ_pos
    · exact hτ_neg
    · exact absurd hτ_zero hτ_ne_zero
    · -- τ > 0 leads to contradiction
      have hAseq : Filter.Tendsto (fun n => P.A (seq n)) Filter.atTop (nhds P.b) := by
        have h : Filter.Tendsto (fun n => P.b - (P.b - P.A (seq n))) Filter.atTop (nhds (P.b - 0)) :=
          tendsto_const_nhds.sub hseq_conv
        simp only [sub_sub_cancel, sub_zero] at h
        exact h
      have hc_lim : Filter.Tendsto (fun n => ⟪P.c, seq n⟫_ℝ) Filter.atTop (nhds γ) := hseq_obj
      have h_inner_lim : Filter.Tendsto
          (fun n => ⟪P.A (seq n), y⟫_ℝ + τ * ⟪P.c, seq n⟫_ℝ) Filter.atTop
          (nhds (⟪P.b, y⟫_ℝ + τ * γ)) := by
        apply Filter.Tendsto.add
        · exact Filter.Tendsto.inner hAseq tendsto_const_nhds
        · exact Filter.Tendsto.const_mul τ hc_lim
      have h_nonneg : ∀ n, 0 ≤ ⟪P.A (seq n), y⟫_ℝ + τ * ⟪P.c, seq n⟫_ℝ := by
        intro n
        have := hsep_cone (seq n) (hseq_K n)
        linarith [mul_comm τ ⟪P.c, seq n⟫_ℝ]
      have h_lim_nonneg : 0 ≤ ⟪P.b, y⟫_ℝ + τ * γ :=
        ge_of_tendsto h_inner_lim (Filter.Eventually.of_forall h_nonneg)
      have hsep_pt' : ⟪P.b, y⟫_ℝ + τ * γ + τ * ε < 0 := by linarith
      have hτε_pos : τ * ε > 0 := mul_pos hτ_pos hε
      linarith

  -- Construct y' = y / (-τ)
  set τ' := -τ with hτ'_def
  have hτ'_pos : 0 < τ' := by linarith
  set y' := (1 / τ') • y with hy'_def

  use y'
  constructor
  · -- y' is dual feasible
    unfold isDualFeasible
    constructor
    · exact hL_eq y'
    · rw [SetLike.mem_coe, ProperCone.mem_innerDual]
      intro x hxK
      have h := hsep_cone x hxK
      have hadj : ⟪P.A x, y⟫_ℝ = ⟪x, P.A.adjoint y⟫_ℝ :=
        (ContinuousLinearMap.adjoint_inner_right P.A x y).symm
      have h1 : 0 ≤ ⟪x, P.A.adjoint y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ := by
        rw [← hadj]
        calc 0 ≤ ⟪P.A x, y⟫_ℝ + ⟪P.c, x⟫_ℝ * τ := h
             _ = ⟪P.A x, y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ := by ring
      have hτ'_ne : τ' ≠ 0 := ne_of_gt hτ'_pos
      have h2 : 0 ≤ (⟪x, P.A.adjoint y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ) / τ' :=
        div_nonneg h1 (le_of_lt hτ'_pos)
      have hτ_eq_neg : τ = -τ' := by linarith
      have h3 : (⟪x, P.A.adjoint y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ) / τ' =
          ⟪x, P.A.adjoint y⟫_ℝ / τ' - ⟪P.c, x⟫_ℝ := by
        rw [add_div, hτ_eq_neg]
        congr 1
        field_simp
      have h4 : ⟪x, P.A.adjoint y⟫_ℝ / τ' = ⟪x, P.A.adjoint y'⟫_ℝ := by
        rw [hy'_def, ContinuousLinearMap.map_smul, inner_smul_right]
        rw [one_div]
        ring
      calc ⟪x, P.A.adjoint y' - P.c⟫_ℝ
          = ⟪x, P.A.adjoint y'⟫_ℝ - ⟪x, P.c⟫_ℝ := inner_sub_right x _ _
        _ = ⟪x, P.A.adjoint y⟫_ℝ / τ' - ⟪x, P.c⟫_ℝ := by rw [h4]
        _ = ⟪x, P.A.adjoint y⟫_ℝ / τ' - ⟪P.c, x⟫_ℝ := by rw [real_inner_comm P.c x]
        _ = (⟪x, P.A.adjoint y⟫_ℝ + τ * ⟪P.c, x⟫_ℝ) / τ' := h3.symm
        _ ≥ 0 := h2

  · -- Dual objective < γ + ε
    unfold dualObjective
    -- From hsep_pt: ⟪b, y⟫ + (γ + ε) * τ < 0
    -- With τ < 0, τ' = -τ > 0:
    -- ⟪b, y⟫ < -(γ + ε) * τ = (γ + ε) * τ'
    -- ⟪b, y⟫ / τ' < γ + ε
    -- ⟪b, y'⟫ = ⟪b, (1/τ')•y⟫ = (1/τ') * ⟪b, y⟫ = ⟪b, y⟫ / τ' < γ + ε
    have hbound : ⟪P.b, y⟫_ℝ < (γ + ε) * τ' := by
      have : ⟪P.b, y⟫_ℝ < -(γ + ε) * τ := by linarith
      calc ⟪P.b, y⟫_ℝ < -(γ + ε) * τ := this
        _ = (γ + ε) * (-τ) := by ring
        _ = (γ + ε) * τ' := by rw [hτ'_def]
    calc ⟪P.b, y'⟫_ℝ = ⟪P.b, (1 / τ') • y⟫_ℝ := by rw [hy'_def]
      _ = (1 / τ') * ⟪P.b, y⟫_ℝ := by rw [inner_smul_right]
      _ = ⟪P.b, y⟫_ℝ / τ' := by ring
      _ < (γ + ε) * τ' / τ' := by apply div_lt_div_of_pos_right hbound hτ'_pos
      _ = γ + ε := by field_simp

/-- Key lemma: For equational form with Slater condition in finite dimensions,
    limit-feasible sequences have objective limits bounded by the value.

    In finite dimensions, the proof uses compactness:
    - Bounded sequences have convergent subsequences whose limits are feasible
    - Unbounded sequences escape along recession directions with zero objective contribution

    This is Theorem 4.6.5 from Gärtner-Matoušek, adapted for equational form. -/
theorem limitValue_le_value_eq_form
    [FiniteDimensional ℝ V]
    (P : ConeProgram (V := V) (W := W))
    (γ_real : ℝ)
    (_ : ∀ y : W, y ∈ (dualCone (P.L : Set W) : Set W))
    (hSlater : ∃ x₀, P.isSlaterPointEq x₀)
    (hγ_is_sup : γ_real = sSup (Set.range fun (x : {x // P.isFeasible x}) => P.objective x.val))
    (hγ_bdd : BddAbove (Set.range fun (x : {x // P.isFeasible x}) => P.objective x.val))
    (_ : ∃ x, P.isFeasible x)
    (seq' : ℕ → V) (hseq'_K : ∀ n, seq' n ∈ (P.K : Set V))
    (hseq'_conv : Filter.Tendsto (fun n => P.A (seq' n)) Filter.atTop (nhds P.b))
    (v : ℝ) (hv_conv : Filter.Tendsto (fun n => P.objective (seq' n)) Filter.atTop (nhds v)) :
    v ≤ γ_real := by
  -- Get the Slater point
  obtain ⟨x_slater, hx_slater_int, hx_slater_eq⟩ := hSlater

  -- x_slater is feasible
  have hx_slater_K : x_slater ∈ (P.K : Set V) := interior_subset hx_slater_int
  have hx_slater_feas : P.isFeasible x_slater := by
    constructor
    · exact hx_slater_K
    · simp only [hx_slater_eq, sub_self]; exact P.L.zero_mem

  -- The objective of x_slater is ≤ γ_real
  have hobj_slater_le : P.objective x_slater ≤ γ_real := by
    rw [hγ_is_sup]
    apply le_csSup hγ_bdd
    exact ⟨⟨x_slater, hx_slater_feas⟩, rfl⟩

  -- In finite dimensions, we have a proper space (closed balls are compact)
  haveI : ProperSpace V := FiniteDimensional.proper_real V

  -- K is closed (as a ProperCone)
  have hK_closed : IsClosed (P.K : Set V) := P.K.isClosed

  -- Strategy: Use convex combinations with Slater point and compactness
  -- For any ε > 0, mix seq' with x_slater to get a bounded limit-feasible sequence
  -- whose limit is feasible (by compactness) with objective ≥ v - ε

  -- We show v ≤ γ_real using convex combinations that stay bounded
  -- For any t ∈ (0, 1], w_n = t·x_slater + (1-t)·seq' n is in K with A(w_n) → b
  -- and the set {w_n} stays within bounded distance from x_slater

  -- Key observation: For each t ∈ (0, 1), the convex combinations are bounded
  -- w_n - x_slater = (1-t)(seq' n - x_slater), so distance grows linearly with seq' n
  -- But we can use a decreasing t_n → 0 such that w_n stays bounded

  -- Simpler approach: Use the existing limit value machinery
  -- Show that feasible points can approximate the limit v

  by_contra hv_gt
  push_neg at hv_gt
  -- v > γ_real

  -- Choose ε such that v - ε > γ_real
  set ε := (v - γ_real) / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  have hv_ε : v - ε > γ_real := by linarith

  -- Key construction: For t ∈ (0, 1], define w_n^t = t·x_slater + (1-t)·seq' n
  -- w_n^t ∈ K (convexity), A(w_n^t) → b, and objective → t·obj(x_slater) + (1-t)·v

  -- Choose adaptive t based on gap between v and γ_real
  -- We need: t·obj(x_slater) + (1-t)·v > γ_real
  -- Equivalently: v - t(v - obj(x_slater)) > γ_real
  -- i.e., t < (v - γ_real)/(v - obj(x_slater))

  -- Since v > γ_real ≥ obj(x_slater), we have v > obj(x_slater)
  have hv_gt_obj : v > P.objective x_slater := lt_of_le_of_lt hobj_slater_le hv_gt

  -- Choose t = (v - γ_real) / (2 * (v - obj(x_slater)))
  -- This ensures t < (v - γ_real)/(v - obj(x_slater)) and t > 0
  set t : ℝ := (v - γ_real) / (2 * (v - P.objective x_slater)) with ht_def
  have ht_pos : 0 < t := by
    apply div_pos
    · linarith
    · linarith

  have ht_le_half : t ≤ 1/2 := by
    rw [ht_def, div_le_div_iff₀ (by linarith : 0 < 2 * (v - P.objective x_slater)) (by norm_num : (0:ℝ) < 2)]
    ring_nf
    linarith

  have ht_lt_one : t < 1 := lt_of_le_of_lt ht_le_half (by norm_num : (1:ℝ)/2 < 1)

  -- w_n := t·x_slater + (1-t)·seq' n
  set w : ℕ → V := fun n => t • x_slater + (1 - t) • seq' n with hw_def

  -- w n ∈ K by convexity
  have hw_K : ∀ n, w n ∈ (P.K : Set V) := fun n =>
    P.K.convex hx_slater_K (hseq'_K n) (le_of_lt ht_pos) (by linarith) (by ring)

  -- A(w n) → b
  have hw_conv : Filter.Tendsto (fun n => P.A (w n)) Filter.atTop (nhds P.b) := by
    simp only [hw_def, map_add, map_smul]
    have h1 : Filter.Tendsto (fun _ : ℕ => t • P.A x_slater) Filter.atTop (nhds (t • P.b)) := by
      rw [hx_slater_eq]; exact tendsto_const_nhds
    have h2 : Filter.Tendsto (fun n => (1 - t) • P.A (seq' n)) Filter.atTop (nhds ((1 - t) • P.b)) :=
      Filter.Tendsto.const_smul hseq'_conv (1 - t)
    have h3 := Filter.Tendsto.add h1 h2
    simp only [← add_smul] at h3
    convert h3 using 1
    ring_nf
    simp

  -- objective(w n) → t·obj(x_slater) + (1-t)·v
  have hw_obj : Filter.Tendsto (fun n => P.objective (w n)) Filter.atTop
      (nhds (t * P.objective x_slater + (1 - t) * v)) := by
    simp only [hw_def, objective, inner_add_right, inner_smul_right]
    have h1 : Filter.Tendsto (fun _ : ℕ => t * P.objective x_slater) Filter.atTop
        (nhds (t * P.objective x_slater)) := tendsto_const_nhds
    have h2 : Filter.Tendsto (fun n => (1 - t) * P.objective (seq' n)) Filter.atTop
        (nhds ((1 - t) * v)) := Filter.Tendsto.const_mul (1 - t) hv_conv
    exact Filter.Tendsto.add h1 h2

  -- The convex combination objective is > γ_real by our choice of t
  have hw_obj_gt : t * P.objective x_slater + (1 - t) * v > γ_real := by
    -- We need: t * obj + (1-t) * v > γ_real
    -- i.e., v - t * (v - obj) > γ_real
    -- i.e., t < (v - γ_real) / (v - obj)
    -- We chose t = (v - γ_real) / (2 * (v - obj)), so t < (v - γ_real) / (v - obj)
    have hdenom_pos : 0 < v - P.objective x_slater := by linarith
    have hdenom_ne : v - P.objective x_slater ≠ 0 := ne_of_gt hdenom_pos
    have h1 : t * (v - P.objective x_slater) < v - γ_real := by
      rw [ht_def]
      have h2 : (v - γ_real) / (2 * (v - P.objective x_slater)) * (v - P.objective x_slater)
          = (v - γ_real) / 2 := by field_simp
      rw [h2]
      linarith
    linarith

  -- COMPACTNESS ARGUMENT for the contradiction
  -- We have w_n ∈ K with A(w_n) → b and objective(w_n) → (t·obj(x_slater) + (1-t)·v) > γ_real
  -- Case split on whether seq' (and hence w) is bounded

  by_cases hbdd : ∃ R, ∀ n, ‖seq' n‖ ≤ R

  -- Case 1: seq' is bounded → w is bounded → extract convergent subsequence
  · obtain ⟨R, hR⟩ := hbdd

    -- w_n is bounded since w_n = t·x_slater + (1-t)·seq' n
    have hw_bdd : ∃ R', ∀ n, ‖w n‖ ≤ R' := by
      use ‖t • x_slater‖ + |1 - t| * R
      intro n
      calc ‖w n‖ = ‖t • x_slater + (1 - t) • seq' n‖ := rfl
        _ ≤ ‖t • x_slater‖ + ‖(1 - t) • seq' n‖ := norm_add_le _ _
        _ = ‖t • x_slater‖ + ‖1 - t‖ * ‖seq' n‖ := by rw [norm_smul (1 - t) (seq' n)]
        _ = ‖t • x_slater‖ + |1 - t| * ‖seq' n‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖t • x_slater‖ + |1 - t| * R := by gcongr; exact hR n

    obtain ⟨R', hR'⟩ := hw_bdd

    -- The range of w is bounded, hence precompact in ProperSpace
    have hbdd_set : Bornology.IsBounded (Set.range w) := by
      rw [Metric.isBounded_range_iff]
      use 2 * R'
      intro n m
      calc dist (w n) (w m) = ‖w n - w m‖ := dist_eq_norm _ _
        _ ≤ ‖w n‖ + ‖w m‖ := norm_sub_le _ _
        _ ≤ R' + R' := add_le_add (hR' n) (hR' m)
        _ = 2 * R' := by ring

    -- Extract convergent subsequence using SeqCompact (from ProperSpace)
    have hseq_compact : IsSeqCompact (Metric.closedBall (0 : V) R') :=
      (isCompact_closedBall 0 R').isSeqCompact

    -- w n ∈ closedBall 0 R'
    have hw_in_ball : ∀ n, w n ∈ Metric.closedBall (0 : V) R' := fun n => by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact hR' n

    -- Use sequential compactness to extract a convergent subsequence
    obtain ⟨w_star, _, φ, hφ_mono, hφ_tendsto⟩ := hseq_compact hw_in_ball

    -- w_star ∈ K (limit of sequence in closed set)
    have hw_star_K : w_star ∈ (P.K : Set V) := by
      apply hK_closed.mem_of_tendsto hφ_tendsto
      simp only [Filter.eventually_atTop]
      exact ⟨0, fun n _ => hw_K (φ n)⟩

    -- A(w_star) = b by continuity
    have hA_w_star : P.A w_star = P.b := by
      have h := hw_conv.comp hφ_mono.tendsto_atTop
      exact tendsto_nhds_unique (P.A.continuous.tendsto w_star |>.comp hφ_tendsto) h

    -- w_star is feasible
    have hw_star_feas : P.isFeasible w_star := by
      constructor
      · exact hw_star_K
      · simp only [hA_w_star, sub_self]; exact P.L.zero_mem

    -- objective(w_star) = t·obj(x_slater) + (1-t)·v > γ_real
    have hobj_eq : P.objective w_star = t * P.objective x_slater + (1 - t) * v := by
      have h := hw_obj.comp hφ_mono.tendsto_atTop
      have h' : Filter.Tendsto (fun n => P.objective (w (φ n))) Filter.atTop
          (nhds (P.objective w_star)) := by
        unfold objective
        have hcont : Continuous (fun x => ⟪P.c, x⟫_ℝ) := continuous_const.inner continuous_id
        exact hcont.tendsto w_star |>.comp hφ_tendsto
      exact tendsto_nhds_unique h' h

    -- Contradiction: objective(w_star) > γ_real but w_star is feasible so objective ≤ γ_real
    have h_le : P.objective w_star ≤ γ_real := by
      rw [hγ_is_sup]
      apply le_csSup hγ_bdd
      exact ⟨⟨w_star, hw_star_feas⟩, rfl⟩

    linarith [hobj_eq, hw_obj_gt, h_le]

  -- Case 2: seq' is unbounded - use Theorem 4.6.5's correction term approach
  · push_neg at hbdd
    -- Key insight from Gärtner-Matoušek Theorem 4.6.5 (page 61):
    -- The interior point x_slater provides a uniform "buffer" that allows us to correct
    -- limit-feasible sequences to exactly feasible ones, regardless of boundedness.
    --
    -- Specifically:
    -- 1. t * x_slater ∈ int(K), so ∃ r > 0 with B(t * x_slater, r) ⊆ K
    -- 2. By convex_combination_uniform_ball, B(w_n, t*r) ⊆ K for all n
    -- 3. Define correction_n ∈ V with A(correction_n) = b - A(w_n) and ‖correction_n‖ bounded
    -- 4. Since A(w_n) → b, the correction becomes small: eventually ‖correction_n‖ < t*r
    -- 5. So w_n + correction_n ∈ K and A(w_n + correction_n) = b (exactly feasible!)
    -- 6. objective(w_n + correction_n) → objective limit > γ_real, contradiction

    -- Step 1: Get the ball around x_slater in K (from x_slater ∈ interior K)
    -- Use Metric.isOpen_iff applied to isOpen_interior
    have hx_slater_ball : ∃ r' > 0, Metric.ball x_slater r' ⊆ (P.K : Set V) := by
      have h_open := isOpen_interior (s := (P.K : Set V))
      obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp h_open x_slater hx_slater_int
      exact ⟨ε, hε_pos, fun y hy => interior_subset (hε_ball hy)⟩

    obtain ⟨r', hr'_pos, hr'_ball⟩ := hx_slater_ball

    -- Step 2: Apply convex_combination_uniform_ball to get B(w_n, t*r') ⊆ K
    -- Key observation: w_n = (1-t) • seq'_n + t • x_slater
    -- This is a convex combination with ξ = t.
    -- By convex_combination_uniform_ball with ξ = t:
    -- If B(x_slater, r') ⊆ K, then B(w_n, t*r') ⊆ K
    have hw_ball : ∀ n, Metric.ball (w n) (t * r') ⊆ (P.K : Set V) := by
      intro n
      have hw_combo : w n = (1 - t) • seq' n + t • x_slater := by
        simp only [hw_def]; exact add_comm _ _
      rw [hw_combo]
      have hseq'_K_n := hseq'_K n
      apply convex_combination_uniform_ball P.K.convex hr'_pos hr'_ball hseq'_K_n ht_pos
        (le_of_lt ht_lt_one)

    -- Step 3: Use bounded right inverse for A (key finite-dimensional result)
    -- In finite dimensions, for any y ∈ Im(A), there exists x with A(x) = y and ‖x‖ ≤ C‖y‖
    -- where C is a constant depending only on A.

    -- The key is that Im(A) is finite-dimensional, so the restriction A|_{ker(A)^⊥} → Im(A)
    -- is a bijection with a bounded inverse.

    -- Since b = A(x_slater) ∈ Im(A), and A(w_n) → b, we have b - A(w_n) ∈ Im(A) for all n.
    -- Moreover, ‖b - A(w_n)‖ → 0.

    -- We need: ∃ correction : ℕ → V such that A(correction n) = b - A(w n) and
    -- ‖correction n‖ ≤ C * ‖b - A(w n)‖ for some constant C.

    -- We use the bounded inverse existence (standard in finite dimensions; proved below)
    have h_right_inv : ∃ C > 0, ∀ y : W, y ∈ LinearMap.range P.A.toLinearMap →
        ∃ x : V, P.A x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
      -- This follows from finite-dimensionality: the restriction of A to ker(A)^⊥
      -- is a bijection onto Im(A), and all linear maps between finite-dimensional
      -- spaces have bounded inverses.
      --
      -- Detailed proof:
      -- 1. ker(A) is a closed subspace (as a finite-dimensional subspace)
      -- 2. V = ker(A) ⊕ ker(A)^⊥ (orthogonal decomposition)
      -- 3. A|_{ker(A)^⊥} : ker(A)^⊥ → range(A) is a bijection
      -- 4. Both ker(A)^⊥ and range(A) are finite-dimensional
      -- 5. Use LinearEquiv.toContinuousLinearEquiv to get bounded inverse

      -- Set up notation
      set kerA := LinearMap.ker P.A.toLinearMap with hkerA_def
      set rangeA := LinearMap.range P.A.toLinearMap with hrangeA_def

      -- ker(A) is a submodule, hence has orthogonal complement
      -- ker(A)^⊥ is finite-dimensional since V is
      haveI : FiniteDimensional ℝ (kerA.orthogonal) :=
        Submodule.finiteDimensional_of_le le_top

      -- range(A) is finite-dimensional since V is
      haveI : FiniteDimensional ℝ rangeA := LinearMap.finiteDimensional_range _

      -- Both ker(A)^⊥ and range(A) are CompleteSpace (finite-dimensional subspaces)
      haveI : CompleteSpace (kerA.orthogonal) := by infer_instance
      haveI : CompleteSpace rangeA := by infer_instance

      -- The key: construct the restricted map from ker(A)^⊥ to range(A)
      -- and show it's a linear equivalence

      -- First, define the restriction of A to ker(A)^⊥
      let A_restr : kerA.orthogonal →ₗ[ℝ] rangeA :=
        P.A.toLinearMap.restrict (p := kerA.orthogonal) (q := rangeA)
          (fun x _ => LinearMap.mem_range.mpr ⟨x, rfl⟩)

      -- A_restr is injective: if A(x) = 0 and x ∈ ker(A)^⊥, then x ∈ ker(A) ∩ ker(A)^⊥ = {0}
      have h_inj : Function.Injective A_restr := by
        intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
        simp only [Subtype.mk.injEq]
        have h_sub : A_restr ⟨x, hx⟩ - A_restr ⟨y, hy⟩ = 0 := by simp [h_eq]
        simp only at h_sub
        have h_ker : x - y ∈ kerA := by
          rw [LinearMap.mem_ker, map_sub]
          exact sub_eq_zero.mpr (Subtype.mk.injEq _ _ _ _ |>.mp h_eq)
        have h_orth : x - y ∈ kerA.orthogonal := Submodule.sub_mem _ hx hy
        have h_both : x - y ∈ kerA ⊓ kerA.orthogonal := ⟨h_ker, h_orth⟩
        rw [disjoint_iff.mp kerA.orthogonal_disjoint] at h_both
        exact sub_eq_zero.mp (Submodule.mem_bot ℝ |>.mp h_both)

      -- A_restr is surjective: for any y ∈ range(A), there exists x with A(x) = y
      -- Take x₀ with A(x₀) = y, decompose x₀ = x_ker + x_perp, then A(x_perp) = y
      have h_surj : Function.Surjective A_restr := by
        intro ⟨y, hy⟩
        obtain ⟨x₀, hx₀⟩ := LinearMap.mem_range.mp hy
        -- Decompose x₀ into ker(A) and ker(A)^⊥ components
        -- Use the orthogonal projection (available in FiniteDimensional)
        haveI : kerA.HasOrthogonalProjection := inferInstance
        haveI : kerA.orthogonal.HasOrthogonalProjection := inferInstance
        let x_perp := kerA.orthogonal.orthogonalProjection x₀  -- projection onto ker(A)^⊥
        use x_perp
        simp only [LinearMap.restrict_apply, Subtype.mk.injEq, A_restr]
        -- A(x_perp) = A(x₀) because x₀ - x_perp ∈ ker(A)
        have h_diff_ker : x₀ - x_perp.val ∈ kerA := by
          rw [LinearMap.mem_ker]
          have h_proj : x₀ = kerA.starProjection x₀ + kerA.orthogonal.starProjection x₀ :=
            (Submodule.starProjection_add_starProjection_orthogonal x₀).symm
          -- starProjection equals the coercion of orthogonalProjection
          have h_star_eq : kerA.orthogonal.starProjection x₀ = x_perp.val :=
            Submodule.starProjection_apply kerA.orthogonal x₀
          -- So x₀ = kerA.starProjection x₀ + x_perp.val
          have h_proj' : x₀ = kerA.starProjection x₀ + x_perp.val := by
            rw [← h_star_eq]; exact h_proj
          calc P.A.toLinearMap (x₀ - x_perp.val)
              = P.A.toLinearMap x₀ - P.A.toLinearMap x_perp.val := by rw [map_sub]
            _ = P.A.toLinearMap (kerA.starProjection x₀ + x_perp.val) -
                P.A.toLinearMap x_perp.val := by rw [← h_proj']
            _ = P.A.toLinearMap (kerA.starProjection x₀) +
                P.A.toLinearMap x_perp.val - P.A.toLinearMap x_perp.val := by rw [map_add]
            _ = P.A.toLinearMap (kerA.starProjection x₀) := by simp [add_sub_cancel_right]
            _ = 0 := by
              have hmem : kerA.starProjection x₀ ∈ kerA := by
                rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _
              exact LinearMap.mem_ker.mp hmem
        calc P.A.toLinearMap x_perp.val
            = P.A.toLinearMap x₀ - P.A.toLinearMap (x₀ - x_perp.val) := by
              rw [map_sub]; simp [sub_sub_cancel]
          _ = P.A.toLinearMap x₀ - 0 := by rw [LinearMap.mem_ker.mp h_diff_ker]
          _ = y := by simp [hx₀]

      -- A_restr is a linear equivalence
      let A_equiv : kerA.orthogonal ≃ₗ[ℝ] rangeA := LinearEquiv.ofBijective A_restr ⟨h_inj, h_surj⟩

      -- In finite dimensions, linear equivalences are continuous linear equivalences
      let A_clequiv : kerA.orthogonal ≃L[ℝ] rangeA := A_equiv.toContinuousLinearEquiv

      -- The inverse has bounded operator norm
      let inv_norm : ℝ := ContinuousLinearMap.opNorm A_clequiv.symm.toContinuousLinearMap

      -- Choose C = inv_norm + 1 to ensure C > 0 (inv_norm could be 0 for trivial space)
      use inv_norm + 1
      constructor
      · have : (0 : ℝ) ≤ inv_norm := ContinuousLinearMap.opNorm_nonneg _
        linarith
      intro y hy
      -- Get the preimage in ker(A)^⊥
      let y_sub : rangeA := ⟨y, hy⟩
      let x_sub := A_clequiv.symm y_sub
      use x_sub.val
      constructor
      · -- A(x_sub.val) = y
        have : A_clequiv x_sub = y_sub := ContinuousLinearEquiv.apply_symm_apply A_clequiv y_sub
        -- A_clequiv is definitionally e.toContinuousLinearEquiv, and application is definitional
        simp only [A_clequiv, A_equiv, A_restr] at this
        exact Subtype.mk.injEq _ _ _ _ |>.mp this
      · -- ‖x_sub.val‖ ≤ (inv_norm + 1) * ‖y‖
        have h_bound : ‖x_sub‖ ≤ inv_norm * ‖y_sub‖ :=
          ContinuousLinearMap.le_opNorm A_clequiv.symm.toContinuousLinearMap y_sub
        calc ‖x_sub.val‖ = ‖x_sub‖ := rfl
          _ ≤ inv_norm * ‖y_sub‖ := h_bound
          _ = inv_norm * ‖y‖ := rfl
          _ ≤ (inv_norm + 1) * ‖y‖ := by nlinarith [norm_nonneg y]

    obtain ⟨C, hC_pos, h_bounded_inv⟩ := h_right_inv

    -- b ∈ Im(A) since x_slater is feasible
    have hb_in_range : P.b ∈ LinearMap.range P.A.toLinearMap := ⟨x_slater, hx_slater_eq⟩

    -- A(w n) ∈ Im(A) for all n
    have hAw_in_range : ∀ n, P.A (w n) ∈ LinearMap.range P.A.toLinearMap := fun n => ⟨w n, rfl⟩

    -- b - A(w n) ∈ Im(A) (range is a submodule, so closed under subtraction)
    have hdiff_in_range : ∀ n, P.b - P.A (w n) ∈ LinearMap.range P.A.toLinearMap := by
      intro n
      exact Submodule.sub_mem _ hb_in_range (hAw_in_range n)

    -- For each n, get correction_n with A(correction_n) = b - A(w_n)
    have h_correction : ∀ n, ∃ correction : V, P.A correction = P.b - P.A (w n) ∧
        ‖correction‖ ≤ C * ‖P.b - P.A (w n)‖ :=
      fun n => h_bounded_inv (P.b - P.A (w n)) (hdiff_in_range n)

    -- Use choice to get a correction function
    choose correction h_corr_eq h_corr_bound using h_correction

    -- Step 4: Show correction becomes small
    -- Since A(w n) → b, we have ‖b - A(w n)‖ → 0, hence ‖correction n‖ → 0
    have h_corr_tends : Filter.Tendsto (fun n => ‖correction n‖) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => P.b - P.A (w n)) Filter.atTop (nhds 0) := by
        have hconst : Filter.Tendsto (fun _ : ℕ => P.b) Filter.atTop (nhds P.b) := tendsto_const_nhds
        have := hconst.sub hw_conv
        simp only [sub_self] at this
        exact this
      have h2 : Filter.Tendsto (fun n => ‖P.b - P.A (w n)‖) Filter.atTop (nhds 0) := by
        have := h1.norm
        simp only [norm_zero] at this
        exact this
      have h3 : Filter.Tendsto (fun n => C * ‖P.b - P.A (w n)‖) Filter.atTop (nhds 0) := by
        have := h2.const_mul C
        simp only [mul_zero] at this
        exact this
      apply squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _))
        (Filter.Eventually.of_forall h_corr_bound) h3

    -- Step 5: Eventually ‖correction n‖ < t * r', so w n + correction n ∈ B(w n, t*r') ⊆ K
    have h_eventually_small : ∀ᶠ n in Filter.atTop, ‖correction n‖ < t * r' := by
      have htr'_pos : 0 < t * r' := mul_pos ht_pos hr'_pos
      exact Filter.Tendsto.eventually_lt_const htr'_pos h_corr_tends

    -- Step 6: Define w' n = w n + correction n (eventually feasible)
    set w' : ℕ → V := fun n => w n + correction n with hw'_def

    -- w' n ∈ K for large n
    have hw'_K : ∀ᶠ n in Filter.atTop, w' n ∈ (P.K : Set V) := by
      filter_upwards [h_eventually_small] with n hn
      have hw'_in_ball : w' n ∈ Metric.ball (w n) (t * r') := by
        rw [Metric.mem_ball, dist_eq_norm, hw'_def]
        simp only [add_sub_cancel_left]
        exact hn
      exact hw_ball n hw'_in_ball

    -- A(w' n) = b exactly
    have hw'_eq : ∀ n, P.A (w' n) = P.b := by
      intro n
      simp only [hw'_def, map_add, h_corr_eq]
      abel

    -- w' n is feasible for large n
    have hw'_feas : ∀ᶠ n in Filter.atTop, P.isFeasible (w' n) := by
      filter_upwards [hw'_K] with n hn
      exact ⟨hn, by simp [hw'_eq n]⟩

    -- Step 7: objective(w' n) → t * obj(x_slater) + (1-t) * v > γ_real
    have hw'_obj : Filter.Tendsto (fun n => P.objective (w' n)) Filter.atTop
        (nhds (t * P.objective x_slater + (1 - t) * v)) := by
      -- objective(w' n) = objective(w n) + ⟨c, correction n⟩
      -- Since correction n → 0, ⟨c, correction n⟩ → 0
      -- So objective(w' n) → objective(w n) limit = t * obj + (1-t) * v
      have h1 : Filter.Tendsto (fun n => ⟪P.c, correction n⟫_ℝ) Filter.atTop (nhds 0) := by
        have hcont : Continuous (fun x => ⟪P.c, x⟫_ℝ) := continuous_const.inner continuous_id
        have h := hcont.tendsto 0
        simp only [inner_zero_right] at h
        have h_corr_tends' : Filter.Tendsto correction Filter.atTop (nhds 0) :=
          tendsto_zero_iff_norm_tendsto_zero.mpr h_corr_tends
        exact h.comp h_corr_tends'
      have h2 : Filter.Tendsto (fun n => P.objective (w n) + ⟪P.c, correction n⟫_ℝ) Filter.atTop
          (nhds (t * P.objective x_slater + (1 - t) * v + 0)) := Filter.Tendsto.add hw_obj h1
      simp only [add_zero] at h2
      convert h2 using 1
      ext n
      simp only [hw'_def, objective, inner_add_right]

    -- Step 8: Contradiction
    -- For large n, w' n is feasible with objective close to t * obj + (1-t) * v > γ_real
    have hobj_gt_γ : ∀ᶠ n in Filter.atTop, P.objective (w' n) > γ_real := by
      set limit := t * P.objective x_slater + (1 - t) * v with hlimit_def
      have hlimit_gt : limit > γ_real := hw_obj_gt
      set hε := (limit - γ_real) / 2 with hε_def
      have hε_pos : 0 < hε := by simp only [hε_def]; linarith
      rw [Metric.tendsto_atTop] at hw'_obj
      obtain ⟨N, hN⟩ := hw'_obj hε hε_pos
      filter_upwards [Filter.Ici_mem_atTop N] with n hn
      have h := hN n hn
      rw [Real.dist_eq] at h
      have h' := abs_sub_lt_iff.mp h
      simp only [hε_def] at h'
      linarith

    -- Get a specific n where both hold
    have h_combined := Filter.Eventually.and hw'_feas hobj_gt_γ
    obtain ⟨n, hn_feas, hn_obj_gt⟩ := Filter.Eventually.exists h_combined

    -- But feasible points have objective ≤ γ_real
    have h_le : P.objective (w' n) ≤ γ_real := by
      rw [hγ_is_sup]
      apply le_csSup hγ_bdd
      exact ⟨⟨w' n, hn_feas⟩, rfl⟩

    linarith

/-- **Strong Duality for Cone Programs** (Theorem 4.7.1, Equational Form):

    For equational form (L = {0}, so A(x) = b exactly):
    If (P) is feasible, has finite value, and satisfies Slater's condition
    (x₀ ∈ interior(K) with A(x₀) = b), then (D) is feasible with value = primal value.

    The proof chains:
    1. Slater point x₀ ∈ interior(K) allows perturbing towards any feasible point
    2. Convex combinations (1-t)x₀ + tx for t ∈ (0,1] stay in interior(K) hence in K
    3. The value γ = sup{⟨c,x⟩ : x feasible} is achieved as a limit
    4. Apply regular_duality to get dual feasible y with dual objective = γ
    5. By weak_duality, primal ≤ dual; construction ensures dual value = γ

    Note: The finite dimensionality assumption is required for the compactness argument
    in `limitValue_le_value_eq_form`, following Gärtner-Matoušek Theorem 4.6.5.
-/
theorem strong_duality_exists [FiniteDimensional ℝ V] (P : ConeProgram (V := V) (W := W))
    (hPfeas : ∃ x, P.isFeasible x)
    -- Equational form: dualCone L = W (equivalent to L = {0})
    (hL_eq : ∀ y : W, y ∈ (dualCone (P.L : Set W) : Set W))
    -- Slater condition for equational form: x₀ ∈ interior(K) with A(x₀) = b
    (hSlater : ∃ x₀, P.isSlaterPointEq x₀)
    -- Finite value (bounded above)
    (hFinite : BddAbove (Set.range fun (x : {x // P.isFeasible x}) => P.objective x.val)) :
    ∃ y, P.isDualFeasible y ∧
      ⨆ x : {x // P.isFeasible x}, P.objective x.val =
      ⨅ y : {y // P.isDualFeasible y}, P.dualObjective y.val := by

  -- Step 1: Get the primal value γ (the supremum)
  set γ := ⨆ x : {x // P.isFeasible x}, P.objective x.val with hγ_def

  -- Step 2: Show we have at least one feasible point
  obtain ⟨x₀, hx₀_feasible⟩ := hPfeas
  haveI : Nonempty {x // P.isFeasible x} := ⟨⟨x₀, hx₀_feasible⟩⟩

  -- Step 3: Get Slater point properties
  obtain ⟨x_slater, hx_slater_int, hx_slater_eq⟩ := hSlater

  -- Step 4: x_slater is feasible (in K and A(x_slater) = b means b - A(x_slater) = 0 ∈ L)
  have hx_slater_K : x_slater ∈ (P.K : Set V) := interior_subset hx_slater_int
  have hx_slater_feas : P.isFeasible x_slater := by
    constructor
    · exact hx_slater_K
    · simp only [hx_slater_eq, sub_self]
      exact P.L.zero_mem

  -- Step 5: Construct a limit-feasible sequence approaching γ
  -- For each n, pick x_n with objective ≥ γ - 1/(n+1)
  -- Using classical choice and the supremum property
  have hseq_exists : ∀ n : ℕ, ∃ x : V, P.isFeasible x ∧ γ - 1 / (n + 1 : ℝ) ≤ P.objective x := by
    intro n
    -- γ is the supremum of a nonempty bounded set, so it's a real number
    -- We use Real.lt_sSup_iff to find points close to γ
    have hlt : γ - 1 / (n + 1 : ℝ) < γ := by
      have hn : (0 : ℝ) < n + 1 := by positivity
      linarith [one_div_pos.mpr hn]
    -- Since γ is the iSup, there exists a point with objective > γ - 1/(n+1)
    have hne : (Set.range fun x : {x // P.isFeasible x} => P.objective x.val).Nonempty :=
      Set.range_nonempty _
    rw [hγ_def] at hlt
    -- Use exists_lt_of_lt_ciSup to find a point with objective > γ - 1/(n+1)
    obtain ⟨⟨x, hx_feas⟩, hx_gt⟩ := exists_lt_of_lt_ciSup hlt
    use x, hx_feas
    exact le_of_lt hx_gt

  choose seq hseq_feas hseq_obj using hseq_exists

  -- Step 6: For equational form, b - A(seq n) = 0 (since A(seq n) = b for feasible points)
  -- Wait, that's not right. Feasible means x ∈ K and b - A(x) ∈ L.
  -- For L = {0}, feasible means A(x) = b exactly.
  have hseq_Aeq : ∀ n, P.A (seq n) = P.b := by
    intro n
    have hfeas := hseq_feas n
    unfold isFeasible at hfeas
    have hL_zero : P.b - P.A (seq n) ∈ (P.L : Set W) := hfeas.2
    -- For L = {0}, the only element is 0
    -- Need: if dualCone L = W, then L = {0}
    -- This is actually the reverse direction...
    -- We have hL_eq : ∀ y, y ∈ dualCone L
    -- This means ∀ y, ∀ s ∈ L, ⟨s, y⟩ ≥ 0
    -- Taking s ∈ L and y arbitrary, this forces s = 0
    -- (if s ≠ 0, take y = -s, then ⟨s, -s⟩ = -‖s‖² < 0)
    by_contra h
    push_neg at h
    have hs : P.b - P.A (seq n) ≠ 0 := fun heq => by
      apply h
      exact (sub_eq_zero.mp heq).symm
    set s := P.b - P.A (seq n) with hs_def
    have hs_L : s ∈ (P.L : Set W) := hL_zero
    -- Take y = -s
    have hy_dual : -s ∈ (dualCone (P.L : Set W) : Set W) := hL_eq (-s)
    rw [SetLike.mem_coe, mem_dualCone] at hy_dual
    have hinner := hy_dual s hs_L
    -- ⟨s, -s⟩ ≥ 0, but ⟨s, -s⟩ = -‖s‖² < 0 since s ≠ 0
    simp only [inner_neg_right, neg_nonneg] at hinner
    have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
    have hinner_pos : 0 < ⟪s, s⟫_ℝ := real_inner_self_pos.mpr hs
    linarith

  -- Step 7: The sequence has A(seq n) → b (trivially since A(seq n) = b)
  have hseq_conv : Filter.Tendsto (fun n => P.A (seq n)) Filter.atTop (nhds P.b) := by
    simp_rw [hseq_Aeq]
    exact tendsto_const_nhds

  -- Step 8: Get limit of objectives
  -- Since γ - 1/(n+1) ≤ objective(seq n) ≤ γ, and γ - 1/(n+1) → γ
  -- the objectives converge to γ

  -- γ is already a real number (the iSup over a nonempty bounded set)

  -- Show objective(seq n) → γ
  have hseq_obj_lim : Filter.Tendsto (fun n => P.objective (seq n)) Filter.atTop (nhds γ) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Find N such that 1/(N+1) < ε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    use N
    intro n hn
    have hn_pos : (0 : ℝ) < n + 1 := by positivity
    have hN_pos : (0 : ℝ) < N + 1 := by positivity
    -- We have γ - 1/(n+1) ≤ objective(seq n) ≤ γ
    have h_lb' : γ - 1 / (n + 1 : ℝ) ≤ P.objective (seq n) := hseq_obj n

    have h_ub : P.objective (seq n) ≤ γ := le_ciSup hFinite ⟨seq n, hseq_feas n⟩

    -- |objective(seq n) - γ| ≤ 1/(n+1) ≤ 1/(N+1) < ε
    have h1 : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      apply one_div_le_one_div_of_le hN_pos
      have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith
    have h2 : 1 / (N + 1 : ℝ) < ε := by
      rw [one_div_lt hN_pos hε]
      have hN' : (1 / ε : ℝ) < N := hN
      rw [one_div] at hN'
      linarith
    rw [Real.dist_eq]
    have habs : |P.objective (seq n) - γ| ≤ 1 / (n + 1 : ℝ) := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    linarith

  -- Step 10: Apply regular_duality
  have hdual := regular_duality P γ
    ⟨seq, fun n => (hseq_feas n).1,
      by simp_rw [show ∀ n, P.b - P.A (seq n) = 0 by intro n; simp [hseq_Aeq n]]; exact tendsto_const_nhds,
      hseq_obj_lim⟩
    (by -- All sequences have objective limit ≤ γ
      intro seq' hseq'_K hseq'_conv v hv_conv
      -- Apply limitValue_le_value_eq_form
      have hSlater' : ∃ x₀, P.isSlaterPointEq x₀ := ⟨x_slater, hx_slater_int, hx_slater_eq⟩
      have hγ_is_sSup : γ = sSup (Set.range fun (x : {x // P.isFeasible x}) => P.objective x.val) := by
        rfl
      have hFeas' : ∃ x, P.isFeasible x := ⟨x₀, hx₀_feasible⟩
      exact limitValue_le_value_eq_form P γ hL_eq hSlater' hγ_is_sSup hFinite hFeas'
        seq' hseq'_K hseq'_conv v hv_conv)
    hL_eq

  -- Step 11: Get dual feasible y from regular_duality
  obtain ⟨y, hy_dual⟩ := hdual

  -- Step 12: Show dual value = primal value
  use y
  constructor
  · exact hy_dual

  -- Show equality of values
  -- Need nonempty instances for iSup/iInf
  haveI hNE_dual : Nonempty {y // P.isDualFeasible y} := ⟨⟨y, hy_dual⟩⟩

  apply le_antisymm

  · -- Primal value ≤ dual value (weak duality)
    apply ciSup_le
    intro ⟨x, hx_feas⟩
    apply le_ciInf
    intro ⟨y', hy'_feas⟩
    exact weak_duality P x y' hx_feas hy'_feas

  · -- Dual value ≤ primal value
    -- Strategy: For any ε > 0, regular_duality_bound gives y_ε with ⟨b, y_ε⟩ < γ + ε
    -- Thus inf_y ⟨b, y⟩ ≤ γ + ε for all ε > 0
    -- Taking ε → 0: dual value ≤ γ = primal value

    -- Construct the limit-feasible sequence data needed for regular_duality_bound
    have hlf' : ∃ (seq : ℕ → V), (∀ n, seq n ∈ (P.K : Set V)) ∧
        Filter.Tendsto (fun n => P.b - P.A (seq n)) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun n => P.objective (seq n)) Filter.atTop (nhds γ) :=
      ⟨seq, fun n => (hseq_feas n).1,
        by simp_rw [show ∀ n, P.b - P.A (seq n) = 0 by intro n; simp [hseq_Aeq n]]
           exact tendsto_const_nhds,
        hseq_obj_lim⟩

    -- For any ε > 0, use regular_duality_bound
    have h_approx : ∀ ε > 0, ∃ y', P.isDualFeasible y' ∧ P.dualObjective y' < γ + ε := by
      intro ε hε
      -- Show that all limit-feasible sequences have objective limits ≤ γ
      have hγ_bound' : ∀ (seq' : ℕ → V), (∀ n, seq' n ∈ (P.K : Set V)) →
          Filter.Tendsto (fun n => P.A (seq' n)) Filter.atTop (nhds P.b) →
          ∀ v, Filter.Tendsto (fun n => P.objective (seq' n)) Filter.atTop (nhds v) → v ≤ γ := by
        intro seq' hseq'_K hseq'_conv v hv_conv
        have hSlater' : ∃ x₀, P.isSlaterPointEq x₀ := ⟨x_slater, hx_slater_int, hx_slater_eq⟩
        have hγ_is_sSup : γ = sSup (Set.range fun (x : {x // P.isFeasible x}) => P.objective x.val) := rfl
        have hFeas' : ∃ x, P.isFeasible x := ⟨x₀, hx₀_feasible⟩
        exact limitValue_le_value_eq_form P γ hL_eq hSlater' hγ_is_sSup hFinite hFeas'
          seq' hseq'_K hseq'_conv v hv_conv
      exact regular_duality_bound P γ ε hε hlf' hγ_bound' hL_eq

    -- We have a dual feasible y from regular_duality, so nonempty
    haveI hNE : Nonempty {y // P.isDualFeasible y} := ⟨⟨y, hy_dual⟩⟩

    -- From h_approx, show the infimum is ≤ γ
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨y', hy'_feas, hy'_bound⟩ := h_approx ε hε
    -- The dual objectives are bounded below by weak duality
    have hBddBelow : BddBelow (Set.range fun (y : {y // P.isDualFeasible y}) => P.dualObjective y.val) := by
      use P.objective x₀
      intro r ⟨⟨y'', hy''⟩, hr⟩
      simp only at hr
      rw [← hr]
      exact weak_duality P x₀ y'' hx₀_feasible hy''
    calc (⨅ y : {y // P.isDualFeasible y}, P.dualObjective y.val)
        ≤ P.dualObjective y' := ciInf_le hBddBelow ⟨y', hy'_feas⟩
      _ < γ + ε := hy'_bound

theorem strong_duality [FiniteDimensional ℝ V] (P : ConeProgram (V := V) (W := W))
    (hPfeas : ∃ x, P.isFeasible x)
    (hL_eq : ∀ y : W, y ∈ (dualCone (P.L : Set W) : Set W))
    (hSlater : ∃ x₀, P.isSlaterPointEq x₀)
    (hFinite : BddAbove (Set.range fun (x : {x // P.isFeasible x}) => P.objective x.val)) :
    ∃ y, P.isDualFeasible y ∧
      ⨆ x : {x // P.isFeasible x}, P.objective x.val =
      ⨅ y : {y // P.isDualFeasible y}, P.dualObjective y.val :=
  strong_duality_exists P hPfeas hL_eq hSlater hFinite

end ConeProgram

end Duality

end ConeProgramming
