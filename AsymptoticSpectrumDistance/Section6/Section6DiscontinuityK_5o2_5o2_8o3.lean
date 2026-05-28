/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# `(5/2, 5/2, 8/3)` is an α₃-discontinuity

Paper Theorem 6.9 case 7 (line 2806). The smallest non-integer α₃-discontinuity.

## Strategy

Let `v := ![(5,2),(5,2),(8,3)]`. We have `alphaK v = alpha3 v = 11`.

For `u` valid with `ltPermK u v`, suppose for contradiction `alphaK u ≥ 11`.
By αₖ-monotonicity, `alphaK u ≤ alphaK v = 11`, so `alphaK u = 11`.

Reduce to a coprime form `u₀` (same `alphaK` since same `toRat`).
Apply `alphaK_attained_with_bounded_max` to get `u'` valid coprime with
`lePermK u' u₀` (so `lePermK u' v` by transitivity), `alphaK u' = 11`, and
`(u' i).1 ≤ 11` for all `i`.

Each slot of `u'` is one of 6 allowed `(p, q)` pairs determined by:
- `2 ≤ p / q ≤ 8/3` (validity + ≤ max of `v`),
- `p ≤ 11` (numerator bound),
- `coprime(p, q)`.

The pairs are: `(2,1), (5,2), (7,3), (8,3), (9,4), (11,5)`.

Case A: every slot has `3p < 8q` (strict ratio < 8/3). By
`alpha3_le_10_of_lt_8o3`, `alphaK u' ≤ 10 < 11`. Contradiction.

Case B: some slot equals `(8, 3)`. Permute so that slot is last (position 2);
the other two slots are in `allowedPairs` with `3p < 8q`. By the multiset
strict-less constraint `ltPermK u' v`, the other two pairs aren't both
`(5, 2)`. By `alpha3_le_nestedFloor3Nat` with `(8,3)` last, `alphaK u' ≤
nestedFloor3Nat p₁ q₁ p₂ q₂ 8 3 ≤ 10`. Contradiction.

## Main results

* `alphaK_5o2_5o2_8o3_isDiscontinuityK` — K-form disc claim.
* `alpha3_5o2_5o2_8o3_isDiscontinuity` — FracTriple-form disc claim, by bridge.
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKAlphaTable
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## The disc point and its `alphaK` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(5,2),(5,2),(8,3)] = 11`. Direct from `alpha3_5o2_5o2_8o3` via
    the K-bridge. -/
theorem alphaK_5o2_5o2_8o3_eq :
    alphaK (![(5,2),(5,2),(8,3)] : FracTuple 3) = 11 := by
  rw [alphaK_three]
  change ((fractionGraph 5 2 ⊠ fractionGraph 5 2) ⊠ fractionGraph 8 3).indepNum = 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_5o2_5o2_8o3

private lemma validK_5o2_5o2_8o3 :
    ValidK (![(5,2),(5,2),(8,3)] : FracTuple 3) := by
  intro i; fin_cases i <;> decide

/-! ## Slot membership in allowed pairs -/

/-- The 6 allowed `(p, q) : ℕ × ℕ` pairs: coprime, lowest terms, `2q ≤ p ≤ 8q/3`,
    and `p ≤ 11`. -/
private def allowedPairs : List (ℕ × ℕ) :=
  [(2, 1), (5, 2), (7, 3), (8, 3), (9, 4), (11, 5)]

/-- Membership in `allowedPairs` from the constraints. -/
private lemma slot_in_allowedPairs (p q : ℕ) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (h_valid : 2 * q ≤ p) (h_p_le : p ≤ 11) (h_ratio_le : 3 * p ≤ 8 * q)
    (h_coprime : Nat.Coprime p q) :
    (p, q) ∈ allowedPairs := by
  -- Brute interval analysis. Since `2q ≤ p ≤ 11`, `q ≤ 5`. And `p ≥ 2`.
  have hq_le_5 : q ≤ 5 := by omega
  have hp_ge_2 : 2 ≤ p := by omega
  unfold allowedPairs
  -- For each (p, q) within bounds, either it's in the list or excluded by
  -- omega (ratio bounds), or excluded by coprimality (decide on Nat.Coprime).
  interval_cases q <;> interval_cases p <;>
    first
    | (exfalso; omega)
    | (exfalso; revert h_coprime; decide)
    | simp

/-- A pair in `allowedPairs` either equals `(8, 3)` or has `3 p < 8 q`. -/
private lemma allowedPair_strict_or_8o3 {p q : ℕ}
    (h_mem : (p, q) ∈ allowedPairs) :
    (p, q) = (8, 3) ∨ 3 * p < 8 * q := by
  unfold allowedPairs at h_mem
  fin_cases h_mem <;> first | (left; rfl) | (right; omega)

/-! ## Case A bound: all slots `< 8/3` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- If a `FracTuple 3` is valid and each slot has `3 (u i).1 < 8 (u i).2`,
    then `alphaK u ≤ 10`. -/
private lemma alphaK_le_10_of_all_lt_8o3 {u : FracTuple 3}
    (h_valid : ValidK u)
    (h_strict : ∀ i, 3 * ((u i).1 : ℕ) < 8 * ((u i).2 : ℕ)) :
    alphaK u ≤ 10 := by
  rw [alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  haveI : NeZero ((u 0).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 0).1.pos⟩
  haveI : NeZero ((u 1).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 1).1.pos⟩
  haveI : NeZero ((u 2).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 2).1.pos⟩
  have h2q : ∀ i, 2 * ((u i).2 : ℕ) ≤ ((u i).1 : ℕ) := fun i => by exact_mod_cast h_valid i
  have hq_pos : ∀ i, 0 < ((u i).2 : ℕ) := fun i => (u i).2.pos
  exact alpha3_le_10_of_lt_8o3 _ _ _ _ _ _
    (hq_pos 0) (h2q 0) (h_strict 0)
    (hq_pos 1) (h2q 1) (h_strict 1)
    (hq_pos 2) (h2q 2) (h_strict 2)

/-! ## Case B bound: one slot is `(8, 3)`, first position. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Nested-floor bound for `((8, 3), (p₁, q₁), (p₂, q₂))` viewed as a FracTuple. -/
private lemma alphaK_le_nestedFloor_with_8o3_first {u : FracTuple 3}
    (h_valid : ValidK u)
    (h_p0 : ((u 0).1 : ℕ) = 8) (h_q0 : ((u 0).2 : ℕ) = 3) :
    alphaK u ≤ nestedFloor3Nat 8 3 ((u 1).1 : ℕ) ((u 1).2 : ℕ)
                                ((u 2).1 : ℕ) ((u 2).2 : ℕ) := by
  rw [alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  haveI : NeZero ((u 0).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 0).1.pos⟩
  haveI : NeZero ((u 1).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 1).1.pos⟩
  haveI : NeZero ((u 2).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 2).1.pos⟩
  have h2q : ∀ i, 2 * ((u i).2 : ℕ) ≤ ((u i).1 : ℕ) := fun i => by exact_mod_cast h_valid i
  have hq_pos : ∀ i, 0 < ((u i).2 : ℕ) := fun i => (u i).2.pos
  have h := alpha3_le_nestedFloor3Nat
    ((u 0).1 : ℕ) ((u 0).2 : ℕ) ((u 1).1 : ℕ) ((u 1).2 : ℕ)
    ((u 2).1 : ℕ) ((u 2).2 : ℕ)
    (hq_pos 0) (h2q 0) (hq_pos 1) (h2q 1) (hq_pos 2) (h2q 2)
  have h_eq : nestedFloor3Nat ((u 0).1 : ℕ) ((u 0).2 : ℕ) ((u 1).1 : ℕ) ((u 1).2 : ℕ)
                ((u 2).1 : ℕ) ((u 2).2 : ℕ) =
              nestedFloor3Nat 8 3 ((u 1).1 : ℕ) ((u 1).2 : ℕ)
                ((u 2).1 : ℕ) ((u 2).2 : ℕ) := by
    unfold nestedFloor3Nat; rw [h_p0, h_q0]
  rw [h_eq] at h
  exact h

/-- `nestedFloor3Nat 8 3 p₁ q₁ p₂ q₂ ≤ 10` whenever the middle pair
    `(p₁, q₁) ∉ {(5, 2), (8, 3)}` and both pairs are in `allowedPairs`. -/
private lemma nestedFloor_8o3_first_le_10
    {p₁ q₁ p₂ q₂ : ℕ}
    (h₁ : (p₁, q₁) ∈ allowedPairs)
    (h_ne_5o2 : (p₁, q₁) ≠ (5, 2)) (h_ne_8o3 : (p₁, q₁) ≠ (8, 3))
    (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat 8 3 p₁ q₁ p₂ q₂ ≤ 10 := by
  unfold allowedPairs at h₁ h₂
  unfold nestedFloor3Nat
  fin_cases h₁ <;> fin_cases h₂ <;>
    first
    | (exfalso; exact h_ne_5o2 rfl)
    | (exfalso; exact h_ne_8o3 rfl)
    | decide

/-! ## Main: the disc proof in K-form -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9.** The tuple `(5/2, 5/2, 8/3)` is
    an α₃-discontinuity. -/
theorem alphaK_5o2_5o2_8o3_isDiscontinuityK :
    IsDiscontinuityK (![(5,2),(5,2),(8,3)] : FracTuple 3) := by
  set v : FracTuple 3 := ![(5,2),(5,2),(8,3)] with hv_def
  have hv_valid : ValidK v := validK_5o2_5o2_8o3
  have hα_v : alphaK v = 11 := alphaK_5o2_5o2_8o3_eq
  intro u hu_valid hu_lt
  by_contra h_not_lt
  push_neg at h_not_lt
  -- h_not_lt : alphaK v ≤ alphaK u, i.e., 11 ≤ alphaK u.
  -- αₖ-monotonicity: alphaK u ≤ alphaK v = 11.
  have hu_le_v : lePermK u v := hu_lt.1
  have hα_u_le : alphaK u ≤ alphaK v := alphaK_le_of_lePermK hu_valid hv_valid hu_le_v
  have hα_u : alphaK u = 11 := by
    rw [hα_v] at hα_u_le h_not_lt; omega
  -- Reduce u to coprime form.
  obtain ⟨u₀, hu₀_valid, hu₀_eq, hu₀_coprime⟩ := exists_coprime_form u hu_valid
  have hα_u₀ : alphaK u₀ = 11 := by
    rw [alphaK_eq_of_toRat_eq hu₀_valid hu_valid hu₀_eq, hα_u]
  -- Apply alphaK_attained_with_bounded_max to u₀.
  obtain ⟨u', hu'_valid, hu'_le_u₀, hu'_alpha, hu'_bound, hu'_coprime⟩ :=
    alphaK_attained_with_bounded_max hu₀_valid hu₀_coprime
  have hα_u' : alphaK u' = 11 := by rw [hu'_alpha, hα_u₀]
  -- Each (u' i).1 ≤ 11.
  have hu'_p_le : ∀ i, ((u' i).1 : ℕ) ≤ 11 := fun i => by
    have := hu'_bound i; rw [hα_u'] at this; exact this
  -- u₀ ≤ₚ v: from u ≤ₚ v + toRat preservation.
  have hu₀_le_v : lePermK u₀ v := by
    obtain ⟨σ, hσ⟩ := hu_le_v
    refine ⟨σ, fun i => ?_⟩
    rw [hu₀_eq (σ i)]; exact hσ i
  -- u' ≤ₚ v: chain through u₀.
  have hu'_le_v : lePermK u' v := by
    obtain ⟨σ₁, hσ₁⟩ := hu'_le_u₀
    obtain ⟨σ₂, hσ₂⟩ := hu₀_le_v
    refine ⟨σ₁ * σ₂, fun i => ?_⟩
    calc FracTuple.toRat u' ((σ₁ * σ₂) i)
        = FracTuple.toRat u' (σ₁ (σ₂ i)) := by rw [Equiv.Perm.mul_apply]
      _ ≤ FracTuple.toRat u₀ (σ₂ i) := hσ₁ (σ₂ i)
      _ ≤ FracTuple.toRat v i := hσ₂ i
  -- Each slot of u' has ratio ≤ max ratio of v = 8/3.
  obtain ⟨σ_uv, hσ_uv⟩ := hu'_le_v
  have hv_toRat_le_8o3 : ∀ k : Fin 3, FracTuple.toRat v k ≤ (8 : ℚ) / 3 := by
    intro k
    simp only [hv_def, FracTuple.toRat]
    fin_cases k <;> norm_num
  have hu'_ratio_le_8o3 : ∀ i, 3 * ((u' i).1 : ℕ) ≤ 8 * ((u' i).2 : ℕ) := by
    intro i
    have h_sym : σ_uv (σ_uv.symm i) = i := σ_uv.apply_symm_apply i
    have h_le_at_j : FracTuple.toRat u' i ≤ FracTuple.toRat v (σ_uv.symm i) := by
      have h := hσ_uv (σ_uv.symm i); rw [h_sym] at h; exact h
    have h_le : FracTuple.toRat u' i ≤ (8 : ℚ) / 3 :=
      h_le_at_j.trans (hv_toRat_le_8o3 _)
    unfold FracTuple.toRat at h_le
    have hq_pos : (0 : ℚ) < ((u' i).2 : ℚ) := by exact_mod_cast (u' i).2.pos
    rw [div_le_div_iff₀ hq_pos (by norm_num : (0 : ℚ) < 3)] at h_le
    -- h_le : ((u' i).1 : ℚ) * 3 ≤ 8 * ((u' i).2 : ℚ).
    have h_int : (((u' i).1 : ℕ) : ℚ) * 3 ≤ (((u' i).2 : ℕ) : ℚ) * 8 := by linarith
    have h_int_n : ((u' i).1 : ℕ) * 3 ≤ ((u' i).2 : ℕ) * 8 := by exact_mod_cast h_int
    omega
  -- Each slot in allowedPairs.
  have hu'_in_allowed : ∀ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ∈ allowedPairs := by
    intro i
    have h2q : 2 * ((u' i).2 : ℕ) ≤ ((u' i).1 : ℕ) := by exact_mod_cast hu'_valid i
    exact slot_in_allowedPairs _ _ (u' i).1.pos (u' i).2.pos h2q (hu'_p_le i)
      (hu'_ratio_le_8o3 i) (hu'_coprime i)
  -- Case split on whether some slot is (8, 3).
  by_cases h_anyB : ∃ i, ((u' i).1 : ℕ) = 8 ∧ ((u' i).2 : ℕ) = 3
  · -- Case B: some slot is (8, 3). Permute to put it at slot 0.
    obtain ⟨i₀, hi₀_p, hi₀_q⟩ := h_anyB
    -- Define u_a = u' ∘ swap i₀ 0 (8,3 at slot 0).
    set τ_a : Equiv.Perm (Fin 3) := Equiv.swap i₀ 0 with hτ_a_def
    set u_a : FracTuple 3 := u' ∘ τ_a with hu_a_def
    have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ_a i)
    have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ_a).symm
    have hu_a_0_p : ((u_a 0).1 : ℕ) = 8 := by
      change ((u' (τ_a 0)).1 : ℕ) = 8
      rw [hτ_a_def, Equiv.swap_apply_right]; exact hi₀_p
    have hu_a_0_q : ((u_a 0).2 : ℕ) = 3 := by
      change ((u' (τ_a 0)).2 : ℕ) = 3
      rw [hτ_a_def, Equiv.swap_apply_right]; exact hi₀_q
    have hu_a_1_mem : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
    have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
    -- u' has at most one slot at ratio 8/3 (since v has only one). Its index is i₀.
    have hv_only_one_8o3 :
        ∀ i, ((u' i).1 : ℕ) = 8 ∧ ((u' i).2 : ℕ) = 3 → i = i₀ := by
      intro i ⟨hi_p, hi_q⟩
      by_contra hne
      have h_i_toRat : FracTuple.toRat u' i = 8 / 3 := by
        unfold FracTuple.toRat
        have h_i_p_q : (((u' i).1 : ℕ) : ℚ) = 8 := by exact_mod_cast hi_p
        have h_i_q_q : (((u' i).2 : ℕ) : ℚ) = 3 := by exact_mod_cast hi_q
        push_cast at h_i_p_q h_i_q_q ⊢
        rw [h_i_p_q, h_i_q_q]
      have h_i₀_toRat : FracTuple.toRat u' i₀ = 8 / 3 := by
        unfold FracTuple.toRat
        have h_i₀_p_q : (((u' i₀).1 : ℕ) : ℚ) = 8 := by exact_mod_cast hi₀_p
        have h_i₀_q_q : (((u' i₀).2 : ℕ) : ℚ) = 3 := by exact_mod_cast hi₀_q
        push_cast at h_i₀_p_q h_i₀_q_q ⊢
        rw [h_i₀_p_q, h_i₀_q_q]
      -- Both σ_uv⁻¹ i and σ_uv⁻¹ i₀ are slots in v with ratio ≥ 8/3, so both = 2.
      have hj_ne : σ_uv.symm i ≠ σ_uv.symm i₀ := fun h_eq => hne (σ_uv.symm.injective h_eq)
      have h_le_j : FracTuple.toRat u' i ≤ FracTuple.toRat v (σ_uv.symm i) := by
        have h := hσ_uv (σ_uv.symm i)
        rw [σ_uv.apply_symm_apply] at h; exact h
      have h_le_j₀ : FracTuple.toRat u' i₀ ≤ FracTuple.toRat v (σ_uv.symm i₀) := by
        have h := hσ_uv (σ_uv.symm i₀)
        rw [σ_uv.apply_symm_apply] at h; exact h
      have h_v_j_ge : (8 : ℚ) / 3 ≤ FracTuple.toRat v (σ_uv.symm i) := h_i_toRat ▸ h_le_j
      have h_v_j₀_ge : (8 : ℚ) / 3 ≤ FracTuple.toRat v (σ_uv.symm i₀) := h_i₀_toRat ▸ h_le_j₀
      have hv_lt_8o3 : ∀ k : Fin 3, k ≠ 2 → FracTuple.toRat v k < 8/3 := by
        intro k hk
        simp only [hv_def, FracTuple.toRat]
        fin_cases k
        · norm_num
        · norm_num
        · exact absurd rfl hk
      have hj_eq_2 : σ_uv.symm i = 2 := by
        by_contra h
        exact absurd (hv_lt_8o3 _ h) (not_lt_of_ge h_v_j_ge)
      have hj₀_eq_2 : σ_uv.symm i₀ = 2 := by
        by_contra h
        exact absurd (hv_lt_8o3 _ h) (not_lt_of_ge h_v_j₀_ge)
      exact hj_ne (hj_eq_2.trans hj₀_eq_2.symm)
    -- u_a 1 ≠ (8, 3) and u_a 2 ≠ (8, 3): since τ_a 1, τ_a 2 ≠ i₀ (by injectivity).
    have hτ_a_0 : τ_a 0 = i₀ := by rw [hτ_a_def, Equiv.swap_apply_right]
    have hτ_a_1_ne : τ_a 1 ≠ i₀ := by
      intro h
      have : τ_a 1 = τ_a 0 := h.trans hτ_a_0.symm
      exact absurd (τ_a.injective this) (by decide)
    have hτ_a_2_ne : τ_a 2 ≠ i₀ := by
      intro h
      have : τ_a 2 = τ_a 0 := h.trans hτ_a_0.symm
      exact absurd (τ_a.injective this) (by decide)
    have hu_a_1_ne_8o3 : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ≠ (8, 3) := by
      intro h
      have h_p : ((u' (τ_a 1)).1 : ℕ) = 8 := (Prod.mk.inj h).1
      have h_q : ((u' (τ_a 1)).2 : ℕ) = 3 := (Prod.mk.inj h).2
      exact hτ_a_1_ne (hv_only_one_8o3 (τ_a 1) ⟨h_p, h_q⟩)
    have hu_a_2_ne_8o3 : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ≠ (8, 3) := by
      intro h
      have h_p : ((u' (τ_a 2)).1 : ℕ) = 8 := (Prod.mk.inj h).1
      have h_q : ((u' (τ_a 2)).2 : ℕ) = 3 := (Prod.mk.inj h).2
      exact hτ_a_2_ne (hv_only_one_8o3 (τ_a 2) ⟨h_p, h_q⟩)
    -- Define u_b = u_a ∘ swap 1 2 (just for the slot-1, slot-2 swap option).
    set τ_b : Equiv.Perm (Fin 3) := Equiv.swap 1 2 with hτ_b_def
    set u_b : FracTuple 3 := u_a ∘ τ_b with hu_b_def
    have hu_b_valid : ValidK u_b := fun i => hu_a_valid (τ_b i)
    have hα_u_b : alphaK u_b = alphaK u_a := (alphaK_perm u_a τ_b).symm
    have hu_b_0_p : ((u_b 0).1 : ℕ) = 8 := by
      change ((u_a (τ_b 0)).1 : ℕ) = 8
      rw [hτ_b_def]
      rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1) (by decide : (0:Fin 3) ≠ 2)]
      exact hu_a_0_p
    have hu_b_0_q : ((u_b 0).2 : ℕ) = 3 := by
      change ((u_a (τ_b 0)).2 : ℕ) = 3
      rw [hτ_b_def]
      rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1) (by decide : (0:Fin 3) ≠ 2)]
      exact hu_a_0_q
    have hu_b_1_eq_a_2 : u_b 1 = u_a 2 := by
      change u_a (τ_b 1) = u_a 2
      rw [hτ_b_def, Equiv.swap_apply_left]
    have hu_b_2_eq_a_1 : u_b 2 = u_a 1 := by
      change u_a (τ_b 2) = u_a 1
      rw [hτ_b_def, Equiv.swap_apply_right]
    have hu_b_1_mem : (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) ∈ allowedPairs := by
      rw [hu_b_1_eq_a_2]; exact hu_a_2_mem
    -- Bound alphaK u' by min of two nested-floor expressions.
    have h_bound_a : alphaK u' ≤ nestedFloor3Nat 8 3
        ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ) ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
      rw [← hα_u_a]
      exact alphaK_le_nestedFloor_with_8o3_first hu_a_valid hu_a_0_p hu_a_0_q
    have h_bound_b : alphaK u' ≤ nestedFloor3Nat 8 3
        ((u_b 1).1 : ℕ) ((u_b 1).2 : ℕ) ((u_b 2).1 : ℕ) ((u_b 2).2 : ℕ) := by
      rw [← hα_u_a, ← hα_u_b]
      exact alphaK_le_nestedFloor_with_8o3_first hu_b_valid hu_b_0_p hu_b_0_q
    -- We have at least one of (u_a 1), (u_a 2) ≠ (5, 2) (else multiset = v).
    -- Pick the one that's not (5, 2) — use that perm to get nestedFloor ≤ 10.
    by_cases h_a1_5o2 : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (5, 2)
    · -- u_a 1 = (5, 2). Then u_a 2 ≠ (5, 2) (else multiset = v). Use u_b.
      -- u_b 1 = u_a 2, u_b 2 = u_a 1 = (5, 2).
      have h_a2_neq : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ≠ (5, 2) := by
        intro h_a2_5o2
        have h_a2_p : ((u_a 2).1 : ℕ) = 5 := (Prod.mk.inj h_a2_5o2).1
        have h_a2_q : ((u_a 2).2 : ℕ) = 2 := (Prod.mk.inj h_a2_5o2).2
        have h_a1_p : ((u_a 1).1 : ℕ) = 5 := (Prod.mk.inj h_a1_5o2).1
        have h_a1_q : ((u_a 1).2 : ℕ) = 2 := (Prod.mk.inj h_a1_5o2).2
        -- u_a has slots (8/3, 5/2, 5/2). v has (5/2, 5/2, 8/3). They're equal as multisets:
        -- specifically v ∘ swap 0 2 = u_a (pointwise rationals).
        have h_eq_perm : ∀ i, FracTuple.toRat v (Equiv.swap (0:Fin 3) 2 i) =
            FracTuple.toRat u_a i := by
          intro i
          have h_u_a_0_rat : FracTuple.toRat u_a 0 = 8 / 3 := by
            unfold FracTuple.toRat
            have h0p : (((u_a 0).1 : ℕ) : ℚ) = 8 := by exact_mod_cast hu_a_0_p
            have h0q : (((u_a 0).2 : ℕ) : ℚ) = 3 := by exact_mod_cast hu_a_0_q
            push_cast at h0p h0q ⊢
            rw [h0p, h0q]
          have h_u_a_1_rat : FracTuple.toRat u_a 1 = 5 / 2 := by
            unfold FracTuple.toRat
            have h1p : (((u_a 1).1 : ℕ) : ℚ) = 5 := by exact_mod_cast h_a1_p
            have h1q : (((u_a 1).2 : ℕ) : ℚ) = 2 := by exact_mod_cast h_a1_q
            push_cast at h1p h1q ⊢
            rw [h1p, h1q]
          have h_u_a_2_rat : FracTuple.toRat u_a 2 = 5 / 2 := by
            unfold FracTuple.toRat
            have h2p : (((u_a 2).1 : ℕ) : ℚ) = 5 := by exact_mod_cast h_a2_p
            have h2q : (((u_a 2).2 : ℕ) : ℚ) = 2 := by exact_mod_cast h_a2_q
            push_cast at h2p h2q ⊢
            rw [h2p, h2q]
          fin_cases i
          · -- i = 0: v.toRat (swap 0 2 0) = v.toRat 2 = 8/3 = u_a.toRat 0.
            change FracTuple.toRat v (Equiv.swap (0:Fin 3) 2 0) = FracTuple.toRat u_a 0
            rw [Equiv.swap_apply_left, h_u_a_0_rat]
            simp [hv_def, FracTuple.toRat]
          · -- i = 1: v.toRat (swap 0 2 1) = v.toRat 1 = 5/2 = u_a.toRat 1.
            change FracTuple.toRat v (Equiv.swap (0:Fin 3) 2 1) = FracTuple.toRat u_a 1
            rw [Equiv.swap_apply_of_ne_of_ne (by decide : (1:Fin 3) ≠ 0)
                  (by decide : (1:Fin 3) ≠ 2), h_u_a_1_rat]
            simp [hv_def, FracTuple.toRat]
          · -- i = 2: v.toRat (swap 0 2 2) = v.toRat 0 = 5/2 = u_a.toRat 2.
            change FracTuple.toRat v (Equiv.swap (0:Fin 3) 2 2) = FracTuple.toRat u_a 2
            rw [Equiv.swap_apply_right, h_u_a_2_rat]
            simp [hv_def, FracTuple.toRat]
        apply hu_lt.2
        have h_v_le_u_a : lePermK v u_a :=
          ⟨Equiv.swap (0:Fin 3) 2, fun i => (h_eq_perm i).le⟩
        have h_u_a_le_u' : lePermK u_a u' :=
          ⟨τ_a.symm, fun i => by
            change FracTuple.toRat (u' ∘ τ_a) (τ_a.symm i) ≤ FracTuple.toRat u' i
            rw [FracTuple.toRat_comp]; rw [τ_a.apply_symm_apply]⟩
        have h_u₀_le_u : lePermK u₀ u :=
          ⟨1, fun i => by simp only [Equiv.Perm.coe_one, id_eq]; exact (hu₀_eq i).le⟩
        -- Chain: v ≤ₚ u_a ≤ₚ u' ≤ₚ u₀ ≤ₚ u.
        have h_v_le_u' : lePermK v u' := by
          obtain ⟨ρ₁, hρ₁⟩ := h_v_le_u_a
          obtain ⟨ρ₂, hρ₂⟩ := h_u_a_le_u'
          refine ⟨ρ₁ * ρ₂, fun i => ?_⟩
          calc FracTuple.toRat v ((ρ₁ * ρ₂) i)
              = FracTuple.toRat v (ρ₁ (ρ₂ i)) := by rw [Equiv.Perm.mul_apply]
            _ ≤ FracTuple.toRat u_a (ρ₂ i) := hρ₁ (ρ₂ i)
            _ ≤ FracTuple.toRat u' i := hρ₂ i
        have h_v_le_u₀ : lePermK v u₀ := by
          obtain ⟨ρ₁, hρ₁⟩ := h_v_le_u'
          obtain ⟨ρ₂, hρ₂⟩ := hu'_le_u₀
          refine ⟨ρ₁ * ρ₂, fun i => ?_⟩
          calc FracTuple.toRat v ((ρ₁ * ρ₂) i)
              = FracTuple.toRat v (ρ₁ (ρ₂ i)) := by rw [Equiv.Perm.mul_apply]
            _ ≤ FracTuple.toRat u' (ρ₂ i) := hρ₁ (ρ₂ i)
            _ ≤ FracTuple.toRat u₀ i := hρ₂ i
        obtain ⟨ρ₁, hρ₁⟩ := h_v_le_u₀
        obtain ⟨ρ₂, hρ₂⟩ := h_u₀_le_u
        refine ⟨ρ₁ * ρ₂, fun i => ?_⟩
        calc FracTuple.toRat v ((ρ₁ * ρ₂) i)
            = FracTuple.toRat v (ρ₁ (ρ₂ i)) := by rw [Equiv.Perm.mul_apply]
          _ ≤ FracTuple.toRat u₀ (ρ₂ i) := hρ₁ (ρ₂ i)
          _ ≤ FracTuple.toRat u i := hρ₂ i
      -- Use u_b: u_b 1 = u_a 2 ≠ (5, 2). h_bound_b gives the bound.
      have h_b1_neq_5o2 : (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) ≠ (5, 2) := by
        rw [hu_b_1_eq_a_2]; exact h_a2_neq
      have h_b1_neq_8o3 : (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) ≠ (8, 3) := by
        rw [hu_b_1_eq_a_2]; exact hu_a_2_ne_8o3
      have h_floor_le_10 := nestedFloor_8o3_first_le_10 hu_b_1_mem h_b1_neq_5o2
        h_b1_neq_8o3
        (show (((u_b 2).1 : ℕ), ((u_b 2).2 : ℕ)) ∈ allowedPairs by
          rw [hu_b_2_eq_a_1]; exact hu_a_1_mem)
      have : alphaK u' ≤ 10 := h_bound_b.trans h_floor_le_10
      rw [hα_u'] at this
      omega
    · -- u_a 1 ≠ (5, 2). Use u_a directly.
      have h_floor_le_10 := nestedFloor_8o3_first_le_10 hu_a_1_mem h_a1_5o2
        hu_a_1_ne_8o3 hu_a_2_mem
      have : alphaK u' ≤ 10 := h_bound_a.trans h_floor_le_10
      rw [hα_u'] at this
      omega
  · -- Case A: no slot is (8, 3). Then every slot has 3p < 8q.
    push_neg at h_anyB
    have hu'_strict : ∀ i, 3 * ((u' i).1 : ℕ) < 8 * ((u' i).2 : ℕ) := by
      intro i
      rcases allowedPair_strict_or_8o3 (hu'_in_allowed i) with h_8o3 | h_strict
      · exfalso
        have h_p : ((u' i).1 : ℕ) = 8 := (Prod.mk.inj h_8o3).1
        have h_q : ((u' i).2 : ℕ) = 3 := (Prod.mk.inj h_8o3).2
        exact h_anyB i h_p h_q
      · exact h_strict
    have h_alpha_le_10 : alphaK u' ≤ 10 :=
      alphaK_le_10_of_all_lt_8o3 hu'_valid hu'_strict
    rw [hα_u'] at h_alpha_le_10
    omega

/-! ## FracTriple-form bridge -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9, FracTriple form.** -/
theorem alpha3_5o2_5o2_8o3_isDiscontinuity :
    IsDiscontinuity (![(5,2),(5,2),(8,3)] : FracTriple) :=
  (isDiscontinuity_iff_isDiscontinuityK ![(5,2),(5,2),(8,3)]).mpr
    alphaK_5o2_5o2_8o3_isDiscontinuityK

end Section6
