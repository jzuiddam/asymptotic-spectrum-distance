/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# `(14/5, 14/5, 14/5)` is an α₃-discontinuity

Paper Theorem 6.9 case 12 (line 2806). The diagonal disc point with α₃ = 14.

## Strategy

Let `v := ![(14,5),(14,5),(14,5)]`. We have `alphaK v = alpha3 v = 14`.

For `u` valid with `ltPermK u v`, suppose for contradiction `alphaK u ≥ 14`.
By αₖ-monotonicity, `alphaK u ≤ alphaK v = 14`, so `alphaK u = 14`.

Reduce to a coprime form `u₀` (same `alphaK` since same `toRat`).
Apply `alphaK_attained_with_bounded_max` to get `u'` valid coprime with
`lePermK u' u₀` (so `lePermK u' v` by transitivity), `alphaK u' = 14`, and
`(u' i).1 ≤ 14` for all `i`.

Each slot of `u'` is one of 10 allowed `(p, q)` pairs determined by:
- `2 ≤ p / q ≤ 14/5` (validity + ≤ max of `v`),
- `p ≤ 14` (numerator bound),
- `coprime(p, q)`.

The pairs are: `(2,1), (5,2), (7,3), (8,3), (9,4), (11,4), (11,5), (12,5),
(13,5), (14,5), (13,6)`.

Since `u' <ₚ v` strictly (and `v` has all three slots equal to `14/5`), at
least one slot of `u'` is not `(14, 5)`. Permute that slot to position 0
(the outermost in the nested-floor formula). Then `nestedFloor3Nat` with a
non-`(14, 5)` first slot and arbitrary `allowedPairs`-slots in positions
1, 2 gives at most `13`. Contradiction.

## Main results

* `alphaK_14o5_14o5_14o5_isDiscontinuityK` — K-form disc claim.
* `alpha3_14o5_14o5_14o5_isDiscontinuity` — FracTriple-form disc claim, by bridge.
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKAlphaTable
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## The disc point and its `alphaK` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(14,5),(14,5),(14,5)] = 14`. Direct from `alpha3_14o5_14o5_14o5`
    via the K-bridge. -/
theorem alphaK_14o5_14o5_14o5_eq :
    alphaK (![(14,5),(14,5),(14,5)] : FracTuple 3) = 14 := by
  rw [alphaK_three]
  change ((fractionGraph 14 5 ⊠ fractionGraph 14 5) ⊠ fractionGraph 14 5).indepNum = 14
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_14o5_14o5_14o5

private lemma validK_14o5_14o5_14o5 :
    ValidK (![(14,5),(14,5),(14,5)] : FracTuple 3) := by
  intro i; fin_cases i <;> decide

/-! ## Slot membership in allowed pairs -/

/-- The 11 allowed `(p, q) : ℕ × ℕ` pairs: coprime, lowest terms,
    `2q ≤ p ≤ 14q/5`, and `p ≤ 14`. -/
private def allowedPairs : List (ℕ × ℕ) :=
  [(2, 1), (5, 2), (7, 3), (8, 3), (9, 4), (11, 4),
   (11, 5), (12, 5), (13, 5), (14, 5), (13, 6)]

/-- Membership in `allowedPairs` from the constraints. -/
private lemma slot_in_allowedPairs (p q : ℕ) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (h_valid : 2 * q ≤ p) (h_p_le : p ≤ 14) (h_ratio_le : 5 * p ≤ 14 * q)
    (h_coprime : Nat.Coprime p q) :
    (p, q) ∈ allowedPairs := by
  -- Brute interval analysis. Since `2q ≤ p ≤ 14`, `q ≤ 7`. And `p ≥ 2`.
  have hq_le_7 : q ≤ 7 := by omega
  have hp_ge_2 : 2 ≤ p := by omega
  unfold allowedPairs
  -- For each (p, q) within bounds, either it's in the list or excluded by
  -- omega (ratio bounds), or excluded by coprimality.
  interval_cases q <;> interval_cases p <;>
    first
    | (exfalso; omega)
    | (exfalso; revert h_coprime; decide)
    | simp

/-! ## Nested-floor bound: `(14, 5)` is the only pair giving 14 -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Nested-floor bound for `((p₀, q₀), (p₁, q₁), (p₂, q₂))` viewed as a
    FracTuple, parameterized by the actual values at each slot. -/
private lemma alphaK_le_nestedFloor_with_first {u : FracTuple 3}
    (h_valid : ValidK u)
    (p₀ q₀ : ℕ) (h_p0 : ((u 0).1 : ℕ) = p₀) (h_q0 : ((u 0).2 : ℕ) = q₀) :
    alphaK u ≤ nestedFloor3Nat p₀ q₀ ((u 1).1 : ℕ) ((u 1).2 : ℕ)
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
              nestedFloor3Nat p₀ q₀ ((u 1).1 : ℕ) ((u 1).2 : ℕ)
                ((u 2).1 : ℕ) ((u 2).2 : ℕ) := by
    unfold nestedFloor3Nat; rw [h_p0, h_q0]
  rw [h_eq] at h
  exact h

/-- `nestedFloor3Nat p₀ q₀ p₁ q₁ p₂ q₂ ≤ 13` whenever `(p₀, q₀) ∈ allowedPairs`
    with `(p₀, q₀) ≠ (14, 5)`, and both other pairs are in `allowedPairs`. -/
private lemma nestedFloor_first_not_14o5_le_13
    {p₀ q₀ p₁ q₁ p₂ q₂ : ℕ}
    (h₀ : (p₀, q₀) ∈ allowedPairs) (h_ne : (p₀, q₀) ≠ (14, 5))
    (h₁ : (p₁, q₁) ∈ allowedPairs) (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat p₀ q₀ p₁ q₁ p₂ q₂ ≤ 13 := by
  unfold allowedPairs at h₀ h₁ h₂
  unfold nestedFloor3Nat
  fin_cases h₀ <;> fin_cases h₁ <;> fin_cases h₂ <;>
    first
    | (exfalso; exact h_ne rfl)
    | decide

/-! ## Main: the disc proof in K-form -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9.** The tuple `(14/5, 14/5, 14/5)`
    is an α₃-discontinuity. -/
theorem alphaK_14o5_14o5_14o5_isDiscontinuityK :
    IsDiscontinuityK (![(14,5),(14,5),(14,5)] : FracTuple 3) := by
  set v : FracTuple 3 := ![(14,5),(14,5),(14,5)] with hv_def
  have hv_valid : ValidK v := validK_14o5_14o5_14o5
  have hα_v : alphaK v = 14 := alphaK_14o5_14o5_14o5_eq
  intro u hu_valid hu_lt
  by_contra h_not_lt
  push_neg at h_not_lt
  -- h_not_lt : alphaK v ≤ alphaK u, i.e., 14 ≤ alphaK u.
  -- αₖ-monotonicity: alphaK u ≤ alphaK v = 14.
  have hu_le_v : lePermK u v := hu_lt.1
  have hα_u_le : alphaK u ≤ alphaK v := alphaK_le_of_lePermK hu_valid hv_valid hu_le_v
  have hα_u : alphaK u = 14 := by
    rw [hα_v] at hα_u_le h_not_lt; omega
  -- Reduce u to coprime form.
  obtain ⟨u₀, hu₀_valid, hu₀_eq, hu₀_coprime⟩ := exists_coprime_form u hu_valid
  have hα_u₀ : alphaK u₀ = 14 := by
    rw [alphaK_eq_of_toRat_eq hu₀_valid hu_valid hu₀_eq, hα_u]
  -- Apply alphaK_attained_with_bounded_max to u₀.
  obtain ⟨u', hu'_valid, hu'_le_u₀, hu'_alpha, hu'_bound, hu'_coprime⟩ :=
    alphaK_attained_with_bounded_max hu₀_valid hu₀_coprime
  have hα_u' : alphaK u' = 14 := by rw [hu'_alpha, hα_u₀]
  -- Each (u' i).1 ≤ 14.
  have hu'_p_le : ∀ i, ((u' i).1 : ℕ) ≤ 14 := fun i => by
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
  -- Each slot of u' has ratio ≤ 14/5 (max of v).
  obtain ⟨σ_uv, hσ_uv⟩ := hu'_le_v
  have hv_toRat_le_14o5 : ∀ k : Fin 3, FracTuple.toRat v k ≤ (14 : ℚ) / 5 := by
    intro k
    simp only [hv_def, FracTuple.toRat]
    fin_cases k <;> norm_num
  have hu'_ratio_le_14o5 : ∀ i, 5 * ((u' i).1 : ℕ) ≤ 14 * ((u' i).2 : ℕ) := by
    intro i
    have h_sym : σ_uv (σ_uv.symm i) = i := σ_uv.apply_symm_apply i
    have h_le_at_j : FracTuple.toRat u' i ≤ FracTuple.toRat v (σ_uv.symm i) := by
      have h := hσ_uv (σ_uv.symm i); rw [h_sym] at h; exact h
    have h_le : FracTuple.toRat u' i ≤ (14 : ℚ) / 5 :=
      h_le_at_j.trans (hv_toRat_le_14o5 _)
    unfold FracTuple.toRat at h_le
    have hq_pos : (0 : ℚ) < ((u' i).2 : ℚ) := by exact_mod_cast (u' i).2.pos
    rw [div_le_div_iff₀ hq_pos (by norm_num : (0 : ℚ) < 5)] at h_le
    have h_int : (((u' i).1 : ℕ) : ℚ) * 5 ≤ (((u' i).2 : ℕ) : ℚ) * 14 := by linarith
    have h_int_n : ((u' i).1 : ℕ) * 5 ≤ ((u' i).2 : ℕ) * 14 := by exact_mod_cast h_int
    omega
  -- Each slot in allowedPairs.
  have hu'_in_allowed : ∀ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ∈ allowedPairs := by
    intro i
    have h2q : 2 * ((u' i).2 : ℕ) ≤ ((u' i).1 : ℕ) := by exact_mod_cast hu'_valid i
    exact slot_in_allowedPairs _ _ (u' i).1.pos (u' i).2.pos h2q (hu'_p_le i)
      (hu'_ratio_le_14o5 i) (hu'_coprime i)
  -- u' has at least one slot ≠ (14, 5) (else multiset = v, contradicting strict <).
  -- If all slots are (14, 5), then v ≤ₚ u' (via identity), and chained:
  -- v ≤ₚ u' ≤ₚ u₀ ≤ₚ u (the last through toRat equality), giving lePermK v u
  -- which contradicts hu_lt.2.
  have h_some_ne_14o5 : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ≠ (14, 5) := by
    by_contra h_all
    push_neg at h_all
    -- All slots of u' are (14, 5). Then v ≤ₚ u' (via identity).
    have h_all_p : ∀ i, ((u' i).1 : ℕ) = 14 := fun i => (Prod.mk.inj (h_all i)).1
    have h_all_q : ∀ i, ((u' i).2 : ℕ) = 5 := fun i => (Prod.mk.inj (h_all i)).2
    have h_u'_toRat : ∀ i, FracTuple.toRat u' i = 14 / 5 := by
      intro i
      unfold FracTuple.toRat
      have hp : (((u' i).1 : ℕ) : ℚ) = 14 := by exact_mod_cast h_all_p i
      have hq : (((u' i).2 : ℕ) : ℚ) = 5 := by exact_mod_cast h_all_q i
      push_cast at hp hq ⊢
      rw [hp, hq]
    have h_v_toRat : ∀ i, FracTuple.toRat v i = 14 / 5 := by
      intro i
      simp only [hv_def, FracTuple.toRat]
      fin_cases i <;> norm_num
    -- Build v ≤ₚ u (chain v ≤ₚ u' ≤ₚ u₀ ≤ₚ u).
    have h_v_le_u' : lePermK v u' :=
      ⟨1, fun i => by
        simp only [Equiv.Perm.coe_one, id_eq]
        rw [h_v_toRat, h_u'_toRat]⟩
    have h_u'_le_u₀ : lePermK u' u₀ := hu'_le_u₀
    have h_u₀_le_u : lePermK u₀ u :=
      ⟨1, fun i => by simp only [Equiv.Perm.coe_one, id_eq]; exact (hu₀_eq i).le⟩
    have h_v_le_u₀ : lePermK v u₀ := by
      obtain ⟨ρ₁, hρ₁⟩ := h_v_le_u'
      obtain ⟨ρ₂, hρ₂⟩ := h_u'_le_u₀
      refine ⟨ρ₁ * ρ₂, fun i => ?_⟩
      calc FracTuple.toRat v ((ρ₁ * ρ₂) i)
          = FracTuple.toRat v (ρ₁ (ρ₂ i)) := by rw [Equiv.Perm.mul_apply]
        _ ≤ FracTuple.toRat u' (ρ₂ i) := hρ₁ (ρ₂ i)
        _ ≤ FracTuple.toRat u₀ i := hρ₂ i
    have h_v_le_u : lePermK v u := by
      obtain ⟨ρ₁, hρ₁⟩ := h_v_le_u₀
      obtain ⟨ρ₂, hρ₂⟩ := h_u₀_le_u
      refine ⟨ρ₁ * ρ₂, fun i => ?_⟩
      calc FracTuple.toRat v ((ρ₁ * ρ₂) i)
          = FracTuple.toRat v (ρ₁ (ρ₂ i)) := by rw [Equiv.Perm.mul_apply]
        _ ≤ FracTuple.toRat u₀ (ρ₂ i) := hρ₁ (ρ₂ i)
        _ ≤ FracTuple.toRat u i := hρ₂ i
    exact hu_lt.2 h_v_le_u
  -- Pick a slot i₀ with (u' i₀) ≠ (14, 5). Permute to slot 0.
  obtain ⟨i₀, hi₀_ne⟩ := h_some_ne_14o5
  set τ : Equiv.Perm (Fin 3) := Equiv.swap i₀ 0 with hτ_def
  set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
  have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
  have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
  have hu_a_0_p : ((u_a 0).1 : ℕ) = ((u' i₀).1 : ℕ) := by
    change ((u' (τ 0)).1 : ℕ) = ((u' i₀).1 : ℕ)
    rw [hτ_def, Equiv.swap_apply_right]
  have hu_a_0_q : ((u_a 0).2 : ℕ) = ((u' i₀).2 : ℕ) := by
    change ((u' (τ 0)).2 : ℕ) = ((u' i₀).2 : ℕ)
    rw [hτ_def, Equiv.swap_apply_right]
  have hu_a_0_mem : (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) ∈ allowedPairs := by
    rw [hu_a_0_p, hu_a_0_q]; exact hu'_in_allowed i₀
  have hu_a_0_ne : (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) ≠ (14, 5) := by
    rw [hu_a_0_p, hu_a_0_q]; exact hi₀_ne
  have hu_a_1_mem : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
  have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
  -- Bound alphaK u' by nested floor with non-(14,5) at slot 0.
  have h_bound : alphaK u' ≤ nestedFloor3Nat ((u_a 0).1 : ℕ) ((u_a 0).2 : ℕ)
      ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ) ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
    rw [← hα_u_a]
    exact alphaK_le_nestedFloor_with_first hu_a_valid _ _ rfl rfl
  -- The nested-floor value is ≤ 13.
  have h_floor_le_13 :=
    nestedFloor_first_not_14o5_le_13 hu_a_0_mem hu_a_0_ne hu_a_1_mem hu_a_2_mem
  have h_alpha_le_13 : alphaK u' ≤ 13 := h_bound.trans h_floor_le_13
  rw [hα_u'] at h_alpha_le_13
  omega

/-! ## FracTriple-form bridge -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9, FracTriple form.** -/
theorem alpha3_14o5_14o5_14o5_isDiscontinuity :
    IsDiscontinuity (![(14,5),(14,5),(14,5)] : FracTriple) :=
  (isDiscontinuity_iff_isDiscontinuityK ![(14,5),(14,5),(14,5)]).mpr
    alphaK_14o5_14o5_14o5_isDiscontinuityK

end Section6
