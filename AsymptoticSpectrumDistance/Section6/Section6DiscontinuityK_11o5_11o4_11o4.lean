/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# `(11/5, 11/4, 11/4)` is an α₃-discontinuity

Paper Theorem 6.9 case 10. Has `α₃ = 11`.

## Strategy

Let `v := ![(11,5),(11,4),(11,4)]`. We have `alphaK v = alpha3 v = 11`.

For `u` valid with `ltPermK u v`, suppose for contradiction `alphaK u ≥ 11`.
By αₖ-monotonicity, `alphaK u ≤ alphaK v = 11`, so `alphaK u = 11`.

Reduce to a coprime form `u₀` (same `alphaK` since same `toRat`).
Apply `alphaK_attained_with_bounded_max` to get `u'` valid coprime with
`lePermK u' u₀` (so `lePermK u' v` by transitivity), `alphaK u' = 11`, and
`(u' i).1 ≤ 11` for all `i`.

Each slot of `u'` is one of 7 allowed `(p, q)` pairs determined by:
- `2 ≤ p / q ≤ 11/4` (validity + ≤ max of `v`),
- `p ≤ 11` (numerator bound),
- `coprime(p, q)`.

The pairs are: `(2,1), (5,2), (7,3), (8,3), (9,4), (11,4), (11,5)`.

Furthermore, by `lePermK u' v` and `v_sorted = (11/5, 11/4, 11/4)`, the smallest
slot of `u'` has ratio `≤ 11/5`. The only allowed pairs with ratio `≤ 11/5`
are `(2,1)` and `(11,5)`.

We split into 3 cases:

* **Case A**: some slot of `u'` is `(2, 1)`. Permute it to slot 0 (outer in
  the nested floor). Then `nestedFloor3Nat 2 1 p₁ q₁ p₂ q₂ ≤ 10` for any
  `(p₁, q₁), (p₂, q₂) ∈ allowedPairs`.

* **Case B**: no `(2, 1)`, ≥ 2 slots equal `(11, 5)`. Permute two `(11, 5)`s
  to slots 0 and 1. Then `nestedFloor3Nat 11 5 11 5 p₂ q₂ = 8 ≤ 10` for any
  `(p₂, q₂) ∈ allowedPairs`.

* **Case C**: no `(2, 1)`, exactly one `(11, 5)` slot. The other two slots
  have ratio `> 11/5`. By the strict `ltPermK u' v` (multiset `<`), at least
  one of those other two slots has ratio `< 11/4` (else `u' = v` as
  multiset). Permute that strict slot `(a, b) ∈ {(5,2), (7,3), (8,3), (9,4)}`
  to slot 0 and the unique `(11, 5)` to slot 1. Then `nestedFloor3Nat a b 11
  5 p₂ q₂ ≤ 10` for any `(p₂, q₂) ∈ allowedPairs`.

## Main results

* `alphaK_11o5_11o4_11o4_isDiscontinuityK` — K-form disc claim.
* `alpha3_11o5_11o4_11o4_isDiscontinuity` — FracTriple-form disc claim, by
  bridge.
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKAlphaTable
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## The disc point and its `alphaK` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(11,5),(11,4),(11,4)] = 11`. Direct from `alpha3_11o5_11o4_11o4`
    via the K-bridge. -/
theorem alphaK_11o5_11o4_11o4_eq :
    alphaK (![(11,5),(11,4),(11,4)] : FracTuple 3) = 11 := by
  rw [alphaK_three]
  change ((fractionGraph 11 5 ⊠ fractionGraph 11 4) ⊠ fractionGraph 11 4).indepNum = 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_11o5_11o4_11o4

private lemma validK_11o5_11o4_11o4 :
    ValidK (![(11,5),(11,4),(11,4)] : FracTuple 3) := by
  intro i; fin_cases i <;> decide

/-! ## Slot membership in allowed pairs -/

/-- The 7 allowed `(p, q) : ℕ × ℕ` pairs: coprime, lowest terms, `2q ≤ p`,
    `4p ≤ 11q` (ratio ≤ 11/4), and `p ≤ 11`. -/
private def allowedPairs : List (ℕ × ℕ) :=
  [(2, 1), (5, 2), (7, 3), (8, 3), (9, 4), (11, 4), (11, 5)]

/-- Membership in `allowedPairs` from the constraints. -/
private lemma slot_in_allowedPairs (p q : ℕ) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (h_valid : 2 * q ≤ p) (h_p_le : p ≤ 11) (h_ratio_le : 4 * p ≤ 11 * q)
    (h_coprime : Nat.Coprime p q) :
    (p, q) ∈ allowedPairs := by
  -- Brute interval analysis. Since `2q ≤ p ≤ 11`, `q ≤ 5`. And `p ≥ 2`.
  have hq_le_5 : q ≤ 5 := by omega
  have hp_ge_2 : 2 ≤ p := by omega
  unfold allowedPairs
  interval_cases q <;> interval_cases p <;>
    first
    | (exfalso; omega)
    | (exfalso; revert h_coprime; decide)
    | simp

/-! ## Key allowedPairs facts: ratio constraints -/

/-- Every pair in `allowedPairs` has ratio `≤ 11/5` iff it is `(2, 1)` or `(11, 5)`. -/
private lemma allowedPair_ratio_le_11o5_iff {p q : ℕ}
    (h_mem : (p, q) ∈ allowedPairs) :
    5 * p ≤ 11 * q ↔ ((p, q) = (2, 1) ∨ (p, q) = (11, 5)) := by
  unfold allowedPairs at h_mem
  fin_cases h_mem <;> simp

/-! ## Nested-floor bound: case A — `(2, 1)` at slot 0 -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bound: with first slot `(2, 1)` and other two in `allowedPairs`,
    `nestedFloor3Nat 2 1 p₁ q₁ p₂ q₂ ≤ 10`. -/
private lemma nestedFloor_2o1_first_le_10
    {p₁ q₁ p₂ q₂ : ℕ}
    (h₁ : (p₁, q₁) ∈ allowedPairs) (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat 2 1 p₁ q₁ p₂ q₂ ≤ 10 := by
  unfold allowedPairs at h₁ h₂
  unfold nestedFloor3Nat
  fin_cases h₁ <;> fin_cases h₂ <;> decide

/-! ## Nested-floor bound: case B — two `(11, 5)`s at slots 0, 1 -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bound: with first two slots `(11, 5)` and third in `allowedPairs`,
    `nestedFloor3Nat 11 5 11 5 p₂ q₂ = 8 ≤ 10`. -/
private lemma nestedFloor_11o5_11o5_first_le_10
    {p₂ q₂ : ℕ}
    (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat 11 5 11 5 p₂ q₂ ≤ 10 := by
  unfold allowedPairs at h₂
  unfold nestedFloor3Nat
  fin_cases h₂ <;> decide

/-! ## Nested-floor bound: case C — strict-`< 11/4` at slot 0, `(11, 5)` at slot 1 -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bound: with first slot in `allowedPairs` with ratio `< 11/4` (and not
    `(2, 1)`), middle slot `(11, 5)`, third slot in `allowedPairs`,
    `nestedFloor3Nat p₀ q₀ 11 5 p₂ q₂ ≤ 10`. -/
private lemma nestedFloor_strict_lt_11o4_then_11o5_le_10
    {p₀ q₀ p₂ q₂ : ℕ}
    (h₀ : (p₀, q₀) ∈ allowedPairs)
    (h_ne_2o1 : (p₀, q₀) ≠ (2, 1)) (h_ne_11o4 : (p₀, q₀) ≠ (11, 4))
    (h_ne_11o5 : (p₀, q₀) ≠ (11, 5))
    (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat p₀ q₀ 11 5 p₂ q₂ ≤ 10 := by
  unfold allowedPairs at h₀ h₂
  unfold nestedFloor3Nat
  fin_cases h₀ <;> fin_cases h₂ <;>
    first
    | (exfalso; exact h_ne_2o1 rfl)
    | (exfalso; exact h_ne_11o4 rfl)
    | (exfalso; exact h_ne_11o5 rfl)
    | decide

/-! ## Nested-floor bound (parameterized by first-two slot values) -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Nested-floor bound with the first two slot values matched explicitly. -/
private lemma alphaK_le_nestedFloor_with_first_two {u : FracTuple 3}
    (h_valid : ValidK u)
    (p₀ q₀ p₁ q₁ : ℕ)
    (h_p0 : ((u 0).1 : ℕ) = p₀) (h_q0 : ((u 0).2 : ℕ) = q₀)
    (h_p1 : ((u 1).1 : ℕ) = p₁) (h_q1 : ((u 1).2 : ℕ) = q₁) :
    alphaK u ≤ nestedFloor3Nat p₀ q₀ p₁ q₁ ((u 2).1 : ℕ) ((u 2).2 : ℕ) := by
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
              nestedFloor3Nat p₀ q₀ p₁ q₁ ((u 2).1 : ℕ) ((u 2).2 : ℕ) := by
    unfold nestedFloor3Nat; rw [h_p0, h_q0, h_p1, h_q1]
  rw [h_eq] at h
  exact h

/-! ## Main: the disc proof in K-form -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9.** The tuple `(11/5, 11/4, 11/4)`
    is an α₃-discontinuity. -/
theorem alphaK_11o5_11o4_11o4_isDiscontinuityK :
    IsDiscontinuityK (![(11,5),(11,4),(11,4)] : FracTuple 3) := by
  set v : FracTuple 3 := ![(11,5),(11,4),(11,4)] with hv_def
  have hv_valid : ValidK v := validK_11o5_11o4_11o4
  have hα_v : alphaK v = 11 := alphaK_11o5_11o4_11o4_eq
  intro u hu_valid hu_lt
  by_contra h_not_lt
  push_neg at h_not_lt
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
  -- Each slot of u' has ratio ≤ 11/4 (max of v).
  obtain ⟨σ_uv, hσ_uv⟩ := hu'_le_v
  have hv_toRat_le_11o4 : ∀ k : Fin 3, FracTuple.toRat v k ≤ (11 : ℚ) / 4 := by
    intro k
    simp only [hv_def, FracTuple.toRat]
    fin_cases k <;> norm_num
  have hu'_ratio_le_11o4 : ∀ i, 4 * ((u' i).1 : ℕ) ≤ 11 * ((u' i).2 : ℕ) := by
    intro i
    have h_sym : σ_uv (σ_uv.symm i) = i := σ_uv.apply_symm_apply i
    have h_le_at_j : FracTuple.toRat u' i ≤ FracTuple.toRat v (σ_uv.symm i) := by
      have h := hσ_uv (σ_uv.symm i); rw [h_sym] at h; exact h
    have h_le : FracTuple.toRat u' i ≤ (11 : ℚ) / 4 :=
      h_le_at_j.trans (hv_toRat_le_11o4 _)
    unfold FracTuple.toRat at h_le
    have hq_pos : (0 : ℚ) < ((u' i).2 : ℚ) := by exact_mod_cast (u' i).2.pos
    rw [div_le_div_iff₀ hq_pos (by norm_num : (0 : ℚ) < 4)] at h_le
    have h_int : (((u' i).1 : ℕ) : ℚ) * 4 ≤ (((u' i).2 : ℕ) : ℚ) * 11 := by linarith
    have h_int_n : ((u' i).1 : ℕ) * 4 ≤ ((u' i).2 : ℕ) * 11 := by exact_mod_cast h_int
    omega
  -- Each slot in allowedPairs.
  have hu'_in_allowed : ∀ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ∈ allowedPairs := by
    intro i
    have h2q : 2 * ((u' i).2 : ℕ) ≤ ((u' i).1 : ℕ) := by exact_mod_cast hu'_valid i
    exact slot_in_allowedPairs _ _ (u' i).1.pos (u' i).2.pos h2q (hu'_p_le i)
      (hu'_ratio_le_11o4 i) (hu'_coprime i)
  -- ## Key constraint from `lePermK u' v`: smallest slot of u' ≤ 11/5.
  have h_some_le_11o5 : ∃ i, 5 * ((u' i).1 : ℕ) ≤ 11 * ((u' i).2 : ℕ) := by
    refine ⟨σ_uv 0, ?_⟩
    have h := hσ_uv 0
    have hv0 : FracTuple.toRat v 0 = (11 : ℚ) / 5 := by
      simp only [hv_def, FracTuple.toRat]
      norm_num
    rw [hv0] at h
    unfold FracTuple.toRat at h
    have hq_pos : (0 : ℚ) < (((u' (σ_uv 0)).2 : ℕ) : ℚ) := by
      exact_mod_cast (u' (σ_uv 0)).2.pos
    rw [div_le_div_iff₀ hq_pos (by norm_num : (0 : ℚ) < 5)] at h
    have h_int : (((u' (σ_uv 0)).1 : ℕ) : ℚ) * 5 ≤ (((u' (σ_uv 0)).2 : ℕ) : ℚ) * 11 := by
      linarith
    have h_int_n : ((u' (σ_uv 0)).1 : ℕ) * 5 ≤ ((u' (σ_uv 0)).2 : ℕ) * 11 := by
      exact_mod_cast h_int
    omega
  -- Convert `5 p ≤ 11 q` constraint to "(p,q) is (2,1) or (11,5)":
  have h_some_2o1_or_11o5 : ∃ i,
      (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (2, 1) ∨
      (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (11, 5) := by
    obtain ⟨i, h_le⟩ := h_some_le_11o5
    refine ⟨i, ?_⟩
    rw [← allowedPair_ratio_le_11o5_iff (hu'_in_allowed i)]
    exact h_le
  -- # Case split.
  by_cases h_caseA : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (2, 1)
  · -- ## Case A: some slot is (2, 1). Permute to slot 0.
    obtain ⟨i₀, hi₀⟩ := h_caseA
    have hi₀_p : ((u' i₀).1 : ℕ) = 2 := (Prod.mk.inj hi₀).1
    have hi₀_q : ((u' i₀).2 : ℕ) = 1 := (Prod.mk.inj hi₀).2
    set τ : Equiv.Perm (Fin 3) := Equiv.swap i₀ 0 with hτ_def
    set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
    have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
    have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
    have hu_a_0_p : ((u_a 0).1 : ℕ) = 2 := by
      change ((u' (τ 0)).1 : ℕ) = 2
      rw [hτ_def, Equiv.swap_apply_right]; exact hi₀_p
    have hu_a_0_q : ((u_a 0).2 : ℕ) = 1 := by
      change ((u' (τ 0)).2 : ℕ) = 1
      rw [hτ_def, Equiv.swap_apply_right]; exact hi₀_q
    have hu_a_1_mem : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
    have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
    have h_bound : alphaK u' ≤ nestedFloor3Nat 2 1 ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ)
        ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
      rw [← hα_u_a]
      exact alphaK_le_nestedFloor_with_first_two hu_a_valid 2 1 ((u_a 1).1 : ℕ)
        ((u_a 1).2 : ℕ) hu_a_0_p hu_a_0_q rfl rfl
    have h_floor_le_10 := nestedFloor_2o1_first_le_10 hu_a_1_mem hu_a_2_mem
    have h_alpha_le_10 : alphaK u' ≤ 10 := h_bound.trans h_floor_le_10
    rw [hα_u'] at h_alpha_le_10
    omega
  · -- No slot is (2, 1). So h_some_2o1_or_11o5 yields some slot is (11, 5).
    push_neg at h_caseA
    have h_some_11o5 : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (11, 5) := by
      obtain ⟨i, h_or⟩ := h_some_2o1_or_11o5
      rcases h_or with h_2o1 | h_11o5
      · exact absurd h_2o1 (h_caseA i)
      · exact ⟨i, h_11o5⟩
    by_cases h_caseB : ∃ i j : Fin 3, i ≠ j ∧
        (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (11, 5) ∧
        (((u' j).1 : ℕ), ((u' j).2 : ℕ)) = (11, 5)
    · -- ## Case B: ≥ 2 slots are (11, 5). Permute two of them to slots 0, 1.
      obtain ⟨i₀, i₁, hij_ne, hi₀, hi₁⟩ := h_caseB
      have hi₀_p : ((u' i₀).1 : ℕ) = 11 := (Prod.mk.inj hi₀).1
      have hi₀_q : ((u' i₀).2 : ℕ) = 5 := (Prod.mk.inj hi₀).2
      have hi₁_p : ((u' i₁).1 : ℕ) = 11 := (Prod.mk.inj hi₁).1
      have hi₁_q : ((u' i₁).2 : ℕ) = 5 := (Prod.mk.inj hi₁).2
      set τ_a : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) i₀
      set i₁' : Fin 3 := τ_a.symm i₁ with hi₁'_def
      have hi₁'_ne_0 : i₁' ≠ 0 := by
        intro h
        have : τ_a i₁' = τ_a 0 := by rw [h]
        rw [Equiv.apply_symm_apply, Equiv.swap_apply_left] at this
        exact hij_ne (this.trans rfl).symm
      set τ_b : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) i₁'
      set τ : Equiv.Perm (Fin 3) := τ_a * τ_b with hτ_def
      have hτ_0 : τ 0 = i₀ := by
        change τ_a (τ_b 0) = i₀
        rw [show τ_b 0 = (0 : Fin 3) from
          Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1)
            (fun h => hi₁'_ne_0 h.symm)]
        exact Equiv.swap_apply_left _ _
      have hτ_1 : τ 1 = i₁ := by
        change τ_a (τ_b 1) = i₁
        rw [show τ_b 1 = i₁' from Equiv.swap_apply_left _ _]
        exact Equiv.apply_symm_apply _ _
      set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
      have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
      have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
      have hu_a_0_p : ((u_a 0).1 : ℕ) = 11 := by
        change ((u' (τ 0)).1 : ℕ) = 11; rw [hτ_0]; exact hi₀_p
      have hu_a_0_q : ((u_a 0).2 : ℕ) = 5 := by
        change ((u' (τ 0)).2 : ℕ) = 5; rw [hτ_0]; exact hi₀_q
      have hu_a_1_p : ((u_a 1).1 : ℕ) = 11 := by
        change ((u' (τ 1)).1 : ℕ) = 11; rw [hτ_1]; exact hi₁_p
      have hu_a_1_q : ((u_a 1).2 : ℕ) = 5 := by
        change ((u' (τ 1)).2 : ℕ) = 5; rw [hτ_1]; exact hi₁_q
      have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
      have h_bound : alphaK u' ≤ nestedFloor3Nat 11 5 11 5 ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
        rw [← hα_u_a]
        exact alphaK_le_nestedFloor_with_first_two hu_a_valid 11 5 11 5
          hu_a_0_p hu_a_0_q hu_a_1_p hu_a_1_q
      have h_floor_le_10 := nestedFloor_11o5_11o5_first_le_10 hu_a_2_mem
      have h_alpha_le_10 : alphaK u' ≤ 10 := h_bound.trans h_floor_le_10
      rw [hα_u'] at h_alpha_le_10
      omega
    · -- ## Case C: no (2, 1), exactly one (11, 5). Need a strict-`<11/4` slot.
      push_neg at h_caseB
      obtain ⟨i_115, hi_115⟩ := h_some_11o5
      have h_only_i_115 : ∀ j, (((u' j).1 : ℕ), ((u' j).2 : ℕ)) = (11, 5) → j = i_115 := by
        intro j hj
        by_contra h_ne
        exact h_caseB j i_115 h_ne hj hi_115
      have h_some_strict : ∃ j, j ≠ i_115 ∧
          (((u' j).1 : ℕ), ((u' j).2 : ℕ)) ≠ (11, 4) := by
        by_contra h_all
        push_neg at h_all
        have h_other_slots : ∀ j, j ≠ i_115 →
            (((u' j).1 : ℕ), ((u' j).2 : ℕ)) = (11, 4) := h_all
        -- All other slots are (11, 4); i_115 is (11, 5). u' has multiset = v's.
        -- Build v ≤ₚ u (chain v ≤ₚ u' ≤ₚ u₀ ≤ₚ u), contradicting hu_lt.2.
        have hu'_i_115_rat : FracTuple.toRat u' i_115 = 11 / 5 := by
          unfold FracTuple.toRat
          have hp : (((u' i_115).1 : ℕ) : ℚ) = 11 := by
            exact_mod_cast (Prod.mk.inj hi_115).1
          have hq : (((u' i_115).2 : ℕ) : ℚ) = 5 := by
            exact_mod_cast (Prod.mk.inj hi_115).2
          push_cast at hp hq ⊢
          rw [hp, hq]
        have hu'_other_rat : ∀ j, j ≠ i_115 → FracTuple.toRat u' j = 11 / 4 := by
          intro j hj_ne
          have h_eq := h_other_slots j hj_ne
          unfold FracTuple.toRat
          have hp : (((u' j).1 : ℕ) : ℚ) = 11 := by
            exact_mod_cast (Prod.mk.inj h_eq).1
          have hq : (((u' j).2 : ℕ) : ℚ) = 4 := by
            exact_mod_cast (Prod.mk.inj h_eq).2
          push_cast at hp hq ⊢
          rw [hp, hq]
        have hv_0_rat : FracTuple.toRat v 0 = 11 / 5 := by
          simp [hv_def, FracTuple.toRat]
        have hv_1_rat : FracTuple.toRat v 1 = 11 / 4 := by
          simp [hv_def, FracTuple.toRat]
        have hv_2_rat : FracTuple.toRat v 2 = 11 / 4 := by
          simp [hv_def, FracTuple.toRat]
        have h_v_le_u' : lePermK v u' := by
          refine ⟨Equiv.swap (0 : Fin 3) i_115, fun i => ?_⟩
          fin_cases i
          · -- i = 0. Goal: v.toRat (swap 0 i_115 0) ≤ u'.toRat 0.
            change FracTuple.toRat v (Equiv.swap (0:Fin 3) i_115 0) ≤ FracTuple.toRat u' 0
            rw [Equiv.swap_apply_left]
            by_cases h0 : i_115 = 0
            · rw [h0, hv_0_rat]; rw [h0] at hu'_i_115_rat; rw [hu'_i_115_rat]
            · have h_v_i_115 : FracTuple.toRat v i_115 = 11 / 4 := by
                fin_cases i_115
                · exact absurd rfl h0
                · exact hv_1_rat
                · exact hv_2_rat
              rw [h_v_i_115]
              rw [hu'_other_rat 0 (fun h => h0 h.symm)]
          · -- i = 1.
            change FracTuple.toRat v (Equiv.swap (0:Fin 3) i_115 1) ≤ FracTuple.toRat u' 1
            by_cases h1 : i_115 = 1
            · rw [show Equiv.swap (0:Fin 3) i_115 1 = 0 from by
                rw [h1]; exact Equiv.swap_apply_right _ _]
              rw [hv_0_rat]; rw [h1] at hu'_i_115_rat; rw [hu'_i_115_rat]
            · rw [show Equiv.swap (0:Fin 3) i_115 1 = 1 from
                Equiv.swap_apply_of_ne_of_ne (by decide : (1:Fin 3) ≠ 0)
                  (fun h => h1 h.symm)]
              rw [hv_1_rat]
              rw [hu'_other_rat 1 (fun h => h1 h.symm)]
          · -- i = 2.
            change FracTuple.toRat v (Equiv.swap (0:Fin 3) i_115 2) ≤ FracTuple.toRat u' 2
            by_cases h2 : i_115 = 2
            · rw [show Equiv.swap (0:Fin 3) i_115 2 = 0 from by
                rw [h2]; exact Equiv.swap_apply_right _ _]
              rw [hv_0_rat]; rw [h2] at hu'_i_115_rat; rw [hu'_i_115_rat]
            · rw [show Equiv.swap (0:Fin 3) i_115 2 = 2 from
                Equiv.swap_apply_of_ne_of_ne (by decide : (2:Fin 3) ≠ 0)
                  (fun h => h2 h.symm)]
              rw [hv_2_rat]
              rw [hu'_other_rat 2 (fun h => h2 h.symm)]
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
      obtain ⟨j_strict, hj_strict_ne, hj_strict_ne_11o4⟩ := h_some_strict
      have hj_strict_mem := hu'_in_allowed j_strict
      have hj_strict_ne_2o1 : (((u' j_strict).1 : ℕ), ((u' j_strict).2 : ℕ)) ≠ (2, 1) :=
        h_caseA j_strict
      have hj_strict_ne_11o5 : (((u' j_strict).1 : ℕ), ((u' j_strict).2 : ℕ)) ≠ (11, 5) := by
        intro h
        exact hj_strict_ne (h_only_i_115 j_strict h)
      set τ_a : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) j_strict
      set i_115' : Fin 3 := τ_a.symm i_115 with hi_115'_def
      have hi_115'_ne_0 : i_115' ≠ 0 := by
        intro h
        have : τ_a i_115' = τ_a 0 := by rw [h]
        rw [Equiv.apply_symm_apply, Equiv.swap_apply_left] at this
        exact hj_strict_ne (this.symm.trans rfl)
      set τ_b : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) i_115'
      set τ : Equiv.Perm (Fin 3) := τ_a * τ_b with hτ_def
      have hτ_0 : τ 0 = j_strict := by
        change τ_a (τ_b 0) = j_strict
        rw [show τ_b 0 = (0 : Fin 3) from
          Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1)
            (fun h => hi_115'_ne_0 h.symm)]
        exact Equiv.swap_apply_left _ _
      have hτ_1 : τ 1 = i_115 := by
        change τ_a (τ_b 1) = i_115
        rw [show τ_b 1 = i_115' from Equiv.swap_apply_left _ _]
        exact Equiv.apply_symm_apply _ _
      set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
      have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
      have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
      have hu_a_0_p : ((u_a 0).1 : ℕ) = ((u' j_strict).1 : ℕ) := by
        change ((u' (τ 0)).1 : ℕ) = _; rw [hτ_0]
      have hu_a_0_q : ((u_a 0).2 : ℕ) = ((u' j_strict).2 : ℕ) := by
        change ((u' (τ 0)).2 : ℕ) = _; rw [hτ_0]
      have hu_a_1_p : ((u_a 1).1 : ℕ) = 11 := by
        change ((u' (τ 1)).1 : ℕ) = 11; rw [hτ_1]; exact (Prod.mk.inj hi_115).1
      have hu_a_1_q : ((u_a 1).2 : ℕ) = 5 := by
        change ((u' (τ 1)).2 : ℕ) = 5; rw [hτ_1]; exact (Prod.mk.inj hi_115).2
      have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
      have h_bound : alphaK u' ≤ nestedFloor3Nat ((u_a 0).1 : ℕ) ((u_a 0).2 : ℕ)
          11 5 ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
        rw [← hα_u_a]
        exact alphaK_le_nestedFloor_with_first_two hu_a_valid _ _ 11 5 rfl rfl
          hu_a_1_p hu_a_1_q
      have hu_a_0_mem : (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) ∈ allowedPairs := by
        rw [hu_a_0_p, hu_a_0_q]; exact hj_strict_mem
      have hu_a_0_ne_2o1 : (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) ≠ (2, 1) := by
        rw [hu_a_0_p, hu_a_0_q]; exact hj_strict_ne_2o1
      have hu_a_0_ne_11o4 : (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) ≠ (11, 4) := by
        rw [hu_a_0_p, hu_a_0_q]; exact hj_strict_ne_11o4
      have hu_a_0_ne_11o5 : (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) ≠ (11, 5) := by
        rw [hu_a_0_p, hu_a_0_q]; exact hj_strict_ne_11o5
      have h_floor_le_10 := nestedFloor_strict_lt_11o4_then_11o5_le_10
        hu_a_0_mem hu_a_0_ne_2o1 hu_a_0_ne_11o4 hu_a_0_ne_11o5 hu_a_2_mem
      have h_alpha_le_10 : alphaK u' ≤ 10 := h_bound.trans h_floor_le_10
      rw [hα_u'] at h_alpha_le_10
      omega

/-! ## FracTriple-form bridge -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9, FracTriple form.** -/
theorem alpha3_11o5_11o4_11o4_isDiscontinuity :
    IsDiscontinuity (![(11,5),(11,4),(11,4)] : FracTriple) :=
  (isDiscontinuity_iff_isDiscontinuityK ![(11,5),(11,4),(11,4)]).mpr
    alphaK_11o5_11o4_11o4_isDiscontinuityK

end Section6
