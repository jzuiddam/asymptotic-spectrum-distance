/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# `(9/4, 7/3, 5/2)` is an α₃-discontinuity

Paper Theorem 6.9 case 9. Has `α₃ = 9` (from `alpha3_9o4_7o3_5o2`).

## Strategy

Let `v := ![(9,4),(7,3),(5,2)]`. We have `alphaK v = alpha3 v = 9`.

For `u` valid with `ltPermK u v`, suppose for contradiction `alphaK u ≥ 9`.
By αₖ-monotonicity, `alphaK u ≤ alphaK v = 9`, so `alphaK u = 9`.

Reduce to a coprime form `u₀` (same `alphaK` since same `toRat`). Apply
`alphaK_attained_with_bounded_max` to get `u'` valid coprime with
`lePermK u' u₀` (so `lePermK u' v` by transitivity), `alphaK u' = 9`, and
`(u' i).1 ≤ 9` for all `i`.

Each slot of `u'` is one of 4 allowed `(p, q)` pairs determined by:
- `2 ≤ p / q ≤ 5/2` (validity + ≤ max of `v`),
- `p ≤ 9` (numerator bound),
- `coprime(p, q)`.

The pairs are: `(2,1), (5,2), (7,3), (9,4)`.

We split into 2 main cases:

* **Case A**: no slot of `u'` is `(5, 2)`. Then every slot has ratio strictly
  `< 5/2`. By `alpha3_le_8_of_lt_5o2`, `alphaK u' ≤ 8 < 9`. Contradiction.

* **Case B**: some slot of `u'` is `(5, 2)`. The constraint `lePermK u' v`
  forces the smallest sorted slot to have ratio `≤ 9/4`, i.e., u' has at
  least one slot in `{(2,1), (9,4)}`. Sub-split:

  - **Case B1**: some slot is `(2, 1)`. Permute `(2, 1)` to slot 0 and a
    `(5, 2)` to slot 2. The middle slot (slot 1) is in `allowedPairs`. By
    the multiset constraint at most one slot is `(5, 2)`, so the middle
    slot is not `(5, 2)`. Then `nestedFloor3Nat 2 1 p₁ q₁ 5 2 ≤ 8` for any
    `(p₁, q₁) ∈ allowedPairs ∖ {(5, 2)}`. Contradiction.

  - **Case B2**: no slot is `(2, 1)`, some slot is `(5, 2)`. From "smallest
    slot ≤ 9/4" we get a `(9, 4)` slot. The "second-largest sorted ≤ 7/3"
    constraint forbids `(7, 3)` together with `(5, 2)`, so the third slot
    is in `{(5, 2), (9, 4)}`. The strict `<ₚ v` excludes the case
    `(5, 2)(7, 3)(9, 4) = v`; "at most one (5, 2)" excludes
    `(5, 2)(5, 2)(9, 4)`. So the multiset is exactly `(5, 2)(9, 4)(9, 4)`.
    Apply `alpha3_9o4_9o4_5o2_le ≤ 8`. Contradiction.

## Main results

* `alphaK_9o4_7o3_5o2_isDiscontinuityK` — K-form disc claim.
* `alpha3_9o4_7o3_5o2_isDiscontinuity` — FracTriple-form disc claim, by bridge.
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKAlphaTable
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## The disc point and its `alphaK` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(9,4),(7,3),(5,2)] = 9`. Direct from `alpha3_9o4_7o3_5o2` via
    the K-bridge. -/
theorem alphaK_9o4_7o3_5o2_eq :
    alphaK (![(9,4),(7,3),(5,2)] : FracTuple 3) = 9 := by
  rw [alphaK_three]
  change ((fractionGraph 9 4 ⊠ fractionGraph 7 3) ⊠ fractionGraph 5 2).indepNum = 9
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_9o4_7o3_5o2

private lemma validK_9o4_7o3_5o2 :
    ValidK (![(9,4),(7,3),(5,2)] : FracTuple 3) := by
  intro i; fin_cases i <;> decide

/-! ## Slot membership in allowed pairs -/

/-- The 4 allowed `(p, q) : ℕ × ℕ` pairs: coprime, lowest terms,
    `2q ≤ p ≤ 5q/2`, and `p ≤ 9`. -/
private def allowedPairs : List (ℕ × ℕ) :=
  [(2, 1), (5, 2), (7, 3), (9, 4)]

/-- Membership in `allowedPairs` from the constraints. -/
private lemma slot_in_allowedPairs (p q : ℕ) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (h_valid : 2 * q ≤ p) (h_p_le : p ≤ 9) (h_ratio_le : 2 * p ≤ 5 * q)
    (h_coprime : Nat.Coprime p q) :
    (p, q) ∈ allowedPairs := by
  have hq_le_4 : q ≤ 4 := by omega
  have hp_ge_2 : 2 ≤ p := by omega
  unfold allowedPairs
  interval_cases q <;> interval_cases p <;>
    first
    | (exfalso; omega)
    | (exfalso; revert h_coprime; decide)
    | simp

/-- A pair in `allowedPairs` either equals `(5, 2)` or has `2 p < 5 q`
    (i.e., ratio strictly `< 5/2`). -/
private lemma allowedPair_strict_or_5o2 {p q : ℕ}
    (h_mem : (p, q) ∈ allowedPairs) :
    (p, q) = (5, 2) ∨ 2 * p < 5 * q := by
  unfold allowedPairs at h_mem
  fin_cases h_mem <;> first | (left; rfl) | (right; omega)

/-- A pair in `allowedPairs` has ratio `≤ 9/4` iff it is `(2, 1)` or `(9, 4)`. -/
private lemma allowedPair_ratio_le_9o4_iff {p q : ℕ}
    (h_mem : (p, q) ∈ allowedPairs) :
    4 * p ≤ 9 * q ↔ ((p, q) = (2, 1) ∨ (p, q) = (9, 4)) := by
  unfold allowedPairs at h_mem
  fin_cases h_mem <;> simp

/-! ## Case A: all slots ratio `< 5/2` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- If a `FracTuple 3` is valid and each slot has `2 (u i).1 < 5 (u i).2`,
    then `alphaK u ≤ 8`. -/
private lemma alphaK_le_8_of_all_lt_5o2 {u : FracTuple 3}
    (h_valid : ValidK u)
    (h_strict : ∀ i, 2 * ((u i).1 : ℕ) < 5 * ((u i).2 : ℕ)) :
    alphaK u ≤ 8 := by
  rw [alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  haveI : NeZero ((u 0).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 0).1.pos⟩
  haveI : NeZero ((u 1).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 1).1.pos⟩
  haveI : NeZero ((u 2).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 2).1.pos⟩
  have h2q : ∀ i, 2 * ((u i).2 : ℕ) ≤ ((u i).1 : ℕ) := fun i => by exact_mod_cast h_valid i
  have hq_pos : ∀ i, 0 < ((u i).2 : ℕ) := fun i => (u i).2.pos
  exact alpha3_le_8_of_lt_5o2 _ _ _ _ _ _
    (hq_pos 0) (h2q 0) (h_strict 0)
    (hq_pos 1) (h2q 1) (h_strict 1)
    (hq_pos 2) (h2q 2) (h_strict 2)

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

/-! ## Case B1 nested-floor bound: `(2, 1)` at slot 0, `(5, 2)` at slot 2,
        middle slot in `allowedPairs` and not `(5, 2)`. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For `(p₁, q₁) ∈ allowedPairs` with `(p₁, q₁) ≠ (5, 2)`,
    `nestedFloor3Nat 2 1 p₁ q₁ 5 2 ≤ 8`. -/
private lemma nestedFloor_2o1_mid_5o2_le_8
    {p₁ q₁ : ℕ}
    (h₁ : (p₁, q₁) ∈ allowedPairs) (h_ne_5o2 : (p₁, q₁) ≠ (5, 2)) :
    nestedFloor3Nat 2 1 p₁ q₁ 5 2 ≤ 8 := by
  unfold allowedPairs at h₁
  unfold nestedFloor3Nat
  fin_cases h₁ <;>
    first
    | (exfalso; exact h_ne_5o2 rfl)
    | decide

/-! ## Case B2 bridge: multiset `(5,2)(9,4)(9,4)` ⇒ `alphaK ≤ 8` via Baumert. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a 0 = (9, 4)`, `u_a 1 = (9, 4)`, `u_a 2 = (5, 2)`, then
    `alphaK u_a ≤ 8`. Uses `alpha3_9o4_9o4_5o2_le`. -/
private lemma alphaK_le_8_of_9o4_9o4_5o2 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 9) (h0q : ((u_a 0).2 : ℕ) = 4)
    (h1p : ((u_a 1).1 : ℕ) = 9) (h1q : ((u_a 1).2 : ℕ) = 4)
    (h2p : ((u_a 2).1 : ℕ) = 5) (h2q : ((u_a 2).2 : ℕ) = 2) :
    alphaK u_a ≤ 8 := by
  set w : FracTuple 3 := ![(9,4),(9,4),(5,2)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 9 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h0q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 1).1 : ℚ) / ((u_a 1).2 : ℚ) = ((w 1).1 : ℚ) / ((w 1).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 1).1 : ℕ) : ℚ) = 9 := by exact_mod_cast h1p
      have hq : (((u_a 1).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h1q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 2).1 : ℚ) / ((u_a 2).2 : ℚ) = ((w 2).1 : ℚ) / ((w 2).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 2).1 : ℕ) : ℚ) = 5 := by exact_mod_cast h2p
      have hq : (((u_a 2).2 : ℕ) : ℚ) = 2 := by exact_mod_cast h2q
      push_cast at hp hq ⊢
      rw [hp, hq]
  have hα_eq : alphaK u_a = alphaK w :=
    alphaK_eq_of_toRat_eq h_valid hw_valid h_toRat_eq
  rw [hα_eq, alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_9o4_9o4_5o2_le

/-! ## Main: the disc proof in K-form -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9.** The tuple `(9/4, 7/3, 5/2)` is
    an α₃-discontinuity. -/
theorem alphaK_9o4_7o3_5o2_isDiscontinuityK :
    IsDiscontinuityK (![(9,4),(7,3),(5,2)] : FracTuple 3) := by
  set v : FracTuple 3 := ![(9,4),(7,3),(5,2)] with hv_def
  have hv_valid : ValidK v := validK_9o4_7o3_5o2
  have hα_v : alphaK v = 9 := alphaK_9o4_7o3_5o2_eq
  intro u hu_valid hu_lt
  by_contra h_not_lt
  push_neg at h_not_lt
  -- αₖ-monotonicity: alphaK u ≤ alphaK v = 9.
  have hu_le_v : lePermK u v := hu_lt.1
  have hα_u_le : alphaK u ≤ alphaK v := alphaK_le_of_lePermK hu_valid hv_valid hu_le_v
  have hα_u : alphaK u = 9 := by
    rw [hα_v] at hα_u_le h_not_lt; omega
  -- Reduce u to coprime form.
  obtain ⟨u₀, hu₀_valid, hu₀_eq, hu₀_coprime⟩ := exists_coprime_form u hu_valid
  have hα_u₀ : alphaK u₀ = 9 := by
    rw [alphaK_eq_of_toRat_eq hu₀_valid hu_valid hu₀_eq, hα_u]
  -- Apply alphaK_attained_with_bounded_max to u₀.
  obtain ⟨u', hu'_valid, hu'_le_u₀, hu'_alpha, hu'_bound, hu'_coprime⟩ :=
    alphaK_attained_with_bounded_max hu₀_valid hu₀_coprime
  have hα_u' : alphaK u' = 9 := by rw [hu'_alpha, hα_u₀]
  -- Each (u' i).1 ≤ 9.
  have hu'_p_le : ∀ i, ((u' i).1 : ℕ) ≤ 9 := fun i => by
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
  -- Each slot of u' has ratio ≤ 5/2 (max of v).
  obtain ⟨σ_uv, hσ_uv⟩ := hu'_le_v
  have hv_toRat_le_5o2 : ∀ k : Fin 3, FracTuple.toRat v k ≤ (5 : ℚ) / 2 := by
    intro k
    simp only [hv_def, FracTuple.toRat]
    fin_cases k <;> norm_num
  have hu'_ratio_le_5o2 : ∀ i, 2 * ((u' i).1 : ℕ) ≤ 5 * ((u' i).2 : ℕ) := by
    intro i
    have h_sym : σ_uv (σ_uv.symm i) = i := σ_uv.apply_symm_apply i
    have h_le_at_j : FracTuple.toRat u' i ≤ FracTuple.toRat v (σ_uv.symm i) := by
      have h := hσ_uv (σ_uv.symm i); rw [h_sym] at h; exact h
    have h_le : FracTuple.toRat u' i ≤ (5 : ℚ) / 2 :=
      h_le_at_j.trans (hv_toRat_le_5o2 _)
    unfold FracTuple.toRat at h_le
    have hq_pos : (0 : ℚ) < ((u' i).2 : ℚ) := by exact_mod_cast (u' i).2.pos
    rw [div_le_div_iff₀ hq_pos (by norm_num : (0 : ℚ) < 2)] at h_le
    have h_int : (((u' i).1 : ℕ) : ℚ) * 2 ≤ (((u' i).2 : ℕ) : ℚ) * 5 := by linarith
    have h_int_n : ((u' i).1 : ℕ) * 2 ≤ ((u' i).2 : ℕ) * 5 := by exact_mod_cast h_int
    omega
  -- Each slot in allowedPairs.
  have hu'_in_allowed : ∀ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ∈ allowedPairs := by
    intro i
    have h2q : 2 * ((u' i).2 : ℕ) ≤ ((u' i).1 : ℕ) := by exact_mod_cast hu'_valid i
    exact slot_in_allowedPairs _ _ (u' i).1.pos (u' i).2.pos h2q (hu'_p_le i)
      (hu'_ratio_le_5o2 i) (hu'_coprime i)
  -- # Case A: no slot of u' is (5, 2). Then all slots have ratio strictly < 5/2.
  by_cases h_caseA : ∀ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ≠ (5, 2)
  · -- Case A: all slots have ratio < 5/2.
    have hu'_strict : ∀ i, 2 * ((u' i).1 : ℕ) < 5 * ((u' i).2 : ℕ) := by
      intro i
      rcases allowedPair_strict_or_5o2 (hu'_in_allowed i) with h_5o2 | h_strict
      · exfalso; exact h_caseA i h_5o2
      · exact h_strict
    have h_alpha_le_8 : alphaK u' ≤ 8 := alphaK_le_8_of_all_lt_5o2 hu'_valid hu'_strict
    rw [hα_u'] at h_alpha_le_8
    omega
  · -- # Case B: some slot of u' is (5, 2).
    push_neg at h_caseA
    obtain ⟨i_52, hi_52⟩ := h_caseA
    have hi_52_p : ((u' i_52).1 : ℕ) = 5 := (Prod.mk.inj hi_52).1
    have hi_52_q : ((u' i_52).2 : ℕ) = 2 := (Prod.mk.inj hi_52).2
    -- "smallest sorted ≤ 9/4" constraint: some slot has ratio ≤ 9/4.
    have h_some_le_9o4 : ∃ i, 4 * ((u' i).1 : ℕ) ≤ 9 * ((u' i).2 : ℕ) := by
      refine ⟨σ_uv 0, ?_⟩
      have h := hσ_uv 0
      have hv0 : FracTuple.toRat v 0 = (9 : ℚ) / 4 := by
        simp only [hv_def, FracTuple.toRat]
        norm_num
      rw [hv0] at h
      unfold FracTuple.toRat at h
      have hq_pos : (0 : ℚ) < (((u' (σ_uv 0)).2 : ℕ) : ℚ) := by
        exact_mod_cast (u' (σ_uv 0)).2.pos
      rw [div_le_div_iff₀ hq_pos (by norm_num : (0 : ℚ) < 4)] at h
      have h_int : (((u' (σ_uv 0)).1 : ℕ) : ℚ) * 4 ≤ (((u' (σ_uv 0)).2 : ℕ) : ℚ) * 9 := by
        linarith
      have h_int_n : ((u' (σ_uv 0)).1 : ℕ) * 4 ≤ ((u' (σ_uv 0)).2 : ℕ) * 9 := by
        exact_mod_cast h_int
      omega
    have h_some_2o1_or_9o4 : ∃ i,
        (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (2, 1) ∨
        (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (9, 4) := by
      obtain ⟨i, h_le⟩ := h_some_le_9o4
      refine ⟨i, ?_⟩
      rw [← allowedPair_ratio_le_9o4_iff (hu'_in_allowed i)]
      exact h_le
    -- "second-largest sorted ≤ 7/3": at most one slot has ratio > 7/3.
    have h_at_most_one_5o2 : ∀ i j, i ≠ j →
        (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (5, 2) →
        (((u' j).1 : ℕ), ((u' j).2 : ℕ)) ≠ (5, 2) := by
      intro i j hij hi hj
      -- u'(i) and u'(j) both have ratio 5/2 > 7/3.
      have hi_rat : FracTuple.toRat u' i = 5 / 2 := by
        unfold FracTuple.toRat
        have hp : (((u' i).1 : ℕ) : ℚ) = 5 := by exact_mod_cast (Prod.mk.inj hi).1
        have hq : (((u' i).2 : ℕ) : ℚ) = 2 := by exact_mod_cast (Prod.mk.inj hi).2
        push_cast at hp hq ⊢
        rw [hp, hq]
      have hj_rat : FracTuple.toRat u' j = 5 / 2 := by
        unfold FracTuple.toRat
        have hp : (((u' j).1 : ℕ) : ℚ) = 5 := by exact_mod_cast (Prod.mk.inj hj).1
        have hq : (((u' j).2 : ℕ) : ℚ) = 2 := by exact_mod_cast (Prod.mk.inj hj).2
        push_cast at hp hq ⊢
        rw [hp, hq]
      -- Their preimages under σ_uv are distinct slots in v with toRat ≥ 5/2.
      -- Among v's slots, only slot 2 has toRat = 5/2 (slots 0,1 have 9/4, 7/3 < 5/2).
      have hi_pre : FracTuple.toRat v (σ_uv.symm i) ≥ 5 / 2 := by
        have h := hσ_uv (σ_uv.symm i)
        rw [σ_uv.apply_symm_apply] at h
        rw [hi_rat] at h; exact h
      have hj_pre : FracTuple.toRat v (σ_uv.symm j) ≥ 5 / 2 := by
        have h := hσ_uv (σ_uv.symm j)
        rw [σ_uv.apply_symm_apply] at h
        rw [hj_rat] at h; exact h
      have hv_lt_5o2 : ∀ k : Fin 3, k ≠ 2 → FracTuple.toRat v k < 5 / 2 := by
        intro k hk
        simp only [hv_def, FracTuple.toRat]
        fin_cases k
        · norm_num
        · norm_num
        · exact absurd rfl hk
      have h_i_pre_eq_2 : σ_uv.symm i = 2 := by
        by_contra hne
        exact absurd (hv_lt_5o2 _ hne) (not_lt_of_ge hi_pre)
      have h_j_pre_eq_2 : σ_uv.symm j = 2 := by
        by_contra hne
        exact absurd (hv_lt_5o2 _ hne) (not_lt_of_ge hj_pre)
      have hij' : σ_uv.symm i = σ_uv.symm j := h_i_pre_eq_2.trans h_j_pre_eq_2.symm
      exact hij (σ_uv.symm.injective hij')
    -- Sub-split: Case B1 (some (2, 1) slot) vs B2.
    by_cases h_caseB1 : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (2, 1)
    · -- ## Case B1: some slot is (2, 1). Permute (2,1) → 0, (5,2) → 2.
      obtain ⟨i_21, hi_21⟩ := h_caseB1
      have hi_21_p : ((u' i_21).1 : ℕ) = 2 := (Prod.mk.inj hi_21).1
      have hi_21_q : ((u' i_21).2 : ℕ) = 1 := (Prod.mk.inj hi_21).2
      -- i_21 ≠ i_52 (different slot values).
      have hi_21_ne_52 : i_21 ≠ i_52 := by
        intro h
        rw [h] at hi_21_p; rw [hi_52_p] at hi_21_p
        exact absurd hi_21_p (by decide)
      -- Build τ : Fin 3 → Fin 3 with τ 0 = i_21, τ 2 = i_52.
      -- Use τ_a = swap 0 i_21 to send 0 → i_21.
      -- Then i_52' = τ_a⁻¹ i_52 ∈ {1, 2} (since i_52 ≠ i_21).
      -- Use τ_b = swap 2 i_52' to send 2 → i_52'.
      -- Then τ = τ_a ∘ τ_b sends 0 → i_21 (since τ_b 0 = 0 if i_52' ≠ 0)
      -- and 2 → i_52.
      set τ_a : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) i_21
      set i_52' : Fin 3 := τ_a.symm i_52 with hi_52'_def
      have hi_52'_ne_0 : i_52' ≠ 0 := by
        intro h
        have htmp : τ_a i_52' = τ_a 0 := by rw [h]
        rw [Equiv.apply_symm_apply, Equiv.swap_apply_left] at htmp
        exact hi_21_ne_52 htmp.symm
      set τ_b : Equiv.Perm (Fin 3) := Equiv.swap (2 : Fin 3) i_52'
      set τ : Equiv.Perm (Fin 3) := τ_a * τ_b with hτ_def
      have hτ_0 : τ 0 = i_21 := by
        change τ_a (τ_b 0) = i_21
        rw [show τ_b 0 = (0 : Fin 3) from
          Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 2)
            (fun h => hi_52'_ne_0 h.symm)]
        exact Equiv.swap_apply_left _ _
      have hτ_2 : τ 2 = i_52 := by
        change τ_a (τ_b 2) = i_52
        rw [show τ_b 2 = i_52' from Equiv.swap_apply_left _ _]
        exact Equiv.apply_symm_apply _ _
      set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
      have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
      have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
      have hu_a_0_p : ((u_a 0).1 : ℕ) = 2 := by
        change ((u' (τ 0)).1 : ℕ) = 2; rw [hτ_0]; exact hi_21_p
      have hu_a_0_q : ((u_a 0).2 : ℕ) = 1 := by
        change ((u' (τ 0)).2 : ℕ) = 1; rw [hτ_0]; exact hi_21_q
      have hu_a_2_p : ((u_a 2).1 : ℕ) = 5 := by
        change ((u' (τ 2)).1 : ℕ) = 5; rw [hτ_2]; exact hi_52_p
      have hu_a_2_q : ((u_a 2).2 : ℕ) = 2 := by
        change ((u' (τ 2)).2 : ℕ) = 2; rw [hτ_2]; exact hi_52_q
      have hu_a_1_mem : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
      -- u_a 1 is not (5, 2): τ 1 ≠ i_52.
      have hτ_1_ne_i_52 : τ 1 ≠ i_52 := by
        intro h
        have : τ 1 = τ 2 := h.trans hτ_2.symm
        exact absurd (τ.injective this) (by decide)
      have hu_a_1_ne_5o2 : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ≠ (5, 2) := by
        intro h
        have h_p : ((u' (τ 1)).1 : ℕ) = 5 := (Prod.mk.inj h).1
        have h_q : ((u' (τ 1)).2 : ℕ) = 2 := (Prod.mk.inj h).2
        have h_τ_1_5o2 : (((u' (τ 1)).1 : ℕ), ((u' (τ 1)).2 : ℕ)) = (5, 2) := by
          rw [h_p, h_q]
        exact h_at_most_one_5o2 (τ 1) i_52 hτ_1_ne_i_52 h_τ_1_5o2 hi_52
      have h_bound : alphaK u' ≤ nestedFloor3Nat 2 1 ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ) 5 2 := by
        rw [← hα_u_a]
        have h := alphaK_le_nestedFloor_with_first_two hu_a_valid 2 1 ((u_a 1).1 : ℕ)
          ((u_a 1).2 : ℕ) hu_a_0_p hu_a_0_q rfl rfl
        -- h : alphaK u_a ≤ nestedFloor3Nat 2 1 (u_a 1).1 (u_a 1).2 (u_a 2).1 (u_a 2).2.
        -- Rewrite (u_a 2).1 and (u_a 2).2 to 5 and 2.
        have h_eq : nestedFloor3Nat 2 1 ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ)
                      ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) =
                    nestedFloor3Nat 2 1 ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ) 5 2 := by
          unfold nestedFloor3Nat; rw [hu_a_2_p, hu_a_2_q]
        rw [h_eq] at h
        exact h
      have h_floor_le_8 := nestedFloor_2o1_mid_5o2_le_8 hu_a_1_mem hu_a_1_ne_5o2
      have h_alpha_le_8 : alphaK u' ≤ 8 := h_bound.trans h_floor_le_8
      rw [hα_u'] at h_alpha_le_8
      omega
    · -- ## Case B2: no (2, 1), some (5, 2). The multiset is (5,2)(9,4)(9,4).
      push_neg at h_caseB1
      -- We have a (9,4) slot.
      have h_some_9o4 : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (9, 4) := by
        obtain ⟨i, h_or⟩ := h_some_2o1_or_9o4
        rcases h_or with h_2o1 | h_9o4
        · exact absurd h_2o1 (h_caseB1 i)
        · exact ⟨i, h_9o4⟩
      obtain ⟨i_94, hi_94⟩ := h_some_9o4
      have hi_94_p : ((u' i_94).1 : ℕ) = 9 := (Prod.mk.inj hi_94).1
      have hi_94_q : ((u' i_94).2 : ℕ) = 4 := (Prod.mk.inj hi_94).2
      -- i_94 ≠ i_52.
      have hi_94_ne_52 : i_94 ≠ i_52 := by
        intro h
        rw [h] at hi_94_p; rw [hi_52_p] at hi_94_p
        exact absurd hi_94_p (by decide)
      -- The third slot k (≠ i_94, i_52) is in allowedPairs. By:
      -- (a) no (2,1): k ∉ {(2,1)}.
      -- (b) at most one (5,2): k ≠ (5,2).
      -- So k ∈ {(7,3), (9,4)}.
      -- (c) lePermK u' v with strict <ₚ rules out k = (7,3) (would give v as multiset).
      -- So k = (9,4). Multiset = (5,2)(9,4)(9,4).
      -- Find third slot index.
      -- The three indices are 0, 1, 2. We have i_52 and i_94 distinct.
      -- The third index is the one not equal to either.
      have h_third_exists : ∃ k : Fin 3, k ≠ i_52 ∧ k ≠ i_94 := by
        -- The third element of Fin 3 distinct from i_52 and i_94 exists since
        -- two of {0, 1, 2} are taken by i_52 and i_94.
        by_contra h
        push_neg at h
        have h0 := h 0
        have h1 := h 1
        have h2 := h 2
        revert h0 h1 h2 hi_94_ne_52
        fin_cases i_52 <;> fin_cases i_94 <;> decide
      obtain ⟨k, hk_ne_52, hk_ne_94⟩ := h_third_exists
      have hk_mem := hu'_in_allowed k
      have hk_ne_2o1 : (((u' k).1 : ℕ), ((u' k).2 : ℕ)) ≠ (2, 1) := h_caseB1 k
      have hk_ne_5o2 : (((u' k).1 : ℕ), ((u' k).2 : ℕ)) ≠ (5, 2) :=
        h_at_most_one_5o2 i_52 k (fun h => hk_ne_52 h.symm) hi_52
      -- From hk_mem ∧ hk_ne_2o1 ∧ hk_ne_5o2: (u' k) = (7, 3) or (9, 4).
      have hk_or : (((u' k).1 : ℕ), ((u' k).2 : ℕ)) = (7, 3) ∨
                    (((u' k).1 : ℕ), ((u' k).2 : ℕ)) = (9, 4) := by
        unfold allowedPairs at hk_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk_mem
        rcases hk_mem with h | h | h | h
        · exact absurd h hk_ne_2o1
        · exact absurd h hk_ne_5o2
        · left; exact h
        · right; exact h
      -- Rule out (7, 3): would make multiset = v.
      rcases hk_or with hk_73 | hk_94'
      · -- u'(k) = (7, 3). Then u' has multiset {(9,4), (7,3), (5,2)} = v's. Use strict <.
        exfalso
        have hk_p : ((u' k).1 : ℕ) = 7 := (Prod.mk.inj hk_73).1
        have hk_q : ((u' k).2 : ℕ) = 3 := (Prod.mk.inj hk_73).2
        -- Build a permutation σ : Fin 3 → Fin 3 with v.toRat (σ i) = u'.toRat i.
        -- v = ![(9,4),(7,3),(5,2)]. Map i_94 → 0, k → 1, i_52 → 2.
        -- This is a permutation since i_94, k, i_52 are distinct.
        have hu'_i_94_rat : FracTuple.toRat u' i_94 = 9 / 4 := by
          unfold FracTuple.toRat
          have hp : (((u' i_94).1 : ℕ) : ℚ) = 9 := by exact_mod_cast hi_94_p
          have hq : (((u' i_94).2 : ℕ) : ℚ) = 4 := by exact_mod_cast hi_94_q
          push_cast at hp hq ⊢
          rw [hp, hq]
        have hu'_k_rat : FracTuple.toRat u' k = 7 / 3 := by
          unfold FracTuple.toRat
          have hp : (((u' k).1 : ℕ) : ℚ) = 7 := by exact_mod_cast hk_p
          have hq : (((u' k).2 : ℕ) : ℚ) = 3 := by exact_mod_cast hk_q
          push_cast at hp hq ⊢
          rw [hp, hq]
        have hu'_i_52_rat : FracTuple.toRat u' i_52 = 5 / 2 := by
          unfold FracTuple.toRat
          have hp : (((u' i_52).1 : ℕ) : ℚ) = 5 := by exact_mod_cast hi_52_p
          have hq : (((u' i_52).2 : ℕ) : ℚ) = 2 := by exact_mod_cast hi_52_q
          push_cast at hp hq ⊢
          rw [hp, hq]
        have hv_0 : FracTuple.toRat v 0 = 9 / 4 := by
          simp [hv_def, FracTuple.toRat]
        have hv_1 : FracTuple.toRat v 1 = 7 / 3 := by
          simp [hv_def, FracTuple.toRat]
        have hv_2 : FracTuple.toRat v 2 = 5 / 2 := by
          simp [hv_def, FracTuple.toRat]
        -- Define σ : Fin 3 → Fin 3 by σ 0 = i_94, σ 1 = k, σ 2 = i_52.
        -- Build σ as a composition of swaps.
        -- σ_a = swap 0 i_94; σ_b = swap 1 (σ_a⁻¹ k); σ_c = identity-fix-up...
        -- Simpler: define directly using `Equiv.ofBijective` over Fin 3.
        -- We use the "permute" construction: Fin 3 has 6 perms.
        -- Build using two swaps:
        -- step1: σ_a = swap 0 i_94. σ_a 0 = i_94, σ_a i_94 = 0, others fixed.
        -- Now we need σ_b such that σ_a ∘ σ_b sends 1 → k, 2 → i_52, 0 → 0 (so σ_a 0 = i_94).
        -- σ_b 0 = 0, σ_b 1 = σ_a⁻¹ k, σ_b 2 = σ_a⁻¹ i_52.
        -- Since σ_a is involution, σ_a⁻¹ = σ_a.
        -- σ_a k = swap 0 i_94 k. If k = i_94, moves to 0. If k = 0, moves to i_94. Else k.
        -- We have k ≠ i_94. If k = 0, then σ_b 1 = i_94. But σ_b is supposed to fix 0...
        -- Easier: let's just pick the 6 cases based on (i_94, k, i_52) combinations.
        set τ_a : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) i_94 with hτ_a_def
        set k' : Fin 3 := τ_a.symm k with hk'_def
        have hk'_ne_0 : k' ≠ 0 := by
          intro h
          have htmp : τ_a k' = τ_a 0 := by rw [h]
          rw [Equiv.apply_symm_apply, Equiv.swap_apply_left] at htmp
          exact hk_ne_94 htmp
        set τ_b : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) k'
        set σ_τ : Equiv.Perm (Fin 3) := τ_a * τ_b with hσ_τ_def
        have hσ_τ_0 : σ_τ 0 = i_94 := by
          change τ_a (τ_b 0) = i_94
          rw [show τ_b 0 = (0 : Fin 3) from
            Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1)
              (fun h => hk'_ne_0 h.symm)]
          exact Equiv.swap_apply_left _ _
        have hσ_τ_1 : σ_τ 1 = k := by
          change τ_a (τ_b 1) = k
          rw [show τ_b 1 = k' from Equiv.swap_apply_left _ _]
          exact Equiv.apply_symm_apply _ _
        -- σ_τ 2 must equal i_52.
        -- σ_τ is a permutation of Fin 3, with σ_τ 0 = i_94, σ_τ 1 = k.
        -- The remaining value σ_τ 2 ∈ Fin 3 \ {i_94, k}. By assumption, i_52 is the unique
        -- such value.
        have hσ_τ_2_ne_i_94 : σ_τ 2 ≠ i_94 := by
          intro h; rw [← hσ_τ_0] at h; exact absurd (σ_τ.injective h) (by decide)
        have hσ_τ_2_ne_k : σ_τ 2 ≠ k := by
          intro h; rw [← hσ_τ_1] at h; exact absurd (σ_τ.injective h) (by decide)
        have hσ_τ_2 : σ_τ 2 = i_52 := by
          -- σ_τ 2 ∈ Fin 3 with σ_τ 2 ≠ i_94 and σ_τ 2 ≠ k. The remaining element is i_52.
          by_contra h_ne
          -- Now σ_τ 2 differs from i_94, k, and i_52, but Fin 3 has only 3 elements.
          set j := σ_τ 2 with hj_def
          revert hσ_τ_2_ne_i_94 hσ_τ_2_ne_k h_ne hk_ne_94 hk_ne_52 hi_94_ne_52
          clear_value j
          fin_cases j <;> fin_cases i_94 <;> fin_cases k <;> fin_cases i_52 <;> decide
        -- Now build v ≤ₚ u'. Use σ_τ⁻¹: it sends i_94 ↦ 0, k ↦ 1, i_52 ↦ 2.
        have hστ_inv_94 : σ_τ.symm i_94 = 0 := by
          rw [← hσ_τ_0]; exact σ_τ.symm_apply_apply 0
        have hστ_inv_k : σ_τ.symm k = 1 := by
          rw [← hσ_τ_1]; exact σ_τ.symm_apply_apply 1
        have hστ_inv_52 : σ_τ.symm i_52 = 2 := by
          rw [← hσ_τ_2]; exact σ_τ.symm_apply_apply 2
        have h_v_le_u' : lePermK v u' := by
          refine ⟨σ_τ.symm, fun i => ?_⟩
          -- Goal: v.toRat (σ_τ.symm i) ≤ u'.toRat i.
          -- i is one of i_94, k, i_52 (since these are all of Fin 3).
          have hi_or : i = i_94 ∨ i = k ∨ i = i_52 := by
            -- Use that fin_cases splits i_94, k, i_52 into 6 cases (after distinctness),
            -- and i is in Fin 3, so it equals one of them.
            by_contra h
            push_neg at h
            obtain ⟨h1, h2, h3⟩ := h
            -- i, i_94, k, i_52 are 4 distinct elements of Fin 3, contradiction.
            revert h1 h2 h3 hk_ne_94 hk_ne_52 hi_94_ne_52
            fin_cases i <;> fin_cases i_94 <;> fin_cases k <;> fin_cases i_52 <;>
              decide
          rcases hi_or with rfl | rfl | rfl
          · rw [hστ_inv_94, hv_0, hu'_i_94_rat]
          · rw [hστ_inv_k, hv_1, hu'_k_rat]
          · rw [hστ_inv_52, hv_2, hu'_i_52_rat]
        -- Chain v ≤ₚ u' ≤ₚ u₀ ≤ₚ u.
        have h_u₀_le_u : lePermK u₀ u :=
          ⟨1, fun i => by simp only [Equiv.Perm.coe_one, id_eq]; exact (hu₀_eq i).le⟩
        have h_v_le_u₀ : lePermK v u₀ := by
          obtain ⟨ρ₁, hρ₁⟩ := h_v_le_u'
          obtain ⟨ρ₂, hρ₂⟩ := hu'_le_u₀
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
      · -- u'(k) = (9, 4). Multiset is (5,2)(9,4)(9,4).
        have hk_p : ((u' k).1 : ℕ) = 9 := (Prod.mk.inj hk_94').1
        have hk_q : ((u' k).2 : ℕ) = 4 := (Prod.mk.inj hk_94').2
        -- Permute u' so slot 0 = i_94, slot 1 = k, slot 2 = i_52.
        set τ_a : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) i_94
        set k' : Fin 3 := τ_a.symm k with hk'_def
        have hk'_ne_0 : k' ≠ 0 := by
          intro h
          have htmp : τ_a k' = τ_a 0 := by rw [h]
          rw [Equiv.apply_symm_apply, Equiv.swap_apply_left] at htmp
          exact hk_ne_94 htmp
        set τ_b : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) k'
        set τ : Equiv.Perm (Fin 3) := τ_a * τ_b with hτ_def
        have hτ_0 : τ 0 = i_94 := by
          change τ_a (τ_b 0) = i_94
          rw [show τ_b 0 = (0 : Fin 3) from
            Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1)
              (fun h => hk'_ne_0 h.symm)]
          exact Equiv.swap_apply_left _ _
        have hτ_1 : τ 1 = k := by
          change τ_a (τ_b 1) = k
          rw [show τ_b 1 = k' from Equiv.swap_apply_left _ _]
          exact Equiv.apply_symm_apply _ _
        -- τ 2 must equal i_52 by pigeonhole.
        have hτ_2_ne_i_94 : τ 2 ≠ i_94 := by
          intro h; rw [← hτ_0] at h; exact absurd (τ.injective h) (by decide)
        have hτ_2_ne_k : τ 2 ≠ k := by
          intro h; rw [← hτ_1] at h; exact absurd (τ.injective h) (by decide)
        have hτ_2 : τ 2 = i_52 := by
          by_contra h_ne
          set j := τ 2 with hj_def
          revert hτ_2_ne_i_94 hτ_2_ne_k h_ne hk_ne_94 hk_ne_52 hi_94_ne_52
          clear_value j
          fin_cases j <;> fin_cases i_94 <;> fin_cases k <;> fin_cases i_52 <;> decide
        set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
        have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
        have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
        have hu_a_0_p : ((u_a 0).1 : ℕ) = 9 := by
          change ((u' (τ 0)).1 : ℕ) = 9; rw [hτ_0]; exact hi_94_p
        have hu_a_0_q : ((u_a 0).2 : ℕ) = 4 := by
          change ((u' (τ 0)).2 : ℕ) = 4; rw [hτ_0]; exact hi_94_q
        have hu_a_1_p : ((u_a 1).1 : ℕ) = 9 := by
          change ((u' (τ 1)).1 : ℕ) = 9; rw [hτ_1]; exact hk_p
        have hu_a_1_q : ((u_a 1).2 : ℕ) = 4 := by
          change ((u' (τ 1)).2 : ℕ) = 4; rw [hτ_1]; exact hk_q
        have hu_a_2_p : ((u_a 2).1 : ℕ) = 5 := by
          change ((u' (τ 2)).1 : ℕ) = 5; rw [hτ_2]; exact hi_52_p
        have hu_a_2_q : ((u_a 2).2 : ℕ) = 2 := by
          change ((u' (τ 2)).2 : ℕ) = 2; rw [hτ_2]; exact hi_52_q
        have h_bound : alphaK u_a ≤ 8 :=
          alphaK_le_8_of_9o4_9o4_5o2 hu_a_valid hu_a_0_p hu_a_0_q hu_a_1_p hu_a_1_q
            hu_a_2_p hu_a_2_q
        have h_alpha_le_8 : alphaK u' ≤ 8 := hα_u_a ▸ h_bound
        rw [hα_u'] at h_alpha_le_8
        omega

/-! ## FracTriple-form bridge -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9, FracTriple form.** -/
theorem alpha3_9o4_7o3_5o2_isDiscontinuity :
    IsDiscontinuity (![(9,4),(7,3),(5,2)] : FracTriple) :=
  (isDiscontinuity_iff_isDiscontinuityK ![(9,4),(7,3),(5,2)]).mpr
    alphaK_9o4_7o3_5o2_isDiscontinuityK

end Section6
