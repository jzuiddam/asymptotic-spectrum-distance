/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# `(8/3, 8/3, 8/3)` is an α₃-discontinuity

Paper Theorem 6.9 case 8 (line 2806). Diagonal point with α₃ = 12, where the
nested floor gives 13 (Baumert slicing trims it to 12).

## Strategy

Let `v := ![(8,3),(8,3),(8,3)]`. We have `alphaK v = alpha3 v = 12`.

For `u` valid with `ltPermK u v`, suppose for contradiction `alphaK u ≥ 12`.
By αₖ-monotonicity, `alphaK u ≤ alphaK v = 12`, so `alphaK u = 12`.

Reduce to a coprime form `u₀` (same `alphaK` since same `toRat`). Apply
`alphaK_attained_with_bounded_max` to get `u'` valid coprime with
`lePermK u' u₀` (so `lePermK u' v` by transitivity), `alphaK u' = 12`, and
`(u' i).1 ≤ 12` for all `i`.

Each slot of `u'` is one of 7 allowed `(p, q)` pairs determined by:
- `2 ≤ p / q ≤ 8/3` (validity + ≤ max of `v`),
- `p ≤ 12` (numerator bound),
- `coprime(p, q)`.

The pairs are: `(2,1), (5,2), (7,3), (8,3), (9,4), (11,5), (12,5)`.

Since `u' <ₚ v` strictly (and `v` has all slots `(8, 3)`), at least one slot
of `u'` is not `(8, 3)`. We split into 3 cases:

* **Case A**: some slot of `u'` is in `{(2,1), (7,3), (9,4), (11,5)}`. Permute
  to slot 0. For any pair `(p₀, q₀)` in this set and any `(p₁, q₁), (p₂, q₂) ∈
  allowedPairs`, `nestedFloor3Nat p₀ q₀ p₁ q₁ p₂ q₂ ≤ 11`.

* **Case B**: some slot of `u'` is `(12, 5)` (and Case A fails). Permute to
  slot 1. For any `(p₀, q₀), (p₂, q₂) ∈ allowedPairs`,
  `nestedFloor3Nat p₀ q₀ 12 5 p₂ q₂ ≤ 10 ≤ 11`.

* **Case C**: every slot of `u'` is in `{(5, 2), (8, 3)}`, and at least one
  slot is `(5, 2)` (since `u' <ₚ v` rules out all `(8, 3)`). Sub-cases by
  count of `(5, 2)`:
  - All three are `(5, 2)`: `alpha3_5o2_5o2_5o2_le ≤ 10`.
  - Two `(5, 2)`, one `(8, 3)`: `alpha3_5o2_5o2_8o3_le ≤ 11`.
  - One `(5, 2)`, two `(8, 3)`: `alpha3_5o2_8o3_8o3_le ≤ 11`.

In every sub-case, `alphaK u' ≤ 11 < 12`, contradicting `alphaK u' = 12`.

## Main results

* `alphaK_8o3_8o3_8o3_isDiscontinuityK` — K-form disc claim.
* `alpha3_8o3_8o3_8o3_isDiscontinuity` — FracTriple-form disc claim, by bridge.
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKAlphaTable
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## The disc point and its `alphaK` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(8,3),(8,3),(8,3)] = 12`. Direct from `alpha3_8o3_8o3_8o3` via
    the K-bridge. -/
theorem alphaK_8o3_8o3_8o3_eq :
    alphaK (![(8,3),(8,3),(8,3)] : FracTuple 3) = 12 := by
  rw [alphaK_three]
  change ((fractionGraph 8 3 ⊠ fractionGraph 8 3) ⊠ fractionGraph 8 3).indepNum = 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_8o3_8o3_8o3

private lemma validK_8o3_8o3_8o3 :
    ValidK (![(8,3),(8,3),(8,3)] : FracTuple 3) := by
  intro i; fin_cases i <;> decide

/-! ## Slot membership in allowed pairs -/

/-- The 7 allowed `(p, q) : ℕ × ℕ` pairs: coprime, lowest terms,
    `2q ≤ p ≤ 8q/3`, and `p ≤ 12`. -/
private def allowedPairs : List (ℕ × ℕ) :=
  [(2, 1), (5, 2), (7, 3), (8, 3), (9, 4), (11, 5), (12, 5)]

/-- Membership in `allowedPairs` from the constraints. -/
private lemma slot_in_allowedPairs (p q : ℕ) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (h_valid : 2 * q ≤ p) (h_p_le : p ≤ 12) (h_ratio_le : 3 * p ≤ 8 * q)
    (h_coprime : Nat.Coprime p q) :
    (p, q) ∈ allowedPairs := by
  have hq_le_6 : q ≤ 6 := by omega
  have hp_ge_2 : 2 ≤ p := by omega
  unfold allowedPairs
  interval_cases q <;> interval_cases p <;>
    first
    | (exfalso; omega)
    | (exfalso; revert h_coprime; decide)
    | simp

/-! ## Nested-floor bound: parameterized by first slot -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Nested-floor bound for a `FracTuple 3` parameterized by the first slot's
    `(p, q)`. -/
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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Nested-floor bound for a `FracTuple 3` parameterized by the first two slots'
    `(p, q)`. -/
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

/-! ## Case A: nested floor ≤ 11 when slot 0 ∈ {(2,1), (7,3), (9,4), (11,5)} -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For `(p₀, q₀) ∈ {(2,1), (7,3), (9,4), (11,5)}` and any `(p₁, q₁), (p₂, q₂) ∈
    allowedPairs`, `nestedFloor3Nat p₀ q₀ p₁ q₁ p₂ q₂ ≤ 11`. -/
private lemma nestedFloor_caseA_le_11
    {p₀ q₀ p₁ q₁ p₂ q₂ : ℕ}
    (h₀ : (p₀, q₀) = (2, 1) ∨ (p₀, q₀) = (7, 3) ∨ (p₀, q₀) = (9, 4) ∨
          (p₀, q₀) = (11, 5))
    (h₁ : (p₁, q₁) ∈ allowedPairs) (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat p₀ q₀ p₁ q₁ p₂ q₂ ≤ 11 := by
  unfold allowedPairs at h₁ h₂
  unfold nestedFloor3Nat
  rcases h₀ with h | h | h | h <;>
    (rw [show p₀ = _ from (Prod.mk.inj h).1, show q₀ = _ from (Prod.mk.inj h).2]
     fin_cases h₁ <;> fin_cases h₂ <;> decide)

/-! ## Case B: nested floor ≤ 11 when slot 1 = (12, 5) -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For any `(p₀, q₀) ∈ allowedPairs` and any `(p₂, q₂) ∈ allowedPairs`,
    `nestedFloor3Nat p₀ q₀ 12 5 p₂ q₂ ≤ 11`. -/
private lemma nestedFloor_caseB_12o5_mid_le_11
    {p₀ q₀ p₂ q₂ : ℕ}
    (h₀ : (p₀, q₀) ∈ allowedPairs) (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat p₀ q₀ 12 5 p₂ q₂ ≤ 11 := by
  unfold allowedPairs at h₀ h₂
  unfold nestedFloor3Nat
  fin_cases h₀ <;> fin_cases h₂ <;> decide

/-! ## Case C helpers: bridges to specific Baumert/interval bounds -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a` has all three slots equal to `(5, 2)` (as ℕ pairs), then
    `alphaK u_a ≤ 10`. Uses `alpha3_5o2_5o2_5o2_le`. -/
private lemma alphaK_le_10_of_all_5o2 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 5) (h0q : ((u_a 0).2 : ℕ) = 2)
    (h1p : ((u_a 1).1 : ℕ) = 5) (h1q : ((u_a 1).2 : ℕ) = 2)
    (h2p : ((u_a 2).1 : ℕ) = 5) (h2q : ((u_a 2).2 : ℕ) = 2) :
    alphaK u_a ≤ 10 := by
  -- Reference disc point: w := ![(5,2),(5,2),(5,2)].
  set w : FracTuple 3 := ![(5,2),(5,2),(5,2)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · -- i = 0
      change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 5 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 2 := by exact_mod_cast h0q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 1).1 : ℚ) / ((u_a 1).2 : ℚ) = ((w 1).1 : ℚ) / ((w 1).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 1).1 : ℕ) : ℚ) = 5 := by exact_mod_cast h1p
      have hq : (((u_a 1).2 : ℕ) : ℚ) = 2 := by exact_mod_cast h1q
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
  exact alpha3_5o2_5o2_5o2_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a 0 = (5, 2)`, `u_a 1 = (5, 2)`, `u_a 2 = (8, 3)`, then
    `alphaK u_a ≤ 11`. Uses `alpha3_5o2_5o2_8o3_le`. -/
private lemma alphaK_le_11_of_5o2_5o2_8o3 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 5) (h0q : ((u_a 0).2 : ℕ) = 2)
    (h1p : ((u_a 1).1 : ℕ) = 5) (h1q : ((u_a 1).2 : ℕ) = 2)
    (h2p : ((u_a 2).1 : ℕ) = 8) (h2q : ((u_a 2).2 : ℕ) = 3) :
    alphaK u_a ≤ 11 := by
  set w : FracTuple 3 := ![(5,2),(5,2),(8,3)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 5 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 2 := by exact_mod_cast h0q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 1).1 : ℚ) / ((u_a 1).2 : ℚ) = ((w 1).1 : ℚ) / ((w 1).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 1).1 : ℕ) : ℚ) = 5 := by exact_mod_cast h1p
      have hq : (((u_a 1).2 : ℕ) : ℚ) = 2 := by exact_mod_cast h1q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 2).1 : ℚ) / ((u_a 2).2 : ℚ) = ((w 2).1 : ℚ) / ((w 2).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 2).1 : ℕ) : ℚ) = 8 := by exact_mod_cast h2p
      have hq : (((u_a 2).2 : ℕ) : ℚ) = 3 := by exact_mod_cast h2q
      push_cast at hp hq ⊢
      rw [hp, hq]
  have hα_eq : alphaK u_a = alphaK w :=
    alphaK_eq_of_toRat_eq h_valid hw_valid h_toRat_eq
  rw [hα_eq, alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_5o2_5o2_8o3_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a 0 = (5, 2)`, `u_a 1 = (8, 3)`, `u_a 2 = (8, 3)`, then
    `alphaK u_a ≤ 11`. Uses `alpha3_5o2_8o3_8o3_le`. -/
private lemma alphaK_le_11_of_5o2_8o3_8o3 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 5) (h0q : ((u_a 0).2 : ℕ) = 2)
    (h1p : ((u_a 1).1 : ℕ) = 8) (h1q : ((u_a 1).2 : ℕ) = 3)
    (h2p : ((u_a 2).1 : ℕ) = 8) (h2q : ((u_a 2).2 : ℕ) = 3) :
    alphaK u_a ≤ 11 := by
  set w : FracTuple 3 := ![(5,2),(8,3),(8,3)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 5 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 2 := by exact_mod_cast h0q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 1).1 : ℚ) / ((u_a 1).2 : ℚ) = ((w 1).1 : ℚ) / ((w 1).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 1).1 : ℕ) : ℚ) = 8 := by exact_mod_cast h1p
      have hq : (((u_a 1).2 : ℕ) : ℚ) = 3 := by exact_mod_cast h1q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 2).1 : ℚ) / ((u_a 2).2 : ℚ) = ((w 2).1 : ℚ) / ((w 2).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 2).1 : ℕ) : ℚ) = 8 := by exact_mod_cast h2p
      have hq : (((u_a 2).2 : ℕ) : ℚ) = 3 := by exact_mod_cast h2q
      push_cast at hp hq ⊢
      rw [hp, hq]
  have hα_eq : alphaK u_a = alphaK w :=
    alphaK_eq_of_toRat_eq h_valid hw_valid h_toRat_eq
  rw [hα_eq, alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_5o2_8o3_8o3_le

/-! ## Main: the disc proof in K-form -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9.** The tuple `(8/3, 8/3, 8/3)` is
    an α₃-discontinuity. -/
theorem alphaK_8o3_8o3_8o3_isDiscontinuityK :
    IsDiscontinuityK (![(8,3),(8,3),(8,3)] : FracTuple 3) := by
  set v : FracTuple 3 := ![(8,3),(8,3),(8,3)] with hv_def
  have hv_valid : ValidK v := validK_8o3_8o3_8o3
  have hα_v : alphaK v = 12 := alphaK_8o3_8o3_8o3_eq
  intro u hu_valid hu_lt
  by_contra h_not_lt
  push_neg at h_not_lt
  -- αₖ-monotonicity: alphaK u ≤ alphaK v = 12.
  have hu_le_v : lePermK u v := hu_lt.1
  have hα_u_le : alphaK u ≤ alphaK v := alphaK_le_of_lePermK hu_valid hv_valid hu_le_v
  have hα_u : alphaK u = 12 := by
    rw [hα_v] at hα_u_le h_not_lt; omega
  -- Reduce u to coprime form.
  obtain ⟨u₀, hu₀_valid, hu₀_eq, hu₀_coprime⟩ := exists_coprime_form u hu_valid
  have hα_u₀ : alphaK u₀ = 12 := by
    rw [alphaK_eq_of_toRat_eq hu₀_valid hu_valid hu₀_eq, hα_u]
  -- Apply alphaK_attained_with_bounded_max to u₀.
  obtain ⟨u', hu'_valid, hu'_le_u₀, hu'_alpha, hu'_bound, hu'_coprime⟩ :=
    alphaK_attained_with_bounded_max hu₀_valid hu₀_coprime
  have hα_u' : alphaK u' = 12 := by rw [hu'_alpha, hα_u₀]
  -- Each (u' i).1 ≤ 12.
  have hu'_p_le : ∀ i, ((u' i).1 : ℕ) ≤ 12 := fun i => by
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
  -- Each slot of u' has ratio ≤ 8/3 (max of v).
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
    have h_int : (((u' i).1 : ℕ) : ℚ) * 3 ≤ (((u' i).2 : ℕ) : ℚ) * 8 := by linarith
    have h_int_n : ((u' i).1 : ℕ) * 3 ≤ ((u' i).2 : ℕ) * 8 := by exact_mod_cast h_int
    omega
  -- Each slot in allowedPairs.
  have hu'_in_allowed : ∀ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ∈ allowedPairs := by
    intro i
    have h2q : 2 * ((u' i).2 : ℕ) ≤ ((u' i).1 : ℕ) := by exact_mod_cast hu'_valid i
    exact slot_in_allowedPairs _ _ (u' i).1.pos (u' i).2.pos h2q (hu'_p_le i)
      (hu'_ratio_le_8o3 i) (hu'_coprime i)
  -- u' has at least one slot ≠ (8, 3) (else multiset = v, contradicting strict <).
  have h_some_ne_8o3 : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ≠ (8, 3) := by
    by_contra h_all
    push_neg at h_all
    have h_all_p : ∀ i, ((u' i).1 : ℕ) = 8 := fun i => (Prod.mk.inj (h_all i)).1
    have h_all_q : ∀ i, ((u' i).2 : ℕ) = 3 := fun i => (Prod.mk.inj (h_all i)).2
    have h_u'_toRat : ∀ i, FracTuple.toRat u' i = 8 / 3 := by
      intro i
      unfold FracTuple.toRat
      have hp : (((u' i).1 : ℕ) : ℚ) = 8 := by exact_mod_cast h_all_p i
      have hq : (((u' i).2 : ℕ) : ℚ) = 3 := by exact_mod_cast h_all_q i
      push_cast at hp hq ⊢
      rw [hp, hq]
    have h_v_toRat : ∀ i, FracTuple.toRat v i = 8 / 3 := by
      intro i
      simp only [hv_def, FracTuple.toRat]
      fin_cases i <;> norm_num
    have h_v_le_u' : lePermK v u' :=
      ⟨1, fun i => by
        simp only [Equiv.Perm.coe_one, id_eq]
        rw [h_v_toRat, h_u'_toRat]⟩
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
  -- # Case split.
  by_cases h_caseA : ∃ i,
      (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (2, 1) ∨
      (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (7, 3) ∨
      (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (9, 4) ∨
      (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (11, 5)
  · -- ## Case A: some slot is in {(2,1), (7,3), (9,4), (11,5)}. Permute to slot 0.
    obtain ⟨i₀, h_or⟩ := h_caseA
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
    have hu_a_0_or : (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) = (2, 1) ∨
                     (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) = (7, 3) ∨
                     (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) = (9, 4) ∨
                     (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) = (11, 5) := by
      rw [show (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) =
            (((u' i₀).1 : ℕ), ((u' i₀).2 : ℕ)) from by rw [hu_a_0_p, hu_a_0_q]]
      exact h_or
    have hu_a_1_mem : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
    have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
    have h_bound : alphaK u' ≤ nestedFloor3Nat ((u_a 0).1 : ℕ) ((u_a 0).2 : ℕ)
        ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ) ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
      rw [← hα_u_a]
      exact alphaK_le_nestedFloor_with_first hu_a_valid _ _ rfl rfl
    have h_floor_le_11 := nestedFloor_caseA_le_11 hu_a_0_or hu_a_1_mem hu_a_2_mem
    have h_alpha_le_11 : alphaK u' ≤ 11 := h_bound.trans h_floor_le_11
    rw [hα_u'] at h_alpha_le_11
    omega
  · -- No slot is in {(2,1), (7,3), (9,4), (11,5)}. So all slots ∈ {(5,2), (8,3), (12,5)}.
    push_neg at h_caseA
    have h_slots_in : ∀ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (5, 2) ∨
                            (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (8, 3) ∨
                            (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (12, 5) := by
      intro i
      have h_in := hu'_in_allowed i
      obtain ⟨h_ne_2o1, h_ne_7o3, h_ne_9o4, h_ne_11o5⟩ := h_caseA i
      unfold allowedPairs at h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with h | h | h | h | h | h | h
      · exact absurd h h_ne_2o1
      · left; exact h
      · exact absurd h h_ne_7o3
      · right; left; exact h
      · exact absurd h h_ne_9o4
      · exact absurd h h_ne_11o5
      · right; right; exact h
    by_cases h_caseB : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (12, 5)
    · -- ## Case B: some slot is (12, 5). Permute to slot 1.
      obtain ⟨i_125, hi_125⟩ := h_caseB
      have hi_125_p : ((u' i_125).1 : ℕ) = 12 := (Prod.mk.inj hi_125).1
      have hi_125_q : ((u' i_125).2 : ℕ) = 5 := (Prod.mk.inj hi_125).2
      -- Permute i_125 to slot 1.
      set τ : Equiv.Perm (Fin 3) := Equiv.swap i_125 1 with hτ_def
      set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
      have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
      have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
      have hu_a_1_p : ((u_a 1).1 : ℕ) = 12 := by
        change ((u' (τ 1)).1 : ℕ) = 12
        rw [hτ_def, Equiv.swap_apply_right]; exact hi_125_p
      have hu_a_1_q : ((u_a 1).2 : ℕ) = 5 := by
        change ((u' (τ 1)).2 : ℕ) = 5
        rw [hτ_def, Equiv.swap_apply_right]; exact hi_125_q
      have hu_a_0_mem : (((u_a 0).1 : ℕ), ((u_a 0).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
      have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
      have h_bound : alphaK u' ≤ nestedFloor3Nat ((u_a 0).1 : ℕ) ((u_a 0).2 : ℕ)
          12 5 ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
        rw [← hα_u_a]
        exact alphaK_le_nestedFloor_with_first_two hu_a_valid _ _ 12 5 rfl rfl
          hu_a_1_p hu_a_1_q
      have h_floor_le_11 := nestedFloor_caseB_12o5_mid_le_11 hu_a_0_mem hu_a_2_mem
      have h_alpha_le_11 : alphaK u' ≤ 11 := h_bound.trans h_floor_le_11
      rw [hα_u'] at h_alpha_le_11
      omega
    · -- ## Case C: no slot is (12, 5). All slots ∈ {(5, 2), (8, 3)}.
      push_neg at h_caseB
      have h_slots_2 : ∀ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (5, 2) ∨
                              (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (8, 3) := by
        intro i
        rcases h_slots_in i with h | h | h
        · left; exact h
        · right; exact h
        · exact absurd h (h_caseB i)
      -- We have ≥ 1 slot = (5, 2) (else all = (8, 3), contradicts h_some_ne_8o3).
      have h_some_5o2 : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (5, 2) := by
        by_contra h_no
        push_neg at h_no
        obtain ⟨i, hi_ne⟩ := h_some_ne_8o3
        rcases h_slots_2 i with h_5 | h_8
        · exact absurd h_5 (h_no i)
        · exact hi_ne h_8
      obtain ⟨i_52, hi_52⟩ := h_some_5o2
      have hi_52_p : ((u' i_52).1 : ℕ) = 5 := (Prod.mk.inj hi_52).1
      have hi_52_q : ((u' i_52).2 : ℕ) = 2 := (Prod.mk.inj hi_52).2
      -- Sub-case on whether ≥ 2 slots are (5, 2).
      by_cases h_two_5o2 : ∃ j : Fin 3, j ≠ i_52 ∧
          (((u' j).1 : ℕ), ((u' j).2 : ℕ)) = (5, 2)
      · -- ## Sub-case C2: ≥ 2 slots are (5, 2). Permute two of them to slots 0, 1.
        obtain ⟨i_52', hi_52'_ne, hi_52'⟩ := h_two_5o2
        have hi_52'_p : ((u' i_52').1 : ℕ) = 5 := (Prod.mk.inj hi_52').1
        have hi_52'_q : ((u' i_52').2 : ℕ) = 2 := (Prod.mk.inj hi_52').2
        -- Place i_52 → 0 and i_52' → 1 via composition of swaps.
        set τ_a : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) i_52
        set i_52'_a : Fin 3 := τ_a.symm i_52' with hi_52'_a_def
        have hi_52'_a_ne_0 : i_52'_a ≠ 0 := by
          intro h
          have htmp : τ_a i_52'_a = τ_a 0 := by rw [h]
          rw [Equiv.apply_symm_apply, Equiv.swap_apply_left] at htmp
          exact hi_52'_ne htmp
        set τ_b : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) i_52'_a
        set τ : Equiv.Perm (Fin 3) := τ_a * τ_b with hτ_def
        have hτ_0 : τ 0 = i_52 := by
          change τ_a (τ_b 0) = i_52
          rw [show τ_b 0 = (0 : Fin 3) from
            Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1)
              (fun h => hi_52'_a_ne_0 h.symm)]
          exact Equiv.swap_apply_left _ _
        have hτ_1 : τ 1 = i_52' := by
          change τ_a (τ_b 1) = i_52'
          rw [show τ_b 1 = i_52'_a from Equiv.swap_apply_left _ _]
          exact Equiv.apply_symm_apply _ _
        set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
        have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
        have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
        have hu_a_0_p : ((u_a 0).1 : ℕ) = 5 := by
          change ((u' (τ 0)).1 : ℕ) = 5; rw [hτ_0]; exact hi_52_p
        have hu_a_0_q : ((u_a 0).2 : ℕ) = 2 := by
          change ((u' (τ 0)).2 : ℕ) = 2; rw [hτ_0]; exact hi_52_q
        have hu_a_1_p : ((u_a 1).1 : ℕ) = 5 := by
          change ((u' (τ 1)).1 : ℕ) = 5; rw [hτ_1]; exact hi_52'_p
        have hu_a_1_q : ((u_a 1).2 : ℕ) = 2 := by
          change ((u' (τ 1)).2 : ℕ) = 2; rw [hτ_1]; exact hi_52'_q
        -- Slot 2 is in {(5,2), (8,3)}.
        have hu_a_2_in : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (5, 2) ∨
                          (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (8, 3) :=
          h_slots_2 (τ 2)
        rcases hu_a_2_in with h_2_52 | h_2_83
        · -- All three slots are (5, 2).
          have hu_a_2_p : ((u_a 2).1 : ℕ) = 5 := (Prod.mk.inj h_2_52).1
          have hu_a_2_q : ((u_a 2).2 : ℕ) = 2 := (Prod.mk.inj h_2_52).2
          have h_bound : alphaK u_a ≤ 10 :=
            alphaK_le_10_of_all_5o2 hu_a_valid hu_a_0_p hu_a_0_q hu_a_1_p hu_a_1_q
              hu_a_2_p hu_a_2_q
          have : alphaK u' ≤ 10 := hα_u_a ▸ h_bound
          rw [hα_u'] at this; omega
        · -- Two (5, 2), one (8, 3): use alpha3_5o2_5o2_8o3_le.
          have hu_a_2_p : ((u_a 2).1 : ℕ) = 8 := (Prod.mk.inj h_2_83).1
          have hu_a_2_q : ((u_a 2).2 : ℕ) = 3 := (Prod.mk.inj h_2_83).2
          have h_bound : alphaK u_a ≤ 11 :=
            alphaK_le_11_of_5o2_5o2_8o3 hu_a_valid hu_a_0_p hu_a_0_q hu_a_1_p hu_a_1_q
              hu_a_2_p hu_a_2_q
          have : alphaK u' ≤ 11 := hα_u_a ▸ h_bound
          rw [hα_u'] at this; omega
      · -- ## Sub-case C1: exactly one slot is (5, 2), other two are (8, 3).
        push_neg at h_two_5o2
        -- Permute i_52 to slot 0; the other two slots are (8, 3).
        set τ : Equiv.Perm (Fin 3) := Equiv.swap i_52 0 with hτ_def
        set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
        have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
        have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
        have hu_a_0_p : ((u_a 0).1 : ℕ) = 5 := by
          change ((u' (τ 0)).1 : ℕ) = 5
          rw [hτ_def, Equiv.swap_apply_right]; exact hi_52_p
        have hu_a_0_q : ((u_a 0).2 : ℕ) = 2 := by
          change ((u' (τ 0)).2 : ℕ) = 2
          rw [hτ_def, Equiv.swap_apply_right]; exact hi_52_q
        have hτ_0 : τ 0 = i_52 := by rw [hτ_def, Equiv.swap_apply_right]
        have hτ_1_ne : τ 1 ≠ i_52 := by
          intro h
          have : τ 1 = τ 0 := h.trans hτ_0.symm
          exact absurd (τ.injective this) (by decide)
        have hτ_2_ne : τ 2 ≠ i_52 := by
          intro h
          have : τ 2 = τ 0 := h.trans hτ_0.symm
          exact absurd (τ.injective this) (by decide)
        have hu_a_1_8o3 : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (8, 3) := by
          have h_or := h_slots_2 (τ 1)
          rcases h_or with h_5 | h_8
          · exact absurd h_5 (h_two_5o2 (τ 1) hτ_1_ne)
          · exact h_8
        have hu_a_2_8o3 : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (8, 3) := by
          have h_or := h_slots_2 (τ 2)
          rcases h_or with h_5 | h_8
          · exact absurd h_5 (h_two_5o2 (τ 2) hτ_2_ne)
          · exact h_8
        have hu_a_1_p : ((u_a 1).1 : ℕ) = 8 := (Prod.mk.inj hu_a_1_8o3).1
        have hu_a_1_q : ((u_a 1).2 : ℕ) = 3 := (Prod.mk.inj hu_a_1_8o3).2
        have hu_a_2_p : ((u_a 2).1 : ℕ) = 8 := (Prod.mk.inj hu_a_2_8o3).1
        have hu_a_2_q : ((u_a 2).2 : ℕ) = 3 := (Prod.mk.inj hu_a_2_8o3).2
        have h_bound : alphaK u_a ≤ 11 :=
          alphaK_le_11_of_5o2_8o3_8o3 hu_a_valid hu_a_0_p hu_a_0_q hu_a_1_p hu_a_1_q
            hu_a_2_p hu_a_2_q
        have : alphaK u' ≤ 11 := hα_u_a ▸ h_bound
        rw [hα_u'] at this; omega

/-! ## FracTriple-form bridge -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9, FracTriple form.** -/
theorem alpha3_8o3_8o3_8o3_isDiscontinuity :
    IsDiscontinuity (![(8,3),(8,3),(8,3)] : FracTriple) :=
  (isDiscontinuity_iff_isDiscontinuityK ![(8,3),(8,3),(8,3)]).mpr
    alphaK_8o3_8o3_8o3_isDiscontinuityK

end Section6
