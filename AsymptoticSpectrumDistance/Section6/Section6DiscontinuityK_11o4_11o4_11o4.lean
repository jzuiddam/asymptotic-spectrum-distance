/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# `(11/4, 11/4, 11/4)` is an α₃-discontinuity

Paper Theorem 6.9 case 11 (line 2806). Diagonal point with α₃ = 13, where the
nested floor gives 13 (tight) and the discontinuity follows from a careful
case analysis using both `alpha3_le_12_of_lt_11o4` and the five
Baumert-style mixed-multiset bounds.

## Strategy

Let `v := ![(11,4),(11,4),(11,4)]`. We have `alphaK v = alpha3 v = 13`.

For `u` valid with `ltPermK u v`, suppose for contradiction `alphaK u ≥ 13`.
By αₖ-monotonicity, `alphaK u ≤ alphaK v = 13`, so `alphaK u = 13`.

Reduce to a coprime form `u₀` (same `alphaK` since same `toRat`). Apply
`alphaK_attained_with_bounded_max` to get `u'` valid coprime with
`lePermK u' u₀` (so `lePermK u' v` by transitivity), `alphaK u' = 13`, and
`(u' i).1 ≤ 13` for all `i`.

Each slot of `u'` is one of 10 allowed `(p, q)` pairs determined by:
- `2 ≤ p / q ≤ 11/4` (validity + ≤ max of `v`),
- `p ≤ 13` (numerator bound),
- `coprime(p, q)`.

The pairs are: `(2,1), (5,2), (7,3), (8,3), (9,4), (11,4), (11,5), (12,5),
(13,5), (13,6)`.

Since `u' <ₚ v` strictly (and `v` has all three slots `(11, 4)`), at least
one slot of `u'` is not `(11, 4)`. We split into 3 main cases:

* **Case A**: some slot of `u'` is `(5, 2)`. Permute `(5, 2)` to slot 0. With
  `(5, 2)` outermost in `nestedFloor3Nat`, and any `allowedPairs`-slots in
  positions 1, 2, the result is `≤ 12 ≤ 12`. Contradiction.

* **Case B-R**: no slot is `(5, 2)` and no slot is `(11, 4)`. Then every
  slot has ratio strictly `< 11/4`. By `alpha3_le_12_of_lt_11o4`,
  `alphaK u' ≤ 12 < 13`. Contradiction.

* **Case B-N**: no slot is `(5, 2)` but some slot is `(11, 4)`. Permute
  `(11, 4)` to slot 0. Sub-split:

  - **Case B-N-1**: some slot in positions 1, 2 is in
    `{(2,1),(7,3),(9,4),(11,5),(12,5),(13,6)}` (the "low" pairs, where
    `⌊p/q · 2⌋ = 4`). Permute that slot to position 1. Then
    `nestedFloor3Nat 11 4 (low) p₂ q₂ ≤ 11`. Contradiction.

  - **Case B-N-2**: both other slots are in `{(8,3),(11,4),(13,5)}` (the
    "high" pairs). The multiset is one of:
    * `{(11,4),(8,3),(8,3)}` → `alpha3_83_83_114_le ≤ 12`
    * `{(11,4),(8,3),(11,4)}` → `alpha3_83_114_114_le ≤ 12`
    * `{(11,4),(8,3),(13,5)}` → `alpha3_83_114_135_le ≤ 12`
    * `{(11,4),(11,4),(11,4)}` = `v`, excluded by strict `<ₚ`
    * `{(11,4),(11,4),(13,5)}` → `alpha3_114_114_135_le ≤ 12`
    * `{(11,4),(13,5),(13,5)}` → `alpha3_114_135_135_le ≤ 12`

In every sub-case, `alphaK u' ≤ 12 < 13`, contradicting `alphaK u' = 13`.

## Main results

* `alphaK_11o4_11o4_11o4_isDiscontinuityK` — K-form disc claim.
* `alpha3_11o4_11o4_11o4_isDiscontinuity` — FracTriple-form disc claim,
  by bridge.
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKAlphaTable
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## The disc point and its `alphaK` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(11,4),(11,4),(11,4)] = 13`. Direct from `alpha3_11o4_11o4_11o4`
    via the K-bridge. -/
theorem alphaK_11o4_11o4_11o4_eq :
    alphaK (![(11,4),(11,4),(11,4)] : FracTuple 3) = 13 := by
  rw [alphaK_three]
  change ((fractionGraph 11 4 ⊠ fractionGraph 11 4) ⊠ fractionGraph 11 4).indepNum = 13
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_11o4_11o4_11o4

private lemma validK_11o4_11o4_11o4 :
    ValidK (![(11,4),(11,4),(11,4)] : FracTuple 3) := by
  intro i; fin_cases i <;> decide

/-! ## Slot membership in allowed pairs -/

/-- The 10 allowed `(p, q) : ℕ × ℕ` pairs: coprime, lowest terms,
    `2q ≤ p ≤ 11q/4`, and `p ≤ 13`. -/
private def allowedPairs : List (ℕ × ℕ) :=
  [(2, 1), (5, 2), (7, 3), (8, 3), (9, 4), (11, 4),
   (11, 5), (12, 5), (13, 5), (13, 6)]

/-- Membership in `allowedPairs` from the constraints. -/
private lemma slot_in_allowedPairs (p q : ℕ) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (h_valid : 2 * q ≤ p) (h_p_le : p ≤ 13) (h_ratio_le : 4 * p ≤ 11 * q)
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

/-- A pair in `allowedPairs` and not equal to `(5, 2)` and not equal to
    `(11, 4)` has ratio strictly `< 11/4`. -/
private lemma allowedPair_strict_of_ne_5o2_ne_11o4 {p q : ℕ}
    (h_mem : (p, q) ∈ allowedPairs)
    (h_ne_5o2 : (p, q) ≠ (5, 2)) (h_ne_11o4 : (p, q) ≠ (11, 4)) :
    4 * p < 11 * q := by
  unfold allowedPairs at h_mem
  fin_cases h_mem <;>
    first
    | (exfalso; exact h_ne_5o2 rfl)
    | (exfalso; exact h_ne_11o4 rfl)
    | omega

/-! ## Nested-floor bound: parameterized by first slot or first two slots -/

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

/-! ## Case A: nested floor ≤ 12 when slot 0 = (5, 2) -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For any `(p₁, q₁), (p₂, q₂) ∈ allowedPairs`,
    `nestedFloor3Nat 5 2 p₁ q₁ p₂ q₂ ≤ 12`. -/
private lemma nestedFloor_caseA_5o2_first_le_12
    {p₁ q₁ p₂ q₂ : ℕ}
    (h₁ : (p₁, q₁) ∈ allowedPairs) (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat 5 2 p₁ q₁ p₂ q₂ ≤ 12 := by
  unfold allowedPairs at h₁ h₂
  unfold nestedFloor3Nat
  fin_cases h₁ <;> fin_cases h₂ <;> decide

/-! ## Case B-R bound: all slots ratio `< 11/4` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- If a `FracTuple 3` is valid and each slot has `4 (u i).1 < 11 (u i).2`,
    then `alphaK u ≤ 12`. -/
private lemma alphaK_le_12_of_all_lt_11o4 {u : FracTuple 3}
    (h_valid : ValidK u)
    (h_strict : ∀ i, 4 * ((u i).1 : ℕ) < 11 * ((u i).2 : ℕ)) :
    alphaK u ≤ 12 := by
  rw [alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  haveI : NeZero ((u 0).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 0).1.pos⟩
  haveI : NeZero ((u 1).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 1).1.pos⟩
  haveI : NeZero ((u 2).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (u 2).1.pos⟩
  have h2q : ∀ i, 2 * ((u i).2 : ℕ) ≤ ((u i).1 : ℕ) := fun i => by exact_mod_cast h_valid i
  have hq_pos : ∀ i, 0 < ((u i).2 : ℕ) := fun i => (u i).2.pos
  exact alpha3_le_12_of_lt_11o4 _ _ _ _ _ _
    (hq_pos 0) (h2q 0) (h_strict 0)
    (hq_pos 1) (h2q 1) (h_strict 1)
    (hq_pos 2) (h2q 2) (h_strict 2)

/-! ## Case B-N-1 nested floor: (11, 4) at slot 0, "low" pair at slot 1 -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For `(p₁, q₁) ∈ {(2,1),(7,3),(9,4),(11,5),(12,5),(13,6)}` and any
    `(p₂, q₂) ∈ allowedPairs`, `nestedFloor3Nat 11 4 p₁ q₁ p₂ q₂ ≤ 11`. -/
private lemma nestedFloor_caseBN1_le_11
    {p₁ q₁ p₂ q₂ : ℕ}
    (h₁ : (p₁, q₁) = (2, 1) ∨ (p₁, q₁) = (7, 3) ∨ (p₁, q₁) = (9, 4) ∨
          (p₁, q₁) = (11, 5) ∨ (p₁, q₁) = (12, 5) ∨ (p₁, q₁) = (13, 6))
    (h₂ : (p₂, q₂) ∈ allowedPairs) :
    nestedFloor3Nat 11 4 p₁ q₁ p₂ q₂ ≤ 11 := by
  unfold allowedPairs at h₂
  unfold nestedFloor3Nat
  rcases h₁ with h | h | h | h | h | h <;>
    (rw [show p₁ = _ from (Prod.mk.inj h).1, show q₁ = _ from (Prod.mk.inj h).2]
     fin_cases h₂ <;> decide)

/-! ## Case B-N-2 helpers: bridges to specific Baumert/interval bounds -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a 0 = (8, 3)`, `u_a 1 = (8, 3)`, `u_a 2 = (11, 4)`, then
    `alphaK u_a ≤ 12`. Uses `alpha3_83_83_114_le`. -/
private lemma alphaK_le_12_of_83_83_114 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 8) (h0q : ((u_a 0).2 : ℕ) = 3)
    (h1p : ((u_a 1).1 : ℕ) = 8) (h1q : ((u_a 1).2 : ℕ) = 3)
    (h2p : ((u_a 2).1 : ℕ) = 11) (h2q : ((u_a 2).2 : ℕ) = 4) :
    alphaK u_a ≤ 12 := by
  set w : FracTuple 3 := ![(8,3),(8,3),(11,4)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 8 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 3 := by exact_mod_cast h0q
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
      have hp : (((u_a 2).1 : ℕ) : ℚ) = 11 := by exact_mod_cast h2p
      have hq : (((u_a 2).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h2q
      push_cast at hp hq ⊢
      rw [hp, hq]
  have hα_eq : alphaK u_a = alphaK w :=
    alphaK_eq_of_toRat_eq h_valid hw_valid h_toRat_eq
  rw [hα_eq, alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_83_83_114_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a 0 = (8, 3)`, `u_a 1 = (11, 4)`, `u_a 2 = (11, 4)`, then
    `alphaK u_a ≤ 12`. Uses `alpha3_83_114_114_le`. -/
private lemma alphaK_le_12_of_83_114_114 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 8) (h0q : ((u_a 0).2 : ℕ) = 3)
    (h1p : ((u_a 1).1 : ℕ) = 11) (h1q : ((u_a 1).2 : ℕ) = 4)
    (h2p : ((u_a 2).1 : ℕ) = 11) (h2q : ((u_a 2).2 : ℕ) = 4) :
    alphaK u_a ≤ 12 := by
  set w : FracTuple 3 := ![(8,3),(11,4),(11,4)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 8 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 3 := by exact_mod_cast h0q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 1).1 : ℚ) / ((u_a 1).2 : ℚ) = ((w 1).1 : ℚ) / ((w 1).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 1).1 : ℕ) : ℚ) = 11 := by exact_mod_cast h1p
      have hq : (((u_a 1).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h1q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 2).1 : ℚ) / ((u_a 2).2 : ℚ) = ((w 2).1 : ℚ) / ((w 2).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 2).1 : ℕ) : ℚ) = 11 := by exact_mod_cast h2p
      have hq : (((u_a 2).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h2q
      push_cast at hp hq ⊢
      rw [hp, hq]
  have hα_eq : alphaK u_a = alphaK w :=
    alphaK_eq_of_toRat_eq h_valid hw_valid h_toRat_eq
  rw [hα_eq, alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_83_114_114_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a 0 = (8, 3)`, `u_a 1 = (11, 4)`, `u_a 2 = (13, 5)`, then
    `alphaK u_a ≤ 12`. Uses `alpha3_83_114_135_le`. -/
private lemma alphaK_le_12_of_83_114_135 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 8) (h0q : ((u_a 0).2 : ℕ) = 3)
    (h1p : ((u_a 1).1 : ℕ) = 11) (h1q : ((u_a 1).2 : ℕ) = 4)
    (h2p : ((u_a 2).1 : ℕ) = 13) (h2q : ((u_a 2).2 : ℕ) = 5) :
    alphaK u_a ≤ 12 := by
  set w : FracTuple 3 := ![(8,3),(11,4),(13,5)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 8 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 3 := by exact_mod_cast h0q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 1).1 : ℚ) / ((u_a 1).2 : ℚ) = ((w 1).1 : ℚ) / ((w 1).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 1).1 : ℕ) : ℚ) = 11 := by exact_mod_cast h1p
      have hq : (((u_a 1).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h1q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 2).1 : ℚ) / ((u_a 2).2 : ℚ) = ((w 2).1 : ℚ) / ((w 2).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 2).1 : ℕ) : ℚ) = 13 := by exact_mod_cast h2p
      have hq : (((u_a 2).2 : ℕ) : ℚ) = 5 := by exact_mod_cast h2q
      push_cast at hp hq ⊢
      rw [hp, hq]
  have hα_eq : alphaK u_a = alphaK w :=
    alphaK_eq_of_toRat_eq h_valid hw_valid h_toRat_eq
  rw [hα_eq, alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_83_114_135_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a 0 = (11, 4)`, `u_a 1 = (11, 4)`, `u_a 2 = (13, 5)`, then
    `alphaK u_a ≤ 12`. Uses `alpha3_114_114_135_le`. -/
private lemma alphaK_le_12_of_114_114_135 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 11) (h0q : ((u_a 0).2 : ℕ) = 4)
    (h1p : ((u_a 1).1 : ℕ) = 11) (h1q : ((u_a 1).2 : ℕ) = 4)
    (h2p : ((u_a 2).1 : ℕ) = 13) (h2q : ((u_a 2).2 : ℕ) = 5) :
    alphaK u_a ≤ 12 := by
  set w : FracTuple 3 := ![(11,4),(11,4),(13,5)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 11 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h0q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 1).1 : ℚ) / ((u_a 1).2 : ℚ) = ((w 1).1 : ℚ) / ((w 1).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 1).1 : ℕ) : ℚ) = 11 := by exact_mod_cast h1p
      have hq : (((u_a 1).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h1q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 2).1 : ℚ) / ((u_a 2).2 : ℚ) = ((w 2).1 : ℚ) / ((w 2).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 2).1 : ℕ) : ℚ) = 13 := by exact_mod_cast h2p
      have hq : (((u_a 2).2 : ℕ) : ℚ) = 5 := by exact_mod_cast h2q
      push_cast at hp hq ⊢
      rw [hp, hq]
  have hα_eq : alphaK u_a = alphaK w :=
    alphaK_eq_of_toRat_eq h_valid hw_valid h_toRat_eq
  rw [hα_eq, alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_114_114_135_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bridge: if `u_a 0 = (11, 4)`, `u_a 1 = (13, 5)`, `u_a 2 = (13, 5)`, then
    `alphaK u_a ≤ 12`. Uses `alpha3_114_135_135_le`. -/
private lemma alphaK_le_12_of_114_135_135 {u_a : FracTuple 3}
    (h_valid : ValidK u_a)
    (h0p : ((u_a 0).1 : ℕ) = 11) (h0q : ((u_a 0).2 : ℕ) = 4)
    (h1p : ((u_a 1).1 : ℕ) = 13) (h1q : ((u_a 1).2 : ℕ) = 5)
    (h2p : ((u_a 2).1 : ℕ) = 13) (h2q : ((u_a 2).2 : ℕ) = 5) :
    alphaK u_a ≤ 12 := by
  set w : FracTuple 3 := ![(11,4),(13,5),(13,5)] with hw_def
  have hw_valid : ValidK w := by intro i; fin_cases i <;> decide
  have h_toRat_eq : ∀ i, FracTuple.toRat u_a i = FracTuple.toRat w i := by
    intro i
    fin_cases i
    · change ((u_a 0).1 : ℚ) / ((u_a 0).2 : ℚ) = ((w 0).1 : ℚ) / ((w 0).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 0).1 : ℕ) : ℚ) = 11 := by exact_mod_cast h0p
      have hq : (((u_a 0).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h0q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 1).1 : ℚ) / ((u_a 1).2 : ℚ) = ((w 1).1 : ℚ) / ((w 1).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 1).1 : ℕ) : ℚ) = 13 := by exact_mod_cast h1p
      have hq : (((u_a 1).2 : ℕ) : ℚ) = 5 := by exact_mod_cast h1q
      push_cast at hp hq ⊢
      rw [hp, hq]
    · change ((u_a 2).1 : ℚ) / ((u_a 2).2 : ℚ) = ((w 2).1 : ℚ) / ((w 2).2 : ℚ)
      rw [hw_def]
      have hp : (((u_a 2).1 : ℕ) : ℚ) = 13 := by exact_mod_cast h2p
      have hq : (((u_a 2).2 : ℕ) : ℚ) = 5 := by exact_mod_cast h2q
      push_cast at hp hq ⊢
      rw [hp, hq]
  have hα_eq : alphaK u_a = alphaK w :=
    alphaK_eq_of_toRat_eq h_valid hw_valid h_toRat_eq
  rw [hα_eq, alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_114_135_135_le

/-! ## Main: the disc proof in K-form -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9.** The tuple `(11/4, 11/4, 11/4)`
    is an α₃-discontinuity. -/
theorem alphaK_11o4_11o4_11o4_isDiscontinuityK :
    IsDiscontinuityK (![(11,4),(11,4),(11,4)] : FracTuple 3) := by
  set v : FracTuple 3 := ![(11,4),(11,4),(11,4)] with hv_def
  have hv_valid : ValidK v := validK_11o4_11o4_11o4
  have hα_v : alphaK v = 13 := alphaK_11o4_11o4_11o4_eq
  intro u hu_valid hu_lt
  by_contra h_not_lt
  push_neg at h_not_lt
  -- αₖ-monotonicity: alphaK u ≤ alphaK v = 13.
  have hu_le_v : lePermK u v := hu_lt.1
  have hα_u_le : alphaK u ≤ alphaK v := alphaK_le_of_lePermK hu_valid hv_valid hu_le_v
  have hα_u : alphaK u = 13 := by
    rw [hα_v] at hα_u_le h_not_lt; omega
  -- Reduce u to coprime form.
  obtain ⟨u₀, hu₀_valid, hu₀_eq, hu₀_coprime⟩ := exists_coprime_form u hu_valid
  have hα_u₀ : alphaK u₀ = 13 := by
    rw [alphaK_eq_of_toRat_eq hu₀_valid hu_valid hu₀_eq, hα_u]
  -- Apply alphaK_attained_with_bounded_max to u₀.
  obtain ⟨u', hu'_valid, hu'_le_u₀, hu'_alpha, hu'_bound, hu'_coprime⟩ :=
    alphaK_attained_with_bounded_max hu₀_valid hu₀_coprime
  have hα_u' : alphaK u' = 13 := by rw [hu'_alpha, hα_u₀]
  -- Each (u' i).1 ≤ 13.
  have hu'_p_le : ∀ i, ((u' i).1 : ℕ) ≤ 13 := fun i => by
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
  -- u' has at least one slot ≠ (11, 4) (else multiset = v, contradicting strict <).
  have h_some_ne_11o4 : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) ≠ (11, 4) := by
    by_contra h_all
    push_neg at h_all
    have h_all_p : ∀ i, ((u' i).1 : ℕ) = 11 := fun i => (Prod.mk.inj (h_all i)).1
    have h_all_q : ∀ i, ((u' i).2 : ℕ) = 4 := fun i => (Prod.mk.inj (h_all i)).2
    have h_u'_toRat : ∀ i, FracTuple.toRat u' i = 11 / 4 := by
      intro i
      unfold FracTuple.toRat
      have hp : (((u' i).1 : ℕ) : ℚ) = 11 := by exact_mod_cast h_all_p i
      have hq : (((u' i).2 : ℕ) : ℚ) = 4 := by exact_mod_cast h_all_q i
      push_cast at hp hq ⊢
      rw [hp, hq]
    have h_v_toRat : ∀ i, FracTuple.toRat v i = 11 / 4 := by
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
  by_cases h_caseA : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (5, 2)
  · -- ## Case A: some slot is (5, 2). Permute to slot 0.
    obtain ⟨i₀, hi₀⟩ := h_caseA
    have hi₀_p : ((u' i₀).1 : ℕ) = 5 := (Prod.mk.inj hi₀).1
    have hi₀_q : ((u' i₀).2 : ℕ) = 2 := (Prod.mk.inj hi₀).2
    set τ : Equiv.Perm (Fin 3) := Equiv.swap i₀ 0 with hτ_def
    set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
    have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
    have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
    have hu_a_0_p : ((u_a 0).1 : ℕ) = 5 := by
      change ((u' (τ 0)).1 : ℕ) = 5
      rw [hτ_def, Equiv.swap_apply_right]; exact hi₀_p
    have hu_a_0_q : ((u_a 0).2 : ℕ) = 2 := by
      change ((u' (τ 0)).2 : ℕ) = 2
      rw [hτ_def, Equiv.swap_apply_right]; exact hi₀_q
    have hu_a_1_mem : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
    have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs := hu'_in_allowed _
    have h_bound : alphaK u' ≤ nestedFloor3Nat 5 2
        ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ) ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
      rw [← hα_u_a]
      exact alphaK_le_nestedFloor_with_first hu_a_valid 5 2 hu_a_0_p hu_a_0_q
    have h_floor_le_12 := nestedFloor_caseA_5o2_first_le_12 hu_a_1_mem hu_a_2_mem
    have h_alpha_le_12 : alphaK u' ≤ 12 := h_bound.trans h_floor_le_12
    rw [hα_u'] at h_alpha_le_12
    omega
  · -- ## No slot is (5, 2).
    push_neg at h_caseA
    by_cases h_caseBN : ∃ i, (((u' i).1 : ℕ), ((u' i).2 : ℕ)) = (11, 4)
    · -- ## Case B-N: no slot is (5,2), some slot is (11,4).
      obtain ⟨i_114, hi_114⟩ := h_caseBN
      have hi_114_p : ((u' i_114).1 : ℕ) = 11 := (Prod.mk.inj hi_114).1
      have hi_114_q : ((u' i_114).2 : ℕ) = 4 := (Prod.mk.inj hi_114).2
      -- Permute (11, 4) to slot 0.
      set τ : Equiv.Perm (Fin 3) := Equiv.swap i_114 0 with hτ_def
      set u_a : FracTuple 3 := u' ∘ τ with hu_a_def
      have hu_a_valid : ValidK u_a := fun i => hu'_valid (τ i)
      have hα_u_a : alphaK u_a = alphaK u' := (alphaK_perm u' τ).symm
      have hu_a_0_p : ((u_a 0).1 : ℕ) = 11 := by
        change ((u' (τ 0)).1 : ℕ) = 11
        rw [hτ_def, Equiv.swap_apply_right]; exact hi_114_p
      have hu_a_0_q : ((u_a 0).2 : ℕ) = 4 := by
        change ((u' (τ 0)).2 : ℕ) = 4
        rw [hτ_def, Equiv.swap_apply_right]; exact hi_114_q
      have hu_a_1_mem : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ∈ allowedPairs :=
        hu'_in_allowed _
      have hu_a_2_mem : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ∈ allowedPairs :=
        hu'_in_allowed _
      have hu_a_1_ne_5o2 : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) ≠ (5, 2) := h_caseA _
      have hu_a_2_ne_5o2 : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) ≠ (5, 2) := h_caseA _
      -- Define "low" set and "high" set membership.
      -- low = {(2,1),(7,3),(9,4),(11,5),(12,5),(13,6)}
      -- high = {(8,3),(11,4),(13,5)} (since (5,2) is excluded)
      -- Each slot in 1, 2 is in either low or high ∪ {(5,2)}, and not (5,2),
      -- so in low ∪ high.
      have classify : ∀ (p q : ℕ), (p, q) ∈ allowedPairs → (p, q) ≠ (5, 2) →
          (((p, q) = (2, 1) ∨ (p, q) = (7, 3) ∨ (p, q) = (9, 4) ∨
            (p, q) = (11, 5) ∨ (p, q) = (12, 5) ∨ (p, q) = (13, 6)) ∨
           ((p, q) = (8, 3) ∨ (p, q) = (11, 4) ∨ (p, q) = (13, 5))) := by
        intro p q h_mem h_ne
        unfold allowedPairs at h_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
        rcases h_mem with h | h | h | h | h | h | h | h | h | h
        · left; left; exact h
        · exact absurd h h_ne
        · left; right; left; exact h
        · right; left; exact h
        · left; right; right; left; exact h
        · right; right; left; exact h
        · left; right; right; right; left; exact h
        · left; right; right; right; right; left; exact h
        · right; right; right; exact h
        · left; right; right; right; right; right; exact h
      -- Sub-case on whether some slot in {1, 2} is in low.
      by_cases h_caseBN1 : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (2, 1) ∨
          (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (7, 3) ∨
          (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (9, 4) ∨
          (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (11, 5) ∨
          (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (12, 5) ∨
          (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (13, 6)
      · -- Slot 1 (of u_a) is "low": apply nestedFloor_caseBN1_le_11.
        have h_bound : alphaK u' ≤ nestedFloor3Nat 11 4 ((u_a 1).1 : ℕ) ((u_a 1).2 : ℕ)
            ((u_a 2).1 : ℕ) ((u_a 2).2 : ℕ) := by
          rw [← hα_u_a]
          exact alphaK_le_nestedFloor_with_first hu_a_valid 11 4 hu_a_0_p hu_a_0_q
        have h_floor_le_11 := nestedFloor_caseBN1_le_11 h_caseBN1 hu_a_2_mem
        have h_alpha_le_11 : alphaK u' ≤ 11 := h_bound.trans h_floor_le_11
        rw [hα_u'] at h_alpha_le_11
        omega
      · -- Slot 1 is not low (relative to the "low" enumeration).
        push_neg at h_caseBN1
        obtain ⟨h_ne1_21, h_ne1_73, h_ne1_94, h_ne1_115, h_ne1_125, h_ne1_136⟩ :=
          h_caseBN1
        by_cases h_caseBN1' : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (2, 1) ∨
            (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (7, 3) ∨
            (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (9, 4) ∨
            (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (11, 5) ∨
            (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (12, 5) ∨
            (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (13, 6)
        · -- Slot 2 is "low": swap slot 1 ↔ slot 2 first.
          set ρ : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2 with hρ_def
          set u_b : FracTuple 3 := u_a ∘ ρ with hu_b_def
          have hu_b_valid : ValidK u_b := fun i => hu_a_valid (ρ i)
          have hα_u_b : alphaK u_b = alphaK u_a := (alphaK_perm u_a ρ).symm
          have hu_b_0_p : ((u_b 0).1 : ℕ) = 11 := by
            change ((u_a (ρ 0)).1 : ℕ) = 11
            rw [hρ_def, Equiv.swap_apply_of_ne_of_ne
              (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
            exact hu_a_0_p
          have hu_b_0_q : ((u_b 0).2 : ℕ) = 4 := by
            change ((u_a (ρ 0)).2 : ℕ) = 4
            rw [hρ_def, Equiv.swap_apply_of_ne_of_ne
              (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
            exact hu_a_0_q
          have hu_b_1_p : ((u_b 1).1 : ℕ) = ((u_a 2).1 : ℕ) := by
            change ((u_a (ρ 1)).1 : ℕ) = ((u_a 2).1 : ℕ)
            rw [hρ_def, Equiv.swap_apply_left]
          have hu_b_1_q : ((u_b 1).2 : ℕ) = ((u_a 2).2 : ℕ) := by
            change ((u_a (ρ 1)).2 : ℕ) = ((u_a 2).2 : ℕ)
            rw [hρ_def, Equiv.swap_apply_left]
          have hu_b_2_p : ((u_b 2).1 : ℕ) = ((u_a 1).1 : ℕ) := by
            change ((u_a (ρ 2)).1 : ℕ) = ((u_a 1).1 : ℕ)
            rw [hρ_def, Equiv.swap_apply_right]
          have hu_b_2_q : ((u_b 2).2 : ℕ) = ((u_a 1).2 : ℕ) := by
            change ((u_a (ρ 2)).2 : ℕ) = ((u_a 1).2 : ℕ)
            rw [hρ_def, Equiv.swap_apply_right]
          have hu_b_1_low : (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) = (2, 1) ∨
              (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) = (7, 3) ∨
              (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) = (9, 4) ∨
              (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) = (11, 5) ∨
              (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) = (12, 5) ∨
              (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) = (13, 6) := by
            rw [show (((u_b 1).1 : ℕ), ((u_b 1).2 : ℕ)) =
                  (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) from by rw [hu_b_1_p, hu_b_1_q]]
            exact h_caseBN1'
          have hu_b_2_mem : (((u_b 2).1 : ℕ), ((u_b 2).2 : ℕ)) ∈ allowedPairs := by
            rw [show (((u_b 2).1 : ℕ), ((u_b 2).2 : ℕ)) =
                  (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) from by rw [hu_b_2_p, hu_b_2_q]]
            exact hu_a_1_mem
          have h_bound : alphaK u' ≤ nestedFloor3Nat 11 4 ((u_b 1).1 : ℕ) ((u_b 1).2 : ℕ)
              ((u_b 2).1 : ℕ) ((u_b 2).2 : ℕ) := by
            rw [← hα_u_a, ← hα_u_b]
            exact alphaK_le_nestedFloor_with_first hu_b_valid 11 4 hu_b_0_p hu_b_0_q
          have h_floor_le_11 := nestedFloor_caseBN1_le_11 hu_b_1_low hu_b_2_mem
          have h_alpha_le_11 : alphaK u' ≤ 11 := h_bound.trans h_floor_le_11
          rw [hα_u'] at h_alpha_le_11
          omega
        · -- Both slot 1 and slot 2 are NOT in low. Combined with not-(5,2),
          -- they must be in high = {(8,3),(11,4),(13,5)}.
          push_neg at h_caseBN1'
          obtain ⟨h_ne2_21, h_ne2_73, h_ne2_94, h_ne2_115, h_ne2_125, h_ne2_136⟩ :=
            h_caseBN1'
          -- Slot 1 ∈ high.
          have hu_a_1_high : (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (8, 3) ∨
              (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (11, 4) ∨
              (((u_a 1).1 : ℕ), ((u_a 1).2 : ℕ)) = (13, 5) := by
            rcases classify _ _ hu_a_1_mem hu_a_1_ne_5o2 with h_low | h_high
            · rcases h_low with h | h | h | h | h | h
              · exact absurd h h_ne1_21
              · exact absurd h h_ne1_73
              · exact absurd h h_ne1_94
              · exact absurd h h_ne1_115
              · exact absurd h h_ne1_125
              · exact absurd h h_ne1_136
            · exact h_high
          have hu_a_2_high : (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (8, 3) ∨
              (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (11, 4) ∨
              (((u_a 2).1 : ℕ), ((u_a 2).2 : ℕ)) = (13, 5) := by
            rcases classify _ _ hu_a_2_mem hu_a_2_ne_5o2 with h_low | h_high
            · rcases h_low with h | h | h | h | h | h
              · exact absurd h h_ne2_21
              · exact absurd h h_ne2_73
              · exact absurd h h_ne2_94
              · exact absurd h h_ne2_115
              · exact absurd h h_ne2_125
              · exact absurd h h_ne2_136
            · exact h_high
          -- Now we case-split on slot 1 and slot 2 to identify the multiset.
          -- (u_a 0) = (11,4); (u_a 1) ∈ high; (u_a 2) ∈ high.
          -- We need to show: alphaK u' ≤ 12, i.e., contradict alpha = 13.
          -- 9 sub-cases (3 × 3), but (11,4),(11,4),(11,4) is excluded by strict <.
          -- Helper: get explicit (p, q) for slot 1 and 2.
          rcases hu_a_1_high with h1_83 | h1_114 | h1_135 <;>
            rcases hu_a_2_high with h2_83 | h2_114 | h2_135
          · -- (8,3),(8,3): u_a = (11,4),(8,3),(8,3). Permute to (8,3),(8,3),(11,4).
            -- Use swap (0, 2): u_c 0 = u_a 2 (=(8,3)), u_c 2 = u_a 0 (=(11,4)).
            set ρ' : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 2 with hρ'_def
            set u_c : FracTuple 3 := u_a ∘ ρ' with hu_c_def
            have hu_c_valid : ValidK u_c := fun i => hu_a_valid (ρ' i)
            have hα_u_c : alphaK u_c = alphaK u_a := (alphaK_perm u_a ρ').symm
            have hu_c_0_p : ((u_c 0).1 : ℕ) = 8 := by
              change ((u_a (ρ' 0)).1 : ℕ) = 8
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h2_83).1
            have hu_c_0_q : ((u_c 0).2 : ℕ) = 3 := by
              change ((u_a (ρ' 0)).2 : ℕ) = 3
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h2_83).2
            have hu_c_1_p : ((u_c 1).1 : ℕ) = 8 := by
              change ((u_a (ρ' 1)).1 : ℕ) = 8
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)]
              exact (Prod.mk.inj h1_83).1
            have hu_c_1_q : ((u_c 1).2 : ℕ) = 3 := by
              change ((u_a (ρ' 1)).2 : ℕ) = 3
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)]
              exact (Prod.mk.inj h1_83).2
            have hu_c_2_p : ((u_c 2).1 : ℕ) = 11 := by
              change ((u_a (ρ' 2)).1 : ℕ) = 11
              rw [hρ'_def, Equiv.swap_apply_right]
              exact hu_a_0_p
            have hu_c_2_q : ((u_c 2).2 : ℕ) = 4 := by
              change ((u_a (ρ' 2)).2 : ℕ) = 4
              rw [hρ'_def, Equiv.swap_apply_right]
              exact hu_a_0_q
            have h_bound : alphaK u_c ≤ 12 :=
              alphaK_le_12_of_83_83_114 hu_c_valid hu_c_0_p hu_c_0_q
                hu_c_1_p hu_c_1_q hu_c_2_p hu_c_2_q
            have : alphaK u' ≤ 12 := by rw [← hα_u_a, ← hα_u_c]; exact h_bound
            rw [hα_u'] at this; omega
          · -- (8,3),(11,4): u_a = (11,4),(8,3),(11,4). Permute to (8,3),(11,4),(11,4).
            -- Swap 0 ↔ 1: u_c 0 = u_a 1 (=(8,3)), u_c 1 = u_a 0 (=(11,4)).
            set ρ' : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1 with hρ'_def
            set u_c : FracTuple 3 := u_a ∘ ρ' with hu_c_def
            have hu_c_valid : ValidK u_c := fun i => hu_a_valid (ρ' i)
            have hα_u_c : alphaK u_c = alphaK u_a := (alphaK_perm u_a ρ').symm
            have hu_c_0_p : ((u_c 0).1 : ℕ) = 8 := by
              change ((u_a (ρ' 0)).1 : ℕ) = 8
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h1_83).1
            have hu_c_0_q : ((u_c 0).2 : ℕ) = 3 := by
              change ((u_a (ρ' 0)).2 : ℕ) = 3
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h1_83).2
            have hu_c_1_p : ((u_c 1).1 : ℕ) = 11 := by
              change ((u_a (ρ' 1)).1 : ℕ) = 11
              rw [hρ'_def, Equiv.swap_apply_right]
              exact hu_a_0_p
            have hu_c_1_q : ((u_c 1).2 : ℕ) = 4 := by
              change ((u_a (ρ' 1)).2 : ℕ) = 4
              rw [hρ'_def, Equiv.swap_apply_right]
              exact hu_a_0_q
            have hu_c_2_p : ((u_c 2).1 : ℕ) = 11 := by
              change ((u_a (ρ' 2)).1 : ℕ) = 11
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
              exact (Prod.mk.inj h2_114).1
            have hu_c_2_q : ((u_c 2).2 : ℕ) = 4 := by
              change ((u_a (ρ' 2)).2 : ℕ) = 4
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
              exact (Prod.mk.inj h2_114).2
            have h_bound : alphaK u_c ≤ 12 :=
              alphaK_le_12_of_83_114_114 hu_c_valid hu_c_0_p hu_c_0_q
                hu_c_1_p hu_c_1_q hu_c_2_p hu_c_2_q
            have : alphaK u' ≤ 12 := by rw [← hα_u_a, ← hα_u_c]; exact h_bound
            rw [hα_u'] at this; omega
          · -- (8,3),(13,5): u_a = (11,4),(8,3),(13,5). Permute to (8,3),(11,4),(13,5).
            -- Swap 0 ↔ 1.
            set ρ' : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1 with hρ'_def
            set u_c : FracTuple 3 := u_a ∘ ρ' with hu_c_def
            have hu_c_valid : ValidK u_c := fun i => hu_a_valid (ρ' i)
            have hα_u_c : alphaK u_c = alphaK u_a := (alphaK_perm u_a ρ').symm
            have hu_c_0_p : ((u_c 0).1 : ℕ) = 8 := by
              change ((u_a (ρ' 0)).1 : ℕ) = 8
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h1_83).1
            have hu_c_0_q : ((u_c 0).2 : ℕ) = 3 := by
              change ((u_a (ρ' 0)).2 : ℕ) = 3
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h1_83).2
            have hu_c_1_p : ((u_c 1).1 : ℕ) = 11 := by
              change ((u_a (ρ' 1)).1 : ℕ) = 11
              rw [hρ'_def, Equiv.swap_apply_right]
              exact hu_a_0_p
            have hu_c_1_q : ((u_c 1).2 : ℕ) = 4 := by
              change ((u_a (ρ' 1)).2 : ℕ) = 4
              rw [hρ'_def, Equiv.swap_apply_right]
              exact hu_a_0_q
            have hu_c_2_p : ((u_c 2).1 : ℕ) = 13 := by
              change ((u_a (ρ' 2)).1 : ℕ) = 13
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
              exact (Prod.mk.inj h2_135).1
            have hu_c_2_q : ((u_c 2).2 : ℕ) = 5 := by
              change ((u_a (ρ' 2)).2 : ℕ) = 5
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
              exact (Prod.mk.inj h2_135).2
            have h_bound : alphaK u_c ≤ 12 :=
              alphaK_le_12_of_83_114_135 hu_c_valid hu_c_0_p hu_c_0_q
                hu_c_1_p hu_c_1_q hu_c_2_p hu_c_2_q
            have : alphaK u' ≤ 12 := by rw [← hα_u_a, ← hα_u_c]; exact h_bound
            rw [hα_u'] at this; omega
          · -- (11,4),(8,3): u_a = (11,4),(11,4),(8,3). Permute to (8,3),(11,4),(11,4).
            -- Swap 0 ↔ 2: u_c 0 = u_a 2 (=(8,3)), u_c 2 = u_a 0 (=(11,4)).
            set ρ' : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 2 with hρ'_def
            set u_c : FracTuple 3 := u_a ∘ ρ' with hu_c_def
            have hu_c_valid : ValidK u_c := fun i => hu_a_valid (ρ' i)
            have hα_u_c : alphaK u_c = alphaK u_a := (alphaK_perm u_a ρ').symm
            have hu_c_0_p : ((u_c 0).1 : ℕ) = 8 := by
              change ((u_a (ρ' 0)).1 : ℕ) = 8
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h2_83).1
            have hu_c_0_q : ((u_c 0).2 : ℕ) = 3 := by
              change ((u_a (ρ' 0)).2 : ℕ) = 3
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h2_83).2
            have hu_c_1_p : ((u_c 1).1 : ℕ) = 11 := by
              change ((u_a (ρ' 1)).1 : ℕ) = 11
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)]
              exact (Prod.mk.inj h1_114).1
            have hu_c_1_q : ((u_c 1).2 : ℕ) = 4 := by
              change ((u_a (ρ' 1)).2 : ℕ) = 4
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)]
              exact (Prod.mk.inj h1_114).2
            have hu_c_2_p : ((u_c 2).1 : ℕ) = 11 := by
              change ((u_a (ρ' 2)).1 : ℕ) = 11
              rw [hρ'_def, Equiv.swap_apply_right]
              exact hu_a_0_p
            have hu_c_2_q : ((u_c 2).2 : ℕ) = 4 := by
              change ((u_a (ρ' 2)).2 : ℕ) = 4
              rw [hρ'_def, Equiv.swap_apply_right]
              exact hu_a_0_q
            have h_bound : alphaK u_c ≤ 12 :=
              alphaK_le_12_of_83_114_114 hu_c_valid hu_c_0_p hu_c_0_q
                hu_c_1_p hu_c_1_q hu_c_2_p hu_c_2_q
            have : alphaK u' ≤ 12 := by rw [← hα_u_a, ← hα_u_c]; exact h_bound
            rw [hα_u'] at this; omega
          · -- (11,4),(11,4): u_a = (11,4),(11,4),(11,4). Excluded by strict <.
            exfalso
            obtain ⟨j, hj_ne⟩ := h_some_ne_11o4
            apply hj_ne
            -- u' j = u_a (τ.symm j) (since u_a = u' ∘ τ).
            have h_jeq : u' j = u_a (τ.symm j) := by
              change u' j = u' (τ (τ.symm j))
              rw [τ.apply_symm_apply]
            -- u_a k = (11, 4) for all k.
            have h_u_a_all : ∀ k : Fin 3,
                (((u_a k).1 : ℕ), ((u_a k).2 : ℕ)) = (11, 4) := by
              intro k
              fin_cases k
              · exact Prod.mk.injEq .. |>.mpr ⟨hu_a_0_p, hu_a_0_q⟩
              · exact h1_114
              · exact h2_114
            calc (((u' j).1 : ℕ), ((u' j).2 : ℕ))
                = (((u_a (τ.symm j)).1 : ℕ), ((u_a (τ.symm j)).2 : ℕ)) := by rw [h_jeq]
              _ = (11, 4) := h_u_a_all _
          · -- (11,4),(13,5): u_a = (11,4),(11,4),(13,5). Bridge directly.
            have hu_a_1_p : ((u_a 1).1 : ℕ) = 11 := (Prod.mk.inj h1_114).1
            have hu_a_1_q : ((u_a 1).2 : ℕ) = 4 := (Prod.mk.inj h1_114).2
            have hu_a_2_p : ((u_a 2).1 : ℕ) = 13 := (Prod.mk.inj h2_135).1
            have hu_a_2_q : ((u_a 2).2 : ℕ) = 5 := (Prod.mk.inj h2_135).2
            have h_bound : alphaK u_a ≤ 12 :=
              alphaK_le_12_of_114_114_135 hu_a_valid hu_a_0_p hu_a_0_q
                hu_a_1_p hu_a_1_q hu_a_2_p hu_a_2_q
            have : alphaK u' ≤ 12 := by rw [← hα_u_a]; exact h_bound
            rw [hα_u'] at this; omega
          · -- (13,5),(8,3): u_a = (11,4),(13,5),(8,3). Permute to (8,3),(11,4),(13,5).
            -- ρ' 0 = 2, ρ' 1 = 0, ρ' 2 = 1: cycle (0 2 1) = swap(0,1) ∘ swap(0,2).
            set ρ_a : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 2
            set ρ_b : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1
            set ρ' : Equiv.Perm (Fin 3) := ρ_b * ρ_a with hρ'_def
            set u_c : FracTuple 3 := u_a ∘ ρ' with hu_c_def
            have hu_c_valid : ValidK u_c := fun i => hu_a_valid (ρ' i)
            have hα_u_c : alphaK u_c = alphaK u_a := (alphaK_perm u_a ρ').symm
            have hρ'_0 : ρ' 0 = 2 := by decide
            have hρ'_1 : ρ' 1 = 0 := by decide
            have hρ'_2 : ρ' 2 = 1 := by decide
            have hu_c_0_p : ((u_c 0).1 : ℕ) = 8 := by
              change ((u_a (ρ' 0)).1 : ℕ) = 8
              rw [hρ'_0]; exact (Prod.mk.inj h2_83).1
            have hu_c_0_q : ((u_c 0).2 : ℕ) = 3 := by
              change ((u_a (ρ' 0)).2 : ℕ) = 3
              rw [hρ'_0]; exact (Prod.mk.inj h2_83).2
            have hu_c_1_p : ((u_c 1).1 : ℕ) = 11 := by
              change ((u_a (ρ' 1)).1 : ℕ) = 11
              rw [hρ'_1]; exact hu_a_0_p
            have hu_c_1_q : ((u_c 1).2 : ℕ) = 4 := by
              change ((u_a (ρ' 1)).2 : ℕ) = 4
              rw [hρ'_1]; exact hu_a_0_q
            have hu_c_2_p : ((u_c 2).1 : ℕ) = 13 := by
              change ((u_a (ρ' 2)).1 : ℕ) = 13
              rw [hρ'_2]; exact (Prod.mk.inj h1_135).1
            have hu_c_2_q : ((u_c 2).2 : ℕ) = 5 := by
              change ((u_a (ρ' 2)).2 : ℕ) = 5
              rw [hρ'_2]; exact (Prod.mk.inj h1_135).2
            have h_bound : alphaK u_c ≤ 12 :=
              alphaK_le_12_of_83_114_135 hu_c_valid hu_c_0_p hu_c_0_q
                hu_c_1_p hu_c_1_q hu_c_2_p hu_c_2_q
            have : alphaK u' ≤ 12 := by rw [← hα_u_a, ← hα_u_c]; exact h_bound
            rw [hα_u'] at this; omega
          · -- (13,5),(11,4): u_a = (11,4),(13,5),(11,4). Permute to (11,4),(11,4),(13,5).
            -- Swap 1 ↔ 2: u_c 1 = u_a 2 (=(11,4)), u_c 2 = u_a 1 (=(13,5)).
            set ρ' : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2 with hρ'_def
            set u_c : FracTuple 3 := u_a ∘ ρ' with hu_c_def
            have hu_c_valid : ValidK u_c := fun i => hu_a_valid (ρ' i)
            have hα_u_c : alphaK u_c = alphaK u_a := (alphaK_perm u_a ρ').symm
            have hu_c_0_p : ((u_c 0).1 : ℕ) = 11 := by
              change ((u_a (ρ' 0)).1 : ℕ) = 11
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
              exact hu_a_0_p
            have hu_c_0_q : ((u_c 0).2 : ℕ) = 4 := by
              change ((u_a (ρ' 0)).2 : ℕ) = 4
              rw [hρ'_def, Equiv.swap_apply_of_ne_of_ne
                (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
              exact hu_a_0_q
            have hu_c_1_p : ((u_c 1).1 : ℕ) = 11 := by
              change ((u_a (ρ' 1)).1 : ℕ) = 11
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h2_114).1
            have hu_c_1_q : ((u_c 1).2 : ℕ) = 4 := by
              change ((u_a (ρ' 1)).2 : ℕ) = 4
              rw [hρ'_def, Equiv.swap_apply_left]
              exact (Prod.mk.inj h2_114).2
            have hu_c_2_p : ((u_c 2).1 : ℕ) = 13 := by
              change ((u_a (ρ' 2)).1 : ℕ) = 13
              rw [hρ'_def, Equiv.swap_apply_right]
              exact (Prod.mk.inj h1_135).1
            have hu_c_2_q : ((u_c 2).2 : ℕ) = 5 := by
              change ((u_a (ρ' 2)).2 : ℕ) = 5
              rw [hρ'_def, Equiv.swap_apply_right]
              exact (Prod.mk.inj h1_135).2
            have h_bound : alphaK u_c ≤ 12 :=
              alphaK_le_12_of_114_114_135 hu_c_valid hu_c_0_p hu_c_0_q
                hu_c_1_p hu_c_1_q hu_c_2_p hu_c_2_q
            have : alphaK u' ≤ 12 := by rw [← hα_u_a, ← hα_u_c]; exact h_bound
            rw [hα_u'] at this; omega
          · -- (13,5),(13,5): u_a = (11,4),(13,5),(13,5). Bridge directly.
            have hu_a_1_p : ((u_a 1).1 : ℕ) = 13 := (Prod.mk.inj h1_135).1
            have hu_a_1_q : ((u_a 1).2 : ℕ) = 5 := (Prod.mk.inj h1_135).2
            have hu_a_2_p : ((u_a 2).1 : ℕ) = 13 := (Prod.mk.inj h2_135).1
            have hu_a_2_q : ((u_a 2).2 : ℕ) = 5 := (Prod.mk.inj h2_135).2
            have h_bound : alphaK u_a ≤ 12 :=
              alphaK_le_12_of_114_135_135 hu_a_valid hu_a_0_p hu_a_0_q
                hu_a_1_p hu_a_1_q hu_a_2_p hu_a_2_q
            have : alphaK u' ≤ 12 := by rw [← hα_u_a]; exact h_bound
            rw [hα_u'] at this; omega
    · -- ## Case B-R: no slot is (5, 2) AND no slot is (11, 4). All ratios < 11/4.
      push_neg at h_caseBN
      have hu'_strict : ∀ i, 4 * ((u' i).1 : ℕ) < 11 * ((u' i).2 : ℕ) := by
        intro i
        exact allowedPair_strict_of_ne_5o2_ne_11o4 (hu'_in_allowed i)
          (h_caseA i) (h_caseBN i)
      have h_alpha_le_12 : alphaK u' ≤ 12 := alphaK_le_12_of_all_lt_11o4 hu'_valid hu'_strict
      rw [hα_u'] at h_alpha_le_12
      omega

/-! ## FracTriple-form bridge -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Paper Theorem 6.9, FracTriple form.** -/
theorem alpha3_11o4_11o4_11o4_isDiscontinuity :
    IsDiscontinuity (![(11,4),(11,4),(11,4)] : FracTriple) :=
  (isDiscontinuity_iff_isDiscontinuityK ![(11,4),(11,4),(11,4)]).mpr
    alphaK_11o4_11o4_11o4_isDiscontinuityK

end Section6
