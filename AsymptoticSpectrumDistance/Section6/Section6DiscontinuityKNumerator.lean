/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# K-form of the numerator bound (paper Lemma 6.13)

Lifts `numerator_bound` (in `Section6NumeratorBound.lean`, FracTriple-shaped) to
`IsDiscontinuityK` form. Result: if `v : FracTuple 3` is `α₃`-discontinuous,
each slot has denominator `≥ 2`, and each slot is in lowest terms, then
`max (v i).1 ≤ alphaK v`.

This is the paper's Lemma 6.13 (`lem:numerator-bound`). It's the foundational
piece for the bounded enumeration of discontinuity candidates.

## Main result

* `alphaK_ge_num_zero_of_isDiscontinuityK` : `(v 0).1 ≤ alphaK v` for
  `v : FracTuple 3` α₃-disc with `(v 0)` in lowest terms.
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge
import AsymptoticSpectrumDistance.Section6.Section6NumeratorBound

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## Numerator bound at slot 0

`alphaK v` written in right-associative form, then `numerator_bound` applies
directly. The contradiction with `IsDiscontinuityK` comes from constructing a
`v' <ₚ v` valid with `αₖ v ≤ αₖ v'`. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK v` equals the right-associated strongProduct form. -/
private lemma alphaK_three_right_assoc (v : FracTuple 3) :
    alphaK v =
      (strongProduct (fractionGraph (v 0).1 (v 0).2)
        (strongProduct (fractionGraph (v 1).1 (v 1).2)
          (fractionGraph (v 2).1 (v 2).2))).indepNum := by
  rw [alphaK_three]
  unfold alpha3
  exact ShannonCapacity.indepNum_strongProduct_assoc _ _ _

/-- The "perturbed" `FracTuple 3` with slot 0 replaced by `(a, b)`. -/
private def replaceAt0 (a b : ℕ+) (v : FracTuple 3) : FracTuple 3 :=
  ![(a, b), v 1, v 2]

@[simp] private lemma replaceAt0_zero (a b : ℕ+) (v : FracTuple 3) :
    (replaceAt0 a b v) 0 = (a, b) := rfl

@[simp] private lemma replaceAt0_one (a b : ℕ+) (v : FracTuple 3) :
    (replaceAt0 a b v) 1 = v 1 := rfl

@[simp] private lemma replaceAt0_two (a b : ℕ+) (v : FracTuple 3) :
    (replaceAt0 a b v) 2 = v 2 := rfl

/-- If `(a/b) < (v 0).toRat` strictly, then `replaceAt0 a b v <ₚ v`.
    Proof via id-permutation `lePermK` and a sum-of-rationals contradiction
    for the back direction. -/
private lemma replaceAt0_ltPermK {a b : ℕ+} {v : FracTuple 3}
    (h_lt : (a : ℚ) / b < ((v 0).1 : ℚ) / ((v 0).2 : ℚ)) :
    ltPermK (replaceAt0 a b v) v := by
  refine ⟨⟨1, fun i => ?_⟩, ?_⟩
  · -- lePermK (replaceAt0 a b v) v via id.
    fin_cases i
    · -- slot 0: (a/b).toRat ≤ (v 0).toRat (strict inequality).
      change ((a : ℚ) / b) ≤ ((v 0).1 : ℚ) / ((v 0).2 : ℚ)
      exact h_lt.le
    · change FracTuple.toRat (replaceAt0 a b v) 1 ≤ FracTuple.toRat v 1
      simp [FracTuple.toRat]
    · change FracTuple.toRat (replaceAt0 a b v) 2 ≤ FracTuple.toRat v 2
      simp [FracTuple.toRat]
  · -- ¬ lePermK v (replaceAt0 a b v): sum-of-rationals contradiction.
    rintro ⟨τ, hτ⟩
    -- ∀ i, (v (τ i)).toRat ≤ (replaceAt0 a b v) i.toRat.
    -- Sum LHS = sum (v i).toRat. Sum RHS = (a/b) + (v 1).toRat + (v 2).toRat.
    -- LHS - RHS = (v 0).toRat - (a/b) > 0. Contradiction.
    have h_sum_le : (∑ i, FracTuple.toRat v (τ i)) ≤
        (∑ i, FracTuple.toRat (replaceAt0 a b v) i) :=
      Finset.sum_le_sum (fun i _ => hτ i)
    have h_sum_eq : (∑ i, FracTuple.toRat v (τ i)) = (∑ i, FracTuple.toRat v i) :=
      Finset.sum_equiv τ (by simp) (fun _ _ => rfl)
    have h_replaceSum :
        (∑ i, FracTuple.toRat (replaceAt0 a b v) i) =
          (a : ℚ) / b + FracTuple.toRat v 1 + FracTuple.toRat v 2 := by
      simp [Fin.sum_univ_three, FracTuple.toRat]
    have h_vSum :
        (∑ i, FracTuple.toRat v i) =
          FracTuple.toRat v 0 + FracTuple.toRat v 1 + FracTuple.toRat v 2 := by
      simp [Fin.sum_univ_three]
    rw [h_sum_eq, h_vSum, h_replaceSum] at h_sum_le
    -- (v 0).toRat ≤ a/b. But h_lt says (v 0).toRat > a/b. Contradiction.
    have h_v0_le : FracTuple.toRat v 0 ≤ (a : ℚ) / b := by linarith
    unfold FracTuple.toRat at h_v0_le
    linarith

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Slot-0 form.** If `v : FracTuple 3` is `α₃`-discontinuous,
    `(v 0).2 ≥ 2` (the slot-0 denominator), and `(v 0)` is in lowest terms,
    then `(v 0).1 ≤ alphaK v`. -/
theorem alphaK_ge_num_zero_of_isDiscontinuityK
    {v : FracTuple 3} (hv_valid : ValidK v) (hv_disc : IsDiscontinuityK v)
    (h_q0_ge2 : 2 ≤ ((v 0).2 : ℕ))
    (h_coprime0 : Nat.Coprime ((v 0).1 : ℕ) ((v 0).2 : ℕ)) :
    ((v 0).1 : ℕ) ≤ alphaK v := by
  by_contra h_lt
  push_neg at h_lt
  -- h_lt : alphaK v < (v 0).1.
  have hα_form : alphaK v =
      (strongProduct (fractionGraph ((v 0).1 : ℕ) ((v 0).2 : ℕ))
        (strongProduct (fractionGraph ((v 1).1 : ℕ) ((v 1).2 : ℕ))
          (fractionGraph ((v 2).1 : ℕ) ((v 2).2 : ℕ)))).indepNum :=
    alphaK_three_right_assoc v
  rw [hα_form] at h_lt
  -- Apply numerator_bound (slot 0, k = 3).
  have h2q0_le : 2 * ((v 0).2 : ℕ) ≤ ((v 0).1 : ℕ) := by exact_mod_cast hv_valid 0
  have h2q1_le : 2 * ((v 1).2 : ℕ) ≤ ((v 1).1 : ℕ) := by exact_mod_cast hv_valid 1
  have h2q2_le : 2 * ((v 2).2 : ℕ) ≤ ((v 2).1 : ℕ) := by exact_mod_cast hv_valid 2
  obtain ⟨a, b, ha_pos, hb_pos, _ha_lt, h2b_le_a, _hab_coprime, hab_lt_q, hα_le⟩ :=
    numerator_bound ((v 0).1 : ℕ) ((v 0).2 : ℕ) ((v 1).1 : ℕ) ((v 1).2 : ℕ)
                    ((v 2).1 : ℕ) ((v 2).2 : ℕ)
      h_q0_ge2 h2q0_le h_coprime0
      (v 1).2.pos h2q1_le
      (v 2).2.pos h2q2_le
      h_lt
  -- Construct `v' : FracTuple 3` with `v' 0 = (a, b)`.
  haveI hp_a : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  set a_pn : ℕ+ := ⟨a, ha_pos⟩ with ha_pn_def
  set b_pn : ℕ+ := ⟨b, hb_pos⟩ with hb_pn_def
  set v' : FracTuple 3 := replaceAt0 a_pn b_pn v with hv'_def
  -- ValidK v'.
  have hv'_valid : ValidK v' := by
    intro i
    fin_cases i
    · change 2 * b ≤ a
      exact h2b_le_a
    · exact hv_valid 1
    · exact hv_valid 2
  -- v' <ₚ v.
  have hv'_lt_v : ltPermK v' v := by
    refine replaceAt0_ltPermK ?_
    change ((a_pn : ℚ) / b_pn) < ((v 0).1 : ℚ) / ((v 0).2 : ℚ)
    exact_mod_cast hab_lt_q
  -- αₖ v' < αₖ v by disc.
  have h_α_strict : alphaK v' < alphaK v := hv_disc v' hv'_valid hv'_lt_v
  -- alphaK v' in right-assoc form (defeq to (a/b ⊠ rest).indepNum since v' 0 = (a_pn, b_pn)).
  have hα_v' : alphaK v' =
      (strongProduct (fractionGraph a b)
        (strongProduct (fractionGraph ((v 1).1 : ℕ) ((v 1).2 : ℕ))
          (fractionGraph ((v 2).1 : ℕ) ((v 2).2 : ℕ)))).indepNum :=
    alphaK_three_right_assoc v'
  rw [hα_v', hα_form] at h_α_strict
  -- h_α_strict : (a/b ⊠ ...).indepNum < (p₀/q₀ ⊠ ...).indepNum.
  -- hα_le : (p₀/q₀ ⊠ ...).indepNum ≤ (a/b ⊠ ...).indepNum. Contradiction.
  exact absurd h_α_strict (not_lt.mpr hα_le)

/-! ## Max numerator over a `FracTuple 3` -/

/-- Max numerator over a FracTuple 3 (foundation for the descent argument
    in `alphaK_attained_with_bounded_max`). -/
def maxNumK (u : FracTuple 3) : ℕ :=
  max ((u 0).1 : ℕ) (max ((u 1).1 : ℕ) ((u 2).1 : ℕ))

@[simp] lemma maxNumK_at_zero (u : FracTuple 3) : ((u 0).1 : ℕ) ≤ maxNumK u := by
  unfold maxNumK; omega

@[simp] lemma maxNumK_at_one (u : FracTuple 3) : ((u 1).1 : ℕ) ≤ maxNumK u := by
  unfold maxNumK; omega

@[simp] lemma maxNumK_at_two (u : FracTuple 3) : ((u 2).1 : ℕ) ≤ maxNumK u := by
  unfold maxNumK; omega

/-- Each slot's numerator is at most the max. -/
lemma maxNumK_at_slot (u : FracTuple 3) (i : Fin 3) : ((u i).1 : ℕ) ≤ maxNumK u := by
  fin_cases i <;> simp

/-! ## Descent step (slot-0 form)

If `alphaK u < (u 0).1`, then by the existential form of `numerator_bound`,
we can replace slot 0 with a Stern-Brocot predecessor `(a, b)` to get
`u' ≤ₚ u` with `(u' 0).1 < (u 0).1` and `alphaK u' = alphaK u`. -/

lemma alphaK_descent_at_zero {u : FracTuple 3} (hu : ValidK u)
    (hq_ge2 : 2 ≤ ((u 0).2 : ℕ))
    (hcoprime : Nat.Coprime ((u 0).1 : ℕ) ((u 0).2 : ℕ))
    (h_big : alphaK u < (u 0).1) :
    ∃ u' : FracTuple 3, ValidK u' ∧ lePermK u' u ∧ alphaK u' = alphaK u ∧
      ((u' 0).1 : ℕ) < ((u 0).1 : ℕ) ∧
      u' 1 = u 1 ∧ u' 2 = u 2 ∧
      Nat.Coprime ((u' 0).1 : ℕ) ((u' 0).2 : ℕ) := by
  have hα_form : alphaK u =
      (strongProduct (fractionGraph ((u 0).1 : ℕ) ((u 0).2 : ℕ))
        (strongProduct (fractionGraph ((u 1).1 : ℕ) ((u 1).2 : ℕ))
          (fractionGraph ((u 2).1 : ℕ) ((u 2).2 : ℕ)))).indepNum := by
    rw [alphaK_three]
    unfold alpha3
    exact ShannonCapacity.indepNum_strongProduct_assoc _ _ _
  rw [hα_form] at h_big
  have h2q0_le : 2 * ((u 0).2 : ℕ) ≤ ((u 0).1 : ℕ) := by exact_mod_cast hu 0
  have h2q1_le : 2 * ((u 1).2 : ℕ) ≤ ((u 1).1 : ℕ) := by exact_mod_cast hu 1
  have h2q2_le : 2 * ((u 2).2 : ℕ) ≤ ((u 2).1 : ℕ) := by exact_mod_cast hu 2
  obtain ⟨a, b, ha_pos, hb_pos, ha_lt, h2b_le_a, hab_coprime, hab_lt_q, hα_le⟩ :=
    numerator_bound ((u 0).1 : ℕ) ((u 0).2 : ℕ) ((u 1).1 : ℕ) ((u 1).2 : ℕ)
                    ((u 2).1 : ℕ) ((u 2).2 : ℕ)
      hq_ge2 h2q0_le hcoprime
      (u 1).2.pos h2q1_le
      (u 2).2.pos h2q2_le
      h_big
  haveI hp_a : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  set a_pn : ℕ+ := ⟨a, ha_pos⟩
  set b_pn : ℕ+ := ⟨b, hb_pos⟩
  refine ⟨![(a_pn, b_pn), u 1, u 2], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · change 2 * b ≤ a; exact h2b_le_a
    · exact hu 1
    · exact hu 2
  · refine ⟨1, fun i => ?_⟩
    fin_cases i
    · change ((a_pn : ℚ) / b_pn) ≤ ((u 0).1 : ℚ) / ((u 0).2 : ℚ)
      have : ((a : ℚ) / b) < ((u 0).1 : ℚ) / ((u 0).2 : ℚ) := by exact_mod_cast hab_lt_q
      exact_mod_cast this.le
    · simp [FracTuple.toRat]
    · simp [FracTuple.toRat]
  · have h_α_u' : alphaK ![(a_pn, b_pn), u 1, u 2] =
        (strongProduct (fractionGraph a b)
          (strongProduct (fractionGraph ((u 1).1 : ℕ) ((u 1).2 : ℕ))
            (fractionGraph ((u 2).1 : ℕ) ((u 2).2 : ℕ)))).indepNum := by
      rw [alphaK_three]
      unfold alpha3
      exact ShannonCapacity.indepNum_strongProduct_assoc _ _ _
    rw [h_α_u', hα_form]
    apply le_antisymm
    · have ha_q : ((a : ℕ) : ℚ) / ((b : ℕ) : ℚ) ≤ ((u 0).1 : ℚ) / ((u 0).2 : ℚ) := by
        exact_mod_cast hab_lt_q.le
      have hq0_pos : (0 : ℚ) < ((u 0).2 : ℚ) := by exact_mod_cast (u 0).2.pos
      have hb_pos_q : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb_pos
      have h_le_nat : a * ((u 0).2 : ℕ) ≤ ((u 0).1 : ℕ) * b := by
        rw [div_le_div_iff₀ hb_pos_q hq0_pos] at ha_q
        exact_mod_cast ha_q
      have h_cohom : fractionGraph a b ≤_G fractionGraph ((u 0).1 : ℕ) ((u 0).2 : ℕ) :=
        cohom_fractionGraph_monotone a b ((u 0).1 : ℕ) ((u 0).2 : ℕ)
          hb_pos h2b_le_a (u 0).2.pos h2q0_le h_le_nat
      obtain ⟨f, hf⟩ := Cohom.strongProduct_left _ h_cohom
      exact independenceNumber_le_of_cohomomorphism _ _ f hf
    · exact hα_le
  · change a < ((u 0).1 : ℕ); exact ha_lt
  · rfl
  · rfl
  · -- Coprime at the new slot 0.
    change Nat.Coprime a b
    exact hab_coprime

/-- **Any-slot form (paper Lemma 6.13).** Reducing to slot 0 via
    `isDiscontinuityK_perm` + `alphaK_perm`. -/
theorem alphaK_ge_num_at_of_isDiscontinuityK
    {v : FracTuple 3} (hv_valid : ValidK v) (hv_disc : IsDiscontinuityK v)
    (i : Fin 3)
    (h_qi_ge2 : 2 ≤ ((v i).2 : ℕ))
    (h_coprimei : Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ)) :
    ((v i).1 : ℕ) ≤ alphaK v := by
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 i with hσ_def
  have hv'_valid : ValidK (v ∘ σ) := fun j => hv_valid (σ j)
  have hv'_disc : IsDiscontinuityK (v ∘ σ) := (isDiscontinuityK_perm σ).mp hv_disc
  have hv'_0 : (v ∘ σ) 0 = v i := by
    change v (σ 0) = v i
    rw [hσ_def, Equiv.swap_apply_left]
  have h_qi_ge2' : 2 ≤ (((v ∘ σ) 0).2 : ℕ) := by rw [hv'_0]; exact h_qi_ge2
  have h_coprime' : Nat.Coprime (((v ∘ σ) 0).1 : ℕ) (((v ∘ σ) 0).2 : ℕ) := by
    rw [hv'_0]; exact h_coprimei
  have h := alphaK_ge_num_zero_of_isDiscontinuityK hv'_valid hv'_disc h_qi_ge2' h_coprime'
  rw [hv'_0] at h
  rw [show alphaK v = alphaK (v ∘ σ) from alphaK_perm v σ]
  exact h

/-! ## Descent step (any-slot form)

Wrap `alphaK_descent_at_zero` with `Equiv.swap 0 j` to get the slot-`j`
generalization. Pattern matches `alphaK_ge_num_at_of_isDiscontinuityK`. -/

lemma alphaK_descent_at_slot {u : FracTuple 3} (hu : ValidK u) (j : Fin 3)
    (hq_ge2 : 2 ≤ ((u j).2 : ℕ))
    (hcoprime : Nat.Coprime ((u j).1 : ℕ) ((u j).2 : ℕ))
    (h_big : alphaK u < (u j).1) :
    ∃ u' : FracTuple 3, ValidK u' ∧ lePermK u' u ∧ alphaK u' = alphaK u ∧
      ((u' j).1 : ℕ) < ((u j).1 : ℕ) ∧
      (∀ i, i ≠ j → u' i = u i) ∧
      Nat.Coprime ((u' j).1 : ℕ) ((u' j).2 : ℕ) := by
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 j with hσ_def
  -- The "permuted-to-slot-0" version of u.
  have hu'_valid : ValidK (u ∘ σ) := fun i => hu (σ i)
  have hu_σ0 : (u ∘ σ) 0 = u j := by
    change u (σ 0) = u j
    rw [hσ_def, Equiv.swap_apply_left]
  have hq_ge2' : 2 ≤ (((u ∘ σ) 0).2 : ℕ) := by rw [hu_σ0]; exact hq_ge2
  have hcoprime' : Nat.Coprime (((u ∘ σ) 0).1 : ℕ) (((u ∘ σ) 0).2 : ℕ) := by
    rw [hu_σ0]; exact hcoprime
  have h_big' : alphaK (u ∘ σ) < ((u ∘ σ) 0).1 := by
    rw [hu_σ0, show alphaK (u ∘ σ) = alphaK u from (alphaK_perm u σ).symm]
    exact h_big
  obtain ⟨w, hw_valid, hw_le, hw_alpha, hw_lt, hw_one, hw_two, hw_coprime⟩ :=
    alphaK_descent_at_zero hu'_valid hq_ge2' hcoprime' h_big'
  -- Compose w with σ to get u' = w ∘ σ. Then `u' j = w 0`, and `u' i = u i` for `i ≠ j`.
  refine ⟨w ∘ σ, fun i => hw_valid (σ i), ?_, ?_, ?_, ?_, ?_⟩
  · -- lePermK (w ∘ σ) u from lePermK w (u ∘ σ).
    have h1 : lePermK w u := (lePermK_perm_right σ).mp hw_le
    exact (lePermK_perm_left σ).mpr h1
  · -- alphaK (w ∘ σ) = alphaK u.
    rw [show alphaK (w ∘ σ) = alphaK w from (alphaK_perm w σ).symm, hw_alpha,
        show alphaK (u ∘ σ) = alphaK u from (alphaK_perm u σ).symm]
  · -- ((w ∘ σ) j).1 < (u j).1, since (w ∘ σ) j = w (σ j) = w 0.
    change (w (σ j)).1 < (u j).1
    rw [hσ_def, Equiv.swap_apply_right]
    have : ((w 0).1 : ℕ) < (((u ∘ σ) 0).1 : ℕ) := hw_lt
    rw [hu_σ0] at this
    exact_mod_cast this
  · -- For i ≠ j, (w ∘ σ) i = u i.
    intro i hi
    -- Useful facts about σ.
    have hσ_0 : σ 0 = j := by rw [hσ_def]; exact Equiv.swap_apply_left 0 j
    have hσ_j : σ j = 0 := by rw [hσ_def]; exact Equiv.swap_apply_right 0 j
    have hσ_other : ∀ k : Fin 3, k ≠ 0 → k ≠ j → σ k = k := fun k h1 h2 => by
      rw [hσ_def]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
    -- hw_one, hw_two re-stated.
    have hw1 : w 1 = u (σ 1) := hw_one
    have hw2 : w 2 = u (σ 2) := hw_two
    -- Determine which of {0, 1, 2} j and i are.
    have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 := by
      have h := j.isLt
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
          · exact absurd h (Nat.not_lt_zero _)
          · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by
      have h := i.isLt
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
          · exact absurd h (Nat.not_lt_zero _)
          · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    change w (σ i) = u i
    rcases hj_cases with hj0 | hj1 | hj2
    · -- j = 0: σ = identity. Goal: w i = u i.
      have hσ_id : σ = Equiv.refl _ := by rw [hσ_def, hj0]; exact Equiv.swap_self 0
      rw [hσ_id]; change w i = u i
      rcases hi_cases with hi0 | hi1 | hi2
      · exact absurd (hi0.trans hj0.symm) hi
      · subst hi1
        have := hw1; rw [hσ_id] at this; exact this
      · subst hi2
        have := hw2; rw [hσ_id] at this; exact this
    · -- j = 1.
      subst hj1
      rcases hi_cases with hi0 | hi1 | hi2
      · -- i = 0. σ 0 = 1. Need: w 1 = u 0.
        subst hi0; rw [hσ_0]
        have := hw1; rw [hσ_j] at this; exact this
      · exact absurd hi1 hi
      · -- i = 2. σ 2 = 2.
        subst hi2
        rw [hσ_other 2 (by decide) (by decide)]
        have := hw2; rw [hσ_other 2 (by decide) (by decide)] at this; exact this
    · -- j = 2.
      subst hj2
      rcases hi_cases with hi0 | hi1 | hi2
      · -- i = 0. σ 0 = 2. Need: w 2 = u 0.
        subst hi0; rw [hσ_0]
        have := hw2; rw [hσ_j] at this; exact this
      · -- i = 1. σ 1 = 1.
        subst hi1
        rw [hσ_other 1 (by decide) (by decide)]
        have := hw1; rw [hσ_other 1 (by decide) (by decide)] at this; exact this
      · exact absurd hi2 hi
  · -- Coprime at slot j of u' = w ∘ σ. (w ∘ σ) j = w (σ j) = w 0.
    change Nat.Coprime ((w (σ j)).1 : ℕ) ((w (σ j)).2 : ℕ)
    rw [hσ_def, Equiv.swap_apply_right]
    exact hw_coprime

/-! ## Max-numerator slot helper -/

/-- A slot index where the numerator-max is attained. Implementation: ties broken
    in favor of the smallest slot. -/
def maxSlot (u : FracTuple 3) : Fin 3 :=
  if ((u 1).1 : ℕ) ≤ ((u 0).1 : ℕ) then
    if ((u 2).1 : ℕ) ≤ ((u 0).1 : ℕ) then 0 else 2
  else
    if ((u 2).1 : ℕ) ≤ ((u 1).1 : ℕ) then 1 else 2

/-- The numerator at `maxSlot u` equals `maxNumK u`. -/
lemma numAt_maxSlot (u : FracTuple 3) :
    ((u (maxSlot u)).1 : ℕ) = maxNumK u := by
  unfold maxSlot maxNumK
  split_ifs with h1 h2 h3 <;> omega

/-! ## αₖ-positivity (re-proved locally to avoid private dependency) -/

/-- Local re-proof of `0 < alphaK v` (needed below for the integer-slot case
    of the descent). Mirrors the proof in `Section6DiscontinuityK.lean`. -/
private lemma alphaK_pos_local {k : ℕ} (v : FracTuple k) : 0 < alphaK v := by
  classical
  unfold alphaK
  set G := bigStrongProduct (fun i : Fin k => fractionGraph ((v i).1 : ℕ) ((v i).2 : ℕ))
    with hG
  let x : ∀ i : Fin k, ZMod ((v i).1 : ℕ) := fun _ => 0
  have hsing : G.IsIndepSet (({x} : Finset _) : Set _) := by
    rw [SimpleGraph.IsIndepSet, Set.Pairwise]
    intro a ha b hb _
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
    exact G.loopless.irrefl x
  have hcard : ({x} : Finset _).card = 1 := Finset.card_singleton x
  have hle : ({x} : Finset _).card ≤ G.indepNum := hsing.card_le_indepNum
  omega

/-! ## Integer-slot bound

If `(u j).2 = 1`, then `(u j).1 ≤ alphaK u`. Proof: permute slot `j` to slot 0,
apply integer-factor formula `alphaK_consInt`, and use `alphaK rest ≥ 1`. -/

private lemma alphaK_ge_num_at_of_qOne {u : FracTuple 3} (j : Fin 3)
    (hu : ValidK u) (hq : ((u j).2 : ℕ) = 1) :
    ((u j).1 : ℕ) ≤ alphaK u := by
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 j with hσ_def
  -- (u ∘ σ) 0 = u j.
  have hu_σ0 : (u ∘ σ) 0 = u j := by
    change u (σ 0) = u j
    rw [hσ_def, Equiv.swap_apply_left]
  -- alphaK u = alphaK (u ∘ σ).
  have hα_eq : alphaK u = alphaK (u ∘ σ) := alphaK_perm u σ
  -- Express u ∘ σ as consInt ((u j).1) rest, where rest is (u ∘ σ) ∘ Fin.succ.
  set n : ℕ+ := (u j).1
  set rest : FracTuple 2 := fun i => (u ∘ σ) i.succ with hrest_def
  -- Establish u ∘ σ = consInt n rest.
  have h_eq : u ∘ σ = consInt n rest := by
    funext i
    cases i using Fin.cases with
    | zero =>
      change (u ∘ σ) 0 = consInt n rest 0
      rw [consInt_zero, hu_σ0]
      -- Need: u j = (n, 1). Since n = (u j).1 and (u j).2 = 1.
      ext
      · rfl
      · -- (u j).2 = 1.
        have : ((u j).2 : ℕ) = (1 : ℕ+) := by
          rw [hq]; rfl
        exact PNat.coe_inj.mp this
    | succ i' =>
      rw [consInt_succ]
  -- Now alphaK (u ∘ σ) = alphaK (consInt n rest) = n * alphaK rest.
  -- For consInt with n ≥ 2: alphaK_consInt. We have n ≥ 2 because hu gives 2 q ≤ p at slot j,
  -- and (u j).2 ≥ 1, so (u j).1 ≥ 2.
  have hn_ge2 : (2 : ℕ+) ≤ n := by
    -- 2 * (u j).2 ≤ (u j).1 = n, and (u j).2 ≥ 1, so 2 ≤ 2 * (u j).2 ≤ n.
    have h2q : 2 * ((u j).2 : ℕ) ≤ ((u j).1 : ℕ) := by exact_mod_cast hu j
    have hq_pos : 1 ≤ ((u j).2 : ℕ) := (u j).2.one_le
    change 2 ≤ ((u j).1 : ℕ+)
    have : 2 ≤ ((u j).1 : ℕ) := by omega
    exact_mod_cast this
  have h_alpha_consInt := alphaK_consInt n hn_ge2 rest
  rw [hα_eq, h_eq, h_alpha_consInt]
  -- Goal: ((u j).1 : ℕ) ≤ ↑n * alphaK rest. Since n = (u j).1.
  have h_rest_pos : 0 < alphaK rest := alphaK_pos_local rest
  -- n = (u j).1 (definitional set).
  change ((u j).1 : ℕ) ≤ (n : ℕ) * alphaK rest
  have : (n : ℕ) = ((u j).1 : ℕ) := rfl
  rw [this]
  -- (u j).1 ≤ (u j).1 * alphaK rest, since alphaK rest ≥ 1.
  exact Nat.le_mul_of_pos_right _ h_rest_pos

/-! ## `lePermK` transitivity (local helper) -/

private lemma lePermK_trans {k : ℕ} {u v w : FracTuple k}
    (h1 : lePermK u v) (h2 : lePermK v w) : lePermK u w := by
  obtain ⟨σ1, hσ1⟩ := h1
  obtain ⟨σ2, hσ2⟩ := h2
  refine ⟨σ1 * σ2, fun i => ?_⟩
  -- toRat u ((σ1 * σ2) i) = toRat u (σ1 (σ2 i)) ≤ toRat v (σ2 i) ≤ toRat w i.
  calc FracTuple.toRat u ((σ1 * σ2) i)
      = FracTuple.toRat u (σ1 (σ2 i)) := by rw [Equiv.Perm.mul_apply]
    _ ≤ FracTuple.toRat v (σ2 i) := hσ1 (σ2 i)
    _ ≤ FracTuple.toRat w i := hσ2 i

/-! ## Sum of numerators (induction measure)

We use sum-of-numerators rather than `maxNumK` to drive the induction, since
the descent step strictly decreases the sum at one slot but only weakly affects
the max (in case of ties). -/

/-- Sum of numerators across all 3 slots. -/
def sumNumK (u : FracTuple 3) : ℕ :=
  ((u 0).1 : ℕ) + ((u 1).1 : ℕ) + ((u 2).1 : ℕ)

/-- Each slot's numerator is at most the sum. -/
lemma maxNumK_le_sumNumK (u : FracTuple 3) : maxNumK u ≤ sumNumK u := by
  unfold maxNumK sumNumK; omega

/-! ## Main result: `αₖ` attained at a tuple with bounded numerators

For every valid coprime `u : FracTuple 3`, there exists `u'` with `u' ≤ₚ u`,
`alphaK u' = alphaK u`, and `(u' i).1 ≤ alphaK u'` for all `i`. -/

/-- Strong-induction core: for any natural `N`, every valid coprime
    `u : FracTuple 3` with `sumNumK u ≤ N` admits a bounded-max attained partner. -/
private lemma alphaK_attained_with_bounded_max_aux :
    ∀ N : ℕ, ∀ u : FracTuple 3, ValidK u →
      (∀ i, Nat.Coprime ((u i).1 : ℕ) ((u i).2 : ℕ)) →
      sumNumK u ≤ N →
      ∃ u' : FracTuple 3, ValidK u' ∧ lePermK u' u ∧ alphaK u' = alphaK u ∧
        (∀ i, ((u' i).1 : ℕ) ≤ alphaK u') ∧
        (∀ i, Nat.Coprime ((u' i).1 : ℕ) ((u' i).2 : ℕ)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro u hu hcoprime hsum
  by_cases h_base : maxNumK u ≤ alphaK u
  · -- Base: maxNumK u ≤ alphaK u. Take u' = u.
    refine ⟨u, hu, ⟨1, fun i => le_refl _⟩, rfl, ?_, hcoprime⟩
    intro i
    exact (maxNumK_at_slot u i).trans h_base
  · -- Step: pick j = maxSlot u; descend.
    push_neg at h_base
    set j := maxSlot u with hj_def
    have h_at_max : ((u j).1 : ℕ) = maxNumK u := numAt_maxSlot u
    have h_big : alphaK u < ((u j).1 : ℕ) := h_at_max ▸ h_base
    by_cases hq1 : ((u j).2 : ℕ) = 1
    · exfalso
      have h := alphaK_ge_num_at_of_qOne j hu hq1
      omega
    have hq_ge2 : 2 ≤ ((u j).2 : ℕ) := by
      have := (u j).2.pos; omega
    have h_big_pn : alphaK u < ((u j).1 : ℕ+) := by exact_mod_cast h_big
    obtain ⟨v, hv_valid, hv_le, hv_alpha, hv_lt, hv_others, hv_coprime⟩ :=
      alphaK_descent_at_slot hu j hq_ge2 (hcoprime j) h_big_pn
    have hsum_v : sumNumK v < sumNumK u := by
      unfold sumNumK
      have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 := by
        have h := j.isLt
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
          · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
            · exact absurd h (Nat.not_lt_zero _)
            · exact Or.inl (Fin.ext h)
          · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases hj_cases with hj0 | hj1 | hj2
      · have h0 : ((v 0).1 : ℕ) < ((u 0).1 : ℕ) := hj0 ▸ hv_lt
        have h1 : v 1 = u 1 := hv_others 1 (by rw [hj0]; decide)
        have h2 : v 2 = u 2 := hv_others 2 (by rw [hj0]; decide)
        rw [h1, h2]; omega
      · have h1 : ((v 1).1 : ℕ) < ((u 1).1 : ℕ) := hj1 ▸ hv_lt
        have h0 : v 0 = u 0 := hv_others 0 (by rw [hj1]; decide)
        have h2 : v 2 = u 2 := hv_others 2 (by rw [hj1]; decide)
        rw [h0, h2]; omega
      · have h2 : ((v 2).1 : ℕ) < ((u 2).1 : ℕ) := hj2 ▸ hv_lt
        have h0 : v 0 = u 0 := hv_others 0 (by rw [hj2]; decide)
        have h1 : v 1 = u 1 := hv_others 1 (by rw [hj2]; decide)
        rw [h0, h1]; omega
    have hv_coprime_all : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ) := by
      intro i
      by_cases hi : i = j
      · subst hi; exact hv_coprime
      · rw [hv_others i hi]; exact hcoprime i
    -- Apply IH at sumNumK v < sumNumK u ≤ N.
    have hv_lt_N : sumNumK v < N := lt_of_lt_of_le hsum_v hsum
    -- Use sumNumK v as the strict-decrease index.
    obtain ⟨w, hw_valid, hw_le, hw_alpha, hw_bound, hw_coprime⟩ :=
      ih (sumNumK v) hv_lt_N v hv_valid hv_coprime_all (le_refl _)
    refine ⟨w, hw_valid, lePermK_trans hw_le hv_le, ?_, hw_bound, hw_coprime⟩
    rw [hw_alpha, hv_alpha]

/-! ## Main result: `αₖ` attained at a tuple with bounded numerators

For every valid coprime `u : FracTuple 3`, there exists `u'` with `u' ≤ₚ u`,
`alphaK u' = alphaK u`, and `(u' i).1 ≤ alphaK u'` for all `i`. -/

theorem alphaK_attained_with_bounded_max {u : FracTuple 3} (hu : ValidK u)
    (hcoprime : ∀ i, Nat.Coprime ((u i).1 : ℕ) ((u i).2 : ℕ)) :
    ∃ u' : FracTuple 3, ValidK u' ∧ lePermK u' u ∧ alphaK u' = alphaK u ∧
      (∀ i, ((u' i).1 : ℕ) ≤ alphaK u') ∧
      (∀ i, Nat.Coprime ((u' i).1 : ℕ) ((u' i).2 : ℕ)) :=
  alphaK_attained_with_bounded_max_aux (sumNumK u) u hu hcoprime (le_refl _)

end Section6
