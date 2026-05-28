/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# α₂ converse classification (Theorem 6.9 at k = 2)

Discharges the hypothesis `Section6.Alpha2Classification` of
`Section6.theorem_6_9_unconditional_of_alpha2_classification`. Every
α₂-discontinuity in `(ℚ ∩ [2, 3])²` (in lowest terms) matches one of the 4
paper-canonical α₂-disc multisets up to permutation:
`{(2, 2), (2, 3), (3, 3), (5/2, 5/2)}`.

## Strategy

1. **k = 2 numerator bound** (`numerator_bound_two`): replicates
   `Section6.numerator_bound` with `H = fractionGraph p₂ q₂` (instead of a
   strong product of two fraction graphs).

2. **`alphaK v ≤ 9`** for `v` valid + `≤ 3`. Combined with (1), each `q ≥ 2`
   slot has `p ≤ 9`, restricting to `{(5, 2), (7, 3), (8, 3), (9, 4)}`.
   With `q = 1` slots, each is `(2, 1)` or `(3, 1)`. Total: 6 candidates
   per slot.

3. **Per-pair classification**: 36 = 6×6 ordered pairs. Each is either a
   canonical multiset or has an explicit non-disc witness `u <ₚ v` with
   `alphaK u ≥ alphaK v`.

## Main result

* `Section6.alpha2_classification` — the proven `Alpha2Classification`.
-/
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKConverse
import AsymptoticSpectrumDistance.Section6.Section6NumeratorBound

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

open AsymptoticSpectrumDistance Lemma66

/-! ## k = 2 numerator bound (analog of `numerator_bound`) -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Lemma 6.13 (contrapositive, k = 2).** If
    `α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) < p₁`, then there exist `a, b` with
    `a/b < p₁/q₁`, `2b ≤ a`, `gcd(a, b) = 1`, and replacing `p₁/q₁` with
    `a/b` does not decrease the independence number. Direct k = 2 analog of
    `Section6.numerator_bound`. -/
theorem numerator_bound_two (p₁ q₁ p₂ q₂ : ℕ)
    [NeZero p₁] [NeZero p₂]
    (hq₁ : 2 ≤ q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hcop₁ : Nat.Coprime p₁ q₁)
    (_hq₂ : 0 < q₂) (_h2q₂ : 2 * q₂ ≤ p₂)
    (hp₁_big :
      (strongProduct (fractionGraph p₁ q₁) (fractionGraph p₂ q₂)).indepNum < p₁) :
    ∃ (a b : ℕ) (ha : 0 < a) (_hb : 0 < b),
      a < p₁ ∧ 2 * b ≤ a ∧ Nat.Coprime a b ∧
      (a : ℚ) / b < (p₁ : ℚ) / q₁ ∧
      haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
      (strongProduct (fractionGraph p₁ q₁) (fractionGraph p₂ q₂)).indepNum ≤
      (strongProduct (fractionGraph a b) (fractionGraph p₂ q₂)).indepNum := by
  set G := strongProduct (fractionGraph p₁ q₁) (fractionGraph p₂ q₂) with hG_def
  set H := fractionGraph p₂ q₂
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_indep : G.IsIndepSet ↑S := (SimpleGraph.isMaximumIndepSet_iff G S).1 hSmax |>.1
  have hS_card : S.card = G.indepNum :=
    SimpleGraph.maximumIndepSet_card_eq_indepNum S hSmax
  have hS_lt_p₁ : S.card < p₁ := hS_card ▸ hp₁_big
  obtain ⟨v, hv⟩ := exists_fst_not_mem_image p₁ S hS_lt_p₁
  have hp₁_pos : 0 < p₁ := NeZero.pos p₁
  have hq₁_pos : 0 < q₁ := by omega
  have hpq : q₁ < p₁ := Nat.lt_of_lt_of_le (by omega : q₁ < 2 * q₁) h2q₁
  obtain ⟨a, b, ha_pos, ha_lt_p₁, hb_pos, hb_lt_q₁, hbezout⟩ :=
    sternBrocotPredecessor_exists p₁ q₁ hp₁_pos hq₁ hcop₁ hpq
  haveI ha_ne : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  have hab_coprime : Nat.Coprime a b := coprime_p'_q' hbezout
  have hab_lt : (a : ℚ) / b < (p₁ : ℚ) / q₁ :=
    sternBrocot_predecessor_lt p₁ q₁ a b ha_lt_p₁ hb_lt_q₁ hb_pos hbezout
  have ha_ge2 : 2 ≤ a := by
    by_contra ha_lt2
    push_neg at ha_lt2
    have ha_eq1 : a = 1 := by omega
    rw [ha_eq1] at hbezout
    have hpb : p₁ * b = q₁ + 1 := by omega
    have hb_le1 : b ≤ 1 := by
      have hle : p₁ * b ≤ p₁ * 1 := by
        calc p₁ * b = q₁ + 1 := hpb
          _ ≤ q₁ + q₁ := by omega
          _ = 2 * q₁ := by ring
          _ ≤ p₁ := h2q₁
          _ = p₁ * 1 := by ring
      exact Nat.le_of_mul_le_mul_left hle (by omega : 0 < p₁)
    have hb_eq1 : b = 1 := by omega
    rw [hb_eq1] at hpb; omega
  have h2b_le_a : 2 * b ≤ a :=
    two_q'_le_p'_of_bezout ha_pos ha_ge2 hb_pos hb_lt_q₁ hq₁ h2q₁ hbezout
  obtain ⟨a', b', ha'_pos, hb'_pos, ha'_lt, hb'_lt, hbezout',
    ⟨f_sub, hf_sub⟩, _⟩ :=
    fractionGraph_remove_vertex_equiv p₁ q₁ hq₁ h2q₁ hcop₁ v
  haveI : NeZero a' := ⟨Nat.pos_iff_ne_zero.mp ha'_pos⟩
  have ⟨ha'_eq, hb'_eq⟩ := sternBrocotPredecessor_unique p₁ q₁ a' b' a b hcop₁
    ha'_pos ha'_lt hb'_pos hb'_lt ha_pos ha_lt_p₁ hb_pos hb_lt_q₁ hbezout' hbezout
  let f' : ZMod p₁ → ZMod a := fun x =>
    if h : x = v then 0
    else ha'_eq ▸ f_sub ⟨x, h⟩
  have hf'_partial : ∀ u₁ u₂ : ZMod p₁, u₁ ≠ v → u₂ ≠ v → u₁ ≠ u₂ →
      ¬(fractionGraph p₁ q₁).Adj u₁ u₂ →
      f' u₁ ≠ f' u₂ ∧ ¬(fractionGraph a b).Adj (f' u₁) (f' u₂) := by
    intro u₁ u₂ hu₁ hu₂ hne hnadj
    simp only [f', hu₁, hu₂, dif_neg, not_false_eq_true]
    have hne_sub : (⟨u₁, hu₁⟩ : {x : ZMod p₁ | x ≠ v}) ≠ ⟨u₂, hu₂⟩ := by
      intro h; exact hne (Subtype.mk.inj h)
    have hnadj_ind : ¬((fractionGraph p₁ q₁).induce {x : ZMod p₁ | x ≠ v}).Adj
        ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ := by
      simp only [SimpleGraph.induce_adj, Set.mem_setOf_eq, ne_eq]
      exact fun hadj => hnadj hadj
    have h := hf_sub ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ hne_sub hnadj_ind
    subst ha'_eq; subst hb'_eq
    exact h
  have hbound := indepNum_ge_of_partial_cohom H f' v hf'_partial S hS_indep hv
  use a, b, ha_pos, hb_pos, ha_lt_p₁, h2b_le_a, hab_coprime, hab_lt
  calc G.indepNum = S.card := hS_card.symm
    _ ≤ (strongProduct (fractionGraph a b) H).indepNum := hbound

/-! ## `alphaK` for `FracTuple 2` is the strongProduct of two fraction graphs -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_two_eq (v : FracTuple 2) :
    alphaK v =
      (strongProduct (fractionGraph ((v 0).1 : ℕ) ((v 0).2 : ℕ))
        (fractionGraph ((v 1).1 : ℕ) ((v 1).2 : ℕ))).indepNum := by
  rw [alphaK_two]; rfl

/-! ## Permutations of `Fin 2`: every σ is `1` or `Equiv.swap 0 1` -/

private lemma perm_fin_two_cases (σ : Equiv.Perm (Fin 2)) :
    σ = 1 ∨ σ = Equiv.swap 0 1 := by
  revert σ
  decide

/-! ## Slot-0 numerator bound at k = 2 in `alphaK` form -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For an α₂-disc `v : FracTuple 2` valid + lowest-terms, with slot 0
    satisfying `(v 0).2 ≥ 2`, we have `(v 0).1 ≤ alphaK v`. -/
theorem alphaK_two_ge_num_zero_of_isDiscontinuityK
    {v : FracTuple 2} (hv_valid : ValidK v) (hv_disc : IsDiscontinuityK v)
    (h_q0_ge2 : 2 ≤ ((v 0).2 : ℕ))
    (h_coprime0 : Nat.Coprime ((v 0).1 : ℕ) ((v 0).2 : ℕ)) :
    ((v 0).1 : ℕ) ≤ alphaK v := by
  by_contra h_lt
  push_neg at h_lt
  rw [alphaK_two_eq] at h_lt
  have h2q0_le : 2 * ((v 0).2 : ℕ) ≤ ((v 0).1 : ℕ) := by exact_mod_cast hv_valid 0
  have h2q1_le : 2 * ((v 1).2 : ℕ) ≤ ((v 1).1 : ℕ) := by exact_mod_cast hv_valid 1
  obtain ⟨a, b, ha_pos, hb_pos, ha_lt, h2b_le_a, hab_coprime, hab_lt_q, hα_le⟩ :=
    numerator_bound_two ((v 0).1 : ℕ) ((v 0).2 : ℕ) ((v 1).1 : ℕ) ((v 1).2 : ℕ)
      h_q0_ge2 h2q0_le h_coprime0 (v 1).2.pos h2q1_le h_lt
  haveI hp_a : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  set a_pn : ℕ+ := ⟨a, ha_pos⟩
  set b_pn : ℕ+ := ⟨b, hb_pos⟩
  set v' : FracTuple 2 := ![(a_pn, b_pn), v 1] with hv'_def
  have hv'_valid : ValidK v' := by
    intro i; fin_cases i
    · change 2 * b ≤ a; exact h2b_le_a
    · exact hv_valid 1
  have h_v'0 : FracTuple.toRat v' 0 = (a : ℚ) / b := by
    simp [FracTuple.toRat, v', a_pn, b_pn]
  have h_v'1 : FracTuple.toRat v' 1 = ((v 1).1 : ℚ) / ((v 1).2 : ℚ) := by
    simp [FracTuple.toRat, v']
  have h_ab_lt_v0 : (a : ℚ) / b < FracTuple.toRat v 0 := by
    change (a : ℚ) / b < ((v 0).1 : ℚ) / ((v 0).2 : ℚ)
    exact_mod_cast hab_lt_q
  have hv'_lt_v : ltPermK v' v := by
    refine ⟨⟨1, fun i => ?_⟩, ?_⟩
    · simp only [Equiv.Perm.coe_one, id_eq]
      fin_cases i
      · change FracTuple.toRat v' 0 ≤ FracTuple.toRat v 0
        rw [h_v'0]; exact h_ab_lt_v0.le
      · change FracTuple.toRat v' 1 ≤ FracTuple.toRat v 1
        rw [h_v'1]; rfl
    · intro ⟨σ, hσ⟩
      have h00 : FracTuple.toRat v (σ 0) ≤ FracTuple.toRat v' 0 := hσ 0
      have h11 : FracTuple.toRat v (σ 1) ≤ FracTuple.toRat v' 1 := hσ 1
      rcases perm_fin_two_cases σ with hσ_eq | hσ_eq
      · rw [hσ_eq] at h00 h11
        simp only [Equiv.Perm.coe_one, id_eq] at h00 h11
        rw [h_v'0] at h00
        linarith
      · rw [hσ_eq] at h00 h11
        rw [Equiv.swap_apply_left] at h00
        rw [Equiv.swap_apply_right] at h11
        rw [h_v'0] at h00
        rw [h_v'1] at h11
        -- h00 : v.toRat 1 ≤ a/b
        -- h11 : v.toRat 0 ≤ (v 1).1 / (v 1).2 = v.toRat 1
        -- h_ab_lt_v0 : a/b < v.toRat 0
        change FracTuple.toRat v 0 ≤ ((v 1).1 : ℚ) / ((v 1).2 : ℚ) at h11
        have h_v1 : ((v 1).1 : ℚ) / ((v 1).2 : ℚ) = FracTuple.toRat v 1 := rfl
        rw [h_v1] at h11
        linarith
  have h_α_strict : alphaK v' < alphaK v := hv_disc v' hv'_valid hv'_lt_v
  have hα_v' : alphaK v' =
      (strongProduct (fractionGraph a b)
        (fractionGraph ((v 1).1 : ℕ) ((v 1).2 : ℕ))).indepNum := by
    rw [alphaK_two_eq]; rfl
  rw [hα_v', alphaK_two_eq] at h_α_strict
  exact absurd h_α_strict (not_lt.mpr hα_le)

/-- Any-slot form. -/
theorem alphaK_two_ge_num_at_of_isDiscontinuityK
    {v : FracTuple 2} (hv_valid : ValidK v) (hv_disc : IsDiscontinuityK v)
    (i : Fin 2) (h_qi_ge2 : 2 ≤ ((v i).2 : ℕ))
    (h_coprimei : Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ)) :
    ((v i).1 : ℕ) ≤ alphaK v := by
  set σ : Equiv.Perm (Fin 2) := Equiv.swap 0 i with hσ_def
  have hv'_valid : ValidK (v ∘ σ) := fun j => hv_valid (σ j)
  have hv'_disc : IsDiscontinuityK (v ∘ σ) := (isDiscontinuityK_perm σ).mp hv_disc
  have hv'_0 : (v ∘ σ) 0 = v i := by
    change v (σ 0) = v i
    rw [hσ_def, Equiv.swap_apply_left]
  have h_qi_ge2' : 2 ≤ (((v ∘ σ) 0).2 : ℕ) := by rw [hv'_0]; exact h_qi_ge2
  have h_coprime' : Nat.Coprime (((v ∘ σ) 0).1 : ℕ) (((v ∘ σ) 0).2 : ℕ) := by
    rw [hv'_0]; exact h_coprimei
  have h := alphaK_two_ge_num_zero_of_isDiscontinuityK hv'_valid hv'_disc
    h_qi_ge2' h_coprime'
  rw [hv'_0] at h
  rw [show alphaK v = alphaK (v ∘ σ) from alphaK_perm v σ]
  exact h

/-! ## Upper bound `alphaK v ≤ 9` for `v : FracTuple 2` in `[2, 3]²` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For `v : FracTuple 2` valid with each `toRat v i ≤ 3`, `alphaK v ≤ 9`. -/
theorem alphaK_two_le_9 {v : FracTuple 2} (hv_valid : ValidK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3) :
    alphaK v ≤ 9 := by
  set v33 : FracTuple 2 := ![(3, 1), (3, 1)] with hv33_def
  have h33_valid : ValidK v33 := by intro i; fin_cases i <;> decide
  have h_le : lePermK v v33 := by
    refine ⟨1, fun i => ?_⟩
    simp only [Equiv.Perm.coe_one, id_eq]
    fin_cases i
    · change FracTuple.toRat v 0 ≤ FracTuple.toRat v33 0
      have : FracTuple.toRat v33 0 = 3 := by simp [FracTuple.toRat, v33]
      rw [this]; exact hv_le3 0
    · change FracTuple.toRat v 1 ≤ FracTuple.toRat v33 1
      have : FracTuple.toRat v33 1 = 3 := by simp [FracTuple.toRat, v33]
      rw [this]; exact hv_le3 1
  have h_α_le : alphaK v ≤ alphaK v33 :=
    alphaK_le_of_lePermK hv_valid h33_valid h_le
  have h_α_v33 : alphaK v33 = 9 := by
    rw [alphaK_two]
    change alpha2 pair33 = 9
    exact alpha2_pair33_eq
  rw [h_α_v33] at h_α_le
  exact h_α_le

/-! ## The 6 candidates per slot -/

/-- The 6 candidate `(p, q)` pairs at k = 2 (per slot). -/
def candList : List (ℕ+ × ℕ+) :=
  [((2 : ℕ+), (1 : ℕ+)), ((3 : ℕ+), (1 : ℕ+)),
   ((5 : ℕ+), (2 : ℕ+)), ((7 : ℕ+), (3 : ℕ+)),
   ((8 : ℕ+), (3 : ℕ+)), ((9 : ℕ+), (4 : ℕ+))]

-- The `omega` fallback inside the nested `first` block is reached in some
-- interval_cases branches where the goal is already `False`; disable the
-- unusedTactic linter for this declaration so the fallback can stand.
set_option linter.unusedTactic false in
theorem slot_in_candList
    {v : FracTuple 2} (hv_valid : ValidK v) (hv_disc : IsDiscontinuityK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3)
    (hv_coprime : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ))
    (i : Fin 2) :
    v i ∈ candList := by
  have h_pq_pos : 0 < ((v i).1 : ℕ) ∧ 0 < ((v i).2 : ℕ) :=
    ⟨(v i).1.pos, (v i).2.pos⟩
  have h2q_le_p : 2 * ((v i).2 : ℕ) ≤ ((v i).1 : ℕ) := by exact_mod_cast hv_valid i
  have h_le3_nat : ((v i).1 : ℕ) ≤ 3 * ((v i).2 : ℕ) := by
    have h := hv_le3 i
    unfold FracTuple.toRat at h
    have hq_pos_q : (0 : ℚ) < ((v i).2 : ℚ) := by exact_mod_cast (v i).2.pos
    rw [div_le_iff₀ hq_pos_q] at h
    exact_mod_cast h
  have h_cop : Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ) := hv_coprime i
  by_cases hq : 2 ≤ ((v i).2 : ℕ)
  · have h_α_le_9 : alphaK v ≤ 9 := alphaK_two_le_9 hv_valid hv_le3
    have h_pi : ((v i).1 : ℕ) ≤ alphaK v :=
      alphaK_two_ge_num_at_of_isDiscontinuityK hv_valid hv_disc i hq h_cop
    have h_pi_le_9 : ((v i).1 : ℕ) ≤ 9 := le_trans h_pi h_α_le_9
    have h_q_le_4 : ((v i).2 : ℕ) ≤ 4 := by omega
    have hq2 := hq
    have h_vi_pn : v i = (⟨((v i).1 : ℕ), h_pq_pos.1⟩, ⟨((v i).2 : ℕ), h_pq_pos.2⟩) := by
      apply Prod.ext
      · apply PNat.coe_inj.mp; rfl
      · apply PNat.coe_inj.mp; rfl
    -- Possible (p, q) values: (5,2), (7,3), (8,3), (9,4).
    interval_cases ((v i).2 : ℕ) <;>
      interval_cases ((v i).1 : ℕ) <;>
      first
        | -- coprimality fails
          (exfalso; revert h_cop; decide)
        | -- p ∉ valid range, kill via omega
          (exfalso; omega)
        | -- valid: write v i in canonical form and match in candList.
          (rw [h_vi_pn]
           simp only [candList, List.mem_cons, List.not_mem_nil, or_false]
           first
             | (right; right; left; rfl)
             | (right; right; right; left; rfl)
             | (right; right; right; right; left; rfl)
             | (right; right; right; right; right; rfl))
  · push_neg at hq
    have hq1 : ((v i).2 : ℕ) = 1 := by
      have hp1 : (1 : ℕ) ≤ ((v i).2 : ℕ) := (v i).2.pos
      omega
    rw [hq1] at h2q_le_p h_le3_nat
    have hp_in : ((v i).1 : ℕ) = 2 ∨ ((v i).1 : ℕ) = 3 := by omega
    have h_vi_q : (v i).2 = 1 := by
      apply PNat.coe_inj.mp; exact hq1
    rcases hp_in with hp2 | hp3
    · have h_vi_p : (v i).1 = 2 := by apply PNat.coe_inj.mp; exact hp2
      have h_vi : v i = ((2 : ℕ+), (1 : ℕ+)) := Prod.ext h_vi_p h_vi_q
      rw [h_vi]
      simp [candList]
    · have h_vi_p : (v i).1 = 3 := by apply PNat.coe_inj.mp; exact hp3
      have h_vi : v i = ((3 : ℕ+), (1 : ℕ+)) := Prod.ext h_vi_p h_vi_q
      rw [h_vi]
      simp [candList]

/-! ## αₖ values for the canonical and witness tuples -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(2, 1), (2, 1)] = 4`. -/
lemma alphaK_22_pn :
    alphaK (![((2 : ℕ+), (1 : ℕ+)), ((2, 1) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]
  change alpha2 pair22 = 4
  unfold alpha2 pair22
  change (fractionGraph 2 1 ⊠ fractionGraph 2 1).indepNum = 4
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  rw [fractionGraph_one_indepNum 2 (by omega)]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(2, 1), (3, 1)] = 6`. -/
lemma alphaK_23_pn :
    alphaK (![((2 : ℕ+), (1 : ℕ+)), ((3, 1) : ℕ+ × ℕ+)] : FracTuple 2) = 6 := by
  rw [alphaK_two]
  change alpha2 pair23 = 6
  exact alpha2_pair23_eq

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(3, 1), (3, 1)] = 9`. -/
lemma alphaK_33_pn :
    alphaK (![((3 : ℕ+), (1 : ℕ+)), ((3, 1) : ℕ+ × ℕ+)] : FracTuple 2) = 9 := by
  rw [alphaK_two]
  change alpha2 pair33 = 9
  exact alpha2_pair33_eq

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK ![(5, 2), (5, 2)] = 5`. -/
lemma alphaK_5o2_5o2_pn :
    alphaK (![((5 : ℕ+), (2 : ℕ+)), ((5, 2) : ℕ+ × ℕ+)] : FracTuple 2) = 5 := by
  rw [alphaK_two]
  change alpha2 pair5o2_5o2 = 5
  exact alpha2_pair5o2_5o2_eq

/-! ## Helper: build a `lePermK` witness with `σ = 1` from pointwise `≤` -/

private lemma lePermK_id (u v : FracTuple 2)
    (h0 : FracTuple.toRat u 0 ≤ FracTuple.toRat v 0)
    (h1 : FracTuple.toRat u 1 ≤ FracTuple.toRat v 1) :
    lePermK u v := by
  refine ⟨1, fun i => ?_⟩
  simp only [Equiv.Perm.coe_one, id_eq]
  fin_cases i
  · exact h0
  · exact h1

/-- Build `¬ lePermK v u` from contradictions in both σ = 1 and σ = swap. -/
private lemma not_lePermK_two (u v : FracTuple 2)
    (h_id : ¬ (FracTuple.toRat v 0 ≤ FracTuple.toRat u 0 ∧
                FracTuple.toRat v 1 ≤ FracTuple.toRat u 1))
    (h_swap : ¬ (FracTuple.toRat v 1 ≤ FracTuple.toRat u 0 ∧
                  FracTuple.toRat v 0 ≤ FracTuple.toRat u 1)) :
    ¬ lePermK v u := by
  intro ⟨σ, hσ⟩
  have h0 := hσ 0
  have h1 := hσ 1
  rcases perm_fin_two_cases σ with hσ_eq | hσ_eq
  · rw [hσ_eq] at h0 h1
    simp only [Equiv.Perm.coe_one, id_eq] at h0 h1
    exact h_id ⟨h0, h1⟩
  · rw [hσ_eq] at h0 h1
    rw [Equiv.swap_apply_left] at h0
    rw [Equiv.swap_apply_right] at h1
    exact h_swap ⟨h0, h1⟩

/-! ## Witness templates -/

private def witness22 : FracTuple 2 := ![((2 : ℕ+), (1 : ℕ+)), ((2, 1) : ℕ+ × ℕ+)]
private def witness23 : FracTuple 2 := ![((2 : ℕ+), (1 : ℕ+)), ((3, 1) : ℕ+ × ℕ+)]
private def witness5o2_5o2 : FracTuple 2 :=
  ![((5 : ℕ+), (2 : ℕ+)), ((5, 2) : ℕ+ × ℕ+)]

private lemma witness22_valid : ValidK witness22 := by
  intro i; fin_cases i <;> decide
private lemma witness23_valid : ValidK witness23 := by
  intro i; fin_cases i <;> decide
private lemma witness5o2_5o2_valid : ValidK witness5o2_5o2 := by
  intro i; fin_cases i <;> decide

private lemma alphaK_witness22 : alphaK witness22 = 4 := alphaK_22_pn
private lemma alphaK_witness23 : alphaK witness23 = 6 := alphaK_23_pn
private lemma alphaK_witness5o2_5o2 : alphaK witness5o2_5o2 = 5 := alphaK_5o2_5o2_pn

/-! ## Key non-disc lemma: if `u ≤ₚ v`, `¬ v ≤ₚ u`, and `alphaK u ≥ alphaK v`,
    then `v` is not an α-discontinuity. -/

private lemma not_isDisc_of_witness {v u : FracTuple 2}
    (hu_valid : ValidK u)
    (h_le : lePermK u v) (h_nle : ¬ lePermK v u)
    (h_α : alphaK v ≤ alphaK u) :
    ¬ IsDiscontinuityK v := by
  intro hv_disc
  have h_lt : ltPermK u v := ⟨h_le, h_nle⟩
  have := hv_disc u hu_valid h_lt
  omega

/-! ## αₖ values for q≥2 candidate slots: α(E_{p_i/q_i}) = 2

For our 4 q≥2 candidates (5/2, 7/3, 8/3, 9/4), the independence number of
the corresponding `fractionGraph` is 2. This follows from `⌊p/q⌋ = 2` and a
2-element independent set witness. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma indepNum_fractionGraph_5_2 : (fractionGraph 5 2).indepNum = 2 := by
  apply le_antisymm
  · have h := fractionGraph_indepNum_le 5 2 (by omega) (by omega)
    have h_floor : ⌊((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)⌋₊ = 2 := by
      apply (Nat.floor_eq_iff (by norm_num)).mpr
      refine ⟨by norm_num, by norm_num⟩
    omega
  · have h_set : (fractionGraph 5 2).IsIndepSet ({0, 2} : Set (ZMod 5)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne hadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        (first | (exact hne rfl) |
          (revert hadj; simp only [fractionGraph, distMod, ne_eq]; decide))
    have h_card : ({0, 2} : Finset (ZMod 5)).card = 2 := by decide
    calc 2 = ({0, 2} : Finset (ZMod 5)).card := h_card.symm
      _ ≤ (fractionGraph 5 2).indepNum := by
          apply SimpleGraph.IsIndepSet.card_le_indepNum
          convert h_set using 0
          simp [Finset.coe_insert, Finset.coe_singleton]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma indepNum_fractionGraph_7_3 : (fractionGraph 7 3).indepNum = 2 := by
  apply le_antisymm
  · have h := fractionGraph_indepNum_le 7 3 (by omega) (by omega)
    have h_floor : ⌊((7 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)⌋₊ = 2 := by
      apply (Nat.floor_eq_iff (by norm_num)).mpr
      refine ⟨by norm_num, by norm_num⟩
    omega
  · have h_set : (fractionGraph 7 3).IsIndepSet ({0, 3} : Set (ZMod 7)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne hadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        (first | (exact hne rfl) |
          (revert hadj; simp only [fractionGraph, distMod, ne_eq]; decide))
    have h_card : ({0, 3} : Finset (ZMod 7)).card = 2 := by decide
    calc 2 = ({0, 3} : Finset (ZMod 7)).card := h_card.symm
      _ ≤ (fractionGraph 7 3).indepNum := by
          apply SimpleGraph.IsIndepSet.card_le_indepNum
          convert h_set using 0
          simp [Finset.coe_insert, Finset.coe_singleton]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma indepNum_fractionGraph_8_3 : (fractionGraph 8 3).indepNum = 2 := by
  apply le_antisymm
  · have h := fractionGraph_indepNum_le 8 3 (by omega) (by omega)
    have h_floor : ⌊((8 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)⌋₊ = 2 := by
      apply (Nat.floor_eq_iff (by norm_num)).mpr
      refine ⟨by norm_num, by norm_num⟩
    omega
  · have h_set : (fractionGraph 8 3).IsIndepSet ({0, 3} : Set (ZMod 8)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne hadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        (first | (exact hne rfl) |
          (revert hadj; simp only [fractionGraph, distMod, ne_eq]; decide))
    have h_card : ({0, 3} : Finset (ZMod 8)).card = 2 := by decide
    calc 2 = ({0, 3} : Finset (ZMod 8)).card := h_card.symm
      _ ≤ (fractionGraph 8 3).indepNum := by
          apply SimpleGraph.IsIndepSet.card_le_indepNum
          convert h_set using 0
          simp [Finset.coe_insert, Finset.coe_singleton]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma indepNum_fractionGraph_9_4 : (fractionGraph 9 4).indepNum = 2 := by
  apply le_antisymm
  · have h := fractionGraph_indepNum_le 9 4 (by omega) (by omega)
    have h_floor : ⌊((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)⌋₊ = 2 := by
      apply (Nat.floor_eq_iff (by norm_num)).mpr
      refine ⟨by norm_num, by norm_num⟩
    omega
  · have h_set : (fractionGraph 9 4).IsIndepSet ({0, 4} : Set (ZMod 9)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne hadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        (first | (exact hne rfl) |
          (revert hadj; simp only [fractionGraph, distMod, ne_eq]; decide))
    have h_card : ({0, 4} : Finset (ZMod 9)).card = 2 := by decide
    calc 2 = ({0, 4} : Finset (ZMod 9)).card := h_card.symm
      _ ≤ (fractionGraph 9 4).indepNum := by
          apply SimpleGraph.IsIndepSet.card_le_indepNum
          convert h_set using 0
          simp [Finset.coe_insert, Finset.coe_singleton]

/-! ## αₖ values for each (v 0, v 1) pair from candList × candList

Naming: `alphaK_<p₀>_<q₀>_<p₁>_<q₁>` where (p_i, q_i) follows the candList. -/

-- Pure integer pairs (4):
-- αₖ ((2,1)(2,1)) = 4 -- canonical
-- αₖ ((2,1)(3,1)) = 6 -- canonical
-- αₖ ((3,1)(2,1)) = 6 -- canonical via swap
-- αₖ ((3,1)(3,1)) = 9 -- canonical

-- (2,1) × q≥2 pairs (4 cases × 2 orderings = 8):
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_2_5o2 :
    alphaK (![((2 : ℕ+), (1 : ℕ+)), ((5, 2) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 2 1) ⊠ (fractionGraph 5 2)).indepNum = 4
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega), indepNum_fractionGraph_5_2]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_2_7o3 :
    alphaK (![((2 : ℕ+), (1 : ℕ+)), ((7, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 2 1) ⊠ (fractionGraph 7 3)).indepNum = 4
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega), indepNum_fractionGraph_7_3]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_2_8o3 :
    alphaK (![((2 : ℕ+), (1 : ℕ+)), ((8, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 2 1) ⊠ (fractionGraph 8 3)).indepNum = 4
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega), indepNum_fractionGraph_8_3]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_2_9o4 :
    alphaK (![((2 : ℕ+), (1 : ℕ+)), ((9, 4) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 2 1) ⊠ (fractionGraph 9 4)).indepNum = 4
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega), indepNum_fractionGraph_9_4]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_3_5o2 :
    alphaK (![((3 : ℕ+), (1 : ℕ+)), ((5, 2) : ℕ+ × ℕ+)] : FracTuple 2) = 6 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 3 1) ⊠ (fractionGraph 5 2)).indepNum = 6
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega), indepNum_fractionGraph_5_2]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_3_7o3 :
    alphaK (![((3 : ℕ+), (1 : ℕ+)), ((7, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 6 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 3 1) ⊠ (fractionGraph 7 3)).indepNum = 6
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega), indepNum_fractionGraph_7_3]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_3_8o3 :
    alphaK (![((3 : ℕ+), (1 : ℕ+)), ((8, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 6 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 3 1) ⊠ (fractionGraph 8 3)).indepNum = 6
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega), indepNum_fractionGraph_8_3]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_3_9o4 :
    alphaK (![((3 : ℕ+), (1 : ℕ+)), ((9, 4) : ℕ+ × ℕ+)] : FracTuple 2) = 6 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 3 1) ⊠ (fractionGraph 9 4)).indepNum = 6
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega), indepNum_fractionGraph_9_4]

-- swap forms: (p, 1) × (a, b) → (a, b) × (p, 1) (use indepNum_strongProduct_comm)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_5o2_2 :
    alphaK (![((5, 2) : ℕ+ × ℕ+), ((2 : ℕ+), (1 : ℕ+))] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 5 2) ⊠ (fractionGraph 2 1)).indepNum = 4
  rw [indepNum_strongProduct_comm, indepNum_strongProduct_edgeless_fraction 2 (by omega),
      indepNum_fractionGraph_5_2]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_7o3_2 :
    alphaK (![((7, 3) : ℕ+ × ℕ+), ((2 : ℕ+), (1 : ℕ+))] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 7 3) ⊠ (fractionGraph 2 1)).indepNum = 4
  rw [indepNum_strongProduct_comm, indepNum_strongProduct_edgeless_fraction 2 (by omega),
      indepNum_fractionGraph_7_3]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_8o3_2 :
    alphaK (![((8, 3) : ℕ+ × ℕ+), ((2 : ℕ+), (1 : ℕ+))] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 8 3) ⊠ (fractionGraph 2 1)).indepNum = 4
  rw [indepNum_strongProduct_comm, indepNum_strongProduct_edgeless_fraction 2 (by omega),
      indepNum_fractionGraph_8_3]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_9o4_2 :
    alphaK (![((9, 4) : ℕ+ × ℕ+), ((2 : ℕ+), (1 : ℕ+))] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 9 4) ⊠ (fractionGraph 2 1)).indepNum = 4
  rw [indepNum_strongProduct_comm, indepNum_strongProduct_edgeless_fraction 2 (by omega),
      indepNum_fractionGraph_9_4]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_5o2_3 :
    alphaK (![((5, 2) : ℕ+ × ℕ+), ((3 : ℕ+), (1 : ℕ+))] : FracTuple 2) = 6 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 5 2) ⊠ (fractionGraph 3 1)).indepNum = 6
  rw [indepNum_strongProduct_comm, indepNum_strongProduct_edgeless_fraction 3 (by omega),
      indepNum_fractionGraph_5_2]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_7o3_3 :
    alphaK (![((7, 3) : ℕ+ × ℕ+), ((3 : ℕ+), (1 : ℕ+))] : FracTuple 2) = 6 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 7 3) ⊠ (fractionGraph 3 1)).indepNum = 6
  rw [indepNum_strongProduct_comm, indepNum_strongProduct_edgeless_fraction 3 (by omega),
      indepNum_fractionGraph_7_3]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_8o3_3 :
    alphaK (![((8, 3) : ℕ+ × ℕ+), ((3 : ℕ+), (1 : ℕ+))] : FracTuple 2) = 6 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 8 3) ⊠ (fractionGraph 3 1)).indepNum = 6
  rw [indepNum_strongProduct_comm, indepNum_strongProduct_edgeless_fraction 3 (by omega),
      indepNum_fractionGraph_8_3]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_9o4_3 :
    alphaK (![((9, 4) : ℕ+ × ℕ+), ((3 : ℕ+), (1 : ℕ+))] : FracTuple 2) = 6 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 9 4) ⊠ (fractionGraph 3 1)).indepNum = 6
  rw [indepNum_strongProduct_comm, indepNum_strongProduct_edgeless_fraction 3 (by omega),
      indepNum_fractionGraph_9_4]

/-! ## αₖ for q≥2 × q≥2 pairs, computed via theorem_6_5 -/

/-- Helper: simplify ⌊p/q⌋ for our 4 candidates. -/
private lemma floor_5o2 : ⌊((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)⌋₊ = 2 := by
  apply (Nat.floor_eq_iff (by norm_num)).mpr
  refine ⟨by norm_num, by norm_num⟩
private lemma floor_7o3 : ⌊((7 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)⌋₊ = 2 := by
  apply (Nat.floor_eq_iff (by norm_num)).mpr
  refine ⟨by norm_num, by norm_num⟩
private lemma floor_8o3 : ⌊((8 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)⌋₊ = 2 := by
  apply (Nat.floor_eq_iff (by norm_num)).mpr
  refine ⟨by norm_num, by norm_num⟩
private lemma floor_9o4 : ⌊((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)⌋₊ = 2 := by
  apply (Nat.floor_eq_iff (by norm_num)).mpr
  refine ⟨by norm_num, by norm_num⟩

/-- Helper: floor of `p/q · 2` for our 4 candidates. -/
private lemma floor_5o2_2 : ⌊((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)⌋₊ = 5 := by
  have heq : (((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) = 5 := by push_cast; ring
  rw [heq]; simp
private lemma floor_7o3_2 : ⌊((7 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)⌋₊ = 4 := by
  apply (Nat.floor_eq_iff (by norm_num)).mpr
  refine ⟨by push_cast; norm_num, by push_cast; norm_num⟩
private lemma floor_8o3_2 : ⌊((8 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)⌋₊ = 5 := by
  apply (Nat.floor_eq_iff (by norm_num)).mpr
  refine ⟨by push_cast; norm_num, by push_cast; norm_num⟩
private lemma floor_9o4_2 : ⌊((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)⌋₊ = 4 := by
  apply (Nat.floor_eq_iff (by norm_num)).mpr
  refine ⟨by push_cast; norm_num, by push_cast; norm_num⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_5o2_7o3 :
    alphaK (![((5, 2) : ℕ+ × ℕ+), ((7, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 5 2) ⊠ (fractionGraph 7 3)).indepNum = 4
  rw [theorem_6_5 5 2 7 3 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_5o2, floor_7o3, floor_5o2_2, floor_7o3_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_5o2_8o3 :
    alphaK (![((5, 2) : ℕ+ × ℕ+), ((8, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 5 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 5 2) ⊠ (fractionGraph 8 3)).indepNum = 5
  rw [theorem_6_5 5 2 8 3 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_5o2, floor_8o3, floor_5o2_2, floor_8o3_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_5o2_9o4 :
    alphaK (![((5, 2) : ℕ+ × ℕ+), ((9, 4) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 5 2) ⊠ (fractionGraph 9 4)).indepNum = 4
  rw [theorem_6_5 5 2 9 4 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_5o2, floor_9o4, floor_5o2_2, floor_9o4_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_7o3_7o3 :
    alphaK (![((7, 3) : ℕ+ × ℕ+), ((7, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 7 3) ⊠ (fractionGraph 7 3)).indepNum = 4
  rw [theorem_6_5 7 3 7 3 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_7o3, floor_7o3_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_7o3_8o3 :
    alphaK (![((7, 3) : ℕ+ × ℕ+), ((8, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 7 3) ⊠ (fractionGraph 8 3)).indepNum = 4
  rw [theorem_6_5 7 3 8 3 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_7o3, floor_8o3, floor_7o3_2, floor_8o3_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_7o3_9o4 :
    alphaK (![((7, 3) : ℕ+ × ℕ+), ((9, 4) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 7 3) ⊠ (fractionGraph 9 4)).indepNum = 4
  rw [theorem_6_5 7 3 9 4 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_7o3, floor_9o4, floor_7o3_2, floor_9o4_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_8o3_8o3 :
    alphaK (![((8, 3) : ℕ+ × ℕ+), ((8, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 5 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 8 3) ⊠ (fractionGraph 8 3)).indepNum = 5
  rw [theorem_6_5 8 3 8 3 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_8o3, floor_8o3_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_8o3_9o4 :
    alphaK (![((8, 3) : ℕ+ × ℕ+), ((9, 4) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 8 3) ⊠ (fractionGraph 9 4)).indepNum = 4
  rw [theorem_6_5 8 3 9 4 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_8o3, floor_9o4, floor_8o3_2, floor_9o4_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_9o4_9o4 :
    alphaK (![((9, 4) : ℕ+ × ℕ+), ((9, 4) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two]; unfold alpha2
  change ((fractionGraph 9 4) ⊠ (fractionGraph 9 4)).indepNum = 4
  rw [theorem_6_5 9 4 9 4 (by omega) (by omega) (by omega) (by omega)]
  rw [floor_9o4, floor_9o4_2]; rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Symmetry of `alphaK` under tuple swap (k = 2). -/
private lemma alphaK_two_swap (a b : ℕ+ × ℕ+) :
    alphaK (![a, b] : FracTuple 2) = alphaK (![b, a] : FracTuple 2) := by
  rw [alphaK_two_eq, alphaK_two_eq]
  change ((fractionGraph (a.1 : ℕ) (a.2 : ℕ)) ⊠ (fractionGraph (b.1 : ℕ) (b.2 : ℕ))).indepNum =
         ((fractionGraph (b.1 : ℕ) (b.2 : ℕ)) ⊠ (fractionGraph (a.1 : ℕ) (a.2 : ℕ))).indepNum
  exact indepNum_strongProduct_comm _ _

-- swap forms for q≥2 × q≥2 cases
private lemma alphaK_7o3_5o2 :
    alphaK (![((7, 3) : ℕ+ × ℕ+), ((5, 2) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two_swap]; exact alphaK_5o2_7o3
private lemma alphaK_8o3_5o2 :
    alphaK (![((8, 3) : ℕ+ × ℕ+), ((5, 2) : ℕ+ × ℕ+)] : FracTuple 2) = 5 := by
  rw [alphaK_two_swap]; exact alphaK_5o2_8o3
private lemma alphaK_9o4_5o2 :
    alphaK (![((9, 4) : ℕ+ × ℕ+), ((5, 2) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two_swap]; exact alphaK_5o2_9o4
private lemma alphaK_8o3_7o3 :
    alphaK (![((8, 3) : ℕ+ × ℕ+), ((7, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two_swap]; exact alphaK_7o3_8o3
private lemma alphaK_9o4_7o3 :
    alphaK (![((9, 4) : ℕ+ × ℕ+), ((7, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two_swap]; exact alphaK_7o3_9o4
private lemma alphaK_9o4_8o3 :
    alphaK (![((9, 4) : ℕ+ × ℕ+), ((8, 3) : ℕ+ × ℕ+)] : FracTuple 2) = 4 := by
  rw [alphaK_two_swap]; exact alphaK_8o3_9o4

/-! ## The main classification: Alpha2Classification

For each of the 32 non-canonical (v 0, v 1) pairs in `candList × candList`,
we exhibit a witness `u <ₚ v` with `alphaK u ≥ alphaK v`. The 4 canonical
pairs go directly to `IsKnownDisc2Mod` matching. -/

set_option maxHeartbeats 1600000 in
-- 36 explicit case splits with per-case witness construction; needs raised limit.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **α₂ converse classification.** -/
theorem alpha2_classification : Alpha2Classification := by
  intro v hv_valid hv_le3 hv_coprime hv_disc
  have h0_cand : v 0 ∈ candList :=
    slot_in_candList hv_valid hv_disc hv_le3 hv_coprime 0
  have h1_cand : v 1 ∈ candList :=
    slot_in_candList hv_valid hv_disc hv_le3 hv_coprime 1
  simp only [candList, List.mem_cons, List.not_mem_nil, or_false] at h0_cand h1_cand
  have h_v_eq : v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [h_v_eq] at hv_disc ⊢
  rcases h0_cand with h0 | h0 | h0 | h0 | h0 | h0 <;>
    rcases h1_cand with h1 | h1 | h1 | h1 | h1 | h1 <;>
    (rw [h0, h1] at hv_disc ⊢)
  -- 36 cases; for each, either match canonical or apply not_isDisc_of_witness.
  -- Canonical cases:
  · -- (2,1)(2,1): canonical pair22.
    exact ⟨1, ![(2, 1), (2, 1)], by simp [knownDisc2List], by funext i; fin_cases i <;> rfl⟩
  · -- (2,1)(3,1): canonical pair23.
    exact ⟨1, ![(2, 1), (3, 1)], by simp [knownDisc2List], by funext i; fin_cases i <;> rfl⟩
  · -- (2,1)(5,2): non-canonical, use witness22 (alpha=4).
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat])
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_2_5o2]) hv_disc
  · -- (2,1)(7,3)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat])
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_2_7o3]) hv_disc
  · -- (2,1)(8,3)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat])
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_2_8o3]) hv_disc
  · -- (2,1)(9,4)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat])
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_2_9o4]) hv_disc
  · -- (3,1)(2,1): canonical (2,1)(3,1) via swap σ.
    refine ⟨Equiv.swap (0 : Fin 2) 1, ![(2, 1), (3, 1)],
        by simp [knownDisc2List], ?_⟩
    funext i; fin_cases i
    · change (![((3 : ℕ+), (1 : ℕ+)), ((2, 1) : ℕ+ × ℕ+)] : FracTuple 2)
        ((Equiv.swap (0 : Fin 2) 1) 0) = (2, 1)
      rw [Equiv.swap_apply_left]; rfl
    · change (![((3 : ℕ+), (1 : ℕ+)), ((2, 1) : ℕ+ × ℕ+)] : FracTuple 2)
        ((Equiv.swap (0 : Fin 2) 1) 1) = (3, 1)
      rw [Equiv.swap_apply_right]; rfl
  · -- (3,1)(3,1): canonical pair33.
    exact ⟨1, ![(3, 1), (3, 1)], by simp [knownDisc2List], by funext i; fin_cases i <;> rfl⟩
  · -- (3,1)(5,2): non-canonical, use witness23 (alpha=6).
    exfalso
    -- witness23 = ((2,1), (3,1)) ≤ₚ (3,1)(5,2): use σ = swap.
    -- σ=swap: u(1) = (3,1) ≤ v(0) = (3,1) ✓; u(0) = (2,1) ≤ v(1) = (5,2) ✓.
    refine not_isDisc_of_witness witness23_valid ?_ ?_ ?_ hv_disc
    · -- lePermK witness23 v: use σ = swap.
      refine ⟨Equiv.swap (0 : Fin 2) 1, fun i => ?_⟩
      fin_cases i
      · simp [witness23, FracTuple.toRat, Equiv.swap_apply_left]
      · simp [witness23, FracTuple.toRat, Equiv.swap_apply_right]; norm_num
    · -- ¬ lePermK v witness23.
      apply not_lePermK_two
      · simp [witness23, FracTuple.toRat]; norm_num
      · simp [witness23, FracTuple.toRat]; norm_num
    · rw [alphaK_witness23, alphaK_3_5o2]
  · -- (3,1)(7,3)
    exfalso
    refine not_isDisc_of_witness witness23_valid ?_ ?_ ?_ hv_disc
    · refine ⟨Equiv.swap (0 : Fin 2) 1, fun i => ?_⟩
      fin_cases i
      · simp [witness23, FracTuple.toRat, Equiv.swap_apply_left]
      · simp [witness23, FracTuple.toRat, Equiv.swap_apply_right]; norm_num
    · apply not_lePermK_two
      · simp [witness23, FracTuple.toRat]; norm_num
      · simp [witness23, FracTuple.toRat]; norm_num
    · rw [alphaK_witness23, alphaK_3_7o3]
  · -- (3,1)(8,3)
    exfalso
    refine not_isDisc_of_witness witness23_valid ?_ ?_ ?_ hv_disc
    · refine ⟨Equiv.swap (0 : Fin 2) 1, fun i => ?_⟩
      fin_cases i
      · simp [witness23, FracTuple.toRat, Equiv.swap_apply_left]
      · simp [witness23, FracTuple.toRat, Equiv.swap_apply_right]; norm_num
    · apply not_lePermK_two
      · simp [witness23, FracTuple.toRat]; norm_num
      · simp [witness23, FracTuple.toRat]; norm_num
    · rw [alphaK_witness23, alphaK_3_8o3]
  · -- (3,1)(9,4)
    exfalso
    refine not_isDisc_of_witness witness23_valid ?_ ?_ ?_ hv_disc
    · refine ⟨Equiv.swap (0 : Fin 2) 1, fun i => ?_⟩
      fin_cases i
      · simp [witness23, FracTuple.toRat, Equiv.swap_apply_left]
      · simp [witness23, FracTuple.toRat, Equiv.swap_apply_right]; norm_num
    · apply not_lePermK_two
      · simp [witness23, FracTuple.toRat]; norm_num
      · simp [witness23, FracTuple.toRat]; norm_num
    · rw [alphaK_witness23, alphaK_3_9o4]
  · -- (5,2)(2,1)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_5o2_2]) hv_disc
  · -- (5,2)(3,1): non-canon, use witness23. Need to figure out perm.
    -- witness23 = ((2,1),(3,1)), v = ((5,2),(3,1)).
    -- σ=1: u(0)=(2,1)=2 ≤ v(0)=(5,2)=5/2 ✓; u(1)=(3,1)=3 ≤ v(1)=(3,1)=3 ✓.
    exfalso
    apply not_isDisc_of_witness witness23_valid
        (lePermK_id witness23 _
          (by simp [witness23, FracTuple.toRat]; norm_num)
          (by simp [witness23, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness23, FracTuple.toRat]; norm_num)
          (by simp [witness23, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness23, alphaK_5o2_3]) hv_disc
  · -- (5,2)(5,2): canonical pair5o2_5o2.
    exact ⟨1, ![(5, 2), (5, 2)], by simp [knownDisc2List], by funext i; fin_cases i <;> rfl⟩
  · -- (5,2)(7,3)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_5o2_7o3]) hv_disc
  · -- (5,2)(8,3): non-canon, use witness5o2_5o2 (alpha=5).
    -- v = ((5,2),(8,3)). u = ((5,2),(5,2)).
    -- σ=1: u(0)=5/2 ≤ v(0)=5/2 ✓; u(1)=5/2 ≤ v(1)=8/3 ✓ (5/2=15/6 < 16/6=8/3).
    exfalso
    apply not_isDisc_of_witness witness5o2_5o2_valid
        (lePermK_id witness5o2_5o2 _
          (by simp [witness5o2_5o2, FracTuple.toRat])
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num)
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness5o2_5o2, alphaK_5o2_8o3]) hv_disc
  · -- (5,2)(9,4)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_5o2_9o4]) hv_disc
  · -- (7,3)(2,1)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_7o3_2]) hv_disc
  · -- (7,3)(3,1)
    exfalso
    apply not_isDisc_of_witness witness23_valid
        (lePermK_id witness23 _
          (by simp [witness23, FracTuple.toRat]; norm_num)
          (by simp [witness23, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness23, FracTuple.toRat]; norm_num)
          (by simp [witness23, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness23, alphaK_7o3_3]) hv_disc
  · -- (7,3)(5,2)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_7o3_5o2]) hv_disc
  · -- (7,3)(7,3)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_7o3_7o3]) hv_disc
  · -- (7,3)(8,3)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_7o3_8o3]) hv_disc
  · -- (7,3)(9,4)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_7o3_9o4]) hv_disc
  · -- (8,3)(2,1)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_8o3_2]) hv_disc
  · -- (8,3)(3,1)
    exfalso
    apply not_isDisc_of_witness witness23_valid
        (lePermK_id witness23 _
          (by simp [witness23, FracTuple.toRat]; norm_num)
          (by simp [witness23, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness23, FracTuple.toRat]; norm_num)
          (by simp [witness23, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness23, alphaK_8o3_3]) hv_disc
  · -- (8,3)(5,2)
    exfalso
    apply not_isDisc_of_witness witness5o2_5o2_valid
        (lePermK_id witness5o2_5o2 _
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num)
          (by simp [witness5o2_5o2, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num)
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness5o2_5o2, alphaK_8o3_5o2]) hv_disc
  · -- (8,3)(7,3)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_8o3_7o3]) hv_disc
  · -- (8,3)(8,3)
    exfalso
    apply not_isDisc_of_witness witness5o2_5o2_valid
        (lePermK_id witness5o2_5o2 _
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num)
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num)
          (by simp [witness5o2_5o2, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness5o2_5o2, alphaK_8o3_8o3]) hv_disc
  · -- (8,3)(9,4)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_8o3_9o4]) hv_disc
  · -- (9,4)(2,1)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_9o4_2]) hv_disc
  · -- (9,4)(3,1)
    exfalso
    apply not_isDisc_of_witness witness23_valid
        (lePermK_id witness23 _
          (by simp [witness23, FracTuple.toRat]; norm_num)
          (by simp [witness23, FracTuple.toRat]))
        (not_lePermK_two _ _
          (by simp [witness23, FracTuple.toRat]; norm_num)
          (by simp [witness23, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness23, alphaK_9o4_3]) hv_disc
  · -- (9,4)(5,2)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_9o4_5o2]) hv_disc
  · -- (9,4)(7,3)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_9o4_7o3]) hv_disc
  · -- (9,4)(8,3)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_9o4_8o3]) hv_disc
  · -- (9,4)(9,4)
    exfalso
    apply not_isDisc_of_witness witness22_valid
        (lePermK_id witness22 _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (not_lePermK_two _ _
          (by simp [witness22, FracTuple.toRat]; norm_num)
          (by simp [witness22, FracTuple.toRat]; norm_num))
        (by rw [alphaK_witness22, alphaK_9o4_9o4]) hv_disc

/-! ## Theorem 6.9 — fully unconditional bidirectional with explicit 12-tuple list -/

/-- **Paper Theorem 6.9 (`th:discont`)** — the α₃-discontinuities on
    `(ℚ ∩ [2, 3])³` (in lowest terms) are exactly the 12 paper-canonical
    multisets up to permutation. Unconditional, fully bidirectional.

    The 12 multisets are listed inline in the iff conclusion. -/
theorem theorem_6_9
    (v : Fin 3 → ℕ+ × ℕ+)
    (hv_ge2 : ∀ i, (2 : ℚ) ≤ ((v i).1 : ℚ) / ((v i).2 : ℚ))
    (hv_le3 : ∀ i, ((v i).1 : ℚ) / ((v i).2 : ℚ) ≤ 3)
    (hv_coprime : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ)) :
    IsDiscontinuityK v ↔
    ∃ σ : Equiv.Perm (Fin 3), v ∘ σ ∈
      ([ ![(2, 1), (2, 1), (2, 1)],
         ![(2, 1), (2, 1), (3, 1)],
         ![(2, 1), (3, 1), (3, 1)],
         ![(3, 1), (3, 1), (3, 1)],
         ![(2, 1), (5, 2), (5, 2)],
         ![(5, 2), (5, 2), (3, 1)],
         ![(5, 2), (5, 2), (8, 3)],
         ![(8, 3), (8, 3), (8, 3)],
         ![(9, 4), (7, 3), (5, 2)],
         ![(11, 5), (11, 4), (11, 4)],
         ![(11, 4), (11, 4), (11, 4)],
         ![(14, 5), (14, 5), (14, 5)] ] :
        List (Fin 3 → ℕ+ × ℕ+)) := by
  have h_iff : IsDiscontinuityK v ↔ IsKnownDiscMod v := by
    apply theorem_6_9_unconditional_of_alpha2_classification
      alpha2_classification v _ hv_le3 hv_coprime
    -- Bridge ℚ form `2 ≤ p/q` to ℕ form `2*q ≤ p` (for ValidK).
    intro i
    have hq : (0 : ℚ) < ((v i).2 : ℚ) := by exact_mod_cast (v i).2.pos
    have h := (le_div_iff₀ hq).mp (hv_ge2 i)
    exact_mod_cast h
  rw [h_iff, IsKnownDiscMod]
  constructor
  · rintro ⟨σ, w, hw_mem, rfl⟩
    refine ⟨σ, ?_⟩
    simpa [knownDiscList, triple222, triple223, triple233, triple333,
      triple_2_5o2_5o2, triple_5o2_5o2_3, triple_5o2_5o2_8o3,
      triple_8o3_8o3_8o3, triple_9o4_7o3_5o2, triple_11o5_11o4_11o4,
      triple_11o4_11o4_11o4, triple_14o5_14o5_14o5] using hw_mem
  · rintro ⟨σ, hmem⟩
    refine ⟨σ, v ∘ σ, ?_, rfl⟩
    simpa [knownDiscList, triple222, triple223, triple233, triple333,
      triple_2_5o2_5o2, triple_5o2_5o2_3, triple_5o2_5o2_8o3,
      triple_8o3_8o3_8o3, triple_9o4_7o3_5o2, triple_11o5_11o4_11o4,
      triple_11o4_11o4_11o4, triple_14o5_14o5_14o5] using hmem

/-! ## Theorem 6.9 — unconditional rational-list form (used by Main.lean) -/

/-- The lowest-terms reduction of a `ℕ+ × ℕ+` pair: `(p, q) ↦ (p / d, q / d)`
    with `d := gcd(p, q)`. Used by `theorem_6_9_rat` to reduce the general
    case to the coprime case. -/
def pnatPairReduce (pq : ℕ+ × ℕ+) : ℕ+ × ℕ+ :=
  let d : ℕ := Nat.gcd (pq.1 : ℕ) (pq.2 : ℕ)
  let hd : 0 < d := Nat.gcd_pos_of_pos_left (pq.2 : ℕ) pq.1.pos
  ⟨⟨(pq.1 : ℕ) / d, Nat.div_pos (Nat.le_of_dvd pq.1.pos (Nat.gcd_dvd_left _ _)) hd⟩,
   ⟨(pq.2 : ℕ) / d, Nat.div_pos (Nat.le_of_dvd pq.2.pos (Nat.gcd_dvd_right _ _)) hd⟩⟩

lemma pnatPairReduce_toRat (pq : ℕ+ × ℕ+) :
    ((pnatPairReduce pq).1 : ℚ) / ((pnatPairReduce pq).2 : ℚ) =
    ((pq.1 : ℚ) / (pq.2 : ℚ)) := by
  unfold pnatPairReduce
  set d : ℕ := Nat.gcd (pq.1 : ℕ) (pq.2 : ℕ) with hd_def
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left (pq.2 : ℕ) pq.1.pos
  have hd_dvd_p : d ∣ (pq.1 : ℕ) := Nat.gcd_dvd_left _ _
  have hd_dvd_q : d ∣ (pq.2 : ℕ) := Nat.gcd_dvd_right _ _
  have hp_eq : (pq.1 : ℕ) = ((pq.1 : ℕ) / d) * d := (Nat.div_mul_cancel hd_dvd_p).symm
  have hq_eq : (pq.2 : ℕ) = ((pq.2 : ℕ) / d) * d := (Nat.div_mul_cancel hd_dvd_q).symm
  -- The goal (after unfolding pnatPairReduce) is
  --   ((pq.1 / d : ℕ) : ℚ) / ((pq.2 / d : ℕ) : ℚ) = (pq.1 : ℕ) / (pq.2 : ℕ) (over ℚ).
  -- Substituting pq.1 = (pq.1/d) * d and pq.2 = (pq.2/d) * d on the RHS cancels d.
  change (((pq.1 : ℕ) / d : ℕ) : ℚ) / (((pq.2 : ℕ) / d : ℕ) : ℚ) =
         ((pq.1 : ℕ) : ℚ) / ((pq.2 : ℕ) : ℚ)
  conv_rhs => rw [hp_eq, hq_eq, Nat.cast_mul, Nat.cast_mul]
  have hd_q : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  have hq_q : (((pq.2 : ℕ) / d : ℕ) : ℚ) ≠ 0 := by
    have h : 0 < (pq.2 : ℕ) / d := Nat.div_pos (Nat.le_of_dvd pq.2.pos hd_dvd_q) hd_pos
    exact_mod_cast h.ne'
  field_simp

lemma pnatPairReduce_coprime (pq : ℕ+ × ℕ+) :
    Nat.Coprime ((pnatPairReduce pq).1 : ℕ) ((pnatPairReduce pq).2 : ℕ) := by
  unfold pnatPairReduce
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left (pq.2 : ℕ) pq.1.pos)

/-- The 12 paper-canonical pair-tuples (lowest terms, sorted multisets). -/
def discPairList : List (Fin 3 → ℕ+ × ℕ+) :=
  [ ![(2, 1), (2, 1), (2, 1)],
    ![(2, 1), (2, 1), (3, 1)],
    ![(2, 1), (3, 1), (3, 1)],
    ![(3, 1), (3, 1), (3, 1)],
    ![(2, 1), (5, 2), (5, 2)],
    ![(5, 2), (5, 2), (3, 1)],
    ![(5, 2), (5, 2), (8, 3)],
    ![(8, 3), (8, 3), (8, 3)],
    ![(9, 4), (7, 3), (5, 2)],
    ![(11, 5), (11, 4), (11, 4)],
    ![(11, 4), (11, 4), (11, 4)],
    ![(14, 5), (14, 5), (14, 5)] ]

/-- The 12 paper-canonical α₃-disc rational triples (in `(ℚ ∩ [2, 3])³`). -/
def discRatList : List (Fin 3 → ℚ) :=
  [ ![2, 2, 2], ![2, 2, 3], ![2, 3, 3], ![3, 3, 3],
    ![2, 5/2, 5/2], ![5/2, 5/2, 3], ![5/2, 5/2, 8/3], ![8/3, 8/3, 8/3],
    ![9/4, 7/3, 5/2], ![11/5, 11/4, 11/4], ![11/4, 11/4, 11/4], ![14/5, 14/5, 14/5] ]

/-- Pointwise rational image of a pair-tuple. -/
def pairTupleToRat (w : Fin 3 → ℕ+ × ℕ+) : Fin 3 → ℚ :=
  fun i => ((w i).1 : ℚ) / ((w i).2 : ℚ)

/-- The pair-list maps pointwise to the rational-list. -/
lemma pairTupleToRat_discPairList :
    discPairList.map pairTupleToRat = discRatList := by
  unfold discPairList discRatList pairTupleToRat
  simp only [List.map_cons, List.map_nil]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    (funext i; fin_cases i <;> norm_num)

/-- Proof of `main_theorem_6_9`: Theorem 6.9 (`th:discont`) — the
    α₃-discontinuities on `(ℚ ∩ [2, 3])³` are exactly the 12 paper-canonical
    rational multisets up to permutation. Unconditional rational-list form
    that wraps the coprime-form `theorem_6_9` by gcd-reducing `v` to its
    lowest-terms representative `v_red` and translating the conclusion via
    `pairTupleToRat_discPairList`. -/
theorem theorem_6_9_rat
    (v : Fin 3 → ℕ+ × ℕ+)
    (hv_ge2 : ∀ i, (2 : ℚ) ≤ ((v i).1 : ℚ) / ((v i).2 : ℚ))
    (hv_le3 : ∀ i, ((v i).1 : ℚ) / ((v i).2 : ℚ) ≤ 3) :
    Section6.IsDiscontinuityK v ↔
    ∃ σ : Equiv.Perm (Fin 3),
      (fun i => ((v (σ i)).1 : ℚ) / ((v (σ i)).2 : ℚ)) ∈ discRatList := by
  -- Reduce v to lowest-terms representative v_red coordinatewise.
  set v_red : Fin 3 → ℕ+ × ℕ+ := fun i => pnatPairReduce (v i) with hvred_def
  have h_toRat_eq : ∀ i, Section6.FracTuple.toRat v i = Section6.FracTuple.toRat v_red i := by
    intro i; unfold Section6.FracTuple.toRat
    exact (pnatPairReduce_toRat (v i)).symm
  have hv_red_ge2 : ∀ i, (2 : ℚ) ≤ ((v_red i).1 : ℚ) / ((v_red i).2 : ℚ) := by
    intro i
    have h := pnatPairReduce_toRat (v i)
    change ((v_red i).1 : ℚ) / ((v_red i).2 : ℚ) = _ at h
    rw [h]; exact hv_ge2 i
  have hv_red_le3 : ∀ i, ((v_red i).1 : ℚ) / ((v_red i).2 : ℚ) ≤ 3 := by
    intro i
    have h := pnatPairReduce_toRat (v i)
    change ((v_red i).1 : ℚ) / ((v_red i).2 : ℚ) = _ at h
    rw [h]; exact hv_le3 i
  have hv_red_coprime : ∀ i, Nat.Coprime ((v_red i).1 : ℕ) ((v_red i).2 : ℕ) := fun i =>
    pnatPairReduce_coprime (v i)
  -- v is valid iff v_red is valid (both Q ≥ 2 ↔ 2 * q ≤ p; passes via toRat).
  have hv_valid : Section6.ValidK v := by
    intro i
    have hq : (0 : ℚ) < ((v i).2 : ℚ) := by exact_mod_cast (v i).2.pos
    have h := hv_ge2 i
    rw [le_div_iff₀ hq] at h
    exact_mod_cast h
  -- Step 1: IsDiscontinuityK v ↔ IsDiscontinuityK v_red.
  have h_disc_iff : Section6.IsDiscontinuityK v ↔ Section6.IsDiscontinuityK v_red :=
    Section6.isDiscontinuityK_iff_of_toRat_eq hv_valid h_toRat_eq
  -- Step 2: existing coprime theorem on v_red.
  have h_red := Section6.theorem_6_9 v_red hv_red_ge2 hv_red_le3 hv_red_coprime
  -- Translate the conclusion of h_red (pair-list) to rational-list.
  rw [h_disc_iff, h_red]
  -- Goal: (∃ σ, v_red ∘ σ ∈ discPairList) ↔ (∃ σ, (toRat v) ∘ σ ∈ discRatList).
  -- Since toRat v = toRat v_red, this reduces to translating discPairList to
  -- discRatList via pairTupleToRat.
  constructor
  · rintro ⟨σ, h_mem⟩
    refine ⟨σ, ?_⟩
    -- pairTupleToRat (v_red ∘ σ) i = toRat v (σ i).
    have h_eq : (fun i => ((v_red (σ i)).1 : ℚ) / ((v_red (σ i)).2 : ℚ)) =
                (fun i => ((v (σ i)).1 : ℚ) / ((v (σ i)).2 : ℚ)) := by
      funext i; exact (pnatPairReduce_toRat (v (σ i)))
    rw [show (fun i => ((v (σ i)).1 : ℚ) / ((v (σ i)).2 : ℚ)) =
            pairTupleToRat (v_red ∘ σ) from h_eq.symm]
    have h_list_mem : pairTupleToRat (v_red ∘ σ) ∈ discPairList.map pairTupleToRat :=
      List.mem_map.mpr ⟨v_red ∘ σ, h_mem, rfl⟩
    rwa [pairTupleToRat_discPairList] at h_list_mem
  · rintro ⟨σ, h_mem⟩
    refine ⟨σ, ?_⟩
    -- From rational-list membership, recover pair-list membership of v_red ∘ σ.
    rw [← pairTupleToRat_discPairList] at h_mem
    obtain ⟨w, hw_mem, hw_eq⟩ := List.mem_map.mp h_mem
    -- w ∈ discPairList and pairTupleToRat w = toRat (v ∘ σ).
    -- We want v_red ∘ σ ∈ discPairList; show v_red ∘ σ = w via pair-equality.
    suffices h_eq_pair : v_red ∘ σ = w by rw [h_eq_pair]; exact hw_mem
    -- For each canonical pair tuple w in discPairList (all in lowest terms),
    -- if the rational values match, then the pair values match.
    -- This is because both v_red ∘ σ and w are coprime pairs with the same
    -- rational value, hence the same pair.
    funext i
    have h_rat_match : ((v_red (σ i)).1 : ℚ) / ((v_red (σ i)).2 : ℚ) =
                       ((w i).1 : ℚ) / ((w i).2 : ℚ) := by
      have h_v_eq : ((v_red (σ i)).1 : ℚ) / ((v_red (σ i)).2 : ℚ) =
                    ((v (σ i)).1 : ℚ) / ((v (σ i)).2 : ℚ) :=
        pnatPairReduce_toRat (v (σ i))
      have hw_app : pairTupleToRat w i = ((v (σ i)).1 : ℚ) / ((v (σ i)).2 : ℚ) := by
        rw [hw_eq]
      rw [h_v_eq]; exact hw_app.symm
    -- Both pairs are coprime; equality of rational values forces equality of pairs.
    have hv_red_cop : Nat.Coprime ((v_red (σ i)).1 : ℕ) ((v_red (σ i)).2 : ℕ) :=
      hv_red_coprime (σ i)
    -- Get coprimality of w i from membership in discPairList.
    have hw_cop : Nat.Coprime ((w i).1 : ℕ) ((w i).2 : ℕ) := by
      revert hw_mem
      unfold discPairList
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        (fin_cases i <;> decide)
    -- Two coprime fractions with equal rational value have equal pairs.
    have hq1 : ((v_red (σ i)).2 : ℚ) ≠ 0 := by
      have h : (0 : ℚ) < ((v_red (σ i)).2 : ℚ) := by exact_mod_cast (v_red (σ i)).2.pos
      exact h.ne'
    have hq2 : ((w i).2 : ℚ) ≠ 0 := by
      have h : (0 : ℚ) < ((w i).2 : ℚ) := by exact_mod_cast (w i).2.pos
      exact h.ne'
    rw [div_eq_div_iff hq1 hq2] at h_rat_match
    have h_nat : ((v_red (σ i)).1 : ℕ) * ((w i).2 : ℕ) =
                 ((w i).1 : ℕ) * ((v_red (σ i)).2 : ℕ) := by exact_mod_cast h_rat_match
    -- Apply Nat.Coprime to lift to pair equality.
    have h_p_eq : ((v_red (σ i)).1 : ℕ) = ((w i).1 : ℕ) := by
      have h_dvd1 : (w i).1.val ∣ (v_red (σ i)).1.val := by
        have h_dvd_prod : ((w i).1 : ℕ) ∣ ((v_red (σ i)).1 : ℕ) * ((w i).2 : ℕ) := by
          rw [show ((v_red (σ i)).1 : ℕ) * ((w i).2 : ℕ) =
            ((w i).1 : ℕ) * ((v_red (σ i)).2 : ℕ) from by exact_mod_cast h_nat]
          exact ⟨_, rfl⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_right hw_cop h_dvd_prod)
      have h_dvd2 : (v_red (σ i)).1.val ∣ (w i).1.val := by
        have h_dvd_prod : ((v_red (σ i)).1 : ℕ) ∣ ((w i).1 : ℕ) * ((v_red (σ i)).2 : ℕ) := by
          rw [show ((w i).1 : ℕ) * ((v_red (σ i)).2 : ℕ) =
            ((v_red (σ i)).1 : ℕ) * ((w i).2 : ℕ) from by exact_mod_cast h_nat.symm]
          exact ⟨_, rfl⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_right hv_red_cop h_dvd_prod)
      exact Nat.dvd_antisymm h_dvd2 h_dvd1
    have h_q_eq : ((v_red (σ i)).2 : ℕ) = ((w i).2 : ℕ) := by
      have hp_pos : 0 < ((v_red (σ i)).1 : ℕ) := (v_red (σ i)).1.pos
      have hh : ((v_red (σ i)).1 : ℕ) * ((v_red (σ i)).2 : ℕ) =
                ((v_red (σ i)).1 : ℕ) * ((w i).2 : ℕ) := by
        rw [show ((v_red (σ i)).1 : ℕ) * ((w i).2 : ℕ) = ((w i).1 : ℕ) * ((v_red (σ i)).2 : ℕ)
              from h_nat]
        rw [h_p_eq]
      exact Nat.eq_of_mul_eq_mul_left hp_pos hh
    -- PNat × PNat equality from underlying ℕ equalities.
    have h_p_pnat : (v_red (σ i)).1 = (w i).1 := PNat.coe_inj.mp h_p_eq
    have h_q_pnat : (v_red (σ i)).2 = (w i).2 := PNat.coe_inj.mp h_q_eq
    change (v_red (σ i)) = w i
    exact Prod.ext h_p_pnat h_q_pnat

end Section6
