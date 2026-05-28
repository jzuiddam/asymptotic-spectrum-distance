/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Discontinuity candidate Finset (paper's bounded enumeration)

Defines the finite set of `(p, q)` pairs that any α₃-discontinuity in
`(ℚ ∩ [2, 3])³` must have at each slot, by combining:
- `numerator_bound`: if `v` is α₃-disc, `(v i).1 ≤ alphaK v`.
- `alphaK_le_of_lePermK`: with `v ∈ [2, 3]³`, `alphaK v ≤ alphaK (3, 3, 3) = 27`.

So every disc has each slot's `(p, q)` coprime with `p ∈ [2, 27]`, `q ∈ [1, 13]`,
`2q ≤ p ≤ 3q`. This is the paper's eq (24) (line 3004) — `max p_i ≤ 27`.

## Main results

* `fracPairCandidates : Finset (ℕ × ℕ)` — the per-slot candidate set.
* `discCandidates : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))` — the cube.
* `isDiscontinuityK_imp_mem_discCandidates` — every α₃-disc in `[2, 3]³` is in
  the cube.

This is the foundation for the per-candidate `alphaK` table
(`Section6DiscontinuityKAlphaTable`) and the bounded-classification
completeness theorem (`Section6DiscontinuityKConverse`).
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKNumerator
import AsymptoticSpectrumDistance.Section6.Section6Alpha3

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## Per-slot candidate set -/

/-- All `(p, q) : ℕ × ℕ` with `p ∈ [2, 27]`, `q ∈ [1, 13]`, `2q ≤ p ≤ 3q`,
    `gcd(p, q) = 1`. Any slot of an α₃-discontinuity in `[2, 3]³` (in lowest
    terms) is in this set. -/
def fracPairCandidates : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 27) ×ˢ (Finset.Icc 1 13)).filter (fun pq =>
    let (p, q) := pq
    2 * q ≤ p ∧ p ≤ 3 * q ∧ Nat.Coprime p q)

@[simp] lemma mem_fracPairCandidates {p q : ℕ} :
    (p, q) ∈ fracPairCandidates ↔
      2 ≤ p ∧ p ≤ 27 ∧ 1 ≤ q ∧ q ≤ 13 ∧ 2 * q ≤ p ∧ p ≤ 3 * q ∧ Nat.Coprime p q := by
  simp only [fracPairCandidates, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-! ## Triple candidate set -/

/-- The cube of `fracPairCandidates`: candidate `(p_i, q_i)` triples. -/
def discCandidates : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  fracPairCandidates ×ˢ fracPairCandidates ×ˢ fracPairCandidates

/-- Extract the `(p, q)` triple of natural numbers from a `FracTuple 3`. -/
def FracTuple.toNatTriple (v : FracTuple 3) : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
  ((((v 0).1 : ℕ), ((v 0).2 : ℕ)),
   (((v 1).1 : ℕ), ((v 1).2 : ℕ)),
   (((v 2).1 : ℕ), ((v 2).2 : ℕ)))

/-! ## Bound: alphaK v ≤ 27 for v ∈ [2, 3]³

Paper bound (24) (line 3004): if `v ∈ (ℚ ∩ [2, 3])³`, then
`alphaK v ≤ alphaK (3, 3, 3) = 27`. Direct corollary of `alphaK_le_of_lePermK`. -/

/-- `alphaK v ≤ 27` for `v` valid with each slot's toRat ≤ 3. -/
theorem alphaK_le_27_of_le3
    {v : FracTuple 3} (hv_valid : ValidK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3) :
    alphaK v ≤ 27 := by
  -- triple333 = ![(3, 1), (3, 1), (3, 1)] is valid with αₖ = 27.
  have h333_valid : ValidK triple333 := by
    intro i; fin_cases i <;> decide
  have h_le : lePermK v triple333 := by
    refine ⟨1, fun i => ?_⟩
    simp only [Equiv.Perm.coe_one, id_eq]
    fin_cases i
    · change FracTuple.toRat v 0 ≤ FracTuple.toRat triple333 0
      have h_v0 : FracTuple.toRat triple333 0 = 3 := by
        simp [FracTuple.toRat, triple333]
      rw [h_v0]; exact hv_le3 0
    · change FracTuple.toRat v 1 ≤ FracTuple.toRat triple333 1
      have h_v1 : FracTuple.toRat triple333 1 = 3 := by
        simp [FracTuple.toRat, triple333]
      rw [h_v1]; exact hv_le3 1
    · change FracTuple.toRat v 2 ≤ FracTuple.toRat triple333 2
      have h_v2 : FracTuple.toRat triple333 2 = 3 := by
        simp [FracTuple.toRat, triple333]
      rw [h_v2]; exact hv_le3 2
  have h_α_le : alphaK v ≤ alphaK triple333 :=
    alphaK_le_of_lePermK hv_valid h333_valid h_le
  have h_α_333 : alphaK triple333 = 27 := by
    rw [alphaK_three]
    exact alpha3_triple333_eq
  rw [h_α_333] at h_α_le
  exact h_α_le

/-! ## Main theorem: every disc is in `discCandidates` -/

/-- **Main theorem.** Every α₃-discontinuity `v : FracTuple 3` in
    `(ℚ ∩ [2, 3])³` (in lowest terms, all slots non-integer) has its
    `toNatTriple` in `discCandidates`. -/
theorem isDiscontinuityK_imp_mem_discCandidates {v : FracTuple 3}
    (hv_valid : ValidK v) (hv_disc : IsDiscontinuityK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3)
    (hv_coprime : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ))
    (hv_q_ge2 : ∀ i, 2 ≤ ((v i).2 : ℕ)) :
    FracTuple.toNatTriple v ∈ discCandidates := by
  -- Per-slot membership in fracPairCandidates.
  have h_α_le_27 : alphaK v ≤ 27 := alphaK_le_27_of_le3 hv_valid hv_le3
  have h_slot_mem : ∀ i : Fin 3, (((v i).1 : ℕ), ((v i).2 : ℕ)) ∈ fracPairCandidates := by
    intro i
    rw [mem_fracPairCandidates]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hv_coprime i⟩
    · -- 2 ≤ p_i: from validity 2 q_i ≤ p_i with q_i ≥ 2 → p_i ≥ 4 ≥ 2.
      have h := hv_valid i
      have hq : (1 : ℕ+) ≤ (v i).2 := PNat.one_le _
      have h_nat : (2 : ℕ) * ((v i).2 : ℕ) ≤ ((v i).1 : ℕ) := by exact_mod_cast h
      have hq_nat : (1 : ℕ) ≤ ((v i).2 : ℕ) := (v i).2.pos
      omega
    · -- p_i ≤ 27: from D1 + alphaK v ≤ 27.
      have h_pi := alphaK_ge_num_at_of_isDiscontinuityK hv_valid hv_disc i
        (hv_q_ge2 i) (hv_coprime i)
      omega
    · -- 1 ≤ q_i.
      exact (v i).2.pos
    · -- q_i ≤ 13: from 2 q_i ≤ p_i ≤ 27.
      have h_2q_le_p : 2 * ((v i).2 : ℕ) ≤ ((v i).1 : ℕ) := by
        exact_mod_cast hv_valid i
      have h_pi := alphaK_ge_num_at_of_isDiscontinuityK hv_valid hv_disc i
        (hv_q_ge2 i) (hv_coprime i)
      omega
    · -- 2 q_i ≤ p_i: from validity.
      exact_mod_cast hv_valid i
    · -- p_i ≤ 3 q_i: from toRat ≤ 3.
      have h := hv_le3 i
      unfold FracTuple.toRat at h
      have hq_pos_q : (0 : ℚ) < ((v i).2 : ℚ) := by exact_mod_cast (v i).2.pos
      rw [div_le_iff₀ hq_pos_q] at h
      exact_mod_cast h
  -- discCandidates membership from per-slot membership.
  unfold discCandidates FracTuple.toNatTriple
  rw [Finset.mem_product, Finset.mem_product]
  exact ⟨h_slot_mem 0, h_slot_mem 1, h_slot_mem 2⟩

end Section6
