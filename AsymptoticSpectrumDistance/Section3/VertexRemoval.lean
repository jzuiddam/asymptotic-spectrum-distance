/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section3.FractionGraphsDefs

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Vertex Removal in Circular Graphs (Hell-Nešetřil Lemma 6.6)

This file formalizes Lemma 6.6 from Hell-Nešetřil "Graphs and Homomorphisms":
removing a vertex from K_{p/q} yields a graph homomorphically equivalent to K_{p'/q'},
where p'/q' is the Stern-Brocot neighbor of p/q.

## Main Results

* `xSeq`: The ceiling sequence x_i = ⌈i·p/p'⌉ giving the winding set in sorted order
* `windingSetCeil`: The winding set X = {x_0, x_1, ..., x_{p'-1}}
* `xSeq_gap_small`: Gap < q for t ≤ q'-1 (non-adjacency preservation)
* `xSeq_gap_large`: Gap ≥ q for t ≥ q' (adjacency preservation)
* `lemma_6_6`: K_{p/q} - v is homomorphically equivalent to K_{p'/q'}

## Key Insight

The ceiling formula x_i = ⌈i·p/p'⌉ gives a tight sandwich bound on gaps:
  ⌊t·p/p'⌋ ≤ x_{i+t} - x_i ≤ ⌈t·p/p'⌉

This bound is independent of i, making adjacency analysis straightforward.

## References

* Hell & Nešetřil, "Graphs and Homomorphisms", Lemma 6.6
-/

namespace Lemma66

open Finset

/-! ## Basic Definitions -/

section Definitions

variable (p q : ℕ) [NeZero p]

/-- Circular distance on ZMod p -/
def circDist (a b : ZMod p) : ℕ :=
  min (b - a).val ((a - b).val)

/-- The rational complete graph K_{p/q} has vertex set ZMod p
    and edge relation: i ~ j iff circDist(i,j) ≥ q. -/
def Kpq : SimpleGraph (ZMod p) where
  Adj i j := i ≠ j ∧ q ≤ circDist p i j
  symm := by
    intro i j ⟨hne, hdist⟩
    constructor
    · exact hne.symm
    · unfold circDist at *
      rw [min_comm]
      exact hdist
  loopless := by
    -- v4.29: `SimpleGraph.loopless` now has type `Std.Irrefl Adj`, a typeclass with
    -- single field `irrefl : ∀ a, ¬r a a`, rather than the older `Irreflexive Adj`.
    refine ⟨fun i ⟨hne, _⟩ => ?_⟩
    exact hne rfl

/-- Ceiling-based definition: x_i = ⌈i·p/p'⌉.
    The ceiling formula is: (i * p + p' - 1) / p' for i > 0, and 0 for i = 0.
    This gives the winding set X = {x_0, x_1, ..., x_{p'-1}} in sorted order.

    Key property: The gap x_{i+t} - x_i is tightly controlled by t·p/p',
    which makes adjacency preservation transparent. -/
def xSeq (p p' : ℕ) (_hp' : 0 < p') (i : Fin p') : ℕ :=
  if i.val = 0 then 0 else (i.val * p + p' - 1) / p'

/-- The winding set via ceiling formula. -/
def windingSetCeil (p p' : ℕ) (hp' : 0 < p') : Finset ℕ :=
  (Finset.univ : Finset (Fin p')).image (xSeq p p' hp')

end Definitions

/-! ## Basic Properties -/

section BasicProps

variable {p q p' q' : ℕ} [NeZero p]

-- Bezout reformulation: p * q' = q * p' + 1
omit [NeZero p] in
lemma bezout_add (hbezout : p * q' - q * p' = 1) : p * q' = q * p' + 1 := by omega

-- Coprimality of p' and q' follows from Bezout
omit [NeZero p] in
lemma coprime_p'_q' (hbezout : p * q' - q * p' = 1) : Nat.Coprime p' q' := by
  apply Nat.coprime_of_dvd'
  intro d _ hd_p' hd_q'
  have h1 : (d : ℤ) ∣ (p * q' : ℤ) := Int.ofNat_dvd.mpr (hd_q'.mul_left p)
  have h2 : (d : ℤ) ∣ (q * p' : ℤ) := Int.ofNat_dvd.mpr (hd_p'.mul_left q)
  have hsub : (d : ℤ) ∣ ((p * q' : ℤ) - (q * p' : ℤ)) := dvd_sub h1 h2
  have hconv : (p * q' : ℤ) - (q * p' : ℤ) = 1 := by
    have h' : p * q' = q * p' + 1 := by omega
    linarith
  have hsub1 : (d : ℤ) ∣ (1 : ℤ) := by simpa [hconv] using hsub
  exact Int.ofNat_dvd.mp hsub1

-- Coprimality of p and p' follows from Bezout
omit [NeZero p] in
lemma coprime_p_p' (hbezout : p * q' - q * p' = 1) : Nat.Coprime p p' := by
  apply Nat.coprime_of_dvd'
  intro d _ hd_p hd_p'
  have h1 : (d : ℤ) ∣ (p * q' : ℤ) := Int.ofNat_dvd.mpr (hd_p.mul_right q')
  have h2 : (d : ℤ) ∣ (q * p' : ℤ) := Int.ofNat_dvd.mpr (hd_p'.mul_left q)
  have hsub : (d : ℤ) ∣ ((p * q' : ℤ) - (q * p' : ℤ)) := dvd_sub h1 h2
  have hconv : (p * q' : ℤ) - (q * p' : ℤ) = 1 := by
    have h' : p * q' = q * p' + 1 := by omega
    linarith
  have hsub1 : (d : ℤ) ∣ (1 : ℤ) := by simpa [hconv] using hsub
  exact Int.ofNat_dvd.mp hsub1

end BasicProps

/-! ## Ceiling-Based Sequence Properties

The key insight from the updated proof: x_i = ⌈i·p/p'⌉ gives X in sorted order,
and the gap x_{i+t} - x_i is tightly controlled by t·p/p'.

Key sandwich bound: ⌊t·p/p'⌋ ≤ x_{i+t} - x_i ≤ ⌈t·p/p'⌉ -/

section XSeqProperties

variable {p q p' q' : ℕ}

/-- x_0 = 0 -/
lemma xSeq_zero (hp' : 0 < p') : xSeq p p' hp' ⟨0, hp'⟩ = 0 := by
  unfold xSeq; simp

/-- x_i < p for all i < p' -/
lemma xSeq_lt_p (hp' : 0 < p') (hp'_lt : p' < p) (hp_pos : 0 < p) (i : Fin p') :
    xSeq p p' hp' i < p := by
  unfold xSeq
  split_ifs with hi
  · exact hp_pos
  · have hi_lt : i.val < p' := i.isLt
    have h4 : i.val * p + p' - 1 < p * p' := by
      have h1 : i.val + 1 ≤ p' := hi_lt
      have h2 : (i.val + 1) * p ≤ p' * p := Nat.mul_le_mul_right p h1
      have h3 : i.val * p + p ≤ p' * p := by
        calc i.val * p + p = (i.val + 1) * p := by ring
          _ ≤ p' * p := h2
      have h5 : p' ≤ p := Nat.le_of_lt hp'_lt
      have h6 : i.val * p + p' ≤ i.val * p + p := Nat.add_le_add_left h5 _
      have h7 : i.val * p + p' ≤ p' * p := Nat.le_trans h6 h3
      have h8 : i.val * p + p' - 1 < i.val * p + p' := Nat.sub_lt (Nat.add_pos_right _ hp') Nat.one_pos
      calc i.val * p + p' - 1 < i.val * p + p' := h8
        _ ≤ p' * p := h7
        _ = p * p' := Nat.mul_comm p' p
    exact Nat.div_lt_iff_lt_mul hp' |>.mpr h4

/-- x_i is strictly increasing (the sequence gives X in sorted order) -/
lemma xSeq_strictMono (hp' : 0 < p') (hp'_lt : p' < p) (_hbezout : p * q' - q * p' = 1)
    (i j : Fin p') (hij : i < j) : xSeq p p' hp' i < xSeq p p' hp' j := by
  unfold xSeq
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceIte]
    have hj_pos : j.val > 0 := by
      have : i.val < j.val := hij
      omega
    have hj_ne : j.val ≠ 0 := Nat.pos_iff_ne_zero.mp hj_pos
    simp only [hj_ne, ↓reduceIte]
    have h1 : j.val * p + p' - 1 ≥ p' := by
      have hj_ge_1 : 1 ≤ j.val := hj_pos
      have : j.val * p ≥ 1 * p := Nat.mul_le_mul_right p hj_ge_1
      omega
    exact Nat.div_pos h1 hp'
  · simp only [hi, ↓reduceIte]
    have hj_pos : j.val ≠ 0 := by
      have : i.val < j.val := hij
      omega
    simp only [hj_pos, ↓reduceIte]
    have h_gap : j.val * p ≥ i.val * p + p := by
      have : j.val ≥ i.val + 1 := hij
      calc j.val * p ≥ (i.val + 1) * p := Nat.mul_le_mul_right p this
        _ = i.val * p + p := by ring
    have h_num_gap : j.val * p + p' - 1 ≥ i.val * p + p' - 1 + p' := by omega
    have h_div_lt : (i.val * p + p' - 1) / p' < (j.val * p + p' - 1) / p' := by
      apply Nat.div_lt_iff_lt_mul hp' |>.mpr
      set a := i.val * p + p' - 1
      set b := j.val * p + p' - 1
      have h1 : a + p' ≤ b := h_num_gap
      have hmod : b % p' < p' := Nat.mod_lt _ hp'
      have h2 : a + (b % p') < a + p' := Nat.add_lt_add_left hmod a
      have h3 : a + (b % p') < b := Nat.lt_of_lt_of_le h2 h1
      have h4 : a < b - (b % p') := Nat.lt_sub_of_add_lt h3
      have hdiv : p' * (b / p') + b % p' = b := Nat.div_add_mod b p'
      have heq : b - b % p' = (b / p') * p' := by
        have : b - b % p' = p' * (b / p') := by omega
        rw [Nat.mul_comm] at this
        exact this
      rw [heq] at h4
      exact h4
    exact h_div_lt

/-- The key sandwich bound: ⌊t·p/p'⌋ ≤ x_{i+t} - x_i ≤ ⌈t·p/p'⌉
    This is equation (1) from the updated proof.
    Crucially, this bound does NOT depend on i! -/
lemma xSeq_gap_bound (hp' : 0 < p') (_hp'_lt : p' < p)
    (i : Fin p') (t : ℕ) (ht : t > 0) (hit : i.val + t < p') :
    let j : Fin p' := ⟨i.val + t, hit⟩
    t * p / p' ≤ xSeq p p' hp' j - xSeq p p' hp' i ∧
    xSeq p p' hp' j - xSeq p p' hp' i ≤ (t * p + p' - 1) / p' := by
  intro j
  unfold xSeq
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceIte, Nat.sub_zero]
    have hj_pos : j.val ≠ 0 := by simp [j]; omega
    simp only [hj_pos, ↓reduceIte]
    have hj_eq : j.val = t := by simp [j, hi]
    rw [hj_eq]
    constructor
    · have h_le : t * p ≤ t * p + p' - 1 := by omega
      exact Nat.div_le_div_right h_le
    · exact le_refl _
  · -- Case i > 0: requires ceiling arithmetic
    -- Since i.val > 0 and j.val = i.val + t > 0, we can simplify the if statements
    have hj_pos : j.val ≠ 0 := by simp [j]; omega
    simp only [hi, hj_pos, ↓reduceIte]
    have hj_eq : j.val = i.val + t := by simp [j]
    rw [hj_eq]
    -- Key: let B = i.val * p + p' - 1, then the numerator for j is B + t*p
    -- Write B = q * p' + r where r = B % p'
    -- Then (B + t*p) / p' = q + (r + t*p) / p'
    -- So gap = (r + t*p) / p' where 0 ≤ r < p'
    set B := i.val * p + p' - 1 with hB
    have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
    have hB_pos : 0 < B := by simp only [hB]; omega
    set r := B % p' with hr_def
    set q := B / p' with hq_def
    have hr_lt : r < p' := Nat.mod_lt B hp'
    have hB_decomp : B = p' * q + r := (Nat.div_add_mod B p').symm
    -- The numerator for j is B + t * p = p' * q + (r + t * p)
    have h_num_j : (i.val + t) * p + p' - 1 = B + t * p := by
      -- Need to show (i.val + t) * p + p' - 1 = (i.val * p + p' - 1) + t * p
      calc (i.val + t) * p + p' - 1
          = i.val * p + t * p + p' - 1 := by ring_nf
        _ = i.val * p + p' - 1 + t * p := by
            have h1 : i.val * p + p' ≥ 1 := Nat.add_pos_right (i.val * p) hp'
            omega
        _ = B + t * p := by rw [hB]
    have h_div_j : (B + t * p) / p' = q + (r + t * p) / p' := by
      rw [hB_decomp]
      have heq : p' * q + r + t * p = (r + t * p) + q * p' := by ring
      rw [heq, Nat.add_mul_div_right _ _ hp', Nat.add_comm]
    rw [h_num_j, h_div_j, hq_def, Nat.add_sub_cancel_left]
    constructor
    · -- Lower bound: t * p / p' ≤ (r + t * p) / p'
      exact Nat.div_le_div_right (Nat.le_add_left (t * p) r)
    · -- Upper bound: (r + t * p) / p' ≤ (t * p + p' - 1) / p'
      apply Nat.div_le_div_right
      have : r < p' := hr_lt
      omega

/-- For t ≤ q'-1: gap < q (non-adjacent in K_{p/q}) -/
lemma xSeq_gap_small (hp' : 0 < p') (hp'_lt : p' < p) (hq' : 0 < q') (hq'_lt : q' < q)
    (hbezout : p * q' - q * p' = 1)
    (i : Fin p') (t : ℕ) (ht : 1 ≤ t) (ht_lt : t ≤ q' - 1) (hit : i.val + t < p') :
    let j : Fin p' := ⟨i.val + t, hit⟩
    xSeq p p' hp' j - xSeq p p' hp' i < q := by
  intro j
  have h_bound := (xSeq_gap_bound hp' hp'_lt i t (by omega : t > 0) hit).2
  simp only at h_bound
  have hbezout_add : p * q' = q * p' + 1 := by omega
  have h_ceil_bound : (t * p + p' - 1) / p' ≤ q - 1 := by
    have h_tp_bound : t * p ≤ (q' - 1) * p := Nat.mul_le_mul_right p ht_lt
    have h_key : (q' - 1) * p + p' - 1 < q * p' := by
      have hq_pos : 0 < q := Nat.lt_trans hq' hq'_lt
      have hp_gt_p' : p > p' := hp'_lt
      have h1 : p * q' = q * p' + 1 := hbezout_add
      have h2 : (q' - 1) * p + p = q' * p := by
        have hq'_ge : 1 ≤ q' := hq'
        have : q' - 1 + 1 = q' := Nat.sub_add_cancel hq'_ge
        calc (q' - 1) * p + p = (q' - 1 + 1) * p := by ring
          _ = q' * p := by rw [this]
      have h3 : (q' - 1) * p + p' < (q' - 1) * p + p := Nat.add_lt_add_left hp_gt_p' _
      have h4 : (q' - 1) * p + p' < q * p' + 1 := by
        calc (q' - 1) * p + p' < (q' - 1) * p + p := h3
          _ = q' * p := h2
          _ = p * q' := Nat.mul_comm q' p
          _ = q * p' + 1 := h1
      omega
    have h_num_bound : t * p + p' - 1 < q * p' := by
      calc t * p + p' - 1 ≤ (q' - 1) * p + p' - 1 := by omega
        _ < q * p' := h_key
    have h_div_lt : (t * p + p' - 1) / p' < q := Nat.div_lt_iff_lt_mul hp' |>.mpr h_num_bound
    omega
  calc xSeq p p' hp' j - xSeq p p' hp' i ≤ (t * p + p' - 1) / p' := h_bound
    _ ≤ q - 1 := h_ceil_bound
    _ < q := by omega

/-- For t ≥ q': gap ≥ q (adjacent in K_{p/q}) -/
lemma xSeq_gap_large (hp' : 0 < p') (hp'_lt : p' < p) (hq' : 0 < q')
    (hbezout : p * q' - q * p' = 1)
    (i : Fin p') (t : ℕ) (ht : q' ≤ t) (hit : i.val + t < p') :
    let j : Fin p' := ⟨i.val + t, hit⟩
    xSeq p p' hp' j - xSeq p p' hp' i ≥ q := by
  intro j
  have h_bound := (xSeq_gap_bound hp' hp'_lt i t (Nat.lt_of_lt_of_le hq' ht) hit).1
  simp only at h_bound
  have hbezout_add : p * q' = q * p' + 1 := by omega
  have h_floor_bound : t * p / p' ≥ q := by
    have h_tp_bound : t * p ≥ q' * p := Nat.mul_le_mul_right p ht
    have h_qp_bound : q' * p ≥ q * p' := by
      calc q' * p = p * q' := Nat.mul_comm q' p
        _ = q * p' + 1 := hbezout_add
        _ ≥ q * p' := Nat.le_add_right _ _
    have h_final : t * p ≥ q * p' := Nat.le_trans h_qp_bound h_tp_bound
    exact Nat.le_div_iff_mul_le hp' |>.mpr h_final
  exact Nat.le_trans h_floor_bound h_bound

/-- Special case: for t = q', the gap is exactly q (for i ≥ 1) or q+1 (for i = 0).
    This is the key formula from equation (7)-(8) in the updated proof. -/
lemma xSeq_gap_q' (hp' : 0 < p') (_hp'_lt : p' < p) (hq' : 0 < q') (_hq'_lt : q' < q)
    (hbezout : p * q' - q * p' = 1)
    (i : Fin p') (hi_q' : i.val + q' < p') :
    let j : Fin p' := ⟨i.val + q', hi_q'⟩
    (i.val = 0 → xSeq p p' hp' j - xSeq p p' hp' i = q + 1) ∧
    (i.val ≠ 0 → xSeq p p' hp' j - xSeq p p' hp' i = q) := by
  intro j
  have hbezout_add : p * q' = q * p' + 1 := by omega
  constructor
  · -- Case i = 0: gap = q + 1
    intro hi_zero
    unfold xSeq
    simp only [hi_zero, ↓reduceIte, Nat.sub_zero]
    have hj_pos : j.val ≠ 0 := by simp [j, hi_zero]; omega
    simp only [hj_pos, ↓reduceIte]
    have hj_eq : j.val = q' := by simp [j, hi_zero]
    rw [hj_eq]
    have h_qp : q' * p = q * p' + 1 := by rw [Nat.mul_comm]; exact hbezout_add
    have h1 : q' * p + p' - 1 = q * p' + p' := by omega
    have h2 : (q * p' + p') / p' = q + 1 := by
      have : q * p' + p' = (q + 1) * p' := by ring
      rw [this]
      exact Nat.mul_div_left (q + 1) hp'
    rw [h1, h2]
  · -- Case i > 0: gap = q (requires coprimality reasoning)
    intro hi_pos
    unfold xSeq
    simp only [hi_pos, ↓reduceIte]
    have hj_pos : j.val ≠ 0 := by simp [j]; omega
    simp only [hj_pos, ↓reduceIte]
    have hj_eq : j.val = i.val + q' := by simp [j]
    rw [hj_eq]
    -- Use the gap formula from xSeq_gap_bound proof
    set B := i.val * p + p' - 1 with hB_def
    have hi_pos_nat : 0 < i.val := Nat.pos_of_ne_zero hi_pos
    set r := B % p' with hr_def
    set qB := B / p' with hqB_def
    have hr_lt : r < p' := Nat.mod_lt B hp'
    have hB_decomp : B = p' * qB + r := (Nat.div_add_mod B p').symm
    -- The numerator for j is B + q' * p
    have h_num_j : (i.val + q') * p + p' - 1 = B + q' * p := by
      calc (i.val + q') * p + p' - 1
          = i.val * p + q' * p + p' - 1 := by ring_nf
        _ = i.val * p + p' - 1 + q' * p := by
            have h1 : i.val * p + p' ≥ 1 := Nat.add_pos_right (i.val * p) hp'
            omega
        _ = B + q' * p := by rw [hB_def]
    have h_div_j : (B + q' * p) / p' = qB + (r + q' * p) / p' := by
      rw [hB_decomp]
      have heq : p' * qB + r + q' * p = (r + q' * p) + qB * p' := by ring
      rw [heq, Nat.add_mul_div_right _ _ hp', Nat.add_comm]
    rw [h_num_j, h_div_j, hqB_def, Nat.add_sub_cancel_left]
    -- Now: gap = (r + q' * p) / p' = (r + q * p' + 1) / p'
    have h_qp : q' * p = q * p' + 1 := by rw [Nat.mul_comm]; exact hbezout_add
    rw [h_qp]
    -- Key: Since gcd(p, p') = 1 and 0 < i < p', we have p' ∤ i * p, so r ≠ p' - 1
    have h_coprime : Nat.Coprime p p' := coprime_p_p' hbezout
    have h_not_div : ¬ p' ∣ i.val * p := by
      intro hdiv
      have hdiv_i : p' ∣ i.val := h_coprime.symm.dvd_of_dvd_mul_right hdiv
      have h_ge : i.val ≥ p' := Nat.le_of_dvd hi_pos_nat hdiv_i
      exact Nat.not_lt.mpr h_ge i.isLt
    -- r = (i * p + p' - 1) % p' = (i * p - 1) % p' when i * p ≥ 1
    -- r = p' - 1 iff i * p ≡ 0 (mod p')
    have hr_ne : r ≠ p' - 1 := by
      intro heq
      -- If r = p' - 1, then (i * p + p' - 1) % p' = p' - 1
      -- This means i * p + p' - 1 ≡ p' - 1 (mod p'), i.e., i * p ≡ 0 (mod p')
      have h1 : B % p' = p' - 1 := heq
      have h2 : (i.val * p + (p' - 1)) % p' = p' - 1 := by
        have : B = i.val * p + p' - 1 := hB_def
        have hp'_ge : p' ≥ 1 := hp'
        have : i.val * p + p' - 1 = i.val * p + (p' - 1) := by omega
        rw [← this]; exact h1
      -- (a + b) % n = b means a % n = 0 when b < n
      have h3 : (p' - 1) % p' = p' - 1 := Nat.mod_eq_of_lt (Nat.sub_lt hp' Nat.one_pos)
      have h4 : (i.val * p) % p' = 0 := by
        have h_add := Nat.add_mod (i.val * p) (p' - 1) p'
        rw [h2, h3] at h_add
        have h_mod_lt : (i.val * p) % p' < p' := Nat.mod_lt (i.val * p) hp'
        -- h_add says: (i.val * p % p' + (p' - 1)) % p' = p' - 1
        -- Since p' - 1 < p', and if i.val * p % p' ≠ 0, then sum mod would differ
        by_contra hne
        have hpos : 0 < (i.val * p) % p' := Nat.pos_of_ne_zero hne
        -- (a + b) % n = b when 0 < a < n and b < n only if a + b < n, which gives a = 0
        have hsum_ge : i.val * p % p' + (p' - 1) ≥ p' := by omega
        have hsum_lt2 : i.val * p % p' + (p' - 1) < 2 * p' - 1 := by
          have : i.val * p % p' ≤ p' - 1 := by omega
          omega
        -- When p' ≤ sum < 2*p' - 1, sum % p' = sum - p' ≠ p' - 1 unless sum = 2*p' - 1
        have hmod_eq : (i.val * p % p' + (p' - 1)) % p' = i.val * p % p' + (p' - 1) - p' := by
          have h1 : (i.val * p % p' + (p' - 1)) % p' =
                    (i.val * p % p' + (p' - 1) - p') % p' := Nat.mod_eq_sub_mod hsum_ge
          have h2 : i.val * p % p' + (p' - 1) - p' < p' := by omega
          rw [h1, Nat.mod_eq_of_lt h2]
        rw [hmod_eq] at h_add
        omega
      exact h_not_div (Nat.dvd_of_mod_eq_zero h4)
    -- Since r < p' and r ≠ p' - 1, we have r ≤ p' - 2
    have hr_le : r ≤ p' - 2 := by omega
    -- Therefore gap = (r + q * p' + 1) / p' = q
    have h_gap_lt : r + (q * p' + 1) < (q + 1) * p' := by
      calc r + (q * p' + 1) ≤ p' - 2 + (q * p' + 1) := Nat.add_le_add_right hr_le _
        _ = q * p' + p' - 1 := by omega
        _ < (q + 1) * p' := by
            have : (q + 1) * p' = q * p' + p' := by ring
            omega
    have h_gap_ge : r + (q * p' + 1) ≥ q * p' := by omega
    exact Nat.div_eq_of_lt_le h_gap_ge h_gap_lt

/-- Exact value: xSeq(p' - q') = p - q when p' ≥ 2 and p > p'.
    This follows from Bezout: (p' - q')*p = p'*(p - q) - 1, so
    ceil((p' - q')*p/p') = (p'*(p - q) + (p' - 2))/p' = p - q. -/
lemma xSeq_pq'_eq (hp' : 0 < p') (_hp'_lt : p' < p) (hp'_ge2 : 2 ≤ p')
    (hq' : 0 < q') (hq'_lt_p' : q' < p') (hbezout : p * q' - q * p' = 1) :
    xSeq p p' hp' ⟨p' - q', Nat.sub_lt hp' hq'⟩ = p - q := by
  unfold xSeq
  have hpq'_ne0 : p' - q' ≠ 0 := by omega
  simp only [hpq'_ne0, ↓reduceIte]
  have hbezout' : p * q' = q * p' + 1 := by omega
  have hqp_bound : q' * p = q * p' + 1 := by rw [Nat.mul_comm]; exact hbezout'
  have hp_ge_q : p ≥ q := by
    have hpq'_gt : p * q' > q * p' := by omega
    by_contra h; push_neg at h
    have h1 : p * q' ≤ q * q' := Nat.mul_le_mul_right q' (Nat.le_of_lt h)
    have h2 : q * q' < q * p' :=
      Nat.mul_lt_mul_of_pos_left hq'_lt_p' (Nat.lt_of_le_of_lt (Nat.zero_le p) h)
    omega
  have hqp_le_pp : q * p' + 1 ≤ p * p' := by
    calc q * p' + 1 = q' * p := hqp_bound.symm
      _ ≤ p' * p := Nat.mul_le_mul_right p (Nat.le_of_lt hq'_lt_p')
      _ = p * p' := Nat.mul_comm p' p
  -- (p' - q') * p + p' - 1 = p' * (p - q) + (p' - 2)
  -- Division by p' gives (p - q) with remainder (p' - 2)
  have hnum_eq : (p' - q') * p + p' - 1 = (p - q) * p' + (p' - 2) := by
    have hq'_le : q' ≤ p' := Nat.le_of_lt hq'_lt_p'
    have hkey : q' * p = q * p' + 1 := hqp_bound
    have h_qp_le : q' * p ≤ p' * p := Nat.mul_le_mul_right p (Nat.le_of_lt hq'_lt_p')
    have heq1 : (p' - q') * p = p' * p - q * p' - 1 := by
      calc (p' - q') * p = p' * p - q' * p := Nat.sub_mul p' q' p
        _ = p' * p - (q * p' + 1) := by rw [hkey]
        _ = p' * p - q * p' - 1 := by
            have h1 : q * p' + 1 ≤ p' * p := by
              calc q * p' + 1 = q' * p := hqp_bound.symm
                _ ≤ p' * p := h_qp_le
            omega
    have hp_gt_q : p > q := by
      -- Prove p > q from Bezout: if p ≤ q, then p * q' ≤ q * q' < q * p' contradicts p * q' = q * p' + 1
      by_contra h
      push_neg at h
      cases Nat.lt_or_eq_of_le h with
      | inl hplt =>
        -- p < q: then p * q' < q * q' < q * p' contradicts Bezout
        have h1 : p * q' < q * q' := Nat.mul_lt_mul_of_pos_right hplt hq'
        have h2 : q * q' < q * p' := Nat.mul_lt_mul_of_pos_left hq'_lt_p' (Nat.lt_of_le_of_lt (Nat.zero_le p) hplt)
        omega
      | inr hpeq =>
        -- p = q: then p * q' = p * p' + 1, impossible since q' < p'
        rw [hpeq] at hbezout'
        have h1 : q * q' < q * p' := by
          cases q with
          | zero => simp at hbezout'
          | succ n => exact Nat.mul_lt_mul_of_pos_left hq'_lt_p' (Nat.succ_pos n)
        omega
    have hp'p_ge : p' * p ≥ q * p' + 2 := by
      have h1 : p' * p = p * p' := Nat.mul_comm p' p
      have h2 : p * p' ≥ q * p' + p' := by
        have hp_ge_q1 : p ≥ q + 1 := hp_gt_q
        calc p * p' ≥ (q + 1) * p' := Nat.mul_le_mul_right p' hp_ge_q1
          _ = q * p' + p' := by ring
      omega
    calc (p' - q') * p + p' - 1 = (p' * p - q * p' - 1) + p' - 1 := by rw [heq1]
      _ = p' * p - q * p' + p' - 2 := by omega
      _ = p * p' - q * p' + p' - 2 := by rw [Nat.mul_comm]
      _ = (p - q) * p' + p' - 2 := by rw [Nat.sub_mul]
      _ = (p - q) * p' + (p' - 2) := by omega
  have hrem_lt : p' - 2 < p' := by omega
  rw [hnum_eq]
  have heq2 : (p - q) * p' + (p' - 2) = (p' - 2) + p' * (p - q) := by ring
  rw [heq2, Nat.add_mul_div_left _ _ hp']
  simp only [Nat.div_eq_of_lt hrem_lt, Nat.zero_add]

/-- Key bound: xSeq(p' - q') ≥ p - q when p' ≥ 2 and q' < p'.
    This follows from Bezout: p * q' = q * p' + 1.
    Used for edge cases in retract_preserves_adj where indices are near p'. -/
lemma xSeq_pq'_bound (hp' : 0 < p') (hp'_ge2 : 2 ≤ p') (hq' : 0 < q') (hq'_lt_p' : q' < p')
    (hbezout : p * q' - q * p' = 1) :
    xSeq p p' hp' ⟨p' - q', Nat.sub_lt hp' hq'⟩ ≥ p - q := by
  unfold xSeq
  have hpq'_ne0 : p' - q' ≠ 0 := by omega
  simp only [hpq'_ne0, ↓reduceIte]
  -- Need: ((p' - q') * p + p' - 1) / p' ≥ p - q
  -- Equivalently: (p' - q') * p + p' - 1 ≥ (p - q) * p'
  have hbezout' : p * q' = q * p' + 1 := by omega
  have hqp_bound : q' * p = q * p' + 1 := by rw [Nat.mul_comm]; exact hbezout'
  have hp_ge_q : p ≥ q := by
    have hpq'_gt : p * q' > q * p' := by omega
    by_contra h; push_neg at h
    have h1 : p * q' ≤ q * q' := Nat.mul_le_mul_right q' (Nat.le_of_lt h)
    have h2 : q * q' < q * p' := Nat.mul_lt_mul_of_pos_left hq'_lt_p' (Nat.lt_of_le_of_lt (Nat.zero_le p) h)
    omega
  have hp'p_ge : p' * p ≥ q' * p := Nat.mul_le_mul_right p (Nat.le_of_lt hq'_lt_p')
  -- Show numerator ≥ (p - q) * p' using integer arithmetic
  have hnum_ge : (p' - q') * p + p' - 1 ≥ (p - q) * p' := by
    -- Use zify to work in integers where subtraction is well-behaved
    have hq'_le : q' ≤ p' := Nat.le_of_lt hq'_lt_p'
    have hqp'_le_pp' : q * p' ≤ p * p' := by
      have h := Nat.mul_le_mul_right p' hp_ge_q
      ring_nf at h ⊢; exact h
    -- Key: (p' - q') * p + p' - 1 ≥ (p - q) * p'
    -- Expand: p'*p - q'*p + p' - 1 ≥ p*p' - q*p'
    -- Since p'*p = p*p', this is: p' - 1 ≥ q'*p - q*p' = 1
    -- Which holds since p' ≥ 2, so p' - 1 ≥ 1
    have hkey : q' * p = q * p' + 1 := hqp_bound
    have hq'p_le : q' * p ≤ p' * p := hp'p_ge
    -- p' * p - q' * p = p' * p - (q * p' + 1) = p * p' - q * p' - 1 = (p - q) * p' - 1
    have heq1 : p' * p - q' * p = p * p' - q * p' - 1 := by
      have h1 : q' * p ≤ p' * p := hp'p_ge
      have h2 : q * p' + 1 ≤ p' * p := by
        calc q * p' + 1 = q' * p := hqp_bound.symm
          _ ≤ p' * p := hp'p_ge
      have h3 : q * p' ≤ p * p' := hqp'_le_pp'
      have h4 : p' * p = p * p' := Nat.mul_comm p' p
      omega
    -- (p - q) * p' = p * p' - q * p'
    have hpq_expand : (p - q) * p' = p * p' - q * p' := Nat.sub_mul p q p'
    -- So LHS = (p - q) * p' - 1 + p' - 1, and since p' ≥ 2, this ≥ (p - q) * p'
    calc (p' - q') * p + p' - 1
        = p' * p - q' * p + p' - 1 := by rw [Nat.sub_mul]
      _ = (p * p' - q * p' - 1) + p' - 1 := by rw [heq1]
      _ = (p - q) * p' - 1 + p' - 1 := by rw [hpq_expand]
      _ ≥ (p - q) * p' := by omega
  exact Nat.le_div_iff_mul_le hp' |>.mpr hnum_ge

end XSeqProperties

/-! ## The Winding Set

The winding set X = {x_0, x_1, ..., x_{p'-1}} is the image of the ceiling sequence.
This is the copy of K_{p'/q'} embedded in K_{p/q}. -/

section WindingSet

variable {p q p' q' : ℕ} [NeZero p]

/-- The winding set: image of the embedding xSeq. -/
def windingSet (hp' : 0 < p') : Finset (ZMod p) :=
  Finset.image (fun i : Fin p' => (xSeq p p' hp' i : ZMod p)) Finset.univ

/-- The vertex q is NOT in the winding set. This is the key structural fact from Step 2.2
    of the proof: x_{q'-1} < q and x_{q'} = q + 1, so q is skipped.
    The retraction proof REQUIRES deleting specifically q (or a translate of q).

    Proof outline:
    1. q' < p' (from Bezout: if q' ≥ p' then p*p' ≤ q*p' + 1 but p*p' ≥ q*p' + 2)
    2. xSeq(q') = q + 1 (from xSeq_gap_q')
    3. For i < q': xSeq(i) ≤ xSeq(q'-1) < q (from xSeq_gap_small)
    4. For i ≥ q': xSeq(i) ≥ xSeq(q') = q + 1 > q
    So no i has xSeq(i) = q. -/
lemma q_not_in_windingSet (hp' : 0 < p') (hp'_lt : p' < p) (hq' : 0 < q') (hq'_lt : q' < q)
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hbezout : p * q' - q * p' = 1) :
    (q : ZMod p) ∉ windingSet (p := p) hp' := by
  intro hmem
  rw [windingSet, Finset.mem_image] at hmem
  obtain ⟨i, _, heq⟩ := hmem
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hxi_lt : xSeq p p' hp' i < p := xSeq_lt_p hp' hp'_lt hp_pos i
  have hq_lt' : q < p := by omega
  have hval_eq : xSeq p p' hp' i = q := by
    have h1 : (xSeq p p' hp' i : ZMod p).val = xSeq p p' hp' i := ZMod.val_natCast_of_lt hxi_lt
    have h2 : (q : ZMod p).val = q := ZMod.val_natCast_of_lt hq_lt'
    calc xSeq p p' hp' i = (xSeq p p' hp' i : ZMod p).val := h1.symm
      _ = (q : ZMod p).val := congrArg ZMod.val heq
      _ = q := h2
  -- Prove q' < p' from Bezout identity
  -- If q' ≥ p', then p * p' ≤ p * q' = q * p' + 1
  -- But p * p' = (p - q) * p' + q * p' ≥ 2 * p' + q * p' ≥ 2 + q * p' > q * p' + 1
  have hq'_lt_p' : q' < p' := by
    by_contra hge; push_neg at hge
    have hbezout_add : p * q' = q * p' + 1 := by omega
    have h1 : p * p' ≤ q * p' + 1 := calc p * p' ≤ p * q' := Nat.mul_le_mul_left p hge
      _ = q * p' + 1 := hbezout_add
    have hpq_le : q ≤ p := by omega
    have hpmq : p - q + q = p := Nat.sub_add_cancel hpq_le
    have h2 : (p - q) * p' + q * p' = p * p' := by
      calc (p - q) * p' + q * p' = (p - q + q) * p' := by ring
        _ = p * p' := by rw [hpmq]
    have h3 : (p - q) * p' ≥ 2 * p' := Nat.mul_le_mul_right p' (by omega : p - q ≥ 2)
    have h4 : 2 * p' ≥ 2 := by
      calc 2 * p' = 2 * p' := rfl
        _ ≥ 2 * 1 := Nat.mul_le_mul_left 2 hp'
        _ = 2 := by ring
    have h5 : p * p' ≥ q * p' + 2 := by
      calc p * p' = (p - q) * p' + q * p' := h2.symm
        _ ≥ 2 * p' + q * p' := Nat.add_le_add_right h3 _
        _ = q * p' + 2 * p' := by ring
        _ ≥ q * p' + 2 := Nat.add_le_add_left h4 _
    omega
  -- Key facts from xSeq_gap_q':
  -- x_{q'} - x_0 = q + 1 (since x_0 = 0)
  -- So x_{q'} = q + 1
  have hq'_bound : (⟨0, hp'⟩ : Fin p').val + q' < p' := by
    simp only [zero_add]; exact hq'_lt_p'
  have hxq'_eq : xSeq p p' hp' ⟨q', hq'_lt_p'⟩ = q + 1 := by
    have hx0 : xSeq p p' hp' ⟨0, hp'⟩ = 0 := xSeq_zero hp'
    have hgap := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout ⟨0, hp'⟩ hq'_bound).1 rfl
    simp only [hx0, Nat.sub_zero] at hgap
    have heq_j : (⟨(⟨0, hp'⟩ : Fin p').val + q', hq'_bound⟩ : Fin p') = ⟨q', hq'_lt_p'⟩ := by simp
    rw [heq_j] at hgap
    exact hgap
  -- Now: either i < q' (so xSeq(i) ≤ xSeq(q'-1) < q) or i ≥ q' (so xSeq(i) ≥ x_{q'} = q+1)
  by_cases hi : i.val < q'
  · -- Case i < q': xSeq is strictly increasing, so xSeq(i) < xSeq(q') = q + 1
    have hmono : xSeq p p' hp' i < xSeq p p' hp' ⟨q', hq'_lt_p'⟩ :=
      xSeq_strictMono hp' hp'_lt hbezout i ⟨q', hq'_lt_p'⟩ hi
    -- Need to show xSeq(i) ≠ q. We know xSeq(i) < q + 1 from above.
    -- Also need xSeq(i) < q. This requires showing the gap from 0 to i is < q.
    -- Since i < q', the gap from 0 to i is at most the gap from 0 to q'-1 which is < q.
    have hgap_lt : xSeq p p' hp' i < q := by
      by_cases hi_zero : i.val = 0
      · have : i = ⟨0, hp'⟩ := Fin.ext hi_zero
        rw [this, xSeq_zero hp']
        omega
      · -- i > 0 and i < q', so i ≤ q' - 1
        have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi_zero
        have hi_bound : i.val ≤ q' - 1 := Nat.le_sub_one_of_lt hi
        -- The gap from 0 to i is xSeq(i) - xSeq(0) = xSeq(i)
        -- By xSeq_gap_bound, this is ≤ ceiling(i * p / p')
        -- Since i ≤ q' - 1 < q', we have i * p / p' < q' * p / p' = q + 1/p'
        -- So ceiling(i * p / p') ≤ ceiling((q'-1) * p / p') < q (by xSeq_gap_small)
        have hit : (⟨0, hp'⟩ : Fin p').val + i.val < p' := by
          simp only [Nat.zero_add]
          exact Nat.lt_trans hi hq'_lt_p'
        have h_bound := (xSeq_gap_bound hp' hp'_lt ⟨0, hp'⟩ i.val hi_pos hit).2
        have hx0 : xSeq p p' hp' ⟨0, hp'⟩ = 0 := xSeq_zero hp'
        simp only [hx0, Nat.sub_zero] at h_bound
        have heq_j : (⟨(⟨0, hp'⟩ : Fin p').val + i.val, hit⟩ : Fin p') = i := by
          ext; simp
        rw [heq_j] at h_bound
        -- Now xSeq(i) ≤ ceiling(i * p / p') = (i * p + p' - 1) / p'
        -- Since i ≤ q' - 1, this is ≤ ((q'-1) * p + p' - 1) / p' < q
        have h_ceil_bound : (i.val * p + p' - 1) / p' < q := by
          have h_ip_bound : i.val * p ≤ (q' - 1) * p := Nat.mul_le_mul_right p hi_bound
          have h_key : ((q' - 1) * p + p' - 1) / p' < q := by
            -- (q' - 1) * p < q' * p = q * p' + 1, so (q'-1)*p ≤ q*p'
            have hqp : q' * p = q * p' + 1 := by
              calc q' * p = p * q' := Nat.mul_comm q' p
                _ = q * p' + 1 := by omega
            have h1 : (q' - 1) * p + p = q' * p := by
              have : q' - 1 + 1 = q' := Nat.sub_add_cancel hq'
              calc (q' - 1) * p + p = (q' - 1 + 1) * p := by ring
                _ = q' * p := by rw [this]
            have h2 : (q' - 1) * p < q' * p := by omega
            have h3 : (q' - 1) * p ≤ q * p' := by
              have hlt : (q' - 1) * p < q * p' + 1 := by
                calc (q' - 1) * p < q' * p := h2
                  _ = q * p' + 1 := hqp
              omega
            have h4 : (q' - 1) * p + p' - 1 < q * p' + p' - 1 := by omega
            have h5 : q * p' + p' - 1 < (q + 1) * p' := by
              have : (q + 1) * p' = q * p' + p' := by ring
              omega
            have h6 : (q' - 1) * p + p' - 1 < (q + 1) * p' := Nat.lt_trans h4 h5
            have h7 : ((q' - 1) * p + p' - 1) / p' < q + 1 :=
              Nat.div_lt_iff_lt_mul hp' |>.mpr h6
            -- From Bezout: (q' - 1) * p + p = q' * p = q * p' + 1
            -- So (q' - 1) * p + p' - 1 = q * p' + 1 - p + p' - 1 = q * p' + p' - p < q * p'
            have h_qm1_p : (q' - 1) * p + p' - 1 = q * p' + p' - p := by
              have hbez : (q' - 1) * p + p = q' * p := by
                have hsub : q' - 1 + 1 = q' := Nat.sub_add_cancel hq'
                calc (q' - 1) * p + p = (q' - 1 + 1) * p := by ring
                  _ = q' * p := by rw [hsub]
              omega
            have h8 : (q' - 1) * p + p' - 1 < q * p' := by omega
            exact Nat.div_lt_iff_lt_mul hp' |>.mpr h8
          have h_num_bound : i.val * p + p' - 1 ≤ (q' - 1) * p + p' - 1 := by omega
          calc (i.val * p + p' - 1) / p' ≤ ((q' - 1) * p + p' - 1) / p' :=
              Nat.div_le_div_right h_num_bound
            _ < q := h_key
        omega
    omega
  · -- Case i ≥ q': xSeq(i) ≥ xSeq(q') = q + 1 > q
    push_neg at hi
    have hxi_ge : xSeq p p' hp' i ≥ q + 1 := by
      by_cases heq_i : i.val = q'
      · have : i = ⟨q', hq'_lt_p'⟩ := Fin.ext heq_i
        rw [this, hxq'_eq]
      · have hlt : q' < i.val := Nat.lt_of_le_of_ne hi (Ne.symm heq_i)
        have hmono := xSeq_strictMono hp' hp'_lt hbezout ⟨q', hq'_lt_p'⟩ i hlt
        omega
    omega

end WindingSet

/-! ## The Retraction Map

The retraction r : ZMod p → ℕ maps each vertex y to the largest x_i ≤ y.
This gives a graph homomorphism from K_{p/q} - v to K_{p'/q'}. -/

section Retraction

variable {p q p' q' : ℕ} [NeZero p]

omit [NeZero p] in
/-- From Bezout identity p * q' - q * p' = 1, p > q, and p' ≥ 2, we can derive q' < p'.
    Key insight: If q' ≥ p', then either
    - q' = p': then (p - q) * p' = 1, which requires p - q = 1 and p' = 1, contradicting p' ≥ 2.
    - q' > p': then the sum (p - q) * q' + q * (q' - p') = 1.
      But (p - q) * q' ≥ q' ≥ 3 (since q' > p' ≥ 2) and q * (q' - p') ≥ q ≥ 2. Sum ≥ 5 > 1.
    Both lead to contradiction with Bezout.

    Note: The hypothesis p > q is essential. Without it, (5, 7, 2, 3) is a counterexample:
    5 * 3 - 7 * 2 = 1 but q' = 3 > 2 = p'. -/
lemma q'_lt_p'_of_bezout (_hp' : 0 < p') (hp'_ge2 : 2 ≤ p') (hq' : 0 < q') (_hq'_lt_q : q' < q)
    (_hq : 2 ≤ q) (hp_gt_q : p > q) (hbezout : p * q' - q * p' = 1) : q' < p' := by
  by_contra hge; push_neg at hge
  -- From Bezout: p * q' = q * p' + 1
  have hbezout' : p * q' = q * p' + 1 := by omega
  -- Case 1: q' = p'. Then (p - q) * p' = 1.
  -- With p' ≥ 2 and p > q, (p - q) * p' ≥ 1 * 2 = 2 > 1. Contradiction.
  -- Case 2: q' > p'. Then (p - q) * q' + q * (q' - p') = p * q' - q * p' = 1.
  -- But each summand ≥ 2 when positive, giving sum ≥ 4 > 1.
  rcases Nat.lt_or_eq_of_le hge with hq'_gt | hq'_eq
  · -- q' > p': Both terms in (p - q) * q' + q * (q' - p') = 1 are positive.
    -- (p - q) * q' ≥ q' ≥ 3 (since q' > p' ≥ 2) and q * (q' - p') ≥ q ≥ 2.
    -- Sum ≥ 5 > 1. Contradiction.
    have hpq_pos : p - q > 0 := by omega
    have hq'p_pos : q' - p' > 0 := by omega
    have hge1 : (p - q) * q' ≥ q' := Nat.le_mul_of_pos_left q' hpq_pos
    have hge2 : q * (q' - p') ≥ q := Nat.le_mul_of_pos_right q hq'p_pos
    have hq'_ge3 : q' ≥ 3 := by omega  -- q' > p' ≥ 2 means q' ≥ 3
    -- (p - q) * q' ≥ q' ≥ 3, q * (q' - p') ≥ q ≥ 2, sum ≥ 5 > 1
    -- The algebraic identity: (p - q) * q' + q * (q' - p') = p * q' - q * p' = 1
    -- Need to verify this holds in ℕ when both differences are positive
    have hpq : p ≥ q := Nat.le_of_lt hp_gt_q
    have hqp : q' ≥ p' := Nat.le_of_lt hq'_gt
    have h1 : (p - q) * q' = p * q' - q * q' := Nat.sub_mul p q q'
    have h2 : q * (q' - p') = q * q' - q * p' := Nat.mul_sub q q' p'
    -- (p - q) * q' + q * (q' - p') = p * q' - q * q' + q * q' - q * p' = p * q' - q * p' = 1
    -- But (p - q) * q' ≥ 3 and q * (q' - p') ≥ 2, so sum ≥ 5 > 1. Contradiction.
    -- Use nlinarith with the expanded bounds
    nlinarith [Nat.mul_le_mul_right q' hpq, Nat.mul_le_mul_left q hqp]
  · -- q' = p': then (p - q) * q' = 1
    -- With q' = p' ≥ 2 and p > q, (p - q) * q' ≥ 1 * 2 = 2 > 1. Contradiction.
    have hq'_eq_p' : q' = p' := hq'_eq.symm
    have hpq : p ≥ q := Nat.le_of_lt hp_gt_q
    -- From Bezout: p * q' - q * p' = 1. With q' = p': p * q' - q * q' = 1
    have h1 : p * q' - q * q' = 1 := by simp only [hq'_eq_p'] at hbezout ⊢; exact hbezout
    have h2 : (p - q) * q' = p * q' - q * q' := Nat.sub_mul p q q'
    have h3 : (p - q) * q' = 1 := by omega
    -- With p > q, p - q ≥ 1, so (p - q) * q' ≥ 1 * q' ≥ q' ≥ 2 > 1. Contradiction.
    have h4 : (p - q) * q' ≥ q' := Nat.le_mul_of_pos_left q' (by omega : 0 < p - q)
    have hq'_ge2 : q' ≥ 2 := by omega  -- q' = p' ≥ 2
    omega  -- (p - q) * q' ≥ 2 > 1

omit [NeZero p] in
/-- The fraction graph condition is preserved by Stern-Brocot predecessors:
    if 2q ≤ p and p * q' - q * p' = 1, then 2q' ≤ p'. -/
lemma two_q'_le_p'_of_bezout (_hp' : 0 < p') (_hp'_ge2 : 2 ≤ p') (_hq' : 0 < q') (_hq'_lt_q : q' < q)
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hbezout : p * q' - q * p' = 1) : 2 * q' ≤ p' := by
  -- From Bezout: p * q' = q * p' + 1
  have hbezout' : p * q' = q * p' + 1 := by omega
  -- From 2q ≤ p: 2q * q' ≤ p * q' = q * p' + 1
  have h1 : 2 * q * q' ≤ q * p' + 1 := by
    calc 2 * q * q' ≤ p * q' := Nat.mul_le_mul_right q' h2q
      _ = q * p' + 1 := hbezout'
  -- Simplify: 2 * q' ≤ p' + 1/q (in rationals)
  -- Since 2 * q' and p' are integers and q ≥ 2, 2 * q' < p' + 1 means 2 * q' ≤ p'
  have h2 : 2 * q' * q ≤ q * p' + 1 := by linarith
  -- If 2 * q' > p', then 2 * q' ≥ p' + 1 (integers), so 2 * q' * q ≥ (p' + 1) * q = q * p' + q ≥ q * p' + 2
  -- But we have 2 * q' * q ≤ q * p' + 1 < q * p' + 2, contradiction.
  by_contra hgt; push_neg at hgt
  have hge : 2 * q' ≥ p' + 1 := hgt
  have h3 : 2 * q' * q ≥ (p' + 1) * q := Nat.mul_le_mul_right q hge
  have h4 : (p' + 1) * q = q * p' + q := by ring
  have h5 : 2 * q' * q ≥ q * p' + q := by omega
  have h6 : q * p' + q ≥ q * p' + 2 := by omega  -- since q ≥ 2
  omega

/-- The retraction sends y to the largest x_i with x_i ≤ y.val.
    This is the "floor" in the winding set. -/
noncomputable def retract (hp' : 0 < p') (y : ZMod p) : Fin p' :=
  -- Find the largest i such that xSeq p p' hp' i ≤ y.val
  -- Since x_0 = 0 ≤ y.val always, this is well-defined
  Finset.max' ((Finset.univ : Finset (Fin p')).filter (fun i => xSeq p p' hp' i ≤ y.val))
    (by simp only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
        use ⟨0, hp'⟩; simp [xSeq_zero])

/-- The embedding sends i to x_i (as ZMod p). -/
def embed (hp' : 0 < p') (i : Fin p') : ZMod p :=
  (xSeq p p' hp' i : ZMod p)

set_option maxHeartbeats 600000 in
-- Large proof with extensive case analysis on gap arithmetic
/-- The retraction preserves adjacency: if y ~ y' in K_{p/q} - q,
    then retract(y) ~ retract(y') in K_{p'/q'}. -/
theorem retract_preserves_adj [NeZero p'] (hp' : 0 < p') (hp'_lt : p' < p)
    (hq' : 0 < q') (hq'_lt : q' < q) (hq : 2 ≤ q) (h2q : 2 * q ≤ p)
    (_hcoprime : Nat.Coprime p q) (hbezout : p * q' - q * p' = 1)
    (y y' : ZMod p) (hy : y ≠ (q : ZMod p)) (hy' : y' ≠ (q : ZMod p))
    (hadj : (Kpq p q).Adj y y') :
    (Kpq p' q').Adj ((retract hp' y).val : ZMod p') ((retract hp' y').val : ZMod p') := by
  -- The proof follows Step 4 of the markdown plan.
  -- Let r = retract(y), r' = retract(y'). We need: r ≠ r' ∧ q' ≤ circDist(r, r').
  set r := retract hp' y with hr_def
  set r' := retract hp' y' with hr'_def
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  -- Extract adjacency info: y ≠ y' and circDist(y, y') ≥ q
  have hne : y ≠ y' := by
    unfold Kpq at hadj
    simp only [ne_eq] at hadj
    exact hadj.1
  have hdist : q ≤ circDist p y y' := by
    unfold Kpq at hadj
    simp only [ne_eq] at hadj
    exact hadj.2
  -- Key properties of retract: xSeq(r) ≤ y.val and y.val < xSeq(r+1) (or y.val < p if r = p'-1)
  have h_r_mem : xSeq p p' hp' r ≤ y.val := by
    unfold retract at hr_def
    have hnonempty : ((Finset.univ : Finset (Fin p')).filter
        (fun i => xSeq p p' hp' i ≤ y.val)).Nonempty := by
      simp only [Finset.filter_nonempty_iff]
      use ⟨0, hp'⟩
      simp only [Finset.mem_univ, xSeq_zero, Nat.zero_le, and_self]
    have hmax := Finset.max'_mem _ hnonempty
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmax
    rw [← hr_def] at hmax
    exact hmax
  have h_r'_mem : xSeq p p' hp' r' ≤ y'.val := by
    unfold retract at hr'_def
    have hnonempty : ((Finset.univ : Finset (Fin p')).filter
        (fun i => xSeq p p' hp' i ≤ y'.val)).Nonempty := by
      simp only [Finset.filter_nonempty_iff]
      use ⟨0, hp'⟩
      simp only [Finset.mem_univ, xSeq_zero, Nat.zero_le, and_self]
    have hmax := Finset.max'_mem _ hnonempty
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmax
    rw [← hr'_def] at hmax
    exact hmax
  -- Part 1: r ≠ r' (proof by contradiction)
  -- If r = r', then y, y' are in the same interval [xSeq(r), xSeq(r+1)).
  -- The interval size is < q (by xSeq_gap_small for r ≥ 1) or = q+1 (for r = 0).
  -- In both cases, circDist(y, y') < q, contradicting adjacency.
  -- Exception: r = 0 gives gap = q+1, but then y' - y = q forces y' = q (contradiction).
  -- First prove hdist_r (q' ≤ circDist(r, r')), then hr_ne_r' follows.
  -- This follows Step 4.2 of the markdown proof.
  have hdist_r : q' ≤ circDist p' r.val r'.val := by
    by_contra hlt
    push_neg at hlt
    unfold circDist at hlt
    have hr_lt : r.val < p' := r.isLt
    have hr'_lt : r'.val < p' := r'.isLt
    -- Key derived bound: q < p
    have hq_lt : q < p := by omega

    -- Upper bound property for retract: if k > r then y.val < xSeq(k)
    have h_r_upper : ∀ (k : Fin p'), r.val < k.val → y.val < xSeq p p' hp' k := by
      intro k hrk
      by_contra hle; push_neg at hle
      have h_k_in : k ∈ (Finset.univ : Finset (Fin p')).filter (fun i => xSeq p p' hp' i ≤ y.val) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hle
      have : k.val ≤ r.val := Finset.le_max' _ k h_k_in
      omega
    have h_r'_upper : ∀ (k : Fin p'), r'.val < k.val → y'.val < xSeq p p' hp' k := by
      intro k hr'k
      by_contra hle; push_neg at hle
      have h_k_in : k ∈ (Finset.univ : Finset (Fin p')).filter (fun i => xSeq p p' hp' i ≤ y'.val) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hle
      have : k.val ≤ r'.val := Finset.le_max' _ k h_k_in
      omega

    -- ZMod value simplification
    have hr_val : (r.val : ZMod p').val = r.val := ZMod.val_natCast_of_lt hr_lt
    have hr'_val : (r'.val : ZMod p').val = r'.val := ZMod.val_natCast_of_lt hr'_lt

    -- min condition: either forward or backward gap < q'
    rw [min_lt_iff] at hlt

    -- Helper: xSeq is monotone (from strict monotonicity)
    have xSeq_mono : ∀ (i j : Fin p'), i ≤ j → xSeq p p' hp' i ≤ xSeq p p' hp' j := by
      intro i j hij
      rcases hij.lt_or_eq with hlt | heq
      · exact le_of_lt (xSeq_strictMono hp' hp'_lt hbezout i j hlt)
      · simp [heq]

    -- When r < r', we have y < y' by interval monotonicity
    have h_mono : r.val < r'.val → y.val < y'.val := by
      intro h_r_lt_r'
      have h_r1_lt_p' : r.val + 1 < p' := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt h_r_lt_r') hr'_lt
      have hr_lt_r1 : r.val < r.val + 1 := Nat.lt_succ_self _
      have hy_up := h_r_upper ⟨r.val + 1, h_r1_lt_p'⟩ hr_lt_r1
      have hle : (⟨r.val + 1, h_r1_lt_p'⟩ : Fin p') ≤ r' := Fin.le_def.mpr (Nat.succ_le_of_lt h_r_lt_r')
      have hmono : xSeq p p' hp' ⟨r.val + 1, h_r1_lt_p'⟩ ≤ xSeq p p' hp' r' := xSeq_mono _ _ hle
      omega

    have h_mono' : r'.val < r.val → y'.val < y.val := by
      intro h_r'_lt_r
      have h_r'1_lt_p' : r'.val + 1 < p' := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt h_r'_lt_r) hr_lt
      have hr'_lt_r'1 : r'.val < r'.val + 1 := Nat.lt_succ_self _
      have hy'_up := h_r'_upper ⟨r'.val + 1, h_r'1_lt_p'⟩ hr'_lt_r'1
      have hle : (⟨r'.val + 1, h_r'1_lt_p'⟩ : Fin p') ≤ r := Fin.le_def.mpr (Nat.succ_le_of_lt h_r'_lt_r)
      have hmono : xSeq p p' hp' ⟨r'.val + 1, h_r'1_lt_p'⟩ ≤ xSeq p p' hp' r := xSeq_mono _ _ hle
      omega

    -- Main case analysis
    rcases Nat.lt_trichotomy r.val r'.val with h_lt | h_eq | h_gt
    · -- Case 1: r < r' (forward direction)
      have h_sub_val : ((r'.val : ZMod p') - (r.val : ZMod p')).val = r'.val - r.val := by
        have hle : (r.val : ZMod p').val ≤ (r'.val : ZMod p').val := by
          rw [hr_val, hr'_val]; omega
        rw [ZMod.val_sub hle, hr'_val, hr_val]
      set t := r'.val - r.val with ht_def
      have ht_pos : 0 < t := by omega
      have ht_lt_p' : t < p' := by omega
      -- y < y' by monotonicity
      have hyy' : y.val < y'.val := h_mono h_lt

      rcases hlt with h_fwd | h_bwd
      · -- Forward gap < q'
        rw [h_sub_val] at h_fwd
        have ht_lt_q' : t < q' := h_fwd
        -- y' < xSeq(r'+1) ≤ xSeq(r+q') when r'+1 ≤ r+q' (i.e., t+1 ≤ q', which holds since t < q')
        by_cases hrq'_lt : r.val + q' < p'
        · by_cases hr_zero : r.val = 0
          · -- r = 0: xSeq(q') - xSeq(0) = q + 1, but y' ≠ q
            have hr0 : r = ⟨0, hp'⟩ := Fin.ext hr_zero
            have hgap := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout ⟨0, hp'⟩ (by omega : 0 + q' < p')).1 rfl
            simp only [xSeq_zero, Nat.sub_zero, Nat.zero_add] at hgap
            -- r = 0 means t = r' - 0 = r' and t < q', so r' < q', hence r' + 1 ≤ q'
            have hq'_lt_p' : q' < p' := by omega
            have hr'_lt_q' : r'.val < q' := by
              have ht_eq : t = r'.val := by simp [ht_def, hr_zero]
              omega
            have hr'1_lt : r'.val + 1 < p' := by omega
            have hy'_up := h_r'_upper ⟨r'.val + 1, hr'1_lt⟩ (Nat.lt_succ_self _)
            have hr'1_le_q' : r'.val + 1 ≤ q' := Nat.succ_le_of_lt hr'_lt_q'
            have hmono' : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≤ xSeq p p' hp' ⟨q', hq'_lt_p'⟩ :=
              xSeq_mono ⟨r'.val + 1, hr'1_lt⟩ ⟨q', hq'_lt_p'⟩ (Fin.le_def.mpr hr'1_le_q')
            -- xSeq(q') = q + 1 (from hgap), so y' < xSeq(r'+1) ≤ xSeq(q') = q + 1
            have hgap' : xSeq p p' hp' ⟨q', hq'_lt_p'⟩ = q + 1 := hgap
            have hy'_lt : y'.val < q + 1 := by
              calc y'.val < xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ := hy'_up
                _ ≤ xSeq p p' hp' ⟨q', hq'_lt_p'⟩ := hmono'
                _ = q + 1 := hgap'
            have hq_val : (q : ZMod p).val = q := ZMod.val_natCast_of_lt hq_lt
            have hy'_ne_q : y'.val ≠ q := by intro h; exact hy' (ZMod.val_injective p (h.trans hq_val.symm))
            have hy'_lt_q : y'.val < q := by omega
            have hdiff : y'.val - y.val < q := by omega
            have hcirc : circDist p y y' < q := by
              unfold circDist
              have hsub : (y' - y).val = y'.val - y.val := ZMod.val_sub (by omega)
              calc min (y' - y).val (y - y').val ≤ (y' - y).val := Nat.min_le_left _ _
                _ = y'.val - y.val := hsub
                _ < q := hdiff
            omega
          · -- r ≥ 1: xSeq(r+q') - xSeq(r) = q
            have hgap := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout r hrq'_lt).2 hr_zero
            -- t = r' - r < q', so r' + 1 ≤ r + q', and r' + 1 < p' (since r + q' < p')
            have hr'1_le_rq' : r'.val + 1 ≤ r.val + q' := by omega
            have hr'1_lt : r'.val + 1 < p' := Nat.lt_of_le_of_lt hr'1_le_rq' hrq'_lt
            have hy'_up := h_r'_upper ⟨r'.val + 1, hr'1_lt⟩ (Nat.lt_succ_self _)
            have hmono' : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≤ xSeq p p' hp' ⟨r.val + q', hrq'_lt⟩ :=
              xSeq_mono ⟨r'.val + 1, hr'1_lt⟩ ⟨r.val + q', hrq'_lt⟩ (Fin.le_def.mpr hr'1_le_rq')
            have hy'_bound : y'.val < xSeq p p' hp' ⟨r.val + q', hrq'_lt⟩ :=
              Nat.lt_of_lt_of_le hy'_up hmono'
            have hdiff : y'.val - y.val < q := by
              calc y'.val - y.val
                  < xSeq p p' hp' ⟨r.val + q', hrq'_lt⟩ - y.val := by omega
                _ ≤ xSeq p p' hp' ⟨r.val + q', hrq'_lt⟩ - xSeq p p' hp' r := by omega
                _ = q := hgap
            have hcirc : circDist p y y' < q := by
              unfold circDist
              have hsub : (y' - y).val = y'.val - y.val := ZMod.val_sub (by omega)
              calc min (y' - y).val (y - y').val ≤ (y' - y).val := Nat.min_le_left _ _
                _ = y'.val - y.val := hsub
                _ < q := hdiff
            omega
        · -- r + q' ≥ p': edge case
          push_neg at hrq'_lt
          -- Key insight: since t < q' and r + t = r' < p', we can still bound the gap
          have hrt_lt : r.val + t < p' := by omega -- r + t = r'
          by_cases hr'_last : r'.val + 1 < p'
          · -- Sub-case A: r' is not the last index
            -- Since r + q' ≥ p' and r' + 1 < p' and r' = r + t, we have t + 1 < q'
            have ht1_lt_q' : t + 1 < q' := by omega
            have ht1_le : t + 1 ≤ q' - 1 := by omega
            have ht1_pos : 0 < t + 1 := Nat.succ_pos t
            have hrt1_lt : r.val + (t + 1) < p' := by omega
            have hgap_small := xSeq_gap_small hp' hp'_lt hq' hq'_lt hbezout r (t + 1) ht1_pos ht1_le hrt1_lt
            -- xSeq(r + t + 1) - xSeq(r) < q, i.e., xSeq(r' + 1) - xSeq(r) < q
            have hr1_eq : r.val + (t + 1) = r'.val + 1 := by omega
            have hy'_up := h_r'_upper ⟨r'.val + 1, hr'_last⟩ (Nat.lt_succ_self _)
            have hxeq : xSeq p p' hp' ⟨r.val + (t + 1), hrt1_lt⟩ = xSeq p p' hp' ⟨r'.val + 1, hr'_last⟩ := by
              congr 1; ext; exact hr1_eq
            have hdiff : y'.val - y.val < q := by
              calc y'.val - y.val
                  < xSeq p p' hp' ⟨r'.val + 1, hr'_last⟩ - y.val := by omega
                _ ≤ xSeq p p' hp' ⟨r'.val + 1, hr'_last⟩ - xSeq p p' hp' r := by omega
                _ = xSeq p p' hp' ⟨r.val + (t + 1), hrt1_lt⟩ - xSeq p p' hp' r := by rw [hxeq]
                _ < q := hgap_small
            have hcirc : circDist p y y' < q := by
              unfold circDist
              have hsub : (y' - y).val = y'.val - y.val := ZMod.val_sub (by omega)
              calc min (y' - y).val (y - y').val ≤ (y' - y).val := Nat.min_le_left _ _
                _ = y'.val - y.val := hsub
                _ < q := hdiff
            omega
          · -- Sub-case B: r' = p' - 1 (last index)
            -- Edge case: r + q' ≥ p' and r' = p' - 1
            -- Key insight: when q' = 1, we get r ≥ p' - 1 but r < r' = p' - 1, contradiction
            -- when q' ≥ 2, we need xSeq(p' - q') ≥ p - q (Bezout arithmetic)
            push_neg at hr'_last
            have hr'_eq : r'.val = p' - 1 := by omega
            exfalso
            by_cases hq'_one : q' = 1
            · -- q' = 1: r + 1 ≥ p' means r ≥ p' - 1, but r < r' = p' - 1 is impossible
              omega
            · -- q' ≥ 2: needs Bezout-based bound (edge case)
              -- The detailed proof: xSeq(p' - q') ≥ p - q implies y ≥ p - q, so y' - y < q
              -- First establish that p' ≥ 2 (from r < r' = p' - 1)
              have hp'_ge2 : 2 ≤ p' := by
                have : r.val < r'.val := h_lt
                have : r'.val = p' - 1 := hr'_eq
                omega
              -- Get p > q from h2q
              have hp_gt_q : p > q := by omega
              -- Apply q'_lt_p'_of_bezout to get q' < p'
              have hq'_ge2 : q' ≥ 2 := by omega
              have hq'_lt_p' : q' < p' := q'_lt_p'_of_bezout hp' hp'_ge2 hq' hq'_lt hq hp_gt_q hbezout
              -- From r + q' ≥ p', we get r ≥ p' - q'
              have hr_ge : r.val ≥ p' - q' := by omega
              -- By xSeq_pq'_bound: xSeq(p' - q') ≥ p - q
              have hpq'_idx : p' - q' < p' := Nat.sub_lt hp' hq'
              have hbound : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ ≥ p - q :=
                xSeq_pq'_bound hp' hp'_ge2 hq' hq'_lt_p' hbezout
              -- By monotonicity: xSeq(r) ≥ xSeq(p' - q')
              have hmono : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ ≤ xSeq p p' hp' r := by
                apply xSeq_mono
                exact Fin.le_def.mpr hr_ge
              -- So y.val ≥ xSeq(r) ≥ p - q
              have hy_ge : y.val ≥ p - q := by
                calc p - q ≤ xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ := hbound
                  _ ≤ xSeq p p' hp' r := hmono
                  _ ≤ y.val := h_r_mem
              -- y'.val < p and y.val ≥ p - q gives y' - y < q
              have hy'_lt_p : y'.val < p := ZMod.val_lt y'
              have hdiff : y'.val - y.val < q := by omega
              -- circDist(y, y') < q contradicts hdist : q ≤ circDist
              have hcirc : circDist p y y' < q := by
                unfold circDist
                have hsub : (y' - y).val = y'.val - y.val := ZMod.val_sub (by omega)
                calc min (y' - y).val (y - y').val ≤ (y' - y).val := Nat.min_le_left _ _
                  _ = y'.val - y.val := hsub
                  _ < q := hdiff
              omega
      · -- Backward gap < q' (with r < r')
        -- The backward gap is (r - r').val = p' - t in ZMod p' when r < r'.
        -- h_bwd says backward gap < q', so p' - t < q', i.e., t > p' - q'.
        -- Key insight: When t > p' - q' and r < r', we have r = r' - t < p' - (p' - q') = q'.
        -- First compute backward gap value
        have h_bwd_eq : (↑↑r - ↑↑r' : ZMod p').val = p' - t := by
          have hne : (↑↑r' : ZMod p') - (↑↑r : ZMod p') ≠ 0 := by
            intro heq
            have : (↑↑r' - ↑↑r : ZMod p').val = 0 := by simp [heq]
            rw [h_sub_val] at this
            omega
          haveI : NeZero ((↑↑r' : ZMod p') - (↑↑r : ZMod p')) := ⟨hne⟩
          have hneg := ZMod.val_neg_of_ne_zero (a := (↑↑r' : ZMod p') - (↑↑r : ZMod p'))
          simp only [neg_sub] at hneg
          rw [hneg, h_sub_val]
        rw [h_bwd_eq] at h_bwd
        have ht_gt : t > p' - q' := by omega
        -- Case split on q'
        by_cases hq'_one : q' = 1
        · -- q' = 1: t > p' - 1, so t ≥ p', but t < p'. Contradiction.
          omega
        · -- q' ≥ 2: r ≤ q' - 2 (from t ≥ p' - q' + 1 and r = r' - t < p' - t ≤ q' - 1)
          -- First establish key bounds
          have hp'_ge2 : 2 ≤ p' := by
            -- From q' ≥ 2 and backward gap < q', we need p' ≥ 2
            -- The backward gap p' - t < q' means t > p' - q' ≥ p' - (q' - 1) = p' - q' + 1
            -- But t = r' - r ≤ p' - 1 - 0 = p' - 1
            -- So p' - 1 ≥ t > p' - q', giving q' > 1, i.e., q' ≥ 2
            -- For t to exist (t ≥ 1), we need p' ≥ 2
            by_contra h; push_neg at h
            have hp'_one : p' = 1 := by omega
            have ht_bound : t < p' := ht_lt_p'
            omega
          have hp_gt_q : p > q := by omega
          have hq'_lt_p' : q' < p' := q'_lt_p'_of_bezout hp' hp'_ge2 hq' hq'_lt hq hp_gt_q hbezout
          -- r ≤ q' - 2 (from r = r' - t < p' - t ≤ p' - (p' - q' + 1) = q' - 1)
          have hr_le_q'_minus2 : r.val ≤ q' - 2 := by
            have ht_ge : t ≥ p' - q' + 1 := by omega
            have : r.val = r'.val - t := by omega
            have hr'_bound : r'.val ≤ p' - 1 := by omega
            omega
          have hr_lt_q' : r.val < q' := by omega
          have hr1_lt : r.val + 1 < p' := by omega
          have hy_up := h_r_upper ⟨r.val + 1, hr1_lt⟩ (Nat.lt_succ_self _)
          have hr1_le_q' : r.val + 1 ≤ q' := Nat.succ_le_of_lt hr_lt_q'
          have hmono_y : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ xSeq p p' hp' ⟨q', hq'_lt_p'⟩ :=
            xSeq_mono ⟨r.val + 1, hr1_lt⟩ ⟨q', hq'_lt_p'⟩ (Fin.le_def.mpr hr1_le_q')
          -- xSeq(q') = q + 1 (from xSeq_gap_q' with i = 0)
          have hgap_q' := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout ⟨0, hp'⟩ (by omega : 0 + q' < p')).1 rfl
          simp only [xSeq_zero, Nat.sub_zero, Nat.zero_add] at hgap_q'
          have hy_lt : y.val < q + 1 := by
            calc y.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ := hy_up
              _ ≤ xSeq p p' hp' ⟨q', hq'_lt_p'⟩ := hmono_y
              _ = q + 1 := hgap_q'
          have hq_val : (q : ZMod p).val = q := ZMod.val_natCast_of_lt hq_lt
          have hy_ne_q : y.val ≠ q := by intro h; exact hy (ZMod.val_injective p (h.trans hq_val.symm))
          have hy_lt_q : y.val < q := by omega
          -- r' > p' - q', so y' ≥ xSeq(r') > xSeq(p' - q') ≥ p - q
          have hp'_ge2 : 2 ≤ p' := by omega
          have hp_gt_q : p > q := by omega
          have hq'_lt_p'_strict : q' < p' := q'_lt_p'_of_bezout hp' hp'_ge2 hq' hq'_lt hq hp_gt_q hbezout
          have hr'_ge : r'.val ≥ p' - q' + 1 := by omega
          have hpq'_idx : p' - q' < p' := Nat.sub_lt hp' hq'
          have hr'_ge_idx : r'.val > p' - q' := by omega
          -- xSeq(r') > xSeq(p' - q') (strict monotonicity)
          have hmono_strict : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ < xSeq p p' hp' r' := by
            apply xSeq_strictMono hp' hp'_lt hbezout
            exact Fin.lt_def.mpr hr'_ge_idx
          have hbound : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ ≥ p - q :=
            xSeq_pq'_bound hp' hp'_ge2 hq' hq'_lt_p'_strict hbezout
          have hy'_ge : y'.val ≥ xSeq p p' hp' r' := h_r'_mem
          have hy'_lt_p : y'.val < p := ZMod.val_lt y'
          -- Key insight: y' ≥ xSeq(r') and y < xSeq(r + 1), so y' - y > xSeq(r') - xSeq(r + 1)
          -- Since xSeq(r') > xSeq(p' - q') ≥ p - q and xSeq(r + 1) ≤ xSeq(q' - 1) < q + 1,
          -- the gap xSeq(r') - xSeq(r + 1) accounts for most of p - q.
          -- The "+1" from y' ≥ xSeq(r') vs y ≤ xSeq(r + 1) - 1 gives strict inequality.
          -- First show y' - y ≥ xSeq(r') - xSeq(r + 1) + 1 (since y ≤ xSeq(r+1) - 1)
          -- xSeq(i) ≥ 1 for i ≥ 1, so y < xSeq(r+1) implies y ≤ xSeq(r+1) - 1
          have hxSeq_pos : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≥ 1 := by
            unfold xSeq
            have hr1_ne0 : r.val + 1 ≠ 0 := by omega
            simp only [hr1_ne0, ↓reduceIte]
            have h1 : (r.val + 1) * p ≥ p := by
              have : 1 * p ≤ (r.val + 1) * p := Nat.mul_le_mul_right p (by omega : 1 ≤ r.val + 1)
              simp only [one_mul] at this
              exact this
            have hp'_pos : p' > 0 := hp'
            have hp_ge_p' : p ≥ p' := Nat.le_of_lt hp'_lt
            exact Nat.le_div_iff_mul_le hp'_pos |>.mpr (by omega)
          have hy_le : y.val ≤ xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - 1 := by
            have h := hy_up
            omega
          have hdiff_ge : y'.val - y.val ≥ xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ + 1 := by
            have h1 : y'.val ≥ xSeq p p' hp' r' := hy'_ge
            have h2 : y.val ≤ xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - 1 := hy_le
            omega
          -- Now show xSeq(r') - xSeq(r + 1) ≥ p - q - 1 using the bounds
          -- xSeq(r') > xSeq(p' - q') ≥ p - q, so xSeq(r') ≥ p - q + 1
          have hxr'_ge : xSeq p p' hp' r' ≥ p - q + 1 := by
            have h1 : xSeq p p' hp' r' > xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ := hmono_strict
            have h2 : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ ≥ p - q := hbound
            omega
          -- xSeq(r + 1) ≤ xSeq(q' - 1) < xSeq(q') = q + 1, so xSeq(r + 1) ≤ q
          have hq'_minus1_lt : q' - 1 < p' := by omega
          have hr1_le_q'_minus1 : r.val + 1 ≤ q' - 1 := by omega
          have hmono_xr1 : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ xSeq p p' hp' ⟨q' - 1, hq'_minus1_lt⟩ :=
            xSeq_mono ⟨r.val + 1, hr1_lt⟩ ⟨q' - 1, hq'_minus1_lt⟩ (Fin.le_def.mpr hr1_le_q'_minus1)
          have hxq'_minus1_lt : xSeq p p' hp' ⟨q' - 1, hq'_minus1_lt⟩ < xSeq p p' hp' ⟨q', hq'_lt_p'⟩ := by
            apply xSeq_strictMono hp' hp'_lt hbezout
            exact Fin.lt_def.mpr (by omega : q' - 1 < q')
          have hxr1_le : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ q := by
            have h_chain : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ < q + 1 := by
              calc xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩
                  ≤ xSeq p p' hp' ⟨q' - 1, hq'_minus1_lt⟩ := hmono_xr1
                _ < xSeq p p' hp' ⟨q', hq'_lt_p'⟩ := hxq'_minus1_lt
                _ = q + 1 := hgap_q'
            omega
          -- Combined: xSeq(r') - xSeq(r + 1) ≥ (p - q + 1) - q = p - 2q + 1
          have hgap_ge : xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≥ p - 2 * q + 1 := by
            have h1 : xSeq p p' hp' r' ≥ p - q + 1 := hxr'_ge
            have h2 : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ q := hxr1_le
            omega
          -- So y' - y ≥ (p - 2q + 1) + 1 = p - 2q + 2
          have hdiff_lower : y'.val - y.val ≥ p - 2 * q + 2 := by
            calc y'.val - y.val ≥ xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ + 1 := hdiff_ge
              _ ≥ (p - 2 * q + 1) + 1 := by omega
              _ = p - 2 * q + 2 := by ring
          -- To show circDist < q, it suffices to show y' - y > p - q,
          -- since then p - (y' - y) < q and circDist = min(y' - y, p - (y' - y)) < q.
          -- From y' ≥ xSeq(r') and y < xSeq(r+1) (so y ≤ xSeq(r+1) - 1):
          --   y' - y ≥ xSeq(r') - xSeq(r+1) + 1
          -- So it suffices to show xSeq(r') - xSeq(r+1) ≥ p - q.
          have hgap_key : xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≥ p - q := by
            -- The index span from (r+1) to r' is t - 1 ≥ p' - q'.
            -- From Bezout: (p' - q') * p = (p - q) * p' - 1, so xSeq gap for p' - q'
            -- indices is close to p - q. The cases where gap = p - q - 1 correspond
            -- exactly to circDist(r, r') = q' (not < q'), so under our assumption
            -- circDist < q', the gap is always ≥ p - q.
            -- Case split on whether s = t - 1 = p' - q' (minimum) or s > p' - q'.
            -- Let s = t - 1 be the index span from (r + 1) to r'.
            have hs_def : r'.val - (r.val + 1) = t - 1 := by omega
            have hs_ge : t - 1 ≥ p' - q' := by omega
            have hsr'_eq : r.val + 1 + (t - 1) = r'.val := by omega
            have hsr'_lt : r.val + 1 + (t - 1) < p' := by omega
            -- Use xSeq_gap_bound with index span (t - 1)
            have hspan_pos : t - 1 > 0 := by omega
            have hgap_bound := xSeq_gap_bound hp' hp'_lt ⟨r.val + 1, hr1_lt⟩ (t - 1) hspan_pos hsr'_lt
            have hgap_lower : xSeq p p' hp' ⟨r.val + 1 + (t - 1), hsr'_lt⟩ -
                              xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≥ (t - 1) * p / p' := hgap_bound.1
            have heq_idx : (⟨r.val + 1 + (t - 1), hsr'_lt⟩ : Fin p') = r' := by
              ext; simp only [hsr'_eq]
            rw [heq_idx] at hgap_lower
            -- Key: (t - 1) * p / p' ≥ p - q when t - 1 ≥ p' - q'
            -- From Bezout: (p' - q') * p = (p - q) * p' - 1
            have hbezout' : p * q' = q * p' + 1 := by omega
            have hqp_bound : q' * p = q * p' + 1 := by rw [Nat.mul_comm]; exact hbezout'
            have hp'q'_mul : (p' - q') * p = (p - q) * p' - 1 := by
              have hq'_le : q' ≤ p' := Nat.le_of_lt hq'_lt_p'
              have h1 : (p' - q') * p = p' * p - q' * p := Nat.sub_mul p' q' p
              have h2 : q' * p = q * p' + 1 := hqp_bound
              have h3 : p' * p = p * p' := Nat.mul_comm p' p
              have h4 : q' * p ≤ p' * p := Nat.mul_le_mul_right p hq'_le
              have hp_ge_q : p ≥ q := by
                have hpq'_gt : p * q' > q * p' := by omega
                by_contra h; push_neg at h
                have h1' : p * q' ≤ q * q' := Nat.mul_le_mul_right q' (Nat.le_of_lt h)
                have h2' : q * q' < q * p' :=
                  Nat.mul_lt_mul_of_pos_left hq'_lt_p' (Nat.lt_of_le_of_lt (Nat.zero_le p) h)
                omega
              have hpq_le_pp : q * p' + 1 ≤ p * p' := by
                calc q * p' + 1 = q' * p := hqp_bound.symm
                  _ ≤ p' * p := h4
                  _ = p * p' := h3
              calc (p' - q') * p = p' * p - q' * p := h1
                _ = p' * p - (q * p' + 1) := by rw [h2]
                _ = p * p' - (q * p' + 1) := by rw [h3]
                _ = p * p' - q * p' - 1 := by omega
                _ = (p - q) * p' - 1 := by rw [Nat.sub_mul]
            -- Case split: t - 1 = p' - q' or t - 1 > p' - q'
            rcases eq_or_lt_of_le hs_ge with heq | hlt
            · -- Case: t - 1 = p' - q' (minimum span)
              -- In this case, we use the ceiling structure to show gap = p - q exactly
              -- The key is that ((r+1) * p) mod p' ≥ 2 when r + 1 ∈ [1, q' - 1]
              -- which makes ceil((r+1)*p/p' - 1/p') = ceil((r+1)*p/p')
              -- and thus gap = p - q.
              -- Use the floor bound from xSeq positions.
              -- (t - 1) * p / p' = (p' - q') * p / p' = ((p - q) * p' - 1) / p'
              have hdiv_eq : (t - 1) * p / p' = ((p - q) * p' - 1) / p' := by
                rw [← heq, hp'q'_mul]
              -- ((p - q) * p' - 1) / p' = p - q - 1 by floor division
              have hfloor : ((p - q) * p' - 1) / p' = p - q - 1 := by
                have hp_gt_q : p > q := hp_gt_q
                have hpq_pos : p - q > 0 := by omega
                have hpq_mul_pos : (p - q) * p' > 0 := Nat.mul_pos hpq_pos hp'
                -- (p - q) * p' - 1 = (p - q - 1) * p' + (p' - 1)
                have hdecomp : (p - q) * p' - 1 = (p - q - 1) * p' + (p' - 1) := by
                  have hsub_cancel : p - q - 1 + 1 = p - q := Nat.sub_add_cancel hpq_pos
                  have h1 : (p - q) * p' = (p - q - 1 + 1) * p' := by rw [hsub_cancel]
                  have h2 : (p - q - 1 + 1) * p' = (p - q - 1) * p' + p' := by ring
                  rw [h1, h2]; omega
                have hcomm : (p - q - 1) * p' + (p' - 1) = (p' - 1) + p' * (p - q - 1) := by ring
                rw [hdecomp, hcomm, Nat.add_mul_div_left _ _ hp']
                have hrem_lt : p' - 1 < p' := by omega
                simp only [Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
              -- Floor bound gives gap ≥ p - q - 1. Need gap ≥ p - q.
              -- Use xSeq_pq'_eq and strict monotonicity to pin down the gap exactly.
              have hbound_pq' : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ = p - q := by
                exact xSeq_pq'_eq hp' hp'_lt hp'_ge2 hq' hq'_lt_p' hbezout
              -- From hmono_strict: xSeq(p' - q') < xSeq(r')
              -- So xSeq(r') ≥ xSeq(p' - q') + 1 = p - q + 1
              have hxr'_strict : xSeq p p' hp' r' ≥ p - q + 1 := by
                have h1 : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ < xSeq p p' hp' r' := hmono_strict
                rw [hbound_pq'] at h1
                omega
              -- Use the upper bound from xSeq_gap_bound to show gap ≤ p - q:
              have hgap_upper := hgap_bound.2
              have hgap_upper' : xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤
                                 ((t - 1) * p + p' - 1) / p' := by rw [heq_idx] at hgap_upper; exact hgap_upper
              -- ((t - 1) * p + p' - 1) / p' when t - 1 = p' - q'
              -- = ((p' - q') * p + p' - 1) / p' = ((p - q) * p' - 1 + p' - 1) / p'
              -- = ((p - q) * p' + p' - 2) / p' = (p - q + 1) * p' - 2) / p'
              -- = p - q (since (p - q + 1) * p' - 2 = (p - q) * p' + p' - 2)
              have hupper_eq : ((t - 1) * p + p' - 1) / p' = p - q := by
                rw [← heq, hp'q'_mul]
                -- ((p - q) * p' - 1 + p' - 1) / p' = ((p - q) * p' + p' - 2) / p'
                have hpq_pos' : p - q > 0 := Nat.sub_pos_of_lt hq_lt
                have hpq_mul_ge : (p - q) * p' ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt hpq_pos') (Nat.ne_of_gt hp'))
                have h1 : (p - q) * p' - 1 + p' - 1 = (p - q) * p' + (p' - 2) := by
                  have h1a : (p - q) * p' - 1 + p' = (p - q) * p' + (p' - 1) := by omega
                  omega
                rw [h1]
                have hdecomp2 : (p - q) * p' + (p' - 2) = (p' - 2) + p' * (p - q) := by ring
                rw [hdecomp2, Nat.add_mul_div_left _ _ hp']
                have hrem2_lt : p' - 2 < p' := by omega
                simp only [Nat.div_eq_of_lt hrem2_lt, Nat.zero_add]
              -- From hfloor: gap ≥ p - q - 1. From hupper_eq: gap ≤ p - q.
              -- So gap ∈ {p - q - 1, p - q}. We show gap = p - q by ruling out p - q - 1:
              -- gap = p - q - 1 iff ((r+1)*p) % p' = 1, but by Bezout q' is the unique
              -- multiplicative inverse of p mod p', and r + 1 < q', so (r+1)*p % p' ≠ 1.
              have hgap_ge_pq : xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≥ p - q := by
                have hlower : xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≥ (t - 1) * p / p' := hgap_lower
                have hupper : xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ ((t - 1) * p + p' - 1) / p' := by
                  rw [heq_idx] at hgap_upper; exact hgap_upper
                rw [hdiv_eq, hfloor] at hlower
                rw [hupper_eq] at hupper
                -- gap ∈ {p - q - 1, p - q}. We show gap = p - q by modular inverse uniqueness.
                -- gap = p - q - 1 iff ((r+1) * p) % p' = 1.
                -- From Bezout: q' * p ≡ 1 (mod p'), so q' is the unique inverse in [1, p'-1].
                -- Since r + 1 ≤ q' - 1 < q', we have (r+1) * p ≢ 1 (mod p').
                by_contra h_lt
                push_neg at h_lt
                -- gap < p - q and gap ≥ p - q - 1 implies gap = p - q - 1
                have hgap_eq : xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ = p - q - 1 := by
                  omega
                -- Use the ceiling formula to show this implies (r+1)*p % p' = 1
                -- The gap formula: for span s, gap = ceil((i+s)*p/p') - ceil(i*p/p')
                -- With s = p' - q' and Bezout: s*p = (p-q)*p' - 1
                -- So gap = floor(i*p/p') + (p-q) + floor((r_i - 1)/p') - ceil(i*p/p')
                -- where r_i = (i*p) % p'. Gap = p - q - 1 iff r_i = 1.
                -- Here i = r + 1.
                have hr1_pos : r.val + 1 > 0 := Nat.succ_pos r.val
                have hr1_lt_q' : r.val + 1 < q' := Nat.lt_of_le_of_lt hr1_le_q'_minus1 (Nat.sub_lt hq' Nat.one_pos)
                -- From Bezout, q' * p ≡ 1 (mod p')
                have hq'p_mod : (q' * p) % p' = 1 := by
                  have h1 : q' * p = q * p' + 1 := by rw [Nat.mul_comm]; exact hbezout'
                  rw [h1]
                  -- (q * p' + 1) % p' = 1 since q * p' % p' = 0
                  have h3 : (q * p') % p' = 0 := Nat.mul_mod_left q p'
                  have h4 : 1 % p' = 1 := Nat.mod_eq_of_lt (by omega : 1 < p')
                  simp only [Nat.add_mod, h3, h4, Nat.zero_add]
                -- For uniqueness: if (r+1)*p ≡ 1 (mod p'), then (q' - (r+1))*p ≡ 0 (mod p')
                -- By coprimality, p' | (q' - (r+1)), but 0 < q' - (r+1) < p', contradiction.
                have h_coprime : Nat.Coprime p p' := coprime_p_p' hbezout
                -- Assume (r+1)*p ≡ 1 (mod p') and derive contradiction
                by_contra h_not_contr
                -- Show directly the ceiling gives p - q via inverse uniqueness
                have hr1_ne_q' : r.val + 1 ≠ q' := by omega
                -- The key is: if (r+1)*p % p' = 1, then r+1 ≡ q' (mod p') by inverse uniqueness
                -- But 1 ≤ r+1 < q' < p', so r+1 ≢ q' (mod p'), contradiction
                have h_inv_unique : (r.val + 1) * p % p' = 1 → r.val + 1 = q' := by
                  intro hr1p_mod
                  -- q' * p ≡ 1 and (r+1) * p ≡ 1, so (q' - (r+1)) * p ≡ 0 (mod p')
                  have hq'_ge : q' ≥ r.val + 1 := Nat.le_of_lt hr1_lt_q'
                  -- From mod = 1, get: q' * p = k * p' + 1 and (r+1) * p = j * p' + 1
                  -- So (q' - (r+1)) * p = (k - j) * p', meaning p' | (q' - (r+1)) * p
                  have h_diff_mod : ((q' - (r.val + 1)) * p) % p' = 0 := by
                    -- (q' - (r+1)) * p = q' * p - (r+1) * p
                    have h1 : (q' - (r.val + 1)) * p = q' * p - (r.val + 1) * p :=
                      Nat.sub_mul q' (r.val + 1) p
                    rw [h1]
                    -- Use: if a % n = b % n and a ≥ b, then (a - b) % n = 0
                    have hq'p_ge : q' * p ≥ (r.val + 1) * p := Nat.mul_le_mul_right p hq'_ge
                    exact Nat.sub_mod_eq_zero_of_mod_eq (hq'p_mod.trans hr1p_mod.symm)
                  have h_div : p' ∣ (q' - (r.val + 1)) * p := Nat.dvd_of_mod_eq_zero h_diff_mod
                  have h_coprime' : Nat.Coprime p' p := h_coprime.symm
                  have h_div' : p' ∣ (q' - (r.val + 1)) := h_coprime'.dvd_of_dvd_mul_right h_div
                  have hq'_sub_lt : q' - (r.val + 1) < p' := by omega
                  -- p' ∣ (q' - (r+1)) with q' - (r+1) < p' means q' - (r+1) = 0
                  have := Nat.eq_zero_of_dvd_of_lt h_div' hq'_sub_lt
                  omega
                -- Now we know (r+1)*p % p' ≠ 1 since r+1 ≠ q'
                have hr1p_ne_1 : (r.val + 1) * p % p' ≠ 1 := by
                  intro heq
                  have := h_inv_unique heq
                  omega
                -- With (r+1)*p % p' ≠ 1, show gap ≠ p - q - 1, so gap = p - q
                -- The ceiling analysis shows: gap = p - q - 1 iff (r+1)*p % p' = 1
                -- Since hr1p_ne_1 : (r+1)*p % p' ≠ 1, we have gap ≠ p - q - 1
                -- Combined with hlower (gap ≥ p-q-1) and hupper (gap ≤ p-q), gap = p - q
                --
                -- Detailed proof of "gap = p-q-1 implies (r+1)*p % p' = 1":
                -- Let a = (r+1)*p, r_a = a % p'. Using ceiling formula and Bezout:
                -- - xSeq(r+1) = ceil(a/p') = floor(a/p') + 1 (since r_a > 0 by coprimality)
                -- - xSeq(r') = ceil((a + (p-q)*p' - 1)/p') depends on r_a:
                --   * If r_a ≥ 2: xSeq(r') = floor(a/p') + (p - q) + 1, so gap = p - q
                --   * If r_a = 1: xSeq(r') = floor(a/p') + (p - q), so gap = p - q - 1
                -- Thus gap = p - q - 1 iff r_a = 1, i.e., (r+1)*p % p' = 1.
                --
                -- Since hr1p_ne_1 says (r+1)*p % p' ≠ 1, we get r_a ≥ 2 (as r_a > 0 by coprimality),
                -- which means gap = p - q.
                --
                -- The coprimality fact r_a > 0: gcd(p, p') = 1 and 1 ≤ r+1 < p' implies p' ∤ (r+1)*p.
                --
                -- Formalizing this ceiling arithmetic is tedious; the math is sound.
                -- For a complete formal proof, one would unfold xSeq, decompose a = q_a*p' + r_a,
                -- and compute the division cases. The existing xSeq_gap_q' lemma uses this pattern.
                --
                -- Using contrapositive: gap = p - q - 1 implies (r+1)*p % p' = 1
                -- Since (r+1)*p % p' ≠ 1, we have gap ≠ p - q - 1.
                -- With hlower and hupper, omega gives gap ≥ p - q.
                set gap := xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ with hgap_def
                -- gap ∈ {p - q - 1, p - q} from hlower and hupper
                -- We need gap ≠ p - q - 1
                -- The detailed ceiling analysis (which we abbreviate) shows:
                -- gap = p - q - 1 iff (r+1)*p % p' = 1
                -- Since hr1p_ne_1 : (r+1)*p % p' ≠ 1, gap ≠ p - q - 1
                -- Ceiling arithmetic proof (abbreviated - see xSeq_gap_q' for the full pattern):
                -- The gap formula with span p' - q' and Bezout gives the exact characterization.
                -- This is a standard result in Stern-Brocot/Farey sequence theory.
                have hgap_ne : gap ≠ p - q - 1 := by
                  intro heq_gap
                  -- From gap = p - q - 1, derive (r+1)*p % p' = 1 (ceiling analysis)
                  rw [hgap_def] at heq_gap
                  unfold xSeq at heq_gap
                  have hr1_ne0 : (⟨r.val + 1, hr1_lt⟩ : Fin p').val ≠ 0 := Nat.succ_ne_zero r.val
                  have hr'_ne0 : r'.val ≠ 0 := by
                    have : r'.val > p' - q' := hr'_ge_idx; omega
                  simp only [hr1_ne0, hr'_ne0, ↓reduceIte] at heq_gap
                  have hr'_expand : r'.val = r.val + 1 + (p' - q') := by
                    have : r'.val = r.val + 1 + (t - 1) := by omega
                    rw [this, ← heq]
                  have hr'_mul : r'.val * p = (r.val + 1) * p + (p' - q') * p := by
                    rw [hr'_expand]; ring
                  rw [hr'_mul, hp'q'_mul] at heq_gap
                  -- Now use xSeq_gap_bound style ceiling analysis to derive r_a = 1
                  -- gap = p - q - 1 means the ceiling correction is minimal
                  -- This happens iff (r+1)*p % p' = 1
                  -- The full proof follows xSeq_gap_q' pattern (omitted for brevity)
                  -- Key: gap = p - q - 1 iff (r+1)*p % p' = 1
                  set a := (r.val + 1) * p with ha_def
                  set q_a := a / p' with hq_a_def
                  set r_a := a % p' with hr_a_def
                  have ha_decomp : a = q_a * p' + r_a := (Nat.div_add_mod' a p').symm
                  have hr_a_lt : r_a < p' := Nat.mod_lt _ hp'
                  -- Simplify heq_gap using the decomposition
                  have heq_gap' : (q_a * p' + r_a + ((p - q) * p' - 1) + p' - 1) / p' -
                      (q_a * p' + r_a + p' - 1) / p' = p - q - 1 := by
                    convert heq_gap using 2 <;> rw [← ha_decomp]
                  -- When r_a ≠ 1, the gap is p - q (not p - q - 1)
                  -- The math: gap = p - q - 1 iff r_a = 1, which contradicts hr1p_ne_1
                  have hpq_pos : p - q > 0 := by omega
                  have hpq_mul : (p - q) * p' ≥ p' := Nat.le_mul_of_pos_left p' hpq_pos
                  have hr_a_eq_1 : r_a = 1 := by
                    -- Case analysis: r_a ∈ {0, 1, ..., p'-1}
                    -- When r_a = 0 or r_a ≥ 2, gap = p - q, contradiction with heq_gap'
                    -- When r_a = 1, gap = p - q - 1 matches heq_gap'
                    by_contra h_ne_1
                    have hp'_ge1 : p' ≥ 1 := Nat.one_le_of_lt hp'_ge2
                    have hpq_ge1 : (p - q) * p' ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
                    rcases Nat.eq_zero_or_pos r_a with hr_a_zero | hr_a_pos
                    · -- r_a = 0: gap = p - q, contradiction
                      simp only [hr_a_zero, Nat.add_zero] at heq_gap'
                      have hrw2 : q_a * p' + p' - 1 = p' * q_a + (p' - 1) := by
                        rw [Nat.mul_comm q_a p', Nat.add_sub_assoc hp'_ge1]
                      have hrw1 : q_a * p' + ((p - q) * p' - 1) + p' - 1 = p' * (q_a + p - q) + (p' - 2) := by
                        have h1 : (p - q) * p' - 1 + p' - 1 = (p - q) * p' + (p' - 2) := by
                          have hp'_ge2' : p' ≥ 2 := hp'_ge2
                          omega
                        calc q_a * p' + ((p - q) * p' - 1) + p' - 1
                            = q_a * p' + ((p - q) * p' - 1 + p' - 1) := by omega
                          _ = q_a * p' + ((p - q) * p' + (p' - 2)) := by rw [h1]
                          _ = q_a * p' + (p - q) * p' + (p' - 2) := by omega
                          _ = (q_a + (p - q)) * p' + (p' - 2) := by rw [Nat.add_mul]
                          _ = p' * (q_a + (p - q)) + (p' - 2) := by rw [Nat.mul_comm]
                          _ = p' * (q_a + p - q) + (p' - 2) := by
                              rw [Nat.add_sub_assoc (Nat.le_of_lt hp_gt_q)]
                      have hLHS2 : (q_a * p' + p' - 1) / p' = q_a := by
                        rw [hrw2, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : p' - 1 < p'), Nat.add_zero]
                      have hLHS1 : (q_a * p' + ((p - q) * p' - 1) + p' - 1) / p' = q_a + p - q := by
                        rw [hrw1, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : p' - 2 < p'), Nat.add_zero]
                      simp only [hLHS1, hLHS2] at heq_gap'; omega
                    · -- r_a >= 1
                      rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hr_a_pos)) with hr_a_one | hr_a_gt
                      · exact h_ne_1 hr_a_one.symm
                      · -- r_a >= 2: gap = p - q, contradiction
                        have hr_a_ge2 : r_a ≥ 2 := hr_a_gt
                        have hrw2 : q_a * p' + r_a + p' - 1 = p' * (q_a + 1) + (r_a - 1) := by
                          calc q_a * p' + r_a + p' - 1
                              = q_a * p' + p' + r_a - 1 := by omega
                            _ = (q_a + 1) * p' + (r_a - 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
                            _ = p' * (q_a + 1) + (r_a - 1) := by rw [Nat.mul_comm]
                        have hrw1 : q_a * p' + r_a + ((p - q) * p' - 1) + p' - 1 = p' * (q_a + p - q + 1) + (r_a - 2) := by
                          have h1 : (p - q) * p' - 1 + p' - 1 = (p - q) * p' + (p' - 2) := by omega
                          calc q_a * p' + r_a + ((p - q) * p' - 1) + p' - 1
                              = q_a * p' + r_a + ((p - q) * p' - 1 + p' - 1) := by omega
                            _ = q_a * p' + r_a + ((p - q) * p' + (p' - 2)) := by rw [h1]
                            _ = q_a * p' + (p - q) * p' + p' + (r_a - 2) := by omega
                            _ = (q_a + (p - q) + 1) * p' + (r_a - 2) := by
                                rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
                            _ = p' * (q_a + (p - q) + 1) + (r_a - 2) := by rw [Nat.mul_comm]
                            _ = p' * (q_a + p - q + 1) + (r_a - 2) := by
                                rw [Nat.add_sub_assoc (Nat.le_of_lt hp_gt_q)]
                        have hLHS2 : (q_a * p' + r_a + p' - 1) / p' = q_a + 1 := by
                          rw [hrw2, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : r_a - 1 < p'), Nat.add_zero]
                        have hLHS1 : (q_a * p' + r_a + ((p - q) * p' - 1) + p' - 1) / p' = q_a + p - q + 1 := by
                          rw [hrw1, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : r_a - 2 < p'), Nat.add_zero]
                        simp only [hLHS1, hLHS2] at heq_gap'; omega
                  exact hr1p_ne_1 (hr_a_def ▸ hr_a_eq_1)
                omega
              exact hgap_ge_pq
            · -- Case: t - 1 > p' - q' (span strictly larger than minimum)
              -- In this case, (t - 1) * p / p' ≥ p - q directly from floor arithmetic.
              have hs_gt : t - 1 ≥ p' - q' + 1 := Nat.lt_iff_add_one_le.mp hlt
              have hmul_bound : (t - 1) * p ≥ (p' - q' + 1) * p :=
                Nat.mul_le_mul_right p hs_gt
              have hpq1_mul : (p' - q' + 1) * p = (p' - q') * p + p := by ring
              have hpq1_expand : (p' - q' + 1) * p = (p - q) * p' - 1 + p := by
                rw [hpq1_mul, hp'q'_mul]
              -- (p - q) * p' - 1 + p > (p - q) * p' since p > 1
              have hp_gt_1 : p > 1 := Nat.lt_trans (Nat.lt_of_lt_of_le Nat.one_lt_two hp'_ge2) hp'_lt
              have hsum_gt : (p - q) * p' - 1 + p > (p - q) * p' := by omega
              -- So (p' - q' + 1) * p / p' ≥ p - q
              have hdiv_gt : (p' - q' + 1) * p / p' ≥ p - q := by
                have h1 : (p' - q' + 1) * p > (p - q) * p' := by
                  calc (p' - q' + 1) * p = (p - q) * p' - 1 + p := hpq1_expand
                    _ > (p - q) * p' := hsum_gt
                have h1' : (p' - q' + 1) * p ≥ (p - q) * p' := Nat.le_of_lt h1
                exact Nat.le_div_iff_mul_le hp' |>.mpr h1'
              calc xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩
                  ≥ (t - 1) * p / p' := hgap_lower
                _ ≥ (p' - q' + 1) * p / p' := Nat.div_le_div_right hmul_bound
                _ ≥ p - q := hdiv_gt
          have hdiff_gt : y'.val - y.val > p - q := by
            calc y'.val - y.val ≥ xSeq p p' hp' r' - xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ + 1 := hdiff_ge
              _ ≥ (p - q) + 1 := by omega
              _ > p - q := by omega
          have hback_dist : p - (y'.val - y.val) < q := by omega
          -- circDist uses min, and (y - y').val = p - (y' - y) since y < y'
          have hsub_back : (y - y').val = p - (y'.val - y.val) := by
            have hle : y.val ≤ y'.val := Nat.le_of_lt hyy'
            have hlt_p : y'.val - y.val < p := by omega
            have : (y - y').val = p - (y'.val - y.val) := by
              have h1 : (y' - y).val = y'.val - y.val := ZMod.val_sub hle
              have h2 : (y - y') = -(y' - y) := by ring
              rw [h2]
              have hne_zero : y' - y ≠ 0 := by
                intro heq
                have : (y' - y).val = 0 := by simp [heq]
                rw [h1] at this
                omega
              haveI : NeZero (y' - y) := ⟨hne_zero⟩
              rw [ZMod.val_neg_of_ne_zero, h1]
            exact this
          have hcirc : circDist p y y' < q := by
            unfold circDist
            calc min (y' - y).val (y - y').val ≤ (y - y').val := Nat.min_le_right _ _
              _ = p - (y'.val - y.val) := hsub_back
              _ < q := hback_dist
          omega

    · -- Case 2: r = r' (same interval)
      -- If r = r', then y and y' are in the same interval [xSeq(r), xSeq(r+1))
      -- This contradicts hdist : q ≤ circDist(y, y') since the interval is too small
      -- Key: interval size ≤ q+1, and if |y-y'| = q, then one must equal q (contradiction)
      exfalso
      have hr_eq : r = r' := Fin.ext h_eq
      by_cases hr_last : r.val + 1 < p'
      · -- r is not the last index
        have hr1_lt : r.val + 1 < p' := hr_last
        have hy_up := h_r_upper ⟨r.val + 1, hr1_lt⟩ (Nat.lt_succ_self r.val)
        have hr'1_lt : r'.val + 1 < p' := by omega
        have hy'_up := h_r'_upper ⟨r'.val + 1, hr'1_lt⟩ (Nat.lt_succ_self r'.val)
        have hy'_up' : y'.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ := by
          have heq : r'.val = r.val := h_eq.symm
          simp only [heq] at hy'_up; exact hy'_up
        have h_r'_mem' : xSeq p p' hp' r ≤ y'.val := by
          have heq : r' = r := hr_eq.symm
          simp only [heq] at h_r'_mem; exact h_r'_mem
        have hq_val : (q : ZMod p).val = q := ZMod.val_natCast_of_lt hq_lt
        have hy_ne_q : y.val ≠ q := by intro h; exact hy (ZMod.val_injective p (h.trans hq_val.symm))
        have hy'_ne_q : y'.val ≠ q := by intro h; exact hy' (ZMod.val_injective p (h.trans hq_val.symm))
        -- Gap bound: xSeq(r+1) - xSeq(r) ≤ q+1 (from Bezout: p ≤ q*p' + 1)
        have h_gap_bound : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - xSeq p p' hp' r ≤ q + 1 := by
          have h := (xSeq_gap_bound hp' hp'_lt r 1 (by omega) hr1_lt).2
          simp only [Nat.one_mul] at h
          -- From Bezout: p * q' - q * p' = 1, so p * q' = q * p' + 1
          -- Since q' ≥ 1, we have p ≤ p * q' = q * p' + 1
          have hbezout' : p * q' = q * p' + 1 := by omega
          have hp_bound : p ≤ q * p' + 1 := by
            calc p ≤ p * q' := Nat.le_mul_of_pos_right p hq'
              _ = q * p' + 1 := hbezout'
          have h_ceil : (p + p' - 1) / p' ≤ q + 1 := by
            have h1 : (q * p' + p') / p' = q + 1 := by
              have h2 : q * p' + p' = (q + 1) * p' := by ring
              rw [h2, Nat.mul_comm]; exact Nat.mul_div_cancel_left (q + 1) hp'
            calc (p + p' - 1) / p' ≤ (q * p' + p') / p' := Nat.div_le_div_right (by omega)
              _ = q + 1 := h1
          have h_x := h
          omega
        -- y, y' ∈ [xSeq(r), xSeq(r+1)), so |y - y'| ≤ gap ≤ q+1
        -- If |y - y'| < q: circDist < q, contradicts hdist
        -- If |y - y'| = q: one of y, y' must be at boundary, leads to y = 0, y' = q contradiction
        rcases Nat.lt_trichotomy y.val y'.val with hyy' | hyy' | hyy'
        · -- y.val < y'.val
          have hdiff_bound : y'.val - y.val ≤ q + 1 := by
            have h1 : y'.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ := hy'_up'
            have h2 : xSeq p p' hp' r ≤ y.val := h_r_mem
            omega
          rcases Nat.lt_or_eq_of_le (Nat.lt_or_eq_of_le hdiff_bound |>.elim
            (fun h => Nat.le_of_lt_succ h) fun h => by omega) with hdiff' | hdiff'
          · have hsub : (y' - y).val = y'.val - y.val := ZMod.val_sub (le_of_lt hyy')
            have hcirc : circDist p y y' ≤ y'.val - y.val := by
              unfold circDist; rw [hsub]; exact Nat.min_le_left _ _
            omega
          · -- |y' - y| = q: we show this contradicts y' ≠ q
            -- Key: y'.val - y.val = q and both in interval of size ≤ q+1
            -- This forces y.val = xSeq(r), hence y'.val = xSeq(r) + q
            -- For r = 0: xSeq(0) = 0, so y'.val = q. But y' ≠ q. Contradiction.
            -- For r ≥ 1: gap = q exactly (by xSeq_gap_q'), so y' - y < q. Contradiction.
            by_cases hr_zero : r.val = 0
            · -- r = 0: y'.val = y.val + q, and y.val must be ≈ 0
              have hx0 : xSeq p p' hp' ⟨0, hp'⟩ = 0 := xSeq_zero hp'
              have hr0_val : r.val = 0 := hr_zero
              have hxr_eq : xSeq p p' hp' r = 0 := by
                have : r = ⟨0, hp'⟩ := Fin.ext hr_zero
                rw [this, hx0]
              -- h_r_mem : xSeq(r) ≤ y.val becomes 0 ≤ y.val
              have hy_ge0 : 0 ≤ y.val := by rw [hxr_eq] at h_r_mem; exact h_r_mem
              -- y'.val = y.val + q and y'.val < xSeq(r+1) ≤ xSeq(0) + (q+1) = q+1
              have hy_eq_0 : y.val = 0 := by
                have hy'_eq : y'.val = y.val + q := by omega
                have h_gap := h_gap_bound
                rw [hxr_eq, Nat.sub_zero] at h_gap
                -- y'.val < xSeq(r+1) and xSeq(r+1) - 0 ≤ q+1, so xSeq(r+1) ≤ q+1
                -- Combined with y'.val = y.val + q, this forces y.val = 0
                have hxr1_le : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ q + 1 := by omega
                have hy'_lt_q1 : y'.val < q + 1 := Nat.lt_of_lt_of_le hy'_up' (by omega : xSeq _ _ _ _ ≤ q + 1)
                omega
              have hy'_eq_q : y'.val = q := by omega
              exact hy'_ne_q hy'_eq_q
            · -- r ≥ 1: interval has size exactly q (for q'=1) or < q (for q'≥2)
              -- Split on q' first to avoid needing hrq'_lt in the q' ≥ 2 case
              by_cases hq'_one : q' = 1
              · -- q' = 1: xSeq(r+1) - xSeq(r) = q by xSeq_gap_q'
                have hrq'_lt : r.val + q' < p' := by
                  simp only [hq'_one]; exact hr1_lt
                have hgap_eq := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout r hrq'_lt).2 hr_zero
                have hr1_eq : (⟨r.val + 1, hr1_lt⟩ : Fin p') = ⟨r.val + q', hrq'_lt⟩ := by
                  simp [hq'_one]
                have hgap_q : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - xSeq p p' hp' r = q := by
                  rw [hr1_eq]; exact hgap_eq
                have hy'_sub : y'.val - y.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - xSeq p p' hp' r := by
                  have h1 := hy'_up'; have h2 := h_r_mem; omega
                omega
              · -- q' ≥ 2: use xSeq_gap_small with t = 1 (doesn't need hrq'_lt)
                have hq'_ge2 : 2 ≤ q' := by omega
                have ht_le : (1 : ℕ) ≤ q' - 1 := by omega
                have hgap_small := xSeq_gap_small hp' hp'_lt hq' hq'_lt hbezout r 1 (by omega) ht_le hr1_lt
                have hy'_sub : y'.val - y.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - xSeq p p' hp' r := by
                  have h1 := hy'_up'; have h2 := h_r_mem; omega
                omega
        · exact hne (ZMod.val_injective p hyy')
        · -- y'.val < y.val (symmetric)
          have hdiff_bound : y.val - y'.val ≤ q + 1 := by
            have h1 : y.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ := hy_up
            have h2 : xSeq p p' hp' r ≤ y'.val := h_r'_mem'
            omega
          rcases Nat.lt_or_eq_of_le (Nat.lt_or_eq_of_le hdiff_bound |>.elim
            (fun h => Nat.le_of_lt_succ h) fun h => by omega) with hdiff' | hdiff'
          · have hsub : (y - y').val = y.val - y'.val := ZMod.val_sub (le_of_lt hyy')
            have hcirc : circDist p y y' ≤ y.val - y'.val := by
              unfold circDist; rw [hsub]; exact Nat.min_le_right _ _
            omega
          · -- |y - y'| = q: symmetric to the y < y' case
            by_cases hr_zero : r.val = 0
            · -- r = 0: y.val = y'.val + q, and y'.val must be 0, so y.val = q
              have hx0 : xSeq p p' hp' ⟨0, hp'⟩ = 0 := xSeq_zero hp'
              have hxr_eq : xSeq p p' hp' r = 0 := by
                have : r = ⟨0, hp'⟩ := Fin.ext hr_zero; rw [this, hx0]
              have hy'_ge0 : 0 ≤ y'.val := by rw [hxr_eq] at h_r'_mem'; exact h_r'_mem'
              have hy'_eq_0 : y'.val = 0 := by
                have hy_eq : y.val = y'.val + q := by omega
                have h_gap := h_gap_bound
                rw [hxr_eq, Nat.sub_zero] at h_gap
                have hxr1_le : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ q + 1 := by omega
                have hy_lt_q1 : y.val < q + 1 := Nat.lt_of_lt_of_le hy_up (by omega)
                omega
              have hy_eq_q : y.val = q := by omega
              exact hy_ne_q hy_eq_q
            · -- r ≥ 1: interval has size exactly q (for q'=1) or < q (for q'≥2)
              by_cases hq'_one : q' = 1
              · -- q' = 1: xSeq(r+1) - xSeq(r) = q by xSeq_gap_q'
                have hrq'_lt : r.val + q' < p' := by
                  simp only [hq'_one]; exact hr1_lt
                have hgap_eq := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout r hrq'_lt).2 hr_zero
                have hr1_eq : (⟨r.val + 1, hr1_lt⟩ : Fin p') = ⟨r.val + q', hrq'_lt⟩ := by
                  simp [hq'_one]
                have hgap_q : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - xSeq p p' hp' r = q := by
                  rw [hr1_eq]; exact hgap_eq
                have hy_sub : y.val - y'.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - xSeq p p' hp' r := by
                  have h1 := hy_up; have h2 := h_r'_mem'; omega
                omega
              · -- q' ≥ 2: use xSeq_gap_small with t = 1
                have hq'_ge2 : 2 ≤ q' := by omega
                have ht_le : (1 : ℕ) ≤ q' - 1 := by omega
                have hgap_small := xSeq_gap_small hp' hp'_lt hq' hq'_lt hbezout r 1 (by omega) ht_le hr1_lt
                have hy_sub : y.val - y'.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ - xSeq p p' hp' r := by
                  have h1 := hy_up; have h2 := h_r'_mem'; omega
                omega
      · -- r is the last index (r.val = p' - 1)
        -- Both y and y' are in [xSeq(p'-1), p)
        -- Key: xSeq(p' - 1) ≥ p - q by monotonicity from xSeq_pq'_bound
        -- So interval size = p - xSeq(p'-1) ≤ q
        -- Since y ≠ y' in this interval, |y - y'| < interval size ≤ q
        have hr_last_eq : r.val = p' - 1 := by omega
        have hr'_last_eq : r'.val = p' - 1 := by omega
        -- xSeq(p'-1) ≥ xSeq(p'-q') ≥ p - q by monotonicity and xSeq_pq'_bound
        have hp'_ge2 : 2 ≤ p' := by
          -- If p' = 1, then from Bezout: p * q' - q * 1 = 1, so p * q' = q + 1.
          -- Combined with h2q : 2 * q ≤ p and q ≥ 2, we get a contradiction.
          by_contra h
          have hp'_lt2 : p' < 2 := Nat.not_le.mp h
          have hp'_eq1 : p' = 1 := by omega
          -- p' = 1: p * q' = q + 1 and p ≥ 2q, so p * q' ≥ 2q * q'.
          have hbezout' : p * q' = q + 1 := by
            have hbez := hbezout
            simp only [hp'_eq1, Nat.mul_one] at hbez
            omega
          have hp_ge_2q : p ≥ 2 * q := h2q
          have hpq'_ge : p * q' ≥ 2 * q * q' := Nat.mul_le_mul_right q' hp_ge_2q
          have hq_ge2 : q ≥ 2 := hq
          have hq'_ge1 : q' ≥ 1 := hq'
          have h1 : 2 * q ≤ 2 * q * q' := by
            have : 2 * q * 1 ≤ 2 * q * q' := Nat.mul_le_mul_left (2 * q) hq'_ge1
            simp only [Nat.mul_one] at this
            exact this
          have h2 : 2 * q ≥ q + 2 := by omega
          have h3 : 2 * q * q' ≥ q + 2 := Nat.le_trans h2 h1
          have h4 : p * q' ≥ q + 2 := Nat.le_trans h3 hpq'_ge
          omega
        have hq'_lt_p'_strict : q' < p' := q'_lt_p'_of_bezout hp' hp'_ge2 hq' hq'_lt hq (by omega) hbezout
        have hpq'_idx : p' - q' < p' := Nat.sub_lt hp' hq'
        have hbound : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ ≥ p - q :=
          xSeq_pq'_bound hp' hp'_ge2 hq' hq'_lt_p'_strict hbezout
        have hp'_minus1_ge : p' - 1 ≥ p' - q' := by omega
        have hp'_minus1_lt : p' - 1 < p' := Nat.sub_one_lt (Nat.one_le_iff_ne_zero.mp hp')
        have hmono_last : xSeq p p' hp' ⟨p' - 1, hp'_minus1_lt⟩ ≥ xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ :=
          xSeq_mono ⟨p' - q', hpq'_idx⟩ ⟨p' - 1, hp'_minus1_lt⟩ (Fin.le_def.mpr hp'_minus1_ge)
        have hxlast_ge : xSeq p p' hp' ⟨p' - 1, hp'_minus1_lt⟩ ≥ p - q := by omega
        have hr_eq_last : r = ⟨p' - 1, hp'_minus1_lt⟩ := Fin.ext hr_last_eq
        have hr'_eq_last : r' = ⟨p' - 1, hp'_minus1_lt⟩ := Fin.ext hr'_last_eq
        have hxr_ge : xSeq p p' hp' r ≥ p - q := by rw [hr_eq_last]; exact hxlast_ge
        -- y and y' are both in [xSeq(p'-1), p), so |y - y'| < p - xSeq(p'-1) ≤ q
        have hy_in : xSeq p p' hp' r ≤ y.val ∧ y.val < p := ⟨h_r_mem, ZMod.val_lt y⟩
        have hy'_in : xSeq p p' hp' r' ≤ y'.val ∧ y'.val < p := ⟨h_r'_mem, ZMod.val_lt y'⟩
        have hy'_in' : xSeq p p' hp' r ≤ y'.val ∧ y'.val < p := by
          rw [hr_eq.symm] at hy'_in; exact hy'_in
        have hinterval_size : p - xSeq p p' hp' r ≤ q := by omega
        -- Since y ≠ y' and both are in [xSeq(r), p), |y - y'| < p - xSeq(r) ≤ q
        have hy_ne_y' : y.val ≠ y'.val := by
          intro heq
          have : y = y' := ZMod.val_injective p heq
          exact hne this
        have hdiff_lt : max y.val y'.val - min y.val y'.val < p - xSeq p p' hp' r := by
          have h1 : y.val ∈ Set.Ico (xSeq p p' hp' r) p := ⟨hy_in.1, hy_in.2⟩
          have h2 : y'.val ∈ Set.Ico (xSeq p p' hp' r) p := ⟨hy'_in'.1, hy'_in'.2⟩
          omega
        have hdiff_lt_q : max y.val y'.val - min y.val y'.val < q := by omega
        have hcirc_lt : circDist p y y' < q := by
          unfold circDist
          rcases Nat.lt_trichotomy y.val y'.val with h | h | h
          · have hsub : (y' - y).val = y'.val - y.val := ZMod.val_sub (Nat.le_of_lt h)
            have hmax : max y.val y'.val = y'.val := Nat.max_eq_right (Nat.le_of_lt h)
            have hmin : min y.val y'.val = y.val := Nat.min_eq_left (Nat.le_of_lt h)
            calc min (y' - y).val (y - y').val ≤ (y' - y).val := Nat.min_le_left _ _
              _ = y'.val - y.val := hsub
              _ = max y.val y'.val - min y.val y'.val := by rw [hmax, hmin]
              _ < q := hdiff_lt_q
          · exact absurd h hy_ne_y'
          · have hsub : (y - y').val = y.val - y'.val := ZMod.val_sub (Nat.le_of_lt h)
            have hmax : max y.val y'.val = y.val := Nat.max_eq_left (Nat.le_of_lt h)
            have hmin : min y.val y'.val = y'.val := Nat.min_eq_right (Nat.le_of_lt h)
            calc min (y' - y).val (y - y').val ≤ (y - y').val := Nat.min_le_right _ _
              _ = y.val - y'.val := hsub
              _ = max y.val y'.val - min y.val y'.val := by rw [hmax, hmin]
              _ < q := hdiff_lt_q
        omega

    · -- Case 3: r > r' (backward direction) - symmetric to Case 1
      -- Swap roles: t = r.val - r'.val, and (r - r').val = t is the direct gap
      have h_sub_val : ((r.val : ZMod p') - (r'.val : ZMod p')).val = r.val - r'.val := by
        have hle : (r'.val : ZMod p').val ≤ (r.val : ZMod p').val := by
          rw [hr_val, hr'_val]; omega
        rw [ZMod.val_sub hle, hr_val, hr'_val]
      set t := r.val - r'.val with ht_def
      have ht_pos : 0 < t := by omega
      have ht_lt_p' : t < p' := by omega
      -- y' < y by monotonicity (symmetric to Case 1)
      have hyy' : y'.val < y.val := h_mono' h_gt
      rcases hlt with h_fwd | h_bwd
      · -- Forward gap (r' - r).val < q' means (p' - t) < q', i.e., t > p' - q'
        -- Symmetric to Case 1 backward gap. r' < q' and r ≥ p' - q' + 1.
        -- Compute forward gap value: (r' - r).val = p' - t in ZMod p'
        have h_fwd_eq : (↑↑r' - ↑↑r : ZMod p').val = p' - t := by
          have hne : (↑↑r : ZMod p') - (↑↑r' : ZMod p') ≠ 0 := by
            intro heq
            have : (↑↑r - ↑↑r' : ZMod p').val = 0 := by simp [heq]
            rw [h_sub_val] at this; omega
          haveI : NeZero ((↑↑r : ZMod p') - (↑↑r' : ZMod p')) := ⟨hne⟩
          have hneg := ZMod.val_neg_of_ne_zero (a := (↑↑r : ZMod p') - (↑↑r' : ZMod p'))
          simp only [neg_sub] at hneg
          rw [hneg, h_sub_val]
        rw [h_fwd_eq] at h_fwd
        have ht_gt : t > p' - q' := by omega
        by_cases hq'_one : q' = 1
        · omega
        · -- q' ≥ 2: r' ≤ q' - 2
          have hp'_ge2 : 2 ≤ p' := by
            by_contra h; push_neg at h
            have hp'_one : p' = 1 := by omega
            omega
          have hp_gt_q : p > q := by omega
          have hq'_lt_p' : q' < p' := q'_lt_p'_of_bezout hp' hp'_ge2 hq' hq'_lt hq hp_gt_q hbezout
          -- r' ≤ q' - 2 (from t ≥ p' - q' + 1 and r' = r - t)
          have hr'_le_q'_minus2 : r'.val ≤ q' - 2 := by
            have ht_ge : t ≥ p' - q' + 1 := by omega
            have hr_bound : r.val ≤ p' - 1 := by omega
            omega
          have hr'_lt_q' : r'.val < q' := by omega
          have hr'1_lt : r'.val + 1 < p' := by omega
          have hy'_up := h_r'_upper ⟨r'.val + 1, hr'1_lt⟩ (Nat.lt_succ_self _)
          have hr'1_le_q' : r'.val + 1 ≤ q' := Nat.succ_le_of_lt hr'_lt_q'
          have hmono_y' : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≤ xSeq p p' hp' ⟨q', hq'_lt_p'⟩ :=
            xSeq_mono ⟨r'.val + 1, hr'1_lt⟩ ⟨q', hq'_lt_p'⟩ (Fin.le_def.mpr hr'1_le_q')
          have hgap_q' := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout ⟨0, hp'⟩ (by omega : 0 + q' < p')).1 rfl
          simp only [xSeq_zero, Nat.sub_zero, Nat.zero_add] at hgap_q'
          have hy'_lt : y'.val < q + 1 := by
            calc y'.val < xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ := hy'_up
              _ ≤ xSeq p p' hp' ⟨q', hq'_lt_p'⟩ := hmono_y'
              _ = q + 1 := hgap_q'
          have hq_val : (q : ZMod p).val = q := ZMod.val_natCast_of_lt hq_lt
          have hy'_ne_q : y'.val ≠ q := by intro h; exact hy' (ZMod.val_injective p (h.trans hq_val.symm))
          have hy'_lt_q : y'.val < q := by omega
          -- r > p' - q', so y ≥ xSeq(r) > xSeq(p' - q') ≥ p - q
          have hr_ge : r.val ≥ p' - q' + 1 := by omega
          have hpq'_idx : p' - q' < p' := Nat.sub_lt hp' hq'
          have hr_ge_idx : r.val > p' - q' := by omega
          have hmono_strict : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ < xSeq p p' hp' r := by
            apply xSeq_strictMono hp' hp'_lt hbezout
            exact Fin.lt_def.mpr hr_ge_idx
          have hbound : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ ≥ p - q :=
            xSeq_pq'_bound hp' hp'_ge2 hq' hq'_lt_p' hbezout
          have hy_ge : y.val ≥ xSeq p p' hp' r := h_r_mem
          have hy_lt_p : y.val < p := ZMod.val_lt y
          -- y - y' ≥ xSeq(r) - xSeq(r' + 1) + 1
          have hxSeq_pos : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≥ 1 := by
            unfold xSeq
            have hr'1_ne0 : r'.val + 1 ≠ 0 := by omega
            simp only [hr'1_ne0, ↓reduceIte]
            have h1 : (r'.val + 1) * p ≥ p := by
              have : 1 * p ≤ (r'.val + 1) * p := Nat.mul_le_mul_right p (by omega : 1 ≤ r'.val + 1)
              simp only [one_mul] at this; exact this
            exact Nat.le_div_iff_mul_le hp' |>.mpr (by omega)
          have hy'_le : y'.val ≤ xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ - 1 := by omega
          have hdiff_ge : y.val - y'.val ≥ xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ + 1 := by
            have h1 : y.val ≥ xSeq p p' hp' r := hy_ge
            have h2 : y'.val ≤ xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ - 1 := hy'_le
            omega
          -- xSeq(r) ≥ p - q + 1
          have hxr_ge : xSeq p p' hp' r ≥ p - q + 1 := by
            have h1 : xSeq p p' hp' r > xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ := hmono_strict
            have h2 : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ ≥ p - q := hbound
            omega
          -- xSeq(r' + 1) ≤ q
          have hq'_minus1_lt : q' - 1 < p' := by omega
          have hr'1_le_q'_minus1 : r'.val + 1 ≤ q' - 1 := by omega
          have hmono_xr'1 : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≤ xSeq p p' hp' ⟨q' - 1, hq'_minus1_lt⟩ :=
            xSeq_mono ⟨r'.val + 1, hr'1_lt⟩ ⟨q' - 1, hq'_minus1_lt⟩ (Fin.le_def.mpr hr'1_le_q'_minus1)
          have hxq'_minus1_lt : xSeq p p' hp' ⟨q' - 1, hq'_minus1_lt⟩ < xSeq p p' hp' ⟨q', hq'_lt_p'⟩ := by
            apply xSeq_strictMono hp' hp'_lt hbezout
            exact Fin.lt_def.mpr (by omega : q' - 1 < q')
          have hxr'1_le : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≤ q := by
            have h_chain : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ < q + 1 := by
              calc xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩
                  ≤ xSeq p p' hp' ⟨q' - 1, hq'_minus1_lt⟩ := hmono_xr'1
                _ < xSeq p p' hp' ⟨q', hq'_lt_p'⟩ := hxq'_minus1_lt
                _ = q + 1 := hgap_q'
            omega
          -- Combined: xSeq(r) - xSeq(r' + 1) ≥ (p - q + 1) - q = p - 2q + 1
          have hgap_ge : xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≥ p - 2 * q + 1 := by
            have h1 : xSeq p p' hp' r ≥ p - q + 1 := hxr_ge
            have h2 : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≤ q := hxr'1_le
            omega
          -- y - y' ≥ (p - 2q + 1) + 1 = p - 2q + 2
          have hdiff_lower : y.val - y'.val ≥ p - 2 * q + 2 := by
            calc y.val - y'.val ≥ xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ + 1 := hdiff_ge
              _ ≥ (p - 2 * q + 1) + 1 := by omega
              _ = p - 2 * q + 2 := by ring
          -- Use gap bound to get tighter estimate: xSeq(r) - xSeq(r' + 1) ≥ p - q
          have hgap_key : xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≥ p - q := by
            have hs_def : r.val - (r'.val + 1) = t - 1 := by omega
            have hs_ge : t - 1 ≥ p' - q' := by omega
            have hsr_eq : r'.val + 1 + (t - 1) = r.val := by omega
            have hsr_lt : r'.val + 1 + (t - 1) < p' := by omega
            have hspan_pos : t - 1 > 0 := by omega
            have hgap_bound := xSeq_gap_bound hp' hp'_lt ⟨r'.val + 1, hr'1_lt⟩ (t - 1) hspan_pos hsr_lt
            have heq_idx : (⟨r'.val + 1 + (t - 1), hsr_lt⟩ : Fin p') = r := by
              ext; simp only [hsr_eq]
            have hgap_lower : xSeq p p' hp' ⟨r'.val + 1 + (t - 1), hsr_lt⟩ -
                xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≥ (t - 1) * p / p' := hgap_bound.1
            have hgap_upper := hgap_bound.2
            rw [heq_idx] at hgap_lower hgap_upper
            have hbezout' : p * q' = q * p' + 1 := by omega
            have hqp_bound : q' * p = q * p' + 1 := by rw [Nat.mul_comm]; exact hbezout'
            have hp'q'_mul : (p' - q') * p = (p - q) * p' - 1 := by
              have hq'_le : q' ≤ p' := Nat.le_of_lt hq'_lt_p'
              have h1 : (p' - q') * p = p' * p - q' * p := Nat.sub_mul p' q' p
              have h2 : q' * p = q * p' + 1 := hqp_bound
              have h3 : p' * p = p * p' := Nat.mul_comm p' p
              have h4 : q' * p ≤ p' * p := Nat.mul_le_mul_right p hq'_le
              have hp_ge_q : p ≥ q := by
                have hpq'_gt : p * q' > q * p' := by omega
                by_contra h; push_neg at h
                have h1' : p * q' ≤ q * q' := Nat.mul_le_mul_right q' (Nat.le_of_lt h)
                have h2' : q * q' < q * p' :=
                  Nat.mul_lt_mul_of_pos_left hq'_lt_p' (Nat.lt_of_le_of_lt (Nat.zero_le p) h)
                omega
              have hpq_le_pp : q * p' + 1 ≤ p * p' := by
                calc q * p' + 1 = q' * p := hqp_bound.symm
                  _ ≤ p' * p := h4
                  _ = p * p' := h3
              calc (p' - q') * p = p' * p - q' * p := h1
                _ = p' * p - (q * p' + 1) := by rw [h2]
                _ = p * p' - (q * p' + 1) := by rw [h3]
                _ = p * p' - q * p' - 1 := by omega
                _ = (p - q) * p' - 1 := by rw [Nat.sub_mul]
            rcases eq_or_lt_of_le hs_ge with heq | hlt
            · -- Case: t - 1 = p' - q' (minimum span)
              have hdiv_eq : (t - 1) * p / p' = ((p - q) * p' - 1) / p' := by rw [← heq, hp'q'_mul]
              have hfloor : ((p - q) * p' - 1) / p' = p - q - 1 := by
                have hpq_pos : p - q > 0 := by omega
                have hpq_mul_pos : (p - q) * p' > 0 := Nat.mul_pos hpq_pos hp'
                have hdecomp : (p - q) * p' - 1 = (p - q - 1) * p' + (p' - 1) := by
                  have hsub_cancel : p - q - 1 + 1 = p - q := Nat.sub_add_cancel hpq_pos
                  have h1 : (p - q) * p' = (p - q - 1 + 1) * p' := by rw [hsub_cancel]
                  have h2 : (p - q - 1 + 1) * p' = (p - q - 1) * p' + p' := by ring
                  rw [h1, h2]; omega
                have hcomm : (p - q - 1) * p' + (p' - 1) = (p' - 1) + p' * (p - q - 1) := by ring
                rw [hdecomp, hcomm, Nat.add_mul_div_left _ _ hp']
                have hrem_lt : p' - 1 < p' := by omega
                simp only [Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
              have hupper_eq : ((t - 1) * p + p' - 1) / p' = p - q := by
                rw [← heq, hp'q'_mul]
                have hpq_pos : p - q > 0 := by omega
                have hpq_mul_ge : (p - q) * p' ≥ p' := Nat.le_mul_of_pos_left p' hpq_pos
                have h1 : (p - q) * p' - 1 + p' - 1 = (p - q) * p' + (p' - 2) := by omega
                rw [h1]
                have h2 : (p - q) * p' + (p' - 2) = p' * (p - q) + (p' - 2) := by ring
                rw [h2, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : p' - 2 < p'), Nat.add_zero]
              have hlower : xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≥ p - q - 1 := by
                calc xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩
                    ≥ (t - 1) * p / p' := hgap_lower
                  _ = ((p - q) * p' - 1) / p' := hdiv_eq
                  _ = p - q - 1 := hfloor
              have hupper : xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≤ p - q := by
                calc xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩
                    ≤ ((t - 1) * p + p' - 1) / p' := hgap_upper
                  _ = p - q := hupper_eq
              by_cases h_lt : xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ < p - q
              · -- Gap = p - q - 1. Need ceiling arithmetic to rule this out.
                have hgap_eq : xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ = p - q - 1 := by omega
                -- Following Case 1 pattern: this case leads to contradiction
                have hbound_pq' : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ = p - q :=
                  xSeq_pq'_eq hp' hp'_lt hp'_ge2 hq' hq'_lt_p' hbezout
                have hxr_strict : xSeq p p' hp' r ≥ p - q + 1 := by
                  have h1 : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ < xSeq p p' hp' r := hmono_strict
                  rw [hbound_pq'] at h1; omega
                -- Ceiling arithmetic: gap = p - q - 1 is impossible
                -- Following Case 1 pattern (lines 1710-1782):
                -- gap = p - q - 1 iff (r'+1)*p % p' = 1
                -- But r'+1 < q' and q' is the unique modular inverse, contradiction
                -- This case is proven by ceiling arithmetic (same as Case 1)
                have hgap_ge_pq : xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ ≥ p - q := by
                  -- The gap cannot be exactly p - q - 1 by ceiling arithmetic
                  -- (same argument as Case 1 at line 1712)
                  by_contra h_lt_pq
                  push_neg at h_lt_pq
                  have hgap_eq' : xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ = p - q - 1 := by omega
                  -- Same ceiling arithmetic as Case 1: this requires (r'+1)*p % p' = 1
                  -- But r'+1 < q' and q' is the unique inverse mod p', contradiction
                  have hr'1_lt_q' : r'.val + 1 < q' := by omega
                  have hq'_mod : q' * p % p' = 1 := by
                    have hbez : p * q' = q * p' + 1 := by omega
                    have h1 : q' * p = q * p' + 1 := by rw [Nat.mul_comm]; exact hbez
                    have h2 : q * p' = p' * q := Nat.mul_comm q p'
                    rw [h1, h2, Nat.mul_add_mod, Nat.mod_eq_of_lt hp'_ge2]
                  -- Use Case 1 ceiling arithmetic pattern
                  set a := (r'.val + 1) * p with ha_def
                  set q_a := a / p' with hq_a_def
                  set r_a := a % p' with hr_a_def
                  have ha_decomp : a = q_a * p' + r_a := (Nat.div_add_mod' a p').symm
                  have hr_a_lt : r_a < p' := Nat.mod_lt _ hp'
                  -- Derive the gap formula from xSeq definition
                  have hr_ne0 : r.val ≠ 0 := by
                    have : r.val > p' - q' := hr_ge_idx
                    omega
                  have hr'1_ne0 : (⟨r'.val + 1, hr'1_lt⟩ : Fin p').val ≠ 0 := Nat.succ_ne_zero r'.val
                  have hxSeq_r : xSeq p p' hp' r = (r.val * p + p' - 1) / p' := by
                    unfold xSeq; simp only [hr_ne0, ↓reduceIte]
                  have hxSeq_r'1 : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ = (a + p' - 1) / p' := by
                    unfold xSeq; simp only [hr'1_ne0, ↓reduceIte, ← ha_def]
                  -- Express r.val * p in terms of a
                  have hr_expand : r.val = r'.val + 1 + (t - 1) := by omega
                  have hr_mul : r.val * p = (r'.val + 1) * p + (t - 1) * p := by
                    rw [hr_expand]; ring
                  have ht1_mul : (t - 1) * p = (p - q) * p' - 1 := by rw [heq.symm]; exact hp'q'_mul
                  have hr_mul' : r.val * p = a + (p - q) * p' - 1 := by
                    rw [hr_mul, ← ha_def, ht1_mul]
                    have ha_ge : a ≥ 1 := by
                      rw [ha_def]
                      exact Nat.one_le_of_lt (Nat.mul_pos (Nat.succ_pos r'.val) (Nat.lt_trans (Nat.zero_lt_of_lt hp'_ge2) hp'_lt))
                    have hpq_mul_ge : (p - q) * p' ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
                    omega
                  have hr_mul'' : r.val * p = q_a * p' + r_a + (p - q) * p' - 1 := by
                    rw [hr_mul', ← ha_decomp]
                  -- Set up the gap equation in terms of q_a and r_a
                  have hpq_pos : p - q > 0 := by omega
                  have hpq_mul_pos : (p - q) * p' > 0 := Nat.mul_pos hpq_pos hp'
                  have ha_pos : a > 0 := by
                    rw [ha_def]
                    exact Nat.mul_pos (Nat.succ_pos r'.val) (Nat.lt_trans (Nat.zero_lt_of_lt hp'_ge2) hp'_lt)
                  have hsum_ge : q_a * p' + r_a + (p - q) * p' ≥ 1 := by
                    have := ha_decomp; omega
                  -- We need to derive heq_gap' showing gap equals ceiling formula difference
                  -- xSeq(r) = ceiling(r*p/p') = (r*p + p' - 1)/p'
                  -- xSeq(r'+1) = ceiling((r'+1)*p/p') = (a + p' - 1)/p'
                  -- Since r*p = q_a*p' + r_a + (p-q)*p' - 1, we have:
                  -- xSeq(r) = (q_a*p' + r_a + (p-q)*p' - 1 + p' - 1)/p'
                  --         = (q_a*p' + r_a + (p-q)*p' + p' - 2)/p'
                  have hxSeq_r_formula : xSeq p p' hp' r = (q_a * p' + r_a + (p - q) * p' + p' - 2) / p' := by
                    rw [hxSeq_r, hr_mul'']
                    congr 1
                    have h1 : q_a * p' + r_a + (p - q) * p' ≥ 1 := hsum_ge
                    omega
                  have hxSeq_r'1_formula : xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ = (q_a * p' + r_a + p' - 1) / p' := by
                    rw [hxSeq_r'1, ← ha_decomp]
                  -- Derive heq_gap' showing gap equals ceiling formula difference
                  have heq_gap'' : (q_a * p' + r_a + (p - q) * p' + p' - 2) / p' -
                      (q_a * p' + r_a + p' - 1) / p' = p - q - 1 := by
                    rw [← hxSeq_r_formula, ← hxSeq_r'1_formula, hgap_eq']
                  -- Case analysis on r_a to prove r_a = 1
                  have hp'_ge1 : p' ≥ 1 := Nat.one_le_of_lt hp'_ge2
                  have hpq_ge1 : (p - q) * p' ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
                  have hr_a_eq_1 : r_a = 1 := by
                    by_contra h_ne_1
                    rcases Nat.eq_zero_or_pos r_a with hr_a_zero | hr_a_pos
                    · -- r_a = 0: gap = p - q, contradiction
                      simp only [hr_a_zero, Nat.add_zero] at heq_gap''
                      have hrw2 : q_a * p' + p' - 1 = p' * q_a + (p' - 1) := by
                        rw [Nat.mul_comm q_a p', Nat.add_sub_assoc hp'_ge1]
                      have hrw1 : q_a * p' + (p - q) * p' + p' - 2 = p' * (q_a + p - q) + (p' - 2) := by
                        calc q_a * p' + (p - q) * p' + p' - 2
                            = q_a * p' + (p - q) * p' + (p' - 2) := by omega
                          _ = (q_a + (p - q)) * p' + (p' - 2) := by rw [Nat.add_mul]
                          _ = p' * (q_a + (p - q)) + (p' - 2) := by rw [Nat.mul_comm]
                          _ = p' * (q_a + p - q) + (p' - 2) := by rw [Nat.add_sub_assoc (Nat.le_of_lt hp_gt_q)]
                      have hLHS2 : (q_a * p' + p' - 1) / p' = q_a := by
                        rw [hrw2, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : p' - 1 < p'), Nat.add_zero]
                      have hLHS1 : (q_a * p' + (p - q) * p' + p' - 2) / p' = q_a + p - q := by
                        rw [hrw1, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : p' - 2 < p'), Nat.add_zero]
                      simp only [hLHS1, hLHS2] at heq_gap''; omega
                    · -- r_a >= 1
                      rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hr_a_pos)) with hr_a_one | hr_a_gt
                      · exact h_ne_1 hr_a_one.symm
                      · -- r_a >= 2: gap = p - q, contradiction
                        have hr_a_ge2 : r_a ≥ 2 := hr_a_gt
                        have hrw2 : q_a * p' + r_a + p' - 1 = p' * (q_a + 1) + (r_a - 1) := by
                          calc q_a * p' + r_a + p' - 1
                              = q_a * p' + p' + r_a - 1 := by omega
                            _ = (q_a + 1) * p' + (r_a - 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
                            _ = p' * (q_a + 1) + (r_a - 1) := by rw [Nat.mul_comm]
                        have hrw1 : q_a * p' + r_a + (p - q) * p' + p' - 2 = p' * (q_a + p - q + 1) + (r_a - 2) := by
                          calc q_a * p' + r_a + (p - q) * p' + p' - 2
                              = q_a * p' + (p - q) * p' + p' + (r_a - 2) := by omega
                            _ = (q_a + (p - q) + 1) * p' + (r_a - 2) := by rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
                            _ = p' * (q_a + (p - q) + 1) + (r_a - 2) := by rw [Nat.mul_comm]
                            _ = p' * (q_a + p - q + 1) + (r_a - 2) := by rw [Nat.add_sub_assoc (Nat.le_of_lt hp_gt_q)]
                        have hLHS2 : (q_a * p' + r_a + p' - 1) / p' = q_a + 1 := by
                          rw [hrw2, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : r_a - 1 < p'), Nat.add_zero]
                        have hLHS1 : (q_a * p' + r_a + (p - q) * p' + p' - 2) / p' = q_a + p - q + 1 := by
                          rw [hrw1, Nat.mul_add_div hp', Nat.div_eq_of_lt (by omega : r_a - 2 < p'), Nat.add_zero]
                        simp only [hLHS1, hLHS2] at heq_gap''; omega
                  -- Now r_a = 1 means (r'+1)*p % p' = 1
                  have hr'1_mod : (r'.val + 1) * p % p' = 1 := hr_a_def ▸ hr_a_eq_1
                  -- Both (r'+1)*p ≡ 1 (mod p') and q'*p ≡ 1 (mod p')
                  -- So (r'+1)*p ≡ q'*p (mod p')
                  -- Since gcd(p, p') = 1 (from Bezout), we can cancel p to get r'+1 ≡ q' (mod p')
                  -- Since both r'+1 < p' and q' < p', we have r'+1 = q'
                  -- But hr'1_lt_q' says r'+1 < q', contradiction
                  --
                  -- We show this by computing (q' - (r'+1)) * p mod p' = 0, then using coprimality
                  have h_mod_eq : (r'.val + 1) * p % p' = q' * p % p' := by rw [hr'1_mod, hq'_mod]
                  -- Since r'+1 < q', we have q'*p - (r'+1)*p = (q' - (r'+1))*p
                  have hle' : r'.val + 1 ≤ q' := Nat.le_of_lt hr'1_lt_q'
                  have hfact : q' * p - (r'.val + 1) * p = (q' - (r'.val + 1)) * p := by
                    calc q' * p - (r'.val + 1) * p
                        = (q' - (r'.val + 1) + (r'.val + 1)) * p - (r'.val + 1) * p := by
                            rw [Nat.sub_add_cancel hle']
                      _ = (q' - (r'.val + 1)) * p + (r'.val + 1) * p - (r'.val + 1) * p := by
                            rw [Nat.add_mul]
                      _ = (q' - (r'.val + 1)) * p := by omega
                  have hdiff_mod : (q' * p - (r'.val + 1) * p) % p' = 0 :=
                    Nat.sub_mod_eq_zero_of_mod_eq h_mod_eq.symm
                  rw [hfact] at hdiff_mod
                  have hdvd : p' ∣ (q' - (r'.val + 1)) * p := Nat.dvd_of_mod_eq_zero hdiff_mod
                  -- gcd(p, p') = 1 from Bezout identity
                  have hgcd : Nat.gcd p p' = 1 := by
                    have h1 : Nat.gcd p p' ∣ p := Nat.gcd_dvd_left p p'
                    have h2 : Nat.gcd p p' ∣ p' := Nat.gcd_dvd_right p p'
                    have h3 : Nat.gcd p p' ∣ p * q' := h1.mul_right q'
                    have h4 : Nat.gcd p p' ∣ q * p' := h2.mul_left q
                    have h5 : Nat.gcd p p' ∣ p * q' - q * p' := Nat.dvd_sub h3 h4
                    simp only [hbezout] at h5
                    exact Nat.eq_one_of_dvd_one h5
                  have hcoprime_pp' : Nat.Coprime p p' := hgcd
                  -- Use coprimality to cancel p: p' | (q' - (r'+1)) * p and gcd(p', p) = 1
                  -- implies p' | (q' - (r'+1))
                  have hdvd' : p' ∣ (q' - (r'.val + 1)) := hcoprime_pp'.symm.dvd_of_dvd_mul_right hdvd
                  -- But 0 < q' - (r'+1) < p', so the only possibility is q' - (r'+1) = 0
                  have hdiff_pos : q' - (r'.val + 1) > 0 := Nat.sub_pos_of_lt hr'1_lt_q'
                  have hdiff_lt : q' - (r'.val + 1) < p' := by omega
                  have hcontra : q' - (r'.val + 1) ≥ p' := Nat.le_of_dvd hdiff_pos hdvd'
                  omega
                exact hgap_ge_pq
              · omega
            · -- Case: t - 1 > p' - q' (span strictly larger)
              have hs_gt : t - 1 ≥ p' - q' + 1 := Nat.lt_iff_add_one_le.mp hlt
              have hmul_bound : (t - 1) * p ≥ (p' - q' + 1) * p := Nat.mul_le_mul_right p hs_gt
              have hpq1_mul : (p' - q' + 1) * p = (p' - q') * p + p := by ring
              have hpq1_expand : (p' - q' + 1) * p = (p - q) * p' - 1 + p := by rw [hpq1_mul, hp'q'_mul]
              have hp_gt_1 : p > 1 := Nat.lt_trans (Nat.lt_of_lt_of_le Nat.one_lt_two hp'_ge2) hp'_lt
              have hsum_gt : (p - q) * p' - 1 + p > (p - q) * p' := by omega
              have hdiv_gt : (p' - q' + 1) * p / p' ≥ p - q := by
                have h1 : (p' - q' + 1) * p > (p - q) * p' := by
                  calc (p' - q' + 1) * p = (p - q) * p' - 1 + p := hpq1_expand
                    _ > (p - q) * p' := hsum_gt
                have h1' : (p' - q' + 1) * p ≥ (p - q) * p' := Nat.le_of_lt h1
                exact Nat.le_div_iff_mul_le hp' |>.mpr h1'
              calc xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩
                  ≥ (t - 1) * p / p' := hgap_lower
                _ ≥ (p' - q' + 1) * p / p' := Nat.div_le_div_right hmul_bound
                _ ≥ p - q := hdiv_gt
          have hdiff_gt : y.val - y'.val > p - q := by
            calc y.val - y'.val ≥ xSeq p p' hp' r - xSeq p p' hp' ⟨r'.val + 1, hr'1_lt⟩ + 1 := hdiff_ge
              _ ≥ (p - q) + 1 := by omega
              _ > p - q := by omega
          have hback_dist : p - (y.val - y'.val) < q := by omega
          have hsub_back : (y' - y).val = p - (y.val - y'.val) := by
            have hle : y'.val ≤ y.val := Nat.le_of_lt hyy'
            have hlt_p : y.val - y'.val < p := by omega
            have h1 : (y - y').val = y.val - y'.val := ZMod.val_sub (by omega)
            have h2 : (y' - y) = -(y - y') := by ring
            rw [h2]
            have hne_zero : y - y' ≠ 0 := by
              intro heq
              have hval : (y - y').val = 0 := by simp [heq]
              rw [h1] at hval
              omega
            haveI : NeZero (y - y') := ⟨hne_zero⟩
            have hneg := ZMod.val_neg_of_ne_zero (a := y - y')
            rw [hneg, h1]
          have hcirc : circDist p y y' < q := by
            unfold circDist
            calc min (y' - y).val (y - y').val
                ≤ (y' - y).val := Nat.min_le_left _ _
              _ = p - (y.val - y'.val) := hsub_back
              _ < q := hback_dist
          omega
      · -- Backward gap (r - r').val < q' means t < q'
        rw [h_sub_val] at h_bwd
        have ht_lt_q' : t < q' := h_bwd
        -- Symmetric to Case 1 forward gap case
        by_cases hr'q'_lt : r'.val + q' < p'
        · by_cases hr'_zero : r'.val = 0
          · -- r' = 0: xSeq(q') - xSeq(0) = q + 1, but y ≠ q
            have hr'0 : r' = ⟨0, hp'⟩ := Fin.ext hr'_zero
            have hgap := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout ⟨0, hp'⟩ (by omega : 0 + q' < p')).1 rfl
            simp only [xSeq_zero, Nat.sub_zero, Nat.zero_add] at hgap
            have hq'_lt_p' : q' < p' := by omega
            have hr_lt_q' : r.val < q' := by
              have ht_eq : t = r.val := by simp [ht_def, hr'_zero]
              omega
            have hr1_lt : r.val + 1 < p' := by omega
            have hy_up := h_r_upper ⟨r.val + 1, hr1_lt⟩ (Nat.lt_succ_self _)
            have hr1_le_q' : r.val + 1 ≤ q' := Nat.succ_le_of_lt hr_lt_q'
            have hmono' : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ xSeq p p' hp' ⟨q', hq'_lt_p'⟩ :=
              xSeq_mono ⟨r.val + 1, hr1_lt⟩ ⟨q', hq'_lt_p'⟩ (Fin.le_def.mpr hr1_le_q')
            have hgap' : xSeq p p' hp' ⟨q', hq'_lt_p'⟩ = q + 1 := hgap
            have hy_lt : y.val < q + 1 := by
              calc y.val < xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ := hy_up
                _ ≤ xSeq p p' hp' ⟨q', hq'_lt_p'⟩ := hmono'
                _ = q + 1 := hgap'
            have hq_val : (q : ZMod p).val = q := ZMod.val_natCast_of_lt hq_lt
            have hy_ne_q : y.val ≠ q := by intro h; exact hy (ZMod.val_injective p (h.trans hq_val.symm))
            have hy_lt_q : y.val < q := by omega
            have hdiff : y.val - y'.val < q := by omega
            have hcirc : circDist p y y' < q := by
              unfold circDist
              have hsub : (y - y').val = y.val - y'.val := ZMod.val_sub (by omega)
              calc min (y' - y).val (y - y').val ≤ (y - y').val := Nat.min_le_right _ _
                _ = y.val - y'.val := hsub
                _ < q := hdiff
            omega
          · -- r' ≥ 1: xSeq(r'+q') - xSeq(r') = q
            have hgap := (xSeq_gap_q' hp' hp'_lt hq' hq'_lt hbezout r' hr'q'_lt).2 hr'_zero
            have hr1_le_r'q' : r.val + 1 ≤ r'.val + q' := by omega
            have hr1_lt : r.val + 1 < p' := Nat.lt_of_le_of_lt hr1_le_r'q' hr'q'_lt
            have hy_up := h_r_upper ⟨r.val + 1, hr1_lt⟩ (Nat.lt_succ_self _)
            have hmono' : xSeq p p' hp' ⟨r.val + 1, hr1_lt⟩ ≤ xSeq p p' hp' ⟨r'.val + q', hr'q'_lt⟩ :=
              xSeq_mono ⟨r.val + 1, hr1_lt⟩ ⟨r'.val + q', hr'q'_lt⟩ (Fin.le_def.mpr hr1_le_r'q')
            have hy_bound : y.val < xSeq p p' hp' ⟨r'.val + q', hr'q'_lt⟩ :=
              Nat.lt_of_lt_of_le hy_up hmono'
            have hdiff : y.val - y'.val < q := by
              calc y.val - y'.val
                  < xSeq p p' hp' ⟨r'.val + q', hr'q'_lt⟩ - y'.val := by omega
                _ ≤ xSeq p p' hp' ⟨r'.val + q', hr'q'_lt⟩ - xSeq p p' hp' r' := by omega
                _ = q := hgap
            have hcirc : circDist p y y' < q := by
              unfold circDist
              have hsub : (y - y').val = y.val - y'.val := ZMod.val_sub (by omega)
              calc min (y' - y).val (y - y').val ≤ (y - y').val := Nat.min_le_right _ _
                _ = y.val - y'.val := hsub
                _ < q := hdiff
            omega
        · -- r' + q' ≥ p': edge case
          -- Both r and r' are in the upper region [p' - q', p' - 1]
          -- So xSeq(r), xSeq(r') ≥ p - q, meaning y, y' ∈ [p - q, p)
          -- This interval has size ≤ q, so |y - y'| < q
          have hr'_ge_pq : r'.val ≥ p' - q' := by omega
          have hp'_ge2 : 2 ≤ p' := by
            by_contra h
            have hp'_lt2 : p' < 2 := Nat.not_le.mp h
            have hp'_eq1 : p' = 1 := by omega
            -- Same contradiction as Case 2: p' = 1 violates Bezout + h2q
            have hbezout' : p * q' = q + 1 := by
              have hbez := hbezout
              simp only [hp'_eq1, Nat.mul_one] at hbez
              omega
            have hp_ge_2q : p ≥ 2 * q := h2q
            have hpq'_ge : p * q' ≥ 2 * q * q' := Nat.mul_le_mul_right q' hp_ge_2q
            have hq_ge2 : q ≥ 2 := hq
            have hq'_ge1 : q' ≥ 1 := hq'
            have h1 : 2 * q ≤ 2 * q * q' := by
              have : 2 * q * 1 ≤ 2 * q * q' := Nat.mul_le_mul_left (2 * q) hq'_ge1
              simp only [Nat.mul_one] at this
              exact this
            have h2 : 2 * q ≥ q + 2 := by omega
            have h3 : 2 * q * q' ≥ q + 2 := Nat.le_trans h2 h1
            have h4 : p * q' ≥ q + 2 := Nat.le_trans h3 hpq'_ge
            omega
          have hq'_lt_p'_strict : q' < p' := q'_lt_p'_of_bezout hp' hp'_ge2 hq' hq'_lt hq (by omega) hbezout
          have hpq'_idx : p' - q' < p' := Nat.sub_lt hp' hq'
          have hbound_r' : xSeq p p' hp' r' ≥ xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ :=
            xSeq_mono ⟨p' - q', hpq'_idx⟩ r' (Fin.le_def.mpr hr'_ge_pq)
          have hbound_pq : xSeq p p' hp' ⟨p' - q', hpq'_idx⟩ ≥ p - q :=
            xSeq_pq'_bound hp' hp'_ge2 hq' hq'_lt_p'_strict hbezout
          have hxr'_ge : xSeq p p' hp' r' ≥ p - q := Nat.le_trans hbound_pq hbound_r'
          -- r ≥ r' in indices (since r > r'), so xSeq(r) ≥ xSeq(r') ≥ p - q
          have hr_ge_r' : r.val ≥ r'.val := Nat.le_of_lt h_gt
          have hbound_r : xSeq p p' hp' r ≥ xSeq p p' hp' r' :=
            xSeq_mono r' r (Fin.le_def.mpr hr_ge_r')
          have hxr_ge : xSeq p p' hp' r ≥ p - q := Nat.le_trans hxr'_ge hbound_r
          -- y, y' ∈ [p - q, p), interval size ≤ q
          have hy_ge : y.val ≥ p - q := Nat.le_trans hxr_ge h_r_mem
          have hy'_ge : y'.val ≥ p - q := Nat.le_trans hxr'_ge h_r'_mem
          have hy_lt : y.val < p := ZMod.val_lt y
          have hy'_lt : y'.val < p := ZMod.val_lt y'
          have hy_ne_y' : y.val ≠ y'.val := by
            intro heq
            have : y = y' := ZMod.val_injective p heq
            exact hne this
          -- |y - y'| < q since both are in [p - q, p) and y ≠ y'
          have hdiff_lt : y.val - y'.val < q := by omega
          have hcirc : circDist p y y' < q := by
            unfold circDist
            have hsub : (y - y').val = y.val - y'.val := ZMod.val_sub (by omega : y'.val ≤ y.val)
            calc min (y' - y).val (y - y').val ≤ (y - y').val := Nat.min_le_right _ _
              _ = y.val - y'.val := hsub
              _ < q := hdiff_lt
          omega

  -- Now hr_ne_r' follows from hdist_r: if q' ≤ circDist(r, r'), then r ≠ r'
  have hr_ne_r' : r ≠ r' := by
    intro heq
    rw [heq] at hdist_r
    -- circDist(r', r') = 0, but hdist_r says q' ≤ circDist ≥ 1
    unfold circDist at hdist_r
    simp only [sub_self, ZMod.val_zero, Nat.min_self] at hdist_r
    omega
  -- Combine: r ≠ r' and q' ≤ circDist(r, r') gives adjacency in K_{p'/q'}
  unfold Kpq
  simp only [ne_eq]
  constructor
  · intro heq
    apply hr_ne_r'
    have hr_lt : r.val < p' := r.isLt
    have hr'_lt : r'.val < p' := r'.isLt
    have hval_eq : r.val = r'.val := by
      have h1 : (r.val : ZMod p').val = r.val := ZMod.val_natCast_of_lt hr_lt
      have h2 : (r'.val : ZMod p').val = r'.val := ZMod.val_natCast_of_lt hr'_lt
      calc r.val = (r.val : ZMod p').val := h1.symm
        _ = (r'.val : ZMod p').val := congrArg ZMod.val heq
        _ = r'.val := h2
    exact Fin.ext hval_eq
  · exact hdist_r

/-- Ceiling+Floor Identity: For t ∈ [1, p'-1] with gcd(p, p') = 1,
    ⌈t·p/p'⌉ + ⌊(p'-t)·p/p'⌋ = p.
    This is the key to proving the upper bound on xSeq gaps. -/
lemma ceiling_floor_identity (hp' : 0 < p') (hcoprime_pp' : Nat.Coprime p p')
    (t : ℕ) (ht_pos : 0 < t) (ht_lt : t < p') :
    (t * p + p' - 1) / p' + ((p' - t) * p) / p' = p := by
  -- Key insight: t * p + (p' - t) * p = p' * p
  -- Since gcd(p, p') = 1 and 1 ≤ t ≤ p' - 1, neither t * p nor (p' - t) * p is divisible by p'.
  -- The remainders sum to p', so: ⌈t·p/p'⌉ + ⌊(p'-t)·p/p'⌋ = (quotient sum) + 1 = (p - 1) + 1 = p
  have hp'_ne : p' ≠ 0 := Nat.pos_iff_ne_zero.mp hp'
  have hpt_pos : 0 < p' - t := Nat.sub_pos_of_lt ht_lt
  -- t * p is not divisible by p'
  have h_tp_mod : t * p % p' ≠ 0 := by
    intro h
    have hdvd : p' ∣ t * p := Nat.dvd_of_mod_eq_zero h
    have hdvdt : p' ∣ t := hcoprime_pp'.symm.dvd_of_dvd_mul_right hdvd
    exact Nat.not_lt.mpr (Nat.le_of_dvd ht_pos hdvdt) ht_lt
  -- (p' - t) * p is not divisible by p'
  have h_ptp_mod : (p' - t) * p % p' ≠ 0 := by
    intro h
    have hdvd : p' ∣ (p' - t) * p := Nat.dvd_of_mod_eq_zero h
    have hdvdt : p' ∣ p' - t := hcoprime_pp'.symm.dvd_of_dvd_mul_right hdvd
    have hge : p' ≤ p' - t := Nat.le_of_dvd hpt_pos hdvdt
    omega
  -- Key: remainders sum to p'
  have h_mod_sum : t * p % p' + (p' - t) * p % p' = p' := by
    have h_total : (t * p + (p' - t) * p) % p' = 0 := by
      have heq : t * p + (p' - t) * p = p' * p := by
        have : t + (p' - t) = p' := by omega
        calc t * p + (p' - t) * p = (t + (p' - t)) * p := by ring
          _ = p' * p := by rw [this]
      rw [heq]
      simp only [Nat.mul_mod_right]
    have h_add_mod : (t * p % p' + (p' - t) * p % p') % p' = 0 := by
      rw [← Nat.add_mod]; exact h_total
    have hm1 : t * p % p' < p' := Nat.mod_lt _ hp'
    have hm2 : (p' - t) * p % p' < p' := Nat.mod_lt _ hp'
    have hm1_pos : 0 < t * p % p' := Nat.pos_of_ne_zero h_tp_mod
    have hm2_pos : 0 < (p' - t) * p % p' := Nat.pos_of_ne_zero h_ptp_mod
    -- Sum is in (0, 2p') and ≡ 0 mod p', so sum = p'
    have hsum_pos : 0 < t * p % p' + (p' - t) * p % p' := Nat.add_pos_left hm1_pos _
    have hsum_lt : t * p % p' + (p' - t) * p % p' < 2 * p' := by omega
    -- If sum % p' = 0 and 0 < sum < 2p', then sum = p'
    have hdiv : p' ∣ t * p % p' + (p' - t) * p % p' := Nat.dvd_of_mod_eq_zero h_add_mod
    rcases hdiv with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hle
      push_neg at hle
      interval_cases k; omega
    have hk_lt2 : k < 2 := by
      by_contra hge
      push_neg at hge
      have : t * p % p' + (p' - t) * p % p' ≥ 2 * p' := by
        calc t * p % p' + (p' - t) * p % p' = p' * k := hk
          _ ≥ p' * 2 := Nat.mul_le_mul_left p' hge
          _ = 2 * p' := by ring
      omega
    interval_cases k
    omega
  -- Ceiling formula: (t * p + p' - 1) / p' = t * p / p' + 1
  have h_ceil : (t * p + p' - 1) / p' = t * p / p' + 1 := by
    have hmod_pos : 0 < t * p % p' := Nat.pos_of_ne_zero h_tp_mod
    have hmod_lt : t * p % p' < p' := Nat.mod_lt _ hp'
    -- Write t * p = p' * q + r where r = t * p % p'
    have hdiv_mod : t * p = p' * (t * p / p') + t * p % p' := (Nat.div_add_mod (t * p) p').symm
    -- So t * p + p' - 1 = p' * q + (r + p' - 1) where p' ≤ r + p' - 1 < 2p'
    have h1 : t * p + p' - 1 = p' * (t * p / p') + (t * p % p' + p' - 1) := by omega
    rw [h1]
    -- (p' * q + s) / p' = q + s / p' when p' > 0
    have h2 : (p' * (t * p / p') + (t * p % p' + p' - 1)) / p' =
              t * p / p' + (t * p % p' + p' - 1) / p' := by
      have : p' * (t * p / p') + (t * p % p' + p' - 1) =
             (t * p % p' + p' - 1) + p' * (t * p / p') := by ring
      rw [this, Nat.add_mul_div_left _ _ hp', Nat.add_comm]
    rw [h2]
    -- (r + p' - 1) / p' = 1 since p' ≤ r + p' - 1 < 2p'
    have hlo : p' ≤ t * p % p' + p' - 1 := by omega
    have hhi : t * p % p' + p' - 1 < 2 * p' := by omega
    have hdiv_1 : (t * p % p' + p' - 1) / p' = 1 := by
      have hlo' : 1 * p' ≤ t * p % p' + p' - 1 := by omega
      exact Nat.div_eq_of_lt_le hlo' hhi
    omega
  -- Floor sum: t * p / p' + (p' - t) * p / p' = p - 1
  have h_div_sum : t * p / p' + (p' - t) * p / p' = p - 1 := by
    have hdiv1 : t * p = p' * (t * p / p') + t * p % p' := (Nat.div_add_mod (t * p) p').symm
    have hdiv2 : (p' - t) * p = p' * ((p' - t) * p / p') + (p' - t) * p % p' :=
      (Nat.div_add_mod ((p' - t) * p) p').symm
    have h_total : t * p + (p' - t) * p = p' * p := by
      have : t + (p' - t) = p' := by omega
      calc t * p + (p' - t) * p = (t + (p' - t)) * p := by ring
        _ = p' * p := by rw [this]
    -- Substitute divisions
    have h3 : p' * (t * p / p') + t * p % p' + (p' * ((p' - t) * p / p') + (p' - t) * p % p') =
              p' * p := by rw [← hdiv1, ← hdiv2]; exact h_total
    have h4 : p' * (t * p / p' + (p' - t) * p / p') + (t * p % p' + (p' - t) * p % p') =
              p' * p := by linarith
    rw [h_mod_sum] at h4
    have h5 : p' * (t * p / p' + (p' - t) * p / p') + p' = p' * p := h4
    have h6 : p' * (t * p / p' + (p' - t) * p / p' + 1) = p' * p := by linarith
    have h7 : t * p / p' + (p' - t) * p / p' + 1 = p := Nat.eq_of_mul_eq_mul_left hp' h6
    -- From s + 1 = p, derive s = p - 1
    -- First show p > 0: if p = 0, coprimality gives p' = 1, but t < p' and t > 0, contradiction
    have hp_pos : 0 < p := by
      by_contra h; push_neg at h
      interval_cases p
      -- p = 0 case: Coprime 0 p' means gcd(0,p') = 1, so p' = 1
      -- But t < p' and t > 0 means t < 1 and t ≥ 1, contradiction
      have hp'_eq : p' = 1 := by
        unfold Nat.Coprime at hcoprime_pp'
        rw [Nat.gcd_zero_left] at hcoprime_pp'
        exact hcoprime_pp'
      omega
    -- From h7: s + 1 = p, so s = p - 1
    have h7' : 1 + (t * p / p' + (p' - t) * p / p') = p := by omega
    exact Nat.eq_sub_of_add_eq' h7'
  -- Combine: (t * p / p' + 1) + (p' - t) * p / p' = (p - 1) + 1 = p
  rw [h_ceil]
  -- Goal: t * p / p' + 1 + (p' - t) * p / p' = p
  -- h_div_sum: t * p / p' + (p' - t) * p / p' = p - 1
  -- Rearrange and use h_div_sum
  have h_rearrange : t * p / p' + 1 + (p' - t) * p / p' =
                     t * p / p' + (p' - t) * p / p' + 1 := by omega
  rw [h_rearrange, h_div_sum]
  -- Goal: p - 1 + 1 = p
  -- First show p > 0 using coprimality
  have hp_pos : 0 < p := by
    by_contra h; push_neg at h
    interval_cases p
    have hp'_eq : p' = 1 := by
      unfold Nat.Coprime at hcoprime_pp'
      rw [Nat.gcd_zero_left] at hcoprime_pp'
      exact hcoprime_pp'
    omega
  omega

/-- The embedding preserves adjacency: if i ~ j in K_{p'/q'},
    then embed(i) ~ embed(j) in K_{p/q}. -/
theorem embed_preserves_adj [NeZero p'] (hp' : 0 < p') (hp'_lt : p' < p)
    (hq' : 0 < q') (hq'_lt : q' < q) (h2q : 2 * q ≤ p)
    (hbezout : p * q' - q * p' = 1)
    (i j : ZMod p')
    (hadj : (Kpq p' q').Adj i j) :
    (Kpq p q).Adj (embed hp' ⟨i.val, ZMod.val_lt i⟩) (embed hp' ⟨j.val, ZMod.val_lt j⟩) := by
  -- The proof uses xSeq_gap_large and ceiling_floor_identity to show that
  -- adjacency in K_{p'/q'} (circDist ≥ q') maps to adjacency in K_{p/q} (circDist ≥ q).
  -- Key insight: For q' ≤ t ≤ p' - q', we have q ≤ xSeq gap ≤ p - q.
  -- The lower bound follows from xSeq_gap_large.
  -- The upper bound follows from ceiling_floor_identity: the complementary gap is also ≥ q.
  simp only [Kpq, ne_eq] at hadj ⊢
  obtain ⟨hne, hcircDist⟩ := hadj
  -- Set up notation for indices and values
  let i' : Fin p' := ⟨i.val, ZMod.val_lt i⟩
  let j' : Fin p' := ⟨j.val, ZMod.val_lt j⟩
  let xi := xSeq p p' hp' i'
  let xj := xSeq p p' hp' j'
  -- circDist ≥ q' means min(forward, backward) ≥ q'
  -- So both directions have index gap ≥ q'
  have hcircDist' : circDist p' i j ≥ q' := hcircDist
  unfold circDist at hcircDist'
  have h_forward : (j - i).val ≥ q' := Nat.le_min.mp hcircDist' |>.1
  have h_backward : (i - j).val ≥ q' := Nat.le_min.mp hcircDist' |>.2
  -- Need to show: embed values ≠ and circDist ≥ q
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hxi_lt : xi < p := xSeq_lt_p hp' hp'_lt hp_pos i'
  have hxj_lt : xj < p := xSeq_lt_p hp' hp'_lt hp_pos j'
  -- Show embed i' = xi and embed j' = xj as ZMod p
  have hembed_i : embed hp' i' = (xi : ZMod p) := rfl
  have hembed_j : embed hp' j' = (xj : ZMod p) := rfl
  constructor
  · -- embed(i') ≠ embed(j') (by strict monotonicity of xSeq)
    intro heq
    have hxi_ne_xj : xi ≠ xj := by
      intro heq_nat
      -- If xSeq values are equal, then indices must be equal (by strict mono)
      -- But i ≠ j, contradiction
      by_cases hij : i'.val < j'.val
      · have := xSeq_strictMono hp' hp'_lt hbezout i' j' hij
        simp only [xi, xj] at heq_nat
        omega
      · push_neg at hij
        by_cases hji : j'.val < i'.val
        · have := xSeq_strictMono hp' hp'_lt hbezout j' i' hji
          simp only [xi, xj] at heq_nat
          omega
        · push_neg at hji
          have heq_val : i'.val = j'.val := le_antisymm hji hij
          have : i.val = j.val := heq_val
          exact hne (ZMod.val_injective p' this)
    apply hxi_ne_xj
    -- From embed(i') = embed(j') as ZMod p, deduce xi = xj
    rw [hembed_i, hembed_j] at heq
    have hxi_mod : (xi : ZMod p).val = xi := ZMod.val_natCast_of_lt hxi_lt
    have hxj_mod : (xj : ZMod p).val = xj := ZMod.val_natCast_of_lt hxj_lt
    calc xi = (xi : ZMod p).val := hxi_mod.symm
      _ = (xj : ZMod p).val := by rw [heq]
      _ = xj := hxj_mod
  · -- circDist p (embed i') (embed j') ≥ q
    -- Rewrite to work with xi and xj
    rw [hembed_i, hembed_j]
    -- WLOG: Consider i.val < j.val case (the other is symmetric)
    by_cases hij : i.val < j.val
    · -- Case: i.val < j.val, so xi < xj by strict monotonicity
      have hxi_lt_xj : xi < xj := xSeq_strictMono hp' hp'_lt hbezout i' j' hij
      -- Index gap t = j.val - i.val ≥ q'
      set t := j.val - i.val with ht_def
      have h_forward_val : (j - i).val = t := by
        have hi_lt : i.val < p' := ZMod.val_lt i
        have hj_lt : j.val < p' := ZMod.val_lt j
        have h1 : (j - i).val = (j.val + (p' - i.val)) % p' := by
          rw [sub_eq_add_neg, ZMod.val_add]
          by_cases hi0 : i = 0
          · simp only [hi0, neg_zero, ZMod.val_zero, Nat.sub_zero, Nat.add_zero,
              Nat.add_mod_right, Nat.mod_eq_of_lt hj_lt]
          · haveI : NeZero i := ⟨hi0⟩
            rw [ZMod.val_neg_of_ne_zero i]
        have h2 : j.val + (p' - i.val) = t + p' := by simp only [t]; omega
        rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt]
        simp only [t]; omega
      rw [h_forward_val] at h_forward
      have ht_ge : t ≥ q' := h_forward
      have ht_bound : i'.val + t < p' := by
        simp only [i', t]
        have hj_lt : j.val < p' := ZMod.val_lt j
        omega
      -- xj = xSeq ⟨i'.val + t, ht_bound⟩
      have hj'_eq_sum : j' = ⟨i'.val + t, ht_bound⟩ := Fin.ext (by simp only [i', j', t]; omega)
      -- By xSeq_gap_large: xj - xi ≥ q
      have h_val_gap_ge : xj - xi ≥ q := by
        have h := xSeq_gap_large hp' hp'_lt hq' hbezout i' t ht_ge ht_bound
        simp only [xj, xi]
        convert h using 2
        exact congrArg (xSeq p p' hp') hj'_eq_sum
      -- For the upper bound, use ceiling_floor_identity
      have h_backward_val : (i - j).val = p' - t := by
        have hi_lt : i.val < p' := ZMod.val_lt i
        have hj_lt : j.val < p' := ZMod.val_lt j
        have h1 : (i - j).val = (i.val + (p' - j.val)) % p' := by
          rw [sub_eq_add_neg, ZMod.val_add]
          by_cases hj0 : j = 0
          · simp only [hj0, neg_zero, ZMod.val_zero, Nat.sub_zero, Nat.add_zero,
              Nat.add_mod_right, Nat.mod_eq_of_lt hi_lt]
          · haveI : NeZero j := ⟨hj0⟩
            rw [ZMod.val_neg_of_ne_zero j]
        have h2 : i.val + (p' - j.val) = p' - t := by simp only [t]; omega
        rw [h1, h2, Nat.mod_eq_of_lt]; simp only [t]; omega
      rw [h_backward_val] at h_backward
      have hpt_ge : p' - t ≥ q' := h_backward
      have h_coprime_pp' : Nat.Coprime p p' := coprime_p_p' hbezout
      have h_gap_upper' := (xSeq_gap_bound hp' hp'_lt i' t (Nat.lt_of_lt_of_le hq' ht_ge) ht_bound).2
      have h_gap_upper : xj - xi ≤ (t * p + p' - 1) / p' := by
        simp only [xj, xi]
        convert h_gap_upper' using 2
        exact congrArg (xSeq p p' hp') hj'_eq_sum
      have ht_pos : 0 < t := Nat.lt_of_lt_of_le hq' ht_ge
      have ht_lt_p' : t < p' := by simp only [t]; omega
      have h_ceil_floor := ceiling_floor_identity hp' h_coprime_pp' t ht_pos ht_lt_p'
      have h_comp_floor_ge : (p' - t) * p / p' ≥ q := by
        have h_tp_bound : (p' - t) * p ≥ q' * p := Nat.mul_le_mul_right p hpt_ge
        have hbezout_add : p * q' = q * p' + 1 := by omega
        have h_qp_bound : q' * p ≥ q * p' := by
          calc q' * p = p * q' := Nat.mul_comm q' p
            _ = q * p' + 1 := hbezout_add
            _ ≥ q * p' := Nat.le_add_right _ _
        exact Nat.le_div_iff_mul_le hp' |>.mpr (Nat.le_trans h_qp_bound h_tp_bound)
      have h_ceil_le : (t * p + p' - 1) / p' ≤ p - q := by omega
      have h_val_gap_le : xj - xi ≤ p - q := Nat.le_trans h_gap_upper h_ceil_le
      -- Now show circDist ≥ q
      unfold circDist
      -- ZMod arithmetic for subtraction
      have hxj_xi_lt : xj - xi < p := by omega
      have hp_minus_lt : p - (xj - xi) < p := by omega
      have h_forward_zmod : ((xj : ZMod p) - (xi : ZMod p)).val = xj - xi := by
        have hle : xi ≤ xj := Nat.le_of_lt hxi_lt_xj
        have hxj_val : (xj : ZMod p).val = xj := ZMod.val_natCast_of_lt hxj_lt
        have hxi_val : (xi : ZMod p).val = xi := ZMod.val_natCast_of_lt hxi_lt
        have hle' : (xi : ZMod p).val ≤ (xj : ZMod p).val := by rw [hxi_val, hxj_val]; exact hle
        rw [ZMod.val_sub hle', hxj_val, hxi_val]
      have h_backward_zmod : ((xi : ZMod p) - (xj : ZMod p)).val = p - (xj - xi) := by
        have hle : xi ≤ xj := Nat.le_of_lt hxi_lt_xj
        have hxj_val : (xj : ZMod p).val = xj := ZMod.val_natCast_of_lt hxj_lt
        have hxi_val : (xi : ZMod p).val = xi := ZMod.val_natCast_of_lt hxi_lt
        rw [sub_eq_add_neg, ZMod.val_add, hxi_val]
        by_cases hxj0 : (xj : ZMod p) = 0
        · have hxj_zero : xj = 0 := by
            rw [ZMod.natCast_eq_zero_iff] at hxj0
            exact Nat.eq_zero_of_dvd_of_lt hxj0 hxj_lt
          simp [hxj_zero] at hxi_lt_xj
        · haveI : NeZero (xj : ZMod p) := ⟨hxj0⟩
          rw [ZMod.val_neg_of_ne_zero (xj : ZMod p), hxj_val]
          have heq : xi + (p - xj) = p - (xj - xi) := by omega
          rw [heq, Nat.mod_eq_of_lt hp_minus_lt]
      rw [h_forward_zmod, h_backward_zmod]
      apply Nat.le_min.mpr
      exact ⟨h_val_gap_ge, by omega⟩
    · -- Case: j.val ≤ i.val (symmetric by swapping roles)
      push_neg at hij
      have hji : j.val < i.val := Nat.lt_of_le_of_ne hij (by intro h; exact hne (ZMod.val_injective p' h.symm))
      have hxj_lt_xi : xj < xi := xSeq_strictMono hp' hp'_lt hbezout j' i' hji
      -- Index gap t = i.val - j.val ≥ q' (from backward direction)
      set t := i.val - j.val with ht_def
      have h_backward_val : (i - j).val = t := by
        have hi_lt : i.val < p' := ZMod.val_lt i
        have hj_lt : j.val < p' := ZMod.val_lt j
        have h1 : (i - j).val = (i.val + (p' - j.val)) % p' := by
          rw [sub_eq_add_neg, ZMod.val_add]
          by_cases hj0 : j = 0
          · simp only [hj0, neg_zero, ZMod.val_zero, Nat.sub_zero, Nat.add_zero,
              Nat.add_mod_right, Nat.mod_eq_of_lt hi_lt]
          · haveI : NeZero j := ⟨hj0⟩
            rw [ZMod.val_neg_of_ne_zero j]
        have h2 : i.val + (p' - j.val) = t + p' := by simp only [t]; omega
        rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt]
        simp only [t]; omega
      rw [h_backward_val] at h_backward
      have ht_ge : t ≥ q' := h_backward
      have ht_bound : j'.val + t < p' := by
        simp only [j', t]
        have hi_lt : i.val < p' := ZMod.val_lt i
        omega
      -- xi = xSeq ⟨j'.val + t, ht_bound⟩
      have hi'_eq_sum : i' = ⟨j'.val + t, ht_bound⟩ := Fin.ext (by simp only [j', t, i']; omega)
      -- By xSeq_gap_large: xi - xj ≥ q
      have h_val_gap_ge : xi - xj ≥ q := by
        have h := xSeq_gap_large hp' hp'_lt hq' hbezout j' t ht_ge ht_bound
        simp only [xi, xj]
        convert h using 2
        exact congrArg (xSeq p p' hp') hi'_eq_sum
      -- For the upper bound
      have h_forward_val : (j - i).val = p' - t := by
        have hi_lt : i.val < p' := ZMod.val_lt i
        have hj_lt : j.val < p' := ZMod.val_lt j
        have h1 : (j - i).val = (j.val + (p' - i.val)) % p' := by
          rw [sub_eq_add_neg, ZMod.val_add]
          by_cases hi0 : i = 0
          · simp only [hi0, neg_zero, ZMod.val_zero, Nat.sub_zero, Nat.add_zero,
              Nat.add_mod_right, Nat.mod_eq_of_lt hj_lt]
          · haveI : NeZero i := ⟨hi0⟩
            rw [ZMod.val_neg_of_ne_zero i]
        have h2 : j.val + (p' - i.val) = p' - t := by simp only [t]; omega
        rw [h1, h2, Nat.mod_eq_of_lt]; simp only [t]; omega
      rw [h_forward_val] at h_forward
      have hpt_ge : p' - t ≥ q' := h_forward
      have h_coprime_pp' : Nat.Coprime p p' := coprime_p_p' hbezout
      have h_gap_upper' := (xSeq_gap_bound hp' hp'_lt j' t (Nat.lt_of_lt_of_le hq' ht_ge) ht_bound).2
      have h_gap_upper : xi - xj ≤ (t * p + p' - 1) / p' := by
        simp only [xi, xj]
        convert h_gap_upper' using 2
        exact congrArg (xSeq p p' hp') hi'_eq_sum
      have ht_pos : 0 < t := Nat.lt_of_lt_of_le hq' ht_ge
      have ht_lt_p' : t < p' := by simp only [t]; omega
      have h_ceil_floor := ceiling_floor_identity hp' h_coprime_pp' t ht_pos ht_lt_p'
      have h_comp_floor_ge : (p' - t) * p / p' ≥ q := by
        have h_tp_bound : (p' - t) * p ≥ q' * p := Nat.mul_le_mul_right p hpt_ge
        have hbezout_add : p * q' = q * p' + 1 := by omega
        have h_qp_bound : q' * p ≥ q * p' := by
          calc q' * p = p * q' := Nat.mul_comm q' p
            _ = q * p' + 1 := hbezout_add
            _ ≥ q * p' := Nat.le_add_right _ _
        exact Nat.le_div_iff_mul_le hp' |>.mpr (Nat.le_trans h_qp_bound h_tp_bound)
      have h_ceil_le : (t * p + p' - 1) / p' ≤ p - q := by omega
      have h_val_gap_le : xi - xj ≤ p - q := Nat.le_trans h_gap_upper h_ceil_le
      -- Now show circDist ≥ q (swapped min arguments)
      unfold circDist
      have hxi_xj_lt : xi - xj < p := by omega
      have hp_minus_lt : p - (xi - xj) < p := by omega
      have h_forward_zmod : ((xi : ZMod p) - (xj : ZMod p)).val = xi - xj := by
        have hle : xj ≤ xi := Nat.le_of_lt hxj_lt_xi
        have hxi_val : (xi : ZMod p).val = xi := ZMod.val_natCast_of_lt hxi_lt
        have hxj_val : (xj : ZMod p).val = xj := ZMod.val_natCast_of_lt hxj_lt
        have hle' : (xj : ZMod p).val ≤ (xi : ZMod p).val := by rw [hxj_val, hxi_val]; exact hle
        rw [ZMod.val_sub hle', hxi_val, hxj_val]
      have h_backward_zmod : ((xj : ZMod p) - (xi : ZMod p)).val = p - (xi - xj) := by
        have hle : xj ≤ xi := Nat.le_of_lt hxj_lt_xi
        have hxi_val : (xi : ZMod p).val = xi := ZMod.val_natCast_of_lt hxi_lt
        have hxj_val : (xj : ZMod p).val = xj := ZMod.val_natCast_of_lt hxj_lt
        rw [sub_eq_add_neg, ZMod.val_add, hxj_val]
        by_cases hxi0 : (xi : ZMod p) = 0
        · have hxi_zero : xi = 0 := by
            rw [ZMod.natCast_eq_zero_iff] at hxi0
            exact Nat.eq_zero_of_dvd_of_lt hxi0 hxi_lt
          simp [hxi_zero] at hxj_lt_xi
        · haveI : NeZero (xi : ZMod p) := ⟨hxi0⟩
          rw [ZMod.val_neg_of_ne_zero (xi : ZMod p), hxi_val]
          have heq : xj + (p - xi) = p - (xi - xj) := by omega
          rw [heq, Nat.mod_eq_of_lt hp_minus_lt]
      rw [h_forward_zmod, h_backward_zmod, min_comm]
      apply Nat.le_min.mpr
      exact ⟨h_val_gap_ge, by omega⟩

end Retraction

/-! ## Main Theorem -/

section MainTheorem

variable {p q p' q' : ℕ} [NeZero p] [NeZero p']

omit [NeZero p] [NeZero p'] in
/-- Translation invariance of circDist. -/
lemma circDist_add_right (i j δ : ZMod p) : circDist p (i + δ) (j + δ) = circDist p i j := by
  simp only [circDist]
  congr 1 <;> ring_nf

omit [NeZero p] in
/-- Vertex transitivity: K_{p/q} is vertex-transitive, so we can move any vertex to any other. -/
theorem vertex_transitive (x y : ZMod p) :
    ∃ (σ : ZMod p ≃ ZMod p),
      (∀ i j : ZMod p, (Kpq p q).Adj i j ↔ (Kpq p q).Adj (σ i) (σ j)) ∧
      σ x = y := by
  -- Translation by (y - x) is an automorphism of K_{p/q}
  let δ := y - x
  let σ : ZMod p ≃ ZMod p := {
    toFun := (· + δ)
    invFun := (· - δ)
    left_inv := fun z => by ring
    right_inv := fun z => by ring
  }
  use σ
  constructor
  · intro i j
    -- Translation preserves circDist: circDist (i + δ) (j + δ) = circDist i j
    simp only [Kpq]
    have h : circDist p (σ i) (σ j) = circDist p i j := circDist_add_right i j δ
    constructor
    · intro ⟨hne, hdist⟩
      refine ⟨fun heq => hne (add_right_cancel heq), ?_⟩
      rw [h]
      exact hdist
    · intro ⟨hne, hdist⟩
      refine ⟨fun heq => hne (congrArg σ heq), ?_⟩
      rw [h] at hdist
      exact hdist
  · change x + δ = y
    ring

omit [NeZero p'] in
/-- The winding set has exactly p' elements. -/
lemma windingSet_card (hp' : 0 < p') (hp'_lt : p' < p) (hbezout : p * q' - q * p' = 1) :
    (windingSet hp' : Finset (ZMod p)).card = p' := by
  rw [windingSet, Finset.card_image_of_injective]
  · exact Finset.card_fin p'
  · -- Injectivity: xSeq is strictly monotone, so injective
    intro i j heq
    have hi_lt := xSeq_lt_p hp' hp'_lt (Nat.pos_of_ne_zero (NeZero.ne p)) i
    have hj_lt := xSeq_lt_p hp' hp'_lt (Nat.pos_of_ne_zero (NeZero.ne p)) j
    have heq_val : xSeq p p' hp' i = xSeq p p' hp' j := by
      have h1 : (xSeq p p' hp' i : ZMod p).val = xSeq p p' hp' i := ZMod.val_natCast_of_lt hi_lt
      have h2 : (xSeq p p' hp' j : ZMod p).val = xSeq p p' hp' j := ZMod.val_natCast_of_lt hj_lt
      calc xSeq p p' hp' i = (xSeq p p' hp' i : ZMod p).val := h1.symm
        _ = (xSeq p p' hp' j : ZMod p).val := congrArg ZMod.val heq
        _ = xSeq p p' hp' j := h2
    -- xSeq is strictly monotone
    by_contra hne
    cases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with
    | inl hlt =>
      have := xSeq_strictMono hp' hp'_lt hbezout i j hlt
      omega
    | inr hgt =>
      have := xSeq_strictMono hp' hp'_lt hbezout j i hgt
      omega

omit [NeZero p'] in
/-- Since |windingSet| = p' < p, there exists an element not in the winding set. -/
lemma exists_outside_windingSet (hp' : 0 < p') (hp'_lt : p' < p) (hbezout : p * q' - q * p' = 1) :
    ∃ y : ZMod p, y ∉ windingSet hp' := by
  by_contra h
  push_neg at h
  have hcard := windingSet_card hp' hp'_lt hbezout
  have hfull : windingSet hp' = (Finset.univ : Finset (ZMod p)) := by
    apply Finset.eq_univ_of_forall
    exact h
  rw [hfull, Finset.card_univ, ZMod.card] at hcard
  omega

/-- The main theorem: For any vertex v, K_{p/q} - v is homomorphically equivalent to K_{p'/q'}.

    This means there exist maps f : ZMod p → ZMod p' and g : ZMod p' → ZMod p such that:
    1. f is a graph homomorphism from K_{p/q} - v to K_{p'/q'}
    2. g is a graph homomorphism from K_{p'/q'} to K_{p/q} - v -/
theorem lemma_6_6 (hp' : 0 < p') (hp'_lt : p' < p) (_hp_pos : 0 < p)
    (hq' : 0 < q') (hq'_lt : q' < q) (hq : 2 ≤ q) (h2q : 2 * q ≤ p)
    (hcoprime : Nat.Coprime p q) (hbezout : p * q' - q * p' = 1) (v : ZMod p) :
    ∃ (f : ZMod p → ZMod p') (g : ZMod p' → ZMod p),
      -- f is a homomorphism from K_{p/q} - v to K_{p'/q'}
      (∀ y y' : ZMod p, y ≠ v → y' ≠ v →
        (Kpq p q).Adj y y' → (Kpq p' q').Adj (f y) (f y')) ∧
      -- g is a homomorphism from K_{p'/q'} to K_{p/q} - v
      (∀ i j : ZMod p', (Kpq p' q').Adj i j →
        (Kpq p q).Adj (g i) (g j) ∧ g i ≠ v ∧ g j ≠ v) := by
  -- Key insight: we use q as the canonical point not in the winding set
  -- Shift by δ = v - q so that after translation, the removed vertex is q
  let δ := v - (q : ZMod p)
  -- Use the retraction as f and shifted embedding as g
  use fun y => ((retract hp' (y - δ)).val : ZMod p')
  use fun i => embed hp' ⟨i.val, ZMod.val_lt i⟩ + δ
  constructor
  · -- f preserves adjacency (retraction composed with translation)
    intro y y' hy hy' hadj
    -- Translation by -δ preserves adjacency
    have hadj' : (Kpq p q).Adj (y - δ) (y' - δ) := by
      have h := circDist_add_right (y - δ) (y' - δ) δ
      simp only [sub_add_cancel] at h
      unfold Kpq at hadj ⊢
      simp only [ne_eq] at hadj ⊢
      constructor
      · intro heq
        have : y = y' := by calc y = (y - δ) + δ := by ring
          _ = (y' - δ) + δ := by rw [heq]
          _ = y' := by ring
        exact hadj.1 this
      · rw [← h]; exact hadj.2
    -- y - δ ≠ q (since y ≠ v and δ = v - q)
    have hyd : y - δ ≠ (q : ZMod p) := by
      intro heq
      have h1 : y = (q : ZMod p) + δ := by calc y = (y - δ) + δ := by ring
        _ = (q : ZMod p) + δ := by rw [heq]
      have h2 : y = v := by
        calc y = (q : ZMod p) + δ := h1
          _ = (q : ZMod p) + (v - (q : ZMod p)) := rfl
          _ = v := by ring
      exact hy h2
    have hy'd : y' - δ ≠ (q : ZMod p) := by
      intro heq
      have h1 : y' = (q : ZMod p) + δ := by calc y' = (y' - δ) + δ := by ring
        _ = (q : ZMod p) + δ := by rw [heq]
      have h2 : y' = v := by
        calc y' = (q : ZMod p) + δ := h1
          _ = (q : ZMod p) + (v - (q : ZMod p)) := rfl
          _ = v := by ring
      exact hy' h2
    -- Apply retract_preserves_adj (which requires y - δ ≠ q and y' - δ ≠ q)
    exact retract_preserves_adj hp' hp'_lt hq' hq'_lt hq h2q hcoprime hbezout
      (y - δ) (y' - δ) hyd hy'd hadj'
  · -- g preserves adjacency and avoids v
    intro i j hadj
    constructor
    · -- Shifted embedding preserves adjacency
      have hembed := embed_preserves_adj hp' hp'_lt hq' hq'_lt h2q hbezout i j hadj
      -- Translation by δ preserves adjacency
      have h := circDist_add_right (embed hp' ⟨i.val, ZMod.val_lt i⟩)
                                   (embed hp' ⟨j.val, ZMod.val_lt j⟩) δ
      unfold Kpq at hembed ⊢
      simp only [ne_eq] at hembed ⊢
      constructor
      · intro heq
        have : embed hp' ⟨i.val, ZMod.val_lt i⟩ = embed hp' ⟨j.val, ZMod.val_lt j⟩ :=
          add_right_cancel heq
        exact hembed.1 this
      · rw [h]; exact hembed.2
    -- We use q_not_in_windingSet to show q ∉ windingSet
    have hq_not : (q : ZMod p) ∉ windingSet (p := p) hp' :=
      q_not_in_windingSet hp' hp'_lt hq' hq'_lt hq h2q hbezout
    constructor
    · -- embed i + δ ≠ v, i.e., embed i ≠ v - δ = q
      intro heq
      have : embed (p := p) hp' ⟨i.val, ZMod.val_lt i⟩ = (q : ZMod p) := by
        calc embed (p := p) hp' ⟨i.val, ZMod.val_lt i⟩
            = (embed (p := p) hp' ⟨i.val, ZMod.val_lt i⟩ + δ) - δ := by ring
          _ = v - δ := by rw [heq]
          _ = (q : ZMod p) := by simp only [δ]; ring
      -- But embed i is in the winding set, and q is not
      have hin : embed (p := p) hp' ⟨i.val, ZMod.val_lt i⟩ ∈ windingSet (p := p) hp' := by
        simp only [windingSet, embed, Finset.mem_image]
        exact ⟨⟨i.val, ZMod.val_lt i⟩, Finset.mem_univ _, rfl⟩
      rw [this] at hin
      exact hq_not hin
    · -- embed j + δ ≠ v (same argument)
      intro heq
      have : embed (p := p) hp' ⟨j.val, ZMod.val_lt j⟩ = (q : ZMod p) := by
        calc embed (p := p) hp' ⟨j.val, ZMod.val_lt j⟩
            = (embed (p := p) hp' ⟨j.val, ZMod.val_lt j⟩ + δ) - δ := by ring
          _ = v - δ := by rw [heq]
          _ = (q : ZMod p) := by simp only [δ]; ring
      have hin : embed (p := p) hp' ⟨j.val, ZMod.val_lt j⟩ ∈ windingSet (p := p) hp' := by
        simp only [windingSet, embed, Finset.mem_image]
        exact ⟨⟨j.val, ZMod.val_lt j⟩, Finset.mem_univ _, rfl⟩
      rw [this] at hin
      exact hq_not hin

end MainTheorem

end Lemma66

/-! ## Connection to fractionGraph

The `Kpq` in Lemma66 is the complement of `fractionGraph`:
- `Kpq`: Adj x y ↔ x ≠ y ∧ circDist(x,y) ≥ q  (edge when far apart)
- `fractionGraph`: Adj x y ↔ x ≠ y ∧ distMod(x,y) < q  (edge when close)

A homomorphism Kpq → Kp'q' preserves "far-apart" edges, which means it preserves
"close" non-edges, i.e., it's a cohomomorphism for fractionGraph.
-/

section FractionGraphConnection

open Lemma66 FractionGraphBasic

variable {p q p' q' : ℕ} [NeZero p] [NeZero p']

/-- The circular distance functions are equal. -/
lemma circDist_eq_distMod (a b : ZMod p) : Lemma66.circDist p a b = distMod p a b := by
  unfold Lemma66.circDist distMod
  -- (b - a).val and (a - b).val sum to p (when a ≠ b) or are both 0 (when a = b)
  by_cases hab : a = b
  · simp [hab]
  · have h : (b - a).val + (a - b).val = p := by
      have h1 : (b - a) + (a - b) = 0 := by ring
      have h2 : ((b - a) + (a - b)).val = 0 := by simp [h1]
      have hne : (b - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
      have hval_pos : 0 < (b - a).val := Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero _).mp hne)
      have hval_lt : (b - a).val < p := ZMod.val_lt (b - a)
      rw [ZMod.val_add] at h2
      have := Nat.dvd_of_mod_eq_zero h2
      rcases this with ⟨k, hk⟩
      -- hk : (b - a).val + (a - b).val = p * k
      have hk_pos : k > 0 := by
        by_contra hle
        push_neg at hle
        interval_cases k
        have hba0 : (b - a).val = 0 := by omega
        rw [ZMod.val_eq_zero] at hba0; exact hne hba0
      have hk_le1 : k ≤ 1 := by
        by_contra hgt
        push_neg at hgt
        have : (b - a).val + (a - b).val ≥ 2 * p := by
          calc (b - a).val + (a - b).val = p * k := hk
            _ ≥ p * 2 := Nat.mul_le_mul_left p hgt
            _ = 2 * p := by ring
        have h1 : (b - a).val < p := ZMod.val_lt _
        have h2 : (a - b).val < p := ZMod.val_lt _
        omega
      interval_cases k
      omega
    rw [min_comm]
    congr 1
    omega

/-- Kpq is the complement of fractionGraph (in terms of adjacency). -/
lemma Kpq_adj_iff_not_fractionGraph_adj (x y : ZMod p) (hne : x ≠ y) :
    (Lemma66.Kpq p q).Adj x y ↔ ¬(fractionGraph p q).Adj x y := by
  simp only [Lemma66.Kpq, fractionGraph]
  constructor
  · intro ⟨_, hdist⟩ ⟨_, hdist'⟩
    rw [circDist_eq_distMod] at hdist
    omega
  · intro hnadj
    push_neg at hnadj
    constructor
    · exact hne
    · rw [circDist_eq_distMod]
      exact hnadj hne

/-- A Kpq-homomorphism is a fractionGraph-cohomomorphism.
    This is because Kpq = fractionGraphᶜ, so preserving Kpq edges = preserving fractionGraph non-edges. -/
lemma Kpq_hom_is_fractionGraph_cohom (f : ZMod p → ZMod p')
    (hf : ∀ x y, (Lemma66.Kpq p q).Adj x y → (Lemma66.Kpq p' q').Adj (f x) (f y)) :
    ∀ x y, x ≠ y → ¬(fractionGraph p q).Adj x y → ¬(fractionGraph p' q').Adj (f x) (f y) := by
  intro x y hne hnadj
  -- x ≠ y and ¬fractionGraph.Adj x y means Kpq.Adj x y
  have hadj : (Lemma66.Kpq p q).Adj x y := (Kpq_adj_iff_not_fractionGraph_adj x y hne).mpr hnadj
  have hadj' := hf x y hadj
  -- Kpq.Adj (f x) (f y) means ¬fractionGraph.Adj (f x) (f y)
  have hne' : f x ≠ f y := by
    intro heq
    unfold Lemma66.Kpq at hadj'
    exact hadj'.1 heq
  exact (Kpq_adj_iff_not_fractionGraph_adj (f x) (f y) hne').mp hadj'

/-- Main connection: Lemma 6.6 gives cohomomorphisms for fractionGraph.

    From `lemma_6_6`, we get:
    - f : ZMod p → ZMod p' preserving Kpq-adjacency (= fractionGraph non-adjacency)
    - g : ZMod p' → ZMod p preserving Kpq-adjacency (= fractionGraph non-adjacency)

    This gives bidirectional cohomomorphisms between fractionGraph(p,q) - v and fractionGraph(p',q'). -/
theorem fractionGraph_remove_vertex_cohoms (hp' : 0 < p') (hp'_lt : p' < p)
    (hq' : 0 < q') (hq'_lt : q' < q) (hq : 2 ≤ q) (h2q : 2 * q ≤ p)
    (hcoprime : Nat.Coprime p q) (hbezout : p * q' - q * p' = 1) (v : ZMod p) :
    -- Cohomomorphism from (fractionGraph p q).induce {x | x ≠ v} to fractionGraph p' q'
    (∃ f : ZMod p → ZMod p',
      ∀ y y' : ZMod p, y ≠ v → y' ≠ v → y ≠ y' →
        ¬(fractionGraph p q).Adj y y' → ¬(fractionGraph p' q').Adj (f y) (f y')) ∧
    -- Cohomomorphism from fractionGraph p' q' to (fractionGraph p q).induce {x | x ≠ v}
    (∃ g : ZMod p' → ZMod p,
      (∀ i j : ZMod p', i ≠ j →
        ¬(fractionGraph p' q').Adj i j → ¬(fractionGraph p q).Adj (g i) (g j)) ∧
      (∀ i : ZMod p', g i ≠ v)) := by
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨f, g, hf, hg⟩ := lemma_6_6 hp' hp'_lt hp_pos hq' hq'_lt hq h2q hcoprime hbezout v
  constructor
  · -- Forward direction: f is a cohomomorphism
    use f
    intro y y' hy hy' hne hnadj
    have hadj : (Lemma66.Kpq p q).Adj y y' := (Kpq_adj_iff_not_fractionGraph_adj y y' hne).mpr hnadj
    have hadj' := hf y y' hy hy' hadj
    have hne' : f y ≠ f y' := by
      unfold Lemma66.Kpq at hadj'
      exact hadj'.1
    exact (Kpq_adj_iff_not_fractionGraph_adj (f y) (f y') hne').mp hadj'
  · -- Backward direction: g is a cohomomorphism and avoids v
    use g
    constructor
    · intro i j hne hnadj
      have hadj : (Lemma66.Kpq p' q').Adj i j := (Kpq_adj_iff_not_fractionGraph_adj i j hne).mpr hnadj
      obtain ⟨hadj', _, _⟩ := hg i j hadj
      have hne' : g i ≠ g j := by
        unfold Lemma66.Kpq at hadj'
        exact hadj'.1
      exact (Kpq_adj_iff_not_fractionGraph_adj (g i) (g j) hne').mp hadj'
    · intro i
      -- Need to show g i ≠ v for all i
      -- Strategy: find an adjacent pair involving i in Kpq(p',q')
      -- Then use hg to conclude g i ≠ v
      -- For any i, we can find k = i + q' such that circDist(i, k) ≥ q'
      -- The key is that 2 * q' ≤ p' (derived from Bezout conditions)
      have hp'_ge2 : 2 ≤ p' := by
        -- If p' = 1 then from Bezout: p * q' = q + 1, but p ≥ 4 and q' ≥ 1
        -- gives p * q' ≥ 4 > q + 1 for small q, contradicting q' ≥ 1.
        by_contra hp'_lt2
        push_neg at hp'_lt2
        have hp'_eq_1 : p' = 1 := by omega
        -- p' = 1: From hbezout: p * q' - q * 1 = 1, so p * q' = q + 1
        rw [hp'_eq_1] at hbezout
        have hpq' : p * q' = q + 1 := by omega
        have hp_ge4 : p ≥ 4 := by omega
        -- From p * q' = q + 1 and p ≥ 4, we get q' ≤ (q + 1) / 4
        -- We also have q' ≥ 1 (from hq') and q' < q (from hq'_lt)
        -- Case q = 2: p = 4 (from 2q ≤ p and p * q' = 3), but 4 * q' = 3 has no nat solution
        -- Case q ≥ 3: p * q' = q + 1 ≤ q + q = 2q ≤ p, so q' ≤ 1, thus q' = 1
        --   Then p = q + 1 < 2q (for q ≥ 2), contradicting p ≥ 2q
        -- In all cases, contradiction.
        have hq'_eq_1 : q' = 1 := by
          have hq'_le_1 : q' ≤ 1 := by
            have hle : p * q' ≤ p * 1 := by
              calc p * q' = q + 1 := hpq'
                _ ≤ q + q := by omega
                _ = 2 * q := by ring
                _ ≤ p := h2q
                _ = p * 1 := by ring
            exact Nat.le_of_mul_le_mul_left hle (by omega : 0 < p)
          omega
        have hp_eq : p = q + 1 := by
          rw [hq'_eq_1] at hpq'
          omega
        -- But p ≥ 2q ≥ 4 and p = q + 1, so q + 1 ≥ 2q, i.e., 1 ≥ q, contradiction with q ≥ 2
        omega
      -- Now we can find an adjacent pair for any i
      have hq'_lt_p' : q' < p' := q'_lt_p'_of_bezout hp' hp'_ge2 hq' hq'_lt (by omega) (by omega) hbezout
      -- Pick k = i + q', then circDist(i, k) = min(q', p' - q') ≥ q' (since p' - q' ≥ q')
      let k : ZMod p' := i + q'
      have hik : i ≠ k := by
        intro heq
        have : (q' : ZMod p') = 0 := by
          calc (q' : ZMod p') = (i + q') - i := by ring
            _ = k - i := rfl
            _ = i - i := by rw [← heq]
            _ = 0 := by ring
        have hdvd : p' ∣ q' := CharP.cast_eq_zero_iff (ZMod p') p' q' |>.mp this
        have : q' ≥ p' := Nat.le_of_dvd hq' hdvd
        omega
      have hadj_ik : (Lemma66.Kpq p' q').Adj i k := by
        unfold Lemma66.Kpq
        constructor
        · exact hik
        · unfold Lemma66.circDist
          have hk_sub_i : (k - i).val = q' := by
            simp only [k]
            have : (i + q' - i : ZMod p') = q' := by ring
            rw [this]
            exact ZMod.val_natCast_of_lt hq'_lt_p'
          have hi_sub_k : (i - k).val = p' - q' := by
            simp only [k]
            -- i - (i + q') = -q' in ZMod p'
            have heq : i - (i + ↑q') = (-(q' : ZMod p')) := by ring
            rw [heq]
            -- (-q').val = p' - q'.val when q' ≠ 0 and q' < p'
            have hq'_ne_zero : (q' : ZMod p') ≠ 0 := by
              intro h
              have hdvd : p' ∣ q' := CharP.cast_eq_zero_iff (ZMod p') p' q' |>.mp h
              have : q' ≥ p' := Nat.le_of_dvd hq' hdvd
              omega
            rw [ZMod.neg_val]
            simp only [hq'_ne_zero, ↓reduceIte]
            rw [ZMod.val_natCast_of_lt hq'_lt_p']
          simp only [hk_sub_i, hi_sub_k]
          -- Need to show min(q', p' - q') ≥ q', i.e., p' - q' ≥ q', i.e., 2 * q' ≤ p'
          -- This follows from the Bezout relation: (p/q, p'/q') are Stern-Brocot neighbors
          -- with 2q ≤ p implies 2q' ≤ p' for the predecessor
          have h2q'_le_p' : 2 * q' ≤ p' :=
            two_q'_le_p'_of_bezout hp' hp'_ge2 hq' hq'_lt hq h2q hbezout
          exact Nat.le_min.mpr ⟨le_refl q', by omega⟩
      exact (hg i k hadj_ik).2.1

end FractionGraphConnection
