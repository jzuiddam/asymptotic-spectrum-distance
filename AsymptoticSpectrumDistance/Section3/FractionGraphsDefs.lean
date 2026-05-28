/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section2.Basic
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.FractionalCliqueCover
import AsymptoticSpectrumDistance.Prerequisites.FractionGraph
import AsymptoticSpectrumDistance.Prerequisites.FractionalCliqueCoverVertexTransitive
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

set_option linter.style.emptyLine false

/-!
# Fraction Graphs for Asymptotic Spectrum Distance

This file develops the theory of fraction graphs E_{p/q} needed for the
asymptotic spectrum distance paper.

## Main definitions

* `FractionGraph p q` : E_{p/q} as a bundled Graph

## Main results

* `fractionGraph_ordering` : E_{p/q} ≤ E_{r/s} ↔ p/q ≤ r/s
* `fractionGraph_chiBar_f` : χ̄_f(E_{p/q}) = p/q

## References

* [Hell-Nešetřil] Graphs and Homomorphisms, Section 6
* [de Boer, Buys, Zuiddam] Section 3.1
-/

namespace AsymptoticSpectrumDistance

open AsymptoticSpectrumGraphs SimpleGraph FractionGraphBasic

/-! ### Fraction Graph as Bundled Graph -/

/-- The fraction graph E_{p/q} as a bundled Graph. -/
def FractionGraph (p : ℕ+) (q : ℕ) : Graph where
  V := ZMod p
  graph := fractionGraph p q

/-- Convenience: FractionGraph from ℕ with NeZero instance. -/
abbrev FractionGraph' (p q : ℕ) [NeZero p] : Graph :=
  FractionGraph ⟨p, NeZero.pos p⟩ q

notation:max "E[" p "/" q "]ᴳ" => FractionGraph p q

/-! ### Fraction Graph Ordering -/

/-- Cohomomorphism between fraction graphs implies rational ordering.
    This is the converse direction of Lemma 3.2.

    The proof uses: cohomomorphism implies χ̄_f(E_{p/q}) ≤ χ̄_f(E_{r/s}),
    and since χ̄_f(E_{p/q}) = p/q, we get p/q ≤ r/s. -/
theorem fractionGraph_ordering_reverse (p q r s : ℕ) [NeZero p] [NeZero r]
    (hq : 0 < q) (hs : 0 < s) (h2q : 2 * q ≤ p) (h2s : 2 * s ≤ r) :
    Cohom (fractionGraph p q) (fractionGraph r s) → (p : ℚ) / q ≤ (r : ℚ) / s := by
  intro ⟨f, hf⟩
  -- By monotonicity of χ̄_f under cohomomorphisms
  have hmono := fractionalCliqueCoverNumber_cohom_mono (fractionGraph p q) (fractionGraph r s) f hf
  -- For vertex-transitive graphs, χ̄_f = formula = |V|/ω
  have hvt_pq := FractionGraphBasic.fractionGraph_vertexTransitive p q
  have hvt_rs := FractionGraphBasic.fractionGraph_vertexTransitive r s
  have heq_pq := Universality.fractionalCliqueCoverNumber_eq_formula_vertexTransitive
    (fractionGraph p q) hvt_pq
  have heq_rs := Universality.fractionalCliqueCoverNumber_eq_formula_vertexTransitive
    (fractionGraph r s) hvt_rs
  -- The formula for fraction graphs gives p/q and r/s
  have hform_pq := fractionalCliqueCoverNumber_fractionGraph p q hq h2q
  have hform_rs := fractionalCliqueCoverNumber_fractionGraph r s hs h2s
  -- Chain: p/q = χ̄_f(E_{p/q}) ≤ χ̄_f(E_{r/s}) = r/s
  have hle : (p : ℝ) / q ≤ (r : ℝ) / s := by
    calc (p : ℝ) / q
        = fractionalCliqueCoverNumber_formula (fractionGraph p q) := hform_pq.symm
      _ = fractionalCliqueCoverNumber (fractionGraph p q) := heq_pq.symm
      _ ≤ fractionalCliqueCoverNumber (fractionGraph r s) := hmono
      _ = fractionalCliqueCoverNumber_formula (fractionGraph r s) := heq_rs
      _ = (r : ℝ) / s := hform_rs
  -- Convert from ℝ to ℚ
  have hq_pos : (0 : ℚ) < q := Nat.cast_pos.mpr hq
  have hs_pos : (0 : ℚ) < s := Nat.cast_pos.mpr hs
  have hq_pos_r : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hs_pos_r : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  rw [div_le_div_iff₀ hq_pos hs_pos]
  -- From hle : (p : ℝ) / q ≤ (r : ℝ) / s, derive p * s ≤ r * q
  have hle_mul : (p : ℝ) * s ≤ (r : ℝ) * q := by
    have h := (div_le_div_iff₀ hq_pos_r hs_pos_r).mp hle
    linarith
  -- Convert from ℝ to ℚ via ℕ
  have hle_nat : p * s ≤ r * q := by
    have h : (↑(p * s) : ℝ) ≤ ↑(r * q) := by push_cast; exact hle_mul
    exact Nat.cast_le.mp h
  exact_mod_cast hle_nat

/-- Fraction graphs are ordered as rational numbers under cohomomorphism.
    Lemma 3.2: p/q ≤ r/s iff E_{p/q} ≤ E_{r/s}.
    Requires 2q ≤ p and 2s ≤ r for proper fraction graphs. -/
theorem fractionGraph_ordering (p q r s : ℕ) [NeZero p] [NeZero r]
    (hq : 0 < q) (hs : 0 < s) (h2q : 2 * q ≤ p) (h2s : 2 * s ≤ r) :
    (p : ℚ) / q ≤ (r : ℚ) / s ↔ Cohom (fractionGraph p q) (fractionGraph r s) :=
  ⟨fractionGraph_cohomomorphism p q r s hq, fractionGraph_ordering_reverse p q r s hq hs h2q h2s⟩

/-- The floor map for fraction graphs equals the natural division map. -/
lemma floor_map_eq_nat_div (x r p : ℕ) :
    ⌊(x : ℚ) * r / p⌋.toNat = x * r / p := by
  have h : (x : ℚ) * r / p = ((x * r : ℕ) : ℚ) / p := by simp only [Nat.cast_mul]
  rw [h, Int.floor_toNat, Rat.natFloor_natCast_div_natCast]

/-- The floor map equals the scaling map (natural division map). -/
theorem floor_map_eq_scalingMap (p r : ℕ) [NeZero p] [NeZero r] (x : ZMod p) :
    (⌊(x.val : ℚ) * r / p⌋.toNat : ZMod r) = fractionGraph_scalingMap p r x := by
  simp only [fractionGraph_scalingMap, floor_map_eq_nat_div]

/-- The cohomomorphism map for fraction graphs is the floor map.

    The proof uses:
    1. The floor map ⌊x·r/p⌋ equals x·r/p (natural division) by `floor_map_eq_nat_div`
    2. The natural division map is `fractionGraph_scalingMap` by `floor_map_eq_scalingMap`
    3. `fractionGraph_scalingMap_isCohom` proves IsCohom for fractionGraph_scalingMap -/
theorem fractionGraph_cohom_map (p q r s : ℕ) [NeZero p] [NeZero r]
    (hq : 0 < q) (hle : (p : ℚ) / q ≤ (r : ℚ) / s) :
    let f : ZMod p → ZMod r := fun x =>
      (⌊(x.val : ℚ) * r / p⌋.toNat : ZMod r)
    IsCohom (fractionGraph p q) (fractionGraph r s) f := by
  intro f u v huv hnadj
  have hf_eq : ∀ x, f x = fractionGraph_scalingMap p r x := floor_map_eq_scalingMap p r
  simp only [hf_eq]
  exact fractionGraph_scalingMap_isCohom p q r s hq hle u v huv hnadj

/-! ### Fractional Clique Covering Number -/

/-- The fractional clique covering number of E_{p/q} is at most p/q.
    Lemma 3.3: χ̄_f(E_{p/q}) ≤ p/q.

    This follows from `fractionalCliqueCover_fractionGraph` in ShannonCapacity. -/
theorem fractionGraph_chiBar_f (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    ∃ (cliques : Finset (Finset (ZMod p))) (weights : Finset (ZMod p) → ℝ),
      (∀ C ∈ cliques, (fractionGraph p q).IsClique C) ∧
      (∀ C ∈ cliques, weights C ≥ 0) ∧
      (∀ v : ZMod p, (cliques.filter (v ∈ ·)).sum weights ≥ 1) ∧
      cliques.sum weights ≤ (p : ℝ) / q :=
  FractionGraphBasic.fractionalCliqueCover_fractionGraph p q hq h2q

/-! ### Vertex Removal Strategy -/

/-- For coprime p, q with p > q ≥ 2, the Stern-Brocot predecessor exists.

    The Stern-Brocot predecessor p'/q' satisfies:
    - 0 < p' < p, 0 < q' < q
    - pq' - qp' = 1

    Proof:
    1. Let q' = ((p : ZMod q)⁻¹).val (the multiplicative inverse of p mod q)
    2. Since gcd(p, q) = 1, we have p is a unit in ZMod q
    3. Key equation: (p * q') % q = 1 (from ZMod.mul_val_inv)
    4. Define p' = (p * q' - 1) / q
    5. Then p * q' = 1 + q * p', so p * q' - q * p' = 1
    6. Bounds: 0 < q' < q (from ZMod.val_lt and IsUnit)
              0 < p' (since p * q' ≥ p > q, so p * q' - 1 ≥ q)
              p' < p (since q' < q, so p * q' < p * q)

    Note: Requires q ≥ 2 since for q = 1 there's no q' with 0 < q' < 1. -/
theorem sternBrocotPredecessor_exists (p q : ℕ) (hp : 0 < p) (hq : 2 ≤ q)
    (hcoprime : Nat.Coprime p q) (hpq : q < p) :
    ∃ p' q' : ℕ, 0 < p' ∧ p' < p ∧ 0 < q' ∧ q' < q ∧ p * q' - q * p' = 1 := by
  haveI hqne : NeZero q := ⟨by omega⟩
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hq_pos : 0 < q := by omega
  -- Define q' as the multiplicative inverse of p mod q
  set q' := ((p : ZMod q)⁻¹).val with hq'_def
  -- Key property: p * q' ≡ 1 (mod q) from ZMod.mul_val_inv
  have hmul : (p : ZMod q) * q' = 1 := ZMod.mul_val_inv hcoprime
  -- Convert to: (p * q') % q = 1
  have hpq'_mod : (p * q') % q = 1 := by
    have h : ((p * q' : ℕ) : ZMod q) = 1 := by simp only [Nat.cast_mul, hmul]
    have hval : ((p * q' : ℕ) : ZMod q).val = (1 : ZMod q).val := congrArg ZMod.val h
    rw [ZMod.val_natCast] at hval
    have hone : (1 : ZMod q).val = 1 := ZMod.val_one (n := q)
    rw [hone] at hval
    exact hval
  -- q' is positive since (p : ZMod q) is a unit (by coprimality)
  have hq'_pos : 0 < q' := by
    by_contra hq'_zero
    push_neg at hq'_zero
    have hq'_eq : q' = 0 := Nat.le_zero.mp hq'_zero
    -- If q' = 0, then p * q' = 0, contradicting p * q' ≡ 1 (mod q)
    have hcontra : (p : ZMod q) * q' = 0 := by simp [hq'_eq]
    rw [hmul] at hcontra
    exact one_ne_zero hcontra
  -- q' < q from ZMod.val_lt
  have hq'_lt : q' < q := ZMod.val_lt _
  -- p * q' ≥ 1
  have hpq'_ge_1 : p * q' ≥ 1 := by
    have := Nat.mul_pos hp hq'_pos
    omega
  -- q ∣ (p * q' - 1)
  have hdiv : q ∣ p * q' - 1 := by
    -- From (p * q') % q = 1 and p * q' ≥ 1, we get (p * q' - 1) % q = 0
    -- Use: (a - b) % n = 0 iff a % n = b % n (when b ≤ a)
    have hone_lt_q : 1 < q := by omega
    have hone_mod : 1 % q = 1 := Nat.mod_eq_of_lt hone_lt_q
    rw [Nat.dvd_iff_mod_eq_zero]
    have : p * q' % q = 1 % q := by rw [hpq'_mod, hone_mod]
    exact Nat.sub_mod_eq_zero_of_mod_eq this
  -- Define p' = (p * q' - 1) / q
  set p' := (p * q' - 1) / q with hp'_def
  -- p * q' ≥ p since q' ≥ 1
  have hpq'_ge_p : p * q' ≥ p := Nat.le_mul_of_pos_right p hq'_pos
  -- p * q' > q since p > q
  have hpq'_gt_q : p * q' > q := Nat.lt_of_lt_of_le hpq hpq'_ge_p
  -- p * q' - 1 ≥ q
  have hpq'_sub_ge : p * q' - 1 ≥ q := Nat.le_sub_one_of_lt hpq'_gt_q
  -- p' > 0
  have hp'_pos : 0 < p' := Nat.div_pos hpq'_sub_ge hq_pos
  -- p * q' < p * q since q' < q
  have hpq'_lt_pq : p * q' < p * q := Nat.mul_lt_mul_of_pos_left hq'_lt hp
  -- p * q' - 1 < p * q
  have hpq'_sub_lt : p * q' - 1 < p * q := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpq'_lt_pq
  -- p' < p
  have hp'_lt : p' < p := by
    have hdvd : q ∣ p * q := dvd_mul_left q p
    calc p' = (p * q' - 1) / q := rfl
      _ < (p * q) / q := Nat.div_lt_div_of_lt_of_dvd hdvd hpq'_sub_lt
      _ = p := Nat.mul_div_cancel p hq_pos
  -- Main equation: p * q' - q * p' = 1
  have heq : p * q' - q * p' = 1 := by
    -- From hdiv: q ∣ p * q' - 1, so p * q' - 1 = ((p * q' - 1) / q) * q = p' * q
    have h3 : p * q' - 1 = p' * q := (Nat.div_mul_cancel hdiv).symm
    -- So p * q' = p' * q + 1
    have hpq'_eq : p * q' = p' * q + 1 := by
      have hge : p * q' ≥ 1 := hpq'_ge_1
      omega
    -- Therefore p * q' - q * p' = p * q' - p' * q = 1
    have h4 : q * p' = p' * q := by ring
    rw [h4]
    omega
  exact ⟨p', q', hp'_pos, hp'_lt, hq'_pos, hq'_lt, heq⟩

/-- For coprime p, q with p/q ≥ 2, the unique p', q' with 0 < p' < p, 0 < q' < q
    and pq' - qp' = 1 exist. This gives the Stern-Brocot predecessor.

    Note: This is a noncomputable definition that uses choice.
    Requires q ≥ 2 since for q = 1 there's no valid predecessor. -/
noncomputable def sternBrocotPredecessor (p q : ℕ) (hp : 0 < p) (hq : 2 ≤ q)
    (hcoprime : Nat.Coprime p q) (hpq : q < p) :
    { pq' : ℕ × ℕ // 0 < pq'.1 ∧ pq'.1 < p ∧ 0 < pq'.2 ∧ pq'.2 < q ∧
                     p * pq'.2 - q * pq'.1 = 1 } := by
  have h := sternBrocotPredecessor_exists p q hp hq hcoprime hpq
  choose p' q' hp'_pos hp'_lt hq'_pos hq'_lt heq using h
  exact ⟨(p', q'), hp'_pos, hp'_lt, hq'_pos, hq'_lt, heq⟩

/-- The Stern-Brocot predecessor is unique: if two pairs (p₁', q₁') and (p₂', q₂')
    both satisfy 0 < p' < p, 0 < q' < q, and p*q' - q*p' = 1, then they are equal.

    Proof: From p*q₁' - q*p₁' = 1 and p*q₂' - q*p₂' = 1:
    p*(q₁' - q₂') = q*(p₁' - p₂')
    Since gcd(p,q) = 1, we have q | (q₁' - q₂') and p | (p₁' - p₂').
    But |q₁' - q₂'| < q and |p₁' - p₂'| < p, so q₁' = q₂' and p₁' = p₂'. -/
theorem sternBrocotPredecessor_unique (p q p₁' q₁' p₂' q₂' : ℕ)
    (hcoprime : Nat.Coprime p q)
    (hp₁'_pos : 0 < p₁') (hp₁'_lt : p₁' < p) (hq₁'_pos : 0 < q₁') (hq₁'_lt : q₁' < q)
    (_hp₂'_pos : 0 < p₂') (_hp₂'_lt : p₂' < p) (hq₂'_pos : 0 < q₂') (hq₂'_lt : q₂' < q)
    (heq₁ : p * q₁' - q * p₁' = 1) (heq₂ : p * q₂' - q * p₂' = 1) :
    p₁' = p₂' ∧ q₁' = q₂' := by
  -- From the equations: p * q₁' = q * p₁' + 1 and p * q₂' = q * p₂' + 1
  have h1 : p * q₁' = q * p₁' + 1 := by omega
  have h2 : p * q₂' = q * p₂' + 1 := by omega
  have hq_pos : 0 < q := Nat.lt_trans hq₁'_pos hq₁'_lt
  have hp_pos : 0 < p := Nat.lt_trans hp₁'_pos hp₁'_lt
  -- First prove q₁' = q₂' by showing q divides their difference
  have hq_eq : q₁' = q₂' := by
    by_contra hne
    -- Assume q₁' ≠ q₂' and derive contradiction
    have h_cases : q₁' < q₂' ∨ q₂' < q₁' := Nat.lt_or_lt_of_ne hne
    rcases h_cases with hlt | hlt
    · -- Case q₁' < q₂'
      have hp₁_lt_p₂ : p₁' < p₂' := by
        by_contra h
        push_neg at h
        have hpq_le : p * q₁' ≥ p * q₂' := by
          calc p * q₁' = q * p₁' + 1 := h1
            _ ≥ q * p₂' + 1 := by nlinarith
            _ = p * q₂' := h2.symm
        have : q₁' ≥ q₂' := Nat.le_of_mul_le_mul_left hpq_le hp_pos
        omega
      have h_diff : p * q₂' - p * q₁' = q * p₂' - q * p₁' := by omega
      have heq_diff : p * (q₂' - q₁') = q * (p₂' - p₁') := by
        rw [← Nat.mul_sub p q₂' q₁', ← Nat.mul_sub q p₂' p₁'] at h_diff
        exact h_diff
      have hdiv_q : q ∣ q₂' - q₁' := by
        have hdiv : q ∣ q * (p₂' - p₁') := dvd_mul_right q _
        rw [← heq_diff] at hdiv
        exact hcoprime.symm.dvd_of_dvd_mul_left hdiv
      have hq_diff_pos : 0 < q₂' - q₁' := Nat.sub_pos_of_lt hlt
      have hge_q : q ≤ q₂' - q₁' := Nat.le_of_dvd hq_diff_pos hdiv_q
      omega
    · -- Case q₂' < q₁' (symmetric)
      have hp₂_lt_p₁ : p₂' < p₁' := by
        by_contra h
        push_neg at h
        have hpq_le : p * q₂' ≥ p * q₁' := by
          calc p * q₂' = q * p₂' + 1 := h2
            _ ≥ q * p₁' + 1 := by nlinarith
            _ = p * q₁' := h1.symm
        have : q₂' ≥ q₁' := Nat.le_of_mul_le_mul_left hpq_le hp_pos
        omega
      have h_diff : p * q₁' - p * q₂' = q * p₁' - q * p₂' := by omega
      have heq_diff : p * (q₁' - q₂') = q * (p₁' - p₂') := by
        rw [← Nat.mul_sub p q₁' q₂', ← Nat.mul_sub q p₁' p₂'] at h_diff
        exact h_diff
      have hdiv_q : q ∣ q₁' - q₂' := by
        have hdiv : q ∣ q * (p₁' - p₂') := dvd_mul_right q _
        rw [← heq_diff] at hdiv
        exact hcoprime.symm.dvd_of_dvd_mul_left hdiv
      have hq_diff_pos : 0 < q₁' - q₂' := Nat.sub_pos_of_lt hlt
      have hge_q : q ≤ q₁' - q₂' := Nat.le_of_dvd hq_diff_pos hdiv_q
      omega
  -- Now derive p₁' = p₂' from q₁' = q₂'
  have hp_eq : p₁' = p₂' := by
    have h_pq : p * q₁' = p * q₂' := by rw [hq_eq]
    have h_qp : q * p₁' + 1 = q * p₂' + 1 := by rw [← h1, ← h2, h_pq]
    have h_qp' : q * p₁' = q * p₂' := by omega
    exact Nat.eq_of_mul_eq_mul_left hq_pos h_qp'
  exact ⟨hp_eq, hq_eq⟩

/-! ### Vertex Removal: The Winding Subset Construction

The proof of Lemma 6.6 (Hell-Nešetřil) uses a "winding subset" X ⊂ ZMod p
with |X| = p' elements that is isomorphic to ZMod p' as a graph.

Given coprime p, q with pq' - qp' = 1, the subset X consists of vertices
that "wind around" the circle q' times when enumerated by the map k ↦ kq + 1.

Reference: Hell & Nešetřil, "Graphs and Homomorphisms" (2004), Lemma 6.6. -/

/-- The winding subset X for the vertex removal construction.
    X = {0} ∪ {kq + 1 mod p : k = 1, ..., p'-1}

    This set has exactly p' elements and induces a subgraph isomorphic to E_{p'/q'}. -/
def windingSubset (p q p' : ℕ) [NeZero p] : Finset (ZMod p) :=
  (Finset.range p').image (fun k => if k = 0 then 0 else (k * q + 1 : ℕ))

/-- Helper: the winding function that maps k to the k-th element of X. -/
def windingFn (p q : ℕ) (k : ℕ) : ZMod p :=
  if k = 0 then 0 else (k * q + 1 : ℕ)

/-- Key lemma: q^{-1} ≡ p - p' (mod p) when pq' - qp' = 1.
    From the Bezout identity pq' = qp' + 1, we get q(p - p') ≡ 1 (mod p).

    Proof: q * (p - p') = q*p - q*p' = q*p - (p*q' - 1) = p*(q - q') + 1 ≡ 1 (mod p). -/
lemma q_inv_eq_p_minus_p' (p q p' q' : ℕ) [hp : NeZero p]
    (hcoprime : Nat.Coprime p q) (_hp'_pos : 0 < p') (hp'_lt : p' < p)
    (hq'_pos : 0 < q') (hq'_lt : q' < q) (hbezout : p * q' - q * p' = 1) :
    (q : ZMod p)⁻¹ = (p - p' : ℕ) := by
  have hp_pos : 0 < p := NeZero.pos p
  have heq : p * q' = q * p' + 1 := by omega
  -- Show q * (p - p') ≡ 1 (mod p)
  have hqinv : (q : ZMod p) * (p - p' : ℕ) = 1 := by
    have hp'_le : p' ≤ p := hp'_lt.le
    have hq'_le_q : q' ≤ q := hq'_lt.le
    -- Key: q * p' + 1 = p * q', so q * p' = p * q' - 1
    have hqp'_lt : q * p' < q * p := Nat.mul_lt_mul_of_pos_left hp'_lt (by omega : 0 < q)
    have hpq'_le_qp : p * q' ≤ q * p := by nlinarith
    -- Work in ZMod p directly
    have h1 : ((q * (p - p') : ℕ) : ZMod p) = ((q * p - q * p' : ℕ) : ZMod p) := by
      congr 1; exact Nat.mul_sub q p p'
    have h2 : ((q * p - q * p' : ℕ) : ZMod p) =
        ((q * p : ℕ) : ZMod p) - ((q * p' : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (le_of_lt hqp'_lt)]
    have h3 : ((q * p : ℕ) : ZMod p) = 0 := by
      simp only [Nat.cast_mul]
      have : (p : ZMod p) = 0 := ZMod.natCast_self p
      simp only [this, mul_zero]
    have h4 : ((q * p' : ℕ) : ZMod p) = ((p * q' - 1 : ℕ) : ZMod p) := by
      congr 1; omega
    have h5 : ((p * q' - 1 : ℕ) : ZMod p) = -1 := by
      have hpq'_pos : 0 < p * q' := Nat.mul_pos hp_pos hq'_pos
      rw [Nat.cast_sub (by omega : 1 ≤ p * q'), Nat.cast_one]
      simp only [Nat.cast_mul]
      have : (p : ZMod p) = 0 := ZMod.natCast_self p
      simp only [this, zero_mul, zero_sub]
    calc (q : ZMod p) * (p - p' : ℕ)
        = ((q * (p - p') : ℕ) : ZMod p) := by push_cast; ring
      _ = ((q * p - q * p' : ℕ) : ZMod p) := h1
      _ = ((q * p : ℕ) : ZMod p) - ((q * p' : ℕ) : ZMod p) := h2
      _ = 0 - ((q * p' : ℕ) : ZMod p) := by rw [h3]
      _ = 0 - ((p * q' - 1 : ℕ) : ZMod p) := by rw [h4]
      _ = 0 - (-1) := by rw [h5]
      _ = 1 := by ring
  -- From q * (p - p') = 1, deduce (p - p') = q^{-1}
  have hcop : IsUnit (q : ZMod p) := by rw [ZMod.isUnit_iff_coprime]; exact hcoprime.symm
  -- q * (p - p') = 1 implies (p - p') = q⁻¹
  have hinv : (q : ZMod p)⁻¹ * ((q : ZMod p) * (p - p' : ℕ)) = (q : ZMod p)⁻¹ * 1 :=
    congrArg _ hqinv
  rw [← mul_assoc, ZMod.inv_mul_of_unit _ hcop, one_mul, mul_one] at hinv
  exact hinv.symm

/-- The winding function is injective for k < p' when gcd(p,q) = 1. -/
lemma windingFn_injective_on (p q p' q' : ℕ) [hp : NeZero p]
    (_hq : 2 ≤ q) (_h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (hp'_pos : 0 < p') (hp'_lt : p' < p) (hq'_pos : 0 < q') (hq'_lt : q' < q)
    (hbezout : p * q' - q * p' = 1) :
    ∀ i j : ℕ, i < p' → j < p' → windingFn p q i = windingFn p q j → i = j := by
  intro i j hi hj heq
  unfold windingFn at heq
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · -- Both zero
    simp [hi0, hj0]
  · -- i = 0, j ≥ 1: derive contradiction
    simp only [hi0, hj0, ↓reduceIte] at heq
    -- heq: 0 = (j * q + 1 : ZMod p)
    have hj_eq : (j : ZMod p) * q = -1 := by
      have h1 : ((j * q + 1 : ℕ) : ZMod p) = 0 := heq.symm
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h1
      calc (j : ZMod p) * q = (j : ZMod p) * q + 1 - 1 := by ring
        _ = 0 - 1 := by rw [h1]
        _ = -1 := by ring
    -- So j ≡ -q^{-1} ≡ p' (mod p)
    have hqinv := q_inv_eq_p_minus_p' p q p' q' hcoprime hp'_pos hp'_lt hq'_pos hq'_lt hbezout
    have hcop : IsUnit (q : ZMod p) := by rw [ZMod.isUnit_iff_coprime]; exact hcoprime.symm
    have hj_eq_p' : (j : ZMod p) = (p' : ℕ) := by
      have hmul : (j : ZMod p) * q * (q : ZMod p)⁻¹ = -1 * (q : ZMod p)⁻¹ := by rw [hj_eq]
      rw [mul_assoc, ZMod.mul_inv_of_unit _ hcop, mul_one] at hmul
      rw [hmul, hqinv, neg_one_mul]
      simp only [Nat.cast_sub hp'_lt.le]
      have hp_zero : (p : ZMod p) = 0 := ZMod.natCast_self p
      simp only [hp_zero, zero_sub, neg_neg]
    -- But j < p' < p and p' < p, so both have the same val as naturals
    have hj_lt_p : j < p := Nat.lt_trans hj hp'_lt
    have hj_val : ((j : ℕ) : ZMod p).val = j := ZMod.val_natCast_of_lt hj_lt_p
    have hp'_val : ((p' : ℕ) : ZMod p).val = p' := ZMod.val_natCast_of_lt hp'_lt
    have hcontra : j = p' := by
      have := congrArg ZMod.val hj_eq_p'
      rw [hj_val, hp'_val] at this
      exact this
    omega
  · -- i ≥ 1, j = 0: derive contradiction (symmetric case)
    simp only [hi0, hj0, ↓reduceIte] at heq
    have hi_eq : (i : ZMod p) * q = -1 := by
      have h1 : ((i * q + 1 : ℕ) : ZMod p) = 0 := heq
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h1
      calc (i : ZMod p) * q = (i : ZMod p) * q + 1 - 1 := by ring
        _ = 0 - 1 := by rw [h1]
        _ = -1 := by ring
    have hqinv := q_inv_eq_p_minus_p' p q p' q' hcoprime hp'_pos hp'_lt hq'_pos hq'_lt hbezout
    have hcop : IsUnit (q : ZMod p) := by rw [ZMod.isUnit_iff_coprime]; exact hcoprime.symm
    have hi_eq_p' : (i : ZMod p) = (p' : ℕ) := by
      have hmul : (i : ZMod p) * q * (q : ZMod p)⁻¹ = -1 * (q : ZMod p)⁻¹ := by rw [hi_eq]
      rw [mul_assoc, ZMod.mul_inv_of_unit _ hcop, mul_one] at hmul
      rw [hmul, hqinv, neg_one_mul]
      simp only [Nat.cast_sub hp'_lt.le]
      have hp_zero : (p : ZMod p) = 0 := ZMod.natCast_self p
      simp only [hp_zero, zero_sub, neg_neg]
    have hi_lt_p : i < p := Nat.lt_trans hi hp'_lt
    have hi_val : ((i : ℕ) : ZMod p).val = i := ZMod.val_natCast_of_lt hi_lt_p
    have hp'_val : ((p' : ℕ) : ZMod p).val = p' := ZMod.val_natCast_of_lt hp'_lt
    have hcontra : i = p' := by
      have := congrArg ZMod.val hi_eq_p'
      rw [hi_val, hp'_val] at this
      exact this
    omega
  · -- Both ≥ 1: use coprimality
    simp only [hi0, hj0, ↓reduceIte] at heq
    -- heq: (i * q + 1 : ZMod p) = (j * q + 1 : ZMod p)
    have hiq_eq_jq : (i : ZMod p) * q = (j : ZMod p) * q := by
      have h1 : ((i * q + 1 : ℕ) : ZMod p) = ((j * q + 1 : ℕ) : ZMod p) := heq
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h1
      -- From i*q + 1 = j*q + 1, derive i*q = j*q
      have := add_right_cancel h1
      exact this
    have hcop : IsUnit (q : ZMod p) := by rw [ZMod.isUnit_iff_coprime]; exact hcoprime.symm
    have hi_eq_j_mod : (i : ZMod p) = (j : ZMod p) := by
      have hmul : (i : ZMod p) * q * (q : ZMod p)⁻¹ = (j : ZMod p) * q * (q : ZMod p)⁻¹ := by
        rw [hiq_eq_jq]
      rw [mul_assoc, ZMod.mul_inv_of_unit _ hcop, mul_one] at hmul
      rw [mul_assoc, ZMod.mul_inv_of_unit _ hcop, mul_one] at hmul
      exact hmul
    -- i, j < p' < p, so they're equal as naturals
    have hi_lt_p : i < p := Nat.lt_trans hi hp'_lt
    have hj_lt_p : j < p := Nat.lt_trans hj hp'_lt
    have hi_val : ((i : ℕ) : ZMod p).val = i := ZMod.val_natCast_of_lt hi_lt_p
    have hj_val : ((j : ℕ) : ZMod p).val = j := ZMod.val_natCast_of_lt hj_lt_p
    have := congrArg ZMod.val hi_eq_j_mod
    rw [hi_val, hj_val] at this
    exact this

/-- The winding subset has exactly p' elements. -/
lemma windingSubset_card (p q p' q' : ℕ) [hp : NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (hp'_pos : 0 < p') (hp'_lt : p' < p) (hq'_pos : 0 < q') (hq'_lt : q' < q)
    (hbezout : p * q' - q * p' = 1) :
    (windingSubset p q p').card = p' := by
  unfold windingSubset
  rw [Finset.card_image_of_injOn, Finset.card_range]
  -- Show windingFn is injective on range p'
  intro x hx y hy heq
  simp only [Finset.coe_range, Set.mem_Iio] at hx hy
  exact windingFn_injective_on p q p' q' hq h2q hcoprime hp'_pos hp'_lt hq'_pos hq'_lt hbezout
    x y hx hy heq

/-- q is not in the winding subset X.
    This is crucial: it shows X ⊆ V \ {q}, allowing the retraction construction.

    Proof: If q = k*q + 1 (mod p) for some k ∈ [1, p'-1], then (k-1)*q ≡ -1 (mod p),
    so k-1 ≡ -q^{-1} ≡ -(p-p') ≡ p' (mod p). But k-1 ∈ [0, p'-2] and p' > p'-2,
    so no such k exists. The case k=0 gives 0 ≠ q since q > 0. -/
lemma q_not_mem_windingSubset (p q p' q' : ℕ) [hp : NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (hp'_pos : 0 < p') (hp'_lt : p' < p) (hq'_pos : 0 < q') (hq'_lt : q' < q)
    (hbezout : p * q' - q * p' = 1) :
    (q : ZMod p) ∉ windingSubset p q p' := by
  unfold windingSubset
  simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
  intro k hk_lt
  by_cases hk0 : k = 0
  · -- Case k = 0: windingFn gives 0, but q ≠ 0 in ZMod p since 0 < q < p
    simp only [hk0, ↓reduceIte]
    have hq_lt_p : q < p := by omega
    intro heq
    -- heq : (q : ZMod p) = 0
    have hq_val : (q : ZMod p).val = q := ZMod.val_natCast_of_lt hq_lt_p
    have hval_eq : q = 0 := by
      have := congrArg ZMod.val heq
      rw [hq_val, ZMod.val_zero] at this
      exact this.symm
    omega
  · -- Case k ≥ 1: show k*q + 1 ≢ q (mod p)
    simp only [hk0, ↓reduceIte]
    intro heq
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    have hq_lt_p : q < p := by omega
    -- From k*q + 1 ≡ q (mod p), derive k-1 ≡ p' (mod p)
    -- First: k*q + 1 = q in ZMod p means k*q = q - 1
    have hkq_eq : (k : ZMod p) * q = q - 1 := by
      have h1 : ((k * q + 1 : ℕ) : ZMod p) = (q : ZMod p) := heq
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h1
      -- k * q + 1 = q implies k * q = q - 1
      calc (k : ZMod p) * q = (k : ZMod p) * q + 1 - 1 := by ring
        _ = (q : ZMod p) - 1 := by rw [h1]
        _ = q - 1 := rfl
    -- (k-1)*q = k*q - q = (q - 1) - q = -1 in ZMod p
    have hk1q : ((k - 1 : ℕ) : ZMod p) * q = -1 := by
      have hk_sub : (k : ZMod p) = (k - 1 : ℕ) + 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk0)]; ring
      calc ((k - 1 : ℕ) : ZMod p) * q
          = ((k : ZMod p) - 1) * q := by rw [hk_sub]; ring
        _ = (k : ZMod p) * q - q := by ring
        _ = (q - 1) - q := by rw [hkq_eq]
        _ = -1 := by ring
    -- Therefore k-1 = -q^{-1} = -(p - p') = p' in ZMod p
    have hqinv := q_inv_eq_p_minus_p' p q p' q' hcoprime hp'_pos hp'_lt hq'_pos hq'_lt hbezout
    have hcop : IsUnit (q : ZMod p) := by rw [ZMod.isUnit_iff_coprime]; exact hcoprime.symm
    have hk1_eq_p' : ((k - 1 : ℕ) : ZMod p) = (p' : ℕ) := by
      -- (k-1) * q = -1 implies k-1 = -1 * q^{-1} = -q^{-1}
      have hmul : ((k - 1 : ℕ) : ZMod p) * q * (q : ZMod p)⁻¹ = -1 * (q : ZMod p)⁻¹ := by
        rw [hk1q]
      rw [mul_assoc, ZMod.mul_inv_of_unit _ hcop, mul_one] at hmul
      rw [hmul, hqinv, neg_one_mul]
      simp only [Nat.cast_sub hp'_lt.le]
      have hp_zero : (p : ZMod p) = 0 := ZMod.natCast_self p
      simp only [hp_zero, zero_sub, neg_neg]
    -- But k-1 < p' - 1 < p' (since k < p' and k ≥ 1)
    have hk1_lt : k - 1 < p' := by omega
    have hk1_lt_p : k - 1 < p := Nat.lt_trans hk1_lt hp'_lt
    -- So k-1 and p' have the same val in ZMod p, hence are equal as naturals
    have hk1_val : ((k - 1 : ℕ) : ZMod p).val = k - 1 := ZMod.val_natCast_of_lt hk1_lt_p
    have hp'_val : ((p' : ℕ) : ZMod p).val = p' := ZMod.val_natCast_of_lt hp'_lt
    have hcontra : k - 1 = p' := by
      have := congrArg ZMod.val hk1_eq_p'
      rw [hk1_val, hp'_val] at this
      exact this
    -- Contradiction: k - 1 < p' but k - 1 = p'
    omega

/-- The retraction index: for y ∈ ZMod p, computes the index i such that
    the retraction r(y) = windingFn(i). This is the largest index i such that
    windingFn(i).val ≤ y.val. -/
def retractionIndex (p q : ℕ) (y : ZMod p) : ℕ :=
  if y.val = 0 then 0 else (y.val - 1) / q

/-- The retraction map: composes the retraction with the inverse isomorphism.
    Maps y ∈ ZMod p to the corresponding element of ZMod p' via:
    y ↦ retractionIndex(y) * q' mod p' -/
def retractionMap (p q p' q' : ℕ) [NeZero p'] (y : ZMod p) : ZMod p' :=
  (retractionIndex p q y * q' : ℕ)

/-- Find the element of X with maximum val ≤ bound. Returns 0 if no such element exists. -/
noncomputable def maxValElement (p : ℕ) [NeZero p] (X : Finset (ZMod p)) (bound : ℕ) : ZMod p :=
  let candidates := X.filter (fun x => x.val ≤ bound)
  if h : candidates.Nonempty then
    -- Find max val among candidates
    let valSet : Finset ℕ := candidates.image (fun x => x.val)
    have hvalSet_ne : valSet.Nonempty := by
      obtain ⟨z, hz⟩ := h
      exact ⟨z.val, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let maxVal := valSet.max' hvalSet_ne
    -- Return the element with maxVal (val is injective on ZMod p when p > 0)
    have hmem : maxVal ∈ valSet := Finset.max'_mem valSet hvalSet_ne
    have hex : ∃ x ∈ candidates, x.val = maxVal := Finset.mem_image.mp hmem
    Classical.choose hex
  else
    0

/-- The "floor in X" retraction: returns the largest element of the winding subset X
    whose value is ≤ y.val. This is the correct retraction for cohomomorphisms. -/
noncomputable def floorInWindingSubset (p q p' : ℕ) [NeZero p] (y : ZMod p) : ZMod p :=
  maxValElement p (windingSubset p q p') y.val

/-- The position of an element x in the sorted winding subset X.
    This gives the isomorphism X → ZMod p' by mapping x to the count of
    elements of X that are strictly less than x (by val). -/
def positionInWindingSubset (p q p' : ℕ) [NeZero p] [NeZero p'] (x : ZMod p) : ZMod p' :=
  let X := windingSubset p q p'
  ((X.filter (fun z => z.val < x.val)).card : ℕ)

/-- The correct forward cohomomorphism map: combines the floor retraction
    with the position isomorphism. For y ∈ V\{v}, maps to ZMod p' via:
    y ↦ position(floor_in_X(y)) -/
noncomputable def forwardCohomMap (p q p' : ℕ) [NeZero p] [NeZero p'] (y : ZMod p) : ZMod p' :=
  positionInWindingSubset p q p' (floorInWindingSubset p q p' y)

/-- The winding subset always contains 0. -/
lemma zero_mem_windingSubset (p q p' : ℕ) [NeZero p] (hp'_pos : 0 < p') :
    (0 : ZMod p) ∈ windingSubset p q p' := by
  unfold windingSubset
  simp only [Finset.mem_image, Finset.mem_range]
  use 0
  constructor
  · exact hp'_pos
  · rfl

/-- The maxValElement returns an element of the input set S when candidates exist. -/
lemma maxValElement_mem (p : ℕ) [NeZero p] (S : Finset (ZMod p)) (bound : ℕ)
    (hne : (S.filter (fun x => x.val ≤ bound)).Nonempty) :
    maxValElement p S bound ∈ S := by
  simp only [maxValElement, hne, ↓reduceDIte]
  set candidates := S.filter (fun x => x.val ≤ bound) with hcand_def
  set valSet : Finset ℕ := candidates.image (fun x => x.val) with hvalSet_def
  have hvalSet_ne : valSet.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z.val, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  set maxVal := valSet.max' hvalSet_ne with hmaxVal_def
  have hmem : maxVal ∈ valSet := Finset.max'_mem valSet hvalSet_ne
  have hex : ∃ x ∈ candidates, x.val = maxVal := Finset.mem_image.mp hmem
  have hspec := Classical.choose_spec hex
  have hcand_mem : Classical.choose hex ∈ candidates := hspec.1
  exact (Finset.mem_filter.mp hcand_mem).1

/-- The maxValElement has val ≤ bound when candidates exist. -/
lemma maxValElement_val_le (p : ℕ) [NeZero p] (S : Finset (ZMod p)) (bound : ℕ)
    (hne : (S.filter (fun x => x.val ≤ bound)).Nonempty) :
    (maxValElement p S bound).val ≤ bound := by
  simp only [maxValElement, hne, ↓reduceDIte]
  set candidates := S.filter (fun x => x.val ≤ bound) with hcand_def
  set valSet : Finset ℕ := candidates.image (fun x => x.val) with hvalSet_def
  have hvalSet_ne : valSet.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z.val, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  set maxVal := valSet.max' hvalSet_ne with hmaxVal_def
  have hmem : maxVal ∈ valSet := Finset.max'_mem valSet hvalSet_ne
  have hex : ∃ x ∈ candidates, x.val = maxVal := Finset.mem_image.mp hmem
  have hspec := Classical.choose_spec hex
  have hcand_mem : Classical.choose hex ∈ candidates := hspec.1
  have hval_eq : (Classical.choose hex).val = maxVal := hspec.2
  rw [hval_eq]
  have hmaxVal_mem : maxVal ∈ valSet := Finset.max'_mem valSet hvalSet_ne
  obtain ⟨z, hz_mem, hz_val⟩ := Finset.mem_image.mp hmaxVal_mem
  rw [← hz_val]
  exact (Finset.mem_filter.mp hz_mem).2

/-- The maxValElement has val ≥ any element in candidates. -/
lemma maxValElement_val_ge (p : ℕ) [NeZero p] (S : Finset (ZMod p)) (bound : ℕ)
    (hne : (S.filter (fun x => x.val ≤ bound)).Nonempty)
    (z : ZMod p) (hz : z ∈ S) (hz_bound : z.val ≤ bound) :
    (maxValElement p S bound).val ≥ z.val := by
  simp only [maxValElement, hne, ↓reduceDIte]
  set candidates := S.filter (fun x => x.val ≤ bound) with hcand_def
  set valSet : Finset ℕ := candidates.image (fun x => x.val) with hvalSet_def
  have hvalSet_ne : valSet.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨w.val, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
  set maxVal := valSet.max' hvalSet_ne with hmaxVal_def
  have hmem : maxVal ∈ valSet := Finset.max'_mem valSet hvalSet_ne
  have hex : ∃ x ∈ candidates, x.val = maxVal := Finset.mem_image.mp hmem
  have hspec := Classical.choose_spec hex
  have hval_eq : (Classical.choose hex).val = maxVal := hspec.2
  rw [hval_eq]
  have hz_cand : z ∈ candidates := Finset.mem_filter.mpr ⟨hz, hz_bound⟩
  have hz_in_valSet : z.val ∈ valSet := Finset.mem_image.mpr ⟨z, hz_cand, rfl⟩
  exact Finset.le_max' valSet z.val hz_in_valSet

/-- floor(0) = 0 -/
lemma floorInWindingSubset_zero (p q p' : ℕ) [NeZero p] (hp'_pos : 0 < p') :
    floorInWindingSubset p q p' 0 = 0 := by
  unfold floorInWindingSubset
  have h0 : (0 : ZMod p) ∈ windingSubset p q p' := zero_mem_windingSubset p q p' hp'_pos
  have h0_cand :
      (0 : ZMod p) ∈ (windingSubset p q p').filter (fun x => x.val ≤ (0 : ZMod p).val) := by
    rw [Finset.mem_filter]; exact ⟨h0, le_refl _⟩
  have hne :
      ((windingSubset p q p').filter (fun x => x.val ≤ (0 : ZMod p).val)).Nonempty := ⟨0, h0_cand⟩
  -- The only element with val ≤ 0 is 0 itself, so maxValElement returns 0
  have hmax_bound :
      (maxValElement p (windingSubset p q p') (0 : ZMod p).val).val ≤ (0 : ZMod p).val :=
    maxValElement_val_le p _ _ hne
  have hmax_ge :
      (maxValElement p (windingSubset p q p') (0 : ZMod p).val).val ≥ (0 : ZMod p).val :=
    maxValElement_val_ge p _ _ hne 0 h0 (le_refl _)
  have hmax_eq : (maxValElement p (windingSubset p q p') (0 : ZMod p).val).val = 0 := by
    simp only [ZMod.val_zero] at hmax_bound hmax_ge ⊢
    omega
  exact ZMod.val_injective p (hmax_eq.trans ZMod.val_zero.symm)

/-- The floor retraction maps into the winding subset. -/
lemma floorInWindingSubset_mem (p q p' : ℕ) [NeZero p] (hp'_pos : 0 < p')
    (y : ZMod p) : floorInWindingSubset p q p' y ∈ windingSubset p q p' := by
  unfold floorInWindingSubset
  set X := windingSubset p q p'
  set candidates := X.filter (fun x => x.val ≤ y.val)
  -- 0 ∈ X and 0.val = 0 ≤ y.val, so candidates is nonempty
  have h0 : (0 : ZMod p) ∈ X := zero_mem_windingSubset p q p' hp'_pos
  have hzero_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h0_cand : (0 : ZMod p) ∈ candidates := by
    rw [Finset.mem_filter]
    constructor
    · exact h0
    · rw [hzero_val]; exact Nat.zero_le _
  have hne : candidates.Nonempty := ⟨0, h0_cand⟩
  exact maxValElement_mem p X y.val hne

/-- The retractionIndex is bounded by p' - 1 when y ≠ q.
    Key insight: the winding subset has exactly p' elements. -/
lemma retractionIndex_lt_p' (p q p' q' : ℕ) [NeZero p] (hq : 2 ≤ q) (h2q : 2 * q ≤ p)
    (hp'_pos : 0 < p') (hq'_pos : 0 < q') (hbezout : p * q' - q * p' = 1)
    (y : ZMod p) (_hy : y ≠ (q : ZMod p)) : retractionIndex p q y < p' := by
  unfold retractionIndex
  split_ifs with h0
  · exact hp'_pos
  · -- (y.val - 1) / q < p' follows from y.val < p and p * q' = q * p' + 1
    have hbez : p * q' = q * p' + 1 := by omega
    have hy_lt : y.val < p := y.val_lt
    have h1 : y.val - 1 < q * p' := by
      have h2 : p ≤ p * q' := Nat.le_mul_of_pos_right p hq'_pos
      have h3 : p * q' = q * p' + 1 := hbez
      omega
    exact Nat.div_lt_of_lt_mul h1

/-- Two elements with the same retractionIndex are at distance < q.
    This is the key lemma: elements in the same "interval" are adjacent in E_{p/q}. -/
lemma same_retractionIndex_adjacent (p q : ℕ) [NeZero p] (hq_pos : 0 < q) (h2q : 2 * q ≤ p)
    (u w : ZMod p) (hu_ne_q : u ≠ (q : ZMod p)) (hw_ne_q : w ≠ (q : ZMod p))
    (huw : u ≠ w) (hsame : retractionIndex p q u = retractionIndex p q w) :
    distMod p u w < q := by
  -- The retractionIndex partitions ZMod p into intervals.
  -- Elements in the same interval (excluding q) have distMod < q.
  unfold retractionIndex at hsame
  have hq_lt_p : q < p := by omega
  -- Convert u ≠ q to val ≠ q
  have hu_val_ne_q : u.val ≠ q := by
    intro h
    have hcast : (q : ZMod p).val = q := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq_lt_p]
    exact hu_ne_q (ZMod.val_injective p (h.trans hcast.symm))
  have hw_val_ne_q : w.val ≠ q := by
    intro h
    have hcast : (q : ZMod p).val = q := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq_lt_p]
    exact hw_ne_q (ZMod.val_injective p (h.trans hcast.symm))
  -- Show that u.val and w.val are in the same interval, bounded by q
  -- Key: retractionIndex = (val - 1) / q for val > 0, so same index ⟹ vals in same interval
  by_cases hu0 : u.val = 0 <;> by_cases hw0 : w.val = 0
  · -- Both 0: u = w, contradiction
    exact absurd (ZMod.val_injective p (hu0.trans hw0.symm)) huw
  · -- u.val = 0, w.val ≠ 0: hsame: 0 = (w.val - 1) / q, so w.val - 1 < q
    simp only [hu0, ↓reduceIte, hw0] at hsame
    have hw_sub_lt : w.val - 1 < q := (Nat.div_eq_zero_iff_lt hq_pos).mp hsame.symm
    have hw_lt_q : w.val < q := by omega
    have hu_eq_0 : u = 0 := ZMod.val_injective p (hu0.trans (ZMod.val_zero).symm)
    rw [hu_eq_0, distMod_comm]
    simp only [distMod, sub_zero]
    rw [min_def]; split_ifs with hcmp <;> omega
  · -- u.val ≠ 0, w.val = 0: hsame: (u.val - 1) / q = 0, so u.val - 1 < q
    simp only [hu0, ↓reduceIte, hw0] at hsame
    have hu_sub_lt : u.val - 1 < q := (Nat.div_eq_zero_iff_lt hq_pos).mp hsame
    have hu_lt_q : u.val < q := by omega
    have hw_eq_0 : w = 0 := ZMod.val_injective p (hw0.trans (ZMod.val_zero).symm)
    rw [hw_eq_0]
    simp only [distMod, sub_zero]
    rw [min_def]; split_ifs with hcmp <;> omega
  · -- Both nonzero: same (val - 1) / q means in same interval of size ≤ q
    simp only [hu0, ↓reduceIte, hw0] at hsame
    -- u.val and w.val are in the same interval (k*q+1, (k+1)*q]
    set k := (u.val - 1) / q with hk
    have hwk : (w.val - 1) / q = k := hsame.symm
    -- Both in interval (k*q, (k+1)*q], size q
    have hu_lb : k * q < u.val := by
      have h := Nat.mul_div_le (u.val - 1) q
      simp only [← hk] at h
      calc k * q = q * k := mul_comm k q
        _ ≤ u.val - 1 := h
        _ < u.val := Nat.sub_lt (Nat.pos_of_ne_zero hu0) Nat.one_pos
    have hw_lb : k * q < w.val := by
      have h := Nat.mul_div_le (w.val - 1) q
      simp only [hwk] at h
      calc k * q = q * k := mul_comm k q
        _ ≤ w.val - 1 := h
        _ < w.val := Nat.sub_lt (Nat.pos_of_ne_zero hw0) Nat.one_pos
    have hu_ub : u.val ≤ (k + 1) * q := by
      by_contra h
      push_neg at h
      have hdiv : k + 1 ≤ (u.val - 1) / q := by
        rw [Nat.le_div_iff_mul_le hq_pos]
        omega
      omega
    have hw_ub : w.val ≤ (k + 1) * q := by
      by_contra h
      push_neg at h
      have hdiv : k + 1 ≤ (w.val - 1) / q := by
        rw [Nat.le_div_iff_mul_le hq_pos]
        omega
      rw [hwk] at hdiv
      omega
    -- k = 0: interval is [1, q], excluding q gives [1, q-1]
    by_cases hk0 : k = 0
    · simp only [hk0, zero_mul, Nat.zero_add, one_mul] at hu_lb hu_ub hw_lb hw_ub
      have hu_lt_q : u.val < q := by omega
      have hw_lt_q : w.val < q := by omega
      by_cases h : w.val ≤ u.val
      · simp only [distMod, ZMod.val_sub h, min_def]
        split_ifs with hcmp <;> omega
      · push_neg at h
        rw [distMod_comm]
        simp only [distMod, ZMod.val_sub (le_of_lt h), min_def]
        split_ifs with hcmp <;> omega
    · -- k ≥ 1: interval has size exactly q
      have hk_ge : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk0
      have hu_ge_q : u.val > q := by
        calc u.val > k * q := hu_lb
          _ ≥ 1 * q := Nat.mul_le_mul_right q hk_ge
          _ = q := one_mul q
      have hw_ge_q : w.val > q := by
        calc w.val > k * q := hw_lb
          _ ≥ 1 * q := Nat.mul_le_mul_right q hk_ge
          _ = q := one_mul q
      have hdiff_uw : u.val - w.val < q := by
        have h1 : u.val ≤ (k + 1) * q := hu_ub
        have h2 : w.val > k * q := hw_lb
        have h3 : (k + 1) * q = k * q + q := by ring
        omega
      have hdiff_wu : w.val - u.val < q := by
        have h1 : w.val ≤ (k + 1) * q := hw_ub
        have h2 : u.val > k * q := hu_lb
        have h3 : (k + 1) * q = k * q + q := by ring
        omega
      by_cases h : w.val ≤ u.val
      · simp only [distMod, ZMod.val_sub h, min_def]
        split_ifs with hcmp
        · exact hdiff_uw
        · -- This branch is unreachable: diff < q and 2q ≤ p implies diff < p - diff
          exfalso
          have : u.val - w.val < q := hdiff_uw
          omega
      · push_neg at h
        rw [distMod_comm]
        simp only [distMod, ZMod.val_sub (le_of_lt h), min_def]
        split_ifs with hcmp
        · exact hdiff_wu
        · -- This branch is unreachable
          exfalso
          have : w.val - u.val < q := hdiff_wu
          omega

/-- Key structural lemma: if floor(u) = floor(w) for u.val ≤ w.val, then w.val - u.val ≤ q.
    When both u ≠ q and w ≠ q, this becomes w.val - u.val < q.

    Proof sketch: The winding subset X partitions ZMod p into intervals. Each interval
    [x.val, next(x).val) has size at most q + 1. If size = q + 1, the interval contains q.
    Since u ≠ q and w ≠ q, they're in an effective interval of size ≤ q.

    This is a structural property of the Stern-Brocot sequence construction.

    Full proof strategy:
    1. Show same floor implies same retractionIndex (by interval analysis)
    2. Use same_retractionIndex_adjacent to get distMod < q
    3. Since u.val ≤ w.val, distMod = w.val - u.val, so w.val - u.val < q -/
lemma floor_same_implies_val_diff_lt_q (p q p' q' : ℕ) [NeZero p] (hq : 2 ≤ q) (h2q : 2 * q ≤ p)
    (_hcoprime : Nat.Coprime p q) (hp'_pos : 0 < p') (hp'_lt : p' < p)
    (hq'_pos : 0 < q') (hq'_lt : q' < q) (hbezout : p * q' - q * p' = 1)
    (u w : ZMod p) (hu_ne_q : u ≠ (q : ZMod p)) (hw_ne_q : w ≠ (q : ZMod p))
    (huw : u ≠ w) (h_le : u.val ≤ w.val)
    (hsame : floorInWindingSubset p q p' u = floorInWindingSubset p q p' w) :
    w.val - u.val < q := by
  -- Key insight: same floor implies same retractionIndex, which implies distMod < q
  have hq_pos : 0 < q := by omega
  have hq_lt_p : q < p := by omega
  -- Convert u ≠ q to val ≠ q
  have hu_val_ne_q : u.val ≠ q := by
    intro h
    have hcast : (q : ZMod p).val = q := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq_lt_p]
    exact hu_ne_q (ZMod.val_injective p (h.trans hcast.symm))
  have hw_val_ne_q : w.val ≠ q := by
    intro h
    have hcast : (q : ZMod p).val = q := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq_lt_p]
    exact hw_ne_q (ZMod.val_injective p (h.trans hcast.symm))
  -- Step 1: Same floor implies same retractionIndex
  -- The floor function partitions [0, p) into intervals aligned with retractionIndex intervals
  have hsame_retract : retractionIndex p q u = retractionIndex p q w := by
    -- Proof: If retractionIndex differs, there's a winding element between u and w
    -- which would make their floors different
    unfold retractionIndex
    by_cases hu0 : u.val = 0 <;> by_cases hw0 : w.val = 0
    · -- Both 0: refl
      simp only [hu0, ↓reduceIte, hw0]
    · -- u.val = 0, w.val ≠ 0
      simp only [hu0, ↓reduceIte, hw0]
      -- Need: (w.val - 1) / q = 0
      -- floor(u) = floor(0) = 0 (since u.val = 0)
      -- floor(w) = floor(0) implies w.val < q + 1 (else floor(w) ≥ q+1 > 0)
      by_contra h_ne
      push_neg at h_ne
      have hw_ge_q1 : w.val ≥ q + 1 := by
        have hdiv_ge : (w.val - 1) / q ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Ne.symm h_ne)
        have hq_le : q ≤ w.val - 1 := (Nat.one_le_div_iff hq_pos).mp hdiv_ge
        omega
      -- q+1 ∈ windingSubset, so floor(w) ≥ q+1 > 0 = floor(u)
      -- First show p' ≥ 2: from Bezout p*q' - q*p' = 1 and p ≥ 2q, if p' = 1 then p = q + 1 < 2q
      have hp'_ge_2 : p' ≥ 2 := by
        by_contra hp'_lt_2
        push_neg at hp'_lt_2
        -- p' < 2 means p' = 0 or p' = 1
        -- If p' = 0: p*q' = 1, but p ≥ 2q ≥ 4, contradiction
        -- If p' = 1: p*q' = q + 1, but p ≥ 2q, q' ≥ 1 gives p ≤ q + 1 < 2q, contradiction
        have hp'_cases : p' = 0 ∨ p' = 1 := by omega
        rcases hp'_cases with rfl | rfl
        · -- p' = 0: p * q' = 1 + 0 = 1, but p ≥ 4
          simp only [Nat.mul_zero, Nat.sub_zero] at hbezout
          have : p * q' = 1 := hbezout
          have hp_ge : p ≥ 4 := by omega
          have hq'_ge : q' ≥ 1 := hq'_pos
          have : p * q' ≥ 4 := by nlinarith
          omega
        · -- p' = 1: p * q' = q + 1
          simp only [Nat.mul_one] at hbezout
          have heq : p * q' = q + 1 := by omega
          have hp_ge : p ≥ 2 * q := h2q
          have hq'_ge : q' ≥ 1 := hq'_pos
          have hq'_lt : q' < q := hq'_lt
          have : p * q' ≥ p := Nat.le_mul_of_pos_right p hq'_ge
          have : p ≤ q + 1 := by omega
          omega
      have hq1_in : ((q + 1 : ℕ) : ZMod p) ∈ windingSubset p q p' := by
        unfold windingSubset
        rw [Finset.mem_image]
        use 1; constructor; · exact Finset.mem_range.mpr (by omega : 1 < p')
        simp only [one_ne_zero, if_false, one_mul]
      have hq1_val : ((q + 1 : ℕ) : ZMod p).val = q + 1 := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; omega
      have hfloor_w_ge : (floorInWindingSubset p q p' w).val ≥ q + 1 := by
        unfold floorInWindingSubset
        have h0_in : (0 : ZMod p) ∈ windingSubset p q p' := zero_mem_windingSubset p q p' hp'_pos
        have hne : ((windingSubset p q p').filter (fun z => z.val ≤ w.val)).Nonempty := by
          use 0; rw [Finset.mem_filter]; exact ⟨h0_in, by simp [ZMod.val_zero]⟩
        have := maxValElement_val_ge p (windingSubset p q p') w.val hne
          ((q + 1 : ℕ) : ZMod p) hq1_in
        rw [hq1_val] at this; exact this hw_ge_q1
      have hfloor_u_eq : floorInWindingSubset p q p' u = 0 := by
        have hu_eq : u = 0 := ZMod.val_injective p (hu0.trans ZMod.val_zero.symm)
        rw [hu_eq]; exact floorInWindingSubset_zero p q p' hp'_pos
      rw [← hsame, hfloor_u_eq] at hfloor_w_ge; simp at hfloor_w_ge
    · -- u.val ≠ 0, w.val = 0: impossible since u.val ≤ w.val (u.val < w.val)
      exfalso; omega
    · -- Both nonzero
      simp only [hu0, ↓reduceIte, hw0]
      by_contra h_ne
      set ku := (u.val - 1) / q with hku_def
      set kw := (w.val - 1) / q with hkw_def
      wlog hkw_lt : ku < kw generalizing u w with hsym
      · push_neg at hkw_lt
        have hku_lt : kw < ku := Nat.lt_of_le_of_ne hkw_lt (Ne.symm h_ne)
        -- If kw < ku, then since u.val ≤ w.val, we have a contradiction:
        -- ku = (u.val-1)/q, kw = (w.val-1)/q, u.val ≤ w.val ⟹ ku ≤ kw
        have hle_sub : u.val - 1 ≤ w.val - 1 := Nat.sub_le_sub_right h_le 1
        have hdiv_le : ku ≤ kw := Nat.div_le_div_right hle_sub
        omega
      -- ku < kw: the winding element (kw * q + 1) is between u and w
      have hkw_ge_1 : kw ≥ 1 := by
        by_contra hkw_eq_0
        push_neg at hkw_eq_0
        have hkw_zero : kw = 0 := Nat.lt_one_iff.mp hkw_eq_0
        rw [hkw_zero] at hkw_lt
        exact Nat.not_lt_zero ku hkw_lt
      -- Key bound: kw * q ≤ w.val - 1, so kw * q + 1 ≤ w.val
      have hkw_mul_bound : kw * q ≤ w.val - 1 := by
        have h := Nat.mul_div_le (w.val - 1) q
        calc kw * q = q * kw := mul_comm _ _
          _ = q * ((w.val - 1) / q) := by rfl
          _ ≤ w.val - 1 := h
      have hkw1_le_w : kw * q + 1 ≤ w.val := by omega
      have hkw_in : ((kw * q + 1 : ℕ) : ZMod p) ∈ windingSubset p q p' := by
        unfold windingSubset
        rw [Finset.mem_image]
        use kw; constructor
        · -- kw < p' follows from kw * q + 1 ≤ w.val < p ≤ q * p' + 1
          rw [Finset.mem_range]
          have hw_lt : w.val < p := w.val_lt
          -- From Bezout: p * q' = q * p' + 1, so p ≤ p * q' = q * p' + 1
          have hp_le : p ≤ q * p' + 1 := by
            have hbez' : p * q' = q * p' + 1 := by omega
            have hp_le_pq' : p ≤ p * q' := Nat.le_mul_of_pos_right p hq'_pos
            omega
          by_contra hkw_ge
          push_neg at hkw_ge
          have hkw_q_bound : kw * q + 1 ≥ p' * q + 1 := by
            have : kw * q ≥ p' * q := Nat.mul_le_mul_right q hkw_ge
            omega
          -- kw * q + 1 ≤ w.val < p ≤ q * p' + 1 = p' * q + 1 ≤ kw * q + 1
          have : p' * q + 1 = q * p' + 1 := by ring
          omega
        · simp only [Nat.one_le_iff_ne_zero.mp hkw_ge_1, if_false]
      have hkw_mul_le : kw * q ≤ w.val - 1 := by
        have h := Nat.mul_div_le (w.val - 1) q
        calc kw * q = q * kw := mul_comm _ _
          _ = q * ((w.val - 1) / q) := by rfl
          _ ≤ w.val - 1 := h
      have hkw1_le_w : kw * q + 1 ≤ w.val := by omega
      have hkw_val : ((kw * q + 1 : ℕ) : ZMod p).val = kw * q + 1 := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
        have hw_lt : w.val < p := w.val_lt; omega
      -- floor(w).val ≥ kw * q + 1
      have hfloor_w_ge : (floorInWindingSubset p q p' w).val ≥ kw * q + 1 := by
        unfold floorInWindingSubset
        have h0_in : (0 : ZMod p) ∈ windingSubset p q p' := zero_mem_windingSubset p q p' hp'_pos
        have hne : ((windingSubset p q p').filter (fun z => z.val ≤ w.val)).Nonempty := by
          use 0; rw [Finset.mem_filter]; exact ⟨h0_in, by simp [ZMod.val_zero]⟩
        have := maxValElement_val_ge p (windingSubset p q p') w.val hne
          ((kw * q + 1 : ℕ) : ZMod p) hkw_in
        rw [hkw_val] at this; exact this hkw1_le_w
      -- floor(u).val ≤ u.val < kw * q + 1
      have hfloor_u_le : (floorInWindingSubset p q p' u).val ≤ u.val := by
        unfold floorInWindingSubset
        have h0_in : (0 : ZMod p) ∈ windingSubset p q p' := zero_mem_windingSubset p q p' hp'_pos
        have hne : ((windingSubset p q p').filter (fun z => z.val ≤ u.val)).Nonempty := by
          use 0; rw [Finset.mem_filter]; exact ⟨h0_in, by simp [ZMod.val_zero]⟩
        exact maxValElement_val_le p (windingSubset p q p') u.val hne
      have hu_lt_kw1 : u.val < kw * q + 1 := by
        have h1 : u.val ≤ (ku + 1) * q := by
          by_contra h; push_neg at h
          have : ku + 1 ≤ (u.val - 1) / q := by rw [Nat.le_div_iff_mul_le hq_pos]; omega
          omega
        have h2 : (ku + 1) * q ≤ kw * q := Nat.mul_le_mul_right q (by omega : ku + 1 ≤ kw)
        omega
      -- But floor(u) = floor(w), so their vals should be equal
      have hfloor_eq :
          (floorInWindingSubset p q p' u).val = (floorInWindingSubset p q p' w).val := by
        rw [hsame]
      omega
  -- Step 2: Derive w.val - u.val < q directly from same retractionIndex
  -- Since both have the same retractionIndex k = (val - 1) / q, they're both in the interval
  -- (k*q, (k+1)*q] (for val > 0) or [0, q) (for val = 0). The interval has size ≤ q.
  by_cases heq : u = w
  · exact absurd heq huw
  · have hstrict : u.val < w.val :=
      Nat.lt_of_le_of_ne h_le (fun heq' => heq (ZMod.val_injective p heq'))
    by_cases hu0 : u.val = 0 <;> by_cases hw0 : w.val = 0
    · -- Both 0: contradicts u ≠ w
      exact absurd (ZMod.val_injective p (hu0.trans hw0.symm)) huw
    · -- u.val = 0, w.val ≠ 0
      unfold retractionIndex at hsame_retract
      simp only [hu0, ↓reduceIte, hw0] at hsame_retract
      -- hsame_retract: 0 = (w.val - 1) / q
      have hw_sub_lt : w.val - 1 < q := (Nat.div_eq_zero_iff_lt hq_pos).mp hsame_retract.symm
      omega
    · -- u.val ≠ 0, w.val = 0: impossible since u.val < w.val
      exfalso; omega
    · -- Both nonzero: same (val - 1) / q means in same interval of size q
      unfold retractionIndex at hsame_retract
      simp only [hu0, ↓reduceIte, hw0] at hsame_retract
      set k := (u.val - 1) / q with hk
      have hwk : (w.val - 1) / q = k := hsame_retract.symm
      -- Both vals are in (k*q, (k+1)*q]
      have hu_lb : k * q < u.val := by
        have h := Nat.mul_div_le (u.val - 1) q
        simp only [← hk] at h
        calc k * q = q * k := mul_comm k q
          _ ≤ u.val - 1 := h
          _ < u.val := Nat.sub_lt (Nat.pos_of_ne_zero hu0) Nat.one_pos
      have hw_ub : w.val ≤ (k + 1) * q := by
        by_contra h
        push_neg at h
        have hdiv : k + 1 ≤ (w.val - 1) / q := by
          rw [Nat.le_div_iff_mul_le hq_pos]
          omega
        rw [hwk] at hdiv
        omega
      -- So w.val - u.val < (k+1)*q - k*q = q
      have h3 : (k + 1) * q = k * q + q := by ring
      omega

/-- Key lemma: elements in the same "interval" (with same floor in X) have distMod < q,
    provided neither element is q itself. This is because:
    1. Consecutive elements of X in sorted order define intervals
    2. The interval containing q has size at most q + 1 (from Bezout identity)
    3. After excluding q, all intervals have at most q elements
    4. In an interval of k elements, max distMod = k - 1 < q

    Reference: Hell-Nešetřil Lemma 6.6 - the retraction works because q is removed. -/
lemma same_floor_adjacent (p q p' q' : ℕ) [NeZero p] (hq : 2 ≤ q) (h2q : 2 * q ≤ p)
    (hcoprime : Nat.Coprime p q) (hp'_pos : 0 < p') (hp'_lt : p' < p)
    (hq'_pos : 0 < q') (hq'_lt : q' < q) (hbezout : p * q' - q * p' = 1)
    (u w : ZMod p) (hu_ne_q : u ≠ (q : ZMod p)) (hw_ne_q : w ≠ (q : ZMod p))
    (huw : u ≠ w)
    (hsame : floorInWindingSubset p q p' u = floorInWindingSubset p q p' w) :
    distMod p u w < q := by
  -- Strategy: elements with the same floor are in an interval of size ≤ q+1.
  -- If the interval has size q+1, then q is in the interval.
  -- Since u ≠ q and w ≠ q, the effective interval size is ≤ q, so distMod < q.
  have hq_pos : 0 < q := by omega
  have hq_lt_p : q < p := by omega

  -- Convert u ≠ q to val ≠ q
  have hu_val_ne_q : u.val ≠ q := by
    intro h
    have hcast : (q : ZMod p).val = q := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq_lt_p]
    have : u.val = (q : ZMod p).val := h.trans hcast.symm
    exact hu_ne_q (ZMod.val_injective p this)
  have hw_val_ne_q : w.val ≠ q := by
    intro h
    have hcast : (q : ZMod p).val = q := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq_lt_p]
    have : w.val = (q : ZMod p).val := h.trans hcast.symm
    exact hw_ne_q (ZMod.val_injective p this)

  set x := floorInWindingSubset p q p' u with hx_def
  have hxw : floorInWindingSubset p q p' w = x := hsame.symm
  have hx_mem : x ∈ windingSubset p q p' := floorInWindingSubset_mem p q p' hp'_pos u
  have hu_val := u.val_lt
  have hw_val := w.val_lt

  -- x.val ≤ u.val and x.val ≤ w.val (by definition of floor as max with val ≤)
  -- We need to show the interval [x.val, next.val) has bounded size
  -- Since the winding subset has p' elements covering p values and p ≈ p' * q
  -- (from the Bezout relation), intervals have size approximately q.

  -- Direct approach: bound |u.val - w.val| and show it's < q
  -- Key insight: if both u and w have the same floor x, they're both in [x.val, next.val)
  -- The max gap between x.val and the next X element (or p for wrap-around) is ≤ q + 1.
  -- Excluding q from consideration (since u ≠ q and w ≠ q), the effective gap is ≤ q.

  -- For elements in an interval of size ≤ q, the max |u.val - w.val| is q - 1.
  -- But we also need to handle the case where one is 0 and one is near p (wrap-around).

  -- Simpler argument: if floor(u) = floor(w), they're both "retracted" to the same
  -- interval. The interval containing any element y (with floor x) is [x.val, ...].
  -- Since consecutive X elements are spaced by ≤ q + 1, and q appears in at most
  -- one interval, excluding q gives distMod ≤ q - 1 < q.

  -- Use the helper lemma for the key structural claim
  by_cases h : u.val ≤ w.val
  · -- u.val ≤ w.val: use floor_same_implies_val_diff_lt_q
    have hdiff := floor_same_implies_val_diff_lt_q p q p' q' hq h2q hcoprime hp'_pos hp'_lt
      hq'_pos hq'_lt hbezout u w hu_ne_q hw_ne_q huw h hsame
    have hval : (w - u).val = w.val - u.val := ZMod.val_sub h
    rw [distMod_comm]
    simp only [distMod, hval]
    rw [min_def]
    split_ifs with hcmp
    · exact hdiff
    · have hp_sub : p - (w.val - u.val) > q := by omega
      omega
  · -- w.val < u.val: symmetric case
    push_neg at h
    have hdiff := floor_same_implies_val_diff_lt_q p q p' q' hq h2q hcoprime hp'_pos hp'_lt
      hq'_pos hq'_lt hbezout w u hw_ne_q hu_ne_q (huw.symm) (le_of_lt h) hsame.symm
    have hval : (u - w).val = u.val - w.val := ZMod.val_sub (le_of_lt h)
    simp only [distMod, hval]
    rw [min_def]
    split_ifs with hcmp
    · exact hdiff
    · have hp_sub : p - (u.val - w.val) > q := by omega
      omega
lemma floorInWindingSubset_eq_self (p q p' : ℕ) [NeZero p] (_hp'_pos : 0 < p')
    (x : ZMod p) (hx : x ∈ windingSubset p q p') :
    floorInWindingSubset p q p' x = x := by
  -- floor is the max element ≤ x, and x itself is a candidate.
  unfold floorInWindingSubset
  have hx_cand : x ∈ (windingSubset p q p').filter (fun z => z.val ≤ x.val) := by
    rw [Finset.mem_filter]
    exact ⟨hx, le_rfl⟩
  have hne : ((windingSubset p q p').filter (fun z => z.val ≤ x.val)).Nonempty := ⟨x, hx_cand⟩
  have hle : (maxValElement p (windingSubset p q p') x.val).val ≤ x.val :=
    maxValElement_val_le p _ _ hne
  have hge : (maxValElement p (windingSubset p q p') x.val).val ≥ x.val :=
    maxValElement_val_ge p _ _ hne x hx le_rfl
  apply ZMod.val_injective p
  omega

lemma distMod_floor_lt_q (p q p' q' : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (hp'_pos : 0 < p') (hp'_lt : p' < p) (hq'_pos : 0 < q') (hq'_lt : q' < q)
    (hbezout : p * q' - q * p' = 1)
    (y : ZMod p) (hy : y ≠ (q : ZMod p)) :
    distMod p y (floorInWindingSubset p q p' y) < q := by
  by_cases hfy : y = floorInWindingSubset p q p' y
  · -- y equals its floor, so distMod(y, y) = 0 < q
    have : distMod p y (floorInWindingSubset p q p' y) = distMod p y y := by rw [← hfy]
    rw [this]
    simp only [distMod, sub_self, ZMod.val_zero]
    omega
  · -- y and its floor share the same floor, so they are adjacent
    have hfloor_mem : floorInWindingSubset p q p' y ∈ windingSubset p q p' :=
      floorInWindingSubset_mem p q p' hp'_pos y
    have hq_not_mem : (q : ZMod p) ∉ windingSubset p q p' :=
      q_not_mem_windingSubset p q p' q' hq h2q hcoprime hp'_pos hp'_lt hq'_pos hq'_lt hbezout
    have hfy_ne_q : floorInWindingSubset p q p' y ≠ (q : ZMod p) := by
      intro hq_eq
      exact hq_not_mem (hq_eq ▸ hfloor_mem)
    have hsame : floorInWindingSubset p q p' y =
        floorInWindingSubset p q p' (floorInWindingSubset p q p' y) := by
      -- floor of an element of X is itself
      exact (floorInWindingSubset_eq_self p q p' hp'_pos _ hfloor_mem).symm
    have hadj := same_floor_adjacent p q p' q' hq h2q hcoprime hp'_pos hp'_lt
      hq'_pos hq'_lt hbezout y (floorInWindingSubset p q p' y) hy hfy_ne_q hfy hsame
    simpa [distMod_comm] using hadj

lemma floorInWindingSubset_mono (p q p' : ℕ) [NeZero p] (hp'_pos : 0 < p')
    (u w : ZMod p) (h : u.val ≤ w.val) :
    (floorInWindingSubset p q p' u).val ≤ (floorInWindingSubset p q p' w).val := by
  -- floor(u) is the max X element ≤ u.val
  -- floor(w) is the max X element ≤ w.val
  -- Since u.val ≤ w.val, floor(u) is a candidate for floor(w), so floor(u).val ≤ floor(w).val
  unfold floorInWindingSubset
  have h0 : (0 : ZMod p) ∈ windingSubset p q p' := zero_mem_windingSubset p q p' hp'_pos
  have h0_cand_u : (0 : ZMod p) ∈ (windingSubset p q p').filter (fun x => x.val ≤ u.val) := by
    rw [Finset.mem_filter]
    exact ⟨h0, by simp [ZMod.val_zero]⟩
  have hne_u : ((windingSubset p q p').filter (fun x => x.val ≤ u.val)).Nonempty := ⟨0, h0_cand_u⟩
  have h0_cand_w : (0 : ZMod p) ∈ (windingSubset p q p').filter (fun x => x.val ≤ w.val) := by
    rw [Finset.mem_filter]
    exact ⟨h0, by simp [ZMod.val_zero]⟩
  have hne_w : ((windingSubset p q p').filter (fun x => x.val ≤ w.val)).Nonempty := ⟨0, h0_cand_w⟩
  -- maxValElement for u is a candidate for w
  have hfu_le : (maxValElement p (windingSubset p q p') u.val).val ≤ u.val :=
    maxValElement_val_le p _ _ hne_u
  have hfu_mem : maxValElement p (windingSubset p q p') u.val ∈ windingSubset p q p' :=
    maxValElement_mem p _ _ hne_u
  have hfu_le_w : (maxValElement p (windingSubset p q p') u.val).val ≤ w.val := by omega
  -- So floor(u) is a candidate for the max at w
  exact maxValElement_val_ge p _ _ hne_w _ hfu_mem hfu_le_w


end AsymptoticSpectrumDistance
