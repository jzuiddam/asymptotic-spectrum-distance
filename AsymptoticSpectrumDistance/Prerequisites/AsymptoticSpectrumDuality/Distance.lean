/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumDuality.SpectrumDuality
import Mathlib.Topology.UniformSpace.Dini

/-!
# Abstract Asymptotic Spectrum Distance

This file defines the asymptotic spectrum distance on a preordered semiring
and proves its basic properties, an alternative characterization via the
asymptotic preorder, convergence of rank/subrank, and an abstract Dini theorem.

## Main Definitions

* `abstractAsympSpecDistance` : d(a,b) = sup_{F ∈ X} |F(a) - F(b)|
* `AbstractConvergesTo` : convergence in the asymptotic spectrum distance

## Main Results

* `abstractAsympSpecDistance_self` : d(a,a) = 0
* `abstractAsympSpecDistance_symm` : d(a,b) = d(b,a)
* `abstractAsympSpecDistance_nonneg` : 0 ≤ d(a,b)
* `abstractAsympSpecDistance_triangle` : d(a,c) ≤ d(a,b) + d(b,c)
* `abstractAsympSpecDistance_alt_char` : Lemma A.4: d(a,b) ≤ n/m ↔ asymptotic bounds
* `abstractAsympSpecDistance_rank_conv` : Lemma A.5: convergence implies rank convergence
* `abstract_dini_convergence` : Lemma A.6: monotone pointwise → uniform convergence

## References

* de Boer, Buys, Zuiddam, Distance in the asymptotic spectrum of graphs, Appendix A
-/

-- Suppress stylistic warnings
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.emptyLine false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.cdot false
set_option linter.style.show false
set_option linter.unreachableTactic false

namespace AsymptoticSpectrumDuality

open scoped NNReal ENNReal Topology

variable {S : Type*} [CommSemiring S]
variable (p : StrassenPreorder S)

/-! ### Definition A.3: Asymptotic Spectrum Distance -/

/-- The set of spectral distances between a and b. -/
def abstractSpectralDistanceSet (a b : S) : Set ℝ :=
  {x | ∃ φ : AsymptoticSpectrum p, x = |AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ|}

/-- Definition A.3: The asymptotic spectrum distance.
    d(a, b) = sup_{F ∈ X} |F(a) - F(b)| -/
noncomputable def abstractAsympSpecDistance (a b : S) : ℝ :=
  sSup (abstractSpectralDistanceSet p a b)

/-! ### Basic Properties -/

/-- The distance from an element to itself is zero. -/
theorem abstractAsympSpecDistance_self [Nonempty (AsymptoticSpectrum p)] (a : S) :
    abstractAsympSpecDistance p a a = 0 := by
  simp only [abstractAsympSpecDistance, abstractSpectralDistanceSet]
  have h : {x | ∃ φ : AsymptoticSpectrum p, x = |AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p a φ|} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, sub_self, abs_zero, Set.mem_singleton_iff]
    constructor
    · intro ⟨_, hx⟩; exact hx
    · intro hx; exact ⟨‹Nonempty _›.some, hx⟩
  simp only [h]
  exact csSup_singleton 0

/-- The distance is symmetric. -/
theorem abstractAsympSpecDistance_symm (a b : S) :
    abstractAsympSpecDistance p a b = abstractAsympSpecDistance p b a := by
  simp only [abstractAsympSpecDistance, abstractSpectralDistanceSet]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨φ, hφ⟩; exact ⟨φ, by rw [abs_sub_comm]; exact hφ⟩
  · intro ⟨φ, hφ⟩; exact ⟨φ, by rw [abs_sub_comm]; exact hφ⟩

/-- The distance is non-negative. -/
theorem abstractAsympSpecDistance_nonneg [Nonempty (AsymptoticSpectrum p)] (a b : S) :
    0 ≤ abstractAsympSpecDistance p a b := by
  simp only [abstractAsympSpecDistance, abstractSpectralDistanceSet]
  apply Real.sSup_nonneg
  intro x ⟨_, hφ⟩
  rw [hφ]
  exact abs_nonneg _

/-- Any spectral value difference is bounded by the distance. -/
theorem abstractSpectralPoint_dist_le [Nonempty (AsymptoticSpectrum p)]
    (a b : S) (φ : AsymptoticSpectrum p) :
    |AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ| ≤
    abstractAsympSpecDistance p a b := by
  apply le_csSup
  · -- Bounded above by rank a + rank b
    use p.rank a + p.rank b
    intro x ⟨ψ, hψ⟩
    rw [hψ]
    calc |AsymptoticSpectrum.eval p a ψ - AsymptoticSpectrum.eval p b ψ|
        ≤ |AsymptoticSpectrum.eval p a ψ| + |AsymptoticSpectrum.eval p b ψ| := abs_sub _ _
      _ = AsymptoticSpectrum.eval p a ψ + AsymptoticSpectrum.eval p b ψ := by
          rw [abs_of_nonneg (AsymptoticSpectrum.eval_nonneg p ψ a),
              abs_of_nonneg (AsymptoticSpectrum.eval_nonneg p ψ b)]
      _ ≤ p.rank a + p.rank b := by
          apply add_le_add
          · exact AsymptoticSpectrum.eval_le_rank p ψ a
          · exact AsymptoticSpectrum.eval_le_rank p ψ b
  · exact ⟨φ, rfl⟩

/-- The distance set is bounded above. -/
theorem abstractAsympSpecDistance_bdd_above (a b : S) :
    BddAbove (abstractSpectralDistanceSet p a b) := by
  use p.rank a + p.rank b
  intro x ⟨ψ, hψ⟩
  rw [hψ]
  calc |AsymptoticSpectrum.eval p a ψ - AsymptoticSpectrum.eval p b ψ|
      ≤ |AsymptoticSpectrum.eval p a ψ| + |AsymptoticSpectrum.eval p b ψ| := abs_sub _ _
    _ = AsymptoticSpectrum.eval p a ψ + AsymptoticSpectrum.eval p b ψ := by
        rw [abs_of_nonneg (AsymptoticSpectrum.eval_nonneg p ψ a),
            abs_of_nonneg (AsymptoticSpectrum.eval_nonneg p ψ b)]
    _ ≤ p.rank a + p.rank b := by
        apply add_le_add
        · exact AsymptoticSpectrum.eval_le_rank p ψ a
        · exact AsymptoticSpectrum.eval_le_rank p ψ b

/-- Triangle inequality for the asymptotic spectrum distance. -/
theorem abstractAsympSpecDistance_triangle [Nonempty (AsymptoticSpectrum p)]
    (a b c : S) :
    abstractAsympSpecDistance p a c ≤
    abstractAsympSpecDistance p a b + abstractAsympSpecDistance p b c := by
  simp only [abstractAsympSpecDistance, abstractSpectralDistanceSet]
  apply csSup_le
  · obtain ⟨φ₀⟩ := ‹Nonempty (AsymptoticSpectrum p)›
    exact ⟨|AsymptoticSpectrum.eval p a φ₀ - AsymptoticSpectrum.eval p c φ₀|, φ₀, rfl⟩
  · intro x ⟨φ, hφ⟩
    rw [hφ]
    calc |AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p c φ|
        = |(AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ) +
           (AsymptoticSpectrum.eval p b φ - AsymptoticSpectrum.eval p c φ)| := by ring_nf
      _ ≤ |AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ| +
          |AsymptoticSpectrum.eval p b φ - AsymptoticSpectrum.eval p c φ| :=
          abs_add_le _ _
      _ ≤ sSup {x | ∃ ψ : AsymptoticSpectrum p, x = |AsymptoticSpectrum.eval p a ψ - AsymptoticSpectrum.eval p b ψ|} +
          sSup {x | ∃ ψ : AsymptoticSpectrum p, x = |AsymptoticSpectrum.eval p b ψ - AsymptoticSpectrum.eval p c ψ|} := by
          apply add_le_add
          · apply le_csSup (abstractAsympSpecDistance_bdd_above p a b)
            exact ⟨φ, rfl⟩
          · apply le_csSup (abstractAsympSpecDistance_bdd_above p b c)
            exact ⟨φ, rfl⟩

/-! ### Convergence -/

/-- A sequence converges to b if the abstract distance goes to 0. -/
def AbstractConvergesTo (as : ℕ → S) (b : S) : Prop :=
  Filter.Tendsto (fun n => abstractAsympSpecDistance p (as n) b) Filter.atTop (nhds 0)

/-! ### Lemma A.4: Alternative Characterization -/

/-- Helper: φ(n • a) = n * φ(a) for spectral points. -/
private theorem eval_nsmul (φ : AsymptoticSpectrum p) (n : ℕ) (a : S) :
    AsymptoticSpectrum.eval p (n • a) φ = n * AsymptoticSpectrum.eval p a φ := by
  induction n with
  | zero => simp only [zero_smul, AsymptoticSpectrum.eval, φ.map_zero, Nat.cast_zero, zero_mul]
  | succ n ih =>
    simp only [succ_nsmul, AsymptoticSpectrum.eval, φ.map_add]
    rw [show φ.toFun (n • a) = AsymptoticSpectrum.eval p (n • a) φ from rfl,
        show φ.toFun a = AsymptoticSpectrum.eval p a φ from rfl]
    rw [ih]
    push_cast
    ring

/-- Helper: φ(a + (n : S)) = φ(a) + n for spectral points. -/
private theorem eval_add_natCast (φ : AsymptoticSpectrum p) (a : S) (n : ℕ) :
    AsymptoticSpectrum.eval p (a + (n : S)) φ =
    AsymptoticSpectrum.eval p a φ + n := by
  simp only [AsymptoticSpectrum.eval, φ.map_add]
  rw [show φ.toFun a = AsymptoticSpectrum.eval p a φ from rfl,
      show φ.toFun (n : S) = AsymptoticSpectrum.eval p (n : S) φ from rfl,
      AsymptoticSpectrum.eval_natCast]

/-- Lemma A.4: Alternative characterization of the asymptotic spectrum distance.
    d(a,b) ≤ n/m ↔ m•a ≲ m•b + n and m•b ≲ m•a + n

    Reference: Appendix A, Lemma A.4. -/
theorem abstractAsympSpecDistance_alt_char [Nonempty (AsymptoticSpectrum p)]
    (a b : S) (n m : ℕ) (hm : 0 < m) :
    abstractAsympSpecDistance p a b ≤ (n : ℝ) / m ↔
      (AsympRel p (m • a) (m • b + (n : S)) ∧
       AsympRel p (m • b) (m • a + (n : S))) := by
  constructor
  · -- Forward: d(a,b) ≤ n/m → asymptotic bounds
    intro hdist
    constructor
    · -- m•a ≲ m•b + n
      rw [p.asympRel_iff_forall_spectrum]
      intro φ
      rw [eval_nsmul, eval_add_natCast, eval_nsmul]
      have hφ : AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ ≤ (n : ℝ) / m := by
        have hbound := abstractSpectralPoint_dist_le p a b φ
        have hab : |AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ| ≤ (n : ℝ) / m :=
          le_trans hbound hdist
        exact (abs_le.mp hab).2
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have hmul : (m : ℝ) * (AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ) ≤ n := by
        calc (m : ℝ) * (AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ)
            ≤ m * ((n : ℝ) / m) := by apply mul_le_mul_of_nonneg_left hφ (le_of_lt hm_pos)
          _ = n := by field_simp
      linarith
    · -- m•b ≲ m•a + n
      rw [p.asympRel_iff_forall_spectrum]
      intro φ
      rw [eval_nsmul, eval_add_natCast, eval_nsmul]
      have hφ : AsymptoticSpectrum.eval p b φ - AsymptoticSpectrum.eval p a φ ≤ (n : ℝ) / m := by
        have hbound := abstractSpectralPoint_dist_le p a b φ
        have hab : |AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ| ≤ (n : ℝ) / m :=
          le_trans hbound hdist
        have hab' := (abs_le.mp hab).1
        linarith
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have hmul : (m : ℝ) * (AsymptoticSpectrum.eval p b φ - AsymptoticSpectrum.eval p a φ) ≤ n := by
        calc (m : ℝ) * (AsymptoticSpectrum.eval p b φ - AsymptoticSpectrum.eval p a φ)
            ≤ m * ((n : ℝ) / m) := by apply mul_le_mul_of_nonneg_left hφ (le_of_lt hm_pos)
          _ = n := by field_simp
      linarith
  · -- Reverse: asymptotic bounds → d(a,b) ≤ n/m
    intro ⟨h1, h2⟩
    apply csSup_le
    · obtain ⟨φ₀⟩ := ‹Nonempty (AsymptoticSpectrum p)›
      exact ⟨|AsymptoticSpectrum.eval p a φ₀ - AsymptoticSpectrum.eval p b φ₀|, φ₀, rfl⟩
    · intro x ⟨φ, hφ⟩
      rw [hφ]
      rw [p.asympRel_iff_forall_spectrum] at h1 h2
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have h1' := h1 φ
      have h2' := h2 φ
      rw [eval_nsmul, eval_add_natCast, eval_nsmul] at h1'
      rw [eval_nsmul, eval_add_natCast, eval_nsmul] at h2'
      have hGH : AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ ≤ (n : ℝ) / m := by
        have hmul : (m : ℝ) * (AsymptoticSpectrum.eval p a φ - AsymptoticSpectrum.eval p b φ) ≤ n := by linarith
        rw [le_div_iff₀ hm_pos]
        linarith
      have hHG : AsymptoticSpectrum.eval p b φ - AsymptoticSpectrum.eval p a φ ≤ (n : ℝ) / m := by
        have hmul : (m : ℝ) * (AsymptoticSpectrum.eval p b φ - AsymptoticSpectrum.eval p a φ) ≤ n := by linarith
        rw [le_div_iff₀ hm_pos]
        linarith
      rw [abs_le]
      constructor <;> linarith

/-! ### Lemma A.5: Convergence of Asymptotic Rank and Subrank -/

/-- Lemma A.5 (rank part): If a_i → b in asymptotic spectrum distance,
    then asympRank(a_i) → asympRank(b).

    Proof: uniform convergence of spectral evaluation functions on compact
    spectrum implies convergence of maxima. Uses asympRank = max over spectrum.

    Reference: Appendix A, Lemma A.5. -/
theorem abstractAsympSpecDistance_rank_conv [Nonempty (AsymptoticSpectrum p)]
    (as : ℕ → S) (b : S)
    (hb : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p b φ)
    (hconv : AbstractConvergesTo p as b) :
    Filter.Tendsto (fun n => p.asympRank (as n)) Filter.atTop
      (nhds (p.asympRank b)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get N such that d(as n, b) < ε/2
  have hε2 : ε / 2 > 0 := half_pos hε
  rw [show AbstractConvergesTo p as b =
    Filter.Tendsto (fun n => abstractAsympSpecDistance p (as n) b)
      Filter.atTop (nhds 0) from rfl] at hconv
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv (ε / 2) hε2
  use N
  intro n hn
  rw [Real.dist_eq]
  have hdist_n : abstractAsympSpecDistance p (as n) b < ε / 2 := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (abstractAsympSpecDistance_nonneg p _ _)] at h
    exact h
  -- For each φ: |φ(as n) - φ(b)| ≤ d(as n, b) < ε/2
  -- Lower bound: asympRank(as n) ≥ φ(as n) ≥ φ(b) - ε/2 for all φ
  -- In particular for φ* achieving max for b: asympRank(as n) ≥ asympRank(b) - ε/2
  obtain ⟨φmax, hφmax⟩ := p.asympRank_eq_max_spectrum b hb
  have h_lower : p.asympRank (as n) ≥ p.asympRank b - ε / 2 := by
    have habs := abstractSpectralPoint_dist_le p (as n) b φmax
    have hrank_le := StrassenPreorder.spectralPoint_le_asympRank p φmax (as n)
    -- |φmax(as n) - φmax(b)| ≤ d(as n, b) < ε/2
    -- So φmax(as n) ≥ φmax(b) - ε/2 = asympRank(b) - ε/2
    have habs_bound : |AsymptoticSpectrum.eval p (as n) φmax - AsymptoticSpectrum.eval p b φmax| < ε / 2 :=
      lt_of_le_of_lt habs hdist_n
    have := (abs_le.mp (le_of_lt habs_bound)).1
    linarith [hφmax]
  -- Upper bound: use spectral duality to bound rank(as n^k)
  -- For all φ: φ(as n) ≤ φ(b) + ε/2 ≤ asympRank(b) + ε/2
  -- So AsympRel p (as n^k) (M_k : S) where M_k = ⌈(asympRank(b) + ε/2)^k⌉ + 1
  -- Then asympRank(as n)^k ≤ M_k ≤ (asympRank(b) + ε/2)^k + 2
  -- Taking k-th root → asympRank(b) + ε/2 as k → ∞
  have h_upper : p.asympRank (as n) ≤ p.asympRank b + ε / 2 := by
    -- Step 1: bound all spectral evaluations
    have heval_bound : ∀ φ : AsymptoticSpectrum p,
        AsymptoticSpectrum.eval p (as n) φ ≤ p.asympRank b + ε / 2 := by
      intro φ
      have habs := abstractSpectralPoint_dist_le p (as n) b φ
      have hle_rank := StrassenPreorder.spectralPoint_le_asympRank p φ b
      have habs_lt : |AsymptoticSpectrum.eval p (as n) φ - AsymptoticSpectrum.eval p b φ| < ε / 2 :=
        lt_of_le_of_lt habs hdist_n
      have := (abs_le.mp (le_of_lt habs_lt)).2
      linarith
    -- Step 2: set s = asympRank(b) + ε/2 ≥ 1 + ε/2 > 1
    set s := p.asympRank b + ε / 2 with hs_def
    -- s ≥ 1 from the hypothesis
    have hs_ge1 : 1 ≤ s := by
      obtain ⟨φ, hφ⟩ := hb
      have := StrassenPreorder.spectralPoint_le_asympRank p φ b
      linarith
    have hs_pos : 0 < s := lt_of_lt_of_le one_pos hs_ge1
    have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
    -- Step 3: for each k ≥ 1, bound asympRank(as n)^k
    have hkey : ∀ k : ℕ, k ≥ 1 → p.asympRank (as n) ≤ (s ^ k + 2 : ℝ) ^ (1 / k : ℝ) := by
      intro k hk
      set M_k := Nat.ceil (s ^ k) + 1 with hM_k_def
      have hM_k_pos : 0 < M_k := Nat.add_one_pos _
      have hs_lt_Mk : s ^ k < (M_k : ℝ) := by
        have hceil : s ^ k ≤ Nat.ceil (s ^ k) := Nat.le_ceil (s ^ k)
        have hM_k_eq : (M_k : ℝ) = Nat.ceil (s ^ k) + 1 := by exact_mod_cast rfl
        linarith
      -- For all φ: φ(as n)^k ≤ s^k < M_k
      have hasymp : AsympRel p ((as n) ^ k) (M_k : S) := by
        rw [p.asympRel_iff_forall_spectrum]
        intro φ
        have h1 := heval_bound φ
        have heval_nn := AsymptoticSpectrum.eval_nonneg p φ (as n)
        have h2 : AsymptoticSpectrum.eval p (as n) φ ^ k ≤ s ^ k := by
          gcongr
        simp only [AsymptoticSpectrum.eval_pow, AsymptoticSpectrum.eval_natCast]
        linarith
      have h1 := StrassenPreorder.asympRank_mono p hasymp
      have h2 : p.asympRank (M_k : S) = M_k := StrassenPreorder.asympRank_natCast p M_k hM_k_pos
      have h3 : p.asympRank (as n) ^ k = p.asympRank ((as n) ^ k) := (StrassenPreorder.asympRank_pow p (as n) k).symm
      have hM_k_le : (M_k : ℝ) ≤ s ^ k + 2 := by
        have hspow_nonneg : 0 ≤ s ^ k := pow_nonneg hs_nonneg k
        have hceil_le : (Nat.ceil (s ^ k) : ℝ) ≤ s ^ k + 1 := by
          have h1 : (Nat.ceil (s ^ k) : ℝ) ≤ Nat.floor (s ^ k) + 1 := by
            exact_mod_cast Nat.ceil_le_floor_add_one (s ^ k)
          linarith [Nat.floor_le hspow_nonneg]
        have hM_k_eq : (M_k : ℝ) = Nat.ceil (s ^ k) + 1 := by exact_mod_cast rfl
        linarith
      have hasymprk_pow_le : p.asympRank (as n) ^ k ≤ s ^ k + 2 := by
        calc p.asympRank (as n) ^ k = p.asympRank ((as n) ^ k) := h3
          _ ≤ p.asympRank (M_k : S) := h1
          _ = M_k := h2
          _ ≤ s ^ k + 2 := hM_k_le
      have hk_pos : (0 : ℝ) < k :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk))
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have hasymprk_nonneg : 0 ≤ p.asympRank (as n) := StrassenPreorder.asympRank_nonneg p (as n)
      have hexp_nonneg : 0 ≤ (1 : ℝ) / k := div_nonneg (by norm_num) (le_of_lt hk_pos)
      calc p.asympRank (as n)
          = (p.asympRank (as n) ^ k) ^ (1 / k : ℝ) := by
            rw [← Real.rpow_natCast (p.asympRank (as n)) k, ← Real.rpow_mul hasymprk_nonneg,
                mul_one_div_cancel hk_ne, Real.rpow_one]
        _ ≤ (s ^ k + 2) ^ (1 / k : ℝ) := by
            apply Real.rpow_le_rpow (pow_nonneg hasymprk_nonneg k) hasymprk_pow_le hexp_nonneg
    -- Step 4: (s^k + 2)^{1/k} → s as k → ∞
    have htendsto : Filter.Tendsto (fun k : ℕ => (s ^ k + 2 : ℝ) ^ (1 / k : ℝ))
        Filter.atTop (nhds s) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      · -- Upper bound: (s^k + 2)^{1/k} ≤ 3^{1/k} * s → s
        have hupper : Filter.Tendsto (fun k : ℕ => (3 : ℝ) ^ (1 / k : ℝ) * s)
            Filter.atTop (nhds (1 * s)) := by
          apply Filter.Tendsto.mul _ tendsto_const_nhds
          have h1 : Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ))) Filter.atTop (nhds 0) := by
            simp only [one_div]
            exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
          have hcont : ContinuousAt (fun y : ℝ => (3 : ℝ) ^ y) 0 :=
            Real.continuousAt_const_rpow (by norm_num : (3 : ℝ) ≠ 0)
          have hcomp := hcont.tendsto.comp h1
          simp only [one_div, Real.rpow_zero] at hcomp ⊢
          exact hcomp
        rw [one_mul] at hupper
        exact hupper
      · -- Lower: s ≤ (s^k + 2)^{1/k}
        filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        have hk_pos : (0 : ℝ) < k :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk))
        have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
        have hexp_nonneg : 0 ≤ (1 : ℝ) / k := div_nonneg (by norm_num) (le_of_lt hk_pos)
        calc s = (s ^ k) ^ (1 / k : ℝ) := by
              rw [← Real.rpow_natCast s k, ← Real.rpow_mul hs_nonneg,
                  mul_one_div_cancel hk_ne, Real.rpow_one]
          _ ≤ (s ^ k + 2) ^ (1 / k : ℝ) := by
              apply Real.rpow_le_rpow (pow_nonneg hs_nonneg k) (by linarith) hexp_nonneg
      · -- Upper: (s^k + 2)^{1/k} ≤ 3^{1/k} * s when s^k ≥ 1
        filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        have hk_pos : (0 : ℝ) < k :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk))
        have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
        have hexp_nonneg : 0 ≤ (1 : ℝ) / k := div_nonneg (by norm_num) (le_of_lt hk_pos)
        have hspow_ge1 : 1 ≤ s ^ k := one_le_pow₀ hs_ge1
        have hspow_nonneg : 0 ≤ s ^ k := pow_nonneg hs_nonneg k
        calc (s ^ k + 2 : ℝ) ^ (1 / k : ℝ)
            ≤ (s ^ k + 2 * s ^ k : ℝ) ^ (1 / k : ℝ) := by
              apply Real.rpow_le_rpow (by linarith) (by linarith) hexp_nonneg
          _ = (3 * s ^ k : ℝ) ^ (1 / k : ℝ) := by ring_nf
          _ = (3 : ℝ) ^ (1 / k : ℝ) * (s ^ k : ℝ) ^ (1 / k : ℝ) := by
              rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hspow_nonneg]
          _ = (3 : ℝ) ^ (1 / k : ℝ) * s := by
              congr 1
              rw [← Real.rpow_natCast s k, ← Real.rpow_mul hs_nonneg,
                  mul_one_div_cancel hk_ne, Real.rpow_one]
    exact ge_of_tendsto htendsto (Filter.eventually_atTop.mpr ⟨1, fun k hk => hkey k hk⟩)
  -- Combine
  calc |p.asympRank (as n) - p.asympRank b|
      ≤ ε / 2 := by rw [abs_le]; constructor <;> linarith
    _ < ε := half_lt_self hε

/-- Lemma A.5 (subrank part): If a_i → b in asymptotic spectrum distance,
    then asympSubrank(a_i) → asympSubrank(b).

    Uses the spectral characterization asympSubrank = min over spectrum
    for gapped elements (Theorem A.1(iv)).

    The paper assumes the Strassen preorder satisfies condition (⋄),
    meaning all elements are gapped, so both b and as(n) admit
    the min characterization. -/
theorem abstractAsympSpecDistance_subrank_conv [Nonempty (AsymptoticSpectrum p)]
    (as : ℕ → S) (b : S)
    (hb_gapped : p.IsGapped b)
    (has_gapped : ∀ n, p.IsGapped (as n))
    (hconv : AbstractConvergesTo p as b) :
    Filter.Tendsto (fun n => p.asympSubrank (as n)) Filter.atTop
      (nhds (p.asympSubrank b)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [show AbstractConvergesTo p as b =
    Filter.Tendsto (fun n => abstractAsympSpecDistance p (as n) b)
      Filter.atTop (nhds 0) from rfl] at hconv
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv ε hε
  use N
  intro n hn
  rw [Real.dist_eq]
  have hdist_n : abstractAsympSpecDistance p (as n) b < ε := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (abstractAsympSpecDistance_nonneg p _ _)] at h
    exact h
  -- Get spectral points achieving the min for b and as n
  obtain ⟨φmin_b, hφmin_b⟩ := p.asympSubrank_eq_min_spectrum b hb_gapped
  obtain ⟨φmin_n, hφmin_n⟩ := p.asympSubrank_eq_min_spectrum (as n) (has_gapped n)
  -- Upper bound: asympSubrank(as n) < asympSubrank(b) + ε
  have h_upper : p.asympSubrank (as n) < p.asympSubrank b + ε := by
    have habs := abstractSpectralPoint_dist_le p (as n) b φmin_b
    have habs_lt := lt_of_le_of_lt habs hdist_n
    have := (abs_lt.mp habs_lt).2
    have hsub_le := StrassenPreorder.asympSubrank_le_spectralPoint p φmin_b (as n)
    linarith [hφmin_b]
  -- Lower bound: asympSubrank(as n) > asympSubrank(b) - ε
  have h_lower : p.asympSubrank (as n) > p.asympSubrank b - ε := by
    have habs := abstractSpectralPoint_dist_le p (as n) b φmin_n
    have habs_lt := lt_of_le_of_lt habs hdist_n
    have := (abs_lt.mp habs_lt).1
    have hsub_le := StrassenPreorder.asympSubrank_le_spectralPoint p φmin_n b
    linarith [hφmin_n]
  -- Combine
  rw [abs_lt]
  constructor <;> linarith

/-! ### Lemma A.6: Abstract Dini's Theorem -/

/-- Lemma A.6 (Abstract Dini's theorem): If for every F ∈ X, the sequence
    F(a₁), F(a₂), ... is monotone and converges to F(b), then
    a₁, a₂, ... converges to b in asymptotic spectrum distance.

    Reference: Appendix A, Lemma A.6. -/
theorem abstract_dini_convergence [Nonempty (AsymptoticSpectrum p)]
    (as : ℕ → S) (b : S)
    (hmono : (∀ F : AsymptoticSpectrum p, Monotone (fun n => AsymptoticSpectrum.eval p (as n) F)) ∨
             (∀ F : AsymptoticSpectrum p, Antitone (fun n => AsymptoticSpectrum.eval p (as n) F)))
    (hptwise : ∀ F : AsymptoticSpectrum p,
      Filter.Tendsto (fun n => AsymptoticSpectrum.eval p (as n) F) Filter.atTop
        (nhds (AsymptoticSpectrum.eval p b F))) :
    AbstractConvergesTo p as b := by
  -- Define the evaluation functions on the abstract spectrum
  let G : ℕ → AsymptoticSpectrum p → ℝ := fun n φ => AsymptoticSpectrum.eval p (as n) φ
  let g : AsymptoticSpectrum p → ℝ := fun φ => AsymptoticSpectrum.eval p b φ
  -- The abstract spectrum is compact
  have hcompact : IsCompact (Set.univ : Set (AsymptoticSpectrum p)) :=
    AsymptoticSpectrum.isCompact p
  -- Evaluation is continuous
  have hG_cont : ∀ n, Continuous (G n) := fun n =>
    AsymptoticSpectrum.continuous_eval p _
  have hg_cont : Continuous g := AsymptoticSpectrum.continuous_eval p _
  -- Apply Dini's theorem
  have hunif : TendstoUniformlyOn G g Filter.atTop Set.univ := by
    rcases hmono with hmono_inc | hmono_dec
    · exact Monotone.tendstoUniformlyOn_of_forall_tendsto hcompact
        (fun n => (hG_cont n).continuousOn) (fun x _ => hmono_inc x)
        hg_cont.continuousOn (fun x _ => hptwise x)
    · exact Antitone.tendstoUniformlyOn_of_forall_tendsto hcompact
        (fun n => (hG_cont n).continuousOn) (fun x _ => hmono_dec x)
        hg_cont.continuousOn (fun x _ => hptwise x)
  -- Convert uniform convergence to AbstractConvergesTo (distance → 0)
  show Filter.Tendsto (fun n => abstractAsympSpecDistance p (as n) b) Filter.atTop (nhds 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : ε / 2 > 0 := half_pos hε
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  have hunif_ε := hunif (ε / 2) hε2
  obtain ⟨N, hN⟩ := hunif_ε.exists_forall_of_atTop
  use N
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (abstractAsympSpecDistance_nonneg p _ _)]
  have hN' := hN n hn
  calc abstractAsympSpecDistance p (as n) b
      = sSup (abstractSpectralDistanceSet p (as n) b) := rfl
    _ ≤ ε / 2 := by
        apply csSup_le
        · obtain ⟨φ₀⟩ := ‹Nonempty (AsymptoticSpectrum p)›
          exact ⟨|AsymptoticSpectrum.eval p (as n) φ₀ - AsymptoticSpectrum.eval p b φ₀|, φ₀, rfl⟩
        · intro x ⟨φ, hφ⟩
          rw [hφ]
          have hspec := hN' φ (Set.mem_univ _)
          rw [Real.dist_eq, abs_sub_comm] at hspec
          exact le_of_lt hspec
    _ < ε := half_lt_self hε

end AsymptoticSpectrumDuality
