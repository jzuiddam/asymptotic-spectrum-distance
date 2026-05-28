/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section3.Convergence
import AsymptoticSpectrumDistance.Section4.CircleGraphs
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.AsympSpecDistanceInf
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.Embedding
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.Specialization
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphOperations
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphSemiring
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphStrassenPreorder
import Mathlib.NumberTheory.Real.Irrational

/-!
# Circle Graphs as Limits of Fraction Graphs

This file contains the proofs of Section-4 results that relate fraction graphs
to circle graphs as limits, including:

* Theorem 4.11 (`circleGraph_asymp_equiv_irrational`): For irrational `r`, the
  closed and open circle graphs `E_r^c` and `E_r^o` are asymptotically equivalent.
* Theorem 4.11(b) (`fractionGraph_convergesToInf_circleGraph`): Fraction graphs
  `E_{p_n / q_n}` with `p_n / q_n → r` (irrational) converge to `E_r^o`.
* Theorem 4.12 TFAE (`theorem_4_12_tfae`, `theorem_4_12_tfae_with_r`):
  the five equivalent characterisations of left-continuity at a rational `r > 2`.
* The sequential-closure equality
  `seqClosure fractionGraphSet = openCircleGraphSet_specEq` under the Theorem 4.12
  hypothesis.
* `converges_to_circleGraph`, the `ℕ+`-paper-form wrapper used by Main.lean.

Historically these proofs lived in `Section3/Convergence.lean`; they have been
relocated here so that the Section-3 file no longer needs to depend on
`Section4/CircleGraphs.lean`, restoring the paper's Section-3 ↦ Section-4
dependency direction.

## References

* [de Boer, Buys, Zuiddam] Section 4
-/

set_option linter.style.longLine false

namespace AsymptoticSpectrumDistance

open Universality FractionGraphBasic AsymptoticSpectrumGraphs SimpleGraph ShannonCapacity

/-! ### Asymptotic Spectrum Distance for Infinite Graphs

The generic infrastructure (`asympSpecDistanceInf`, `ConvergesToInf`,
`convergesToInf_of_uniform_bound`) now lives in
`Prerequisites/AsymptoticSpectrumInfiniteGraphs/AsympSpecDistanceInf.lean`.
The two theorems below remain here because they reference the finite-graph
distance from `Section2/Basic.lean`. -/

open AsymptoticSpectrumInfiniteGraphs

/-- The infinite graph distance between embedded finite graphs is at most
    the finite graph distance. -/
theorem asympSpecDistanceInf_embed_le (G H : Graph) :
    asympSpecDistanceInf (graphToInfiniteGraph G) (graphToInfiniteGraph H) ≤
    asympSpecDistance G H := by
  unfold asympSpecDistanceInf asympSpecDistance spectralDistanceSet
  apply csSup_le
  · obtain ⟨ψ, _⟩ := restriction_surjective chibar_spectralPoint
    exact ⟨_, ψ, rfl⟩
  · rintro x ⟨ψ, rfl⟩
    have : |ψ.eval (graphToInfiniteGraph G) - ψ.eval (graphToInfiniteGraph H)| =
      |(restrictionMap ψ).eval G - (restrictionMap ψ).eval H| := rfl
    rw [this]
    exact spectralPoint_dist_le G H (restrictionMap ψ)

/-- Sandwich bound: if E_{a/b} ≤ G ≤ E_{c/d} (via cohomomorphisms in the infinite
    graph setting), then d_∞(G, E_r^o) ≤ d(E_{a/b}, E_{c/d}) for any r with
    E_{a/b} ≤ E_r^o ≤ E_{c/d}. -/
theorem asympSpecDistanceInf_sandwich (G : InfiniteGraph)
    (a b c d : ℕ) [NeZero a] [NeZero c]
    (_hb : 0 < b) (_hd : 0 < d) (_h2b : 2 * b ≤ a) (_h2d : 2 * d ≤ c)
    (r : ℝ) (hr : 2 ≤ r)
    (_hab_lt : (a : ℝ) / b < r) (_hcd_gt : r < (c : ℝ) / d)
    (hlo : ∀ ψ : SpectralPointInf,
      ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) ≤ ψ.eval G)
    (hhi : ∀ ψ : SpectralPointInf,
      ψ.eval G ≤ ψ.eval (graphToInfiniteGraph (FractionGraph' c d)))
    (hlo_r : ∀ ψ : SpectralPointInf,
      ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) ≤
      ψ.eval (circleGraphOpenInf r hr))
    (hhi_r : ∀ ψ : SpectralPointInf,
      ψ.eval (circleGraphOpenInf r hr) ≤
      ψ.eval (graphToInfiniteGraph (FractionGraph' c d))) :
    asympSpecDistanceInf G (circleGraphOpenInf r hr) ≤
    asympSpecDistance (FractionGraph' a b) (FractionGraph' c d) := by
  unfold asympSpecDistanceInf
  apply csSup_le
  · obtain ⟨ψ, _⟩ := restriction_surjective chibar_spectralPoint
    exact ⟨_, ψ, rfl⟩
  · rintro x ⟨ψ, rfl⟩
    have h1 := hlo ψ; have h2 := hhi ψ
    have h3 := hlo_r ψ; have h4 := hhi_r ψ
    have hbound : |ψ.eval G - ψ.eval (circleGraphOpenInf r hr)| ≤
        ψ.eval (graphToInfiniteGraph (FractionGraph' c d)) -
        ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) := by
      rw [abs_le]; constructor <;> linarith
    set φ := restrictionMap ψ
    have hφ : ∀ X, φ.eval X = ψ.eval (graphToInfiniteGraph X) := fun _ => rfl
    calc |ψ.eval G - ψ.eval (circleGraphOpenInf r hr)|
        ≤ ψ.eval (graphToInfiniteGraph (FractionGraph' c d)) -
          ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) := hbound
      _ = |φ.eval (FractionGraph' c d) - φ.eval (FractionGraph' a b)| := by
          have := hφ (FractionGraph' a b)
          have := hφ (FractionGraph' c d)
          rw [abs_of_nonneg (by linarith)]; linarith
      _ ≤ asympSpecDistance (FractionGraph' a b) (FractionGraph' c d) := by
          rw [asympSpecDistance_symm]; exact spectralPoint_dist_le _ _ φ

/-! ### Circle Graphs as Limits: Infinite Graph Spectral Theory -/

/-- Fraction graph as InfiniteGraph equals graphToInfiniteGraph applied to FractionGraph. -/
theorem fractionGraphInf_eq (p q : ℕ) [NeZero p] :
    graphToInfiniteGraph (FractionGraph' p q) =
    { V := ZMod p, graph := fractionGraph p q,
      cliqueCover_finite :=
        (graphToInfiniteGraph (FractionGraph' p q)).cliqueCover_finite } := rfl

/-- SpectralPointInf monotonicity: fraction graph below closed circle graph.
    For a/b < r, the embedding E_{a/b} → E_r^c gives ψ(E_{a/b}) ≤ ψ(E_r^c). -/
theorem spectralPointInf_fraction_le_closed (r : ℝ) (hr : 2 ≤ r)
    (ψ : SpectralPointInf)
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    (hlt : (p : ℝ) / q < r) :
    ψ.eval (graphToInfiniteGraph (FractionGraph' p q)) ≤
    ψ.eval (circleGraphClosedInf r hr) := by
  apply ψ.mono_cohom
  -- Need: Cohom (fractionGraph p q) (circleGraphClosed r hr)
  -- Chain: fractionGraph p q → circleGraphOpen (p/q) → circleGraphClosed r
  have hr_pq : 2 ≤ (p : ℝ) / q := by
    have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    calc (2 : ℝ) = 2 * q / q := by field_simp
      _ ≤ p / q := by apply div_le_div_of_nonneg_right (by exact_mod_cast h2q) (le_of_lt hq')
  exact Cohom.trans (fractionGraph_to_circleGraphOpen p q hq h2q)
    (circleGraph_mono ((p : ℝ) / q) r hr_pq hr hlt).2.1

/-- SpectralPointInf monotonicity: open circle graph below fraction graph.
    For r < c/d, the identity E_r^o → E_{c/d}^c → E_{c/d} gives ψ(E_r^o) ≤ ψ(E_{c/d}). -/
theorem spectralPointInf_open_le_fraction (r : ℝ) (hr : 2 ≤ r)
    (ψ : SpectralPointInf)
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    (hgt : r < (p : ℝ) / q) :
    ψ.eval (circleGraphOpenInf r hr) ≤
    ψ.eval (graphToInfiniteGraph (FractionGraph' p q)) := by
  apply ψ.mono_cohom
  -- Chain: circleGraphOpen r → circleGraphClosed (p/q) → circleGraphOpen (p/q) → fractionGraph p q
  have hr_pq : 2 ≤ (p : ℝ) / q := by
    have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    calc (2 : ℝ) = 2 * q / q := by field_simp
      _ ≤ p / q := by apply div_le_div_of_nonneg_right (by exact_mod_cast h2q) (le_of_lt hq')
  exact Cohom.trans (Cohom.trans (circleGraph_mono r ((p : ℝ) / q) hr hr_pq hgt).2.1
    (circleGraphClosed_le_open ((p : ℝ) / q) hr_pq))
    (circleGraphOpen_to_fractionGraph p q hq h2q)

/-- SpectralPointInf monotonicity: closed circle graph below open circle graph.
    E_r^c ≤ E_r^o via identity. -/
theorem spectralPointInf_closed_le_open (r : ℝ) (hr : 2 ≤ r)
    (ψ : SpectralPointInf) :
    ψ.eval (circleGraphClosedInf r hr) ≤ ψ.eval (circleGraphOpenInf r hr) := by
  apply ψ.mono_cohom
  exact circleGraphClosed_le_open r hr

/-- Theorem 4.11(a): For irrational r ≥ 2, every SpectralPointInf assigns the same value
    to E_r^c and E_r^o. In particular, E_r^c and E_r^o are asymptotically equivalent.

    Proof: For any a/b < r < c/d:
      ψ(E_{a/b}) ≤ ψ(E_r^c) ≤ ψ(E_r^o) ≤ ψ(E_{c/d})
    By restriction_surjective, ψ restricted to finite graphs is some φ : SpectralPoint.
    By fractionGraph_sup_eq_inf_irrational, sup = inf, so ψ(E_r^c) = ψ(E_r^o). -/
theorem circleGraph_asymp_equiv_irrational (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) :
    ∀ ψ : SpectralPointInf,
      ψ.eval (circleGraphClosedInf r hr) = ψ.eval (circleGraphOpenInf r hr) := by
  intro ψ
  apply le_antisymm (spectralPointInf_closed_le_open r hr ψ)
  -- Need: ψ(E_r^o) ≤ ψ(E_r^c)
  -- Strategy: squeeze between fraction graphs and use spectral bounds
  set φ := restrictionMap ψ
  by_contra h
  push_neg at h
  set gap := ψ.eval (circleGraphOpenInf r hr) - ψ.eval (circleGraphClosedInf r hr) with hgap_def
  have hgap_pos : 0 < gap := by linarith [spectralPointInf_closed_le_open r hr ψ]
  have hr' : 2 < r := by
    apply lt_of_le_of_ne hr
    intro h; exact hirr ⟨2, by simp [h]⟩
  -- Pick M large enough that ⌈r⌉/(M+1) < gap
  obtain ⟨M, hM⟩ := exists_nat_gt ((Nat.ceil r : ℝ) / gap)
  -- Get convergent pair (a/b, a1/b1) with a1 ≥ M + 2
  obtain ⟨n, a, b, a1, b1, ha, hb, ha1, hb1, h2b, h2b1, hratio, hratio1,
      hdet, hb_lt, hN_le_a1, _⟩ :=
    even_odd_convergent_pair_data_large r hr' hirr (M + 2)
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  haveI : NeZero a1 := ⟨Nat.pos_iff_ne_zero.mp ha1⟩
  have hlt : (a : ℝ) / b < r := by
    have := convergent_even_lt_irrational r hirr n; simpa [hratio] using this
  have hgt : r < (a1 : ℝ) / b1 := by
    calc r < (r.convergent (2 * n + 1) : ℝ) := convergent_odd_gt_irrational r hirr n
      _ = (a1 : ℝ) / b1 := hratio1
  -- Sandwich: ψ(E_{a/b}) ≤ ψ(E_r^c) ≤ ψ(E_r^o) ≤ ψ(E_{a1/b1})
  have h_lo := spectralPointInf_fraction_le_closed r hr ψ a b hb h2b hlt
  have h_hi := spectralPointInf_open_le_fraction r hr ψ a1 b1 hb1 h2b1 hgt
  -- gap ≤ φ(E_{a1/b1}) - φ(E_{a/b}) since φ.eval = ψ.eval ∘ graphToInfiniteGraph by rfl
  have hgap_le : gap ≤ φ.eval (FractionGraph' a1 b1) -
      φ.eval (FractionGraph' a b) := by
    change _ ≤ ψ.eval (graphToInfiniteGraph _) - ψ.eval (graphToInfiniteGraph _)
    simp only [hgap_def]; linarith
  -- Show a < a1 (from determinant and b < b1)
  have ha_lt_a1 : a < a1 := by
    have hb_ltZ : (b : ℤ) < (b1 : ℤ) := by exact_mod_cast hb_lt
    have ha_posZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
    have hmul_lt : (b : ℤ) * (a : ℤ) < (b1 : ℤ) * (a : ℤ) :=
      mul_lt_mul_of_pos_right hb_ltZ ha_posZ
    have hle : b1 * a ≤ a1 * b := by omega
    have hdetZ : (a1 : ℤ) * (b : ℤ) = (b1 : ℤ) * (a : ℤ) + 1 := by
      have hdetZ' : (a1 : ℤ) * (b : ℤ) - (b1 : ℤ) * (a : ℤ) = 1 := by
        have hdetZ'' := congrArg (fun t : ℕ => (t : ℤ)) hdet
        simpa [Int.ofNat_sub hle] using hdetZ''
      linarith
    have hmul_lt' : (a : ℤ) * (b : ℤ) < (a1 : ℤ) * (b : ℤ) := by linarith [hdetZ, hmul_lt]
    have hb_nonneg : (0 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (Nat.zero_le b)
    exact_mod_cast (lt_of_mul_lt_mul_right hmul_lt' hb_nonneg)
  -- Spectral bounds: φ(E_{a/b}) ≤ φ(E_{a1/b1}) ≤ (a1/(a1-1)) * φ(E_{a/b})
  obtain ⟨_, hhi_b⟩ :=
    fractionGraph_spectral_bounds a1 b1 a b hb1 hb h2b1 h2b ha_lt_a1 hb_lt hdet φ
  have ha1_gt1 : 1 < a1 := by omega
  -- Bound φ(E_{a/b}) ≤ ⌈r⌉ (since a/b < r ≤ ⌈r⌉/1 and ordering gives cohomomorphism)
  have hceil_ge : 2 ≤ Nat.ceil r := by exact_mod_cast (le_trans hr (Nat.le_ceil r))
  haveI : NeZero (Nat.ceil r) := ⟨by omega⟩
  have hφ_upper : φ.eval (FractionGraph' a b) ≤ (Nat.ceil r : ℝ) := by
    have hle_rat : (a : ℚ) / b ≤ (Nat.ceil r : ℚ) / 1 := by
      apply (Rat.cast_le (K := ℝ)).1
      simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_one]
      have : (↑a : ℝ) / ↑b ≤ ↑⌈r⌉₊ := le_of_lt (lt_of_lt_of_le hlt (Nat.le_ceil r))
      linarith
    have hcohom := (fractionGraph_ordering a b (Nat.ceil r) 1 hb (by omega) h2b
      (by simpa using hceil_ge)).mp hle_rat
    exact le_trans (φ.mono_cohom _ _ (by simpa using hcohom))
      (fractionGraph_spectral_le_vertices (Nat.ceil r) 1 (by omega) φ)
  -- Combine: diff ≤ (1/(a1-1)) * φ(E_{a/b}) ≤ ⌈r⌉/(a1-1)
  have hden_pos : (0 : ℝ) < (a1 : ℝ) - 1 := by
    have : (1 : ℝ) < a1 := by exact_mod_cast ha1_gt1
    linarith
  have hdiff_bound : φ.eval (FractionGraph' a1 b1) -
      φ.eval (FractionGraph' a b) ≤
      (Nat.ceil r : ℝ) / ((a1 : ℝ) - 1) := by
    calc φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)
        ≤ (a1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) -
          φ.eval (FractionGraph' a b) := by linarith
      _ = (1 / ((a1 : ℝ) - 1)) * φ.eval (FractionGraph' a b) := by
          field_simp; ring
      _ ≤ (1 / ((a1 : ℝ) - 1)) * (Nat.ceil r : ℝ) := by
          apply mul_le_mul_of_nonneg_left hφ_upper
          exact le_of_lt (one_div_pos.mpr hden_pos)
      _ = (Nat.ceil r : ℝ) / ((a1 : ℝ) - 1) := by ring
  -- ⌈r⌉/(a1-1) ≤ ⌈r⌉/(M+1) < gap since a1 ≥ M+2
  have hM_le : (M : ℝ) + 1 ≤ (a1 : ℝ) - 1 := by
    have : (M : ℝ) + 2 ≤ (a1 : ℝ) := by exact_mod_cast hN_le_a1
    linarith
  have hM_pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hfinal : (Nat.ceil r : ℝ) / ((a1 : ℝ) - 1) < gap := by
    calc (Nat.ceil r : ℝ) / ((a1 : ℝ) - 1)
        ≤ (Nat.ceil r : ℝ) / ((M : ℝ) + 1) := by
          exact div_le_div_of_nonneg_left (by positivity) hM_pos hM_le
      _ < gap := by
          rw [div_lt_iff₀ hM_pos]
          have : (Nat.ceil r : ℝ) / gap < (M : ℝ) + 1 := by linarith [hM]
          linarith [(div_lt_iff₀ hgap_pos).mp this]
  linarith

/-- The supremum of spectral values below an irrational r equals the circle graph
    evaluation: sup_{a/b < r} φ(E_{a/b}) = ψ(E_r^o) where φ = restrictionMap ψ. -/
theorem sup_spectral_eq_circleGraph_eval (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ψ : SpectralPointInf) :
    sSup {x | ∃ a b : ℕ, ∃ (ha : 0 < a),
      0 < b ∧ 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
      x = (restrictionMap ψ).eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} =
    ψ.eval (circleGraphOpenInf r hr) := by
  set φ := restrictionMap ψ
  -- Reuse the existing proof infrastructure
  have hr' : 2 < r := by
    apply lt_of_le_of_ne hr
    intro h; exact hirr ⟨2, by simp [h]⟩
  obtain ⟨n0, a0, b0, a1, b1, ha0, hb0, ha1, hb1, h2b0, h2b1, hratio0, hratio1,
      _, _, _⟩ := even_odd_convergent_pair_data_large r hr' hirr 1
  have hlt0 : (a0 : ℝ) / b0 < r := by
    simpa [hratio0] using convergent_even_lt_irrational r hirr n0
  have hgt1 : r < (a1 : ℝ) / b1 := by
    calc r < (r.convergent (2 * n0 + 1) : ℝ) := convergent_odd_gt_irrational r hirr n0
      _ = (a1 : ℝ) / b1 := hratio1
  have hne_below : Set.Nonempty {x | ∃ a b : ℕ, ∃ (ha : 0 < a),
      0 < b ∧ 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
      x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} :=
    ⟨_, a0, b0, ha0, hb0, h2b0, hlt0, rfl⟩
  have hne_above : Set.Nonempty {x | ∃ a b : ℕ, ∃ (ha : 0 < a),
      0 < b ∧ 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
      x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} :=
    ⟨_, a1, b1, ha1, hb1, h2b1, hgt1, rfl⟩
  apply le_antisymm
  · -- sSup ≤ ψ(E_r^o): every fraction a/b < r has φ(E_{a/b}) ≤ ψ(E_r^o)
    apply csSup_le hne_below
    rintro x ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    change ψ.eval (graphToInfiniteGraph _) ≤ _
    have h1 := spectralPointInf_fraction_le_closed r hr ψ a b hb h2b hlt
    have h2 := (circleGraph_asymp_equiv_irrational r hr hirr ψ).symm
    linarith
  · -- ψ(E_r^o) ≤ sSup: ψ(E_r^o) ≤ sInf{above} = sSup{below}
    rw [fractionGraph_sup_eq_inf_irrational r hr hirr φ]
    apply le_csInf hne_above
    rintro x ⟨a, b, ha, hb, h2b, hgt, rfl⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    change _ ≤ ψ.eval (graphToInfiniteGraph _)
    exact spectralPointInf_open_le_fraction r hr ψ a b hb h2b hgt

/-- Theorem 4.11(a), `ℕ+` form / four-way equality:
    `ψ(E_r^c) = ψ(E_r^o) = sup_{a/b < r} φ(E_{a/b}) = inf_{c/d > r} φ(E_{c/d})`,
    indexed over `ℕ+ × ℕ+`. -/
theorem circleGraph_four_way_pnat (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ψ : SpectralPointInf) :
    let φ := restrictionMap ψ
    let S_below := sSup {x | ∃ (a b : ℕ+),
      2 * b ≤ a ∧ (a : ℝ) / b < r ∧
      x = φ (FractionGraph a b)}
    let S_above := sInf {x | ∃ (a b : ℕ+),
      2 * b ≤ a ∧ (a : ℝ) / b > r ∧
      x = φ (FractionGraph a b)}
    ψ (circleGraphClosedInf r hr) = S_below ∧
    ψ (circleGraphOpenInf r hr) = S_below ∧
    S_below = S_above := by
  set φ := restrictionMap ψ
  have hset_below : {x | ∃ (a b : ℕ+),
      2 * b ≤ a ∧ (a : ℝ) / b < r ∧
      x = φ (FractionGraph a b)} =
    {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      (a : ℝ) / b < r ∧
      x = φ (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} := by
    ext x; constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hlt, rfl⟩
      exact ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    · rintro ⟨a, b, ha, hb, h2b, hlt, rfl⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hlt, rfl⟩
  have hset_above : {x | ∃ (a b : ℕ+),
      2 * b ≤ a ∧ (a : ℝ) / b > r ∧
      x = φ (FractionGraph a b)} =
    {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      (a : ℝ) / b > r ∧
      x = φ (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} := by
    ext x; constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hgt, rfl⟩
      exact ⟨a, b, ha, hb, h2b, hgt, rfl⟩
    · rintro ⟨a, b, ha, hb, h2b, hgt, rfl⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hgt, rfl⟩
  simp only [hset_below, hset_above]
  refine ⟨?_, ?_, ?_⟩
  · rw [circleGraph_asymp_equiv_irrational r hr hirr ψ]
    exact (sup_spectral_eq_circleGraph_eval r hr hirr ψ).symm
  · exact (sup_spectral_eq_circleGraph_eval r hr hirr ψ).symm
  · exact fractionGraph_sup_eq_inf_irrational r hr hirr φ

/-- Theorem 4.11(b): If p_n/q_n → r (irrational), then φ(E_{p_n/q_n}) → L(φ)
    where L(φ) = sup_{a/b < r} φ(E_{a/b}) = ψ(E_r^o). -/
theorem fractionGraph_converges_to_circleGraph (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ps qs : ℕ → ℕ) [∀ n, NeZero (ps n)]
    (hqs_pos : ∀ n, 0 < qs n)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℝ) / qs n) Filter.atTop (nhds r)) :
    ∀ φ : SpectralPoint,
      Filter.Tendsto (fun n => φ.eval (FractionGraph' (ps n) (qs n)))
        Filter.atTop (nhds (sSup {x | ∃ a b : ℕ, ∃ (ha : 0 < a),
          0 < b ∧ 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
          x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)})) := by
  classical
  intro φ
  set L := sSup {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
    (a : ℝ) / b < r ∧ x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)}
  -- L = sInf{above} by fractionGraph_sup_eq_inf_irrational
  have hL_eq : L = sInf {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      (a : ℝ) / b > r ∧ x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} :=
    fractionGraph_sup_eq_inf_irrational r hr hirr φ
  have hr' : 2 < r := by
    apply lt_of_le_of_ne hr
    intro h
    exact hirr ⟨2, by simp [h]⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 1: Pick M so that ceil(r)/M < ε
  obtain ⟨M, hM⟩ := exists_nat_gt ((Nat.ceil r : ℝ) / ε)
  have hM_pos : 0 < M := by
    have : (0 : ℝ) < (M : ℝ) := by
      have h0 : (0 : ℝ) ≤ (Nat.ceil r : ℝ) / ε :=
        div_nonneg (by exact_mod_cast (Nat.zero_le _)) (le_of_lt hε)
      linarith
    exact_mod_cast this
  have hM_bound : (Nat.ceil r : ℝ) / (M : ℝ) < ε := by
    have hM'' : (Nat.ceil r : ℝ) / ε < (M : ℝ) := by exact_mod_cast hM
    have hM' : (Nat.ceil r : ℝ) < (M : ℝ) * ε := (div_lt_iff₀ hε).1 hM''
    have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    exact (div_lt_iff₀ hM_pos').2 (by linarith [mul_comm (M : ℝ) ε])
  -- Step 2: Get convergent pair a/b < r < a1/b1 with a1 ≥ M+1
  obtain ⟨n, a, b, a1, b1, ha, hb, ha1, hb1, h2b, h2b1, hratio, hratio1,
      hdet, hb_lt, hN_le_a1, _⟩ :=
    even_odd_convergent_pair_data_large r hr' hirr (M + 1)
  have hlt : (a : ℝ) / b < r := by
    have := convergent_even_lt_irrational r hirr n
    simpa [hratio] using this
  have hgt : r < (a1 : ℝ) / b1 := by
    calc r < (r.convergent (2 * n + 1) : ℝ) := convergent_odd_gt_irrational r hirr n
      _ = (a1 : ℝ) / b1 := by simpa [Real.convergent] using hratio1
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  haveI : NeZero a1 := ⟨Nat.pos_iff_ne_zero.mp ha1⟩
  -- Step 3: Bound φ(E_{a1/b1}) - φ(E_{a/b}) < ε
  have ha_lt : a < a1 := by
    have hb_ltZ : (b : ℤ) < (b1 : ℤ) := by exact_mod_cast hb_lt
    have ha_posZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
    have hmul_lt : (b : ℤ) * (a : ℤ) < (b1 : ℤ) * (a : ℤ) :=
      mul_lt_mul_of_pos_right hb_ltZ ha_posZ
    have hdetZ : (a1 : ℤ) * (b : ℤ) = (b1 : ℤ) * (a : ℤ) + 1 := by
      have hle : b1 * a ≤ a1 * b := by omega
      have hdetZ' : (a1 : ℤ) * (b : ℤ) - (b1 : ℤ) * (a : ℤ) = 1 := by
        have hdetZ'' := congrArg (fun t : ℕ => (t : ℤ)) hdet
        simpa [Int.ofNat_sub hle] using hdetZ''
      linarith
    have hmul_lt' : (a : ℤ) * (b : ℤ) < (a1 : ℤ) * (b : ℤ) := by linarith [hdetZ, hmul_lt]
    have hb_nonneg : (0 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (Nat.zero_le b)
    exact_mod_cast (lt_of_mul_lt_mul_right hmul_lt' hb_nonneg)
  have hbounds := fractionGraph_spectral_bounds a1 b1 a b hb1 hb h2b1 h2b ha_lt hb_lt hdet φ
  obtain ⟨hlo_bound, hhi_bound⟩ := hbounds
  have hdiff_nonneg :
      0 ≤ φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) := by linarith
  have ha1_gt : 1 < a1 := by omega
  have hdiff_bound :
      φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) ≤
        (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := by
    have : (a1 : ℝ) / (a1 - 1) - 1 = 1 / (a1 - 1) := by
      have hden_ne : (a1 : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < a1 := by exact_mod_cast ha1_gt
        linarith
      field_simp [hden_ne]; ring
    calc φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)
        ≤ (a1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) -
          φ.eval (FractionGraph' a b) := by linarith
      _ = ((a1 : ℝ) / (a1 - 1) - 1) * φ.eval (FractionGraph' a b) := by ring
      _ = (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := by rw [this]
  have hupper_bound : φ.eval (FractionGraph' a b) ≤ (Nat.ceil r : ℝ) := by
    have hceil : r ≤ (Nat.ceil r : ℝ) := by exact_mod_cast (Nat.le_ceil r)
    have hle' : (a : ℝ) / b ≤ (Nat.ceil r : ℝ) := by linarith [hlt, hceil]
    have hr_le : (a : ℚ) / b ≤ (Nat.ceil r : ℚ) / 1 := by
      apply (Rat.cast_le (K := ℝ)).1; simpa using hle'
    have hceil_ge : 2 ≤ Nat.ceil r := by
      exact_mod_cast (le_trans hr hceil)
    haveI : NeZero (Nat.ceil r) := ⟨by omega⟩
    have hcohom :=
      (fractionGraph_ordering a b (Nat.ceil r) 1 hb (by omega) h2b (by
        simpa using hceil_ge)).mp hr_le
    exact le_trans
      (φ.mono_cohom _ _ (by simpa using hcohom))
      (fractionGraph_spectral_le_vertices (Nat.ceil r) 1 (by omega) φ)
  have hdiff_bound' :
      φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) ≤
        (Nat.ceil r : ℝ) / (a1 - 1) := by
    calc φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b)
        ≤ (1 : ℝ) / (a1 - 1) * φ.eval (FractionGraph' a b) := hdiff_bound
      _ ≤ (1 : ℝ) / (a1 - 1) * (Nat.ceil r : ℝ) := by
        apply mul_le_mul_of_nonneg_left hupper_bound
        exact le_of_lt (one_div_pos.mpr (by
          have : (1 : ℝ) < a1 := by exact_mod_cast ha1_gt
          linarith))
      _ = (Nat.ceil r : ℝ) / (a1 - 1) := by ring
  have hratio_bound : (Nat.ceil r : ℝ) / (a1 - 1) ≤ (Nat.ceil r : ℝ) / (M : ℝ) := by
    have hM_le : (M : ℝ) ≤ (a1 : ℝ) - 1 := by
      have : (M : ℝ) + 1 ≤ (a1 : ℝ) := by exact_mod_cast hN_le_a1
      linarith
    exact div_le_div_of_nonneg_left
      (by exact_mod_cast (Nat.zero_le _))
      (by exact_mod_cast hM_pos) hM_le
  have hgap_lt : φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) < ε :=
    lt_of_le_of_lt (le_trans hdiff_bound' hratio_bound) hM_bound
  -- Step 4: L is between φ(E_{a/b}) and φ(E_{a1/b1})
  have hbelow_mem : φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) ∈
      {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
        x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} :=
    ⟨a, b, ha, hb, h2b, hlt, rfl⟩
  have habove_mem : φ.eval (@FractionGraph' a1 b1 ⟨Nat.pos_iff_ne_zero.mp ha1⟩) ∈
      {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
        x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} :=
    ⟨a1, b1, ha1, hb1, h2b1, hgt, rfl⟩
  -- BddAbove for the below set
  have hbdd_above : BddAbove {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      (a : ℝ) / b < r ∧ x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} := by
    refine ⟨φ.eval (@FractionGraph' a1 b1 ⟨Nat.pos_iff_ne_zero.mp ha1⟩), ?_⟩
    intro x hx
    rcases hx with ⟨a', b', ha', hb', h2b', hlt', rfl⟩
    haveI : NeZero a' := ⟨Nat.pos_iff_ne_zero.mp ha'⟩
    have hle : (a' : ℚ) / b' ≤ (a1 : ℚ) / b1 := by
      apply (Rat.cast_le (K := ℝ)).1
      simpa using (le_of_lt (lt_trans hlt' hgt))
    have hcoh := (fractionGraph_ordering a' b' a1 b1 hb' hb1 h2b' h2b1).mp hle
    exact φ.mono_cohom _ _ (by simpa using hcoh)
  have hL_ge : φ.eval (FractionGraph' a b) ≤ L :=
    le_csSup hbdd_above hbelow_mem
  -- BddBelow for the above set
  have hbdd_below : BddBelow {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      (a : ℝ) / b > r ∧ x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} := by
    refine ⟨φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩), ?_⟩
    intro x hx
    rcases hx with ⟨a', b', ha', hb', h2b', hgt', rfl⟩
    haveI : NeZero a' := ⟨Nat.pos_iff_ne_zero.mp ha'⟩
    have hle : (a : ℚ) / b ≤ (a' : ℚ) / b' := by
      apply (Rat.cast_le (K := ℝ)).1
      simpa using (le_of_lt (lt_trans hlt hgt'))
    have hcoh := (fractionGraph_ordering a b a' b' hb hb' h2b h2b').mp hle
    exact φ.mono_cohom _ _ (by simpa using hcoh)
  have hL_le : L ≤ φ.eval (FractionGraph' a1 b1) := by
    rw [hL_eq]
    exact csInf_le hbdd_below habove_mem
  -- Step 5: Set δ and get N from convergence
  set δ : ℝ := min (r - (a : ℝ) / b) ((a1 : ℝ) / b1 - r) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv δ hδ_pos
  -- Step 6: For n ≥ N, show |φ(E_{ps n/qs n}) - L| < ε
  refine ⟨N, fun n hn => ?_⟩
  have hdist_n := hN n hn
  rw [Real.dist_eq] at hdist_n
  have habs := abs_lt.mp hdist_n
  have hδ_le_left : δ ≤ r - (a : ℝ) / b := min_le_left _ _
  have hδ_le_right : δ ≤ (a1 : ℝ) / b1 - r := min_le_right _ _
  -- ps n / qs n is between a/b and a1/b1
  have h_between : (a : ℝ) / b ≤ (ps n : ℝ) / qs n ∧ (ps n : ℝ) / qs n ≤ (a1 : ℝ) / b1 := by
    constructor
    · linarith [habs.1, hδ_le_left]
    · linarith [habs.2, hδ_le_right]
  -- Convert to rational ordering for cohomomorphisms
  have hrat_le : (a : ℚ) / b ≤ (ps n : ℚ) / qs n := by
    apply (Rat.cast_le (K := ℝ)).1; simpa using h_between.1
  have hrat_le' : (ps n : ℚ) / qs n ≤ (a1 : ℚ) / b1 := by
    apply (Rat.cast_le (K := ℝ)).1; simpa using h_between.2
  -- Monotonicity: φ(E_{a/b}) ≤ φ(E_{ps n/qs n}) ≤ φ(E_{a1/b1})
  have hcohom_lo : Cohom (fractionGraph a b) (fractionGraph (ps n) (qs n)) :=
    (fractionGraph_ordering a b (ps n) (qs n) hb (hqs_pos n) h2b (h2qs n)).mp hrat_le
  have heval_lo : φ.eval (FractionGraph' a b) ≤ φ.eval (FractionGraph' (ps n) (qs n)) :=
    φ.mono_cohom _ _ hcohom_lo
  have hcohom_hi : Cohom (fractionGraph (ps n) (qs n)) (fractionGraph a1 b1) :=
    (fractionGraph_ordering (ps n) (qs n) a1 b1 (hqs_pos n) hb1 (h2qs n) h2b1).mp hrat_le'
  have heval_hi : φ.eval (FractionGraph' (ps n) (qs n)) ≤ φ.eval (FractionGraph' a1 b1) :=
    φ.mono_cohom _ _ hcohom_hi
  -- Both L and φ(E_{ps n/qs n}) are in [φ(E_{a/b}), φ(E_{a1/b1})]
  rw [Real.dist_eq]
  have h1 : φ.eval (FractionGraph' (ps n) (qs n)) - L ≤
      φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) := by
    linarith [heval_hi, hL_ge]
  have h2 : L - φ.eval (FractionGraph' (ps n) (qs n)) ≤
      φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) := by
    linarith [heval_lo, hL_le]
  calc |φ.eval (FractionGraph' (ps n) (qs n)) - L|
      ≤ φ.eval (FractionGraph' a1 b1) - φ.eval (FractionGraph' a b) :=
        abs_sub_le_iff.mpr ⟨h1, h2⟩
    _ < ε := hgap_lt

/-- Theorem 4.11(b): For irrational r ≥ 2, if p_n/q_n → r, then E_{p_n/q_n}
    converges to E_r^o in the infinite graph asymptotic spectrum distance.
    Proof: sandwich argument — both E_{p_n/q_n} and E_r^o lie between
    E_{a/b} and E_{c/d} for convergents a/b < r < c/d, giving
    d_∞(E_{p_n/q_n}, E_r^o) ≤ d(E_{a/b}, E_{c/d}) < ε. -/
theorem fractionGraph_convergesToInf_circleGraph (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ps qs : ℕ → ℕ) [∀ n, NeZero (ps n)]
    (hqs_pos : ∀ n, 0 < qs n)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℝ) / qs n) Filter.atTop (nhds r)) :
    ConvergesToInf
      (fun n => graphToInfiniteGraph (FractionGraph' (ps n) (qs n)))
      (circleGraphOpenInf r hr) := by
  apply convergesToInf_of_uniform_bound
  intro ε hε
  have hr' : 2 < r := lt_of_le_of_ne hr (fun h => hirr ⟨2, by simp [h]⟩)
  obtain ⟨δ, hδ_pos, hδ⟩ := fractionGraph_uniform_continuity_irrational r hr hirr ε hε
  -- Pick convergent pair a/b < r < c/d within δ of r
  have hconv_r := tendsto_convergent_real r
  rw [Metric.tendsto_atTop] at hconv_r
  obtain ⟨K, hK⟩ := hconv_r δ (by exact_mod_cast hδ_pos)
  obtain ⟨n0, a, b, c, d0, ha, hb, hc, hd, h2b, h2d, hratio_a, hratio_c,
      _, _, _, hK_le_2n0⟩ := even_odd_convergent_pair_data_large r hr' hirr K
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  haveI : NeZero c := ⟨Nat.pos_iff_ne_zero.mp hc⟩
  have hab_lt : (a : ℝ) / b < r := by
    simpa [hratio_a] using convergent_even_lt_irrational r hirr n0
  have hcd_gt : r < (c : ℝ) / d0 := by
    calc r < (r.convergent (2 * n0 + 1) : ℝ) := convergent_odd_gt_irrational r hirr n0
      _ = (c : ℝ) / d0 := hratio_c
  -- Both a/b and c/d are fractions ≥ 2 within distance < ε of each other
  -- by fractionGraph_spectral_bounds (Stern-Brocot neighbors)
  -- The convergent pair is within δ of r for large enough index
  -- (convergents approach r by tendsto_convergent_real)
  have hab_near : |(a : ℝ) / b - r| < δ := by
    have h := hK (2 * n0) hK_le_2n0
    rw [show (r.convergent (2 * n0) : ℝ) = (a : ℝ) / b from hratio_a] at h
    simpa [Real.dist_eq] using h
  have hcd_near : |(c : ℝ) / d0 - r| < δ := by
    have h := hK (2 * n0 + 1) (by omega)
    rw [show (r.convergent (2 * n0 + 1) : ℝ) = (c : ℝ) / d0 from hratio_c] at h
    simpa [Real.dist_eq] using h
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N₁, hN₁⟩ := hconv (r - (a : ℝ) / b) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hconv ((c : ℝ) / d0 - r) (by linarith)
  use max N₁ N₂
  intro n hn
  have hdn₁ := hN₁ n (le_of_max_le_left hn); rw [Real.dist_eq] at hdn₁
  have hdn₂ := hN₂ n (le_of_max_le_right hn); rw [Real.dist_eq] at hdn₂
  have hpn_gt : (a : ℝ) / b < (ps n : ℝ) / qs n := by linarith [abs_lt.mp hdn₁]
  have hpn_lt : (ps n : ℝ) / qs n < (c : ℝ) / d0 := by linarith [abs_lt.mp hdn₂]
  intro ψ
  set φ := restrictionMap ψ
  have hle_lo : (a : ℚ) / b ≤ (ps n : ℚ) / qs n := by
    apply (Rat.cast_le (K := ℝ)).1; push_cast; exact le_of_lt hpn_gt
  have hle_hi : (ps n : ℚ) / qs n ≤ (c : ℚ) / d0 := by
    apply (Rat.cast_le (K := ℝ)).1; push_cast; exact le_of_lt hpn_lt
  have hmono_lo := φ.mono_cohom (FractionGraph' a b) (FractionGraph' (ps n) (qs n))
    (by simpa using
      (fractionGraph_ordering a b (ps n) (qs n) hb (hqs_pos n) h2b (h2qs n)).mp hle_lo)
  have hmono_hi := φ.mono_cohom (FractionGraph' (ps n) (qs n)) (FractionGraph' c d0)
    (by simpa using
      (fractionGraph_ordering (ps n) (qs n) c d0 (hqs_pos n) hd (h2qs n) h2d).mp hle_hi)
  have hlo_r : φ.eval (FractionGraph' a b) ≤ ψ.eval (circleGraphOpenInf r hr) := by
    calc φ.eval (FractionGraph' a b)
        = ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) := rfl
      _ ≤ ψ.eval (circleGraphClosedInf r hr) :=
          spectralPointInf_fraction_le_closed r hr ψ a b hb h2b hab_lt
      _ = ψ.eval (circleGraphOpenInf r hr) :=
          circleGraph_asymp_equiv_irrational r hr hirr ψ
  have hhi_r : ψ.eval (circleGraphOpenInf r hr) ≤ φ.eval (FractionGraph' c d0) := by
    calc ψ.eval (circleGraphOpenInf r hr)
        ≤ ψ.eval (graphToInfiniteGraph (FractionGraph' c d0)) :=
          spectralPointInf_open_le_fraction r hr ψ c d0 hd h2d hcd_gt
      _ = φ.eval (FractionGraph' c d0) := rfl
  -- ψ(embed(G)) = φ(G) definitionally
  have heq_n : ψ.eval (graphToInfiniteGraph (FractionGraph' (ps n) (qs n))) =
      φ.eval (FractionGraph' (ps n) (qs n)) := rfl
  calc |ψ.eval (graphToInfiniteGraph (FractionGraph' (ps n) (qs n))) -
        ψ.eval (circleGraphOpenInf r hr)|
      ≤ φ.eval (FractionGraph' c d0) - φ.eval (FractionGraph' a b) := by
        rw [abs_le, heq_n]; constructor <;> linarith
    _ ≤ |φ.eval (FractionGraph' c d0) - φ.eval (FractionGraph' a b)| := le_abs_self _
    _ ≤ asympSpecDistance (FractionGraph' a b) (FractionGraph' c d0) := by
        rw [asympSpecDistance_symm]; exact spectralPoint_dist_le _ _ φ
    _ < ε := hδ a b c d0 ha hc hb hd h2b h2d hab_near hcd_near

/-! ### Characterization of Left-Continuity -/

/-- For rational r = p/q, the open circle graph has the same SpectralPointInf value
    as the fraction graph, since they are cohomomorphically equivalent (Lemma 4.4). -/
theorem spectralPointInf_open_eq_fraction (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) (ψ : SpectralPointInf) :
    let r : ℝ := p / q
    have hr : 2 ≤ r := by
      have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
      calc (2 : ℝ) = 2 * q / q := by field_simp
        _ ≤ p / q := div_le_div_of_nonneg_right
            (by exact_mod_cast h2q) (le_of_lt hq')
    ψ.eval (circleGraphOpenInf r hr) =
    ψ.eval (graphToInfiniteGraph (FractionGraph' p q)) := by
  have hequiv := circleGraphOpen_equiv_fractionGraph p q hq h2q
  exact le_antisymm (ψ.mono_cohom _ _ hequiv.1)
    (ψ.mono_cohom _ _ hequiv.2)

/-- Theorem 4.12 (v)⟹(i): Left-continuity of spectral values implies
    asymptotic equivalence of closed and open circle graphs.

    If sup_{a/b < p/q} φ(E_{a/b}) = φ(E_{p/q}) for all spectral points φ,
    then ψ(E_r^c) = ψ(E_r^o) for all SpectralPointInf ψ. -/
theorem leftContinuity_implies_circleGraph_asymp_equiv
    (r : ℝ) (hr : 2 ≤ r)
    (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p)
    (hr_eq : r = (p : ℝ) / q)
    (hleft : ∀ φ : SpectralPoint,
      sSup {x | ∃ a b : ℕ, ∃ (ha : 0 < a),
        0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b < r ∧
        x = φ.eval
          (@FractionGraph' a b
            ⟨Nat.pos_iff_ne_zero.mp ha⟩)} =
      φ.eval (FractionGraph' p q)) :
    ∀ ψ : SpectralPointInf,
      ψ.eval (circleGraphClosedInf r hr) =
      ψ.eval (circleGraphOpenInf r hr) := by
  subst hr_eq
  intro ψ
  apply le_antisymm
    (spectralPointInf_closed_le_open _ hr ψ)
  -- Need: ψ(E_r^o) ≤ ψ(E_r^c)
  set φ := restrictionMap ψ
  -- ψ(E_r^o) = φ(E_{p/q}) by Lemma 4.4 equivalence
  have hψ_open_eq :=
    spectralPointInf_open_eq_fraction p q hq h2q ψ
  rw [hψ_open_eq]
  -- φ(E_{p/q}) = sup_{a/b < r} φ(E_{a/b}) by hypothesis
  have hsup_eq := hleft φ
  -- φ(E_{p/q}) ≤ ψ(E_r^c) since each sup element ≤ ψ(E_r^c)
  change φ.eval (FractionGraph' p q) ≤ _
  rw [← hsup_eq]
  set S := {x | ∃ a b : ℕ, ∃ (ha : 0 < a),
    0 < b ∧ 2 * b ≤ a ∧
    (a : ℝ) / b < (p : ℝ) / q ∧
    x = φ.eval
      (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)}
  by_cases hne : S.Nonempty
  · apply csSup_le hne
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    change ψ.eval (graphToInfiniteGraph _) ≤ _
    exact spectralPointInf_fraction_le_closed _ hr ψ
      a b hb h2b hlt
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact ψ.nonneg _

/-- Theorem 4.12 (≤ direction): For rational r = p/q, the supremum of spectral values
    over smaller fractions is at most the spectral value at p/q.
    This follows from monotonicity of spectral points under cohomomorphisms. -/
theorem fractionGraph_leftContinuity_equiv (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    -- sup_{a/b < p/q} F(E_{a/b}) ≤ F(E_{p/q}) for all F ∈ X
    ∀ φ : SpectralPoint,
      sSup {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b < (p : ℝ) / q ∧
        x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} ≤
      φ.eval (FractionGraph' p q) := by
  intro φ
  set S := {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
    (a : ℝ) / b < (p : ℝ) / q ∧
    x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)}
  by_cases hne : S.Nonempty
  · -- Nonempty case: use csSup_le
    apply csSup_le hne
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    -- Convert (a : ℝ) / b < (p : ℝ) / q to (a : ℚ) / b ≤ (p : ℚ) / q
    have hle : (a : ℚ) / b ≤ (p : ℚ) / q := by
      apply (Rat.cast_le (K := ℝ)).1
      simpa using (le_of_lt hlt)
    -- Get cohomomorphism from ordering
    have hcohom := (fractionGraph_ordering a b p q hb hq h2b h2q).mp hle
    -- Apply monotonicity of spectral points
    exact φ.mono_cohom _ _ (by simpa using hcohom)
  · -- Empty case: sSup ∅ = 0 ≤ φ.eval(E_{p/q})
    rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact φ.nonneg _

/-- Left-continuity at integers: for integer n ≥ 3, the supremum of spectral values
    over fractions a/b < n is at most the spectral value at n.
    This follows from monotonicity of spectral points under cohomomorphisms. -/
theorem circleGraph_asymp_equiv_integer (n : ℕ) (hn : 3 ≤ n) :
    haveI : NeZero n := ⟨by omega⟩
    ∀ φ : SpectralPoint,
      sSup {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b < n ∧
        x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} ≤
      φ.eval (FractionGraph' n 1) := by
  haveI : NeZero n := ⟨by omega⟩
  intro φ
  set S := {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
    (a : ℝ) / b < (n : ℝ) ∧
    x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)}
  by_cases hne : S.Nonempty
  · apply csSup_le hne
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    -- Convert (a : ℝ) / b < (n : ℝ) to (a : ℚ) / b ≤ (n : ℚ) / 1
    have hlt' : (a : ℝ) / b < (n : ℝ) / 1 := by rwa [div_one]
    have hle : (a : ℚ) / b ≤ (n : ℚ) / 1 := by
      apply (Rat.cast_le (K := ℝ)).1
      simpa using (le_of_lt hlt')
    have hcohom := (fractionGraph_ordering a b n 1 hb (by omega : 0 < 1) h2b
      (by omega : 2 * 1 ≤ n)).mp hle
    exact φ.mono_cohom _ _ (by simpa using hcohom)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact φ.nonneg _

/-! The individual implications (i)⟹(ii)⟹(iii)⟹(iv)⟹(v)⟹(i) follow,
    combined into the TFAE statement `theorem_4_12_tfae` at the end. -/

/-- Theorem 4.12 (iii)⟹(iv): Uniform left-continuity implies sequential convergence.

    If for every ε > 0 there exists δ > 0 such that any fraction a/b within δ of p/q
    from below has φ(E_{p/q}) - φ(E_{a/b}) < ε uniformly in φ,
    then any sequence a_n/b_n → p/q from below has φ(E_{a_n/b_n}) → φ(E_{p/q}). -/
theorem thm47_iii_implies_iv
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    -- Condition (iii): uniform left-continuity
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ (a b : ℕ) (ha : 0 < a),
      0 < b → 2 * b ≤ a →
      0 < (p : ℝ) / q - (a : ℝ) / b →
      (p : ℝ) / q - (a : ℝ) / b < δ →
      ∀ φ : SpectralPoint,
        φ.eval (FractionGraph' p q) -
        φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) < ε)
    -- Condition (iv): sequential left-convergence
    (as bs : ℕ → ℕ) (has_pos : ∀ n, 0 < as n)
    (hbs_pos : ∀ n, 0 < bs n) (h2bs : ∀ n, 2 * bs n ≤ as n)
    (hconv : Filter.Tendsto (fun n => (as n : ℝ) / bs n)
      Filter.atTop (nhds ((p : ℝ) / q)))
    (hbelow : ∀ n, (as n : ℝ) / bs n < (p : ℝ) / q) :
    ∀ φ : SpectralPoint,
      Filter.Tendsto
        (fun n => φ.eval
          (@FractionGraph' (as n) (bs n) ⟨Nat.pos_iff_ne_zero.mp (has_pos n)⟩))
        Filter.atTop (nhds (φ.eval (FractionGraph' p q))) := by
  intro φ
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get δ from uniform left-continuity
  obtain ⟨δ, hδ, hunif_δ⟩ := hunif ε hε
  -- Get N from convergence of the sequence
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv δ hδ
  refine ⟨N, fun n hn => ?_⟩
  -- |as n / bs n - p/q| < δ, and as n / bs n < p/q
  have hconv_n := hN n hn
  have hgap_pos : 0 < (p : ℝ) / q - (as n : ℝ) / bs n := by linarith [hbelow n]
  have hgap_lt : (p : ℝ) / q - (as n : ℝ) / bs n < δ := by
    rw [Real.dist_eq] at hconv_n
    rw [abs_lt] at hconv_n
    linarith [hconv_n.1]
  -- Apply uniform left-continuity
  have hspec := hunif_δ (as n) (bs n) (has_pos n) (hbs_pos n) (h2bs n) hgap_pos hgap_lt φ
  -- Monotonicity: φ(E_{as n/bs n}) ≤ φ(E_{p/q})
  haveI : NeZero (as n) := ⟨Nat.pos_iff_ne_zero.mp (has_pos n)⟩
  have hle_rat : (as n : ℚ) / bs n ≤ (p : ℚ) / q := by
    apply (Rat.cast_le (K := ℝ)).1; simpa using le_of_lt (hbelow n)
  have hmono : φ.eval (@FractionGraph' (as n) (bs n)
      ⟨Nat.pos_iff_ne_zero.mp (has_pos n)⟩) ≤ φ.eval (FractionGraph' p q) :=
    φ.mono_cohom _ _ (by simpa using (fractionGraph_ordering (as n) (bs n) p q
      (hbs_pos n) hq (h2bs n) h2q).mp hle_rat)
  -- Combine: distance = φ(E_r) - φ(E_{as n/bs n}) < ε
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmono)]
  linarith

set_option linter.flexible false in
/-- Theorem 4.12 (iv)⟹(v): Sequential left-convergence implies supremum equality.

    If φ(E_{a_n/b_n}) → φ(E_{p/q}) for any sequence a_n/b_n → p/q from below,
    then sup_{a/b < p/q} φ(E_{a/b}) = φ(E_{p/q}).

    This requires 2*q < p (i.e., p/q > 2) so that the set of fractions below p/q
    with a/b ≥ 2 is nonempty. -/
theorem thm47_iv_implies_v
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q < p)
    -- Condition (iv): sequential left-convergence
    (hseq : ∀ (as bs : ℕ → ℕ) (has_pos : ∀ n, 0 < as n),
      (∀ n, 0 < bs n) → (∀ n, 2 * bs n ≤ as n) →
      Filter.Tendsto (fun n => (as n : ℝ) / bs n)
        Filter.atTop (nhds ((p : ℝ) / q)) →
      (∀ n, (as n : ℝ) / bs n < (p : ℝ) / q) →
      ∀ φ : SpectralPoint,
        Filter.Tendsto
          (fun n => φ.eval
            (@FractionGraph' (as n) (bs n) ⟨Nat.pos_iff_ne_zero.mp (has_pos n)⟩))
          Filter.atTop (nhds (φ.eval (FractionGraph' p q)))) :
    -- Condition (v): supremum equals spectral value
    ∀ φ : SpectralPoint,
      sSup {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b < (p : ℝ) / q ∧
        x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} =
      φ.eval (FractionGraph' p q) := by
  intro φ
  apply le_antisymm
  · -- ≤ direction: from fractionGraph_leftContinuity_equiv
    exact fractionGraph_leftContinuity_equiv p q hq (le_of_lt h2q) φ
  · -- ≥ direction: construct sequence approaching from below, use (iv)
    -- Sequence: a_n = p*(n+2), b_n = q*(n+2) + 1
    -- Then a_n/b_n = p*(n+2)/(q*(n+2)+1) < p/q and → p/q
    set as := fun n : ℕ => p * (n + 2) with has_def
    set bs := fun n : ℕ => q * (n + 2) + 1 with hbs_def
    have hp_ge3 : 3 ≤ p := by omega
    have has_pos : ∀ n, 0 < as n := by intro n; simp only [has_def]; positivity
    have hbs_pos : ∀ n, 0 < bs n := by intro n; simp only [hbs_def]; positivity
    have h2bs : ∀ n, 2 * bs n ≤ as n := by
      intro n; simp only [has_def, hbs_def]; nlinarith
    -- Below: a_n/b_n < p/q (since p*(n+2)*q < p*(q*(n+2)+1) = p*q*(n+2)+p)
    have hbelow : ∀ n, (as n : ℝ) / bs n < (p : ℝ) / q := by
      intro n; simp [has_def, hbs_def]
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < ↑q * (↑n + 2) + 1)
        (by positivity : (0 : ℝ) < ↑q)]
      have hp_pos : (0 : ℝ) < p := by positivity
      nlinarith [hp_pos]
    -- Convergence: a_n/b_n → p/q
    have hconv : Filter.Tendsto (fun n => (as n : ℝ) / bs n)
        Filter.atTop (nhds ((p : ℝ) / q)) := by
      simp only [has_def, hbs_def]
      rw [Metric.tendsto_atTop]
      intro ε hε
      -- |p*(n+2)/(q*(n+2)+1) - p/q| = p/(q*(q*(n+2)+1)) → 0
      obtain ⟨N, hN⟩ := exists_nat_gt ((p : ℝ) / (ε * q * q))
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq]
      have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
      have hden_pos : (0 : ℝ) < q * (↑n + 2) + 1 := by positivity
      -- Rewrite: p*(n+2)/(q*(n+2)+1) - p/q = -p/(q*(q*(n+2)+1))
      have hdiff : (p : ℝ) * (↑n + 2) / (q * (↑n + 2) + 1) - p / q =
          -(p : ℝ) / (q * (q * (↑n + 2) + 1)) := by
        field_simp; ring
      push_cast
      rw [hdiff, neg_div, abs_neg, abs_of_nonneg (by positivity)]
      calc (p : ℝ) / (q * (q * (↑n + 2) + 1))
          ≤ p / (q * (q * (↑n + 2))) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            linarith [show (0 : ℝ) ≤ q * (↑n + 2) from by positivity]
        _ = p / (q * q * (↑n + 2)) := by ring_nf
        _ ≤ p / (q * q * (↑N + 1)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            have : (N : ℝ) + 1 ≤ ↑n + 2 := by exact_mod_cast (show N + 1 ≤ n + 2 by omega)
            nlinarith
        _ < ε := by
            rw [div_lt_iff₀ (by positivity : (0 : ℝ) < q * q * (↑N + 1))]
            have hN' := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε * ↑q * ↑q)).mp hN
            nlinarith
    -- Apply (iv) to get convergence of spectral values
    have htend := hseq as bs has_pos hbs_pos h2bs hconv hbelow φ
    -- Since φ(E_{a_n/b_n}) → φ(E_{p/q}) and each term is in S,
    -- the limit ≤ sup S
    -- Use: tendsto + each term ≤ sup → limit ≤ sup
    -- And: each term ∈ S → each term ≤ sup S → limit ≤ sup S
    -- But we want sup S ≥ limit = φ(E_{p/q}), i.e., φ(E_{p/q}) ≤ sup S
    -- From tendsto: ∀ ε > 0, ∃ N, φ(E_{a_N/b_N}) > φ(E_{p/q}) - ε
    -- Each φ(E_{a_N/b_N}) ≤ sup S
    -- So sup S > φ(E_{p/q}) - ε for all ε > 0
    -- Hence sup S ≥ φ(E_{p/q})
    -- Need: S is nonempty and bounded above
    set S := {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b < (p : ℝ) / q ∧
        x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)}
    have hnonempty : S.Nonempty := by
      exact ⟨φ.eval (@FractionGraph' (as 0) (bs 0)
        ⟨Nat.pos_iff_ne_zero.mp (has_pos 0)⟩),
        as 0, bs 0, has_pos 0, hbs_pos 0, h2bs 0, hbelow 0, rfl⟩
    have hbdd : BddAbove S := by
      refine ⟨φ.eval (FractionGraph' p q), ?_⟩
      intro x hx
      rcases hx with ⟨a, b, ha, hb, h2b, hlt, rfl⟩
      haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
      have hle : (a : ℚ) / b ≤ (p : ℚ) / q := by
        apply (Rat.cast_le (K := ℝ)).1; simpa using le_of_lt hlt
      exact φ.mono_cohom _ _ (by simpa using
        (fractionGraph_ordering a b p q hb hq h2b (le_of_lt h2q)).mp hle)
    by_contra hlt
    push_neg at hlt
    have hε := sub_pos.mpr hlt
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend _ hε
    have hN' := hN N (le_refl N)
    rw [Real.dist_eq] at hN'
    have hmem : φ.eval (@FractionGraph' (as N) (bs N)
        ⟨Nat.pos_iff_ne_zero.mp (has_pos N)⟩) ∈ S :=
      ⟨as N, bs N, has_pos N, hbs_pos N, h2bs N, hbelow N, rfl⟩
    have hle_sup := le_csSup hbdd hmem
    have := abs_lt.mp hN'
    linarith

/-! ### Conditional Closure Theorem (Section 4.4)

The main result of Section 4.4: if the closed and open circle graphs are
asymptotically equivalent (in the sense of SpectralPointInf) for every rational r > 2,
then they are equivalent for ALL r ≥ 2. The irrational case is unconditional
(Theorem 4.11(a) = `circleGraph_asymp_equiv_irrational`). -/

/-- Conditional closure theorem: If ψ(E_r^c) = ψ(E_r^o) for all rational r > 2 and
    all ψ : SpectralPointInf, then the same holds for all real r > 2.

    Strict `2 < r` is essential: at r = 2 the equivalence fails (E_2^c is the
    complete graph on Circle, E_2^o excludes antipodal pairs), so the conclusion
    cannot hold at the boundary point. -/
theorem circleGraph_asymp_equiv_conditional
    (hhyp : ∀ (r : ℝ) (hr : 2 < r), ¬ Irrational r → ∀ ψ : SpectralPointInf,
      ψ.eval (circleGraphClosedInf r (le_of_lt hr)) =
        ψ.eval (circleGraphOpenInf r (le_of_lt hr))) :
    ∀ (r : ℝ) (hr : 2 < r) (ψ : SpectralPointInf),
      ψ.eval (circleGraphClosedInf r (le_of_lt hr)) =
        ψ.eval (circleGraphOpenInf r (le_of_lt hr)) := by
  intro r hr ψ
  by_cases hirr : Irrational r
  · exact circleGraph_asymp_equiv_irrational r (le_of_lt hr) hirr ψ
  · exact hhyp r hr hirr ψ

/-! ### Theorem 4.12 (ii)⟹(iii): Strong power bound implies uniform left-continuity

The proof uses strong product power evaluation (φ(G^⊠m) = φ(G)^m) to convert
the cohomomorphism bound into a spectral inequality, then uses rpow to bound
the gap uniformly.
-/

/-- Helper: strong power cohomomorphism gives spectral power bound.
    If E_{p/q}^⊠n ≤_G E_{a/b}^⊠m, then φ(E_{p/q})^n ≤ φ(E_{a/b})^m. -/
lemma spectral_pow_le_of_strongPower_cohom (G H : Graph) (n m : ℕ) (φ : SpectralPoint)
    (hcohom : Cohom (strongPower G.graph n) (strongPower H.graph m)) :
    φ.eval G ^ n ≤ φ.eval H ^ m := by
  have h1 := φ.mono_cohom (strongPowerGraph G n) (strongPowerGraph H m) hcohom
  rw [eval_strongPowerGraph, eval_strongPowerGraph] at h1
  exact h1

/-- Helper: IsLittleO implies f(n)/n → 0 as n → ∞. -/
lemma isLittleO_div_tendsto (f : ℕ → ℕ) (hf : IsLittleO f) :
    Filter.Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hf ε hε
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos))]
  exact (div_lt_iff₀ hn_pos).mpr (hN n hnN)

/-- Helper: p * (p^t - 1) → 0 as t → 0 for p > 0, since p^t is continuous
    and p^0 = 1. -/
lemma tendsto_mul_rpow_sub_one {p : ℝ} (hp : 0 < p) :
    Filter.Tendsto (fun t : ℝ => p * (p ^ t - 1)) (nhds 0) (nhds 0) := by
  have hcont : ContinuousAt (fun y : ℝ => p ^ y) 0 :=
    Real.continuousAt_const_rpow (ne_of_gt hp)
  have h0 : p ^ (0 : ℝ) = 1 := Real.rpow_zero p
  have htend : Filter.Tendsto (fun t : ℝ => p ^ t) (nhds 0) (nhds 1) := by
    rw [← h0]; exact hcont.tendsto
  have hsub : Filter.Tendsto (fun (t : ℝ) => p ^ t - 1) (nhds 0) (nhds (1 - 1)) :=
    htend.sub tendsto_const_nhds
  simp only [sub_self] at hsub
  have hmul : Filter.Tendsto (fun (t : ℝ) => p * (p ^ t - 1)) (nhds 0) (nhds (p * 0)) :=
    hsub.const_mul p
  simp only [mul_zero] at hmul
  exact hmul

/-- Helper: The rpow gap bound p * (p^{f(n)/n} - 1) → 0 when f is o(n). -/
lemma rpow_gap_tendsto_zero {p : ℝ} (hp : 0 < p) (f : ℕ → ℕ) (hf : IsLittleO f) :
    Filter.Tendsto (fun n : ℕ => p * (p ^ ((f n : ℝ) / (n : ℝ)) - 1))
      Filter.atTop (nhds 0) :=
  (tendsto_mul_rpow_sub_one hp).comp (isLittleO_div_tendsto f hf)

/-- Key inequality: if x^n ≤ y^{n+k} with 0 < y ≤ x ≤ C and n ≥ 1,
    then x - y ≤ C * (C^{k/n} - 1).

    Proof: From x^n ≤ y^{n+k} and y > 0, take nth root to get
    x ≤ y^{(n+k)/n} = y^{1+k/n}. Then the gap
    x - y ≤ y^{1+k/n} - y = y(y^{k/n} - 1) ≤ C(C^{k/n} - 1). -/
lemma gap_bound_of_pow_le {x y C : ℝ} {n k : ℕ}
    (hn : 1 ≤ n) (hy : 0 < y) (hyx : y ≤ x) (hxC : x ≤ C) (hC1 : 1 ≤ C)
    (hpow : x ^ n ≤ y ^ (n + k)) :
    x - y ≤ C * (C ^ ((k : ℝ) / (n : ℝ)) - 1) := by
  have hC : 0 < C := lt_of_lt_of_le (by linarith) hC1
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  -- Step 1: x^n ≤ y^n * y^k, so (x/y)^n ≤ y^k ≤ C^k
  have hyn_pos : 0 < y ^ n := pow_pos hy n
  have hdiv_pow : (x / y) ^ n ≤ C ^ k := by
    rw [div_pow]
    calc x ^ n / y ^ n ≤ y ^ (n + k) / y ^ n := by
            exact div_le_div_of_nonneg_right hpow (le_of_lt hyn_pos)
      _ = y ^ k := by rw [pow_add]; field_simp
      _ ≤ C ^ k := by
            exact pow_le_pow_left₀ (le_of_lt hy) (le_trans hyx hxC) k
  -- Step 2: x/y ≤ C^{k/n} using rpow nth root
  have hxy_pos : 0 < x / y := div_pos (lt_of_lt_of_le hy hyx) hy
  have hxy_nonneg : 0 ≤ x / y := le_of_lt hxy_pos
  have hC_nonneg : 0 ≤ C := le_of_lt hC
  -- (x/y)^n ≤ C^k in rpow form
  have hrpow_le : (x / y) ^ (n : ℝ) ≤ C ^ (k : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact hdiv_pow
  -- Take (1/n)-th power of both sides
  have hrpow_root : x / y ≤ C ^ ((k : ℝ) / (n : ℝ)) := by
    have hn_inv_pos : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos_of_pos hn_pos
    have h1 : ((x / y) ^ (n : ℝ)) ^ ((n : ℝ)⁻¹) ≤
        (C ^ (k : ℝ)) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hrpow_le (le_of_lt hn_inv_pos)
    rw [← Real.rpow_mul hxy_nonneg, mul_inv_cancel₀ (ne_of_gt hn_pos),
        Real.rpow_one] at h1
    rw [← Real.rpow_mul hC_nonneg, show (k : ℝ) * (n : ℝ)⁻¹ = (k : ℝ) / (n : ℝ)
        from div_eq_mul_inv (k : ℝ) (n : ℝ) |>.symm] at h1
    exact h1
  -- Step 3: x - y ≤ y * (C^{k/n} - 1) ≤ C * (C^{k/n} - 1)
  have hCk_ge1 : 1 ≤ C ^ ((k : ℝ) / (n : ℝ)) := by
    rw [← Real.rpow_zero C]
    exact Real.rpow_le_rpow_of_exponent_le hC1
      (div_nonneg (Nat.cast_nonneg k) (le_of_lt hn_pos))
  have hxy_le_mul : x ≤ y * C ^ ((k : ℝ) / (n : ℝ)) := by
    rw [div_le_iff₀ hy] at hrpow_root; linarith
  calc x - y ≤ y * C ^ ((k : ℝ) / (n : ℝ)) - y := by linarith
    _ = y * (C ^ ((k : ℝ) / (n : ℝ)) - 1) := by ring
    _ ≤ C * (C ^ ((k : ℝ) / (n : ℝ)) - 1) := by
        exact mul_le_mul_of_nonneg_right (le_trans hyx hxC)
          (sub_nonneg.mpr hCk_ge1)

/-- Theorem 4.12 (ii)⟹(iii): Strong power bound implies uniform left-continuity.

    If for some f = o(n), for each n ≥ 1 there exists a/b < p/q with
    E_{p/q}^⊠n ≤_G E_{a/b}^⊠(n+f(n)), then for every ε > 0 there exists δ > 0
    such that whenever 0 < p/q - a/b < δ with a/b ≥ 2, we have
    φ(E_{p/q}) - φ(E_{a/b}) < ε uniformly in φ. -/
theorem thm47_ii_implies_iii
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    -- Condition (ii): strong power bound
    (hii : ∃ f : ℕ → ℕ, IsLittleO f ∧
      ∀ n, n ≥ 1 → ∃ a b : ℕ, ∃ (ha : 0 < a) (_ : 0 < b),
        2 * b ≤ a ∧ (a : ℝ) / b < (p : ℝ) / q ∧
        Cohom (strongPower (fractionGraph p q) n)
          (strongPower (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) (n + f n))) :
    -- Condition (iii): uniform left-continuity
    ∀ ε > 0, ∃ δ > 0, ∀ (a b : ℕ) (ha : 0 < a),
      0 < b → 2 * b ≤ a →
      0 < (p : ℝ) / q - (a : ℝ) / b →
      (p : ℝ) / q - (a : ℝ) / b < δ →
      ∀ φ : SpectralPoint,
        φ.eval (FractionGraph' p q) -
        φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) < ε := by
  obtain ⟨f, hf, hii⟩ := hii
  intro ε hε
  -- The rpow gap bound p * (p^{f(n)/n} - 1) → 0
  have htend := rpow_gap_tendsto_zero (Nat.cast_pos.mpr (NeZero.pos p)) f hf
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend ε hε
  -- Choose n₀ ≥ max(N₀, 1)
  set n₀ := max N₀ 1 with hn₀_def
  have hn₀_ge1 : n₀ ≥ 1 := le_max_right _ _
  have hn₀_geN : n₀ ≥ N₀ := le_max_left _ _
  -- Get a₀/b₀ from condition (ii) at n₀
  obtain ⟨a₀, b₀, ha₀, hb₀, h2b₀, hbelow₀, hcohom₀⟩ := hii n₀ hn₀_ge1
  -- Set δ = p/q - a₀/b₀ > 0
  set δ := (p : ℝ) / q - (a₀ : ℝ) / b₀ with hδ_def
  have hδ_pos : 0 < δ := sub_pos.mpr hbelow₀
  refine ⟨δ, hδ_pos, fun a b ha hb h2b hgap_pos hgap_lt φ => ?_⟩
  -- Any a/b with p/q - δ < a/b < p/q satisfies a₀/b₀ < a/b < p/q
  haveI : NeZero a₀ := ⟨Nat.pos_iff_ne_zero.mp ha₀⟩
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  -- Monotonicity: φ(E_{a₀/b₀}) ≤ φ(E_{a/b}) ≤ φ(E_{p/q})
  have hab_below : (a₀ : ℝ) / b₀ < (a : ℝ) / b := by linarith
  have hab_le_pq : (a : ℝ) / b < (p : ℝ) / q := by linarith [hgap_pos]
  have hle_ab_pq : (a : ℚ) / b ≤ (p : ℚ) / q := by
    apply (Rat.cast_le (K := ℝ)).1; simpa using le_of_lt hab_le_pq
  have hmono_ab : φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) ≤
      φ.eval (FractionGraph' p q) :=
    φ.mono_cohom _ _ (by simpa using (fractionGraph_ordering a b p q hb hq h2b h2q).mp hle_ab_pq)
  -- The gap for a/b is bounded by the gap for a₀/b₀
  -- Since a₀/b₀ ≤ a/b, φ(E_{a₀/b₀}) ≤ φ(E_{a/b})
  -- So φ(E_{p/q}) - φ(E_{a/b}) ≤ φ(E_{p/q}) - φ(E_{a₀/b₀})
  have hab0_le : (a₀ : ℚ) / b₀ ≤ (a : ℚ) / b := by
    apply (Rat.cast_le (K := ℝ)).1; simpa using le_of_lt hab_below
  have hmono_a0_ab : φ.eval (FractionGraph' a₀ b₀) ≤
      φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) :=
    φ.mono_cohom _ _ (by simpa using
      (fractionGraph_ordering a₀ b₀ a b hb₀ hb h2b₀ h2b).mp hab0_le)
  -- Now bound φ(E_{p/q}) - φ(E_{a₀/b₀}) using the spectral power inequality
  -- From hcohom₀: φ(E_{p/q})^n₀ ≤ φ(E_{a₀/b₀})^{n₀+f(n₀)}
  have hspec := spectral_pow_le_of_strongPower_cohom
    (FractionGraph' p q)
    (FractionGraph' a₀ b₀)
    n₀ (n₀ + f n₀) φ hcohom₀
  -- Apply gap bound: φ(E_{p/q}) - φ(E_{a₀/b₀}) ≤ p * (p^{f(n₀)/n₀} - 1)
  have hp_bound : φ.eval (FractionGraph' p q) ≤ p :=
    fractionGraph_spectral_le_vertices p q hq φ
  have ha0_pos_eval : 0 < φ.eval (FractionGraph' a₀ b₀) := by
    -- Any graph with ≥ 1 vertex has φ ≥ 1 > 0
    -- because EdgelessGraph 1 ≤_G any graph (vacuous cohom)
    -- and φ(EdgelessGraph 1) = 1
    have h1 : φ.eval (EdgelessGraph 1) = 1 := by
      have := φ.normalized 1; simp only [Nat.cast_one] at this; exact this
    have hcohom1 : Cohom (EdgelessGraph 1).graph (FractionGraph' a₀ b₀).graph := by
      refine ⟨fun _ => (0 : ZMod a₀), fun u v huv => ?_⟩
      exact absurd (Fin.ext (by omega) : u = v) huv
    have := φ.mono_cohom (EdgelessGraph 1) (FractionGraph' a₀ b₀) hcohom1
    linarith
  have hmono_a0_pq : φ.eval (FractionGraph' a₀ b₀) ≤
      φ.eval (FractionGraph' p q) := by
    have hle0 : (a₀ : ℚ) / b₀ ≤ (p : ℚ) / q := by
      apply (Rat.cast_le (K := ℝ)).1; simpa using le_of_lt hbelow₀
    exact φ.mono_cohom _ _ (by simpa using
      (fractionGraph_ordering a₀ b₀ p q hb₀ hq h2b₀ h2q).mp hle0)
  have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast NeZero.one_le
  have hgap_bound := gap_bound_of_pow_le (n := n₀) (k := f n₀)
    hn₀_ge1 ha0_pos_eval hmono_a0_pq hp_bound hp_ge1 hspec
  -- The bound p * (p^{f(n₀)/n₀} - 1) < ε
  have hN₀' := hN₀ n₀ hn₀_geN
  rw [Real.dist_eq, sub_zero] at hN₀'
  have hbound_pos : 0 ≤ (p : ℝ) * ((p : ℝ) ^ ((f n₀ : ℝ) / (n₀ : ℝ)) - 1) := by
    apply mul_nonneg (Nat.cast_nonneg p)
    rw [sub_nonneg]
    rw [← Real.rpow_zero (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast NeZero.one_le)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [abs_of_nonneg hbound_pos] at hN₀'
  -- Combine: gap for a/b ≤ gap for a₀/b₀ ≤ bound < ε
  linarith


/-- Core combinatorial step for Theorem 4.12 (i)⟹(ii). Requires 2 < r. -/
theorem thm47_core_finite_image
    (p q : ℕ) [NeZero p] (_hq : 0 < q) (_h2q : 2 * q ≤ p)
    (hr : 2 < (p : ℝ) / q) (n k : ℕ) (hn : 0 < n)
    (hcomp : Cohom
      (recInfProduct (graphToInfiniteGraph (FractionGraph' p q)) n).graph
      ((recInfProduct (circleGraphClosedInf ((p : ℝ) / q) (le_of_lt hr)) n) ⊠∞
        InfiniteGraph.edgeless k).graph) :
    ∃ a b : ℕ, ∃ (ha : 0 < a) (_ : 0 < b),
      2 * b ≤ a ∧ (a : ℝ) / b < (p : ℝ) / q ∧
      Cohom (strongPower (fractionGraph p q) n)
        (strongPower (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) (n + logBound k)) := by
  set r := (p : ℝ) / q with hr_def
  set hr_le := le_of_lt hr
  -- Step 1: Convert to strongPower form via graph isomorphisms
  let fracInf := graphToInfiniteGraph (FractionGraph' p q)
  let closedInf := circleGraphClosedInf r hr_le
  -- Source iso: recInfProduct fracInf n ≃g strongPower (fractionGraph p q) n
  have iso_src := recInfProduct_iso_strongPower fracInf n
  -- Target iso: recInfProduct closedInf n ≃g strongPower (circleGraphClosed r hr_le) n
  have iso_tgt := recInfProduct_iso_strongPower closedInf n
  -- Convert hypothesis to strongPower form
  have hcomp' : Cohom (strongPower (fractionGraph p q) n)
      (ShannonCapacity.strongProduct (strongPower (circleGraphClosed r hr_le) n)
        (⊥ : SimpleGraph (Fin k))) :=
    Cohom.trans (cohom_of_relIso iso_src.symm)
      (Cohom.trans hcomp
        (strongProduct_cohom_both (cohom_of_relIso iso_tgt) ⟨id, fun _ _ h h2 => ⟨h, h2⟩⟩))
  -- Step 2: Extract cohomomorphism and build finite image set
  obtain ⟨f, hf⟩ := hcomp'
  -- f : (Fin n → ZMod p) → (Fin n → Circle) × Fin k, IsCohom
  -- Build S: all Circle values appearing in coordinates of the image
  let S : Finset Circle := Finset.univ.biUnion fun (x : Fin n → ZMod p) =>
    Finset.univ.image fun (i : Fin n) => (f x).1 i
  -- S is nonempty (source has at least one vertex, n ≥ 1)
  have hS_nonempty : S.Nonempty := by
    simp only [S, Finset.Nonempty]
    refine ⟨(f (fun _ => 0)).1 ⟨0, hn⟩, ?_⟩
    simp [Finset.mem_biUnion, Finset.mem_image]
  -- All image coordinates land in S
  have hf_in_S : ∀ (x : Fin n → ZMod p) (i : Fin n), (f x).1 i ∈ S := by
    intro x i; simp only [S, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨x, Finset.mem_univ x, i, Finset.mem_univ i, rfl⟩
  -- Step 3: Apply Lemma 4.3 (circleGraphClosed_finite_subgraph)
  obtain ⟨a, b, ha, hb, h2b, hab_lt, hcohom_induce⟩ :=
    circleGraphClosed_finite_subgraph r hr S hS_nonempty
  -- hcohom_induce : Cohom (circleGraphClosed r hr_le).induce S (circleGraphOpen (a/b) hs)
  -- Get cohom from open to fractionGraph via Lemma 4.4
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  have hab_frac := (circleGraphOpen_equiv_fractionGraph a b hb h2b).1
  -- hab_frac : Cohom (circleGraphOpen (a/b) _) (fractionGraph a b)
  -- Compose: induce S → open(a/b) → fractionGraph a b
  have hS_to_frac : Cohom ((circleGraphClosed r hr_le).induce (S : Set Circle))
      (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) :=
    Cohom.trans hcohom_induce hab_frac
  -- Step 4: Factor through induced subgraph and compose
  -- Restrict f to land in S^n × Fin k (it already does by construction)
  -- Then compose with strongPower_mono from Lemma 4.3 result
  -- And absorb the edgeless factor
  -- Build the restricted function into (Fin n → ↥S) × Fin k
  let f' : (Fin n → ZMod p) → (Fin n → (S : Set Circle)) × Fin k :=
    fun x => (fun i => ⟨(f x).1 i, hf_in_S x i⟩, (f x).2)
  -- f' is a cohomomorphism to (closedGraph.induce S)^n × edgeless(k)
  have hf'_cohom : Cohom (strongPower (fractionGraph p q) n)
      (ShannonCapacity.strongProduct
        (strongPower ((circleGraphClosed r hr_le).induce (S : Set Circle)) n)
        (⊥ : SimpleGraph (Fin k))) := by
    refine ⟨f', fun g₁ g₂ hne hnadj => ?_⟩
    have ⟨hfne, hfnadj⟩ := hf g₁ g₂ hne hnadj
    constructor
    · -- f' g₁ ≠ f' g₂
      intro heq; apply hfne
      exact Prod.ext
        (funext fun i => congrArg Subtype.val (congr_fun (Prod.mk.inj heq).1 i))
        (Prod.mk.inj heq).2
    · -- ¬ adj in (induce S closedGraph)^n × ⊥: contrapositive
      intro ⟨_, hleft, hright⟩
      apply hfnadj
      refine ⟨hfne, ?_, hright⟩
      cases hleft with
      | inl heq =>
        exact Or.inl (funext fun i => congrArg Subtype.val (congr_fun heq i))
      | inr hadj =>
        exact Or.inr ⟨fun h => hadj.1 (funext fun i =>
          Subtype.ext (congr_fun h i)), fun i =>
          (hadj.2 i).elim (fun h => Or.inl (congrArg Subtype.val h)) Or.inr⟩
  -- Apply strongPower_mono to S → fractionGraph a b
  have hpow_cohom : Cohom
      (strongPower ((circleGraphClosed r hr_le).induce (S : Set Circle)) n)
      (strongPower (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) n) :=
    Cohom.strongPower hS_to_frac n
  -- Step 5: Absorb edgeless factor
  -- fractionGraph a b has two non-adjacent vertices (since a ≥ 2b, vertices 0 and b have
  -- distMod ≥ b, so they are non-adjacent)
  have hba : b < a := by omega
  have hfrac_indep : ∃ v₀ v₁ : ZMod a, v₀ ≠ v₁ ∧
      ¬(@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩).Adj v₀ v₁ := by
    refine ⟨0, (b : ZMod a), ?_, ?_⟩
    · intro heq
      have := congr_arg ZMod.val heq
      rw [ZMod.val_zero, ZMod.val_natCast_of_lt hba] at this
      omega
    · intro ⟨_, hdist⟩
      have hdist_ge := FractionGraphBasic.distMod_ge_q_of_val_diff_in_range a b h2b 0 (b : ZMod a)
        (by rw [ZMod.val_zero, ZMod.val_natCast_of_lt hba]; omega)
        (by rw [ZMod.val_natCast_of_lt hba, ZMod.val_zero]; omega)
        (by rw [ZMod.val_natCast_of_lt hba, ZMod.val_zero]; omega)
      omega
  -- edgeless_cohom_to_strongPower gives Cohom (edgelessGraph k) (recStrongPowerGraph ...)
  have hedgeless := edgeless_cohom_to_strongPower
    (FractionGraph' a b) k (logBound k) hfrac_indep (two_pow_logBound_ge k)
  -- Convert to strongPower form via recStrongPowerGraph_iso
  -- Note: must use AsymptoticSpectrumGraphs. prefix to match the recStrongPowerGraph used
  -- by edgeless_cohom_to_strongPower (AsymptoticSpectrumDistance also defines recStrongPowerGraph)
  have hedgeless' := Cohom.trans hedgeless
    (cohom_of_relIso
      (AsymptoticSpectrumGraphs.recStrongPowerGraph_iso (FractionGraph' a b) (logBound k)))
  -- Compose: fracGraph^n ⊠ edgeless(k) → fracGraph^n ⊠ fracGraph^(logBound k)
  have hprod_cohom := strongProduct_cohom_both hpow_cohom hedgeless'
  -- Merge: fracGraph^n ⊠ fracGraph^(logBound k) → fracGraph^(n + logBound k)
  have hmerge := strongPower_product_merge
    (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) n (logBound k)
  -- Final composition
  exact ⟨a, b, ha, hb, h2b, hab_lt,
    Cohom.trans hf'_cohom (Cohom.trans hprod_cohom hmerge)⟩

/-- Theorem 4.12 (i)⟹(ii): Spectral equivalence implies strong power bound.

    If ψ(E_r^c) = ψ(E_r^o) for all ψ : SpectralPointInf, then there
    exists f = o(n) such that for each n ≥ 1, some a/b < r satisfies
    E_{p/q}^⊠n ≤_G E_{a/b}^⊠(n+f(n)).

    Paper reference: Theorem 4.12, implication (i) ⇒ (ii).

    Proof outline:
    1. Spectral duality (spectral_duality_inf): ∀ψ, ψ(E_r^o) ≤ ψ(E_r^c)
       gives AsympRel infiniteGraphStrassenPreorder (mk E_r^o) (mk E_r^c)
    2. AsympRel_iff_tendsto: extract witnesses x(n) with x(n)^{1/n} → 1
    3. logBound x gives IsLittleO function f
    4. For each n: unpack the rel bound, compose with E_{p/q} → E_r^o,
       apply finite subgraph argument (Lemma 4.3) coordinatewise to
       get a/b < r, then use edgeless_cohom_to_strongPower -/
theorem thm47_i_implies_ii
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    -- Condition (i): spectral equivalence of circle graphs (requires 2 < r)
    (hr : 2 < (p : ℝ) / q)
    (hi : ∀ ψ : SpectralPointInf,
      ψ.eval (circleGraphClosedInf ((p : ℝ) / q) (le_of_lt hr))
        = ψ.eval (circleGraphOpenInf ((p : ℝ) / q) (le_of_lt hr))) :
    -- Condition (ii): strong power bound
    ∃ f : ℕ → ℕ, IsLittleO f ∧
      ∀ n, n ≥ 1 → ∃ a b : ℕ, ∃ (ha : 0 < a) (_ : 0 < b),
        2 * b ≤ a ∧ (a : ℝ) / b < (p : ℝ) / q ∧
        Cohom (strongPower (fractionGraph p q) n)
          (strongPower (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) (n + f n)) := by
  have hr_le : 2 ≤ (p : ℝ) / q := le_of_lt hr
  -- Step 1: From condition (i), ψ(E_r^o) ≤ ψ(E_r^c) for all ψ
  have hle : ∀ ψ : SpectralPointInf,
      ψ.eval (circleGraphOpenInf ((p : ℝ) / q) hr_le) ≤
      ψ.eval (circleGraphClosedInf ((p : ℝ) / q) hr_le) :=
    fun ψ => le_of_eq (hi ψ).symm
  -- Step 2: By spectral duality, E_r^o ≲ E_r^c in AsympRel
  have hasym := (spectral_duality_inf _ _).mpr hle
  -- Step 3: Convert to Tendsto form — get witnesses x(n) with x(n)^{1/n} → 1
  obtain ⟨x, hx_rel, hx_tendsto⟩ :=
    (AsymptoticSpectrumDuality.AsympRel_iff_tendsto
      infiniteGraphStrassenPreorder _ _).mp hasym
  -- Step 4: logBound gives IsLittleO function
  use fun n => logBound (x n)
  refine ⟨logBound_littleO_of_tendsto x hx_tendsto, ?_⟩
  -- Step 5: For each n ≥ 1, construct the cohomomorphism
  intro n hn
  -- hx_rel n hn gives: infiniteGraphStrassenPreorder.rel
  --   ((mk E_r^o)^n) ((mk E_r^c)^n * (x n : InfiniteGraphClass))
  -- Unpack to concrete Cohom using infClass_pow_eq_mk and infiniteGraphCohom_mk
  have hrel_n := hx_rel n hn
  rw [infClass_pow_eq_mk, infClass_pow_eq_mk, InfiniteGraphClass.natCast_eq_edgeless,
      InfiniteGraphClass.mul_def] at hrel_n
  -- hrel_n now has type infiniteGraphStrassenPreorder.rel (mk A) (mk B)
  -- which is definitionally Cohom A.graph B.graph (via infiniteGraphCohom_mk)
  -- hrel_n : Cohom (recInfProduct (circleGraphOpenInf r hr) n).graph
  --          ((recInfProduct (circleGraphClosedInf r hr) n) ⊠∞ edgeless(x n)).graph
  -- Compose with E_{p/q} → E_r^o (strong power monotonicity)
  let fracInf := graphToInfiniteGraph (FractionGraph' p q)
  let openInf := circleGraphOpenInf ((p : ℝ) / q) hr_le
  let closedInf := circleGraphClosedInf ((p : ℝ) / q) hr_le
  have hfrac_to_open : Cohom fracInf.graph openInf.graph :=
    (circleGraphOpen_equiv_fractionGraph p q hq h2q).2
  have hpow_mono := recInfProduct_mono hfrac_to_open n
  -- Compose: E_{p/q}^n → (E_r^o)^n → (E_r^c)^n ⊠ E_{x(n)}
  have hcomp := Cohom.trans hpow_mono hrel_n
  -- Apply the core finite image argument (Lemma 4.3 coordinatewise + absorption)
  exact thm47_core_finite_image p q hq h2q hr n (x n) (by omega) hcomp

/-! ### Theorem 4.12 (i)⟹(ii): Edge case r = 2

At r = 2, condition (i) is false: E₂ᶜ is the complete graph on the circle
(since max distance = 1/2 = 1/r), so ψ(E₂ᶜ) = 1. Meanwhile E₂ᵒ ≡ E_{2/1}
which is edgeless on 2 vertices, so ψ(E₂ᵒ) = 2. Thus (i)⟹(ii) is vacuously true. -/

/-- E₂ᶜ is complete: every distinct pair is adjacent (distance ≤ 1/2 always holds). -/
private theorem circleGraphClosed_two_complete (u v : Circle) (huv : u ≠ v) :
    (circleGraphClosed 2 (by norm_num : (2 : ℝ) ≤ 2)).Adj u v :=
  ⟨huv, circleDistance_le_half u v⟩

/-- E₂ᶜ has a cohomomorphism to edgeless 1 (send everything to the single vertex). -/
private theorem circleGraphClosed_two_cohom_to_edgeless_one :
    Cohom (circleGraphClosed 2 (by norm_num : (2 : ℝ) ≤ 2))
             (InfiniteGraph.edgeless 1).graph := by
  refine ⟨fun _ => (⟨0, by omega⟩ : Fin 1), fun u v huv hnadj => ?_⟩
  exact absurd (circleGraphClosed_two_complete u v huv) hnadj

/-- Edgeless 1 has a cohomomorphism to E₂ᶜ (send the single vertex to any point). -/
private theorem edgeless_one_cohom_to_circleGraphClosed_two :
    Cohom (InfiniteGraph.edgeless 1).graph
             (circleGraphClosed 2 (by norm_num : (2 : ℝ) ≤ 2)) := by
  refine ⟨fun _ => QuotientAddGroup.mk 0, fun u v huv _ => ?_⟩
  exact absurd (show u = v from Subsingleton.elim (α := Fin 1) u v) huv

/-- ψ(E₂ᶜ) = 1 for all SpectralPointInf ψ. -/
private theorem spectralPointInf_closed_two_eq_one (ψ : SpectralPointInf) :
    ψ.eval (circleGraphClosedInf 2 (by norm_num : (2 : ℝ) ≤ 2)) = 1 := by
  apply le_antisymm
  · -- ψ(E₂ᶜ) ≤ ψ(edgeless 1) = 1
    calc ψ.eval (circleGraphClosedInf 2 _)
        ≤ ψ.eval (InfiniteGraph.edgeless 1) :=
          ψ.mono_cohom _ _ circleGraphClosed_two_cohom_to_edgeless_one
      _ = 1 := by rw [ψ.normalized 1]; simp
  · -- 1 = ψ(edgeless 1) ≤ ψ(E₂ᶜ)
    calc (1 : ℝ) = ψ.eval (InfiniteGraph.edgeless 1) := by rw [ψ.normalized 1]; simp
      _ ≤ ψ.eval (circleGraphClosedInf 2 _) :=
          ψ.mono_cohom _ _ edgeless_one_cohom_to_circleGraphClosed_two

/-- Two antipodal points on the circle are at distance 1/2. -/
private theorem circleDistance_zero_half :
    circleDistance (QuotientAddGroup.mk (0 : ℝ) : Circle)
                   (QuotientAddGroup.mk (1/2 : ℝ)) = 1/2 := by
  simp only [circleDistance, dist_eq_norm, ← QuotientAddGroup.mk_sub, zero_sub,
    QuotientAddGroup.mk_neg, norm_neg]
  have := AddCircle.norm_half_period_eq (1 : ℝ)
  simp only [abs_one] at this
  exact this

/-- Two antipodal points on the circle are distinct. -/
private theorem circle_zero_ne_half :
    (QuotientAddGroup.mk (0 : ℝ) : Circle) ≠ QuotientAddGroup.mk (1/2 : ℝ) := by
  intro heq
  rw [QuotientAddGroup.eq] at heq
  simp only [AddSubgroup.mem_zmultiples_iff] at heq
  obtain ⟨n, hn⟩ := heq
  -- hn : n • 1 = -0 + 1/2 i.e. (n : ℝ) = 1/2
  have h1 : (n : ℝ) = 1/2 := by simp [zsmul_eq_mul] at hn; linarith
  have h2 : (2 : ℝ) * n = 1 := by linarith
  have h3 : (2 : ℤ) * n = 1 := by exact_mod_cast h2
  omega

/-- Two antipodal points on the circle are non-adjacent in E₂ᵒ (distance = 1/2 ≮ 1/2). -/
private theorem circleGraphOpen_two_antipodal_nonadj :
    ¬(circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2)).Adj
      (QuotientAddGroup.mk (0 : ℝ) : Circle) (QuotientAddGroup.mk (1/2 : ℝ)) := by
  intro ⟨_, hdist⟩
  -- hdist : circleDistance ... < 1/2
  rw [circleDistance_zero_half] at hdist
  linarith

/-- Edgeless 2 has a cohomomorphism to E₂ᵒ (map to antipodal points). -/
private theorem edgeless_two_cohom_to_circleGraphOpen_two :
    Cohom (InfiniteGraph.edgeless 2).graph
             (circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2)) := by
  -- Map 0 ↦ mk 0, 1 ↦ mk (1/2)
  -- Work with Fin 2 explicitly via show
  change Cohom (⊥ : SimpleGraph (Fin 2))
    (circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2))
  let p0 : Circle := QuotientAddGroup.mk (0 : ℝ)
  let p1 : Circle := QuotientAddGroup.mk (1/2 : ℝ)
  have hne : p0 ≠ p1 := circle_zero_ne_half
  have hnonadj : ¬(circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2)).Adj p0 p1 :=
    circleGraphOpen_two_antipodal_nonadj
  refine ⟨![p0, p1], fun u v huv _ => ?_⟩
  -- u, v : Fin 2, u ≠ v
  have hu : u = 0 ∨ u = 1 := by omega
  have hv : v = 0 ∨ v = 1 := by omega
  constructor
  · -- Mapped vertices are distinct
    intro heq
    apply huv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  · -- Mapped vertices are not adjacent in E₂ᵒ
    have hnonadj' : ¬(circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2)).Adj p1 p0 :=
      fun h => hnonadj ((circleGraphOpen 2 _).symm h)
    intro hadj
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- For every point `u` on the unit circle there exists an antipodal point
    `v ≠ u` at distance exactly `1/2`. Used in the `r = 2` case of
    `circleGraph_open_closed_not_equiv`: at `r = 2` the open graph `E₂ᵒ` has
    `u ≁ u*` for the antipode while the closed graph `E₂ᶜ = K_{Circle}` has
    `u ∼ u*`. -/
theorem circleDistance_exists_antipodal (u : Circle) :
    ∃ v : Circle, v ≠ u ∧ circleDistance u v = 1/2 := by
  refine ⟨u + (QuotientAddGroup.mk (1/2 : ℝ) : Circle), ?_, ?_⟩
  · -- v ≠ u, i.e. u + mk(1/2) ≠ u, i.e. mk(1/2) ≠ 0.
    intro hv
    have hhalf : (QuotientAddGroup.mk (1/2 : ℝ) : Circle) = 0 := by
      have := congrArg (fun x => x - u) hv
      simpa using this
    -- But mk(1/2) ≠ 0 in Circle = ℝ ⧸ ⟨1⟩: from circle_zero_ne_half (`mk 0 ≠ mk (1/2)`)
    -- we have mk(0) ≠ mk(1/2). Since mk(0) = 0, mk(1/2) ≠ 0.
    have h0 : (QuotientAddGroup.mk (0 : ℝ) : Circle) = 0 := by
      simp [QuotientAddGroup.mk_zero]
    exact circle_zero_ne_half (h0.trans hhalf.symm)
  · -- circleDistance u (u + mk(1/2)) = 1/2
    -- dist (u) (u + w) = ‖u - (u + w)‖ = ‖-w‖ = ‖w‖
    simp only [circleDistance, dist_eq_norm]
    have hsub : u - (u + (QuotientAddGroup.mk (1/2 : ℝ) : Circle))
        = -(QuotientAddGroup.mk (1/2 : ℝ) : Circle) := by
      abel
    rw [hsub, norm_neg]
    have := AddCircle.norm_half_period_eq (1 : ℝ)
    simpa [abs_one] using this

/-- ψ(E₂ᵒ) ≥ 2 for all SpectralPointInf ψ. -/
private theorem spectralPointInf_open_two_ge_two (ψ : SpectralPointInf) :
    2 ≤ ψ.eval (circleGraphOpenInf 2 (by norm_num : (2 : ℝ) ≤ 2)) := by
  calc (2 : ℝ) = ψ.eval (InfiniteGraph.edgeless 2) := by rw [ψ.normalized 2]; simp
    _ ≤ ψ.eval (circleGraphOpenInf 2 _) :=
        ψ.mono_cohom _ _ edgeless_two_cohom_to_circleGraphOpen_two

/-- Theorem 4.12 (i)⟹(ii) for all r = p/q ≥ 2 (matching the paper's Q_{≥2}).
    At r > 2, uses the core finite image argument.
    At r = 2, condition (i) is false (vacuously true). -/
theorem thm47_i_implies_ii_ge
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    (hr : 2 ≤ (p : ℝ) / q)
    (hi : ∀ ψ : SpectralPointInf,
      ψ.eval (circleGraphClosedInf ((p : ℝ) / q) hr)
        = ψ.eval (circleGraphOpenInf ((p : ℝ) / q) hr)) :
    ∃ f : ℕ → ℕ, IsLittleO f ∧
      ∀ n, n ≥ 1 → ∃ a b : ℕ, ∃ (ha : 0 < a) (_ : 0 < b),
        2 * b ≤ a ∧ (a : ℝ) / b < (p : ℝ) / q ∧
        Cohom (strongPower (fractionGraph p q) n)
          (strongPower (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩) (n + f n)) := by
  by_cases hgt : 2 < (p : ℝ) / q
  · exact thm47_i_implies_ii p q hq h2q hgt (fun ψ => hi ψ)
  · -- r = 2 case: condition (i) is false
    push_neg at hgt
    have hr_eq : (p : ℝ) / q = 2 := le_antisymm hgt hr
    exfalso
    -- Get any SpectralPointInf
    obtain ⟨φ⟩ := spectralPoint_nonempty
    obtain ⟨ψ, _⟩ := restriction_surjective φ
    have h1 := spectralPointInf_closed_two_eq_one ψ
    have h2 := spectralPointInf_open_two_ge_two ψ
    have h3 := hi ψ
    -- h3 : ψ.eval (circleGraphClosedInf ((p:ℝ)/q) hr) = ψ.eval (circleGraphOpenInf ((p:ℝ)/q) hr)
    -- h1 : ψ.eval (circleGraphClosedInf 2 (by norm_num)) = 1
    -- h2 : 2 ≤ ψ.eval (circleGraphOpenInf 2 (by norm_num))
    -- Since (p:ℝ)/q = 2, the circle graphs with r = (p:ℝ)/q and r = 2 are isomorphic
    -- via the identity (same adjacency condition), so use eval_congr to rewrite
    have hc : ψ.eval (circleGraphClosedInf ((p : ℝ) / q) hr) =
              ψ.eval (circleGraphClosedInf 2 (by norm_num : (2 : ℝ) ≤ 2)) := by
      apply ψ.eval_congr
      exact ⟨⟨Equiv.refl _, fun {u v} => by
        simp only [circleGraphClosedInf, circleGraphClosed, Equiv.refl_apply, hr_eq]
        rfl⟩⟩
    have ho : ψ.eval (circleGraphOpenInf ((p : ℝ) / q) hr) =
              ψ.eval (circleGraphOpenInf 2 (by norm_num : (2 : ℝ) ≤ 2)) := by
      apply ψ.eval_congr
      exact ⟨⟨Equiv.refl _, fun {u v} => by
        simp only [circleGraphOpenInf, circleGraphOpen, Equiv.refl_apply, hr_eq]
        rfl⟩⟩
    rw [hc, ho] at h3
    linarith

/-! ### Theorem 4.12: Full TFAE -/

/-- Theorem 4.12: For rational r = p/q ≥ 2, five equivalent conditions for
    left-continuity. Proved via the cycle (i)⟹(ii)⟹(iii)⟹(iv)⟹(v)⟹(i). -/
theorem theorem_4_12_tfae (p q : ℕ+) (h2q : 2 * q < p) :
    have hr : 2 ≤ (p : ℝ) / q := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q
    List.TFAE [
      -- (i) E_r^c and E_r^o are asymptotically equivalent
      AsympCohomEquivInf (circleGraphClosedInf ((p : ℝ) / q) hr)
        (circleGraphOpenInf ((p : ℝ) / q) hr),
      -- (ii) Strong power bound with o(n) error
      ∃ f : ℕ → ℕ, IsLittleO f ∧ ∀ n, n ≥ 1 →
        ∃ (a b : ℕ+), 2 * b ≤ a ∧
          (a : ℝ) / b < (p : ℝ) / q ∧
          Cohom (strongPower (fractionGraph p q) n)
            (strongPower (fractionGraph a b) (n + f n)),
      -- (iii) Uniform left-continuity
      ∀ ε > 0, ∃ δ > 0, ∀ (a b : ℕ+),
        2 * b ≤ a →
        0 < (p : ℝ) / q - (a : ℝ) / b →
        (p : ℝ) / q - (a : ℝ) / b < δ →
        ∀ φ : SpectralPoint,
          φ (FractionGraph p q) - φ (FractionGraph a b) < ε,
      -- (iv) Sequential left-convergence: E_{a_n/b_n} → E_{p/q}
      ∀ (as bs : ℕ → ℕ+),
        (∀ n, 2 * bs n ≤ as n) →
        Filter.Tendsto (fun n => (as n : ℝ) / bs n)
          Filter.atTop (nhds ((p : ℝ) / q)) →
        (∀ n, (as n : ℝ) / bs n < (p : ℝ) / q) →
        ConvergesTo
          (fun n => FractionGraph (as n) (bs n))
          (FractionGraph p q),
      -- (v) Supremum equals spectral value
      ∀ φ : SpectralPoint,
        sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧
          (a : ℝ) / b < (p : ℝ) / q ∧
          x = φ (FractionGraph a b)} =
        φ (FractionGraph p q)
    ] := by
  have hr : 2 ≤ (p : ℝ) / q := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q
  -- Helper: convert between ∀ψ equal and AsympCohomEquivInf
  have equiv_iff : (∀ ψ : SpectralPointInf,
      ψ.eval (circleGraphClosedInf ((p : ℝ) / q) hr) =
      ψ.eval (circleGraphOpenInf ((p : ℝ) / q) hr)) ↔
    AsympCohomEquivInf (circleGraphClosedInf ((p : ℝ) / q) hr)
      (circleGraphOpenInf ((p : ℝ) / q) hr) := by
    constructor
    · intro h; exact ⟨(spectral_duality_inf _ _).mpr (fun ψ => le_of_eq (h ψ)),
        (spectral_duality_inf _ _).mpr (fun ψ => le_of_eq (h ψ).symm)⟩
    · intro ⟨h1, h2⟩ ψ; exact le_antisymm
        ((spectral_duality_inf _ _).mp h1 ψ) ((spectral_duality_inf _ _).mp h2 ψ)
  -- Helper: convert ℕ+ ↔ ℕ sets
  have set_conv : ∀ φ : SpectralPoint,
      {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < (p : ℝ) / q ∧
        x = φ (FractionGraph a b)} =
      {x | ∃ a b : ℕ, ∃ (ha : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
        (a : ℝ) / b < (p : ℝ) / q ∧
        x = φ.eval (@FractionGraph' a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)} := by
    intro φ; ext x; constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hlt, rfl⟩
      exact ⟨a, b, ha, hb, h2b, hlt, rfl⟩
    · rintro ⟨a, b, ha, hb, h2b, hlt, rfl⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hlt, rfl⟩
  tfae_have 1 → 2 := by
    intro hi
    obtain ⟨f, hf, hfn⟩ := thm47_i_implies_ii_ge p q q.pos (le_of_lt h2q) hr
      (equiv_iff.mpr hi)
    exact ⟨f, hf, fun n hn => by
      obtain ⟨a, b, ha, hb, h2b, hlt, hcohom⟩ := hfn n hn
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hlt, hcohom⟩⟩
  tfae_have 2 → 3 := by
    intro ⟨f, hf, hfn⟩
    have h := thm47_ii_implies_iii p q q.pos (le_of_lt h2q)
      ⟨f, hf, fun n hn => by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, h2b, hlt, hcohom⟩ := hfn n hn
        exact ⟨a, b, ha, hb, h2b, hlt, hcohom⟩⟩
    intro ε hε; obtain ⟨δ, hδ, hd⟩ := h ε hε
    exact ⟨δ, hδ, fun ⟨a, ha⟩ ⟨b, hb⟩ h2b hpos hlt φ => hd a b ha hb h2b hpos hlt φ⟩
  tfae_have 3 → 4 := by
    -- (iii) → ConvergesTo: uniform left-continuity gives d → 0 directly
    intro h3 as bs h2bs hconv hbelow
    unfold ConvergesTo
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := h3 (ε / 2) (by linarith)
    rw [Metric.tendsto_atTop] at hconv
    obtain ⟨N, hN⟩ := hconv δ (by exact_mod_cast hδ)
    use N; intro n hn
    rw [Real.dist_0_eq_abs, abs_of_nonneg (asympSpecDistance_nonneg _ _)]
    have hne : (spectralDistanceSet (FractionGraph (as n) (bs n))
      (FractionGraph p q)).Nonempty := ⟨_, spectralPoint_nonempty.some, rfl⟩
    have hbound : ∀ x ∈ spectralDistanceSet (FractionGraph (as n) (bs n))
        (FractionGraph p q), x ≤ ε / 2 := by
      rintro x ⟨φ, rfl⟩
      have hdist := hN n hn; rw [Real.dist_eq] at hdist
      have hpos : 0 < (p : ℝ) / q - (as n : ℝ) / bs n := by linarith [hbelow n]
      have hdiff : (p : ℝ) / q - (as n : ℝ) / bs n < δ := by linarith [abs_lt.mp hdist]
      have h := hd (as n) (bs n) (h2bs n) hpos hdiff φ
      -- h : φ(E_{p/q}) - φ(E_{a_n/b_n}) < ε/2
      -- Need: |φ.eval(E_{a_n/b_n}) - φ.eval(E_{p/q})| ≤ ε/2
      -- Since a/b < p/q, by monotonicity φ(E_{a/b}) ≤ φ(E_{p/q})
      have hmono : φ.eval (FractionGraph (as n) (bs n)) ≤ φ.eval (FractionGraph p q) := by
        apply φ.mono_cohom
        have hle : (as n : ℚ) / bs n ≤ (p : ℚ) / q := by
          apply (Rat.cast_le (K := ℝ)).1; push_cast; exact le_of_lt (hbelow n)
        simpa using (fractionGraph_ordering (as n) (bs n) p q
          (bs n).pos q.pos (h2bs n) (le_of_lt h2q)).mp hle
      rw [abs_of_nonpos (by linarith)]; linarith
    change sSup _ < ε; linarith [csSup_le hne hbound]
  tfae_have 4 → 5 := by
    intro h4
    -- ConvergesTo → pointwise, then use thm47_iv_implies_v
    have h4' : ∀ (as' bs' : ℕ → ℕ) (has_pos : ∀ n, 0 < as' n),
        (∀ n, 0 < bs' n) → (∀ n, 2 * bs' n ≤ as' n) →
        Filter.Tendsto (fun n => (as' n : ℝ) / bs' n)
          Filter.atTop (nhds ((p : ℝ) / q)) →
        (∀ n, (as' n : ℝ) / bs' n < (p : ℝ) / q) →
        ∀ φ : SpectralPoint,
          Filter.Tendsto
            (fun n => φ.eval (@FractionGraph' (as' n) (bs' n)
              ⟨Nat.pos_iff_ne_zero.mp (has_pos n)⟩))
            Filter.atTop (nhds (φ.eval (FractionGraph' p q))) := by
      intro as' bs' has_pos hbs_pos h2bs hconv' hbelow' φ
      exact spectral_converges_pointwise _ _ (h4 (fun n => ⟨as' n, has_pos n⟩)
        (fun n => ⟨bs' n, hbs_pos n⟩) h2bs hconv' hbelow') φ
    have h := thm47_iv_implies_v p q q.pos h2q h4'
    intro φ; rw [set_conv]; exact h φ
  tfae_have 5 → 1 := by
    intro h5
    apply equiv_iff.mp
    apply leftContinuity_implies_circleGraph_asymp_equiv
      ((p : ℝ) / q) hr p q q.pos (le_of_lt h2q) rfl
    intro φ; rw [← set_conv]; exact h5 φ
  tfae_finish

/-! ### Sequential closure of fraction graphs equals open circle graphs -/

/-- `ψ(graphToInfiniteGraph (FractionGraph' n 1)) = n` for every SpectralPointInf.
    E_{n/1} is edgeless on n vertices (`fractionGraph_one_edgeless`). -/
private theorem spectralPointInf_fractionGraph_one_eq (ψ : SpectralPointInf)
    (n : ℕ) [NeZero n] :
    ψ.eval (graphToInfiniteGraph (FractionGraph' n 1)) = n := by
  have hedg : fractionGraph n 1 = ⊥ := fractionGraph_one_edgeless n
  have hiso : InfiniteGraphIso (graphToInfiniteGraph (FractionGraph' n 1))
      (InfiniteGraph.edgeless n) := by
    refine ⟨⟨(Universality.edgelessIsoZMod n).symm.toEquiv, ?_⟩⟩
    intro u v
    rw [show (graphToInfiniteGraph (FractionGraph' n 1)).graph =
        (⊥ : SimpleGraph (ZMod n)) from hedg]
    simp [InfiniteGraph.edgeless]
  rw [ψ.eval_congr hiso]; exact ψ.normalized n

/-- `ψ(E_2^o) = 2` for every `SpectralPointInf`. -/
private theorem spectralPointInf_open_two_eq_two (ψ : SpectralPointInf) :
    ψ.eval (circleGraphOpenInf 2 (by norm_num : (2 : ℝ) ≤ 2)) = 2 := by
  apply le_antisymm
  · have hcohom : Cohom (circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2))
        (fractionGraph 2 1) := by
      have := circleGraphOpen_to_fractionGraph 2 1 (by omega) (by omega)
      simpa using this
    have h1 : ψ.eval (circleGraphOpenInf 2 (by norm_num : (2 : ℝ) ≤ 2)) ≤
        ψ.eval (graphToInfiniteGraph (FractionGraph' 2 1)) :=
      ψ.mono_cohom _ _ hcohom
    have h2 : ψ.eval (graphToInfiniteGraph (FractionGraph' 2 1)) = 2 := by
      simpa using spectralPointInf_fractionGraph_one_eq ψ 2
    linarith
  · exact spectralPointInf_open_two_ge_two ψ

/-- R1b: every open circle graph is a sequential limit of fraction graphs.
    For every r ≥ 2, there is a sequence (ps n, qs n) of pairs of natural numbers with
    `ps n / qs n ≥ 2` and `ps n / qs n → r` such that the fraction graphs
    `E_{ps n / qs n}` converge to `E_r^o` in the infinite graph distance. -/
theorem circleGraphOpen_is_limit_of_fractionGraphs (r : ℝ) (hr : 2 ≤ r) :
    ∃ (ps qs : ℕ → ℕ) (_ : ∀ n, NeZero (ps n)),
      (∀ n, 0 < qs n) ∧ (∀ n, 2 * qs n ≤ ps n) ∧
      Filter.Tendsto (fun n => (ps n : ℝ) / qs n) Filter.atTop (nhds r) ∧
      ConvergesToInf (fun n => graphToInfiniteGraph (FractionGraph' (ps n) (qs n)))
                     (circleGraphOpenInf r hr) := by
  by_cases hirr : Irrational r
  · -- Irrational r: r > 2 automatically; use continued fraction convergents.
    have hr_gt : 2 < r := lt_of_le_of_ne hr (fun h => hirr ⟨2, by simp [h]⟩)
    -- For each n, use convergent data if > 2, else fallback to (3, 1). Eventually > 2.
    obtain ⟨N0, hN0⟩ := convergent_gt_two_eventually_nat r hr_gt
    -- Define the sequence using the shifted even convergents.
    -- Use convergent_nat_data_of_gt_two at index (n + N0 even shifted).
    -- Simplest: define ps, qs via Classical.choice from convergent_nat_data_of_gt_two.
    classical
    refine ⟨fun n => (convergent_nat_data_of_gt_two r hirr (n + N0)
        (hN0 (n + N0) (by omega))).choose,
      fun n => ?_, fun n => ⟨?_⟩, fun n => ?_, fun n => ?_, ?_, ?_⟩
    · exact (convergent_nat_data_of_gt_two r hirr (n + N0)
        (hN0 (n + N0) (by omega))).choose_spec.choose
    · -- NeZero: p > 0
      exact Nat.pos_iff_ne_zero.mp
        (convergent_nat_data_of_gt_two r hirr (n + N0)
          (hN0 (n + N0) (by omega))).choose_spec.choose_spec.1
    · -- 0 < qs n
      exact
        (convergent_nat_data_of_gt_two r hirr (n + N0)
          (hN0 (n + N0) (by omega))).choose_spec.choose_spec.2.1
    · -- 2 * qs n ≤ ps n
      exact
        (convergent_nat_data_of_gt_two r hirr (n + N0)
          (hN0 (n + N0) (by omega))).choose_spec.choose_spec.2.2.1
    · -- ps n / qs n → r
      have htend := tendsto_convergent_real r
      -- We have: ps n / qs n = r.convergent (n + N0) (for each n)
      have heq : ∀ n, ((convergent_nat_data_of_gt_two r hirr (n + N0)
          (hN0 (n + N0) (by omega))).choose : ℝ) /
          ((convergent_nat_data_of_gt_two r hirr (n + N0)
            (hN0 (n + N0) (by omega))).choose_spec.choose : ℝ) =
          (r.convergent (n + N0) : ℝ) := fun n =>
        ((convergent_nat_data_of_gt_two r hirr (n + N0)
            (hN0 (n + N0) (by omega))).choose_spec.choose_spec.2.2.2.1).symm
      apply Filter.Tendsto.congr (fun n => (heq n).symm)
      -- (fun n => r.convergent (n + N0)) → r
      exact (htend.comp (Filter.tendsto_add_atTop_nat N0))
    · -- ConvergesToInf
      haveI : ∀ n, NeZero ((convergent_nat_data_of_gt_two r hirr (n + N0)
          (hN0 (n + N0) (by omega))).choose) := fun n =>
        ⟨Nat.pos_iff_ne_zero.mp
          (convergent_nat_data_of_gt_two r hirr (n + N0)
            (hN0 (n + N0) (by omega))).choose_spec.choose_spec.1⟩
      apply fractionGraph_convergesToInf_circleGraph r hr hirr
      · intro n
        exact
          (convergent_nat_data_of_gt_two r hirr (n + N0)
            (hN0 (n + N0) (by omega))).choose_spec.choose_spec.2.1
      · intro n
        exact
          (convergent_nat_data_of_gt_two r hirr (n + N0)
            (hN0 (n + N0) (by omega))).choose_spec.choose_spec.2.2.1
      · -- convergence
        have htend := tendsto_convergent_real r
        have heq : ∀ n, ((convergent_nat_data_of_gt_two r hirr (n + N0)
            (hN0 (n + N0) (by omega))).choose : ℝ) /
            ((convergent_nat_data_of_gt_two r hirr (n + N0)
              (hN0 (n + N0) (by omega))).choose_spec.choose : ℝ) =
            (r.convergent (n + N0) : ℝ) := fun n =>
          ((convergent_nat_data_of_gt_two r hirr (n + N0)
              (hN0 (n + N0) (by omega))).choose_spec.choose_spec.2.2.2.1).symm
        apply Filter.Tendsto.congr (fun n => (heq n).symm)
        exact (htend.comp (Filter.tendsto_add_atTop_nat N0))
  · -- Rational r: r = p/q with 2q ≤ p, use constant sequence.
    rw [Irrational, not_not] at hirr
    obtain ⟨qrat, hqrat⟩ := hirr
    have hq_pos : 0 < qrat.den := qrat.pos
    have hr_num_pos : 0 < qrat.num := by
      rw [← hqrat] at hr
      have h0 : (0 : ℝ) < (qrat : ℝ) := by linarith
      exact_mod_cast (Rat.num_pos.mpr (by exact_mod_cast h0))
    set p : ℕ := qrat.num.toNat with hp_def
    set qn : ℕ := qrat.den with hq_def
    have hp_pos : 0 < p := by simp only [hp_def]; omega
    haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp_pos⟩
    have hpq_cast : (p : ℝ) / (qn : ℝ) = r := by
      have h1 : (qrat.num : ℝ) = (p : ℝ) := by
        simp only [hp_def]
        exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hr_num_pos)).symm
      rw [← hqrat, Rat.cast_def, ← h1]
    have h2qle : 2 * qn ≤ p := by
      have : (2 : ℝ) ≤ (p : ℝ) / qn := hpq_cast ▸ hr
      have hqn_pos : (0 : ℝ) < (qn : ℝ) := Nat.cast_pos.mpr hq_pos
      have := (le_div_iff₀ hqn_pos).mp this
      exact_mod_cast this
    refine ⟨fun _ => p, fun _ => qn, fun _ => ⟨Nat.pos_iff_ne_zero.mp hp_pos⟩,
      fun _ => hq_pos, fun _ => h2qle, ?_, ?_⟩
    · -- constant sequence converges to p/qn = r
      simp only [hpq_cast]; exact tendsto_const_nhds
    · -- ConvergesToInf for constant sequence
      apply convergesToInf_of_uniform_bound
      intro ε hε
      refine ⟨0, fun n _ ψ => ?_⟩
      -- ψ(graphToInfiniteGraph (FractionGraph' p qn)) = ψ(circleGraphOpenInf r hr)
      have h := spectralPointInf_open_eq_fraction p qn hq_pos h2qle ψ
      -- h : ψ(circleGraphOpenInf (p/qn) _) = ψ(graphToInfiniteGraph (FractionGraph' p qn))
      -- transport via hpq_cast
      have hr_pq : 2 ≤ (p : ℝ) / qn := hpq_cast ▸ hr
      have hopen_eq : ψ.eval (circleGraphOpenInf ((p : ℝ) / qn) hr_pq) =
          ψ.eval (circleGraphOpenInf r hr) := by
        apply ψ.eval_congr
        exact ⟨⟨Equiv.refl _, fun {u v} => by
          simp only [circleGraphOpenInf, circleGraphOpen, Equiv.refl_apply, hpq_cast]
          rfl⟩⟩
      rw [show ψ.eval (graphToInfiniteGraph (FractionGraph' p qn)) =
            ψ.eval (circleGraphOpenInf r hr) from by rw [← h, hopen_eq]]
      simp [hε]

/-- R1a (irrational r version): in the irrational case, `circleGraphOpen_closed_under_limits`
    follows directly from the sandwich with convergents. -/
private theorem circleGraphOpen_closed_under_limits_irrational
    (rs : ℕ → ℝ) (h_rs : ∀ n, 2 ≤ rs n)
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (hrconv : Filter.Tendsto rs Filter.atTop (nhds r)) :
    ConvergesToInf (fun n => circleGraphOpenInf (rs n) (h_rs n))
                   (circleGraphOpenInf r hr) := by
  have hr_gt : 2 < r := lt_of_le_of_ne hr (fun h => hirr ⟨2, by simp [h]⟩)
  apply convergesToInf_of_uniform_bound
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    fractionGraph_uniform_continuity_irrational r hr hirr ε hε
  have hconv_r := tendsto_convergent_real r
  rw [Metric.tendsto_atTop] at hconv_r
  obtain ⟨K, hK⟩ := hconv_r δ (by exact_mod_cast hδ_pos)
  obtain ⟨n0, a, b, c, d0, ha, hb, hc, hd, h2b, h2d, hratio_a, hratio_c,
      _, _, _, hK_le_2n0⟩ := even_odd_convergent_pair_data_large r hr_gt hirr K
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  haveI : NeZero c := ⟨Nat.pos_iff_ne_zero.mp hc⟩
  have hab_lt : (a : ℝ) / b < r := by
    simpa [hratio_a] using convergent_even_lt_irrational r hirr n0
  have hcd_gt : r < (c : ℝ) / d0 := by
    calc r < (r.convergent (2 * n0 + 1) : ℝ) := convergent_odd_gt_irrational r hirr n0
      _ = (c : ℝ) / d0 := hratio_c
  have hab_near : |(a : ℝ) / b - r| < δ := by
    have h := hK (2 * n0) hK_le_2n0
    rw [show (r.convergent (2 * n0) : ℝ) = (a : ℝ) / b from hratio_a] at h
    simpa [Real.dist_eq] using h
  have hcd_near : |(c : ℝ) / d0 - r| < δ := by
    have h := hK (2 * n0 + 1) (by omega)
    rw [show (r.convergent (2 * n0 + 1) : ℝ) = (c : ℝ) / d0 from hratio_c] at h
    simpa [Real.dist_eq] using h
  rw [Metric.tendsto_atTop] at hrconv
  obtain ⟨N₁, hN₁⟩ := hrconv (r - (a : ℝ) / b) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hrconv ((c : ℝ) / d0 - r) (by linarith)
  refine ⟨max N₁ N₂, fun n hn ψ => ?_⟩
  have hdn₁ := hN₁ n (le_of_max_le_left hn); rw [Real.dist_eq] at hdn₁
  have hdn₂ := hN₂ n (le_of_max_le_right hn); rw [Real.dist_eq] at hdn₂
  have hrs_gt : (a : ℝ) / b < rs n := by linarith [abs_lt.mp hdn₁]
  have hrs_lt : rs n < (c : ℝ) / d0 := by linarith [abs_lt.mp hdn₂]
  set φ := restrictionMap ψ
  have hlo_rsn : φ.eval (FractionGraph' a b) ≤ ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) := by
    calc φ.eval (FractionGraph' a b)
        = ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) := rfl
      _ ≤ ψ.eval (circleGraphClosedInf (rs n) (h_rs n)) :=
          spectralPointInf_fraction_le_closed (rs n) (h_rs n) ψ a b hb h2b hrs_gt
      _ ≤ ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) :=
          spectralPointInf_closed_le_open (rs n) (h_rs n) ψ
  have hhi_rsn : ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) ≤ φ.eval (FractionGraph' c d0) :=
    spectralPointInf_open_le_fraction (rs n) (h_rs n) ψ c d0 hd h2d hrs_lt
  have hlo_r : φ.eval (FractionGraph' a b) ≤ ψ.eval (circleGraphOpenInf r hr) := by
    calc φ.eval (FractionGraph' a b)
        = ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) := rfl
      _ ≤ ψ.eval (circleGraphClosedInf r hr) :=
          spectralPointInf_fraction_le_closed r hr ψ a b hb h2b hab_lt
      _ ≤ ψ.eval (circleGraphOpenInf r hr) :=
          spectralPointInf_closed_le_open r hr ψ
  have hhi_r : ψ.eval (circleGraphOpenInf r hr) ≤ φ.eval (FractionGraph' c d0) :=
    spectralPointInf_open_le_fraction r hr ψ c d0 hd h2d hcd_gt
  have hgap_lt : φ.eval (FractionGraph' c d0) - φ.eval (FractionGraph' a b) < ε := by
    calc φ.eval (FractionGraph' c d0) - φ.eval (FractionGraph' a b)
        ≤ |φ.eval (FractionGraph' c d0) - φ.eval (FractionGraph' a b)| := le_abs_self _
      _ ≤ asympSpecDistance (FractionGraph' a b) (FractionGraph' c d0) := by
          rw [asympSpecDistance_symm]; exact spectralPoint_dist_le _ _ φ
      _ < ε := hδ a b c d0 ha hc hb hd h2b h2d hab_near hcd_near
  rw [abs_lt]; refine ⟨?_, ?_⟩ <;> linarith

/-- R1a (rational case, r > 2): under the Theorem 4.12 (i) hypothesis
    `AsympCohomEquivInf E_r^c E_r^o` at rational r > 2, we get a uniform sandwich bound
    for rational r = p/q in terms of fraction graphs `E_{a/b}` and `E_{c/d}`.
    This extracts the left-δ from TFAE (iii) and the right-δ from
    `fractionGraph_convergence_from_above'` (which doesn't require coprimality). -/
private theorem circleGraphOpen_closed_under_limits_rational_aux
    (p q : ℕ+) (h2q : 2 * q < p)
    (hhyp_pq : AsympCohomEquivInf
      (circleGraphClosedInf ((p : ℝ) / q) (by
        rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q))
      (circleGraphOpenInf ((p : ℝ) / q) (by
        rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (a b c d : ℕ) (_ : NeZero a) (_ : NeZero c) (_ : 0 < b) (_ : 0 < d),
      2 * b ≤ a ∧ 2 * d ≤ c ∧
      (a : ℝ) / b < (p : ℝ) / q ∧ (p : ℝ) / q < (c : ℝ) / d ∧
      ∀ φ : SpectralPoint,
        φ.eval (FractionGraph' c d) - φ.eval (FractionGraph' a b) < ε := by
  -- From TFAE (i) → (iii), get uniform left-continuity at p/q
  have hiff := (theorem_4_12_tfae p q h2q).out 0 2
  have hiii := hiff.mp hhyp_pq
  obtain ⟨δ_L, hδL_pos, hδL⟩ := hiii (ε / 2) (by linarith)
  -- Left pair: a = p*N - 1, b = q*N for N large
  -- We need N such that 1/(q*N) < δ_L, i.e., N > 1/(q*δ_L)
  have hqL_pos : (0 : ℝ) < (q : ℝ) * δ_L :=
    mul_pos (Nat.cast_pos.mpr q.pos) hδL_pos
  obtain ⟨NL, hNL⟩ := exists_nat_gt (1 / ((q : ℝ) * δ_L))
  have hNL_pos : 1 ≤ NL := by
    have h1 : (0 : ℝ) < NL := by
      have h2 : (0 : ℝ) ≤ 1 / ((q : ℝ) * δ_L) := le_of_lt (div_pos one_pos hqL_pos)
      linarith
    exact_mod_cast h1
  -- Set a = p*NL - 1, b = q*NL
  -- From 2q < p: p ≥ 2q + 1, so p*NL ≥ (2q+1)*NL = 2*q*NL + NL ≥ 2*q*NL + 1
  have h2q_plus_one_le_p : 2 * (q : ℕ) + 1 ≤ (p : ℕ) := by
    have h1 : 2 * (q : ℕ) < (p : ℕ) := h2q
    omega
  set a : ℕ := (p : ℕ) * NL - 1 with ha_def
  set b : ℕ := (q : ℕ) * NL with hb_def
  have hb_pos : 0 < b := Nat.mul_pos q.pos hNL_pos
  have h2b_le_a : 2 * b ≤ a := by
    -- 2 * q * NL + 1 ≤ p * NL (from 2q + 1 ≤ p and NL ≥ 1)
    have hmul : (2 * (q : ℕ) + 1) * NL ≤ (p : ℕ) * NL :=
      Nat.mul_le_mul_right NL h2q_plus_one_le_p
    have hNL_le : NL ≤ (p : ℕ) * NL := Nat.le_mul_of_pos_left NL p.pos
    change 2 * ((q : ℕ) * NL) ≤ (p : ℕ) * NL - 1
    have hexpand : 2 * ((q : ℕ) * NL) + NL ≤ (p : ℕ) * NL := by
      have hrw : 2 * ((q : ℕ) * NL) + NL = (2 * (q : ℕ) + 1) * NL := by ring
      rw [hrw]; exact hmul
    omega
  have ha_pos : 0 < a := by
    have := h2b_le_a
    have h1 : 0 < 2 * b := by omega
    omega
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  -- Compute a/b = (p*NL - 1)/(q*NL) < p/q
  have hb_real_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb_pos
  have hq_real_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr q.pos
  have hp_real_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr p.pos
  have hNL_real_pos : (0 : ℝ) < (NL : ℝ) := Nat.cast_pos.mpr hNL_pos
  have hb_real_eq : (b : ℝ) = (q : ℝ) * NL := by
    change ((q : ℕ) * NL : ℕ) = (q : ℝ) * NL
    push_cast; rfl
  have ha_real_eq : (a : ℝ) = (p : ℝ) * NL - 1 := by
    have h1 : (1 : ℕ) ≤ (p : ℕ) * NL := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp p.pos) (Nat.pos_iff_ne_zero.mp hNL_pos))
    change (((p : ℕ) * NL - 1 : ℕ) : ℝ) = (p : ℝ) * NL - 1
    rw [Nat.cast_sub h1]; push_cast; rfl
  have hab_lt_pq : (a : ℝ) / b < (p : ℝ) / q := by
    rw [ha_real_eq, hb_real_eq]
    rw [div_lt_div_iff₀ (mul_pos hq_real_pos hNL_real_pos) hq_real_pos]
    nlinarith [hq_real_pos, hNL_real_pos]
  have hpq_sub_ab : (p : ℝ) / q - (a : ℝ) / b = 1 / ((q : ℝ) * NL) := by
    rw [ha_real_eq, hb_real_eq]
    field_simp
    ring
  have hgap_lt_δL : (p : ℝ) / q - (a : ℝ) / b < δ_L := by
    rw [hpq_sub_ab]
    rw [div_lt_iff₀ (mul_pos hq_real_pos hNL_real_pos)]
    -- 1 < δ_L * (q * NL), i.e., 1/(q*δ_L) < NL
    have h1 : 1 / ((q : ℝ) * δ_L) < NL := hNL
    have h2 : 1 / ((q : ℝ) * δ_L) * ((q : ℝ) * δ_L) = 1 := by
      field_simp
    nlinarith [hq_real_pos, hδL_pos, hNL_real_pos, h1, h2]
  have hgap_pos : 0 < (p : ℝ) / q - (a : ℝ) / b := by linarith
  -- Right pair: use fractionGraph_convergence_from_above'
  -- with ps n = p*(n+1) + 1, qs n = q*(n+1)
  set ps : ℕ → ℕ := fun n => (p : ℕ) * (n + 1) + 1 with hps_def
  set qs : ℕ → ℕ := fun n => (q : ℕ) * (n + 1) with hqs_def
  have hqs_pos : ∀ n, 0 < qs n := fun n => Nat.mul_pos q.pos (Nat.succ_pos n)
  have h2qs : ∀ n, 2 * qs n ≤ ps n := fun n => by
    change 2 * ((q : ℕ) * (n + 1)) ≤ (p : ℕ) * (n + 1) + 1
    calc 2 * ((q : ℕ) * (n + 1))
        = (2 * (q : ℕ)) * (n + 1) := by ring
      _ ≤ (p : ℕ) * (n + 1) := Nat.mul_le_mul_right (n + 1) (le_of_lt h2q)
      _ ≤ (p : ℕ) * (n + 1) + 1 := Nat.le_succ _
  have hfrom_above : ∀ n, ((p : ℕ) : ℚ) / (q : ℕ) ≤ (ps n : ℚ) / qs n := by
    intro n
    have hq_ℚ : (0 : ℚ) < (q : ℕ) := Nat.cast_pos.mpr q.pos
    have hqs_ℚ : (0 : ℚ) < (qs n : ℕ) := Nat.cast_pos.mpr (hqs_pos n)
    rw [div_le_div_iff₀ hq_ℚ hqs_ℚ]
    -- Need: p * qs n ≤ ps n * q (in ℚ)
    -- ps n = p*(n+1) + 1, qs n = q*(n+1)
    -- p * q*(n+1) ≤ (p*(n+1) + 1) * q = p*q*(n+1) + q
    change ((p : ℕ) : ℚ) * (qs n : ℕ) ≤ (ps n : ℚ) * ((q : ℕ) : ℚ)
    rw [hps_def, hqs_def]; push_cast
    have hq_pos' : (0 : ℚ) < (q : ℕ) := hq_ℚ
    nlinarith
  have hconv_rat : Filter.Tendsto (fun n => (ps n : ℚ) / qs n) Filter.atTop
      (nhds (((p : ℕ) : ℚ) / (q : ℕ))) := by
    -- (p*(n+1)+1)/(q*(n+1)) = p/q + 1/(q*(n+1)) → p/q
    have heq : ∀ n : ℕ, ((ps n : ℕ) : ℚ) / ((qs n : ℕ) : ℚ) =
        ((p : ℕ) : ℚ) / ((q : ℕ) : ℚ) + 1 / (((q : ℕ) : ℚ) * ((n : ℚ) + 1)) := by
      intro n
      rw [hps_def, hqs_def]
      have hq_ℚ_ne : ((q : ℕ) : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr q.pos)
      have hn1_pos : (0 : ℚ) < (n : ℚ) + 1 := by
        have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        linarith
      have hn1_ne : ((n : ℚ) + 1) ≠ 0 := ne_of_gt hn1_pos
      have hqn1_ne : ((q : ℕ) : ℚ) * ((n : ℚ) + 1) ≠ 0 := mul_ne_zero hq_ℚ_ne hn1_ne
      push_cast
      field_simp
    apply Filter.Tendsto.congr (fun n => (heq n).symm)
    -- p/q + 1/(q*(n+1)) → p/q + 0 = p/q
    have htend : Filter.Tendsto (fun n : ℕ => 1 / (((q : ℕ) : ℚ) * ((n : ℚ) + 1)))
        Filter.atTop (nhds 0) := by
      have hq_ℚ_pos : (0 : ℚ) < (q : ℕ) := Nat.cast_pos.mpr q.pos
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℚ) + 1)) Filter.atTop Filter.atTop := by
        have ht1 : Filter.Tendsto (fun n : ℕ => (n : ℚ)) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop
        exact ht1.atTop_add tendsto_const_nhds
      have h2 : Filter.Tendsto (fun n : ℕ => ((q : ℕ) : ℚ) * ((n : ℚ) + 1))
          Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop hq_ℚ_pos h1
      have h3 : Filter.Tendsto
          (fun n : ℕ => (((q : ℕ) : ℚ) * ((n : ℚ) + 1))⁻¹) Filter.atTop (nhds 0) :=
        Filter.Tendsto.inv_tendsto_atTop h2
      refine Filter.Tendsto.congr (fun n => ?_) h3
      rw [one_div]
    have := htend.const_add (((p : ℕ) : ℚ) / ((q : ℕ) : ℚ))
    simpa using this
  haveI : NeZero (p : ℕ) := ⟨Nat.pos_iff_ne_zero.mp p.pos⟩
  have hps_pos : ∀ n, 0 < ps n := fun n => by
    change 0 < (p : ℕ) * (n + 1) + 1
    omega
  haveI : ∀ n, NeZero (ps n) := fun n => ⟨Nat.pos_iff_ne_zero.mp (hps_pos n)⟩
  have hconv_spec := fractionGraph_convergence_from_above'
    (p : ℕ) (q : ℕ) q.pos (le_of_lt h2q) ps qs hqs_pos h2qs hfrom_above hconv_rat
  -- Extract N from ConvergesTo such that asympSpecDistance < ε/2
  unfold ConvergesTo at hconv_spec
  rw [Metric.tendsto_atTop] at hconv_spec
  obtain ⟨N, hN⟩ := hconv_spec (ε / 2) (by linarith)
  -- Also need p/q < ps N / qs N (strict, from hfrom_above which is ≤; actually we have >)
  have hstrict : ∀ n, ((p : ℕ) : ℚ) / (q : ℕ) < (ps n : ℚ) / qs n := by
    intro n
    have hq_ℚ : (0 : ℚ) < (q : ℕ) := Nat.cast_pos.mpr q.pos
    have hqs_ℚ : (0 : ℚ) < (qs n : ℕ) := Nat.cast_pos.mpr (hqs_pos n)
    rw [div_lt_div_iff₀ hq_ℚ hqs_ℚ]
    change ((p : ℕ) : ℚ) * (qs n : ℕ) < (ps n : ℚ) * ((q : ℕ) : ℚ)
    rw [hps_def, hqs_def]; push_cast
    have hq_pos' : (0 : ℚ) < (q : ℕ) := hq_ℚ
    nlinarith
  have hpq_lt_ccd : (p : ℝ) / q < (ps N : ℝ) / qs N := by
    have h := hstrict N
    have hcast : (((p : ℕ) : ℚ) / ((q : ℕ) : ℚ) : ℝ) < (((ps N : ℚ) / qs N) : ℝ) := by
      exact_mod_cast h
    push_cast at hcast
    exact hcast
  -- asympSpecDistance < ε/2
  have hdist_lt := hN N (le_refl N)
  rw [Real.dist_0_eq_abs, abs_of_nonneg (asympSpecDistance_nonneg _ _)] at hdist_lt
  -- Assemble
  refine ⟨a, b, ps N, qs N, inferInstance, inferInstance, hb_pos, hqs_pos N,
    h2b_le_a, h2qs N, hab_lt_pq, hpq_lt_ccd, ?_⟩
  intro φ
  -- φ(E_{c/d}) - φ(E_{a/b})
  --   = (φ(E_{c/d}) - φ(E_{p/q})) + (φ(E_{p/q}) - φ(E_{a/b}))
  -- First ≤ |φ(c/d) - φ(p/q)| ≤ asympSpecDistance < ε/2
  -- Second < ε/2 by (iii)
  have h_right : φ.eval (FractionGraph' (ps N) (qs N)) - φ.eval (FractionGraph' (p : ℕ) q) <
      ε / 2 := by
    calc φ.eval (FractionGraph' (ps N) (qs N)) - φ.eval (FractionGraph' (p : ℕ) q)
        ≤ |φ.eval (FractionGraph' (ps N) (qs N)) - φ.eval (FractionGraph' (p : ℕ) q)| :=
          le_abs_self _
      _ ≤ asympSpecDistance (FractionGraph' (ps N) (qs N)) (FractionGraph' (p : ℕ) q) :=
          spectralPoint_dist_le _ _ φ
      _ < ε / 2 := hdist_lt
  -- Left: apply hδL with a', b' : ℕ+ built from a, b
  let a_pn : ℕ+ := ⟨a, ha_pos⟩
  let b_pn : ℕ+ := ⟨b, hb_pos⟩
  have h2b_le_a_pn : 2 * b_pn ≤ a_pn := by
    change (2 * b : ℕ) ≤ a
    exact h2b_le_a
  have ha_cast : (a_pn : ℕ) = a := rfl
  have hb_cast : (b_pn : ℕ) = b := rfl
  have h_left : φ.eval (FractionGraph p q) - φ.eval (FractionGraph a_pn b_pn) < ε / 2 :=
    hδL a_pn b_pn h2b_le_a_pn hgap_pos hgap_lt_δL φ
  -- Reduce to FractionGraph' via defeq
  have h_left' : φ.eval (FractionGraph' (p : ℕ) (q : ℕ)) - φ.eval (FractionGraph' a b) <
      ε / 2 := h_left
  linarith

/-- R1a (rational case at r > 2): direct version using p, q from the rational decomposition. -/
private theorem circleGraphOpen_closed_under_limits_rational_gt_two
    (hhyp : ∀ (p q : ℕ+) (h2q : 2 * q < p),
      have hr : 2 ≤ (p : ℝ) / q := by
        rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q
      AsympCohomEquivInf (circleGraphClosedInf ((p : ℝ) / q) hr)
                    (circleGraphOpenInf ((p : ℝ) / q) hr))
    (rs : ℕ → ℝ) (h_rs : ∀ n, 2 ≤ rs n)
    (r : ℝ) (hr : 2 ≤ r) (hrconv : Filter.Tendsto rs Filter.atTop (nhds r))
    (hnirr : ¬ Irrational r) (hr_gt : 2 < r) :
    ConvergesToInf (fun n => circleGraphOpenInf (rs n) (h_rs n))
                   (circleGraphOpenInf r hr) := by
  -- Extract rational representation r = p/q with 2q < p
  rw [Irrational, not_not] at hnirr
  obtain ⟨qrat, hqrat⟩ := hnirr
  have hq_pos : 0 < qrat.den := qrat.pos
  have hr_num_pos : 0 < qrat.num := by
    rw [← hqrat] at hr_gt
    have h0 : (0 : ℝ) < (qrat : ℝ) := by linarith
    exact_mod_cast (Rat.num_pos.mpr (by exact_mod_cast h0))
  set p_val : ℕ := qrat.num.toNat with hp_val_def
  set q_val : ℕ := qrat.den with hq_val_def
  have hp_pos : 0 < p_val := by simp only [hp_val_def]; omega
  have hpq_cast : (p_val : ℝ) / (q_val : ℝ) = r := by
    have h1 : (qrat.num : ℝ) = (p_val : ℝ) := by
      simp only [hp_val_def]
      exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hr_num_pos)).symm
    rw [← hqrat, Rat.cast_def, ← h1]
  have h2q_lt : 2 * q_val < p_val := by
    have h : (2 : ℝ) < (p_val : ℝ) / q_val := hpq_cast ▸ hr_gt
    have hqn_pos : (0 : ℝ) < (q_val : ℝ) := Nat.cast_pos.mpr hq_pos
    have := (lt_div_iff₀ hqn_pos).mp h
    exact_mod_cast this
  set p : ℕ+ := ⟨p_val, hp_pos⟩ with hp_pn_def
  set q : ℕ+ := ⟨q_val, hq_pos⟩ with hq_pn_def
  have h2q_pn : 2 * q < p := by
    change (2 : ℕ) * q_val < p_val
    exact h2q_lt
  -- p/q (as PNat) equals p_val/q_val = r
  have hpq_eq_r : ((p : ℕ) : ℝ) / q = r := by
    change (p_val : ℝ) / q_val = r
    exact hpq_cast
  have hhyp_pq := hhyp p q h2q_pn
  -- ConvergesToInf via uniform bound
  apply convergesToInf_of_uniform_bound
  intro ε hε
  obtain ⟨a, b, c, d, hNe_a, hNe_c, hb_pos, hd_pos, h2b, h2d, hab_lt_pq,
    hpq_lt_cd, hgap_bound⟩ :=
    circleGraphOpen_closed_under_limits_rational_aux p q h2q_pn hhyp_pq ε hε
  -- Translate a/b < p/q < c/d to a/b < r < c/d
  have hab_lt_r : (a : ℝ) / b < r := by rw [← hpq_eq_r]; exact hab_lt_pq
  have hcd_gt_r : r < (c : ℝ) / d := by rw [← hpq_eq_r]; exact hpq_lt_cd
  -- Find N such that a/b < rs n < c/d for n ≥ N
  rw [Metric.tendsto_atTop] at hrconv
  obtain ⟨N₁, hN₁⟩ := hrconv (r - (a : ℝ) / b) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hrconv ((c : ℝ) / d - r) (by linarith)
  refine ⟨max N₁ N₂, fun n hn ψ => ?_⟩
  have hdn₁ := hN₁ n (le_of_max_le_left hn); rw [Real.dist_eq] at hdn₁
  have hdn₂ := hN₂ n (le_of_max_le_right hn); rw [Real.dist_eq] at hdn₂
  have hrs_gt : (a : ℝ) / b < rs n := by linarith [abs_lt.mp hdn₁]
  have hrs_lt : rs n < (c : ℝ) / d := by linarith [abs_lt.mp hdn₂]
  -- Set up sandwich for rs n and r
  set φ := restrictionMap ψ
  -- AsympCohomEquivInf gives ψ(E_r^c) = ψ(E_r^o) via equiv_iff (from theorem_4_12_tfae's proof)
  have hclosed_eq_open_pq : ∀ (ψ' : SpectralPointInf),
      ψ'.eval (circleGraphClosedInf ((p : ℕ) / (q : ℕ) : ℝ)
        (by rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q_pn)) =
      ψ'.eval (circleGraphOpenInf ((p : ℕ) / (q : ℕ) : ℝ)
        (by rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q_pn)) := by
    intro ψ'
    obtain ⟨h1, h2⟩ := hhyp_pq
    have hle1 := (spectral_duality_inf _ _).mp h1 ψ'
    have hle2 := (spectral_duality_inf _ _).mp h2 ψ'
    linarith
  have hclosed_eq_open_r : ψ.eval (circleGraphClosedInf r hr) =
      ψ.eval (circleGraphOpenInf r hr) := by
    -- r = p/q, so this follows from hclosed_eq_open_pq via congr
    have hr' : 2 ≤ ((p : ℕ) : ℝ) / q := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q_pn
    have hcongr_closed : ψ.eval (circleGraphClosedInf r hr) =
        ψ.eval (circleGraphClosedInf ((p : ℕ) / (q : ℕ) : ℝ) hr') := by
      apply ψ.eval_congr
      refine ⟨⟨Equiv.refl _, fun {u v} => ?_⟩⟩
      simp only [circleGraphClosedInf, circleGraphClosed, Equiv.refl_apply, hpq_eq_r]
      rfl
    have hcongr_open : ψ.eval (circleGraphOpenInf r hr) =
        ψ.eval (circleGraphOpenInf ((p : ℕ) / (q : ℕ) : ℝ) hr') := by
      apply ψ.eval_congr
      refine ⟨⟨Equiv.refl _, fun {u v} => ?_⟩⟩
      simp only [circleGraphOpenInf, circleGraphOpen, Equiv.refl_apply, hpq_eq_r]
      rfl
    rw [hcongr_closed, hcongr_open]; exact hclosed_eq_open_pq ψ
  -- Sandwich: E_{a/b} ≤ E_{rs n}^c ≤ E_{rs n}^o ≤ E_{c/d}
  have hlo_rsn : φ.eval (FractionGraph' a b) ≤ ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) := by
    calc φ.eval (FractionGraph' a b)
        = ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) := rfl
      _ ≤ ψ.eval (circleGraphClosedInf (rs n) (h_rs n)) :=
          spectralPointInf_fraction_le_closed (rs n) (h_rs n) ψ a b hb_pos h2b hrs_gt
      _ ≤ ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) :=
          spectralPointInf_closed_le_open (rs n) (h_rs n) ψ
  have hhi_rsn : ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) ≤ φ.eval (FractionGraph' c d) :=
    spectralPointInf_open_le_fraction (rs n) (h_rs n) ψ c d hd_pos h2d hrs_lt
  -- Same sandwich for r
  have hlo_r : φ.eval (FractionGraph' a b) ≤ ψ.eval (circleGraphOpenInf r hr) := by
    calc φ.eval (FractionGraph' a b)
        = ψ.eval (graphToInfiniteGraph (FractionGraph' a b)) := rfl
      _ ≤ ψ.eval (circleGraphClosedInf r hr) :=
          spectralPointInf_fraction_le_closed r hr ψ a b hb_pos h2b hab_lt_r
      _ ≤ ψ.eval (circleGraphOpenInf r hr) :=
          spectralPointInf_closed_le_open r hr ψ
  have hhi_r : ψ.eval (circleGraphOpenInf r hr) ≤ φ.eval (FractionGraph' c d) :=
    spectralPointInf_open_le_fraction r hr ψ c d hd_pos h2d hcd_gt_r
  -- Combine
  have hgap_lt : φ.eval (FractionGraph' c d) - φ.eval (FractionGraph' a b) < ε := hgap_bound φ
  rw [abs_lt]; refine ⟨?_, ?_⟩ <;> linarith

/-- R1a (rational case at r = 2): when the limit r = 2, we use right-continuity at (2, 1). -/
private theorem circleGraphOpen_closed_under_limits_rational_eq_two
    (rs : ℕ → ℝ) (h_rs : ∀ n, 2 ≤ rs n)
    (hrconv : Filter.Tendsto rs Filter.atTop (nhds 2)) :
    ConvergesToInf (fun n => circleGraphOpenInf (rs n) (h_rs n))
                   (circleGraphOpenInf 2 (by norm_num : (2 : ℝ) ≤ 2)) := by
  apply convergesToInf_of_uniform_bound
  intro ε hε
  -- By right-continuity at (a, b) = (2, 1) with coprime a b (gcd(2,1) = 1),
  -- for every ε there is δ > 0 with any 2 ≤ p/q within δ of 2 giving small distance
  have h2_coprime : Nat.Coprime 2 1 := by decide
  obtain ⟨δ, hδ_pos, hδ⟩ := fractionGraph_rightContinuous_uniform 2 1
    (by norm_num) (by norm_num) (by norm_num) h2_coprime (ε / 2) (by linarith)
  -- δ : ℚ. Compute its real counterpart.
  have hδ_real_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  -- Pick c/d > 2 within δ of 2 (e.g. c = 2*NM+1, d = NM)
  -- We need (2NM+1)/NM - 2 = 1/NM < δ, so NM > 1/δ
  obtain ⟨NM, hNM⟩ := exists_nat_gt (1 / (δ : ℝ))
  have hNM_pos : 1 ≤ NM := by
    have h0 : 0 ≤ 1 / (δ : ℝ) := div_nonneg zero_le_one (le_of_lt hδ_real_pos)
    have h1 : (0 : ℝ) < NM := lt_of_le_of_lt h0 hNM
    exact_mod_cast h1
  set c : ℕ := 2 * NM + 1 with hc_def
  set d : ℕ := NM with hd_def
  have hc_pos : 0 < c := by simp only [hc_def]; omega
  have hd_pos : 0 < d := by simp only [hd_def]; exact hNM_pos
  have h2d_le_c : 2 * d ≤ c := by simp only [hc_def, hd_def]; omega
  haveI : NeZero c := ⟨Nat.pos_iff_ne_zero.mp hc_pos⟩
  -- Real-valued computation: c/d = 2 + 1/NM, so c/d > 2
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have hNM_real_pos : (0 : ℝ) < (NM : ℝ) := Nat.cast_pos.mpr hNM_pos
  have hc_real_eq : (c : ℝ) = 2 * NM + 1 := by
    change ((2 * NM + 1 : ℕ) : ℝ) = 2 * NM + 1
    push_cast; rfl
  have hd_real_eq : (d : ℝ) = (NM : ℝ) := rfl
  have hcd_gt_2 : (2 : ℝ) < (c : ℝ) / d := by
    rw [hc_real_eq, hd_real_eq]
    rw [lt_div_iff₀ hNM_real_pos]; linarith
  have hcd_sub_2 : (c : ℝ) / d - 2 = 1 / NM := by
    rw [hc_real_eq, hd_real_eq]
    field_simp
    ring
  -- ℚ versions for right-continuity
  have hab_le_cd_ℚ : ((2 : ℕ) : ℚ) / (1 : ℕ) ≤ (c : ℚ) / d := by
    have hle_real : (((2 : ℕ) : ℚ) / (1 : ℕ) : ℝ) ≤ (((c : ℚ) / d) : ℝ) := by
      push_cast
      rw [hc_real_eq, hd_real_eq]
      rw [le_div_iff₀ hNM_real_pos]; nlinarith
    exact_mod_cast hle_real
  have hcd_sub_2_ℚ : ((c : ℚ) / d - ((2 : ℕ) : ℚ) / (1 : ℕ)) < δ := by
    have hlt_real : (((c : ℚ) / d - ((2 : ℕ) : ℚ) / (1 : ℕ)) : ℝ) < (δ : ℝ) := by
      push_cast
      -- goal: (c : ℝ) / d - 2 / 1 < (δ : ℝ)
      have hs : (c : ℝ) / d - 2 / 1 = 1 / NM := by
        rw [div_one]; exact hcd_sub_2
      rw [hs]
      rw [div_lt_iff₀ hNM_real_pos]
      -- 1 < δ * NM, since 1/δ < NM and δ > 0
      have h1 : 1 / (δ : ℝ) < NM := hNM
      have : 1 / (δ : ℝ) * (δ : ℝ) = 1 := by field_simp
      nlinarith
    exact_mod_cast hlt_real
  -- Apply fractionGraph_rightContinuous_uniform
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hspec := hδ c d hc_pos hd_pos h2d_le_c hab_le_cd_ℚ hcd_sub_2_ℚ
  -- hspec : asympSpecDistance (FractionGraph' c d) (FractionGraph' 2 1) < ε / 2
  -- Now find N such that for n ≥ N, rs n < c/d
  rw [Metric.tendsto_atTop] at hrconv
  obtain ⟨N, hN⟩ := hrconv ((c : ℝ) / d - 2) (by linarith)
  refine ⟨N, fun n hn ψ => ?_⟩
  have hdn := hN n hn; rw [Real.dist_eq] at hdn
  have hrs_lt : rs n < (c : ℝ) / d := by linarith [abs_lt.mp hdn]
  -- ψ(E_{rs n}^o) and ψ(E_2^o) - bound both above and below
  -- ψ(E_2^o) = 2
  have hψ_2 : ψ.eval (circleGraphOpenInf 2 (by norm_num : (2 : ℝ) ≤ 2)) = 2 :=
    spectralPointInf_open_two_eq_two ψ
  -- Lower bound: ψ(E_{rs n}^o) ≥ 2 = ψ(E_2^o)
  -- Direct cohom edgeless 2 → circleGraphOpen (rs n):
  --   edgeless 2 → E_2^o (via edgeless_two_cohom_to_circleGraphOpen_two)
  --   E_2^o → E_{rs n}^o: if rs n = 2, identity; if rs n > 2, via circleGraph_mono
  have hlo : 2 ≤ ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) := by
    calc (2 : ℝ) = ψ.eval (InfiniteGraph.edgeless 2) := by rw [ψ.normalized 2]; simp
      _ ≤ ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) := by
          apply ψ.mono_cohom
          by_cases h_gt : 2 < rs n
          · -- rs n > 2: edgeless 2 → E_2^o → E_{rs n}^c → E_{rs n}^o
            refine Cohom.trans edgeless_two_cohom_to_circleGraphOpen_two ?_
            exact Cohom.trans (circleGraph_mono 2 (rs n) (by norm_num) (h_rs n) h_gt).2.1
              (circleGraphClosed_le_open (rs n) (h_rs n))
          · push_neg at h_gt
            have h_eq : rs n = 2 := le_antisymm h_gt (h_rs n)
            -- rs n = 2: use edgeless_two_cohom_to_circleGraphOpen_two after rewriting
            change Cohom (InfiniteGraph.edgeless 2).graph
              (circleGraphOpen (rs n) (h_rs n))
            have hreplace : circleGraphOpen (rs n) (h_rs n) =
                circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2) := by
              -- h_eq : rs n = 2. Use it to rewrite.
              have : ∀ (x : ℝ) (hx : 2 ≤ x), x = 2 →
                  circleGraphOpen x hx = circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2) := by
                intro x hx hxeq; subst hxeq; rfl
              exact this (rs n) (h_rs n) h_eq
            rw [hreplace]
            exact edgeless_two_cohom_to_circleGraphOpen_two
  -- Upper bound: ψ(E_{rs n}^o) ≤ ψ(fractionGraph c d)
  have hhi : ψ.eval (circleGraphOpenInf (rs n) (h_rs n)) ≤
      ψ.eval (graphToInfiniteGraph (FractionGraph' c d)) :=
    spectralPointInf_open_le_fraction (rs n) (h_rs n) ψ c d hd_pos h2d_le_c hrs_lt
  -- ψ(fractionGraph c d) ≤ ψ(fractionGraph 2 1) + ε/2 = 2 + ε/2
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hψ_fg_21 : ψ.eval (graphToInfiniteGraph (FractionGraph' 2 1)) = 2 :=
    spectralPointInf_fractionGraph_one_eq ψ 2
  set φ := restrictionMap ψ
  have hfg_dist : |φ.eval (FractionGraph' c d) - φ.eval (FractionGraph' 2 1)| ≤
      asympSpecDistance (FractionGraph' c d) (FractionGraph' 2 1) :=
    spectralPoint_dist_le _ _ φ
  have hfg_lt : φ.eval (FractionGraph' c d) - φ.eval (FractionGraph' 2 1) < ε / 2 := by
    have habs_lt : |φ.eval (FractionGraph' c d) - φ.eval (FractionGraph' 2 1)| < ε / 2 :=
      lt_of_le_of_lt hfg_dist hspec
    have := abs_lt.mp habs_lt
    linarith
  have hψ_fg_cd_le : ψ.eval (graphToInfiniteGraph (FractionGraph' c d)) ≤ 2 + ε / 2 := by
    have h1 : φ.eval (FractionGraph' c d) = ψ.eval (graphToInfiniteGraph (FractionGraph' c d)) :=
      rfl
    have h2 : φ.eval (FractionGraph' 2 1) = ψ.eval (graphToInfiniteGraph (FractionGraph' 2 1)) :=
      rfl
    rw [h2, hψ_fg_21] at hfg_lt
    linarith [h1 ▸ hfg_lt]
  -- Now combine
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · -- ψ(E_{rs n}^o) - ψ(E_2^o) > -ε, i.e., ψ(E_2^o) - ψ(E_{rs n}^o) < ε
    rw [hψ_2]; linarith
  · -- ψ(E_{rs n}^o) - ψ(E_2^o) < ε
    rw [hψ_2]; linarith

/-- R1a: Under the hypothesis of Theorem 4.12 (i) for rational r > 2, the open circle graphs
    are closed under limits. For any sequence r_n → r (r_n, r ≥ 2), the open circle graphs
    `E_{r_n}^o` converge to `E_r^o` in the infinite graph asymptotic spectrum distance. -/
theorem circleGraphOpen_closed_under_limits
    (hhyp : ∀ (p q : ℕ+) (h2q : 2 * q < p),
      have hr : 2 ≤ (p : ℝ) / q := by
        rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q
      AsympCohomEquivInf (circleGraphClosedInf ((p : ℝ) / q) hr)
                    (circleGraphOpenInf  ((p : ℝ) / q) hr))
    (rs : ℕ → ℝ) (h_rs : ∀ n, 2 ≤ rs n)
    (r : ℝ) (hr : 2 ≤ r) (hrconv : Filter.Tendsto rs Filter.atTop (nhds r)) :
    ConvergesToInf (fun n => circleGraphOpenInf (rs n) (h_rs n))
                   (circleGraphOpenInf r hr) := by
  by_cases hirr : Irrational r
  · exact circleGraphOpen_closed_under_limits_irrational rs h_rs r hr hirr hrconv
  · by_cases h_eq_2 : r = 2
    · subst h_eq_2
      exact circleGraphOpen_closed_under_limits_rational_eq_two rs h_rs hrconv
    · have hr_gt : 2 < r := lt_of_le_of_ne hr (Ne.symm h_eq_2)
      exact circleGraphOpen_closed_under_limits_rational_gt_two hhyp rs h_rs r hr hrconv
        hirr hr_gt

/-- R2 (⊇ direction): sequential closure of fractionGraphSet contains openCircleGraphSet. -/
def seqClosure (S : Set InfiniteGraphClass) : Set InfiniteGraphClass :=
  { c | ∃ (G : ℕ → InfiniteGraph) (H : InfiniteGraph),
          (∀ n, InfiniteGraphClass.mk (G n) ∈ S) ∧
          ConvergesToInf G H ∧ c = InfiniteGraphClass.mk H }

/-- The set of fraction graph classes as infinite graphs. -/
def fractionGraphSet : Set InfiniteGraphClass :=
  { c | ∃ (p q : ℕ) (_ : NeZero p), 0 < q ∧ 2 * q ≤ p ∧
        c = InfiniteGraphClass.mk (graphToInfiniteGraph (FractionGraph' p q)) }

/-- The set of open circle graph classes. -/
def openCircleGraphSet : Set InfiniteGraphClass :=
  { c | ∃ (r : ℝ) (hr : 2 ≤ r),
        c = InfiniteGraphClass.mk (circleGraphOpenInf r hr) }

/-- R2 (⊇ direction): every open circle graph class lies in the sequential closure of
    the fraction graph classes. This direction does NOT require the hypothesis and
    follows directly from R1b. -/
theorem openCircleGraphSet_subset_seqClosure_fractionGraphSet :
    openCircleGraphSet ⊆ seqClosure fractionGraphSet := by
  intro c hc
  obtain ⟨r, hr, hceq⟩ := hc
  obtain ⟨ps, qs, hNe, hqs_pos, h2qs, htend, hconv⟩ :=
    circleGraphOpen_is_limit_of_fractionGraphs r hr
  refine ⟨fun n => graphToInfiniteGraph (FractionGraph' (ps n) (qs n)),
    circleGraphOpenInf r hr, ?_, hconv, hceq⟩
  intro n
  refine ⟨ps n, qs n, hNe n, hqs_pos n, h2qs n, rfl⟩

/-- Every `SpectralPointInf` has bounded evaluation on any single `InfiniteGraph`.
    This uses the finite clique cover to get `ψ.eval G ≤ n`. -/
theorem spectralPointInf_eval_bdd (ψ : SpectralPointInf) (G : InfiniteGraph) :
    ∃ M : ℝ, ψ.eval G ≤ M := by
  obtain ⟨n, f, hf⟩ := G.cliqueCover_finite
  -- IsCliqueCover G.graph f ↔ IsCohom G.graph ⊥ f (with codomain Fin n)
  have hcohom : Cohom G.graph (InfiniteGraph.edgeless n).graph := by
    refine ⟨f, ?_⟩
    intro u v huv hnadj
    have := hf u v
    refine ⟨fun heq => huv ?_, ?_⟩
    · rcases this heq with h | h
      · exact h
      · exact absurd h hnadj
    · simp [InfiniteGraph.edgeless]
  exact ⟨n, by
    calc ψ.eval G ≤ ψ.eval (InfiniteGraph.edgeless n) := ψ.mono_cohom _ _ hcohom
      _ = n := ψ.normalized n⟩

/-- The set `{|ψ.eval G - ψ.eval H| : ψ}` is bounded above. -/
theorem spectralDistanceSetInf_bddAbove (G H : InfiniteGraph) :
    BddAbove {x | ∃ ψ : SpectralPointInf, x = |ψ.eval G - ψ.eval H|} := by
  -- |ψ(G) - ψ(H)| ≤ ψ(G) + ψ(H) ≤ M_G + M_H
  -- For a uniform M, use the cliqueCover bounds for G and H respectively.
  obtain ⟨nG, fG, hfG⟩ := G.cliqueCover_finite
  obtain ⟨nH, fH, hfH⟩ := H.cliqueCover_finite
  have hcohomG : Cohom G.graph (InfiniteGraph.edgeless nG).graph := by
    refine ⟨fG, ?_⟩
    intro u v huv hnadj
    have := hfG u v
    refine ⟨fun heq => huv ?_, ?_⟩
    · rcases this heq with h | h
      · exact h
      · exact absurd h hnadj
    · simp [InfiniteGraph.edgeless]
  have hcohomH : Cohom H.graph (InfiniteGraph.edgeless nH).graph := by
    refine ⟨fH, ?_⟩
    intro u v huv hnadj
    have := hfH u v
    refine ⟨fun heq => huv ?_, ?_⟩
    · rcases this heq with h | h
      · exact h
      · exact absurd h hnadj
    · simp [InfiniteGraph.edgeless]
  refine ⟨(nG : ℝ) + nH, ?_⟩
  rintro x ⟨ψ, rfl⟩
  have hGbnd : ψ.eval G ≤ nG := by
    calc ψ.eval G ≤ ψ.eval (InfiniteGraph.edgeless nG) := ψ.mono_cohom _ _ hcohomG
      _ = nG := ψ.normalized nG
  have hHbnd : ψ.eval H ≤ nH := by
    calc ψ.eval H ≤ ψ.eval (InfiniteGraph.edgeless nH) := ψ.mono_cohom _ _ hcohomH
      _ = nH := ψ.normalized nH
  have hGnn := ψ.nonneg G
  have hHnn := ψ.nonneg H
  calc |ψ.eval G - ψ.eval H| ≤ |ψ.eval G| + |ψ.eval H| := abs_sub _ _
    _ = ψ.eval G + ψ.eval H := by rw [abs_of_nonneg hGnn, abs_of_nonneg hHnn]
    _ ≤ (nG : ℝ) + nH := by linarith

/-- `|ψ.eval G - ψ.eval H| ≤ asympSpecDistanceInf G H`. -/
theorem spectralPointInf_dist_le_asympSpecDistanceInf (G H : InfiniteGraph)
    (ψ : SpectralPointInf) :
    |ψ.eval G - ψ.eval H| ≤ asympSpecDistanceInf G H := by
  unfold asympSpecDistanceInf
  exact le_csSup (spectralDistanceSetInf_bddAbove G H) ⟨ψ, rfl⟩

/-- Weakened open circle graph set: classes `c` for which some representative agrees
    on every `SpectralPointInf` with an open circle graph `E_r^o`. Since
    `InfiniteGraphClass` is the quotient by *isomorphism*, the strict inclusion
    `seqClosure fractionGraphSet ⊆ openCircleGraphSet` does not follow from the
    sandwich proof (limits are determined only up to ψ-value agreement, not up to
    isomorphism). We therefore work with this spectral-equality weakening, which is
    the right notion for spectral evaluation. -/
def openCircleGraphSet_specEq : Set InfiniteGraphClass :=
  { c | ∃ (H : InfiniteGraph) (r : ℝ) (hr : 2 ≤ r),
        c = InfiniteGraphClass.mk H ∧
        ∀ ψ : SpectralPointInf, ψ.eval H = ψ.eval (circleGraphOpenInf r hr) }

/-- `openCircleGraphSet ⊆ openCircleGraphSet_specEq` trivially
    (take H = circleGraphOpenInf r hr). -/
theorem openCircleGraphSet_subset_specEq :
    openCircleGraphSet ⊆ openCircleGraphSet_specEq := by
  intro c ⟨r, hr, hceq⟩
  exact ⟨circleGraphOpenInf r hr, r, hr, hceq, fun _ => rfl⟩

/-- R2 (⊆ direction, spectral-equality level): every class in the sequential closure of
    `fractionGraphSet` spectrally agrees with some open circle graph `E_r^o` (r ≥ 2).
    Proof sketch: extract p_n, q_n from the fraction graph classes, define
    `r_n := p_n / q_n`. Show `r_n → r := ψ_chi(H)`, a spectral-invariant limit.
    Apply `circleGraphOpen_closed_under_limits` (under `hhyp`) to get
    `ConvergesToInf (E_{r_n}^o) (E_r^o)`. The fraction graphs and open circle graphs
    agree on ψ-values (Lemma 4.4), and `ConvergesToInf` respects this, so the ψ-value
    of the limit H equals the ψ-value of `E_r^o` for every ψ. -/
theorem seqClosure_fractionGraphSet_subset_openCircleGraphSet_specEq
    (hhyp : ∀ (p q : ℕ+) (h2q : 2 * q < p),
      have hr : 2 ≤ (p : ℝ) / q := by
        rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q
      AsympCohomEquivInf (circleGraphClosedInf ((p : ℝ) / q) hr)
                    (circleGraphOpenInf  ((p : ℝ) / q) hr)) :
    seqClosure fractionGraphSet ⊆ openCircleGraphSet_specEq := by
  classical
  intro c ⟨G, H, hG_mem, hconv, hceq⟩
  -- Extract p_n, q_n via Classical.choose
  choose ps qs hNe hqs_pos h2qs hG_eq using hG_mem
  -- ψ-value of G_n equals ψ-value of the canonical fraction graph
  have hψ_G_eq : ∀ (ψ : SpectralPointInf) (n : ℕ),
      ψ.eval (G n) = ψ.eval (graphToInfiniteGraph (@FractionGraph' (ps n) (qs n) (hNe n))) := by
    intro ψ n
    exact ψ.eval_congr (Quotient.exact (hG_eq n))
  -- For every ψ, ψ(G n) → ψ(H) (from ConvergesToInf)
  have hψ_tend : ∀ (ψ : SpectralPointInf),
      Filter.Tendsto (fun n => ψ.eval (G n)) Filter.atTop (nhds (ψ.eval H)) := by
    intro ψ
    rw [Metric.tendsto_atTop]
    intro ε hε
    unfold ConvergesToInf at hconv
    rw [Metric.tendsto_atTop] at hconv
    obtain ⟨N, hN⟩ := hconv ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero] at hdist
    have hnn : 0 ≤ asympSpecDistanceInf (G n) H := by
      unfold asympSpecDistanceInf
      apply Real.sSup_nonneg; rintro x ⟨ψ', rfl⟩; exact abs_nonneg _
    rw [abs_of_nonneg hnn] at hdist
    have hbound : |ψ.eval (G n) - ψ.eval H| ≤ asympSpecDistanceInf (G n) H :=
      spectralPointInf_dist_le_asympSpecDistanceInf _ _ ψ
    linarith
  -- Use chibar_spectralPoint extension to recover p_n/q_n as ψ_chi(G n)
  obtain ⟨ψ_chi, hψ_chi⟩ := restriction_surjective chibar_spectralPoint
  have hψ_chi_G : ∀ n, ψ_chi.eval (G n) = (ps n : ℝ) / qs n := by
    intro n
    haveI : NeZero (ps n) := hNe n
    rw [hψ_G_eq ψ_chi n, hψ_chi (FractionGraph' (ps n) (qs n))]
    exact chibar_spectralPoint_fractionGraph (ps n) (qs n) (hqs_pos n) (h2qs n)
  -- Thus (ps n / qs n) → ψ_chi(H)
  set r : ℝ := ψ_chi.eval H with hr_def
  have htend_r : Filter.Tendsto (fun n => (ps n : ℝ) / qs n) Filter.atTop (nhds r) := by
    apply Filter.Tendsto.congr hψ_chi_G (hψ_tend ψ_chi)
  -- r ≥ 2: since ps n / qs n ≥ 2 for all n
  have h_rn_ge_2 : ∀ n, 2 ≤ (ps n : ℝ) / qs n := by
    intro n
    have hqs_real_pos : (0 : ℝ) < qs n := Nat.cast_pos.mpr (hqs_pos n)
    rw [le_div_iff₀ hqs_real_pos]
    have : (2 * qs n : ℕ) ≤ ps n := h2qs n
    have : ((2 * qs n : ℕ) : ℝ) ≤ (ps n : ℝ) := by exact_mod_cast this
    simpa [mul_comm] using this
  have hr_ge_2 : 2 ≤ r := by
    apply ge_of_tendsto' htend_r
    exact h_rn_ge_2
  -- Define the sequence of open circle graphs
  -- By R1a, E_{p_n/q_n}^o → E_r^o
  have hconv_circle : ConvergesToInf
      (fun n => circleGraphOpenInf ((ps n : ℝ) / qs n) (h_rn_ge_2 n))
      (circleGraphOpenInf r hr_ge_2) :=
    circleGraphOpen_closed_under_limits hhyp
      (fun n => (ps n : ℝ) / qs n) h_rn_ge_2 r hr_ge_2 htend_r
  -- For every ψ, ψ(E_{p_n/q_n}^o) → ψ(E_r^o)
  have hψ_circle_tend : ∀ (ψ : SpectralPointInf),
      Filter.Tendsto (fun n => ψ.eval (circleGraphOpenInf ((ps n : ℝ) / qs n) (h_rn_ge_2 n)))
        Filter.atTop (nhds (ψ.eval (circleGraphOpenInf r hr_ge_2))) := by
    intro ψ
    rw [Metric.tendsto_atTop]
    intro ε hε
    unfold ConvergesToInf at hconv_circle
    rw [Metric.tendsto_atTop] at hconv_circle
    obtain ⟨N, hN⟩ := hconv_circle ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero] at hdist
    have hnn : 0 ≤ asympSpecDistanceInf (circleGraphOpenInf ((ps n : ℝ) / qs n) (h_rn_ge_2 n))
        (circleGraphOpenInf r hr_ge_2) := by
      unfold asympSpecDistanceInf
      apply Real.sSup_nonneg; rintro x ⟨ψ', rfl⟩; exact abs_nonneg _
    rw [abs_of_nonneg hnn] at hdist
    have hbound : |ψ.eval (circleGraphOpenInf ((ps n : ℝ) / qs n) (h_rn_ge_2 n))
          - ψ.eval (circleGraphOpenInf r hr_ge_2)| ≤
        asympSpecDistanceInf (circleGraphOpenInf ((ps n : ℝ) / qs n) (h_rn_ge_2 n))
          (circleGraphOpenInf r hr_ge_2) :=
      spectralPointInf_dist_le_asympSpecDistanceInf _ _ ψ
    linarith
  -- Now: ψ(G n) = ψ(E_{p_n/q_n}^o) for every ψ, via Lemma 4.4 (spectralPointInf_open_eq_fraction)
  have hψ_G_circle_eq : ∀ (ψ : SpectralPointInf) (n : ℕ),
      ψ.eval (G n) = ψ.eval (circleGraphOpenInf ((ps n : ℝ) / qs n) (h_rn_ge_2 n)) := by
    intro ψ n
    haveI : NeZero (ps n) := hNe n
    rw [hψ_G_eq ψ n]
    exact (spectralPointInf_open_eq_fraction (ps n) (qs n) (hqs_pos n) (h2qs n) ψ).symm
  -- Combine: ψ(G n) → ψ(H) and ψ(G n) = ψ(E_{p_n/q_n}^o) → ψ(E_r^o)
  -- By uniqueness of limits, ψ(H) = ψ(E_r^o)
  have hψ_H_eq : ∀ (ψ : SpectralPointInf), ψ.eval H = ψ.eval (circleGraphOpenInf r hr_ge_2) := by
    intro ψ
    have h1 := hψ_tend ψ
    have h2 := hψ_circle_tend ψ
    -- Both sequences agree pointwise
    have hcongr : ∀ n, ψ.eval (G n) =
        ψ.eval (circleGraphOpenInf ((ps n : ℝ) / qs n) (h_rn_ge_2 n)) := hψ_G_circle_eq ψ
    have h1' := Filter.Tendsto.congr hcongr h1
    -- h1' : Tendsto (fun n => ψ(E_{p_n/q_n}^o)) atTop (nhds (ψ.eval H))
    -- h2  : Tendsto (fun n => ψ(E_{p_n/q_n}^o)) atTop (nhds (ψ(E_r^o)))
    exact tendsto_nhds_unique h1' h2
  exact ⟨H, r, hr_ge_2, hceq, hψ_H_eq⟩

/-- R2 (⊇ direction, spectral-equality level): every class in
    `openCircleGraphSet_specEq` lies in `seqClosure fractionGraphSet`.
    This does not require the hypothesis: given `c = mk H` with `ψ(H) = ψ(E_r^o)`
    for all ψ, the same fraction-graph sequence converging to `E_r^o` also converges
    to H. -/
theorem openCircleGraphSet_specEq_subset_seqClosure_fractionGraphSet :
    openCircleGraphSet_specEq ⊆ seqClosure fractionGraphSet := by
  intro c ⟨H, r, hr, hceq, hψ_eq⟩
  -- Get the fraction-graph sequence converging to E_r^o (R1b)
  obtain ⟨ps, qs, hNe, hqs_pos, h2qs, _htend, hconv⟩ :=
    circleGraphOpen_is_limit_of_fractionGraphs r hr
  -- Since ψ(H) = ψ(E_r^o) for all ψ, asympSpecDistanceInf G_n H = asympSpecDistanceInf G_n E_r^o
  refine ⟨fun n => graphToInfiniteGraph (FractionGraph' (ps n) (qs n)),
    H, ?_, ?_, hceq⟩
  · intro n; exact ⟨ps n, qs n, hNe n, hqs_pos n, h2qs n, rfl⟩
  · -- ConvergesToInf (G n) H from ConvergesToInf (G n) E_r^o and spectral equality
    have heq_dist : ∀ n,
        asympSpecDistanceInf (graphToInfiniteGraph (FractionGraph' (ps n) (qs n))) H =
        asympSpecDistanceInf (graphToInfiniteGraph (FractionGraph' (ps n) (qs n)))
          (circleGraphOpenInf r hr) := by
      intro n
      unfold asympSpecDistanceInf
      congr 1
      ext x
      constructor
      · rintro ⟨ψ, rfl⟩; exact ⟨ψ, by rw [hψ_eq ψ]⟩
      · rintro ⟨ψ, rfl⟩; exact ⟨ψ, by rw [← hψ_eq ψ]⟩
    unfold ConvergesToInf
    apply Filter.Tendsto.congr (fun n => (heq_dist n).symm)
    exact hconv

/-- R2 (equality, spectral-equality level): `seqClosure fractionGraphSet` equals
    `openCircleGraphSet_specEq` under the hypothesis of Theorem 4.12 (i) for all
    rational r > 2. -/
theorem openCircleGraphSet_specEq_eq_seqClosure_fractionGraphSet
    (hhyp : ∀ (p q : ℕ+) (h2q : 2 * q < p),
      have hr : 2 ≤ (p : ℝ) / q := by
        rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q
      AsympCohomEquivInf (circleGraphClosedInf ((p : ℝ) / q) hr)
                    (circleGraphOpenInf  ((p : ℝ) / q) hr)) :
    openCircleGraphSet_specEq = seqClosure fractionGraphSet :=
  le_antisymm openCircleGraphSet_specEq_subset_seqClosure_fractionGraphSet
    (seqClosure_fractionGraphSet_subset_openCircleGraphSet_specEq hhyp)

/-- Theorem 4.12 with the rational `r = p/q` packaged as a real number `r`.
    Wrapper around `theorem_4_12_tfae` that takes an explicit `r : ℝ` plus the
    equation `r = p/q`. -/
theorem theorem_4_12_tfae_with_r (r : ℝ) (hr : 2 < r) (p q : ℕ+)
    (hr_eq : r = (p : ℝ) / q) :
    List.TFAE [
      AsympCohomEquivInf (circleGraphClosedInf r (le_of_lt hr))
        (circleGraphOpenInf r (le_of_lt hr)),
      ∃ f : ℕ → ℕ, IsLittleO f ∧ ∀ n, n ≥ 1 →
        ∃ (a b : ℕ+), 2 * b ≤ a ∧
          (a : ℝ) / b < r ∧
          Cohom (strongPower (fractionGraph p q) n)
            (strongPower (fractionGraph a b) (n + f n)),
      ∀ ε > 0, ∃ δ > 0, ∀ (a b : ℕ+),
        2 * b ≤ a →
        0 < r - (a : ℝ) / b →
        r - (a : ℝ) / b < δ →
        ∀ φ : SpectralPoint,
          φ (FractionGraph p q) - φ (FractionGraph a b) < ε,
      ∀ (as bs : ℕ → ℕ+),
        (∀ n, 2 * bs n ≤ as n) →
        Filter.Tendsto (fun n => (as n : ℝ) / bs n) Filter.atTop (nhds r) →
        (∀ n, (as n : ℝ) / bs n < r) →
        ConvergesTo (fun n => FractionGraph (as n) (bs n)) (FractionGraph p q),
      ∀ φ : SpectralPoint,
        sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧
          (a : ℝ) / b < r ∧
          x = φ (FractionGraph a b)} =
        φ (FractionGraph p q) ] := by
  have h2q : 2 * q < p := by
    have : (2 : ℝ) * q < p := by
      rw [hr_eq] at hr; rwa [lt_div_iff₀ (Nat.cast_pos.mpr q.pos)] at hr
    exact_mod_cast this
  subst hr_eq; exact theorem_4_12_tfae p q h2q

/-- Proof of `main_converges_to_circleGraph`: Theorem 4.11(b).
    Adapter from the `ℕ+` paper-statement form to the underlying `ℕ`
    helper `fractionGraph_convergesToInf_circleGraph`. -/
theorem converges_to_circleGraph (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ps : ℕ → ℕ+) (qs : ℕ → ℕ+)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hconv : Filter.Tendsto (fun n => (ps n : ℝ) / qs n) Filter.atTop
      (nhds r)) :
    ConvergesToInf
      (fun n => graphToInfiniteGraph (FractionGraph (ps n) (qs n)))
      (circleGraphOpenInf r hr) := by
  haveI : ∀ n, NeZero (ps n).val := fun _ => ⟨(ps _).pos.ne'⟩
  exact fractionGraph_convergesToInf_circleGraph r hr hirr
    (fun n => (ps n).val) (fun n => (qs n).val)
    (fun n => (qs n).pos) (fun n => h2qs n) hconv

end AsymptoticSpectrumDistance
