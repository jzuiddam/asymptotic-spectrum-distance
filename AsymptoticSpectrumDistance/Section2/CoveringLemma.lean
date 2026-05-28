/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section2.Basic
import AsymptoticSpectrumDistance.Prerequisites.InducedSubgraphBound
import AsymptoticSpectrumDistance.Prerequisites.FractionalCliqueCoverVertexTransitive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Spectral Bounds for Vertex-Transitive Graphs (Lemma 2.15)

This file contains Lemma 2.15 from the paper: for vertex-transitive graphs,
the spectral value is bounded by the ratio |V|/|S| times the spectral value
of the induced subgraph.

## Main results

* `spectral_vertexTransitive_lower` : F(G[S]) ≤ F(G) for any induced subgraph
* `spectral_vertexTransitive_upper` : F(G) ≤ (|V|/|S|) · F(G[S]) for vertex-transitive G

## Proof outline

The lower bound follows from monotonicity: G[S] ≤_c G implies F(G[S]) ≤ F(G).

For the upper bound, we use the probabilistic covering lemma (Vrana's Lemma 3.1):
  G ≤_c N · G[S]  where N = ⌈(|V|/|S|) ln|V|⌉ + 1

Applied to the m-th tensor power:
  G^⊠m ≤_c N_m · G[S]^⊠m  where N_m = ⌈(|V|^m/|S|^m) · m · ln|V|⌉ + 1

Since spectral functions are multiplicative and monotone:
  F(G)^m ≤ N_m · F(G[S])^m

Taking m-th roots and letting m → ∞:
  F(G) ≤ lim_{m→∞} N_m^{1/m} · F(G[S]) = (|V|/|S|) · F(G[S])

The key observation is that N_m grows polynomially in m (like m · (|V|/|S|)^m),
so N_m^{1/m} → |V|/|S| as m → ∞.

## References

* [de Boer, Buys, Zuiddam] Lemma 2.15 (lem:vertex-transitive-spectrum)
* [Vrana 2019] Lemma 3.1
-/

namespace AsymptoticSpectrumDistance

open AsymptoticSpectrumGraphs SimpleGraph ProbabilisticRefinement

/-! ### Auxiliary lemmas for the asymptotic argument -/

open Filter in
/-- m^(1/m) → 1 for naturals (via tendsto_rpow_div composition). -/
lemma nat_rpow_inv_tendsto :
    Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / (m : ℝ))) Filter.atTop (nhds 1) :=
  tendsto_rpow_div.comp tendsto_natCast_atTop_atTop

open Filter in
/-- c^(1/m) → 1 for c > 0 (via continuity of c^x at x = 0). -/
lemma const_rpow_inv_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℕ => c ^ (1 / (m : ℝ))) atTop (nhds 1) := by
  have h1 : Tendsto (fun m : ℕ => (1 / (m : ℝ))) atTop (nhds 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcont : ContinuousAt (fun y : ℝ => c ^ y) 0 :=
    Real.continuousAt_const_rpow (ne_of_gt hc)
  have h2 : c ^ (0 : ℝ) = 1 := Real.rpow_zero c
  have hcomp := hcont.tendsto.comp h1
  simp only [one_div] at hcomp ⊢
  rwa [h2] at hcomp

open Filter in
/-- (m * c)^(1/m) → 1 for c > 0. -/
lemma mul_const_rpow_inv_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℕ => ((m : ℝ) * c) ^ (1 / (m : ℝ))) atTop (nhds 1) := by
  have h1 := nat_rpow_inv_tendsto
  have h2 := const_rpow_inv_tendsto c hc
  have hmul := h1.mul h2
  simp only [one_mul] at hmul
  convert hmul using 1
  ext m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc' : (0 : ℝ) ≤ c := le_of_lt hc
  rw [Real.mul_rpow hm hc']

open Filter in
/-- For a > 1 and c > 0, (a^m · m · c)^{1/m} → a as m → ∞.

    Proof: Rewrite as a · (m·c)^{1/m}, then use (m·c)^{1/m} → 1. -/
lemma rpow_mul_poly_tendsto (a c : ℝ) (ha : 1 < a) (hc : 0 < c) :
    Tendsto (fun m : ℕ => (a ^ m * m * c) ^ (1 / m : ℝ)) atTop (nhds a) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  -- Rewrite: (a^m * m * c)^(1/m) = (a^m)^(1/m) * (m * c)^(1/m) = a * (m * c)^(1/m)
  have h1 : ∀ m : ℕ, 0 < m →
      (a ^ m * m * c) ^ (1 / m : ℝ) = a * ((m : ℝ) * c) ^ (1 / m : ℝ) := by
    intro m hm
    have ha' : (0 : ℝ) ≤ a := le_of_lt ha0
    have hmc : (0 : ℝ) ≤ (m : ℝ) * c := mul_nonneg (Nat.cast_nonneg m) (le_of_lt hc)
    have ham : (0 : ℝ) ≤ a ^ m := pow_nonneg ha' m
    -- Reassociate: a^m * m * c = a^m * (m * c)
    have hassoc : a ^ m * m * c = a ^ m * ((m : ℝ) * c) := by ring
    rw [hassoc, Real.mul_rpow ham hmc]
    -- Need: (a^m)^(1/m) = a
    have hkey : (a ^ m : ℝ) ^ (1 / (m : ℝ)) = a := by
      rw [← Real.rpow_natCast a m]
      rw [← Real.rpow_mul ha']
      rw [mul_one_div_cancel (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm))]
      exact Real.rpow_one a
    rw [hkey]
  -- Now use tendsto_eventually and the limit lemma
  have h2 := mul_const_rpow_inv_tendsto c hc
  have h3 : Tendsto (fun m : ℕ => a * ((m : ℝ) * c) ^ (1 / m : ℝ)) atTop (nhds (a * 1)) :=
    Tendsto.const_mul a h2
  rw [mul_one] at h3
  apply h3.congr'
  filter_upwards [Filter.Ioi_mem_atTop 0] with m hm
  exact (h1 m hm).symm

open Filter in
/-- For c > 0, K ≥ 0, (m * c + K)^{1/m} → 1 as m → ∞. -/
lemma poly_add_const_rpow_tendsto (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    Tendsto (fun m : ℕ => ((m : ℝ) * c + K) ^ (1 / m : ℝ)) atTop (nhds 1) := by
  have hcK : 0 < c + K := by linarith
  have hc' : (0 : ℝ) ≤ c := le_of_lt hc
  have hlower : Tendsto (fun m : ℕ => ((m : ℝ) * c) ^ (1 / (m : ℝ))) atTop (nhds 1) := by
    have hmul : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / (m : ℝ))) atTop (nhds 1) :=
      tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
    have hconst : Tendsto (fun m : ℕ => c ^ (1 / (m : ℝ))) atTop (nhds 1) :=
      const_rpow_inv_tendsto c hc
    have hprod := hmul.mul hconst; simp only [one_mul] at hprod
    convert hprod using 1; funext m; exact Real.mul_rpow (Nat.cast_nonneg m) hc'
  have hupper : Tendsto (fun m : ℕ => ((m : ℝ) * (c + K)) ^ (1 / (m : ℝ))) atTop (nhds 1) := by
    have hmul : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / (m : ℝ))) atTop (nhds 1) :=
      tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
    have hconst : Tendsto (fun m : ℕ => (c + K) ^ (1 / (m : ℝ))) atTop (nhds 1) :=
      const_rpow_inv_tendsto (c + K) hcK
    have hprod := hmul.mul hconst; simp only [one_mul] at hprod
    convert hprod using 1; funext m; exact Real.mul_rpow (Nat.cast_nonneg m) (le_of_lt hcK)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards with m; apply Real.rpow_le_rpow
    · exact mul_nonneg (Nat.cast_nonneg m) hc'
    · linarith
    · simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  · filter_upwards [Ioi_mem_atTop 0] with m hm; apply Real.rpow_le_rpow
    · exact add_nonneg (mul_nonneg (Nat.cast_nonneg m) hc') hK
    · have hm' : 1 ≤ (m : ℝ) := Nat.one_le_cast.mpr hm
      calc (m : ℝ) * c + K ≤ (m : ℝ) * c + (m : ℝ) * K := by nlinarith
        _ = (m : ℝ) * (c + K) := by ring
    · simp only [one_div, inv_nonneg, Nat.cast_nonneg]

open Filter in
/-- (a^m * m * c + K)^{1/m} → a for a > 1, c > 0, K ≥ 0. -/
lemma rpow_mul_poly_add_const_tendsto (a c K : ℝ) (ha : 1 < a) (hc : 0 < c) (hK : 0 ≤ K) :
    Tendsto (fun m : ℕ => (a ^ m * m * c + K) ^ (1 / m : ℝ)) atTop (nhds a) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hc2 : 0 < c + K := by linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (rpow_mul_poly_tendsto a c ha hc) (rpow_mul_poly_tendsto a (c + K) ha hc2)
  · filter_upwards with m; apply Real.rpow_le_rpow
    · exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt ha0) m) (Nat.cast_nonneg m)) (le_of_lt hc)
    · linarith
    · simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  · filter_upwards [Ioi_mem_atTop 0] with m hm; apply Real.rpow_le_rpow
    · exact add_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt ha0) m) (Nat.cast_nonneg m)) (le_of_lt hc)) hK
    · have h1 : 1 ≤ a ^ m * m := by
        have hp := one_le_pow₀ (le_of_lt ha) (n := m)
        have hm' : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
        nlinarith [pow_nonneg (le_of_lt ha0) m]
      calc a ^ m * m * c + K ≤ a ^ m * m * c + a ^ m * m * K := by nlinarith
        _ = a ^ m * m * (c + K) := by ring
    · simp only [one_div, inv_nonneg, Nat.cast_nonneg]

open Filter in
/-- The covering number N_m for the m-th power grows like (|V|/|S|)^m · m · ln|V|.
    Its m-th root therefore converges to |V|/|S|.

    The proof uses a squeeze argument:
    - Lower: x_m ≤ N_m where x_m = (cardV/cardS)^m · m · ln(cardV)
    - Upper: N_m ≤ x_m + 2 (from ceiling bound)
    Taking m-th roots and using the limit lemmas. -/
lemma covering_number_root_tendsto (cardV cardS : ℕ) (hV : 1 < cardV) (hS : 0 < cardS)
    (hSV : cardS ≤ cardV) :
    Tendsto (fun m : ℕ =>
      (⌈(cardV : ℝ) ^ m / (cardS : ℝ) ^ m * m * Real.log cardV⌉₊ + 1 : ℝ) ^ (1 / m : ℝ))
      atTop (nhds ((cardV : ℝ) / cardS)) := by
  set a := (cardV : ℝ) / cardS with ha_def
  set c := Real.log cardV with hc_def
  have hc : 0 < c := by rw [hc_def]; exact Real.log_pos (Nat.one_lt_cast.mpr hV)
  have ha1 : 1 ≤ a := by
    rw [ha_def]; rw [one_le_div (Nat.cast_pos.mpr hS)]
    exact Nat.cast_le.mpr hSV
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hexp : ∀ m : ℕ, (cardV : ℝ) ^ m / (cardS : ℝ) ^ m = a ^ m := by
    intro m; rw [ha_def, div_pow]
  -- Case split: cardS < cardV (a > 1) vs cardS = cardV (a = 1)
  rcases lt_or_eq_of_le hSV with hlt | heq
  · -- Case a > 1
    have ha : 1 < a := by
      rw [ha_def, one_lt_div (Nat.cast_pos.mpr hS)]
      exact Nat.cast_lt.mpr hlt
    have hlower := rpow_mul_poly_tendsto a c ha hc
    have hupper := rpow_mul_poly_add_const_tendsto a c 2 ha hc (by linarith)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    · filter_upwards with m
      apply Real.rpow_le_rpow
      · exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt ha0) m) (Nat.cast_nonneg m))
          (le_of_lt hc)
      · have h := Nat.le_ceil (a ^ m * m * c); rw [hexp]; linarith
      · simp only [one_div, inv_nonneg, Nat.cast_nonneg]
    · filter_upwards with m; apply Real.rpow_le_rpow
      · simp only [add_nonneg, Nat.cast_nonneg, zero_le_one]
      · have hpos : 0 ≤ a ^ m * m * c := mul_nonneg
          (mul_nonneg (pow_nonneg (le_of_lt ha0) m) (Nat.cast_nonneg m)) (le_of_lt hc)
        have h := Nat.ceil_lt_add_one hpos; rw [hexp]; linarith
      · simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  · -- Case a = 1 (cardS = cardV)
    have ha : a = 1 := by
      rw [ha_def, heq]
      have hV_pos : 0 < cardV := lt_trans Nat.zero_lt_one hV
      exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hV_pos))
    -- When cardS = cardV, the expression simplifies: cardV^m / cardS^m = 1^m = 1
    have hsimp : ∀ m : ℕ, (cardV : ℝ) ^ m / (cardS : ℝ) ^ m * m * c = (m : ℝ) * c := by
      intro m; rw [hexp, ha]; ring
    -- So N_m = ⌈m * c⌉ + 1, and N_m^{1/m} → 1 = cardV/cardS = a
    -- We need to show convergence to a = 1
    conv_rhs => rw [ha]
    have hlower := mul_const_rpow_inv_tendsto c hc
    have hupper := poly_add_const_rpow_tendsto c 2 hc (by linarith)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    · filter_upwards with m
      rw [hsimp]
      apply Real.rpow_le_rpow
      · exact mul_nonneg (Nat.cast_nonneg m) (le_of_lt hc)
      · have h := Nat.le_ceil ((m : ℝ) * c); linarith
      · simp only [one_div, inv_nonneg, Nat.cast_nonneg]
    · filter_upwards with m
      rw [hsimp]
      apply Real.rpow_le_rpow
      · simp only [add_nonneg, Nat.cast_nonneg, zero_le_one]
      · have hpos : 0 ≤ (m : ℝ) * c := mul_nonneg (Nat.cast_nonneg m) (le_of_lt hc)
        have h := Nat.ceil_lt_add_one hpos; linarith
      · simp only [one_div, inv_nonneg, Nat.cast_nonneg]

/-! ### Lower bound: F(G[S]) ≤ F(G) -/

/-- Wrap a SimpleGraph V with Fintype and DecidableEq into a Graph.
    Note: Uses ULift to work around universe constraints in SpectralPoint. -/
def simpleGraphToGraph (G : SimpleGraph V) [Fintype V] [DecidableEq V] : Graph where
  V := V
  graph := G

/-- The induced subgraph as a bundled Graph. -/
def inducedGraph (G : SimpleGraph V) (S : Set V)
    [Fintype V] [DecidableEq V] [Fintype S] : Graph where
  V := S
  graph := G.induce S

-- `cohomLE_to_cohom` is now defined once at root scope in
-- `Prerequisites/Cohomomorphism.lean`; callers should reference it unqualified
-- (it's accessible here via the import chain through `Section2.Basic`).

/-- Cohom for induced subgraphs: G.induce S ≤_G G. -/
theorem induced_cohom {V : Type*} (G : SimpleGraph V) (S : Set V) :
    Cohom (G.induce S) G := by
  refine ⟨Subtype.val, fun u v huv hnadj => ?_⟩
  constructor
  · intro heq
    exact huv (Subtype.ext heq)
  · simp only [SimpleGraph.induce_adj] at hnadj
    exact hnadj

/-- For any graph G and subset S, F(G[S]) ≤ F(G).
    This follows from monotonicity since G[S] ≤_c G (induced subgraph cohomomorphism). -/
theorem spectral_vertexTransitive_lower (G : Graph) (S : Set G.V) [Fintype S]
    (_hS : S.Nonempty) (φ : SpectralPoint) :
    φ.eval (inducedGraph G.graph S) ≤ φ.eval G := by
  apply φ.mono_cohom
  exact induced_cohom G.graph S

/-! ### Upper bound: F(G) ≤ (|V|/|S|) · F(G[S]) -/

/-- The N_m for the m-th tensor power of G.
    N_m = ⌈(|V|^m/|S|^m) · m · ln|V|⌉ + 1 -/
noncomputable def coveringNumber_power (cardV cardS : ℕ) (m : ℕ) : ℕ :=
  ⌈(cardV : ℝ) ^ m / (cardS : ℝ) ^ m * m * Real.log cardV⌉₊ + 1


/-- Coordinatewise application of automorphisms gives an automorphism of strong power. -/
def strongPower_piAut {V : Type*} [DecidableEq V] {G : SimpleGraph V} (n : ℕ)
    (φs : Fin n → (G ≃g G)) :
    strongPower G n ≃g strongPower G n where
  toEquiv := Equiv.piCongrRight (fun i => (φs i).toEquiv)
  map_rel_iff' := by
    intro x y
    simp only [strongPower, Equiv.piCongrRight_apply]
    constructor
    · intro ⟨hne, h⟩
      refine ⟨?_, fun i => ?_⟩
      · intro heq; exact hne (by simp only [heq])
      · cases h i with
        | inl heq => left; exact (φs i).toEquiv.injective heq
        | inr hadj => right; exact (φs i).map_rel_iff'.mp hadj
    · intro ⟨hne, h⟩
      refine ⟨?_, fun i => ?_⟩
      · intro heq
        apply hne
        have : ∀ i, (φs i).toEquiv (x i) = (φs i).toEquiv (y i) := congr_fun heq
        funext i
        exact (φs i).toEquiv.injective (this i)
      · cases h i with
        | inl heq => left; exact congr_arg (φs i).toEquiv heq
        | inr hadj => right; exact (φs i).map_rel_iff'.mpr hadj

/-- Tensor power preserves vertex transitivity.
    If G is vertex-transitive, then G^⊠m is vertex-transitive. -/
theorem strongProduct_vertexTransitive {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hT : IsVertexTransitive G) (m : ℕ) :
    IsVertexTransitive (strongPower G m) := by
  -- Given any two vertices f, g : Fin m → V, we need an automorphism mapping f to g
  intro f g
  -- For each coordinate i, use vertex transitivity to get an automorphism φᵢ with φᵢ(f i) = g i
  have hφ : ∀ i : Fin m, ∃ φ : G ≃g G, φ (f i) = g i := fun i => hT (f i) (g i)
  -- Use choice to get the family of automorphisms
  choose φs hφs using hφ
  -- The product automorphism maps f to g
  use strongPower_piAut m φs
  -- Show that applying φs coordinatewise to f gives g
  funext i
  simp only [strongPower_piAut, RelIso.coe_fn_mk]
  exact hφs i

/-! ### Power Set Infrastructure -/

/-- The m-th power of a set S: all functions Fin m → V that land in S. -/
def powerSet (S : Set V) (m : ℕ) : Set (Fin m → V) :=
  {f | ∀ i, f i ∈ S}

/-- powerSet is nonempty when S is nonempty and m > 0. -/
theorem powerSet_nonempty {S : Set V} (hS : S.Nonempty) (m : ℕ) :
    (powerSet S m).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  exact ⟨fun _ => s, fun _ => hs⟩

/-- Fintype instance for powerSet. -/
noncomputable instance powerSet_fintype [Fintype V] (S : Set V) [Fintype S] (m : ℕ) :
    Fintype (powerSet S m) := by
  classical
  exact Fintype.ofFinite (powerSet S m)

/-- Cardinality of powerSet: |S^m| = |S|^m. -/
theorem powerSet_card [Fintype V] (S : Set V) [Fintype S] (m : ℕ) :
    Fintype.card (powerSet S m) = (Fintype.card S) ^ m := by
  -- powerSet S m ≃ (Fin m → S), so |powerSet S m| = |S|^m
  have heq : powerSet S m ≃ (Fin m → S) := {
    toFun := fun ⟨f, hf⟩ i => ⟨f i, hf i⟩
    invFun := fun g => ⟨fun i => (g i).val, fun i => (g i).prop⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  classical
  simp only [Fintype.card_congr heq, Fintype.card_fun, Fintype.card_fin]

/-- Cardinality of function type Fin m → V is |V|^m. -/
theorem card_fin_arrow [Fintype V] (m : ℕ) : Fintype.card (Fin m → V) = (Fintype.card V) ^ m := by
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- lemma31_N for powerSet S m relates to coveringNumber_power.
    Since lemma31_N uses floor and coveringNumber_power uses ceiling,
    coveringNumber_power ≥ lemma31_N. -/
theorem lemma31_N_le_coveringNumber_power [Fintype V] (S : Set V) [Fintype S] (m : ℕ) :
    lemma31_N (powerSet S m) ≤ coveringNumber_power (Fintype.card V) (Fintype.card S) m := by
  unfold lemma31_N coveringNumber_power
  -- lemma31_N (powerSet S m) = ⌊(|V^m|/|S^m|) * ln|V^m|⌋ + 1
  -- coveringNumber_power = ⌈(|V|^m/|S|^m) * m * ln|V|⌉ + 1
  have h1 : Fintype.card (Fin m → V) = (Fintype.card V) ^ m := card_fin_arrow m
  have h2 : Fintype.card (powerSet S m) = (Fintype.card S) ^ m := powerSet_card S m
  -- The key: |V^m|/|S^m| * ln|V^m| = |V|^m/|S|^m * m * ln|V|
  have hlog : Real.log ((Fintype.card V : ℝ) ^ m) = m * Real.log (Fintype.card V) :=
    Real.log_pow (Fintype.card V) m
  have heq : (Fintype.card (Fin m → V) : ℝ) / (Fintype.card (powerSet S m) : ℝ) *
      Real.log (Fintype.card (Fin m → V)) =
      (Fintype.card V : ℝ) ^ m / (Fintype.card S : ℝ) ^ m * m * Real.log (Fintype.card V) := by
    simp only [h1, h2, Nat.cast_pow, hlog]; ring
  rw [heq]
  exact Nat.add_le_add_right (Nat.floor_le_ceil _) 1

/-- The equivalence between powerSet S m and (Fin m → S). -/
def powerSetEquiv (S : Set V) (m : ℕ) : powerSet S m ≃ (Fin m → S) where
  toFun f := fun i => ⟨f.val i, f.prop i⟩
  invFun g := ⟨fun i => (g i).val, fun i => (g i).prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The induced subgraph on powerSet is isomorphic to the strong power of the induced subgraph.
    (G^⊠m)[S^m] ≃g (G[S])^⊠m

    The proof shows that adjacency in (G^⊠m)[S^m] corresponds exactly to
    adjacency in (G[S])^⊠m via the natural equivalence. -/
theorem strongPower_induce_iso (G : SimpleGraph V) (S : Set V) (m : ℕ) :
    Nonempty ((strongPower G m).induce (powerSet S m) ≃g
              strongPower (G.induce S) m) := by
  -- The isomorphism uses the natural equivalence powerSet S m ≃ (Fin m → S)
  -- Key observation: (powerSetEquiv S m f) i = ⟨f.val i, f.prop i⟩
  -- So ↑((powerSetEquiv S m f) i) = f.val i
  refine ⟨{
    toEquiv := powerSetEquiv S m
    map_rel_iff' := ?_
  }⟩
  intro f g
  -- Both sides use strongPower adjacency and induce_adj simplifies G.induce S
  simp only [strongPower, SimpleGraph.induce_adj]
  -- Key lemmas about powerSetEquiv:
  -- 1. ↑((powerSetEquiv S m h) i) = h.val i (for G.Adj args)
  -- 2. (powerSetEquiv S m f) i = (powerSetEquiv S m g) i ↔ f.val i = g.val i (for eq args)
  have hval : ∀ (h : ↑(powerSet S m)) (i : Fin m), ↑((powerSetEquiv S m h) i) = h.val i :=
    fun _ _ => rfl
  have heq_iff : ∀ i, (powerSetEquiv S m f) i = (powerSetEquiv S m g) i ↔ f.val i = g.val i := by
    intro i
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  simp only [hval]
  constructor
  · intro ⟨hne, hcoord⟩
    refine ⟨?_, fun i => ?_⟩
    · intro heq; apply hne; funext i; exact Subtype.ext (congr_fun heq i)
    · cases hcoord i with
      | inl h => left; exact (heq_iff i).mp h
      | inr h => right; exact h
  · intro ⟨hne, hcoord⟩
    refine ⟨?_, fun i => ?_⟩
    · intro heq; apply hne; funext i; exact congr_arg Subtype.val (congr_fun heq i)
    · cases hcoord i with
      | inl h => left; exact (heq_iff i).mpr h
      | inr h => right; exact h

/-- For vertex-transitive G, the m-th power satisfies G^⊠m ≤_c N_m · G[S]^⊠m.

    Proof: Apply transitive_cohomLE_nfold_full to G^⊠m with subset S^m.
    Then use the isomorphism (G^⊠m)[S^m] ≃g (G[S])^⊠m. -/
theorem vertexTransitive_power_cohomLE {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Set V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive G) (hcard : 0 < Fintype.card S)
    (m : ℕ) (_hm : 0 < m) :
    -- G^⊠m ≤_c N_m · (G[S])^⊠m
    strongPower G m ≤ᶜ
      (coveringNumber_power (Fintype.card V) (Fintype.card S) m ⬝
       strongPower (G.induce S) m) := by
  -- First, apply the covering lemma to strongPower G m with powerSet S m
  have hT' : IsVertexTransitive (strongPower G m) :=
    strongProduct_vertexTransitive G hT m
  have hS' : (powerSet S m).Nonempty := powerSet_nonempty hS m
  have hcard' : 0 < Fintype.card (powerSet S m) := by
    rw [powerSet_card]
    exact Nat.pow_pos hcard
  -- Get the cohomomorphism from Lemma 3.1:
  -- G^⊠m ≤ᶜ lemma31_N (powerSet S m) ⬝ (G^⊠m)[S^m]
  have h := transitive_cohomLE_nfold_full (strongPower G m)
    (powerSet S m) hS' hT' hcard'
  -- Get the isomorphism: (G^⊠m)[S^m] ≃g (G[S])^⊠m
  have h_iso := strongPower_induce_iso G S m
  -- From isomorphism, get (G^⊠m)[S^m] ≤ᶜ (G[S])^⊠m
  obtain ⟨iso⟩ := h_iso
  have h_cohom : (strongPower G m).induce (powerSet S m) ≤ᶜ
      strongPower (G.induce S) m := SimpleGraph.Iso.toCohomLE iso
  -- Use monotonicity to lift to nfold:
  -- lemma31_N ⬝ (G^⊠m)[S^m] ≤ᶜ lemma31_N ⬝ (G[S])^⊠m
  have h_nfold := nFoldDisjointUnion_cohomLE_mono h_cohom
      (n := lemma31_N (powerSet S m))
  -- Transitivity: G^⊠m ≤ᶜ lemma31_N ⬝ (G[S])^⊠m
  have h1 := cohomLE_trans h h_nfold
  -- Use lemma31_N ≤ coveringNumber_power and monotonicity in n
  have hle := lemma31_N_le_coveringNumber_power S m
  have h2 := @_root_.ProbabilisticRefinement.nFoldDisjointUnion_cohomLE_n_mono (Fin m → S)
    (strongPower (G.induce S) m) _ _ hle
  -- Final transitivity
  exact cohomLE_trans h1 h2

/-! ### Spectral Point Infrastructure for Upper Bound -/

/-- The n-fold disjoint union at Graph level: n copies of G.
    This is EdgelessGraph n ⊠ G since n ⬝ G = K̄_n ⊠ G. -/
def nFoldGraph (n : ℕ) (G : Graph) : Graph := EdgelessGraph n ⊠ G

/-- Spectral evaluation of n-fold disjoint union: φ(n ⬝ G) = n * φ(G).
    This follows from multiplicativity: φ(K̄_n ⊠ G) = φ(K̄_n) * φ(G) = n * φ(G). -/
theorem eval_nFoldGraph (φ : SpectralPoint) (n : ℕ) (G : Graph) :
    φ.eval (nFoldGraph n G) = n * φ.eval G := by
  unfold nFoldGraph
  rw [φ.mul_strongProduct]
  rw [φ.normalized n]

/-- The strong power of an induced subgraph at Graph level. -/
def strongPowerInduced (G : SimpleGraph V) (S : Set V) [Fintype V] [DecidableEq V]
    [Fintype S] (m : ℕ) : Graph where
  V := Fin m → S
  graph := strongPower (G.induce S) m

/-- Bridge: Convert SimpleGraph cohomLE to Graph Cohom for spectral monotonicity. -/
theorem simpleGraph_cohomLE_to_graph_eval_le (φ : SpectralPoint)
    {G H : SimpleGraph V} [Fintype V] [DecidableEq V]
    (hcoh : G ≤ᶜ H) : φ.eval (simpleGraphToGraph G) ≤ φ.eval (simpleGraphToGraph H) := by
  apply φ.mono_cohom
  exact cohomLE_to_cohom hcoh

/-- Spectral evaluation of strong power: φ(G^⊠m) = φ(G)^m.
    This follows by induction using multiplicativity: G^⊠(m+1) ≃ G^⊠m ⊠ G.
    The base case G^⊠0 is a single point = E_1 with φ = 1.

    The Graph-level strong product uses a different structure than the iterated
    strong power. We prove spectral equivalence via the isomorphism constructed above. -/
theorem strongPowerGraph_spectral_eq (φ : SpectralPoint) (G : Graph) (m : ℕ) :
    φ.eval (strongPowerGraph G m) = φ.eval (recStrongPowerGraph G m) := by
  exact (Universality.SpectralPoint.eval_iso φ (recStrongPowerGraph_iso G m)).symm

/-- Spectral evaluation of strong power: φ(G^⊠m) = φ(G)^m. -/
theorem eval_strongPowerGraph (φ : SpectralPoint) (G : Graph) (m : ℕ) :
    φ.eval (strongPowerGraph G m) = φ.eval G ^ m := by
  rw [strongPowerGraph_spectral_eq]
  exact eval_recStrongPowerGraph φ G m

/-- The two edgeless graph definitions are equal. -/
theorem edgelessGraph_eq (n : ℕ) :
    AsymptoticSpectrumGraphs.edgelessGraph n = ProbabilisticRefinement.edgelessGraph n := rfl

/-- The Graph-level n-fold construction matches the SimpleGraph-level n-fold. -/
theorem nFoldGraph_graph_eq (n : ℕ) (H : Graph) :
    (nFoldGraph n H).graph = n ⬝ H.graph := by
  simp only [nFoldGraph, Graph.strongProduct, EdgelessGraph, edgelessGraph_eq,
             nFoldDisjointUnion_eq_strongProduct]

/-- strongPowerInduced equals strongPowerGraph applied to inducedGraph. -/
theorem strongPowerInduced_eq (G : SimpleGraph V) (S : Set V) [Fintype V] [DecidableEq V]
    [Fintype S] (m : ℕ) :
    strongPowerInduced G S m = strongPowerGraph (inducedGraph G S) m := rfl

/-- The key lemma: For vertex-transitive G, φ(G)^m ≤ N_m * φ(G[S])^m for each m.

    Proof: Use the cohomLE from vertexTransitive_power_cohomLE, convert to Cohom,
    then use spectral monotonicity. -/
theorem spectral_power_bound (G : Graph) (S : Set G.V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive G.graph) (hcard : 0 < Fintype.card S)
    (φ : SpectralPoint) (m : ℕ) (hm : 0 < m) :
    φ.eval G ^ m ≤
      coveringNumber_power (Fintype.card G.V) (Fintype.card S) m *
      φ.eval (inducedGraph G.graph S) ^ m := by
  -- Use the evaluation theorems to rewrite as spectral evaluations
  rw [← eval_strongPowerGraph, ← eval_strongPowerGraph]
  -- Get the cohomLE from vertexTransitive_power_cohomLE
  have hcohomLE := vertexTransitive_power_cohomLE G.graph S hS hT hcard m hm
  -- Convert to Cohom
  have hcohom := cohomLE_to_cohom hcohomLE
  -- The LHS is strongPowerGraph G m
  -- The RHS is n-fold of strongPowerGraph of inducedGraph
  set N := coveringNumber_power (Fintype.card G.V) (Fintype.card S) m with hN_def
  set H := strongPowerGraph (inducedGraph G.graph S) m with hH_def
  -- Rewrite RHS using eval_nFoldGraph: N * φ(H) = φ(nFoldGraph N H)
  rw [← eval_nFoldGraph]
  -- Now we need: φ.eval (strongPowerGraph G m) ≤ φ.eval (nFoldGraph N H)
  apply φ.mono_cohom
  -- Need to show Cohom between the underlying graphs
  -- hcohom : Cohom (strongPower G.graph m)
  --                   (N ⬝ strongPower (G.graph.induce S) m)
  -- LHS graph: (strongPowerGraph G m).graph = strongPower G.graph m ✓
  -- RHS graph: (nFoldGraph N H).graph = N ⬝ H.graph  (by nFoldGraph_graph_eq)
  --          = N ⬝ strongPower (G.graph.induce S) m ✓
  simp only [strongPowerGraph, nFoldGraph_graph_eq]
  exact hcohom

/-- From the power bound, derive the m-th root inequality:
    φ(G) ≤ N_m^{1/m} · φ(G[S]) for all m > 0.

    This uses the fact that if a^m ≤ b * c^m with a,b,c ≥ 0 and c > 0,
    then a ≤ b^{1/m} * c. -/
lemma spectral_root_bound (G : Graph) (S : Set G.V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive G.graph) (hcard : 0 < Fintype.card S)
    (φ : SpectralPoint) (m : ℕ) (hm : 0 < m)
    (_hH_pos : 0 < φ.eval (inducedGraph G.graph S)) :
    φ.eval G ≤ (coveringNumber_power (Fintype.card G.V) (Fintype.card S) m : ℝ) ^ (1 / m : ℝ) *
               φ.eval (inducedGraph G.graph S) := by
  have hbound := spectral_power_bound G S hS hT hcard φ m hm
  have hG_nonneg : 0 ≤ φ.eval G := φ.nonneg G
  have hH_nonneg : 0 ≤ φ.eval (inducedGraph G.graph S) := φ.nonneg (inducedGraph G.graph S)
  have hN_pos : (0 : ℝ) < coveringNumber_power (Fintype.card G.V) (Fintype.card S) m := by
    unfold coveringNumber_power
    simp only [Nat.cast_add, Nat.cast_one]
    have h := Nat.cast_nonneg (α := ℝ) (⌈(↑(Fintype.card G.V) ^ m / ↑(Fintype.card S) ^ m *
      ↑m * Real.log ↑(Fintype.card G.V))⌉₊)
    linarith
  have hN_nonneg : (0 : ℝ) ≤ coveringNumber_power (Fintype.card G.V) (Fintype.card S) m :=
    le_of_lt hN_pos
  -- From φ(G)^m ≤ N_m * φ(H)^m, take m-th root
  -- Need: (φ(G)^m)^{1/m} ≤ (N_m * φ(H)^m)^{1/m}
  have h1 : φ.eval G ^ m ≤ coveringNumber_power (Fintype.card G.V) (Fintype.card S) m *
            φ.eval (inducedGraph G.graph S) ^ m := hbound
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  -- Take m-th root of both sides
  have h2 : (φ.eval G ^ m) ^ (1 / m : ℝ) ≤
            (coveringNumber_power (Fintype.card G.V) (Fintype.card S) m *
             φ.eval (inducedGraph G.graph S) ^ m) ^ (1 / m : ℝ) := by
    apply Real.rpow_le_rpow (pow_nonneg hG_nonneg m) h1
    simp only [one_div, inv_nonneg]; linarith
  -- Simplify left side: (a^m)^{1/m} = a for a ≥ 0
  have h3 : (φ.eval G ^ m : ℝ) ^ (1 / m : ℝ) = φ.eval G := by
    rw [← Real.rpow_natCast (φ.eval G) m]
    rw [← Real.rpow_mul hG_nonneg]
    simp only [one_div, mul_inv_cancel₀ hm_ne, Real.rpow_one]
  rw [h3] at h2
  -- Simplify right side: (N * H^m)^{1/m} = N^{1/m} * H
  have h4 : (coveringNumber_power (Fintype.card G.V) (Fintype.card S) m *
             φ.eval (inducedGraph G.graph S) ^ m : ℝ) ^ (1 / m : ℝ) =
            (coveringNumber_power (Fintype.card G.V) (Fintype.card S) m : ℝ) ^ (1 / m : ℝ) *
            φ.eval (inducedGraph G.graph S) := by
    rw [Real.mul_rpow hN_nonneg (pow_nonneg hH_nonneg m)]
    congr 1
    rw [← Real.rpow_natCast (φ.eval (inducedGraph G.graph S)) m]
    rw [← Real.rpow_mul hH_nonneg]
    simp only [one_div, mul_inv_cancel₀ hm_ne, Real.rpow_one]
  rw [h4] at h2
  exact h2

/-- Upper bound: For vertex-transitive G with nonempty S,
    F(G) ≤ (|V|/|S|) · F(G[S]).

    This is Lemma 2.15 from the paper (lem:vertex-transitive-spectrum).

    The proof uses the limit argument:
    1. From spectral_power_bound: φ(G)^m ≤ N_m * φ(G[S])^m
    2. Take m-th root: φ(G) ≤ N_m^{1/m} * φ(G[S])
    3. Take limit using covering_number_root_tendsto: N_m^{1/m} → |V|/|S| -/
theorem spectral_vertexTransitive_upper (G : Graph) (S : Set G.V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive G.graph) (hcard : 0 < Fintype.card S)
    (φ : SpectralPoint) :
    φ.eval G ≤ (Fintype.card G.V : ℝ) / (Fintype.card S) * φ.eval (inducedGraph G.graph S) := by
  -- Get cardinalities
  set cardV := Fintype.card G.V with hcardV_def
  set cardS := Fintype.card S with hcardS_def
  have hS_pos : 0 < cardS := hcard
  -- Handle the case where φ(G[S]) = 0 or positive
  by_cases hH_pos : 0 < φ.eval (inducedGraph G.graph S)
  · -- Case: φ(G[S]) > 0, use the limit argument
    -- We need: ∀ ε > 0, φ(G) ≤ (|V|/|S| + ε) * φ(G[S])
    -- Then take ε → 0
    have hH_nonneg : 0 ≤ φ.eval (inducedGraph G.graph S) := le_of_lt hH_pos
    -- Get the limit: N_m^{1/m} → |V|/|S|
    have hV_pos : 0 < cardV := by
      have hS_nonempty : S.Nonempty := hS
      obtain ⟨s, hs⟩ := hS_nonempty
      have : Fintype.card G.V > 0 := Fintype.card_pos_iff.mpr ⟨(s : G.V)⟩
      omega
    have hSV : cardS ≤ cardV := by
      -- S is a subset of V
      have h := Fintype.card_le_of_injective (fun (x : S) => (x : G.V))
        (fun x y h => Subtype.ext h)
      simp only [← hcardV_def, ← hcardS_def] at h
      exact h
    by_cases hV1 : cardV = 1
    · -- If |V| = 1, then |S| = 1 (since S nonempty and S ⊆ V), so |V|/|S| = 1
      -- and G = G[S] (S = V), so φ(G) ≤ 1 * φ(G[S]) = φ(G[S]) holds by equality
      have hS1 : cardS = 1 := by
        have h1 : cardS ≤ 1 := by rw [← hV1]; exact hSV
        have h2 : 1 ≤ cardS := hcard
        omega
      simp only [hV1, hS1, Nat.cast_one, div_one, one_mul]
      -- When |V| = |S| = 1, S must equal V (as sets), so G[S] = G
      -- The lower bound gives φ(G[S]) ≤ φ(G), but we need φ(G) ≤ φ(G[S])
      -- Since both have cardinality 1 and S ⊆ V nonempty, S = V
      -- Thus G.induce S is isomorphic to G, and φ values are equal
      -- Use the power bound argument with m = 1
      have hbound := spectral_power_bound G S hS hT hcard φ 1 Nat.one_pos
      simp only [pow_one] at hbound
      -- N_1 = ⌈(|V|/|S|) * 1 * ln|V|⌉ + 1 = ⌈1 * 1 * 0⌉ + 1 = 1
      have hN1 : coveringNumber_power (Fintype.card G.V) (Fintype.card S) 1 = 1 := by
        unfold coveringNumber_power
        simp_rw [← hcardV_def, ← hcardS_def, hV1, hS1]
        simp only [pow_one, Nat.cast_one, div_one, one_mul, Real.log_one, mul_zero,
                   Nat.ceil_zero, zero_add]
      rw [hN1] at hbound
      simp only [Nat.cast_one, one_mul] at hbound
      exact hbound
    · -- Case: |V| > 1
      have hV_gt1 : 1 < cardV := by omega
      -- Use that N_m^{1/m} → |V|/|S|
      have hlim := covering_number_root_tendsto cardV cardS hV_gt1 hS_pos hSV
      -- The sequence N_m^{1/m} converges to |V|/|S|
      -- For each m, we have φ(G) ≤ N_m^{1/m} * φ(G[S])
      -- Take limit: φ(G) ≤ (|V|/|S|) * φ(G[S])
      have hG_nonneg : 0 ≤ φ.eval G := φ.nonneg G
      -- Use ge_of_tendsto to get the limit inequality
      have hmain : ∀ m : ℕ, 0 < m →
          φ.eval G ≤ (coveringNumber_power cardV cardS m : ℝ) ^ (1 / m : ℝ) *
                     φ.eval (inducedGraph G.graph S) := by
        intro m hm
        exact spectral_root_bound G S hS hT hcard φ m hm hH_pos
      -- The function m ↦ N_m^{1/m} * φ(H) converges to (|V|/|S|) * φ(H)
      have hlim2 : Filter.Tendsto
          (fun m : ℕ => (coveringNumber_power cardV cardS m : ℝ) ^ (1 / m : ℝ) *
                        φ.eval (inducedGraph G.graph S))
          Filter.atTop
          (nhds ((cardV : ℝ) / cardS * φ.eval (inducedGraph G.graph S))) := by
        -- Convert hlim to the right form
        have hlim' : Filter.Tendsto
            (fun m : ℕ => (coveringNumber_power cardV cardS m : ℝ) ^ (1 / m : ℝ))
            Filter.atTop (nhds ((cardV : ℝ) / cardS)) := by
          unfold coveringNumber_power
          -- The issue is (n : ℝ) vs ↑n for natural numbers
          -- (⌈...⌉₊ + 1 : ℝ) = ↑⌈...⌉₊ + 1 as reals
          simp only [Nat.cast_add, Nat.cast_one] at hlim ⊢
          exact hlim
        exact hlim'.mul_const _
      -- Use ge_of_tendsto_of_eventually
      apply ge_of_tendsto hlim2
      filter_upwards [Filter.Ioi_mem_atTop 0] with m hm
      exact hmain m hm
  · -- Case: φ(G[S]) ≤ 0, but by non-negativity φ(G[S]) ≥ 0, so φ(G[S]) = 0
    push_neg at hH_pos
    have hH_eq : φ.eval (inducedGraph G.graph S) = 0 := by
      have h := φ.nonneg (inducedGraph G.graph S)
      linarith
    rw [hH_eq, mul_zero]
    -- From the power bound with m = 1: φ(G)^1 ≤ N_1 * φ(G[S])^1 = N_1 * 0 = 0
    -- Combined with non-negativity φ(G) ≥ 0, we get φ(G) = 0.
    have hG_eq : φ.eval G = 0 := by
      have hbound := spectral_power_bound G S hS hT hcard φ 1 Nat.one_pos
      simp only [pow_one, hH_eq, mul_zero] at hbound
      have h := φ.nonneg G
      linarith
    rw [hG_eq]

/-- Combined bound: For vertex-transitive G with nonempty S,
    F(G[S]) ≤ F(G) ≤ (|V|/|S|) · F(G[S]).

    This is the full Lemma 2.15 from the paper. -/
theorem spectral_vertexTransitive_bounds (G : Graph) (S : Set G.V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive G.graph) (hcard : 0 < Fintype.card S)
    (φ : SpectralPoint) :
    φ.eval (inducedGraph G.graph S) ≤ φ.eval G ∧
    φ.eval G ≤ (Fintype.card G.V : ℝ) / (Fintype.card S) * φ.eval (inducedGraph G.graph S) :=
  ⟨spectral_vertexTransitive_lower G S hS φ, spectral_vertexTransitive_upper G S hS hT hcard φ⟩

/-! ### Distance bound corollary -/

/-- For each spectral point, |φ(G) - φ(G[S])| ≤ (|V|/|S| - 1) · φ(G[S]).

    This follows from the spectral bounds:
    - φ(G[S]) ≤ φ(G) ≤ (|V|/|S|) · φ(G[S])
    - So 0 ≤ φ(G) - φ(G[S]) ≤ ((|V|/|S|) - 1) · φ(G[S]) -/
lemma spectral_distance_bound (G : Graph) (S : Set G.V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive G.graph) (hcard : 0 < Fintype.card S)
    (φ : SpectralPoint) :
    |φ.eval G - φ.eval (inducedGraph G.graph S)| ≤
      ((Fintype.card G.V : ℝ) / (Fintype.card S) - 1) * φ.eval (inducedGraph G.graph S) := by
  set r := (Fintype.card G.V : ℝ) / (Fintype.card S) with hr_def
  set H := inducedGraph G.graph S with hH_def
  have hbounds := spectral_vertexTransitive_bounds G S hS hT hcard φ
  obtain ⟨hlower, hupper⟩ := hbounds
  -- From the bounds: φ(H) ≤ φ(G) ≤ r * φ(H)
  -- So φ(G) - φ(H) ≥ 0 and φ(G) - φ(H) ≤ (r - 1) * φ(H)
  have hdiff_nonneg : 0 ≤ φ.eval G - φ.eval H := by linarith
  have hdiff_upper : φ.eval G - φ.eval H ≤ (r - 1) * φ.eval H := by
    have h1 : φ.eval G ≤ r * φ.eval H := hupper
    have hH_nonneg : 0 ≤ φ.eval H := φ.nonneg H
    calc φ.eval G - φ.eval H ≤ r * φ.eval H - φ.eval H := by linarith
      _ = (r - 1) * φ.eval H := by ring
  -- Since the difference is non-negative, |φ(G) - φ(H)| = φ(G) - φ(H)
  rw [abs_of_nonneg hdiff_nonneg]
  exact hdiff_upper

/-- Corollary: The asymptotic spectrum distance between G and G[S] is bounded.

    From the spectral bounds:
    - F(G[S]) ≤ F(G) ≤ (|V|/|S|) · F(G[S])

    We get: |F(G) - F(G[S])| ≤ ((|V|/|S|) - 1) · F(G[S])

    Taking supremum over all F ∈ X:
    d(G, G[S]) ≤ ((|V|/|S|) - 1) · sup_F F(G[S]) -/
theorem asympSpecDistance_vertexTransitive_bound (G : Graph) (S : Set G.V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive G.graph) (hcard : 0 < Fintype.card S) :
    asympSpecDistance G (inducedGraph G.graph S) ≤
      ((Fintype.card G.V : ℝ) / (Fintype.card S) - 1) *
      sSup {x | ∃ φ : SpectralPoint, x = φ.eval (inducedGraph G.graph S)} := by
  set r := (Fintype.card G.V : ℝ) / (Fintype.card S) with hr_def
  set H := inducedGraph G.graph S with hH_def
  -- Need: r - 1 ≥ 0 since |V| ≥ |S|
  have hr_ge_1 : 1 ≤ r := by
    rw [hr_def, one_le_div (Nat.cast_pos.mpr hcard)]
    apply Nat.cast_le.mpr
    exact Fintype.card_le_of_injective (fun (x : S) => (x : G.V)) (fun x y h => Subtype.ext h)
  have hrm1_nonneg : 0 ≤ r - 1 := by linarith
  -- The set of spectral values is bounded above
  have hbdd := spectralPoint_bdd_above H
  -- Use csSup_le to show the bound
  rw [asympSpecDistance, spectralDistanceSet]
  apply csSup_le
  · -- The set is nonempty
    use |spectralPoint_nonempty.some.eval G - spectralPoint_nonempty.some.eval H|
    exact ⟨spectralPoint_nonempty.some, rfl⟩
  · -- Show each element is bounded
    intro x ⟨φ, hφ⟩
    rw [hφ]
    have hbound := spectral_distance_bound G S hS hT hcard φ
    -- hbound uses inducedGraph G.graph S which equals H
    calc |φ.eval G - φ.eval H|
        ≤ (r - 1) * φ.eval H := hbound
      _ ≤ (r - 1) * sSup {x | ∃ ψ : SpectralPoint, x = ψ.eval H} := by
          apply mul_le_mul_of_nonneg_left _ hrm1_nonneg
          -- φ.eval H ≤ sSup {...}
          apply le_csSup hbdd
          exact ⟨φ, rfl⟩

end AsymptoticSpectrumDistance
