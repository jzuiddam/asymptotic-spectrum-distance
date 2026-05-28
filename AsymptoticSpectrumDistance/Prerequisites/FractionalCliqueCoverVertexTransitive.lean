/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.BigOperators
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.FractionalCliqueCover
import AsymptoticSpectrumDistance.Prerequisites.FractionGraph

/-!
# Fractional Clique Cover Number for Vertex-Transitive Graphs

This file contains the formula χ̄_f(G) = |V|/ω for vertex-transitive graphs G,
specialised to fraction graphs (`chilemma`), together with the small spectral-point /
isomorphism API and the `fractionGraphAsGraph` / `fractionGraphAsFiniteGraph` helpers.

## Main results

* `fractionalCliqueCoverNumber_eq_formula_vertexTransitive` :
    For vertex-transitive G, χ̄_f(G) = |V|/ω.
* `chilemma` : χ̄_f(E_{p/q}) = p/q.
* `SpectralPoint.eval_iso` : spectral points are invariant under graph isomorphism.

## References

* Scheinerman-Ullman (2011), Fractional Graph Theory
* Zuiddam (2019), Asymptotic spectrum of graphs

-/

namespace Universality

open SimpleGraph FractionGraphBasic AsymptoticSpectrumGraphs
open scoped BigOperators

/-! ### Helper definitions for fraction graphs -/

/-- Helper to create a Graph from a fraction graph -/
def fractionGraphAsGraph (p q : ℕ) [NeZero p] : Graph :=
  { V := ZMod p, graph := fractionGraph p q }

/-- Helper to create a FiniteGraph from a fraction graph -/
def fractionGraphAsFiniteGraph (p q : ℕ) [NeZero p] : FiniteGraph :=
  { V := ZMod p, graph := fractionGraph p q }

/-! ### chilemma: χ̄_f(E_{p/q}) = p/q -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For vertex-transitive graphs, every vertex is in some max-clique.
    Proof: Let C be any max-clique (exists since cliqueNum > 0).
    For any vertex v, there's an automorphism σ with σ(v₀) = v where v₀ ∈ C.
    Then σ(C) is a max-clique containing v. -/
lemma exists_maxClique_containing_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hω : 0 < G.cliqueNum)
    (h_vtrans : ∀ i j : V, ∃ φ : G ≃g G, φ i = j) (v : V) :
    ∃ C : Finset V, G.IsClique C ∧ C.card = G.cliqueNum ∧ v ∈ C := by
  -- Get a max-clique C₀
  obtain ⟨C₀, hC₀_clique, hC₀_card⟩ := G.exists_isNClique_cliqueNum
  -- C₀ is nonempty since cliqueNum > 0
  have hC₀_nonempty : C₀.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hC₀_card
    simp at hC₀_card
    omega
  obtain ⟨v₀, hv₀⟩ := hC₀_nonempty
  -- Get automorphism σ with σ(v₀) = v
  obtain ⟨σ, hσ⟩ := h_vtrans v₀ v
  -- σ(C₀) is the desired max-clique
  use C₀.map σ.toEquiv.toEmbedding
  constructor
  · -- σ(C₀) is a clique
    intro x hx y hy hne
    simp only [Finset.coe_map, Equiv.toEmbedding_apply, Set.mem_image] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne' : x' ≠ y' := fun h => hne (congrArg σ.toEquiv h)
    -- σ.toEquiv x' = σ x', so use map_adj_iff
    have hx_eq : σ.toEquiv x' = σ x' := rfl
    have hy_eq : σ.toEquiv y' = σ y' := rfl
    rw [hx_eq, hy_eq, σ.map_adj_iff]
    exact hC₀_clique hx' hy' hne'
  constructor
  · -- |σ(C₀)| = ω
    rw [Finset.card_map]
    exact hC₀_card
  · -- v ∈ σ(C₀)
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    exact ⟨v₀, hv₀, hσ⟩

set_option linter.unusedFintypeInType false in
/-- For vertex-transitive graphs, any FI set has total weight ≤ |V|/ω.

    **Proof (max-clique counting):**
    Let M be the set of all max-cliques (cliques of size ω).
    Let m_v = #{C ∈ M : v ∈ C} (# max-cliques containing v).

    By vertex-transitivity, m_v = m for all v (constant).

    Sum over all max-cliques:
      Σ_{C ∈ M} (Σ_{v ∈ C} fi.weights v) ≤ |M|  (each C contributes ≤ 1 by FI constraint)

    Reorder the sum:
      Σ_v (fi.weights v × m_v) ≤ |M|
      m × fi.totalWeight ≤ |M|

    Double counting: |M| × ω = Σ_{C ∈ M} |C| = Σ_v m_v = |V| × m
    So |M| = |V| × m / ω.

    Therefore: m × fi.totalWeight ≤ |V| × m / ω
    Divide by m (> 0 since every vertex is in some max-clique): fi.totalWeight ≤ |V|/ω.

    **Alternative proof (averaging over automorphisms):**
    Define fi' with weights averaged over Aut(G):
    fi'.weights v = (1/|Aut(G)|) × Σ_σ fi.weights(σ⁻¹ v)
    - fi' is FI (convexity of FI constraint)
    - fi'.totalWeight = fi.totalWeight (bijection)
    - fi'.weights is constant by vertex-transitivity, say = c
    - For any max-clique: ω × c ≤ 1, so c ≤ 1/ω
    - fi.totalWeight = fi'.totalWeight = |V| × c ≤ |V|/ω -/
lemma fractionalIndependentSet_le_card_div_cliqueNum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hω : 0 < G.cliqueNum)
    (h_vtrans : ∀ i j : V, ∃ φ : G ≃g G, φ i = j)
    (fi : FractionalIndependentSet G) :
    fi.totalWeight ≤ (Fintype.card V : ℝ) / G.cliqueNum := by
  classical
  -- Step 1: Get Fintype for automorphism group Aut(G) = G ≃g G
  haveI : Fintype (G ≃g G) := by
    haveI : Finite (G ≃g G) := by
      haveI : Fintype (V ≃ V) := Equiv.instFintype
      apply Finite.of_injective (fun σ : G ≃g G => σ.toEquiv)
      exact RelIso.toEquiv_injective
    exact Fintype.ofFinite _
  let Aut := G ≃g G
  let n : ℕ := Fintype.card Aut
  -- Step 2: Define averaged weights: w'(v) = (1/|Aut|) × Σ_σ w(σ⁻¹ v)
  let w' : V → ℝ := fun v => (1 / n) * Finset.univ.sum (fun σ : Aut => fi.weights (σ.symm v))
  -- Step 3: The averaged weights are constant (same for all vertices)
  have h_const : ∀ v₁ v₂ : V, w' v₁ = w' v₂ := by
    intro v₁ v₂
    obtain ⟨τ, hτ⟩ := h_vtrans v₁ v₂
    simp only [w']
    congr 1
    -- Goal: ∑ σ, fi.weights (σ.symm v₁) = ∑ σ, fi.weights (σ.symm v₂)
    -- Use hτ : τ v₁ = v₂
    rw [← hτ]
    -- Goal: ∑ σ, fi.weights (σ.symm v₁) = ∑ σ, fi.weights (σ.symm (τ v₁))
    -- Use bijection σ ↦ σ.trans τ on the RHS
    -- Key: (σ.trans τ).symm (τ v₁) = σ.symm (τ.symm (τ v₁)) = σ.symm v₁
    symm
    -- After symm, goal is: ∑ σ, fi.weights (σ.symm (τ v₁)) = ∑ σ, fi.weights (σ.symm v₁)
    -- We use bijection e σ = σ.trans τ.symm
    -- Key: (e σ).symm v₁ = (σ.trans τ.symm).symm v₁ = σ.symm (τ.symm.symm v₁) = σ.symm (τ v₁) ✓
    let e : Aut ≃ Aut := {
      toFun := fun σ => σ.trans τ.symm
      invFun := fun ρ => ρ.trans τ
      left_inv := fun σ => by ext v; simp [RelIso.trans_apply]
      right_inv := fun ρ => by ext v; simp [RelIso.trans_apply]
    }
    refine Finset.sum_equiv e ?_ ?_
    · intro σ; simp
    · intro σ _
      -- Need: fi.weights (σ.symm (τ v₁)) = fi.weights ((e σ).symm v₁)
      -- where e σ = σ.trans τ.symm
      -- (σ.trans τ.symm).symm v₁ = σ.symm (τ.symm.symm v₁) = σ.symm (τ v₁) ✓
      congr 1
  -- Step 4: Total weight is preserved: Σ_v w'(v) = Σ_v w(v)
  have h_total : Finset.univ.sum w' = fi.totalWeight := by
    simp only [w', FractionalIndependentSet.totalWeight]
    -- Goal: ∑ v, (1/n) * (∑ σ, fi.weights (σ.symm v)) = ∑ v, fi.weights v
    -- Pull out 1/n factor: (1/n) * ∑ v, ∑ σ, fi.weights (σ.symm v)
    rw [← Finset.mul_sum]
    -- Swap sums: (1/n) * ∑ σ, ∑ v, fi.weights (σ.symm v)
    conv_lhs => arg 2; rw [Finset.sum_comm]
    -- Each σ is a bijection: ∑ v, fi.weights (σ.symm v) = ∑ v, fi.weights v
    have h_bij : ∀ σ : Aut, Finset.univ.sum (fun v => fi.weights (σ.symm v)) =
        Finset.univ.sum fi.weights := by
      intro σ
      exact Finset.sum_equiv σ.symm.toEquiv (by simp) (fun v _ => by simp)
    -- Rewrite each inner sum using h_bij
    have h_sum_eq : (∑ σ : Aut, ∑ v : V, fi.weights (σ.symm v)) =
        ∑ _ : Aut, Finset.univ.sum fi.weights := Finset.sum_congr rfl (fun σ _ => h_bij σ)
    rw [h_sum_eq]
    -- Now: (1/n) * ∑ σ, (∑ v, fi.weights v) = (1/n) * n * (∑ v, fi.weights v)
    rw [Finset.sum_const, Finset.card_univ]
    simp only [n, nsmul_eq_mul]
    -- (1/n) * n * x = x (when n > 0)
    have hn_pos : (0 : ℝ) < Fintype.card Aut := by
      have : 0 < Fintype.card Aut := Fintype.card_pos
      exact Nat.cast_pos.mpr this
    field_simp
  -- Step 5: Get the constant value c = w'(v) for any v
  -- For this, we need V to be nonempty
  by_cases hV : IsEmpty V
  · -- Empty graph case: trivially true
    simp only [FractionalIndependentSet.totalWeight, Fintype.card_eq_zero]
    rw [Finset.sum_eq_zero (fun v _ => hV.elim v)]
    simp
  haveI : Nonempty V := not_isEmpty_iff.mp hV
  let v₀ : V := Classical.arbitrary V
  let c := w' v₀
  -- w' v = c for all v
  have hw'_eq : ∀ v, w' v = c := fun v => h_const v v₀
  -- Step 6: Σ_v w'(v) = |V| × c
  have h_sum_w' : Finset.univ.sum w' = Fintype.card V * c := by
    simp only [Finset.sum_congr rfl (fun v _ => hw'_eq v)]
    simp [Finset.sum_const, Finset.card_univ]
  -- Step 7: Get a max-clique and apply FI constraint to w'
  obtain ⟨C₀, hC₀_clique, hC₀_card, _⟩ := exists_maxClique_containing_vertex G hω h_vtrans v₀
  -- Step 8: Show w' satisfies the clique constraint (by convexity)
  have hw'_clique : ∀ C : Finset V, G.IsClique C → C.sum w' ≤ 1 := by
    intro C hC
    simp only [w']
    -- Goal: ∑ v ∈ C, (1/n) * (∑ σ, fi.weights (σ.symm v)) ≤ 1
    -- Pull out 1/n factor
    rw [← Finset.mul_sum]
    -- Swap the sums: (1/n) * ∑ σ, ∑ v ∈ C, fi.weights (σ.symm v)
    conv_lhs => arg 2; rw [Finset.sum_comm]
    -- Now: (1/n) * (∑ σ, ∑ v ∈ C, fi.weights (σ.symm v)) ≤ 1
    -- Rewrite as division: (∑ σ, ...) / n ≤ 1
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    -- Show (∑ σ, ...) / n ≤ 1 using div_le_one
    have hn_pos : (0 : ℝ) < n := by
      have : 0 < Fintype.card Aut := Fintype.card_pos
      exact Nat.cast_pos.mpr this
    rw [div_le_one hn_pos]
    -- Need: ∑ σ, (∑ v ∈ C, fi.weights (σ.symm v)) ≤ n
    calc ∑ σ : Aut, ∑ v ∈ C, fi.weights (σ.symm v)
        ≤ ∑ _ : Aut, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro σ _
          -- ∑ v ∈ C, fi.weights (σ.symm v) = ∑ u ∈ σ.symm(C), fi.weights u ≤ 1
          -- σ⁻¹(C) is also a clique
          let σC := C.map σ.symm.toEquiv.toEmbedding
          have hσC : G.IsClique (σC : Set V) := by
            intro x hx y hy hne
            simp only [σC, Finset.coe_map, Equiv.toEmbedding_apply, Set.mem_image] at hx hy
            obtain ⟨x', hx', rfl⟩ := hx
            obtain ⟨y', hy', rfl⟩ := hy
            have hne' : x' ≠ y' := fun h => hne (congrArg σ.symm.toEquiv h)
            -- Need to show G.Adj (σ.symm x') (σ.symm y')
            -- σ is a graph iso, so G.Adj x' y' ↔ G.Adj (σ.symm x') (σ.symm y')
            have h_adj : G.Adj x' y' := hC hx' hy' hne'
            exact σ.symm.map_rel_iff.mpr h_adj
          -- Rewrite the sum: ∑ v ∈ C, fi.weights (σ.symm v) = ∑ u ∈ σC, fi.weights u
          have h_sum_eq : ∑ v ∈ C, fi.weights (σ.symm v) = ∑ u ∈ σC, fi.weights u := by
            rw [Finset.sum_map]
            -- Goal: ∑ v ∈ C, fi.weights (σ.symm.toEquiv v) = ∑ v ∈ C, fi.weights (σ.symm v)
            apply Finset.sum_congr rfl
            intro v _
            rfl  -- σ.symm.toEquiv v = σ.symm v definitionally
          rw [h_sum_eq]
          exact fi.clique_bound σC hσC
      _ = n := by simp [Finset.sum_const, Finset.card_univ, n]
  -- Step 9: Apply to max-clique: |C₀| × c ≤ 1, so c ≤ 1/ω
  have hC₀_bound : C₀.sum w' ≤ 1 := hw'_clique C₀ hC₀_clique
  rw [Finset.sum_congr rfl (fun v _ => hw'_eq v)] at hC₀_bound
  simp only [Finset.sum_const] at hC₀_bound
  rw [hC₀_card] at hC₀_bound
  -- G.cliqueNum • c ≤ 1, i.e., G.cliqueNum * c ≤ 1
  rw [nsmul_eq_mul] at hC₀_bound
  have hc_bound : c ≤ 1 / G.cliqueNum := by
    have hω_pos : (0 : ℝ) < G.cliqueNum := Nat.cast_pos.mpr hω
    rw [le_div_iff₀ hω_pos]
    linarith
  -- Step 10: Conclude: fi.totalWeight = |V| × c ≤ |V| / ω
  calc fi.totalWeight
      = Finset.univ.sum w' := h_total.symm
    _ = Fintype.card V * c := h_sum_w'
    _ ≤ Fintype.card V * (1 / G.cliqueNum) := by
        apply mul_le_mul_of_nonneg_left hc_bound
        simp
    _ = (Fintype.card V : ℝ) / G.cliqueNum := by ring

/-- Any fractional clique cover has total weight ≥ |V|/ω.
    Proof: Sum covering constraints, reorder, use |C| ≤ ω. -/
lemma fractionalCliqueCoverNumber_ge_card_div_cliqueNum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hω : 0 < G.cliqueNum) :
    (Fintype.card V : ℝ) / G.cliqueNum ≤ fractionalCliqueCoverNumber G := by
  unfold fractionalCliqueCoverNumber
  apply le_ciInf
  intro cover
  -- Sum the covering constraints: Σ_v (Σ_{C∋v} w(C)) ≥ |V|
  have h1 : (Fintype.card V : ℝ) ≤
      Finset.univ.sum (fun v : V => (cover.cliques.filter (v ∈ ·)).sum cover.weights) := by
    calc (Fintype.card V : ℝ)
        = Finset.univ.sum (fun _ : V => (1 : ℝ)) := by simp [Finset.card_univ]
      _ ≤ Finset.univ.sum (fun v : V => (cover.cliques.filter (v ∈ ·)).sum cover.weights) := by
          apply Finset.sum_le_sum
          intro v _
          exact cover.covers v
  -- Reorder: Σ_v Σ_{C∋v} w(C) = Σ_C w(C) × |C|
  have h2 : Finset.univ.sum (fun v : V => (cover.cliques.filter (v ∈ ·)).sum cover.weights) =
      cover.cliques.sum (fun C => cover.weights C * C.card) := by
    -- Rewrite the double sum by swapping order
    conv_lhs =>
      arg 2; ext v
      rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro C _
    simp only [Finset.sum_ite_mem]
    rw [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    ring
  -- Each |C| ≤ ω, so Σ_C w(C) × |C| ≤ ω × Σ_C w(C)
  have h3 : cover.cliques.sum (fun C => cover.weights C * C.card) ≤
      G.cliqueNum * cover.totalWeight := by
    unfold FractionalCliqueCover.totalWeight
    calc cover.cliques.sum (fun C => cover.weights C * C.card)
        ≤ cover.cliques.sum (fun C => cover.weights C * G.cliqueNum) := by
          apply Finset.sum_le_sum
          intro C hC
          have h_card_le : C.card ≤ G.cliqueNum := (cover.isClique C hC).card_le_cliqueNum
          have h_nonneg : 0 ≤ cover.weights C := cover.nonneg C hC
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h_card_le) h_nonneg
      _ = G.cliqueNum * cover.cliques.sum cover.weights := by
          conv_lhs =>
            arg 2; ext C
            rw [mul_comm]
          rw [← Finset.mul_sum]
  -- Combine: |V| ≤ ω × total_weight, so |V|/ω ≤ total_weight
  have hω_pos : (0 : ℝ) < G.cliqueNum := Nat.cast_pos.mpr hω
  rw [h2] at h1
  calc (Fintype.card V : ℝ) / G.cliqueNum
      ≤ (G.cliqueNum * cover.totalWeight) / G.cliqueNum := by
        apply div_le_div_of_nonneg_right (le_trans h1 h3) (le_of_lt hω_pos)
    _ = cover.totalWeight := by field_simp

/-- For vertex-transitive graphs, χ̄_f = |V|/ω (the formula).

Proof:
- χ̄_f ≥ |V|/ω: counting argument (any cover has weight ≥ |V|/ω)
- α_f ≥ |V|/ω: uniform FI set with weight 1/ω on each vertex
- α_f ≤ χ̄_f: weak duality
- χ̄_f ≤ α_f: LP strong duality
- Combined: χ̄_f = α_f ≥ |V|/ω, and χ̄_f ≥ |V|/ω, so equality follows from LP duality

Reference: Scheinerman-Ullman (2011), Fractional Graph Theory. -/
lemma fractionalCliqueCoverNumber_eq_formula_vertexTransitive
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h_vtrans : ∀ i j : V, ∃ φ : G ≃g G, φ i = j) :
    fractionalCliqueCoverNumber G = fractionalCliqueCoverNumber_formula G := by
  unfold fractionalCliqueCoverNumber_formula
  by_cases hω : G.cliqueNum = 0
  case pos =>
    -- ω = 0 means V is empty
    simp only [hω, ↓reduceDIte]
    have hV : IsEmpty V := by
      rw [isEmpty_iff]
      intro v
      have h2 : G.IsClique (({v} : Finset V) : Set V) := by
        rw [Finset.coe_singleton]
        exact G.isClique_singleton v
      have h3 : ({v} : Finset V).card ≤ G.cliqueNum := h2.card_le_cliqueNum
      simp [Finset.card_singleton] at h3
      omega
    simp only [Fintype.card_eq_zero, CharP.cast_eq_zero]
    -- χ̄_f of empty graph is 0
    unfold fractionalCliqueCoverNumber
    apply le_antisymm
    · -- Show ⨅ cover, cover.totalWeight ≤ 0 using empty cover
      let empty_cover : FractionalCliqueCover G := {
        cliques := ∅
        weights := fun _ => 0
        isClique := fun C hC => (Finset.notMem_empty C hC).elim
        nonneg := fun C hC => (Finset.notMem_empty C hC).elim
        covers := fun v => hV.elim v
      }
      have h_empty : empty_cover.totalWeight = 0 := by
        unfold FractionalCliqueCover.totalWeight
        -- empty_cover.cliques = ∅ definitionally
        rfl
      have h_bdd : BddBelow (Set.range (fun (c : FractionalCliqueCover G) => c.totalWeight)) :=
        ⟨0, fun _ ⟨c, hc⟩ => hc ▸ FractionalCliqueCover.totalWeight_nonneg c⟩
      calc ⨅ (cover : FractionalCliqueCover G), cover.totalWeight
          ≤ empty_cover.totalWeight := ciInf_le h_bdd empty_cover
        _ = 0 := h_empty
    · apply Real.iInf_nonneg
      intro c; exact c.totalWeight_nonneg
  case neg =>
    simp only [hω, ↓reduceDIte]
    have hω_pos : 0 < G.cliqueNum := Nat.pos_of_ne_zero hω
    -- We have:
    -- (1) χ̄_f ≥ |V|/ω (counting argument)
    -- (2) α_f ≥ |V|/ω (uniform FI)
    -- (3) α_f ≤ χ̄_f (weak duality)
    -- (4) χ̄_f = α_f (LP strong duality)
    --
    -- From (4): χ̄_f = α_f
    -- From (1): χ̄_f ≥ |V|/ω
    -- From (2) and (4): χ̄_f = α_f ≥ |V|/ω
    -- So χ̄_f ≥ |V|/ω.
    --
    -- For the upper bound χ̄_f ≤ |V|/ω, we use:
    -- From (3): α_f ≤ χ̄_f
    -- Combined with (4): α_f = χ̄_f
    -- And (2): α_f ≥ |V|/ω
    --
    -- The key insight is that by LP strong duality, χ̄_f = α_f.
    -- The uniform FI achieves α_f ≥ |V|/ω.
    -- By the counting argument, χ̄_f ≥ |V|/ω.
    -- These two lower bounds together with equality give χ̄_f = α_f = |V|/ω.
    --
    -- But we still need the upper bound! The counting gives ≥, not ≤.
    -- For the upper bound, we need to construct a cover achieving |V|/ω.
    -- This requires max-clique infrastructure.
    --
    -- Alternative: Use that for vertex-transitive graphs specifically,
    -- the LP optimal is achieved, so the bounds are tight.
    apply le_antisymm
    · -- Upper bound: χ̄_f ≤ |V|/ω
      -- Use: χ̄_f = α_f (LP duality), and bound α_f ≤ |V|/ω
      rw [lp_duality]
      -- Show α_f ≤ |V|/ω: every FI set has total weight ≤ |V|/ω
      unfold fractionalIndependenceNumber
      -- The zero FI set exists, providing Nonempty
      haveI : Nonempty (FractionalIndependentSet G) := ⟨{
        weights := fun _ => 0
        nonneg := fun _ => le_refl 0
        clique_bound := fun C _ => by simp only [Finset.sum_const_zero]; norm_num
      }⟩
      apply ciSup_le
      intro fi
      exact fractionalIndependentSet_le_card_div_cliqueNum G hω_pos h_vtrans fi
    · -- Lower bound: χ̄_f ≥ |V|/ω (counting argument)
      exact fractionalCliqueCoverNumber_ge_card_div_cliqueNum G hω_pos

/-- chilemma: χ̄_f(E_{p/q}) = p/q (known result from Scheinerman-Ullman).
    For vertex-transitive graphs like fraction graphs, χ̄_f = |V|/ω. -/
theorem chilemma (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    χ̄_f (fractionGraphAsFiniteGraph p q) = (p : ℝ) / q := by
  simp only [fractionalCliqueCovering_finite, fractionalCliqueCoverNumber_finite,
    fractionGraphAsFiniteGraph]
  -- Fraction graphs are vertex-transitive
  have h_vtrans := fractionGraph_vertexTransitive p q
  -- Use the formula for vertex-transitive graphs
  have h_eq := fractionalCliqueCoverNumber_eq_formula_vertexTransitive
    (fractionGraph p q) h_vtrans
  -- The formula gives p/q for fraction graphs
  have h_formula :=
    AsymptoticSpectrumGraphs.fractionalCliqueCoverNumber_fractionGraph p q hq h2q
  -- v4.29: `rw [h_eq]` fails to unify `fractionalCliqueCoverNumber E[p/q]` patterns
  -- across the `fractionGraph p q` / `E[p/q]` notation forms; chain via `.trans`.
  exact h_eq.trans h_formula

/-! ### Spectral point invariance under isomorphism -/

/-- Graph isomorphisms give cohomomorphisms in both directions.
    An isomorphism φ : G ≃g H is a cohomomorphism from G to H. -/
theorem IsCohom_of_Iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) : IsCohom G H φ := by
  intro u v huv hnadj
  constructor
  · intro heq
    have := φ.injective heq
    exact huv this
  · intro hadj
    rw [φ.map_rel_iff] at hadj
    exact hnadj hadj

/-- Spectral points are invariant under graph isomorphism.
    If G ≃g H (as SimpleGraphs on equipotent vertex sets), then φ(G) = φ(H). -/
theorem SpectralPoint.eval_iso (φ : SpectralPoint)
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (iso : G ≃g H) :
    φ.eval { V := V, graph := G } = φ.eval { V := W, graph := H } := by
  apply le_antisymm
  · -- φ(G) ≤ φ(H) by monotonicity (G →co H via iso)
    apply φ.mono_cohom
    exact ⟨iso, IsCohom_of_Iso iso⟩
  · -- φ(H) ≤ φ(G) by monotonicity (H →co G via iso.symm)
    apply φ.mono_cohom
    exact ⟨iso.symm, IsCohom_of_Iso iso.symm⟩

/-- The edgeless graph on ZMod n is isomorphic to the edgeless graph on Fin n. -/
noncomputable def edgelessIsoZMod (n : ℕ) [NeZero n] :
    (⊥ : SimpleGraph (Fin n)) ≃g (⊥ : SimpleGraph (ZMod n)) := by
  have e : Fin n ≃ ZMod n := Fintype.equivOfCardEq (by simp)
  exact {
    toEquiv := e
    map_rel_iff' := by simp [bot_adj]
  }

end Universality
