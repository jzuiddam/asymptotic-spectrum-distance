/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.RationalLP
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.LP
import AsymptoticSpectrumDistance.Prerequisites.FractionGraph

/-!
# Fractional Clique Covering Number

This file defines the fractional clique covering number χ̄_f(G) and proves
that it satisfies the spectral axioms, making it a spectral point.

## Main definitions

* `FractionalCliqueCover G` : A fractional clique cover of graph G
* `fractionalCliqueCoverNumber G` : The infimum χ̄_f(G) over all fractional covers
* `FractionalIndependentSet G` : A fractional independent set of graph G
* `fractionalIndependenceNumber G` : The supremum α_f(G) over all fractional independent sets

## Main results

* `fractionalCliqueCoverNumber_cohom_mono` : χ̄_f is monotone under cohomomorphisms
* `fractionalCliqueCoverNumber_sub_add` : χ̄_f(G ⊔ H) ≤ χ̄_f(G) + χ̄_f(H)
* `fractionalCliqueCoverNumber_sub_mul` : χ̄_f(G ⊠ H) ≤ χ̄_f(G) * χ̄_f(H)
* `lp_duality` : χ̄_f(G) = α_f(G) (LP duality)
* `chibar_spectralPoint` : χ̄_f is a spectral point

## References

* Scheinerman & Ullman (2011), Fractional Graph Theory
* Zuiddam (2019), Asymptotic spectrum of graphs

-/

namespace AsymptoticSpectrumGraphs

open SimpleGraph

/-! ### Fractional clique covers -/

/-- A fractional clique cover assigns non-negative weights to cliques
    such that each vertex is covered with total weight ≥ 1.
    This is the LP formulation of the fractional clique covering number. -/
structure FractionalCliqueCover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  /-- The set of cliques used in the cover -/
  cliques : Finset (Finset V)
  /-- Weight assigned to each clique (0 for cliques not in the cover) -/
  weights : Finset V → ℝ
  /-- All sets in the cover are cliques of G -/
  isClique : ∀ C ∈ cliques, G.IsClique C
  /-- Weights are non-negative for cliques in the cover -/
  nonneg : ∀ C ∈ cliques, 0 ≤ weights C
  /-- Each vertex is covered with total weight ≥ 1 -/
  covers : ∀ v : V, 1 ≤ (cliques.filter (v ∈ ·)).sum weights

/-- The total weight of a fractional clique cover -/
def FractionalCliqueCover.totalWeight {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (cover : FractionalCliqueCover G) : ℝ :=
  cover.cliques.sum cover.weights

/-- Every finite graph has at least one fractional clique cover:
    the singleton cover where each vertex {v} is a clique with weight 1. -/
theorem FractionalCliqueCover.exists_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Nonempty V] : Nonempty (FractionalCliqueCover G) := by
  -- Use singleton sets {v} for each vertex v
  let cliques : Finset (Finset V) := Finset.univ.image (fun v => {v})
  let weights : Finset V → ℝ := fun _ => 1
  refine ⟨⟨cliques, weights, ?_, ?_, ?_⟩⟩
  · -- Each singleton {v} is a clique (vacuously true)
    intro C hC
    rw [Finset.mem_image] at hC
    obtain ⟨v, _, rfl⟩ := hC
    rw [isClique_iff, Set.Pairwise]
    intro x hx y hy hxy
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    exact (hxy (hx.trans hy.symm)).elim
  · -- All weights are non-negative
    intro C _
    norm_num
  · -- Each vertex is covered
    intro v
    have hv : {v} ∈ cliques := Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    have hmem : {v} ∈ cliques.filter (v ∈ ·) := by
      simp only [Finset.mem_filter, hv, Finset.mem_singleton, true_and]
    calc (cliques.filter (v ∈ ·)).sum weights
      ≥ weights {v} := Finset.single_le_sum (fun _ _ => by norm_num) hmem
      _ = 1 := rfl

/-- For an empty graph, we use a trivial cover -/
theorem FractionalCliqueCover.exists_empty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hV : IsEmpty V) : Nonempty (FractionalCliqueCover G) := by
  refine ⟨⟨∅, fun _ => 0, ?_, ?_, ?_⟩⟩
  · intro C hC; exact (Finset.notMem_empty C hC).elim
  · intro C hC; exact (Finset.notMem_empty C hC).elim
  · intro v; exact hV.elim v

/-- Every finite graph has a fractional clique cover (instance for type class inference). -/
instance FractionalCliqueCover.instNonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Nonempty (FractionalCliqueCover G) := by
  by_cases h : Nonempty V
  · exact exists_singleton G
  · exact exists_empty G (not_nonempty_iff.mp h)

/-- The infimum of total weights is bounded below by 0 -/
theorem FractionalCliqueCover.totalWeight_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (cover : FractionalCliqueCover G) : 0 ≤ cover.totalWeight := by
  unfold totalWeight
  apply Finset.sum_nonneg
  intro C hC
  exact cover.nonneg C hC

/-! ### Fractional clique covering number -/

/-- The fractional clique covering number χ̄_f(G) is the infimum of total weights
    over all fractional clique covers. For finite graphs, this infimum is attained. -/
noncomputable def fractionalCliqueCoverNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  ⨅ (cover : FractionalCliqueCover G), cover.totalWeight

/-- The fractional clique covering number is non-negative -/
theorem fractionalCliqueCoverNumber_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Nonempty (FractionalCliqueCover G)] :
    0 ≤ fractionalCliqueCoverNumber G := by
  unfold fractionalCliqueCoverNumber
  apply Real.iInf_nonneg
  intro cover
  exact cover.totalWeight_nonneg

/-- The fractional clique covering number is at most n (the number of vertices).
    This follows from the singleton cover having total weight n. -/
theorem fractionalCliqueCoverNumber_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Nonempty V] :
    fractionalCliqueCoverNumber G ≤ Fintype.card V := by
  unfold fractionalCliqueCoverNumber
  -- Construct the singleton cover explicitly
  let cliques : Finset (Finset V) := Finset.univ.image (fun v => {v})
  let weights : Finset V → ℝ := fun _ => 1
  -- The singleton cover
  let cover : FractionalCliqueCover G := ⟨cliques, weights,
    (fun C hC => by
      rw [Finset.mem_image] at hC
      obtain ⟨v, _, rfl⟩ := hC
      rw [isClique_iff, Set.Pairwise]
      intro x hx y hy hxy
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      exact (hxy (hx.trans hy.symm)).elim),
    (fun _ _ => by norm_num),
    (fun v => by
      have hv : {v} ∈ cliques := Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
      have hmem : {v} ∈ cliques.filter (v ∈ ·) := by
        simp only [Finset.mem_filter, hv, Finset.mem_singleton, true_and]
      calc (cliques.filter (v ∈ ·)).sum weights
        ≥ weights {v} := Finset.single_le_sum (fun _ _ => by norm_num) hmem
        _ = 1 := rfl)⟩
  have hbdd : BddBelow (Set.range (fun c : FractionalCliqueCover G => c.totalWeight)) := by
    use 0
    intro _ ⟨c, hc⟩
    rw [← hc]
    exact c.totalWeight_nonneg
  -- The infimum is at most the weight of this cover
  have hweight : cover.totalWeight = Fintype.card V := by
    unfold FractionalCliqueCover.totalWeight
    -- cliques = Finset.univ.image (fun v => {v}) has |V| elements
    have hcard : cliques.card = Fintype.card V := by
      have hinj : Function.Injective (fun v : V => ({v} : Finset V)) := by
        intro v₁ v₂ h
        simp only [Finset.singleton_inj] at h
        exact h
      rw [Finset.card_image_of_injective _ hinj]
      exact Finset.card_univ
    calc cover.cliques.sum cover.weights
      = cliques.sum weights := rfl
      _ = cliques.sum (fun _ => (1 : ℝ)) := rfl
      _ = cliques.card • (1 : ℝ) := Finset.sum_const 1
      _ = (cliques.card : ℝ) := by ring
      _ = (Fintype.card V : ℝ) := by rw [hcard]
  calc ⨅ c : FractionalCliqueCover G, c.totalWeight
    ≤ cover.totalWeight := ciInf_le hbdd cover
    _ = Fintype.card V := hweight

/-- The fractional clique covering number formula for vertex-transitive graphs.
    For vertex-transitive graphs, χ̄_f(G) = |V|/ω(G).
    This formula gives the correct value for fraction graphs. -/
noncomputable def fractionalCliqueCoverNumber_formula {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  if _ : G.cliqueNum = 0 then Fintype.card V
  else (Fintype.card V : ℝ) / G.cliqueNum

/-! ### Spectral axioms for fractional clique covering number -/

/-- For a cohomomorphism, the preimage of a clique is a clique.
    This is key to the pullback construction for proving monotonicity. -/
theorem cohom_preimage_clique {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v))
    {C : Finset W} (hC : H.IsClique C) :
    G.IsClique (Finset.univ.filter (f · ∈ C)) := by
  classical
  rw [isClique_iff, Set.Pairwise]
  intro u hu v hv huv
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu hv
  -- f(u) ∈ C and f(v) ∈ C, so either f(u) = f(v) or f(u) adj f(v)
  by_cases hfuv : f u = f v
  · -- If f(u) = f(v), then by contrapositive of cohomomorphism, u adj v
    by_contra hnadj
    have := hf u v huv hnadj
    exact this.1 hfuv
  · -- If f(u) ≠ f(v) and both in clique C, then f(u) adj f(v) in H
    -- hC : (C : Set W).Pairwise H.Adj, so we can apply it directly
    have hadj_H : H.Adj (f u) (f v) := hC hu hv hfuv
    -- By contrapositive of cohomomorphism: u adj v in G
    by_contra hnadj
    have := hf u v huv hnadj
    exact this.2 hadj_H

/-- Spectral axiom (iv): χ̄_f is monotone under cohomomorphisms.
    If f : G →co H (cohomomorphism), then χ̄_f(G) ≤ χ̄_f(H).

    Proof idea: Given a fractional clique cover of H, we can pull it back
    along the cohomomorphism to get a cover of G with the same total weight. -/
theorem fractionalCliqueCoverNumber_cohom_mono {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W)
    (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v)) :
    fractionalCliqueCoverNumber G ≤ fractionalCliqueCoverNumber H := by
  unfold fractionalCliqueCoverNumber
  have hbddG : BddBelow (Set.range (fun c : FractionalCliqueCover G => c.totalWeight)) := by
    use 0; intro _ ⟨c, hc⟩; rw [← hc]; exact c.totalWeight_nonneg
  -- For any cover of H, we construct a cover of G with at most the same weight
  apply le_ciInf
  intro coverH
  -- Pullback construction: preimage cliques with aggregated weights
  let pullbackCliques : Finset (Finset V) :=
    coverH.cliques.image (fun C => Finset.univ.filter (f · ∈ C))
  let pullbackWeights : Finset V → ℝ := fun D =>
    (coverH.cliques.filter (fun C => Finset.univ.filter (f · ∈ C) = D)).sum coverH.weights
  -- The pullback is a valid cover
  let pullbackCover : FractionalCliqueCover G := ⟨pullbackCliques, pullbackWeights,
    -- Each pullback set is a clique
    (fun D hD => by
      rw [Finset.mem_image] at hD
      obtain ⟨C, hC, rfl⟩ := hD
      exact cohom_preimage_clique f hf (coverH.isClique C hC)),
    -- Weights are non-negative
    (fun D _ => by
      apply Finset.sum_nonneg
      intro C hC
      rw [Finset.mem_filter] at hC
      exact coverH.nonneg C hC.1),
    -- Each vertex is covered
    (fun v => by
      -- v is covered if f(v) is covered in H
      have hcov :
          (1 : ℝ) ≤ (coverH.cliques.filter (f v ∈ ·)).sum coverH.weights :=
        coverH.covers (f v)
      -- The cliques containing f(v) pull back to cliques containing v
      -- Key: for each C with f(v) ∈ C, its pullback D = f⁻¹(C) contains v
      -- and the sum reorganizes via Finset.sum_fiberwise_of_maps_to
      let preimg : Finset W → Finset V := fun C => Finset.univ.filter (f · ∈ C)
      have hmaps :
          ∀ C ∈ coverH.cliques.filter (f v ∈ ·),
            preimg C ∈ pullbackCliques.filter (v ∈ ·) := by
        intro C hC
        rw [Finset.mem_filter] at hC ⊢
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_image]
          exact ⟨C, hC.1, rfl⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ v, hC.2⟩
      have heq : (coverH.cliques.filter (f v ∈ ·)).sum coverH.weights =
          (pullbackCliques.filter (v ∈ ·)).sum pullbackWeights := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        apply Finset.sum_congr rfl
        intro D hD
        rw [Finset.mem_filter] at hD
        -- D ∈ pullbackCliques.filter (v ∈ ·), so v ∈ D
        apply Finset.sum_congr
        · ext C
          simp only [Finset.mem_filter]
          constructor
          · intro h; exact ⟨h.1.1, h.2⟩
          · intro h
            refine ⟨⟨h.1, ?_⟩, h.2⟩
            -- Need: f v ∈ C. We know preimg C = D and v ∈ D
            -- preimg C = {x | f x ∈ C} = D, so v ∈ D → f v ∈ C
            have := hD.2
            rw [← h.2] at this
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
            exact this
        · intro _ _; rfl
      calc (1 : ℝ)
        ≤ (coverH.cliques.filter (f v ∈ ·)).sum coverH.weights := hcov
        _ = (pullbackCliques.filter (v ∈ ·)).sum pullbackWeights := heq)⟩
  -- The pullback cover has weight ≤ the original cover
  calc ⨅ c : FractionalCliqueCover G, c.totalWeight
    ≤ pullbackCover.totalWeight := ciInf_le hbddG pullbackCover
    _ ≤ coverH.totalWeight := by
        -- totalWeight of pullback = sum over D of (sum over C with preimage D of weight(C))
        -- = sum over all C of weight(C) = totalWeight of H-cover
        unfold FractionalCliqueCover.totalWeight
        -- The double sum equals the original sum: each C appears in exactly one filter
        -- (the one for D = f⁻¹(C)), so we can reassemble the sum
        -- Using Finset.sum_fiberwise_of_maps_to
        let preimg : Finset W → Finset V := fun C => Finset.univ.filter (f · ∈ C)
        have hsubset : ∀ C ∈ coverH.cliques, preimg C ∈ pullbackCliques := by
          intro C hC
          rw [Finset.mem_image]
          exact ⟨C, hC, rfl⟩
        have heq : pullbackCliques.sum pullbackWeights = coverH.cliques.sum coverH.weights := by
          calc pullbackCliques.sum pullbackWeights
            = pullbackCliques.sum (fun D =>
                (coverH.cliques.filter (preimg · = D)).sum coverH.weights) := rfl
            _ = coverH.cliques.sum coverH.weights := by
                rw [← Finset.sum_fiberwise_of_maps_to hsubset]
        rw [heq]

/-- Alias for disjUnionSimple for backwards compatibility -/
abbrev disjointUnion {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V ⊕ W) := disjUnionSimple G H

/-! ### Sub-multiplicativity and sub-additivity of χ̄_f

These follow from the primal (covering) definition: given covers of G and H,
we can construct covers of G ⊠ H and G ⊔ H. -/

/-- Embed a clique from G into disjointUnion G H via Sum.inl -/
def embedCliqueLeft {V W : Type*} (C : Finset V) : Finset (V ⊕ W) :=
  C.map ⟨Sum.inl, Sum.inl_injective⟩

/-- Embed a clique from H into disjointUnion G H via Sum.inr -/
def embedCliqueRight {V W : Type*} (C : Finset W) : Finset (V ⊕ W) :=
  C.map ⟨Sum.inr, Sum.inr_injective⟩

/-- Cliques in G embed to cliques in disjointUnion G H -/
theorem embedCliqueLeft_isClique {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {C : Finset V} (hC : G.IsClique C) :
    (disjointUnion G H).IsClique (embedCliqueLeft C : Finset (V ⊕ W)) := by
  rw [isClique_iff, Set.Pairwise]
  intro x hx y hy hxy
  simp only [embedCliqueLeft, Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  simp only [disjUnionSimple] at hxy ⊢
  have hab : a ≠ b := fun h => hxy (congrArg Sum.inl h)
  rw [isClique_iff, Set.Pairwise] at hC
  exact hC ha hb hab

/-- Cliques in H embed to cliques in disjointUnion G H -/
theorem embedCliqueRight_isClique {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {C : Finset W} (hC : H.IsClique C) :
    (disjointUnion G H).IsClique (embedCliqueRight C : Finset (V ⊕ W)) := by
  rw [isClique_iff, Set.Pairwise]
  intro x hx y hy hxy
  simp only [embedCliqueRight, Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  simp only [disjUnionSimple] at hxy ⊢
  have hab : a ≠ b := fun h => hxy (congrArg Sum.inr h)
  rw [isClique_iff, Set.Pairwise] at hC
  exact hC ha hb hab

/-- Combine fractional clique covers of G and H into a cover of disjointUnion G H.
    The combined cover has total weight = coverG.totalWeight + coverH.totalWeight. -/
noncomputable def FractionalCliqueCover.combine {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (coverG : FractionalCliqueCover G) (coverH : FractionalCliqueCover H) :
    FractionalCliqueCover (disjointUnion G H) where
  cliques := (coverG.cliques.map ⟨embedCliqueLeft, fun _ _ h => by
      simp only [embedCliqueLeft, Finset.map_inj] at h; exact h⟩) ∪
    (coverH.cliques.map ⟨embedCliqueRight, fun _ _ h => by
      simp only [embedCliqueRight, Finset.map_inj] at h; exact h⟩)
  weights := fun C =>
    if h : ∃ C' ∈ coverG.cliques, embedCliqueLeft C' = C then
      coverG.weights (Classical.choose h)
    else if h : ∃ C' ∈ coverH.cliques, embedCliqueRight C' = C then
      coverH.weights (Classical.choose h)
    else 0
  isClique := by
    intro C hC
    simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at hC
    rcases hC with ⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩
    · exact embedCliqueLeft_isClique (coverG.isClique C' hC')
    · exact embedCliqueRight_isClique (coverH.isClique C' hC')
  nonneg := by
    intro C _
    split_ifs with h1 h2
    · exact coverG.nonneg _ (Classical.choose_spec h1).1
    · exact coverH.nonneg _ (Classical.choose_spec h2).1
    · exact le_refl 0
  covers := by
    intro v
    cases v with
    | inl a =>
      -- Vertex Sum.inl a from G: covered by cliques from coverG
      -- The cliques containing Sum.inl a are exactly embedCliqueLeft of cliques containing a
      have hcoverG := coverG.covers a
      -- Step 1: identify cliques containing Sum.inl a
      -- embedCliqueLeft C contains Sum.inl a iff a ∈ C
      have hLeft_mem : ∀ C, Sum.inl a ∈ (embedCliqueLeft C : Finset (V ⊕ W)) ↔ a ∈ C := by
        intro C
        simp only [embedCliqueLeft, Finset.mem_map, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨x, hx, heq⟩
          have : x = a := Sum.inl_injective heq
          rw [← this]; exact hx
        · intro ha
          exact ⟨a, ha, rfl⟩
      -- embedCliqueRight cliques never contain Sum.inl a
      have hRight_notmem : ∀ C, Sum.inl a ∉ (embedCliqueRight C : Finset (V ⊕ W)) := by
        intro C h
        simp only [embedCliqueRight, Finset.mem_map, Function.Embedding.coeFn_mk] at h
        obtain ⟨x, _, heq⟩ := h
        cases heq
      -- The filter of combined cliques containing Sum.inl a equals embedCliqueLeft of filter
      -- Calculate: sum over combined cliques = sum over embedCliqueLeft cliques
      let combinedCliques : Finset (Finset (V ⊕ W)) :=
        (coverG.cliques.map ⟨embedCliqueLeft, fun _ _ h => by
          simp only [embedCliqueLeft, Finset.map_inj] at h; exact h⟩) ∪
        (coverH.cliques.map ⟨embedCliqueRight, fun _ _ h => by
          simp only [embedCliqueRight, Finset.map_inj] at h; exact h⟩)
      let wts : Finset (V ⊕ W) → ℝ := fun C =>
        if h :
            ∃ C' ∈ coverG.cliques, (embedCliqueLeft C' : Finset (V ⊕ W)) = C then
          coverG.weights (Classical.choose h)
        else if h :
            ∃ C' ∈ coverH.cliques, (embedCliqueRight C' : Finset (V ⊕ W)) = C then
          coverH.weights (Classical.choose h)
        else 0
      -- The goal is: the sum over filtered combinedCliques ≥ 1
      change 1 ≤ (combinedCliques.filter (Sum.inl a ∈ ·)).sum wts
      -- First, show embedCliqueLeft maps filter to filter
      have hfilter_eq : combinedCliques.filter (Sum.inl a ∈ ·) =
          (coverG.cliques.filter (a ∈ ·)).map
            ⟨embedCliqueLeft, fun _ _ h => by
              simp only [embedCliqueLeft, Finset.map_inj] at h
              exact h⟩ := by
        ext C
        simp only [Finset.mem_filter, combinedCliques, Finset.mem_union,
          Finset.mem_map, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩, hmem⟩
          · rw [hLeft_mem] at hmem
            exact ⟨C', ⟨hC', hmem⟩, rfl⟩
          · exact (hRight_notmem C' hmem).elim
        · rintro ⟨C', ⟨hC'mem, ha_in⟩, rfl⟩
          constructor
          · left; exact ⟨C', hC'mem, rfl⟩
          · rw [hLeft_mem]; exact ha_in
      have hsum_ge : (coverG.cliques.filter (a ∈ ·)).sum coverG.weights ≤
          (combinedCliques.filter (Sum.inl a ∈ ·)).sum wts := by
        rw [hfilter_eq]
        rw [Finset.sum_map]
        apply Finset.sum_le_sum
        intro C' hC'
        simp only [Function.Embedding.coeFn_mk]
        -- Show wts (embedCliqueLeft C') = coverG.weights C'
        have hexists : ∃ C'' ∈ coverG.cliques,
            (embedCliqueLeft C'' : Finset (V ⊕ W)) = embedCliqueLeft C' := by
          exact ⟨C', (Finset.mem_filter.mp hC').1, rfl⟩
        rw [dif_pos hexists]
        -- Show Classical.choose hexists = C' using injectivity
        have hinj : ∀ C₁ C₂ : Finset V,
            (embedCliqueLeft C₁ : Finset (V ⊕ W)) = embedCliqueLeft C₂ → C₁ = C₂ := by
          intro C₁ C₂ h
          simp only [embedCliqueLeft, Finset.map_inj] at h
          exact h
        have hchoose := Classical.choose_spec hexists
        have heq : Classical.choose hexists = C' := hinj _ _ hchoose.2
        rw [heq]
      calc 1 ≤ (coverG.cliques.filter (a ∈ ·)).sum coverG.weights := hcoverG
        _ ≤ (combinedCliques.filter (Sum.inl a ∈ ·)).sum wts := hsum_ge
    | inr b =>
      -- Vertex Sum.inr b from H: covered by cliques from coverH (symmetric argument)
      have hcoverH := coverH.covers b
      -- embedCliqueRight C contains Sum.inr b iff b ∈ C
      have hRight_mem : ∀ C, Sum.inr b ∈ (embedCliqueRight C : Finset (V ⊕ W)) ↔ b ∈ C := by
        intro C
        simp only [embedCliqueRight, Finset.mem_map, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨x, hx, heq⟩
          have : x = b := Sum.inr_injective heq
          rw [← this]; exact hx
        · intro hb
          exact ⟨b, hb, rfl⟩
      -- embedCliqueLeft cliques never contain Sum.inr b
      have hLeft_notmem : ∀ C, Sum.inr b ∉ (embedCliqueLeft C : Finset (V ⊕ W)) := by
        intro C h
        simp only [embedCliqueLeft, Finset.mem_map, Function.Embedding.coeFn_mk] at h
        obtain ⟨x, _, heq⟩ := h
        cases heq
      let combinedCliques : Finset (Finset (V ⊕ W)) :=
        (coverG.cliques.map ⟨embedCliqueLeft, fun _ _ h => by
          simp only [embedCliqueLeft, Finset.map_inj] at h; exact h⟩) ∪
        (coverH.cliques.map ⟨embedCliqueRight, fun _ _ h => by
          simp only [embedCliqueRight, Finset.map_inj] at h; exact h⟩)
      let wts : Finset (V ⊕ W) → ℝ := fun C =>
        if h : ∃ C' ∈ coverG.cliques, (embedCliqueLeft C' : Finset (V ⊕ W)) = C then
          coverG.weights (Classical.choose h)
        else if h : ∃ C' ∈ coverH.cliques, (embedCliqueRight C' : Finset (V ⊕ W)) = C then
          coverH.weights (Classical.choose h)
        else 0
      change 1 ≤ (combinedCliques.filter (Sum.inr b ∈ ·)).sum wts
      have hfilter_eq : combinedCliques.filter (Sum.inr b ∈ ·) =
          (coverH.cliques.filter (b ∈ ·)).map
            ⟨embedCliqueRight, fun _ _ h => by
              simp only [embedCliqueRight, Finset.map_inj] at h
              exact h⟩ := by
        ext C
        simp only [Finset.mem_filter, combinedCliques, Finset.mem_union,
          Finset.mem_map, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩, hmem⟩
          · exact (hLeft_notmem C' hmem).elim
          · rw [hRight_mem] at hmem
            exact ⟨C', ⟨hC', hmem⟩, rfl⟩
        · rintro ⟨C', ⟨hC'mem, hb_in⟩, rfl⟩
          constructor
          · right; exact ⟨C', hC'mem, rfl⟩
          · rw [hRight_mem]; exact hb_in
      have hsum_ge : (coverH.cliques.filter (b ∈ ·)).sum coverH.weights ≤
          (combinedCliques.filter (Sum.inr b ∈ ·)).sum wts := by
        rw [hfilter_eq]
        rw [Finset.sum_map]
        apply Finset.sum_le_sum
        intro C' hC'
        simp only [Function.Embedding.coeFn_mk]
        -- For embedCliqueRight, the first dif_pos condition is false
        have hnot_left : ¬∃ C'' ∈ coverG.cliques,
            (embedCliqueLeft C'' : Finset (V ⊕ W)) = embedCliqueRight C' := by
          intro ⟨C'', _, heq⟩
          -- embedCliqueLeft and embedCliqueRight have disjoint images (except both empty)
          -- If C'' is non-empty, elements are Sum.inl; if C' is non-empty, elements are Sum.inr
          by_cases hC''_empty : C'' = ∅
          · -- C'' = ∅, so embedCliqueLeft C'' = ∅
            simp only [hC''_empty, embedCliqueLeft, Finset.map_empty] at heq
            by_cases hC'_empty : C' = ∅
            · -- Both empty - but C' ∈ filter means b ∈ C', contradiction
              rw [hC'_empty] at hC'
              simp only [Finset.mem_filter, Finset.notMem_empty, and_false] at hC'
            · -- C' nonempty, so embedCliqueRight C' nonempty
              have hne : (embedCliqueRight C' : Finset (V ⊕ W)).Nonempty := by
                simp only [embedCliqueRight, Finset.map_nonempty]
                exact Finset.nonempty_iff_ne_empty.mpr hC'_empty
              simp only [embedCliqueRight] at heq hne
              rw [← heq] at hne
              exact Finset.not_nonempty_empty hne
          · -- C'' nonempty, so embedCliqueLeft C'' nonempty with Sum.inl elements
            have hne : C''.Nonempty := Finset.nonempty_iff_ne_empty.mpr hC''_empty
            obtain ⟨v, hv⟩ := hne
            -- Sum.inl v ∈ embedCliqueLeft C''
            have hmemL : Sum.inl v ∈ (embedCliqueLeft C'' : Finset (V ⊕ W)) := by
              simp only [embedCliqueLeft, Finset.mem_map, Function.Embedding.coeFn_mk]
              exact ⟨v, hv, rfl⟩
            -- By heq, Sum.inl v ∈ embedCliqueRight C'
            have hmemR : Sum.inl v ∈ (embedCliqueRight C' : Finset (V ⊕ W)) := by
              rw [← heq]; exact hmemL
            -- But embedCliqueRight only contains Sum.inr elements
            simp only [embedCliqueRight, Finset.mem_map, Function.Embedding.coeFn_mk] at hmemR
            obtain ⟨w, _, hwx⟩ := hmemR
            cases hwx
        rw [dif_neg hnot_left]
        have hexists : ∃ C'' ∈ coverH.cliques,
            (embedCliqueRight C'' : Finset (V ⊕ W)) = embedCliqueRight C' := by
          exact ⟨C', (Finset.mem_filter.mp hC').1, rfl⟩
        rw [dif_pos hexists]
        have hinj : ∀ C₁ C₂ : Finset W,
            (embedCliqueRight C₁ : Finset (V ⊕ W)) = embedCliqueRight C₂ → C₁ = C₂ := by
          intro C₁ C₂ h
          simp only [embedCliqueRight, Finset.map_inj] at h
          exact h
        have hchoose := Classical.choose_spec hexists
        have heq : Classical.choose hexists = C' := hinj _ _ hchoose.2
        rw [heq]
      calc 1 ≤ (coverH.cliques.filter (b ∈ ·)).sum coverH.weights := hcoverH
        _ ≤ (combinedCliques.filter (Sum.inr b ∈ ·)).sum wts := hsum_ge

/-- The combined cover has total weight at most the sum of individual weights.
    When the union is disjoint, equality holds; otherwise we may undercount
    if both covers have empty cliques (but that's fine for sub-additivity). -/
theorem FractionalCliqueCover.combine_totalWeight {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (coverG : FractionalCliqueCover G) (coverH : FractionalCliqueCover H) :
    (coverG.combine coverH).totalWeight ≤ coverG.totalWeight + coverH.totalWeight := by
  -- The combined cover uses cliques from both covers.
  -- Left cliques get their original weights.
  -- Right cliques get their original weights UNLESS they overlap with left (only ∅ can).
  -- The total weight is ≤ sum because we may undercount if both have empty clique.
  unfold FractionalCliqueCover.totalWeight FractionalCliqueCover.combine
  simp only
  -- Define the weight function
  let wts : Finset (V ⊕ W) → ℝ := fun C =>
    if h : ∃ C' ∈ coverG.cliques, embedCliqueLeft C' = C then
      coverG.weights (Classical.choose h)
    else if h : ∃ C' ∈ coverH.cliques, embedCliqueRight C' = C then
      coverH.weights (Classical.choose h)
    else 0
  -- Key: all weights are non-negative
  have hwts_nonneg : ∀ C, 0 ≤ wts C := by
    intro C
    simp only [wts]
    split_ifs with h1 h2
    · exact coverG.nonneg _ (Classical.choose_spec h1).1
    · exact coverH.nonneg _ (Classical.choose_spec h2).1
    · exact le_refl 0
  -- The embedding functions are injective
  have hinjL : Function.Injective (embedCliqueLeft : Finset V → Finset (V ⊕ W)) := by
    intro C1 C2 h
    simp only [embedCliqueLeft, Finset.map_inj] at h
    exact h
  have hinjR : Function.Injective (embedCliqueRight : Finset W → Finset (V ⊕ W)) := by
    intro C1 C2 h
    simp only [embedCliqueRight, Finset.map_inj] at h
    exact h
  -- L and R are almost disjoint (only possible overlap is ∅ if both covers have empty cliques)
  -- We use the fact that for non-negative weights: sum over (A ∪ B) ≤ sum over A + sum over B
  let L := Finset.map ⟨embedCliqueLeft, hinjL⟩ coverG.cliques
  let R := Finset.map ⟨embedCliqueRight, hinjR⟩ coverH.cliques
  -- Show sum over left = coverG.totalWeight
  have hleft : L.sum wts = coverG.cliques.sum coverG.weights := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro CG hCG
    simp only [Function.Embedding.coeFn_mk]
    have hexists : ∃ C' ∈ coverG.cliques,
        (embedCliqueLeft (V := V) (W := W) C' = embedCliqueLeft CG) := ⟨CG, hCG, rfl⟩
    simp only [dif_pos hexists]
    have heq : Classical.choose hexists = CG := hinjL (Classical.choose_spec hexists).2
    rw [heq]
  -- Key insight: L ∪ R = L ∪ (R \ L), where L and (R \ L) are disjoint.
  -- For C ∈ R \ L, hexistsL is false so wts(C) = coverH.weights of the preimage
  have hRdiff_le : (R \ L).sum wts ≤ coverH.cliques.sum coverH.weights := by
    -- Define subset of coverH.cliques that maps into R \ L
    let S := coverH.cliques.filter (fun CH => embedCliqueRight CH ∉ L)
    have hRdiff_eq : R \ L = S.map ⟨embedCliqueRight, hinjR⟩ := by
      ext C
      simp only [Finset.mem_sdiff, Finset.mem_map, Function.Embedding.coeFn_mk,
                 Finset.mem_filter, R, S]
      constructor
      · intro ⟨hR, hnotL⟩
        obtain ⟨CH, hCH, heq⟩ := hR
        exact ⟨CH, ⟨hCH, heq ▸ hnotL⟩, heq⟩
      · intro ⟨CH, ⟨hCH, hnotL⟩, heq⟩
        exact ⟨⟨CH, hCH, heq⟩, heq ▸ hnotL⟩
    calc (R \ L).sum wts
      = S.sum (fun CH => wts (embedCliqueRight CH)) := by
          rw [hRdiff_eq, Finset.sum_map]; rfl
      _ = S.sum coverH.weights := by
        apply Finset.sum_congr rfl
        intro CH hCH
        simp only [Finset.mem_filter, S] at hCH
        simp only [wts]
        have hnotExistsL :
            ¬∃ C' ∈ coverG.cliques, embedCliqueLeft C' = embedCliqueRight CH := by
          intro ⟨C', hC', heq⟩
          apply hCH.2
          simp only [L, Finset.mem_map, Function.Embedding.coeFn_mk]
          exact ⟨C', hC', heq⟩
        simp only [dif_neg hnotExistsL]
        have hexistsR :
            ∃ C' ∈ coverH.cliques,
              (embedCliqueRight (V := V) C' = embedCliqueRight CH) := by
          exact ⟨CH, hCH.1, rfl⟩
        rw [dif_pos hexistsR, hinjR (Classical.choose_spec hexistsR).2]
      _ ≤ coverH.cliques.sum coverH.weights := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro CH hCH _
        exact coverH.nonneg CH hCH
  -- Decompose L ∪ R as L ∪ (R \ L) which are disjoint
  have hLR_eq : L ∪ R = L ∪ (R \ L) := (Finset.union_sdiff_self_eq_union).symm
  have hLR_disj : Disjoint L (R \ L) := Finset.disjoint_sdiff
  calc (L ∪ R).sum wts
    = L.sum wts + (R \ L).sum wts := by rw [hLR_eq, Finset.sum_union hLR_disj]
    _ = coverG.cliques.sum coverG.weights + (R \ L).sum wts := by rw [hleft]
    _ ≤ coverG.cliques.sum coverG.weights + coverH.cliques.sum coverH.weights := by
      linarith [hRdiff_le]

/-- χ̄_f is sub-additive under disjoint union.
    Given covers of G and H, their disjoint union covers G ⊔ H.

    Proof: For any covers coverG of G and coverH of H, the combined cover
    coverG.combine coverH covers G ⊔ H with total weight = coverG.weight + coverH.weight.
    Taking infima: inf(G⊔H) ≤ inf(G) + inf(H). -/
theorem fractionalCliqueCoverNumber_sub_add {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [Nonempty (FractionalCliqueCover G)] [Nonempty (FractionalCliqueCover H)] :
    fractionalCliqueCoverNumber (disjointUnion G H) ≤
    fractionalCliqueCoverNumber G + fractionalCliqueCoverNumber H := by
  unfold fractionalCliqueCoverNumber
  -- For any coverG and coverH, the combined cover has weight = coverG.weight + coverH.weight
  -- So inf(G⊔H) ≤ coverG.weight + coverH.weight for any pair (coverG, coverH)
  -- Taking infima on both sides: inf(G⊔H) ≤ inf(G) + inf(H)
  have hbdd : BddBelow (Set.range (fun c : FractionalCliqueCover (disjointUnion G H) =>
      c.totalWeight)) := by
    use 0
    intro _ ⟨cover, hcover⟩
    rw [← hcover]
    exact cover.totalWeight_nonneg
  -- For any pair (coverG, coverH), we have inf(G⊔H) ≤ coverG.weight + coverH.weight
  have hpair : ∀ (coverG : FractionalCliqueCover G) (coverH : FractionalCliqueCover H),
      (⨅ c : FractionalCliqueCover (disjointUnion G H), c.totalWeight) ≤
      coverG.totalWeight + coverH.totalWeight := by
    intro coverG coverH
    calc ⨅ c : FractionalCliqueCover (disjointUnion G H), c.totalWeight
      ≤ (coverG.combine coverH).totalWeight := ciInf_le hbdd (coverG.combine coverH)
      _ ≤ coverG.totalWeight + coverH.totalWeight := FractionalCliqueCover.combine_totalWeight _ _
  -- Now take infimum on the RHS using le_ciInf_add_ciInf
  exact le_ciInf_add_ciInf hpair

/-! ### Sub-multiplicativity under strong product

For the strong product G ⊠ H:
- Cliques in G ⊠ H are exactly products C × D where C is a clique in G and D is a clique in H
- Given covers of G and H, we multiply them to get a cover of G ⊠ H
- Each vertex (v, w) is covered by products C_i × D_j where v ∈ C_i and w ∈ D_j
- Weight on (v, w) = (Σ_{v∈C_i} w_i) · (Σ_{w∈D_j} u_j) ≥ 1 · 1 = 1
- Total weight = (Σ_i w_i) · (Σ_j u_j) = coverG.weight · coverH.weight -/

/-- The Cartesian product of two finite sets -/
def finsetProduct {V W : Type*} (C : Finset V) (D : Finset W) : Finset (V × W) :=
  C ×ˢ D

/-- The product of cliques in the strong product is a clique -/
theorem finsetProduct_isClique {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    {C : Finset V} {D : Finset W}
    (hC : G.IsClique C) (hD : H.IsClique D) :
    (ShannonCapacity.strongProduct G H).IsClique (finsetProduct C D) := by
  rw [isClique_iff, Set.Pairwise]
  intro p hp q hq hne
  simp only [finsetProduct, Finset.coe_product, Set.mem_prod] at hp hq
  simp only [ShannonCapacity.strongProduct]
  refine ⟨hne, ?_, ?_⟩
  · -- Either p.1 = q.1 or G.Adj p.1 q.1
    by_cases h : p.1 = q.1
    · exact Or.inl h
    · right
      rw [isClique_iff, Set.Pairwise] at hC
      exact hC hp.1 hq.1 h
  · -- Either p.2 = q.2 or H.Adj p.2 q.2
    by_cases h : p.2 = q.2
    · exact Or.inl h
    · right
      rw [isClique_iff, Set.Pairwise] at hD
      exact hD hp.2 hq.2 h

/-- Product of fractional clique covers for strong product G ⊠ H -/
noncomputable def FractionalCliqueCover.product {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (coverG : FractionalCliqueCover G) (coverH : FractionalCliqueCover H) :
    FractionalCliqueCover (ShannonCapacity.strongProduct G H) where
  cliques := (coverG.cliques ×ˢ coverH.cliques).image (fun p => finsetProduct p.1 p.2)
  weights := fun C =>
    if h : ∃ p ∈ coverG.cliques ×ˢ coverH.cliques, finsetProduct p.1 p.2 = C then
      coverG.weights (Classical.choose h).1 * coverH.weights (Classical.choose h).2
    else 0
  isClique := by
    intro C hC
    simp only [Finset.mem_image, Finset.mem_product] at hC
    obtain ⟨⟨CG, CH⟩, ⟨hCG, hCH⟩, rfl⟩ := hC
    exact finsetProduct_isClique (coverG.isClique CG hCG) (coverH.isClique CH hCH)
  nonneg := by
    intro C _
    split_ifs with h
    · let p := Classical.choose h
      have hspec := Classical.choose_spec h
      rw [Finset.mem_product] at hspec
      have hmem1 : p.1 ∈ coverG.cliques := hspec.1.1
      have hmem2 : p.2 ∈ coverH.cliques := hspec.1.2
      exact mul_nonneg (coverG.nonneg _ hmem1) (coverH.nonneg _ hmem2)
    · exact le_refl 0
  covers := by
    -- For each vertex (v, w), the covering weight is:
    -- Σ_{C_i × D_j : v ∈ C_i, w ∈ D_j} w_i * u_j ≥ 1
    -- This follows from (Σ_{v∈C} w_C) * (Σ_{w∈D} u_D) ≥ 1 * 1 = 1
    intro ⟨v, w⟩
    -- Key property: (v, w) ∈ C ×ˢ D ↔ v ∈ C ∧ w ∈ D
    have mem_finsetProduct : ∀ (C : Finset V) (D : Finset W),
        (v, w) ∈ finsetProduct C D ↔ v ∈ C ∧ w ∈ D := by
      intro C D; simp only [finsetProduct, Finset.mem_product]
    -- The covering properties of G and H
    have hcoverG := coverG.covers v
    have hcoverH := coverH.covers w
    -- The product cliques and weight function
    let productCliques := (coverG.cliques ×ˢ coverH.cliques).image (fun p => finsetProduct p.1 p.2)
    let wts : Finset (V × W) → ℝ := fun C =>
      if h : ∃ p ∈ coverG.cliques ×ˢ coverH.cliques, finsetProduct p.1 p.2 = C then
        coverG.weights (Classical.choose h).1 * coverH.weights (Classical.choose h).2
      else 0
    -- The filtered pairs: (CG, CH) with v ∈ CG and w ∈ CH
    let pairsVW := (coverG.cliques.filter (v ∈ ·)) ×ˢ (coverH.cliques.filter (w ∈ ·))
    -- Strategy: show filtered sum ≥ product of sums ≥ 1*1 = 1
    -- The sum over pairs factors via sum_product
    have hsum_factor : pairsVW.sum (fun p => coverG.weights p.1 * coverH.weights p.2) =
        (coverG.cliques.filter (v ∈ ·)).sum coverG.weights *
        (coverH.cliques.filter (w ∈ ·)).sum coverH.weights := by
      rw [Finset.sum_mul_sum, Finset.sum_product]
    -- pairsVW is a subset of the full product of cliques
    have hpairs_subset : pairsVW ⊆ coverG.cliques ×ˢ coverH.cliques := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, pairsVW] at hp ⊢
      exact ⟨hp.1.1, hp.2.1⟩
    -- Key insight: finsetProduct is injective on pairs of non-empty sets.
    -- For cliques containing (v, w), both components must be non-empty.
    -- The proof uses:
    -- 1. finsetProduct injectivity on non-empty pairs
    -- 2. sum_image to convert image sum to source sum
    -- 3. Weight correspondence via Classical.choose uniqueness
    -- 4. sum_mul_sum and sum_product for factorization
    --
    -- The calculation chain:
    -- 1 ≤ (Σ_{v∈CG} wG) * (Σ_{w∈CH} wH)              [covering properties]
    --   = pairsVW.sum (wG * wH)                       [sum_mul_sum, sum_product]
    --   ≤ (productCliques.filter ((v,w)∈·)).sum wts  [sum over image with weight corr]
    calc (1 : ℝ)
      = 1 * 1 := by ring
      _ ≤ (coverG.cliques.filter (v ∈ ·)).sum coverG.weights *
        (coverH.cliques.filter (w ∈ ·)).sum coverH.weights := by
          apply mul_le_mul hcoverG hcoverH
          · exact zero_le_one
          · exact le_trans zero_le_one hcoverG
      _ = pairsVW.sum (fun p => coverG.weights p.1 * coverH.weights p.2) := hsum_factor.symm
      _ ≤ (productCliques.filter ((v, w) ∈ ·)).sum wts := by
          -- Image of pairsVW lands in productCliques.filter ((v,w) ∈ ·)
          have himage_subset : pairsVW.image (fun p => finsetProduct p.1 p.2) ⊆
              productCliques.filter ((v, w) ∈ ·) := by
            intro C hC
            simp only [Finset.mem_image] at hC
            obtain ⟨p, hp, rfl⟩ := hC
            simp only [Finset.mem_filter, pairsVW, Finset.mem_product, Finset.mem_filter] at hp ⊢
            constructor
            · simp only [productCliques, Finset.mem_image, Finset.mem_product]
              exact ⟨p, ⟨hp.1.1, hp.2.1⟩, rfl⟩
            · rw [mem_finsetProduct]
              exact ⟨hp.1.2, hp.2.2⟩
          -- finsetProduct is injective on pairsVW
          have hinj : ∀ p ∈ pairsVW, ∀ q ∈ pairsVW,
              finsetProduct p.1 p.2 = finsetProduct q.1 q.2 → p = q := by
            intro p hp q hq heq
            rw [Finset.mem_product] at hp hq
            simp only [Finset.mem_filter] at hp hq
            obtain ⟨⟨hp1_mem, hp1_v⟩, hp2_mem, hp2_w⟩ := hp
            obtain ⟨⟨hq1_mem, hq1_v⟩, hq2_mem, hq2_w⟩ := hq
            simp only [finsetProduct] at heq
            -- p.1 and p.2 are non-empty (contain v and w respectively)
            ext1
            · ext x
              have h1 : (x, w) ∈ p.1 ×ˢ p.2 ↔ (x, w) ∈ q.1 ×ˢ q.2 := by rw [heq]
              simp only [Finset.mem_product] at h1
              exact ⟨fun hx => (h1.mp ⟨hx, hp2_w⟩).1, fun hx => (h1.mpr ⟨hx, hq2_w⟩).1⟩
            · ext y
              have h1 : (v, y) ∈ p.1 ×ˢ p.2 ↔ (v, y) ∈ q.1 ×ˢ q.2 := by rw [heq]
              simp only [Finset.mem_product] at h1
              exact ⟨fun hy => (h1.mp ⟨hp1_v, hy⟩).2, fun hy => (h1.mpr ⟨hq1_v, hy⟩).2⟩
          -- Weight correspondence: for p ∈ pairsVW, wts(finsetProduct p.1 p.2) = wG(p.1) * wH(p.2)
          have hweight_corr :
              ∀ p ∈ pairsVW,
                wts (finsetProduct p.1 p.2) =
                  coverG.weights p.1 * coverH.weights p.2 := by
            intro p hp
            simp only [wts]
            rw [Finset.mem_product] at hp
            simp only [Finset.mem_filter] at hp
            obtain ⟨⟨hp1_mem, hp1_v⟩, hp2_mem, hp2_w⟩ := hp
            have hex :
                ∃ r ∈ coverG.cliques ×ˢ coverH.cliques,
                  finsetProduct r.1 r.2 = finsetProduct p.1 p.2 := by
              exact ⟨p, Finset.mem_product.mpr ⟨hp1_mem, hp2_mem⟩, rfl⟩
            rw [dif_pos hex]
            -- Show Classical.choose hex = p by injectivity
            have hr := Classical.choose_spec hex
            rw [Finset.mem_product] at hr
            -- hr.2 : finsetProduct (Classical.choose hex).1 (Classical.choose hex).2
            --   = finsetProduct p.1 p.2
            have hr_eq : (Classical.choose hex).1 ×ˢ (Classical.choose hex).2 = p.1 ×ˢ p.2 := by
              simp only [finsetProduct] at hr; exact hr.2
            have hvw_p : (v, w) ∈ p.1 ×ˢ p.2 := Finset.mem_product.mpr ⟨hp1_v, hp2_w⟩
            have hvw_r : (v, w) ∈ (Classical.choose hex).1 ×ˢ (Classical.choose hex).2 := by
              rw [hr_eq]; exact hvw_p
            rw [Finset.mem_product] at hvw_r
            have heq1 : (Classical.choose hex).1 = p.1 := by
              ext x
              have h1 :
                  (x, w) ∈ (Classical.choose hex).1 ×ˢ (Classical.choose hex).2 ↔
                    (x, w) ∈ p.1 ×ˢ p.2 := by
                rw [hr_eq]
              rw [Finset.mem_product, Finset.mem_product] at h1
              constructor
              · intro hx; exact (h1.mp ⟨hx, hvw_r.2⟩).1
              · intro hx; exact (h1.mpr ⟨hx, hp2_w⟩).1
            have heq2 : (Classical.choose hex).2 = p.2 := by
              ext y
              have h1 :
                  (v, y) ∈ (Classical.choose hex).1 ×ˢ (Classical.choose hex).2 ↔
                    (v, y) ∈ p.1 ×ˢ p.2 := by
                rw [hr_eq]
              rw [Finset.mem_product, Finset.mem_product] at h1
              constructor
              · intro hy; exact (h1.mp ⟨hvw_r.1, hy⟩).2
              · intro hy; exact (h1.mpr ⟨hp1_v, hy⟩).2
            rw [heq1, heq2]
          -- Use sum_image and sum_le_sum_of_subset_of_nonneg
          calc pairsVW.sum (fun p => coverG.weights p.1 * coverH.weights p.2)
            = (pairsVW.image (fun p => finsetProduct p.1 p.2)).sum wts := by
                rw [Finset.sum_image hinj]
                exact Finset.sum_congr rfl (fun p hp => (hweight_corr p hp).symm)
            _ ≤ (productCliques.filter ((v, w) ∈ ·)).sum wts := by
                apply Finset.sum_le_sum_of_subset_of_nonneg himage_subset
                intro C hC _
                dsimp only [wts]
                split_ifs with hex
                · apply mul_nonneg
                  · apply coverG.nonneg
                    exact (Finset.mem_product.mp (Classical.choose_spec hex).1).1
                  · apply coverH.nonneg
                    exact (Finset.mem_product.mp (Classical.choose_spec hex).1).2
                · rfl

/-- The product cover has total weight at most the product of individual weights.
    Note: Equality holds when finsetProduct is injective on the clique pairs, which is true
    when all cliques are non-empty. With empty cliques, multiple pairs could map to ∅,
    but since we use Classical.choose, we only count one weight per product clique.
    This gives us ≤, which is sufficient for the sub-multiplicativity theorem. -/
theorem FractionalCliqueCover.product_totalWeight_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (coverG : FractionalCliqueCover G) (coverH : FractionalCliqueCover H) :
    (coverG.product coverH).totalWeight ≤ coverG.totalWeight * coverH.totalWeight := by
  unfold FractionalCliqueCover.totalWeight FractionalCliqueCover.product
  simp only
  let pairs := coverG.cliques ×ˢ coverH.cliques
  let pairWeights : Finset V × Finset W → ℝ := fun p => coverG.weights p.1 * coverH.weights p.2
  let productCliques := pairs.image (fun p => finsetProduct p.1 p.2)
  -- For each C in productCliques, pick a representative pair
  let choose_rep : Finset (V × W) → Finset V × Finset W := fun C =>
    if h : ∃ p ∈ pairs, finsetProduct p.1 p.2 = C then Classical.choose h else (∅, ∅)
  -- The weight function equals pairWeights of the chosen representative
  have hwts_eq : ∀ C ∈ productCliques,
      (if h : ∃ p ∈ pairs, finsetProduct p.1 p.2 = C then
        coverG.weights (Classical.choose h).1 * coverH.weights (Classical.choose h).2
      else 0) = pairWeights (choose_rep C) := by
    intro C hC
    simp only [choose_rep, pairWeights]
    simp only [productCliques, Finset.mem_image] at hC
    obtain ⟨p, hp, rfl⟩ := hC
    have hex : ∃ q ∈ pairs, finsetProduct q.1 q.2 = finsetProduct p.1 p.2 := ⟨p, hp, rfl⟩
    rw [dif_pos hex, dif_pos hex]
  -- The representatives are in pairs
  have hrep_mem : ∀ C ∈ productCliques, choose_rep C ∈ pairs := by
    intro C hC
    simp only [choose_rep]
    simp only [productCliques, Finset.mem_image] at hC
    obtain ⟨p, hp, rfl⟩ := hC
    have hex : ∃ q ∈ pairs, finsetProduct q.1 q.2 = finsetProduct p.1 p.2 := ⟨p, hp, rfl⟩
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).1
  -- The representative mapping is injective on productCliques
  have hrep_inj : Set.InjOn choose_rep productCliques := by
    intro C₁ hC₁ C₂ hC₂ heq
    simp only [choose_rep] at heq
    rw [Finset.mem_coe, Finset.mem_image] at hC₁ hC₂
    obtain ⟨p₁, hp₁, rfl⟩ := hC₁
    obtain ⟨p₂, hp₂, rfl⟩ := hC₂
    have hex₁ : ∃ q ∈ pairs, finsetProduct q.1 q.2 = finsetProduct p₁.1 p₁.2 := ⟨p₁, hp₁, rfl⟩
    have hex₂ : ∃ q ∈ pairs, finsetProduct q.1 q.2 = finsetProduct p₂.1 p₂.2 := ⟨p₂, hp₂, rfl⟩
    rw [dif_pos hex₁, dif_pos hex₂] at heq
    have h1 := (Classical.choose_spec hex₁).2
    have h2 := (Classical.choose_spec hex₂).2
    rw [heq] at h1
    exact h1.symm.trans h2
  -- The image of representatives is a subset of pairs
  have himg_subset : productCliques.image choose_rep ⊆ pairs := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨C, hC, rfl⟩ := hp
    exact hrep_mem C hC
  -- Non-negativity of pair weights
  have hpair_nonneg : ∀ p ∈ pairs, 0 ≤ pairWeights p := by
    intro p hp
    simp only [pairWeights]
    rw [Finset.mem_product] at hp
    exact mul_nonneg (coverG.nonneg _ hp.1) (coverH.nonneg _ hp.2)
  -- Sum over productCliques = sum over representatives ≤ sum over pairs
  have hsum_le : productCliques.sum (fun C =>
      if h : ∃ p ∈ pairs, finsetProduct p.1 p.2 = C then
        coverG.weights (Classical.choose h).1 * coverH.weights (Classical.choose h).2
      else 0) ≤ pairs.sum pairWeights := by
    calc productCliques.sum _ = productCliques.sum (pairWeights ∘ choose_rep) := by
          apply Finset.sum_congr rfl
          intro C hC
          exact hwts_eq C hC
      _ = (productCliques.image choose_rep).sum pairWeights := by
          simp only [Function.comp, pairWeights]
          rw [Finset.sum_image hrep_inj]
      _ ≤ pairs.sum pairWeights := by
          apply Finset.sum_le_sum_of_subset_of_nonneg himg_subset
          intro p hp _
          exact hpair_nonneg p hp
  -- The sum over pairs factors
  have hfactor : pairs.sum pairWeights =
      coverG.cliques.sum coverG.weights * coverH.cliques.sum coverH.weights := by
    simp only [pairWeights, pairs]
    rw [Finset.sum_product]
    rw [Finset.sum_mul_sum]
  calc productCliques.sum _ ≤ pairs.sum pairWeights := hsum_le
    _ = coverG.cliques.sum coverG.weights * coverH.cliques.sum coverH.weights := hfactor

/-- χ̄_f is sub-multiplicative under strong product.
    Given covers of G and H, their product covers G ⊠ H.
    Key fact: cliques in G ⊠ H are products of cliques in G and H. -/
theorem fractionalCliqueCoverNumber_sub_mul {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [Nonempty (FractionalCliqueCover G)] [Nonempty (FractionalCliqueCover H)] :
    fractionalCliqueCoverNumber (ShannonCapacity.strongProduct G H) ≤
    fractionalCliqueCoverNumber G * fractionalCliqueCoverNumber H := by
  unfold fractionalCliqueCoverNumber
  have hbdd :
      BddBelow
        (Set.range
          (fun c : FractionalCliqueCover (ShannonCapacity.strongProduct G H) =>
            c.totalWeight)) := by
    use 0
    intro _ ⟨cover, hcover⟩
    rw [← hcover]
    exact cover.totalWeight_nonneg
  have hpair : ∀ (coverG : FractionalCliqueCover G) (coverH : FractionalCliqueCover H),
      (⨅ c : FractionalCliqueCover (ShannonCapacity.strongProduct G H), c.totalWeight) ≤
      coverG.totalWeight * coverH.totalWeight := by
    intro coverG coverH
    calc (⨅ c : FractionalCliqueCover (ShannonCapacity.strongProduct G H), c.totalWeight)
        ≤ (coverG.product coverH).totalWeight := ciInf_le hbdd (coverG.product coverH)
      _ ≤ coverG.totalWeight * coverH.totalWeight := by
          exact FractionalCliqueCover.product_totalWeight_le _ _
  -- For non-negative reals: if a ≤ f(x) * g(y) for all x, y, then a ≤ inf f * inf g
  -- Step 1: Show the LHS ≤ inf over pairs of the product of weights
  let a := ⨅ c : FractionalCliqueCover (ShannonCapacity.strongProduct G H), c.totalWeight
  have hle_pair : a ≤ ⨅ (p : FractionalCliqueCover G × FractionalCliqueCover H),
      p.1.totalWeight * p.2.totalWeight := by
    apply le_ciInf
    intro ⟨coverG, coverH⟩
    exact hpair coverG coverH
  -- Step 2: Factor the inf over pairs into product of infs using Real.iInf_mul_of_nonneg
  -- First, we need BddBelow for the individual infima
  have hbddG : BddBelow (Set.range (fun c : FractionalCliqueCover G => c.totalWeight)) := by
    use 0
    intro _ ⟨cover, hcover⟩
    rw [← hcover]
    exact cover.totalWeight_nonneg
  have hbddH : BddBelow (Set.range (fun c : FractionalCliqueCover H => c.totalWeight)) := by
    use 0
    intro _ ⟨cover, hcover⟩
    rw [← hcover]
    exact cover.totalWeight_nonneg
  -- The inf over pairs equals (inf_G w_G) * (inf_H w_H)
  -- Key lemmas used:
  -- 1. iInf_prod: ⨅ p, f p = ⨅ i, ⨅ j, f (i, j)
  -- 2. Real.mul_iInf_of_nonneg: c * (⨅ i, f i) = ⨅ i, c * f i  (when c ≥ 0)
  -- 3. Real.iInf_mul_of_nonneg: (⨅ i, f i) * c = ⨅ i, f i * c  (when c ≥ 0)
  -- The proof transforms:
  --   ⨅ p, p.1.weight * p.2.weight
  -- = ⨅ i, ⨅ j, i.weight * j.weight          (by iInf_prod)
  -- = ⨅ i, i.weight * (⨅ j, j.weight)        (by Real.mul_iInf_of_nonneg, i.weight ≥ 0)
  -- = (⨅ i, i.weight) * (⨅ j, j.weight)      (by Real.iInf_mul_of_nonneg, inf_H ≥ 0)
  have hfactor : (⨅ (p : FractionalCliqueCover G × FractionalCliqueCover H),
      p.1.totalWeight * p.2.totalWeight) =
      (⨅ c : FractionalCliqueCover G, c.totalWeight) *
      (⨅ c : FractionalCliqueCover H, c.totalWeight) := by
    apply le_antisymm
    · -- Direction (≤): ⨅ p, p.1.w * p.2.w ≤ (⨅ cG) * (⨅ cH)
      -- For any ε > 0, find covers close to infima, get pair product close to inf_G * inf_H
      apply le_of_forall_pos_le_add
      intro ε hε
      -- BddBelow for pairs
      have hpair_bdd : BddBelow (Set.range fun p : FractionalCliqueCover G ×
          FractionalCliqueCover H => p.1.totalWeight * p.2.totalWeight) := by
        use 0; intro _ ⟨⟨c1, c2⟩, hc⟩; rw [← hc]
        exact mul_nonneg c1.totalWeight_nonneg c2.totalWeight_nonneg
      -- Infima are nonnegative
      have hinfG_nonneg : 0 ≤ ⨅ c : FractionalCliqueCover G, c.totalWeight := by
        apply le_ciInf; intro c; exact c.totalWeight_nonneg
      have hinfH_nonneg : 0 ≤ ⨅ c : FractionalCliqueCover H, c.totalWeight := by
        apply le_ciInf; intro c; exact c.totalWeight_nonneg
      -- Choose δ small enough
      let inf_G := ⨅ c : FractionalCliqueCover G, c.totalWeight
      let inf_H := ⨅ c : FractionalCliqueCover H, c.totalWeight
      -- δ such that (inf_G + δ)(inf_H + δ) ≤ inf_G * inf_H + ε
      -- Expanding: inf_G*inf_H + δ*inf_H + δ*inf_G + δ² ≤ inf_G*inf_H + ε
      -- So need: δ*(inf_G + inf_H + δ) ≤ ε
      -- Take δ = min(1, ε / (inf_G + inf_H + 2))
      let M := inf_G + inf_H + 2
      have hM_pos : 0 < M := by linarith
      let δ := min 1 (ε / M)
      have hδ_pos : 0 < δ := lt_min one_pos (div_pos hε hM_pos)
      have hδ_le_one : δ ≤ 1 := min_le_left _ _
      have hδ_le_eps_M : δ ≤ ε / M := min_le_right _ _
      -- Find covers close to infima
      have hG_lt : inf_G < inf_G + δ := by linarith
      have hH_lt : inf_H < inf_H + δ := by linarith
      obtain ⟨coverG, hcoverG⟩ := exists_lt_of_ciInf_lt hG_lt
      obtain ⟨coverH, hcoverH⟩ := exists_lt_of_ciInf_lt hH_lt
      -- Bound the infimum using this pair
      have hpair_le : ⨅ (p : FractionalCliqueCover G × FractionalCliqueCover H),
          p.1.totalWeight * p.2.totalWeight ≤ coverG.totalWeight * coverH.totalWeight :=
        ciInf_le hpair_bdd ⟨coverG, coverH⟩
      -- Bound coverG.w * coverH.w using mul_lt_mul''
      have hcoverG_nonneg : 0 ≤ coverG.totalWeight := coverG.totalWeight_nonneg
      have hcoverH_nonneg : 0 ≤ coverH.totalWeight := coverH.totalWeight_nonneg
      have hprod_lt : coverG.totalWeight * coverH.totalWeight < (inf_G + δ) * (inf_H + δ) :=
        mul_lt_mul'' hcoverG hcoverH hcoverG_nonneg hcoverH_nonneg
      -- Expand (inf_G + δ)(inf_H + δ) and bound error term
      have hexpand : (inf_G + δ) * (inf_H + δ) = inf_G * inf_H + δ * inf_H + δ * inf_G + δ * δ := by
        ring
      have herror : δ * inf_H + δ * inf_G + δ * δ ≤ ε := by
        have h1 : δ * inf_H + δ * inf_G + δ * δ ≤ δ * (inf_G + inf_H + 1) := by
          have : δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ_le_one (le_of_lt hδ_pos)
          linarith
        have h2 : δ * (inf_G + inf_H + 1) ≤ δ * M := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ_pos)
          linarith
        have h3 : δ * M ≤ ε := by
          calc δ * M ≤ (ε / M) * M := mul_le_mul_of_nonneg_right hδ_le_eps_M (le_of_lt hM_pos)
            _ = ε := div_mul_cancel₀ ε (ne_of_gt hM_pos)
        linarith
      calc (⨅ (p : FractionalCliqueCover G × FractionalCliqueCover H),
              p.1.totalWeight * p.2.totalWeight)
          ≤ coverG.totalWeight * coverH.totalWeight := hpair_le
        _ ≤ (inf_G + δ) * (inf_H + δ) := le_of_lt hprod_lt
        _ = inf_G * inf_H + δ * inf_H + δ * inf_G + δ * δ := hexpand
        _ ≤ inf_G * inf_H + ε := by linarith [herror]
    · -- Direction (≥): (⨅ cG) * (⨅ cH) ≤ ⨅ p, p.1.w * p.2.w
      -- For all pairs p, we have (⨅ cG) ≤ p.1.w and (⨅ cH) ≤ p.2.w
      -- Since all are nonnegative, the product is preserved
      apply le_ciInf
      intro ⟨coverG, coverH⟩
      have hinfG : ⨅ c : FractionalCliqueCover G, c.totalWeight ≤ coverG.totalWeight :=
        ciInf_le hbddG coverG
      have hinfH : ⨅ c : FractionalCliqueCover H, c.totalWeight ≤ coverH.totalWeight :=
        ciInf_le hbddH coverH
      have hinfG_nonneg : 0 ≤ ⨅ c : FractionalCliqueCover G, c.totalWeight := by
        apply le_ciInf; intro c; exact c.totalWeight_nonneg
      have hinfH_nonneg : 0 ≤ ⨅ c : FractionalCliqueCover H, c.totalWeight := by
        apply le_ciInf; intro c; exact c.totalWeight_nonneg
      exact mul_le_mul hinfG hinfH hinfH_nonneg (le_trans hinfG_nonneg hinfG)
  rw [hfactor] at hle_pair
  exact hle_pair

/-! ### Fractional independence number (LP dual)

A fractional independent set assigns non-negative weights to vertices such that
the total weight on any clique is at most 1. The fractional independence number
α_f(G) is the supremum of total vertex weights.

By LP duality: χ̄_f(G) = α_f(G) for finite graphs. -/

/-- A fractional independent set assigns non-negative weights to vertices such that
    the total weight on any clique is at most 1. -/
structure FractionalIndependentSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  /-- Weight assigned to each vertex -/
  weights : V → ℝ
  /-- Weights are non-negative -/
  nonneg : ∀ v, 0 ≤ weights v
  /-- Total weight on any clique is at most 1 -/
  clique_bound : ∀ C : Finset V, G.IsClique C → C.sum weights ≤ 1

/-- The total weight of a fractional independent set -/
def FractionalIndependentSet.totalWeight {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (fi : FractionalIndependentSet G) : ℝ :=
  Finset.univ.sum fi.weights

/-- The total weight of a fractional independent set is at most |V| since each vertex
    weight is ≤ 1 (because singletons are cliques). -/
theorem FractionalIndependentSet.totalWeight_le_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (fi : FractionalIndependentSet G) :
    fi.totalWeight ≤ Fintype.card V := by
  unfold totalWeight
  calc Finset.univ.sum fi.weights
    ≤ Finset.univ.sum (fun _ => (1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro v _
        -- Singletons are cliques, so fi.weights v ≤ 1
        have hclique : G.IsClique (({v} : Finset V) : Set V) := by
          rw [isClique_iff, Set.Pairwise]
          intro x hx y hy hxy
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
          rw [hx, hy] at hxy
          exact (hxy rfl).elim
        have hbound := fi.clique_bound {v} hclique
        simp only [Finset.sum_singleton] at hbound
        exact hbound
    _ = Fintype.card V := by simp [Finset.card_univ]

/-- Every finite graph has at least one fractional independent set: the zero assignment. -/
theorem FractionalIndependentSet.exists_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Nonempty (FractionalIndependentSet G) := by
  refine ⟨⟨fun _ => 0, fun _ => le_refl 0, ?_⟩⟩
  intro C _
  simp only [Finset.sum_const_zero]
  norm_num

/-- The fractional independence number α_f(G) is the supremum of total weights
    over all fractional independent sets. -/
noncomputable def fractionalIndependenceNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  ⨆ (fi : FractionalIndependentSet G), fi.totalWeight

/-- The fractional independence number is non-negative -/
theorem fractionalIndependenceNumber_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : 0 ≤ fractionalIndependenceNumber G := by
  -- The zero fractional independent set has total weight 0
  -- Since sup ≥ 0, and 0 ≤ 0, we get sup ≥ 0
  unfold fractionalIndependenceNumber
  have hne := FractionalIndependentSet.exists_zero G
  have hbdd : BddAbove (Set.range (fun fi : FractionalIndependentSet G => fi.totalWeight)) := by
    use Fintype.card V
    intro _ ⟨fi, hfi⟩
    rw [← hfi]
    exact fi.totalWeight_le_card
  -- The zero fi has weight 0, so sup ≥ 0
  have hzero : ∃ fi : FractionalIndependentSet G, fi.totalWeight = 0 := by
    obtain ⟨fi⟩ := hne
    use ⟨fun _ => 0, fun _ => le_refl 0, fun C _ => by simp⟩
    simp [FractionalIndependentSet.totalWeight]
  obtain ⟨fi₀, hfi₀⟩ := hzero
  calc 0 = fi₀.totalWeight := hfi₀.symm
    _ ≤ ⨆ fi : FractionalIndependentSet G, fi.totalWeight := le_ciSup hbdd fi₀

/-! ### LP duality: χ̄_f(G) = α_f(G) -/

/-- For any fractional independent set and clique cover, the independent set weight
    is at most the cover weight. This is the key lemma for weak duality. -/
theorem FractionalIndependentSet.weight_le_cover_weight {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (fi : FractionalIndependentSet G) (cover : FractionalCliqueCover G) :
    fi.totalWeight ≤ cover.totalWeight := by
  -- The proof uses the standard LP duality argument:
  -- Σ_v x(v) ≤ Σ_v x(v) · (Σ_{C∋v} w(C))
  --   [cover property: Σ_{C∋v} w(C) ≥ 1]
  --          = Σ_C w(C) · (Σ_{v∈C} x(v))  [rearranging double sum]
  --          ≤ Σ_C w(C) · 1               [clique bound: Σ_{v∈C} x(v) ≤ 1]
  --          = Σ_C w(C)
  unfold totalWeight FractionalCliqueCover.totalWeight
  -- Step 1: Σ_v x(v) ≤ Σ_v x(v) · (Σ_{C∋v} w(C)) since Σ_{C∋v} w(C) ≥ 1
  have hstep1 :
      Finset.univ.sum fi.weights ≤
        Finset.univ.sum
          (fun v => fi.weights v * (cover.cliques.filter (v ∈ ·)).sum cover.weights) := by
    apply Finset.sum_le_sum
    intro v _
    have hcover := cover.covers v
    have hnonneg := fi.nonneg v
    calc fi.weights v = fi.weights v * 1 := by ring
      _ ≤ fi.weights v * (cover.cliques.filter (v ∈ ·)).sum cover.weights := by
          apply mul_le_mul_of_nonneg_left hcover hnonneg
  -- Step 2: Rearrange double sum
  -- Σ_v x(v) · (Σ_{C∋v} w(C)) = Σ_C w(C) · (Σ_{v∈C} x(v))
  -- This is a standard double sum rearrangement via Finset.sum_comm'
  -- Both sides count pairs (v, C) with v ∈ C, weighted by x(v) * w(C)
  have hstep2 : Finset.univ.sum
      (fun v => fi.weights v * (cover.cliques.filter (v ∈ ·)).sum cover.weights) =
      cover.cliques.sum (fun C => cover.weights C * C.sum fi.weights) := by
    -- Expand: LHS = Σ_v Σ_{C:v∈C} x(v) * w(C)
    --         RHS = Σ_C Σ_{v∈C} w(C) * x(v) = Σ_C Σ_{v∈C} x(v) * w(C)
    -- Use Finset.sum_comm' to swap order of summation
    calc Finset.univ.sum (fun v => fi.weights v *
          (cover.cliques.filter (v ∈ ·)).sum cover.weights)
      = Finset.univ.sum (fun v =>
          (cover.cliques.filter (v ∈ ·)).sum (fun C => fi.weights v * cover.weights C)) := by
          congr 1; ext v; rw [Finset.mul_sum]
      _ = cover.cliques.sum (fun C => C.sum (fun v => fi.weights v * cover.weights C)) := by
          apply Finset.sum_comm'
          intro v C
          simp only [Finset.mem_univ, Finset.mem_filter, true_and]
          exact And.comm
      _ = cover.cliques.sum (fun C => cover.weights C * C.sum fi.weights) := by
          congr 1; ext C
          -- ∑ v ∈ C, fi.weights v * cover.weights C = cover.weights C * ∑ v ∈ C, fi.weights v
          -- Use Finset.sum_mul: (∑ i, f i) * a = ∑ i, f i * a
          -- which is ∑ i, f i * a = (∑ i, f i) * a when reversed
          have h := Finset.sum_mul C fi.weights (cover.weights C)
          -- h : (∑ v ∈ C, fi.weights v) * cover.weights C = ∑ v ∈ C, fi.weights v * cover.weights C
          rw [← h, mul_comm]
  -- Step 3: Σ_C w(C) · (Σ_{v∈C} x(v)) ≤ Σ_C w(C) · 1 since Σ_{v∈C} x(v) ≤ 1
  have hstep3 : cover.cliques.sum (fun C => cover.weights C * C.sum fi.weights) ≤
      cover.cliques.sum cover.weights := by
    apply Finset.sum_le_sum
    intro C hC
    have hclique := cover.isClique C hC
    have hbound := fi.clique_bound C hclique
    have hwnonneg := cover.nonneg C hC
    calc cover.weights C * C.sum fi.weights
      ≤ cover.weights C * 1 := by apply mul_le_mul_of_nonneg_left hbound hwnonneg
      _ = cover.weights C := by ring
  linarith [hstep1, hstep2, hstep3]

/-- Weak duality: α_f(G) ≤ χ̄_f(G).
    Any fractional independent set and fractional cover satisfy: Σ x(v) ≤ Σ w(C). -/
theorem fractionalIndependenceNumber_le_coverNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Nonempty (FractionalCliqueCover G)] :
    fractionalIndependenceNumber G ≤ fractionalCliqueCoverNumber G := by
  unfold fractionalIndependenceNumber fractionalCliqueCoverNumber
  -- sup_fi fi.weight ≤ inf_cover cover.weight
  -- For any fi and cover: fi.weight ≤ cover.weight
  -- So sup_fi fi.weight ≤ cover.weight for any cover
  -- Taking inf: sup_fi fi.weight ≤ inf_cover cover.weight
  have hne : Nonempty (FractionalIndependentSet G) := FractionalIndependentSet.exists_zero G
  apply ciSup_le
  intro fi
  apply le_ciInf
  intro cover
  exact fi.weight_le_cover_weight cover


/-- Helper: Convert LP packing solution to FractionalIndependentSet.
Given x : Fin n → ℝ satisfying the packing constraints via matrix A,
construct a FractionalIndependentSet with the same total weight. -/
noncomputable def FractionalIndependentSet.ofLPPacking {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (vertexEquiv : V ≃ Fin (Fintype.card V))
    (x : Fin (Fintype.card V) → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_clique : ∀ C : Finset V, G.IsClique C →
        (C.sum fun v => x (vertexEquiv v)) ≤ 1) :
    FractionalIndependentSet G where
  weights := fun v => x (vertexEquiv v)
  nonneg := fun v => hx_nonneg (vertexEquiv v)
  clique_bound := fun C hC => hx_clique C hC

/-- The total weight of the LP packing equals the FractionalIndependentSet weight. -/
theorem FractionalIndependentSet.ofLPPacking_totalWeight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (vertexEquiv : V ≃ Fin (Fintype.card V))
    (x : Fin (Fintype.card V) → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_clique : ∀ C : Finset V, G.IsClique C →
        (C.sum fun v => x (vertexEquiv v)) ≤ 1) :
    (FractionalIndependentSet.ofLPPacking G vertexEquiv x hx_nonneg hx_clique).totalWeight =
    Finset.univ.sum x := by
  simp only [FractionalIndependentSet.totalWeight, ofLPPacking]
  rw [← Finset.sum_equiv vertexEquiv.symm]
  · intro _; simp only [Finset.mem_univ]
  · intro i _; simp only [Equiv.apply_symm_apply]

/-- Key lemma: The packing polytope is compact (bounded and closed).
    For any vertex i, the singleton {i} is a clique, so x_i ≤ 1. -/
theorem packing_polytope_bounded {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hA_singletons : ∀ i : Fin n, ∃ j : Fin k, A i j = 1)
    (x : Fin n → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_pack : ∀ j, (A.transpose.mulVec x) j ≤ 1) :
    ∀ i, x i ≤ 1 := by
  intro i
  obtain ⟨j, hj⟩ := hA_singletons i
  have hsum := hx_pack j
  simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct] at hsum
  calc x i = A i j * x i := by rw [hj]; ring
    _ ≤ ∑ i' : Fin n, A i' j * x i' := by
        have : (fun i' => A i' j * x i') i ≤ Finset.univ.sum (fun i' => A i' j * x i') :=
          Finset.single_le_sum (f := fun i' => A i' j * x i')
            (fun i' _ => mul_nonneg (hA_nonneg i' j) (hx_nonneg i'))
            (Finset.mem_univ i)
        exact this
    _ ≤ 1 := hsum

/-- **LP Strong Duality** (finite-dimensional).

This is a fundamental theorem of linear programming: for a primal-dual pair of LPs
where both are feasible and bounded, the optimal values are equal.

For the fractional clique cover / independence LPs:
- Primal: min Σ_C w(C) subject to ∀v: Σ_{C∋v} w(C) ≥ 1, w(C) ≥ 0
- Dual: max Σ_v x(v) subject to ∀C: Σ_{v∈C} x(v) ≤ 1, x(v) ≥ 0

The proof uses LP duality via `ConeProgramming.lp_farkas`:
1. Both primal (covering) and dual (packing) are feasible
2. Both are bounded (weights ≥ 0 and clique constraints give finite bounds)
3. By finite-dimensional LP duality (Farkas' lemma), optimal values are equal

The key insight is that for finite graphs:
- The primal feasible region is a polyhedron in ℝ^(cliques)
- The dual feasible region is a polyhedron in ℝ^(vertices)
- Strong duality follows from closedness of the image cone (`coneImage_isClosed`)

Reference: Scheinerman & Ullman (2011), Fractional Graph Theory, Chapter 2. -/
theorem lp_strong_duality {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Nonempty (FractionalCliqueCover G)] :
    fractionalCliqueCoverNumber G ≤ fractionalIndependenceNumber G := by
  /-
  Proof sketch using LP duality from ConeProgrammingDuality/LP.lean:
  1. Set up the clique-vertex incidence matrix A where A[v,C] = 1 iff v ∈ C
  2. The covering LP is: min 1ᵀw s.t. Aw ≥ 1, w ≥ 0
  3. The packing LP is: max 1ᵀx s.t. Aᵀx ≤ 1, x ≥ 0
  4. Both are feasible: singleton covers and zero independent set
  5. By `lp_farkas`, the system Aw ≥ 1, w ≥ 0 has the same optimal value
     as the dual max 1ᵀx s.t. Aᵀx ≤ 1, x ≥ 0
  The formal connection requires:
  - Enumerating cliques as Fin k for some k (finite since V is finite)
  - Converting FractionalCliqueCover to matrix form
  - Applying lp_farkas from ConeProgrammingDuality/LP.lean
  -/
  -- For any ε > 0, we show inf(cover weights) ≤ sup(independent set weights) + ε
  -- This follows from LP duality: at optimality, complementary slackness gives equality
  unfold fractionalCliqueCoverNumber fractionalIndependenceNumber
  -- Use that both inf and sup are over nonempty sets with bounds
  have hne_cover : Nonempty (FractionalCliqueCover G) := inferInstance
  have hne_fi : Nonempty (FractionalIndependentSet G) := FractionalIndependentSet.exists_zero G
  -- The inf is bounded below by 0
  have hinf_bdd : BddBelow (Set.range (fun c : FractionalCliqueCover G => c.totalWeight)) := by
    use 0
    intro x ⟨c, hc⟩
    rw [← hc]
    exact c.totalWeight_nonneg
  -- The sup is bounded above by |V|
  have hsup_bdd : BddAbove (Set.range (fun fi : FractionalIndependentSet G => fi.totalWeight)) := by
    use Fintype.card V
    intro x ⟨fi, hfi⟩
    rw [← hfi]
    exact fi.totalWeight_le_card
  /-
  LP strong duality for finite-dimensional covering/packing LPs.
  This theorem requires connecting the structural definitions (FractionalCliqueCover,
  FractionalIndependentSet) to the matrix LP formulation and applying LP strong duality.
  The proof uses the closed image cone theorem (coneImage_isClosed) from LP.lean.
  -/
  classical
  -- Step 1: For the trivial case where V is empty
  by_cases hV : IsEmpty V
  · -- With empty V, both inf and sup equal 0
    haveI : IsEmpty V := hV
    have huniv : (Finset.univ : Finset V) = ∅ := Finset.univ_eq_empty
    have hfi_zero : ∀ fi : FractionalIndependentSet G, fi.totalWeight = 0 := by
      intro fi
      simp only [FractionalIndependentSet.totalWeight, huniv, Finset.sum_empty]
    -- The empty cover has weight 0
    let emptycover : FractionalCliqueCover G :=
      { cliques := ∅
        weights := fun _ => 0
        isClique := fun _ h => (Finset.notMem_empty _ h).elim
        nonneg := fun _ h => (Finset.notMem_empty _ h).elim
        covers := fun v => (hV.false v).elim }
    have hinf_le_zero : ⨅ c : FractionalCliqueCover G, c.totalWeight ≤ 0 := by
      apply ciInf_le_of_le hinf_bdd emptycover
      simp only [FractionalCliqueCover.totalWeight]
      -- emptycover.cliques = ∅, so sum is 0
      rfl
    have hsup_zero : ⨆ fi : FractionalIndependentSet G, fi.totalWeight = 0 := by
      apply le_antisymm
      · apply ciSup_le
        intro fi
        rw [hfi_zero fi]
      · let zerofi : FractionalIndependentSet G :=
          { weights := fun _ => 0
            nonneg := fun _ => le_refl 0
            clique_bound := fun _ _ => by simp }
        have hzero : (0 : ℝ) = zerofi.totalWeight := by
          simp only [FractionalIndependentSet.totalWeight, huniv, Finset.sum_empty]
        rw [hzero]
        apply le_ciSup hsup_bdd
    calc ⨅ c : FractionalCliqueCover G, c.totalWeight
      ≤ 0 := hinf_le_zero
      _ = ⨆ fi : FractionalIndependentSet G, fi.totalWeight := hsup_zero.symm
  -- Step 2: For non-empty V, use LP duality
  rw [not_isEmpty_iff] at hV
  haveI : Nonempty V := hV
  -- Enumerate vertices and cliques
  let n := Fintype.card V
  let vertexEquiv : V ≃ Fin n := Fintype.equivFin V
  -- All cliques of G (including singletons and ∅)
  -- We filter Finset (Finset V) by IsClique (which takes Set V, so we coerce)
  let allCliques : Finset (Finset V) :=
    (Finset.univ : Finset (Finset V)).filter (fun C => G.IsClique (C : Set V))
  let k := allCliques.card
  -- Handle the degenerate case where there are no cliques (impossible for nonempty V)
  have hk_pos : 0 < k := by
    have v := Classical.arbitrary V
    have hsing : ({v} : Finset V) ∈ allCliques := by
      simp only [allCliques, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton]
      exact G.isClique_singleton v
    exact Finset.card_pos.mpr ⟨{v}, hsing⟩
  let cliqueEquiv : allCliques ≃ Fin k := by
    have hcard : Fintype.card allCliques = k := Fintype.card_coe allCliques
    exact (Fintype.equivFin allCliques).trans (finCongr hcard)
  -- Define the incidence matrix A : Matrix (Fin n) (Fin k) ℝ
  -- A[i,j] = 1 if vertex i is in clique j, 0 otherwise
  let A : Matrix (Fin n) (Fin k) ℝ := fun i j =>
    if vertexEquiv.symm i ∈ (cliqueEquiv.symm j).val then 1 else 0
  -- The covering LP is: min 1ᵀw s.t. Aw ≥ 1, w ≥ 0
  -- The packing LP is: max 1ᵀx s.t. Aᵀx ≤ 1, x ≥ 0
  --
  -- Key insight: For any covering w and packing x,
  --   1ᵀx ≤ 1ᵀx · (1ᵀAw/n) ≤ ... ≤ 1ᵀw (by weak duality)
  --
  -- For strong duality, we use that the image cone is closed (finite dimensions).
  -- The structural definitions correspond to LP solutions:
  -- - FractionalCliqueCover → w ≥ 0 with Aw ≥ 1
  -- - FractionalIndependentSet → x ≥ 0 with Aᵀx ≤ 1
  -- We show: inf over covers ≤ sup over independent sets
  -- Combined with weak duality (sup ≤ inf), this gives equality.
  -- The proof uses the closed image cone theorem from LP.lean.
  -- For finite-dimensional LP, the cone {(Ax, 1ᵀx) : x ≥ 0} is closed.
  -- This means: if there's no covering with weight < t, then there's
  -- a packing with weight ≥ t (Farkas alternative).
  -- Apply LP strong duality for finite-dimensional covering/packing
  -- The key is coneImage_isClosed from ConeProgrammingDuality/LP.lean
  -- For any ε > 0, we find an independent set with weight ≥ (inf covering) - ε
  -- Since the sup is the limit, sup ≥ inf.
  -- The formal connection uses lp_farkas:
  -- For the system Aw ≥ 1, w ≥ 0 to have no solution with 1ᵀw < t,
  -- there must exist y ≥ 0 with Aᵀy ≤ 1 (packing constraint violated)
  -- But our packing solutions satisfy Aᵀy ≤ 1, so this gives a bound.
  -- Direct proof using compactness of the packing polytope:
  -- The set {x ≥ 0 : Aᵀx ≤ 1} is compact (bounded by [0,1]^n, closed).
  -- The function 1ᵀx is continuous, so the maximum is attained.
  -- By LP strong duality, this maximum equals the covering minimum.
  -- For the formal proof, we show the gap is zero by contradiction.
  -- Suppose inf > sup. Then there's a separating hyperplane (Farkas).
  -- This hyperplane would violate feasibility of one of the problems.
  -- Apply the duality result: both inf and sup are over nonempty bounded sets
  have hweak := fractionalIndependenceNumber_le_coverNumber G
  -- Key helper: allCliques contains all cliques of G
  have hallCliques : ∀ C : Finset V, G.IsClique C → C ∈ allCliques := by
    intro C hC
    simp only [allCliques, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hC
  -- Key helper: for each vertex, the singleton clique exists in allCliques
  have hA_singletons : ∀ i : Fin n, ∃ j : Fin k, A i j = 1 := by
    intro i
    let v := vertexEquiv.symm i
    have hsing : ({v} : Finset V) ∈ allCliques := by
      apply hallCliques
      rw [Finset.coe_singleton]
      exact G.isClique_singleton v
    use cliqueEquiv ⟨{v}, hsing⟩
    simp only [A, Equiv.symm_apply_apply, Subtype.coe_mk, Finset.mem_singleton]
    -- v = vertexEquiv.symm i, so vertexEquiv.symm i ∈ {v} is v ∈ {v} which is true
    simp only [v, ↓reduceIte]
  -- Matrix constraint interpretation: (Aᵀx)_j ≤ 1 means clique j constraint satisfied
  have hA_clique_interp : ∀ (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i),
      (∀ j, (A.transpose.mulVec x) j ≤ 1) ↔
      (∀ C : Finset V, G.IsClique C → (C.sum fun v => x (vertexEquiv v)) ≤ 1) := by
    intro x hx
    constructor
    · -- Forward: matrix packing constraint → structural clique constraint
      intro hpack C hC
      have hCmem := hallCliques C hC
      let j := cliqueEquiv ⟨C, hCmem⟩
      have hj := hpack j
      simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct] at hj
      -- Show the sums are equal: ∑ i, A[i,j] * x_i = ∑ v ∈ C, x(vertexEquiv v)
      have heq : (∑ i : Fin n, A i j * x i) = C.sum (fun v => x (vertexEquiv v)) := by
        -- A[i,j] = 1 iff vertexEquiv.symm i ∈ C (since j = cliqueEquiv ⟨C, hCmem⟩)
        have hAij : ∀ i, A i j = if vertexEquiv.symm i ∈ C then 1 else 0 := by
          intro i
          simp only [A, j, Equiv.symm_apply_apply, Subtype.coe_mk]
        calc ∑ i, A i j * x i
          = ∑ i, (if vertexEquiv.symm i ∈ C then 1 else 0) * x i := by
              apply Finset.sum_congr rfl; intro i _; rw [hAij]
          _ = ∑ i, if vertexEquiv.symm i ∈ C then x i else 0 := by
              apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring
          _ = (Finset.univ.filter (fun i => vertexEquiv.symm i ∈ C)).sum (fun i => x i) := by
              rw [Finset.sum_filter]
          _ = C.sum (fun v => x (vertexEquiv v)) := by
              apply Finset.sum_equiv vertexEquiv.symm
              · intro i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              · intro i _; simp only [Equiv.apply_symm_apply]
      linarith [heq]
    · -- Backward: structural clique constraint → matrix packing constraint
      intro hC j
      let Cj := (cliqueEquiv.symm j).val
      have hCj : G.IsClique Cj := by
        have hmem := (cliqueEquiv.symm j).property
        simp only [allCliques, Finset.mem_filter] at hmem
        exact hmem.2
      simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct]
      -- Show the sums are equal: ∑ i, A[i,j] * x_i = ∑ v ∈ Cj, x(vertexEquiv v)
      have heq : (∑ i : Fin n, A i j * x i) = Cj.sum (fun v => x (vertexEquiv v)) := by
        have hAij : ∀ i, A i j = if vertexEquiv.symm i ∈ Cj then 1 else 0 := by
          intro i
          simp only [A, Cj]
        calc ∑ i, A i j * x i
          = ∑ i, (if vertexEquiv.symm i ∈ Cj then 1 else 0) * x i := by
              apply Finset.sum_congr rfl; intro i _; rw [hAij]
          _ = ∑ i, if vertexEquiv.symm i ∈ Cj then x i else 0 := by
              apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring
          _ = (Finset.univ.filter (fun i => vertexEquiv.symm i ∈ Cj)).sum (fun i => x i) := by
              rw [Finset.sum_filter]
          _ = Cj.sum (fun v => x (vertexEquiv v)) := by
              apply Finset.sum_equiv vertexEquiv.symm
              · intro i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              · intro i _; simp only [Equiv.apply_symm_apply]
      rw [heq]
      exact hC Cj hCj
  -- Use LP duality: inf{covering} ≤ sup{packing} via Farkas alternative
  -- For any t < inf{covering}, the covering LP with bound t is infeasible
  -- By Farkas, there exists a packing with weight > t
  -- Hence sup{packing} ≥ t for all t < inf{covering}
  -- Therefore sup{packing} ≥ inf{covering}
  -- We show: for any t < inf{cover}, we have t < sup{fi}
  -- This implies inf{cover} ≤ sup{fi} by le_of_forall_lt
  apply le_of_forall_lt
  intro t ht
  -- The packing polytope is bounded, so we can find a packing with weight close to sup
  -- We show there exists fi with weight > t
  have hsup_bdd : BddAbove (Set.range (fun fi : FractionalIndependentSet G => fi.totalWeight)) := by
    use Fintype.card V
    intro x ⟨fi, hfi⟩
    rw [← hfi]
    exact fi.totalWeight_le_card
  -- Since t < inf cover, and inf ≤ sup by LP duality argument,
  -- we need to show there exists fi with weight > t
  -- This follows from the weak duality: any fi weight ≤ any cover weight
  -- So sup{fi} ≤ inf{cover}. Combined with t < inf{cover}:
  -- If t < inf, we need sup > t.
  -- The key insight: the packing polytope is compact, so sup = max is achieved
  -- But we need to establish inf ≤ sup first using Farkas.
  -- Use that sup ≥ 0 (zero fi exists) and inf > t implies we need sup > t
  -- The parametric Farkas argument shows: if inf > t, then sup > t
  -- Since this requires the full augmented Farkas, we use an approximation argument:
  -- The packing polytope P = {x ≥ 0 : Aᵀx ≤ 1} is compact (closed and bounded)
  -- The objective ∑xᵢ is continuous, so max is attained
  -- By LP strong duality (proved in LP.lean), inf = max
  -- Convert t to an upper bound on fi weights
  -- We need to show ∃ fi, fi.totalWeight > t
  -- Since ⨅ cover > t, all covers have weight > t
  -- By LP duality, sup{fi} = inf{cover} > t
  -- So there exists fi with weight close to sup > t
  -- Use compactness: packing polytope is compact, sup is achieved
  -- The zero packing gives weight 0
  have hzero_fi : ∃ fi : FractionalIndependentSet G, fi.totalWeight = 0 := by
    use ⟨fun _ => 0, fun _ => le_refl 0, fun _ _ => by simp⟩
    simp [FractionalIndependentSet.totalWeight]
  -- By LP strong duality (proven in LP.lean), inf{LP covering} = sup{LP packing}
  -- The structural inf equals LP inf, structural sup equals LP sup
  -- So inf{cover} = sup{fi}
  -- Since t < ⨅ cover = sup{fi}, there exists fi with weight > t
  -- This is by definition of supremum
  -- Apply ciSup definition: t < ⨆ fi means ∃ fi, fi.weight > t
  -- But we have t < ⨅ cover, and by duality ⨅ cover = ⨆ fi
  -- For the formal proof, we use LP duality from LP.lean:
  -- The result is that both optima are equal (when both feasible)
  -- Here both are feasible:
  -- - Covering: singleton cover
  -- - Packing: zero vector
  -- By LP strong duality (proved in LP.lean),
  -- we have ⨅ cover = ⨆ fi (as real numbers, not just ≤)
  -- So t < ⨅ cover = ⨆ fi, hence by sup definition, ∃ fi, t < fi.weight
  -- The strict inequality version: use that sup is achieved in compact set
  -- or use that for any bound strictly less than sup, there's an element exceeding it
  -- We use the Farkas-based argument directly:
  -- For t < ⨅ cover, the covering LP with bound t is infeasible
  -- By Farkas alternative, there exists a packing with weight > t
  -- This packing corresponds to fi with weight > t
  -- Set up the augmented matrix A' : Matrix (Fin (n+1)) (Fin k) ℝ
  -- A'[i,j] = A[i,j] for i < n
  -- A'[n,j] = -1 for all j
  let A' : Matrix (Fin (n + 1)) (Fin k) ℝ := fun i j =>
    if h : i.val < n then A ⟨i.val, h⟩ j else -1
  -- Set up the right-hand side b' : Fin (n+1) → ℝ
  -- b'[i] = 1 for i < n
  -- b'[n] = -t
  let b' : Fin (n + 1) → ℝ := fun i =>
    if h : i.val < n then 1 else -t
  -- The covering LP with bound t is: ∃ w ≥ 0, A'w ≥ b'
  -- This is equivalent to: Aw ≥ 1 and 1ᵀw ≤ t
  -- Claim: The covering LP with bound t is infeasible
  have hinfeas : ¬∃ w : Fin k → ℝ, (∀ j, 0 ≤ w j) ∧ (∀ i, b' i ≤ (A'.mulVec w) i) := by
    intro ⟨w, hw_nonneg, hw_covers⟩
    -- Extract covering constraints
    have hcov : ∀ i : Fin n, 1 ≤ (A.mulVec w) i := by
      intro i
      have hi := hw_covers ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      simp only [b', A', i.isLt, ↓reduceDIte] at hi
      -- Goal: show (A.mulVec w) i = (A'.mulVec w) ⟨i.val, _⟩
      -- where A' and A agree on rows < n
      have heq : (A.mulVec w) i = (A'.mulVec w) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro j _
        simp only [A', i.isLt, ↓reduceDIte, Fin.eta]
      linarith [heq]
    -- Extract objective bound
    have hobj : -t ≤ -Finset.univ.sum w := by
      have hn := hw_covers ⟨n, Nat.lt_succ_self n⟩
      simp only [b', A', Nat.lt_irrefl, ↓reduceDIte] at hn
      simp only [Matrix.mulVec, dotProduct] at hn
      have heq : ∑ j : Fin k, (-1 : ℝ) * w j = -Finset.univ.sum w := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp only [Nat.lt_irrefl, ↓reduceDIte, neg_one_mul] at hn
      have hsum : ∑ x : Fin k, -w x = -Finset.univ.sum w := by
        rw [← Finset.sum_neg_distrib]
      linarith [hsum]
    have hobj' : Finset.univ.sum w ≤ t := by linarith
    -- Construct a FractionalCliqueCover from w
    let cover : FractionalCliqueCover G :=
      { cliques := allCliques
        weights := fun C => if h : C ∈ allCliques then w (cliqueEquiv ⟨C, h⟩) else 0
        isClique := by
          intro C hC
          simp only [allCliques, Finset.mem_filter] at hC
          exact hC.2
        nonneg := by
          intro C hC
          simp only [hC, ↓reduceDIte]
          exact hw_nonneg _
        covers := by
          intro v
          let i := vertexEquiv v
          have hcov_i := hcov i
          simp only [Matrix.mulVec, dotProduct] at hcov_i
          -- Show: ∑_{C ∋ v} w_C ≥ 1 by showing it equals (A.mulVec w)_i ≥ 1
          -- For C in filter, C ∈ allCliques, so dite simplifies
          have heq : (allCliques.filter (v ∈ ·)).sum
              (fun C => if h : C ∈ allCliques then w (cliqueEquiv ⟨C, h⟩) else 0) =
              ∑ j : Fin k, A i j * w j := by
            -- Step 1: RHS converts to filtered sum
            have hAij : ∀ j, A i j = if v ∈ (cliqueEquiv.symm j).val then 1 else 0 := by
              intro j; simp only [A, i, Equiv.symm_apply_apply]
            have hrhs : ∑ j : Fin k, A i j * w j =
                (Finset.univ.filter (fun j => v ∈ (cliqueEquiv.symm j).val)).sum
                (fun j => w j) := by
              calc ∑ j : Fin k, A i j * w j
                = ∑ j, (if v ∈ (cliqueEquiv.symm j).val then 1 else 0) * w j := by
                    apply Finset.sum_congr rfl; intro j _; rw [hAij]
                _ = ∑ j, if v ∈ (cliqueEquiv.symm j).val then w j else 0 := by
                    apply Finset.sum_congr rfl; intro j _; split_ifs <;> ring
                _ = (Finset.univ.filter (fun j => v ∈ (cliqueEquiv.symm j).val)).sum
                    (fun j => w j) := by
                    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
            rw [hrhs]
            -- Both filtered sums are over the same elements via cliqueEquiv
            refine Finset.sum_bij' (i := fun C hC =>
                cliqueEquiv ⟨C, Finset.mem_of_mem_filter _ hC⟩)
              (j := fun j _ => (cliqueEquiv.symm j).val) ?hi ?hj ?left_inv ?right_inv ?heq
            case hi =>
              intro C hC
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Equiv.symm_apply_apply, Subtype.coe_mk]
              exact (Finset.mem_filter.mp hC).2
            case hj =>
              intro j hj
              rw [Finset.mem_filter] at hj ⊢
              exact ⟨(cliqueEquiv.symm j).property, hj.2⟩
            case left_inv =>
              -- Goal: (cliqueEquiv.symm (cliqueEquiv ⟨C, _⟩)).val = C
              intro C _
              simp only [Equiv.symm_apply_apply, Subtype.coe_mk]
            case right_inv =>
              -- Goal: cliqueEquiv ⟨(cliqueEquiv.symm C).val, _⟩ = C
              intro C _
              simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
            case heq =>
              intro C hC
              have hmem : C ∈ allCliques := Finset.mem_of_mem_filter _ hC
              simp only [hmem, dite_true]
          linarith [heq] }
    -- Show cover.totalWeight ≤ t
    have hcover_weight : cover.totalWeight ≤ t := by
      unfold FractionalCliqueCover.totalWeight
      simp only [cover]
      have heq : allCliques.sum (fun C => if h : C ∈ allCliques then
          w (cliqueEquiv ⟨C, h⟩) else 0) = Finset.univ.sum w := by
        rw [← Finset.sum_coe_sort allCliques]
        have h1 : ∑ x : ↥allCliques, (fun C => if h : C ∈ allCliques then
            w (cliqueEquiv ⟨C, h⟩) else 0) x.val =
            ∑ x : ↥allCliques, w (cliqueEquiv x) := by
          apply Finset.sum_congr rfl
          intro x _
          simp only [x.property, ↓reduceDIte]
        simp only at h1
        rw [h1]
        rw [Finset.sum_equiv cliqueEquiv]
        · intro x; simp only [Finset.mem_univ]
        · intro x _; rfl
      linarith [heq]
    -- Derive contradiction
    have hcover_ge : cover.totalWeight ≥ ⨅ c : FractionalCliqueCover G, c.totalWeight := by
      exact ciInf_le hinf_bdd cover
    linarith
  -- By Farkas alternative (lp_farkas_ineq), since the system is infeasible,
  -- there exists a certificate
  rw [ConeProgramming.lp_farkas_ineq] at hinfeas
  push_neg at hinfeas
  obtain ⟨z, hz_nonneg, hz_trans, hz_obj⟩ := hinfeas
  -- z : Fin (n+1) → ℝ with z ≥ 0
  -- A'ᵀz ≤ 0 and b'·z > 0
  -- Extract y : Fin n → ℝ and μ : ℝ from z
  let y : Fin n → ℝ := fun i => z ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let μ : ℝ := z ⟨n, Nat.lt_succ_self n⟩
  -- Properties of y and μ
  have hy_nonneg : ∀ i, 0 ≤ y i := fun i => hz_nonneg ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  have hμ_nonneg : 0 ≤ μ := hz_nonneg ⟨n, Nat.lt_succ_self n⟩
  -- A'ᵀz ≤ 0 means (Aᵀy)_j - μ ≤ 0 for all j, i.e., Aᵀy ≤ μ·1
  have hATy_bound : ∀ j, (A.transpose.mulVec y) j ≤ μ := by
    intro j
    have hj := hz_trans j
    simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct, A'] at hj
    -- Split the sum over Fin (n+1) into sum over Fin n plus the last term
    have hsplit :
        (∑ x : Fin (n + 1),
            (if h : (x : ℕ) < n then A ⟨x, h⟩ j else -1) * z x) =
          (∑ i : Fin n, A i j * z ⟨i, Nat.lt_succ_of_lt i.isLt⟩) +
            (-1) * z ⟨n, Nat.lt_succ_self n⟩ := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        cases i with
        | mk i hi =>
            simp [Fin.castSucc, hi, ↓reduceDIte]
      · simp only [Nat.lt_irrefl, ↓reduceDIte, Fin.last]
    simp only [hsplit] at hj
    simp only [neg_one_mul] at hj
    -- hj : (∑ i, A i j * y i) + (-μ) ≤ 0
    -- So (∑ i, A i j * y i) ≤ μ
    simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct]
    have heq :
        (∑ i : Fin n, A i j * y i) =
          ∑ i : Fin n, A i j * z ⟨i, Nat.lt_succ_of_lt i.isLt⟩ := by
      apply Finset.sum_congr rfl; intro i _; simp only [y]
    rw [heq]
    linarith
  -- b'·z > 0 means 1ᵀy - t·μ > 0
  have hyz_obj : Finset.univ.sum y > t * μ := by
    simp only [dotProduct] at hz_obj
    -- Split the sum over Fin (n+1) into sum over Fin n plus the last term
    have hsplit :
        (∑ i : Fin (n + 1), b' i * z i) =
          (∑ i : Fin n, z ⟨i, Nat.lt_succ_of_lt i.isLt⟩) +
            (-t) * z ⟨n, Nat.lt_succ_self n⟩ := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        simp only [b', Fin.val_castSucc, i.isLt, ↓reduceDIte, one_mul]
        simp only [Fin.castSucc, Fin.castAdd, Fin.castLE]
      · simp only [b', Nat.lt_irrefl, ↓reduceDIte, Fin.last]
    simp only [hsplit] at hz_obj
    -- hz_obj : (∑ i, y i) + (-t) * μ > 0
    have heq : (∑ i : Fin n, y i) = ∑ i : Fin n, z ⟨i, Nat.lt_succ_of_lt i.isLt⟩ := by
      apply Finset.sum_congr rfl; intro i _; simp only [y]
    simp only [← heq] at hz_obj
    linarith
  -- Key step: μ > 0
  -- If μ = 0, then Aᵀy ≤ 0 and 1ᵀy > 0 with y ≥ 0
  -- But (Aᵀy)_j = ∑_i A[i,j] y_i ≤ 0 for all j
  -- For singleton clique {v}, A[v,j] = 1 only when j is that clique, so y_v ≤ 0
  -- Combined with y ≥ 0, we get y = 0, contradicting 1ᵀy > 0
  have hμ_pos : 0 < μ := by
    by_contra hμ_not_pos
    push_neg at hμ_not_pos
    have hμ_zero : μ = 0 := le_antisymm hμ_not_pos hμ_nonneg
    -- With μ = 0, we have Aᵀy ≤ 0 and 1ᵀy > 0
    have hy_sum_pos : Finset.univ.sum y > 0 := by
      simp only [hμ_zero, mul_zero] at hyz_obj
      exact hyz_obj
    -- For each vertex v, using singleton clique {v}:
    -- (Aᵀy)_{singleton v} = y_v ≤ 0
    have hy_nonpos : ∀ i : Fin n, y i ≤ 0 := by
      intro i
      obtain ⟨j, hj⟩ := hA_singletons i
      have hbound := hATy_bound j
      simp only [hμ_zero] at hbound
      simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct] at hbound
      -- y_i = A[i,j] * y_i ≤ ∑_i' A[i',j] * y_i' ≤ 0
      have h1 : y i = A i j * y i := by rw [hj, one_mul]
      have h2 : A i j * y i ≤ ∑ i', A i' j * y i' := by
        have hpos : ∀ i' : Fin n, 0 ≤ A i' j * y i' := fun i' =>
          mul_nonneg (by simp only [A]; split_ifs <;> linarith) (hy_nonneg i')
        calc A i j * y i
          ≤ ∑ i' ∈ Finset.univ, A i' j * y i' := Finset.single_le_sum (fun i' _ => hpos i')
              (Finset.mem_univ i)
          _ = ∑ i', A i' j * y i' := by rfl
      linarith
    -- Contradiction: y ≥ 0 and y ≤ 0 means y = 0, but 1ᵀy > 0
    have hy_zero : ∀ i, y i = 0 := fun i => le_antisymm (hy_nonpos i) (hy_nonneg i)
    have hy_sum_zero : Finset.univ.sum y = 0 := by simp [hy_zero]
    linarith
  -- Now μ > 0, so we can define x = y/μ
  let x : Fin n → ℝ := fun i => y i / μ
  -- x is a valid packing
  have hx_nonneg : ∀ i, 0 ≤ x i := fun i => div_nonneg (hy_nonneg i) (le_of_lt hμ_pos)
  have hx_pack : ∀ j, (A.transpose.mulVec x) j ≤ 1 := by
    intro j
    simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct, x]
    -- ∑_i A[i,j] * (y_i/μ) = (1/μ) * ∑_i A[i,j] * y_i = (Aᵀy)_j / μ ≤ μ/μ = 1
    have heq : ∑ i, A i j * (y i / μ) = (∑ i, A i j * y i) / μ := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
    rw [heq]
    have hbound := hATy_bound j
    simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct] at hbound
    calc (∑ i, A i j * y i) / μ ≤ μ / μ := by
            apply div_le_div_of_nonneg_right hbound (le_of_lt hμ_pos)
      _ = 1 := by rw [div_self (ne_of_gt hμ_pos)]
  -- x has weight > t
  have hx_weight : Finset.univ.sum x > t := by
    simp only [x]
    calc Finset.univ.sum (fun i => y i / μ)
      = (Finset.univ.sum y) / μ := by rw [Finset.sum_div]
      _ > (t * μ) / μ := by
          apply div_lt_div_of_pos_right hyz_obj hμ_pos
      _ = t := by field_simp
  -- Convert x to packing constraints in structural form
  have hx_clique : ∀ C : Finset V, G.IsClique C →
      (C.sum fun v => x (vertexEquiv v)) ≤ 1 := by
    rw [← hA_clique_interp x hx_nonneg]
    exact hx_pack
  -- Construct FractionalIndependentSet from x
  let fi := FractionalIndependentSet.ofLPPacking G vertexEquiv x hx_nonneg hx_clique
  -- fi has weight > t
  have hfi_weight : fi.totalWeight > t := by
    rw [FractionalIndependentSet.ofLPPacking_totalWeight]
    exact hx_weight
  -- Show t < ⨆ fi
  rw [lt_ciSup_iff hsup_bdd]
  exact ⟨fi, hfi_weight⟩
/-- Strong LP duality: χ̄_f(G) = α_f(G) for finite graphs.

This combines weak duality (α_f ≤ χ̄_f, proved above) with strong duality (χ̄_f ≤ α_f).
The result is that the fractional clique covering number equals the fractional independence
number for all finite graphs. -/
theorem lp_duality {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Nonempty (FractionalCliqueCover G)] :
    fractionalCliqueCoverNumber G = fractionalIndependenceNumber G := by
  apply le_antisymm
  · -- χ̄_f ≤ α_f by LP strong duality
    exact lp_strong_duality G
  · -- α_f ≤ χ̄_f by weak duality (already proved)
    exact fractionalIndependenceNumber_le_coverNumber G

/-! ### Super-multiplicativity and super-additivity of α_f

These follow from the dual definition: given fractional independent sets of G and H,
we can construct fractional independent sets of G ⊠ H and G ⊔ H. -/

/-- Combine fractional independent sets of G and H into one on disjointUnion G H.
    Weights on Sum.inl v = fiG.weights v, on Sum.inr w = fiH.weights w. -/
noncomputable def FractionalIndependentSet.combine {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (fiG : FractionalIndependentSet G) (fiH : FractionalIndependentSet H) :
    FractionalIndependentSet (disjointUnion G H) where
  weights := fun x => match x with
    | .inl v => fiG.weights v
    | .inr w => fiH.weights w
  nonneg := by
    intro x
    match x with
    | .inl v => exact fiG.nonneg v
    | .inr w => exact fiH.nonneg w
  clique_bound := by
    intro C hC
    -- Cliques in disjointUnion G H are either entirely in G or entirely in H
    -- (since there are no edges between Sum.inl and Sum.inr)
    -- First, we partition C into left and right parts
    let CL := C.preimage Sum.inl (Sum.inl_injective (α := V) (β := W)).injOn
    let CR := C.preimage Sum.inr (Sum.inr_injective (α := V) (β := W)).injOn
    -- Key lemma: if C has elements from both sides, it can't be a clique (size ≥ 2)
    -- because there are no edges between inl and inr
    by_cases hCL : CL.Nonempty
    case pos =>
      by_cases hCR : CR.Nonempty
      case pos =>
        -- C has elements from both left and right - contradiction with being a clique
        obtain ⟨vL, hvL⟩ := hCL
        obtain ⟨wR, hwR⟩ := hCR
        -- vL ∈ CL means Sum.inl vL ∈ C
        have hvL' : Sum.inl vL ∈ C := by
          simp only [CL, Finset.mem_preimage] at hvL
          exact hvL
        have hwR' : Sum.inr wR ∈ C := by
          simp only [CR, Finset.mem_preimage] at hwR
          exact hwR
        -- Since C is a clique, Sum.inl vL and Sum.inr wR must be adjacent
        rw [isClique_iff, Set.Pairwise] at hC
        have hne : Sum.inl vL ≠ Sum.inr wR := Sum.inl_ne_inr
        have hadj := hC hvL' hwR' hne
        -- But disjointUnion has no edges between inl and inr
        simp only [disjUnionSimple] at hadj
      case neg =>
        -- C is entirely on the left side (from G)
        -- The clique C projected to G is a clique in G
        have hCL_clique : G.IsClique CL := by
          rw [isClique_iff, Set.Pairwise]
          intro a ha b hb hab
          simp only [CL, Finset.coe_preimage] at ha hb
          rw [isClique_iff, Set.Pairwise] at hC
          have ha' : (Sum.inl a : V ⊕ W) ∈ C := ha
          have hb' : (Sum.inl b : V ⊕ W) ∈ C := hb
          have hne : (Sum.inl a : V ⊕ W) ≠ Sum.inl b := by
            intro heq
            apply hab
            exact Sum.inl_injective heq
          have hadj := hC ha' hb' hne
          simp only [disjUnionSimple] at hadj
          exact hadj
        -- Use fiG.clique_bound on CL
        have hbound := fiG.clique_bound CL hCL_clique
        -- Since CR is empty, C = CL.map Sum.inl
        have hC_eq : C = CL.map ⟨Sum.inl, Sum.inl_injective⟩ := by
          ext x
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
          constructor
          · intro hx
            cases x with
            | inl v =>
              use v
              simp only [CL, Finset.mem_preimage, hx, true_and]
            | inr w =>
              exfalso
              apply hCR
              use w
              simp only [CR, Finset.mem_preimage, hx]
          · rintro ⟨v, hv, rfl⟩
            exact Finset.mem_preimage.mp hv
        -- The sum over C equals the sum over CL
        calc C.sum _ = (CL.map ⟨Sum.inl, Sum.inl_injective⟩).sum _ := by rw [hC_eq]
          _ = CL.sum (fun v => fiG.weights v) := Finset.sum_map _ _ _
          _ ≤ 1 := hbound
    case neg =>
      -- CL is empty, so C is entirely on the right side (from H)
      by_cases hCR : CR.Nonempty
      case pos =>
        have hCR_clique : H.IsClique CR := by
          rw [isClique_iff, Set.Pairwise]
          intro a ha b hb hab
          simp only [CR, Finset.coe_preimage] at ha hb
          rw [isClique_iff, Set.Pairwise] at hC
          have ha' : (Sum.inr a : V ⊕ W) ∈ C := ha
          have hb' : (Sum.inr b : V ⊕ W) ∈ C := hb
          have hne : (Sum.inr a : V ⊕ W) ≠ Sum.inr b := by
            intro heq
            apply hab
            exact Sum.inr_injective heq
          have hadj := hC ha' hb' hne
          simp only [disjUnionSimple] at hadj
          exact hadj
        have hbound := fiH.clique_bound CR hCR_clique
        -- Since CL is empty, C = CR.map Sum.inr
        have hC_eq : C = CR.map ⟨Sum.inr, Sum.inr_injective⟩ := by
          ext x
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
          constructor
          · intro hx
            cases x with
            | inl v =>
              exfalso
              apply hCL
              use v
              simp only [CL, Finset.mem_preimage, hx]
            | inr w =>
              use w
              simp only [CR, Finset.mem_preimage, hx, true_and]
          · rintro ⟨w, hw, rfl⟩
            exact Finset.mem_preimage.mp hw
        -- The sum over C equals the sum over CR
        calc C.sum _ = (CR.map ⟨Sum.inr, Sum.inr_injective⟩).sum _ := by rw [hC_eq]
          _ = CR.sum (fun w => fiH.weights w) := Finset.sum_map _ _ _
          _ ≤ 1 := hbound
      case neg =>
        -- Both CL and CR are empty, so C is empty
        have hC_empty : C = ∅ := by
          ext x
          simp only [Finset.notMem_empty, iff_false]
          intro hx
          cases x with
          | inl v =>
            apply hCL
            use v
            simp only [CL, Finset.mem_preimage]
            exact hx
          | inr w =>
            apply hCR
            use w
            simp only [CR, Finset.mem_preimage]
            exact hx
        simp [hC_empty]

/-- The combined fractional independent set has total weight = sum of individual weights. -/
theorem FractionalIndependentSet.combine_totalWeight {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (fiG : FractionalIndependentSet G) (fiH : FractionalIndependentSet H) :
    (fiG.combine fiH).totalWeight = fiG.totalWeight + fiH.totalWeight := by
  unfold totalWeight combine
  -- Sum over (V ⊕ W) = Sum over V + Sum over W
  rw [Fintype.sum_sum_type]

/-- α_f is super-additive under disjoint union.
    Given fractional independent sets of G and H, their disjoint union is a
    fractional independent set of G ⊔ H. -/
theorem fractionalIndependenceNumber_super_add {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    fractionalIndependenceNumber G + fractionalIndependenceNumber H ≤
    fractionalIndependenceNumber (disjointUnion G H) := by
  unfold fractionalIndependenceNumber
  -- For any fiG and fiH, their combination has weight = fiG.weight + fiH.weight
  -- Taking suprema: sup_G + sup_H ≤ sup_{G⊔H}
  -- The totalWeight is bounded by |V ⊕ W| since each vertex weight is ≤ 1
  have hbddGH : BddAbove (Set.range
      (fun fi : FractionalIndependentSet (disjointUnion G H) => fi.totalWeight)) := by
    use Fintype.card (V ⊕ W)
    intro _ ⟨fi, hfi⟩
    rw [← hfi]
    exact fi.totalWeight_le_card
  have hneG : Nonempty (FractionalIndependentSet G) := FractionalIndependentSet.exists_zero G
  have hneH : Nonempty (FractionalIndependentSet H) := FractionalIndependentSet.exists_zero H
  -- For any pair (fiG, fiH), the combined set has weight = sum
  have hpair : ∀ (fiG : FractionalIndependentSet G) (fiH : FractionalIndependentSet H),
      fiG.totalWeight + fiH.totalWeight ≤
      (⨆ fi : FractionalIndependentSet (disjointUnion G H), fi.totalWeight) := by
    intro fiG fiH
    rw [← FractionalIndependentSet.combine_totalWeight]
    exact le_ciSup hbddGH (fiG.combine fiH)
  -- Use ciSup_add_ciSup_le: if f(x) + g(y) ≤ c for all x, y, then sup f + sup g ≤ c
  exact ciSup_add_ciSup_le hpair

/-- Product of fractional independent sets for strong product G ⊠ H.
    Weight on (v, w) = fiG.weights v * fiH.weights w.
    Key: cliques in G ⊠ H are products of cliques in G and H. -/
noncomputable def FractionalIndependentSet.product {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (fiG : FractionalIndependentSet G) (fiH : FractionalIndependentSet H) :
    FractionalIndependentSet (ShannonCapacity.strongProduct G H) where
  weights := fun p => fiG.weights p.1 * fiH.weights p.2
  nonneg := by
    intro p
    exact mul_nonneg (fiG.nonneg p.1) (fiH.nonneg p.2)
  clique_bound := by
    intro C hC
    -- Cliques in G ⊠ H project to cliques in G and H
    -- Define projections
    let π₁C := C.image Prod.fst
    let π₂C := C.image Prod.snd
    -- Show π₁C is a clique in G
    have hπ₁_clique : G.IsClique π₁C := by
      rw [isClique_iff, Set.Pairwise]
      intro a ha b hb hab
      simp only [π₁C, Finset.coe_image, Set.mem_image] at ha hb
      obtain ⟨⟨a, wa⟩, hpa, rfl⟩ := ha
      obtain ⟨⟨b, wb⟩, hpb, rfl⟩ := hb
      rw [isClique_iff, Set.Pairwise] at hC
      have hne : (a, wa) ≠ (b, wb) := by
        intro heq
        apply hab
        simp only [Prod.mk.injEq] at heq
        exact heq.1
      have hadj := hC hpa hpb hne
      simp only [ShannonCapacity.strongProduct] at hadj
      obtain ⟨_, hG_or, _⟩ := hadj
      cases hG_or with
      | inl heq => exact (hab heq).elim
      | inr hadj => exact hadj
    -- Show π₂C is a clique in H
    have hπ₂_clique : H.IsClique π₂C := by
      rw [isClique_iff, Set.Pairwise]
      intro a ha b hb hab
      simp only [π₂C, Finset.coe_image, Set.mem_image] at ha hb
      obtain ⟨⟨va, a⟩, hpa, rfl⟩ := ha
      obtain ⟨⟨vb, b⟩, hpb, rfl⟩ := hb
      rw [isClique_iff, Set.Pairwise] at hC
      have hne : (va, a) ≠ (vb, b) := by
        intro heq
        apply hab
        simp only [Prod.mk.injEq] at heq
        exact heq.2
      have hadj := hC hpa hpb hne
      simp only [ShannonCapacity.strongProduct] at hadj
      obtain ⟨_, _, hH_or⟩ := hadj
      cases hH_or with
      | inl heq => exact (hab heq).elim
      | inr hadj => exact hadj
    -- Apply clique bounds
    have hbound1 := fiG.clique_bound π₁C hπ₁_clique
    have hbound2 := fiH.clique_bound π₂C hπ₂_clique
    -- Now: Σ_{(v,w) ∈ C} x(v)*y(w) ≤ (Σ_{v ∈ π₁C} x(v)) * (Σ_{w ∈ π₂C} y(w)) ≤ 1 * 1 = 1
    -- First show C ⊆ π₁C ×ˢ π₂C
    have hCsub : C ⊆ π₁C ×ˢ π₂C := by
      intro p hp
      simp only [Finset.mem_product, π₁C, π₂C]
      exact ⟨Finset.mem_image_of_mem Prod.fst hp, Finset.mem_image_of_mem Prod.snd hp⟩
    calc C.sum (fun p => fiG.weights p.1 * fiH.weights p.2)
      ≤ (π₁C ×ˢ π₂C).sum (fun p => fiG.weights p.1 * fiH.weights p.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hCsub
          (fun p _ _ => mul_nonneg (fiG.nonneg p.1) (fiH.nonneg p.2))
      _ = π₁C.sum (fun v => π₂C.sum (fun w => fiG.weights v * fiH.weights w)) :=
        Finset.sum_product π₁C π₂C _
      _ = π₁C.sum (fun v => fiG.weights v * π₂C.sum fiH.weights) := by
        congr 1; ext v; rw [Finset.mul_sum]
      _ = (π₁C.sum fiG.weights) * (π₂C.sum fiH.weights) := (Finset.sum_mul π₁C _ _).symm
      _ ≤ 1 * 1 := by
        apply mul_le_mul hbound1 hbound2
        · exact Finset.sum_nonneg (s := π₂C) (fun w _ => fiH.nonneg w)
        · linarith [Finset.sum_nonneg (s := π₁C) (fun v _ => fiG.nonneg v)]
      _ = 1 := by ring

/-- The product fractional independent set has total weight = product of individual weights. -/
theorem FractionalIndependentSet.product_totalWeight {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (fiG : FractionalIndependentSet G) (fiH : FractionalIndependentSet H) :
    (fiG.product fiH).totalWeight = fiG.totalWeight * fiH.totalWeight := by
  unfold totalWeight product
  -- Sum over (V × W) = Sum_v Sum_w x(v) * y(w) = (Sum_v x(v)) * (Sum_w y(w))
  simp only
  rw [Fintype.sum_prod_type]
  -- Need to show: Σ_v Σ_w x(v) * y(w) = (Σ_v x(v)) * (Σ_w y(w))
  rw [Finset.sum_mul]
  congr 1
  ext v
  rw [Finset.mul_sum]

/-- α_f is super-multiplicative under strong product.
    Given fractional independent sets of G and H, their product is a fractional
    independent set of G ⊠ H.
    Key fact: cliques in G ⊠ H are products of cliques in G and H. -/
theorem fractionalIndependenceNumber_super_mul {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    fractionalIndependenceNumber G * fractionalIndependenceNumber H ≤
    fractionalIndependenceNumber (ShannonCapacity.strongProduct G H) := by
  unfold fractionalIndependenceNumber
  -- For any fiG and fiH, their product has weight = fiG.weight * fiH.weight
  -- Taking suprema: sup_G * sup_H ≤ sup_{G⊠H}
  have hbddGH : BddAbove (Set.range
      (fun fi : FractionalIndependentSet (ShannonCapacity.strongProduct G H) =>
        fi.totalWeight)) := by
    use Fintype.card (V × W)
    intro _ ⟨fi, hfi⟩
    rw [← hfi]
    exact fi.totalWeight_le_card
  have hneG : Nonempty (FractionalIndependentSet G) := FractionalIndependentSet.exists_zero G
  have hneH : Nonempty (FractionalIndependentSet H) := FractionalIndependentSet.exists_zero H
  -- For non-negative reals with bounded suprema, we have:
  -- sup f * sup g ≤ sup (f * g) when all values are non-negative
  have hpair : ∀ (fiG : FractionalIndependentSet G) (fiH : FractionalIndependentSet H),
      fiG.totalWeight * fiH.totalWeight ≤
      (⨆ fi : FractionalIndependentSet (ShannonCapacity.strongProduct G H),
        fi.totalWeight) := by
    intro fiG fiH
    rw [← FractionalIndependentSet.product_totalWeight]
    exact le_ciSup hbddGH (fiG.product fiH)
  -- Use the fact that for non-negative bounded functions:
  -- if ∀ i j, f(i) * g(j) ≤ c, then (sup f) * (sup g) ≤ c
  have hbddG : BddAbove (Set.range (fun fi : FractionalIndependentSet G => fi.totalWeight)) := by
    use Fintype.card V
    intro _ ⟨fi, hfi⟩; rw [← hfi]; exact fi.totalWeight_le_card
  have hbddH : BddAbove (Set.range (fun fi : FractionalIndependentSet H => fi.totalWeight)) := by
    use Fintype.card W
    intro _ ⟨fi, hfi⟩; rw [← hfi]; exact fi.totalWeight_le_card
  have hnonnegG : ∀ fi : FractionalIndependentSet G, 0 ≤ fi.totalWeight := fun fi =>
    Finset.sum_nonneg (fun v _ => fi.nonneg v)
  have hnonnegH : ∀ fi : FractionalIndependentSet H, 0 ≤ fi.totalWeight := fun fi =>
    Finset.sum_nonneg (fun v _ => fi.nonneg v)
  -- Sup is non-negative
  have hsupsH : 0 ≤ ⨆ fi : FractionalIndependentSet H, fi.totalWeight := by
    apply le_ciSup_of_le hbddH (Classical.arbitrary _)
    exact hnonnegH _
  -- (sup_G f) * (sup_H g) = sup_G (f * sup_H g) using Real.iSup_mul_of_nonneg
  -- Then sup_G (f * sup_H g) = sup_G sup_H (f * g) using Real.mul_iSup_of_nonneg for each f
  rw [Real.iSup_mul_of_nonneg hsupsH]
  apply ciSup_le
  intro fiG
  rw [Real.mul_iSup_of_nonneg (hnonnegG fiG)]
  apply ciSup_le
  intro fiH
  exact hpair fiG fiH

/-! ### Spectral axioms (equalities) from sub + super bounds -/

/-- Spectral axiom (iii): χ̄_f is additive under disjoint union.
    χ̄_f(G ⊔ H) = χ̄_f(G) + χ̄_f(H)

    Proof: Combine sub-additivity of χ̄_f with super-additivity of α_f and LP duality.
    - (≤): fractionalCliqueCoverNumber_sub_add
    - (≥): Use lp_duality to convert to α_f, then fractionalIndependenceNumber_super_add -/
theorem fractionalCliqueCoverNumber_disjointUnion {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [Nonempty (FractionalCliqueCover G)] [Nonempty (FractionalCliqueCover H)] :
    fractionalCliqueCoverNumber (disjointUnion G H) =
    fractionalCliqueCoverNumber G + fractionalCliqueCoverNumber H := by
  apply le_antisymm
  · exact fractionalCliqueCoverNumber_sub_add G H
  · -- Use LP duality and super-additivity of α_f
    have h1 : fractionalCliqueCoverNumber G = fractionalIndependenceNumber G := lp_duality G
    have h2 : fractionalCliqueCoverNumber H = fractionalIndependenceNumber H := lp_duality H
    have h3 : fractionalCliqueCoverNumber (disjointUnion G H) =
              fractionalIndependenceNumber (disjointUnion G H) := lp_duality _
    rw [h1, h2, h3]
    exact fractionalIndependenceNumber_super_add G H

/-- Spectral axiom (ii): χ̄_f is multiplicative under strong product.
    χ̄_f(G ⊠ H) = χ̄_f(G) · χ̄_f(H)

    Proof: Combine sub-multiplicativity of χ̄_f with super-multiplicativity of α_f and LP duality.
    - (≤): fractionalCliqueCoverNumber_sub_mul
    - (≥): Use lp_duality to convert to α_f, then fractionalIndependenceNumber_super_mul -/
theorem fractionalCliqueCoverNumber_strongProduct {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [Nonempty (FractionalCliqueCover G)] [Nonempty (FractionalCliqueCover H)] :
    fractionalCliqueCoverNumber (ShannonCapacity.strongProduct G H) =
    fractionalCliqueCoverNumber G * fractionalCliqueCoverNumber H := by
  apply le_antisymm
  · exact fractionalCliqueCoverNumber_sub_mul G H
  · -- Use LP duality and super-multiplicativity of α_f
    have h1 : fractionalCliqueCoverNumber G = fractionalIndependenceNumber G := lp_duality G
    have h2 : fractionalCliqueCoverNumber H = fractionalIndependenceNumber H := lp_duality H
    have h3 : fractionalCliqueCoverNumber (ShannonCapacity.strongProduct G H) =
              fractionalIndependenceNumber (ShannonCapacity.strongProduct G H) := lp_duality _
    rw [h1, h2, h3]
    exact fractionalIndependenceNumber_super_mul G H

/-- Spectral axiom (i): χ̄_f is normalized: χ̄_f(E_1) = 1.
    E_1 is the single-vertex edgeless graph (complement of K_1). -/
theorem fractionalCliqueCoverNumber_normalized :
    fractionalCliqueCoverNumber (⊥ : SimpleGraph (Fin 1)) = 1 := by
  -- This is the n=1 case of the general normalized theorem
  -- The cover {({0}, 1)} has total weight 1 (achievable)
  -- Any cover must have weight ≥ 1 (lower bound)
  unfold fractionalCliqueCoverNumber
  apply le_antisymm
  · -- Upper bound: construct a cover with weight 1
    have hbdd : BddBelow (Set.range (fun c : FractionalCliqueCover (⊥ : SimpleGraph (Fin 1)) =>
        c.totalWeight)) := by
      use 0
      intro _ ⟨c, hc⟩
      rw [← hc]
      exact c.totalWeight_nonneg
    -- The singleton cover has weight 1
    let cover : FractionalCliqueCover (⊥ : SimpleGraph (Fin 1)) :=
      ⟨{{0}}, fun _ => 1,
       fun C hC => by
         simp only [Finset.mem_singleton] at hC
         rw [hC]
         rw [isClique_iff, Set.Pairwise]
         intro x hx y hy hxy
         simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
         rw [hx, hy] at hxy
         exact (hxy rfl).elim,
       fun _ _ => by norm_num,
       fun v => by
         have hv : v = 0 := Fin.ext_iff.mpr (Nat.lt_one_iff.mp v.isLt)
         rw [hv]
         have hfilter : ({{0}} : Finset (Finset (Fin 1))).filter (0 ∈ ·) = {{0}} := by
           ext C
           simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
           intro h; rw [h]; exact Finset.mem_singleton.mpr rfl
         rw [hfilter, Finset.sum_singleton]⟩
    have hweight : cover.totalWeight = 1 := by
      unfold FractionalCliqueCover.totalWeight
      have hcliques : cover.cliques = ({{0}} : Finset (Finset (Fin 1))) := rfl
      rw [hcliques]
      simp only [Finset.sum_singleton]
      rfl
    calc ⨅ c : FractionalCliqueCover (⊥ : SimpleGraph (Fin 1)), c.totalWeight
      ≤ cover.totalWeight := ciInf_le hbdd cover
      _ = 1 := hweight
  · -- Lower bound: any cover has weight ≥ 1
    apply le_ciInf
    intro cover
    -- The covering constraint for vertex 0 gives weight ≥ 1
    have hcov := cover.covers 0
    calc (1 : ℝ) ≤ (cover.cliques.filter (0 ∈ ·)).sum cover.weights := hcov
      _ ≤ cover.cliques.sum cover.weights := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro C hC _; exact cover.nonneg C hC
      _ = cover.totalWeight := rfl

/-- Evaluate fractional clique covering number on a FiniteGraph. -/
noncomputable def fractionalCliqueCoverNumber_finite (G : FiniteGraph) : ℝ :=
  fractionalCliqueCoverNumber G.graph

/-- The fractional clique covering number χ̄_f(G) as a spectral point on finite graphs.
    This is the maximum spectral point in the sense that χ̄_f ≥ φ for all φ ∈ Δ(G). -/
noncomputable def fractionalCliqueCovering_finite : FiniteGraph → ℝ :=
  fractionalCliqueCoverNumber_finite

notation "χ̄_f" => fractionalCliqueCovering_finite

/-- For the edgeless graph, cliques are exactly singletons -/
theorem edgeless_clique_iff {n : ℕ} (C : Finset (Fin n)) :
    (⊥ : SimpleGraph (Fin n)).IsClique C ↔ C.card ≤ 1 := by
  constructor
  · intro hC
    by_contra h
    push_neg at h
    -- C has at least 2 elements
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
    -- Since C is a clique, a and b must be adjacent
    rw [isClique_iff, Set.Pairwise] at hC
    have hadj := hC ha hb hab
    -- But ⊥ has no edges
    exact hadj
  · intro h
    rw [isClique_iff, Set.Pairwise]
    intro x hx y hy hxy
    -- C has at most 1 element, so x = y, contradiction
    have hmem_x : x ∈ C := by simpa using hx
    have hmem_y : y ∈ C := by simpa using hy
    have heq := (Finset.card_le_one_iff (s := C)).mp h hmem_x hmem_y
    exact hxy heq

/-- The singleton cover for the edgeless graph has total weight n -/
theorem edgeless_singleton_cover_weight (n : ℕ) :
    ∃ cover : FractionalCliqueCover (⊥ : SimpleGraph (Fin n)),
      cover.totalWeight = n := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨⟨∅, fun _ => 0, ?_, ?_, ?_⟩, ?_⟩
    · intro C hC; exact (Finset.notMem_empty C hC).elim
    · intro C hC; exact (Finset.notMem_empty C hC).elim
    · intro v; exact Fin.elim0 v
    · simp [FractionalCliqueCover.totalWeight]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    let cliques : Finset (Finset (Fin n)) := Finset.univ.image (fun v => {v})
    let weights : Finset (Fin n) → ℝ := fun _ => 1
    refine ⟨⟨cliques, weights, ?_, ?_, ?_⟩, ?_⟩
    · -- Each singleton is a clique
      intro C hC
      rw [Finset.mem_image] at hC
      obtain ⟨v, _, rfl⟩ := hC
      rw [edgeless_clique_iff]
      simp
    · -- Weights are non-negative
      intro _ _; norm_num
    · -- Each vertex is covered
      intro v
      have hv : {v} ∈ cliques := Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
      have hmem : {v} ∈ cliques.filter (v ∈ ·) := by
        simp only [Finset.mem_filter, hv, Finset.mem_singleton, true_and]
      calc (cliques.filter (v ∈ ·)).sum weights
        ≥ weights {v} := Finset.single_le_sum (fun _ _ => by norm_num) hmem
        _ = 1 := rfl
    · -- Total weight is n
      simp only [FractionalCliqueCover.totalWeight, cliques, weights]
      have : (Finset.univ.image (fun v : Fin n => ({v} : Finset (Fin n)))).sum (fun _ => (1 : ℝ))
           = (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.sum_image]
        · simp
        · intro x _ y _ hxy
          simpa using hxy
      rw [this, Finset.card_fin]

/-- Any fractional clique cover of the edgeless graph has total weight ≥ n -/
theorem edgeless_cover_weight_ge (n : ℕ) (cover : FractionalCliqueCover (⊥ : SimpleGraph (Fin n))) :
    (n : ℝ) ≤ cover.totalWeight := by
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.cast_zero]
    exact cover.totalWeight_nonneg
  · -- For n ≥ 1, we use that each vertex needs weight ≥ 1
    -- and cliques are singletons, so weights don't overlap
    -- Key insight: for edgeless graphs, cliques have card ≤ 1
    -- So the only clique containing v is {v}, which must be in the cover
    -- with weight ≥ 1. Since singletons are disjoint, total weight ≥ n.

    -- Step 1: Show that for each v, {v} ∈ cover.cliques with weight ≥ 1
    have h_singleton_in : ∀ v : Fin n, {v} ∈ cover.cliques := by
      intro v
      -- The covering constraint for v
      have hcov := cover.covers v
      -- If {v} ∉ cliques, then the filter is empty (no clique containing v)
      by_contra h
      -- Any clique C containing v must equal {v} (since cliques have card ≤ 1)
      have hCv_eq : ∀ C ∈ cover.cliques.filter (v ∈ ·), C = {v} := by
        intro C hC
        rw [Finset.mem_filter] at hC
        obtain ⟨hC_mem, hv_in⟩ := hC
        have hclique := cover.isClique C hC_mem
        rw [edgeless_clique_iff] at hclique
        ext x
        constructor
        · intro hx
          rw [Finset.mem_singleton]
          exact (Finset.card_le_one_iff (s := C)).mp hclique hx hv_in
        · intro hx
          rw [Finset.mem_singleton] at hx
          rw [hx]; exact hv_in
      -- Since {v} ∉ cliques, the filter must be empty
      have hfilter_empty : cover.cliques.filter (v ∈ ·) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro C hC
        have heq := hCv_eq C hC
        rw [heq, Finset.mem_filter] at hC
        exact h hC.1
      rw [hfilter_empty] at hcov
      simp only [Finset.sum_empty] at hcov
      norm_num at hcov
    have h_weight_ge : ∀ v : Fin n, cover.weights {v} ≥ 1 := by
      intro v
      have hcov := cover.covers v
      -- The only clique containing v is {v}
      have hfilter : cover.cliques.filter (v ∈ ·) = {{v}} := by
        ext C
        constructor
        · intro hC
          rw [Finset.mem_filter] at hC
          rw [Finset.mem_singleton]
          have hclique := cover.isClique C hC.1
          rw [edgeless_clique_iff] at hclique
          ext x
          constructor
          · intro hx
            rw [Finset.mem_singleton]
            exact (Finset.card_le_one_iff (s := C)).mp hclique hx hC.2
          · intro hx
            rw [Finset.mem_singleton] at hx
            rw [hx]; exact hC.2
        · intro hC
          rw [Finset.mem_singleton] at hC
          rw [hC]
          rw [Finset.mem_filter]
          exact ⟨h_singleton_in v, Finset.mem_singleton.mpr rfl⟩
      rw [hfilter] at hcov
      simp only [Finset.sum_singleton] at hcov
      exact hcov
    -- Step 2: Sum the weights
    have h_sum : (Finset.univ : Finset (Fin n)).sum (fun v => cover.weights {v}) ≤
        cover.totalWeight := by
      -- The singletons are all in cliques, and are distinct
      have hinj : ∀ v₁ v₂ : Fin n, {v₁} = ({v₂} : Finset (Fin n)) → v₁ = v₂ := by
        intro v₁ v₂ h
        have := Finset.singleton_injective h
        exact this
      have hsub :
          (Finset.univ.image (fun v : Fin n => ({v} : Finset (Fin n)))) ⊆ cover.cliques := by
        intro C hC
        rw [Finset.mem_image] at hC
        obtain ⟨v, _, rfl⟩ := hC
        exact h_singleton_in v
      calc (Finset.univ : Finset (Fin n)).sum (fun v => cover.weights {v})
        = (Finset.univ.image (fun v : Fin n => ({v} : Finset (Fin n)))).sum cover.weights := by
            rw [Finset.sum_image]
            intro v₁ _ v₂ _ heq
            exact Finset.singleton_injective heq
        _ ≤ cover.cliques.sum cover.weights := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro C hC _
            exact cover.nonneg C hC
        _ = cover.totalWeight := rfl
    calc (n : ℝ) = (Finset.univ : Finset (Fin n)).sum (fun _ => (1 : ℝ)) := by
          simp
      _ ≤ (Finset.univ : Finset (Fin n)).sum (fun v => cover.weights {v}) := by
          apply Finset.sum_le_sum
          intro v _
          exact h_weight_ge v
      _ ≤ cover.totalWeight := h_sum

/-- χ̄_f is normalized: χ̄_f(E_n) = n for edgeless graphs on n vertices. -/
theorem fractionalCliqueCovering_normalized (n : ℕ) :
    χ̄_f { V := Fin n, graph := ⊥ } = n := by
  simp only [fractionalCliqueCovering_finite, fractionalCliqueCoverNumber_finite,
    fractionalCliqueCoverNumber]
  apply le_antisymm
  · -- χ̄_f ≤ n: the singleton cover achieves n
    obtain ⟨cover, hcover⟩ := edgeless_singleton_cover_weight n
    have hbdd : BddBelow (Set.range fun c : FractionalCliqueCover (⊥ : SimpleGraph (Fin n)) =>
        c.totalWeight) := by
      use 0
      intro x ⟨c, hc⟩
      rw [← hc]
      exact c.totalWeight_nonneg
    calc ⨅ (cover : FractionalCliqueCover (⊥ : SimpleGraph (Fin n))), cover.totalWeight
      ≤ cover.totalWeight := ciInf_le hbdd cover
      _ = n := hcover
  · -- χ̄_f ≥ n: any cover has weight ≥ n
    apply le_ciInf
    intro cover
    exact edgeless_cover_weight_ge n cover

/-- χ̄_f is additive under disjoint union. -/
theorem fractionalCliqueCovering_add_disjointUnion (G H : FiniteGraph)
    [Nonempty (FractionalCliqueCover G.graph)] [Nonempty (FractionalCliqueCover H.graph)] :
    χ̄_f { V := G.V ⊕ H.V, graph := disjointUnion G.graph H.graph } =
    χ̄_f G + χ̄_f H := by
  simp only [fractionalCliqueCovering_finite, fractionalCliqueCoverNumber_finite]
  exact fractionalCliqueCoverNumber_disjointUnion G.graph H.graph

/-- χ̄_f is multiplicative under strong product. -/
theorem fractionalCliqueCovering_mul_strongProduct (G H : FiniteGraph)
    [Nonempty (FractionalCliqueCover G.graph)] [Nonempty (FractionalCliqueCover H.graph)] :
    χ̄_f { V := G.V × H.V, graph := ShannonCapacity.strongProduct G.graph H.graph } =
    χ̄_f G * χ̄_f H := by
  simp only [fractionalCliqueCovering_finite, fractionalCliqueCoverNumber_finite]
  exact fractionalCliqueCoverNumber_strongProduct G.graph H.graph

/-- χ̄_f is monotone under cohomomorphisms. -/
theorem fractionalCliqueCovering_mono_cohom (G H : FiniteGraph)
    (hcohom : ∃ f, IsCohom G.graph H.graph f) :
    χ̄_f G ≤ χ̄_f H := by
  simp only [fractionalCliqueCovering_finite, fractionalCliqueCoverNumber_finite]
  obtain ⟨f, hf⟩ := hcohom
  exact fractionalCliqueCoverNumber_cohom_mono G.graph H.graph f hf

/- χ̄_f is the maximum: for all G and spectral point φ, φ(G) ≤ χ̄_f(G).

    This is proved as `chibar_is_max` in DualityTheorems.lean using:
    - graphAsympRank_eq_chibar: asymptotic rank = χ̄_f
    - spectralPoint_le_asympRank: spectral points ≤ asymptotic rank -/

/-- The fractional clique covering number χ̄_f as a spectral point.
    This is the main construction showing χ̄_f satisfies all four spectral axioms. -/
noncomputable def chibar_spectralPoint : SpectralPoint where
  eval := χ̄_f
  normalized := by
    intro n
    -- χ̄_f (EdgelessGraph n) = n
    -- EdgelessGraph n = { V := Fin n, graph := edgelessGraph n } = { V := Fin n, graph := ⊥ }
    exact fractionalCliqueCovering_normalized n
  mul_strongProduct := by
    intro G H
    -- G ⊠ H = { V := G.V × H.V, graph := ShannonCapacity.strongProduct G.graph H.graph }
    exact fractionalCliqueCovering_mul_strongProduct G H
  add_disjointUnion := by
    intro G H
    -- G ⊔ᴳ H = { V := G.V ⊕ H.V, graph := disjointUnion G.graph H.graph }
    exact fractionalCliqueCovering_add_disjointUnion G H
  mono_cohom := by
    intro G H hcohom
    exact fractionalCliqueCovering_mono_cohom G H hcohom

/-- χ̄_f is monotone under cohomomorphisms: if G →co H then χ̄_f(G) ≤ χ̄_f(H).
    This is a direct consequence of fractionalCliqueCovering_mono_cohom. -/
theorem chibar_cohom_mono {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : V → W) (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v)) :
    χ̄_f { V := V, graph := G } ≤ χ̄_f { V := W, graph := H } := by
  exact fractionalCliqueCovering_mono_cohom { V := V, graph := G } { V := W, graph := H } ⟨f, hf⟩

/-! ### Full clique covers and compactness -/

section Rationality

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite set of all cliques of `G`. -/
noncomputable def allCliques (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact (Finset.univ : Finset (Finset V)).filter (fun C => G.IsClique (C : Set V))

/-- A full fractional clique cover uses weights on all cliques. -/
structure FullCliqueCover (G : SimpleGraph V) where
  weights : Finset V → ℝ
  nonneg : ∀ C ∈ allCliques G, 0 ≤ weights C
  covers : ∀ v : V, 1 ≤ ((allCliques G).filter (v ∈ ·)).sum weights

/-- Total weight of a full clique cover. -/
noncomputable def FullCliqueCover.totalWeight {G : SimpleGraph V} (cover : FullCliqueCover G) : ℝ :=
  (allCliques G).sum cover.weights

theorem FullCliqueCover.totalWeight_nonneg {G : SimpleGraph V} (cover : FullCliqueCover G) :
    0 ≤ cover.totalWeight := by
  unfold FullCliqueCover.totalWeight
  apply Finset.sum_nonneg
  intro C hC
  exact cover.nonneg C hC

private lemma allCliques_mem_of_clique {G : SimpleGraph V} {C : Finset V}
    (hC : G.IsClique C) : C ∈ allCliques G := by
  classical
  simp [allCliques, hC]

/-- Build a full clique cover from a fractional clique cover by filling missing cliques with 0. -/
noncomputable def FractionalCliqueCover.toFull {G : SimpleGraph V}
    (cover : FractionalCliqueCover G) : FullCliqueCover G := by
  classical
  refine ⟨?weights, ?nonneg, ?covers⟩
  · intro C
    by_cases hC : C ∈ cover.cliques
    · exact cover.weights C
    · exact 0
  · intro C hC
    by_cases hC' : C ∈ cover.cliques
    · simpa [hC'] using cover.nonneg C hC'
    · simp [hC']
  · intro v
    have hsubset : cover.cliques ⊆ allCliques G := by
      intro C hC
      exact allCliques_mem_of_clique (cover.isClique C hC)
    have hsum_eq :
        (cover.cliques.filter (v ∈ ·)).sum cover.weights =
          (cover.cliques.filter (v ∈ ·)).sum
            (fun C => if hC : C ∈ cover.cliques then cover.weights C else 0) := by
      refine Finset.sum_congr rfl ?_
      intro C hC
      have hC' : C ∈ cover.cliques := (Finset.mem_filter.mp hC).1
      simp [hC']
    have hsubset_filter :
        cover.cliques.filter (v ∈ ·) ⊆ (allCliques G).filter (v ∈ ·) := by
      intro C hC
      have hC' := Finset.mem_filter.mp hC
      have hC'' : C ∈ allCliques G := hsubset hC'.1
      exact Finset.mem_filter.mpr ⟨hC'', hC'.2⟩
    have hsum_le :
        (cover.cliques.filter (v ∈ ·)).sum
            (fun C => if hC : C ∈ cover.cliques then cover.weights C else 0) ≤
          ((allCliques G).filter (v ∈ ·)).sum
            (fun C => if hC : C ∈ cover.cliques then cover.weights C else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset_filter ?_
      intro C hC _
      by_cases hC' : C ∈ cover.cliques
      · simpa [hC'] using cover.nonneg C hC'
      · simp [hC']
    have hcover := cover.covers v
    have hcover' :
        1 ≤ ((allCliques G).filter (v ∈ ·)).sum
            (fun C => if hC : C ∈ cover.cliques then cover.weights C else 0) := by
      have h' := le_trans hsum_eq.le hsum_le
      exact le_trans hcover h'
    exact hcover'

/-- A full clique cover gives a fractional clique cover on all cliques. -/
noncomputable def FullCliqueCover.toCover {G : SimpleGraph V}
    (cover : FullCliqueCover G) : FractionalCliqueCover G := by
  classical
  refine ⟨allCliques G, cover.weights, ?isClique, ?nonneg, ?covers⟩
  · intro C hC
    simpa [allCliques] using hC
  · intro C hC
    exact cover.nonneg C hC
  · intro v
    simpa using cover.covers v

/-- The total weights agree under the translations. -/
theorem FractionalCliqueCover.toFull_totalWeight {G : SimpleGraph V}
    (cover : FractionalCliqueCover G) :
    (cover.toFull).totalWeight = cover.totalWeight := by
  classical
  unfold FullCliqueCover.totalWeight FractionalCliqueCover.totalWeight FractionalCliqueCover.toFull
  simp only
  have hsubset : cover.cliques ⊆ allCliques G := by
    intro C hC
    exact allCliques_mem_of_clique (cover.isClique C hC)
  have hsum :
      (allCliques G).sum (fun C => if hC : C ∈ cover.cliques then cover.weights C else 0) =
        cover.cliques.sum cover.weights := by
    have hsum_filter :
        ((allCliques G).filter (fun C => C ∈ cover.cliques)).sum cover.weights =
          (allCliques G).sum (fun C => if hC : C ∈ cover.cliques then cover.weights C else 0) := by
      simpa using
        (Finset.sum_filter (s := allCliques G) (p := fun C => C ∈ cover.cliques)
          (f := cover.weights))
    have hfilter :
        (allCliques G).filter (fun C => C ∈ cover.cliques) = cover.cliques := by
      ext C
      constructor
      · intro hC
        exact (Finset.mem_filter.mp hC).2
      · intro hC
        refine Finset.mem_filter.mpr ⟨hsubset hC, hC⟩
    calc
      (allCliques G).sum (fun C => if hC : C ∈ cover.cliques then cover.weights C else 0)
          = ((allCliques G).filter (fun C => C ∈ cover.cliques)).sum cover.weights := by
              symm
              exact hsum_filter
      _ = cover.cliques.sum cover.weights := by
            simp [hfilter]
  exact hsum

theorem FullCliqueCover.toCover_totalWeight {G : SimpleGraph V} (cover : FullCliqueCover G) :
    (cover.toCover).totalWeight = cover.totalWeight := by
  classical
  rfl

theorem FullCliqueCover.nonempty (G : SimpleGraph V) : Nonempty (FullCliqueCover G) := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨cover⟩ := FractionalCliqueCover.exists_singleton G
    exact ⟨cover.toFull⟩
  · obtain ⟨cover⟩ := FractionalCliqueCover.exists_empty G (not_nonempty_iff.mp hV)
    exact ⟨cover.toFull⟩

theorem fractionalCliqueCoverNumber_eq_iInf_full (G : SimpleGraph V) :
    fractionalCliqueCoverNumber G = ⨅ cover : FullCliqueCover G, cover.totalWeight := by
  classical
  haveI : Nonempty (FullCliqueCover G) := FullCliqueCover.nonempty G
  have hbdd : BddBelow (Set.range (fun c : FractionalCliqueCover G => c.totalWeight)) := by
    use 0
    intro x ⟨c, hc⟩
    rw [← hc]
    exact c.totalWeight_nonneg
  have hbdd_full : BddBelow (Set.range (fun c : FullCliqueCover G => c.totalWeight)) := by
    use 0
    intro x ⟨c, hc⟩
    rw [← hc]
    exact c.totalWeight_nonneg
  apply le_antisymm
  · refine le_ciInf ?_
    intro cover
    have h := ciInf_le hbdd (cover.toCover)
    simpa [FullCliqueCover.toCover_totalWeight] using h
  · refine le_ciInf ?_
    intro cover
    have h := ciInf_le hbdd_full (cover.toFull)
    simpa [FractionalCliqueCover.toFull_totalWeight] using h

/-! ### Matrix form for full covers -/

noncomputable def vertexEquiv (V : Type*) [Fintype V] : V ≃ Fin (Fintype.card V) :=
  Fintype.equivFin V

noncomputable def cliqueEquiv (G : SimpleGraph V) :
    (allCliques G) ≃ Fin (allCliques G).card := by
  classical
  simpa using (Fintype.equivFin (allCliques G))

/-- Incidence matrix for all cliques: rows are vertices, columns are cliques. -/
noncomputable def coverMatrix (G : SimpleGraph V) :
    Matrix (Fin (Fintype.card V)) (Fin (allCliques G).card) ℚ := by
  classical
  intro i j
  let v := (vertexEquiv V).symm i
  let C := (cliqueEquiv G).symm j
  exact if v ∈ C.val then 1 else 0

noncomputable def FullCliqueCover.toVector {G : SimpleGraph V} (cover : FullCliqueCover G) :
    Fin (allCliques G).card → ℝ := by
  classical
  intro j
  exact cover.weights ((cliqueEquiv G).symm j).val

theorem FullCliqueCover.totalWeight_eq_sum {G : SimpleGraph V} (cover : FullCliqueCover G) :
    cover.totalWeight = Finset.univ.sum cover.toVector := by
  classical
  unfold FullCliqueCover.totalWeight FullCliqueCover.toVector
  have hsum :
      (Finset.univ : Finset (Fin (allCliques G).card)).sum
          (fun j => cover.weights ((cliqueEquiv G).symm j).val) =
        (Finset.univ : Finset (allCliques G)).sum (fun C => cover.weights C) := by
    simpa using
      (Finset.sum_equiv (cliqueEquiv G).symm
        (s := (Finset.univ : Finset (Fin (allCliques G).card)))
        (t := (Finset.univ : Finset (allCliques G)))
        (f := fun j => cover.weights ((cliqueEquiv G).symm j).val)
        (g := fun C => cover.weights C)
        (by intro j; simp)
        (by intro j _; rfl))
  have hattach :
      (Finset.univ : Finset (allCliques G)).sum (fun C => cover.weights C) =
        (allCliques G).sum cover.weights := by
    have h := (Finset.sum_attach (s := allCliques G) (f := cover.weights))
    rw [Finset.attach_eq_univ] at h
    exact h
  calc
    (allCliques G).sum cover.weights
        = (Finset.univ : Finset (allCliques G)).sum (fun C => cover.weights C) := by
            symm
            exact hattach
    _ = (Finset.univ : Finset (Fin (allCliques G).card)).sum
          (fun j => cover.weights ((cliqueEquiv G).symm j).val) := by
            symm
            exact hsum

noncomputable def coverMatrixReal (G : SimpleGraph V) :
    Matrix (Fin (Fintype.card V)) (Fin (allCliques G).card) ℝ :=
  (coverMatrix G).map (Rat.castHom ℝ)

noncomputable def weightsOfVector (G : SimpleGraph V)
    (w : Fin (allCliques G).card → ℝ) : Finset V → ℝ :=
  fun C => if hC : C ∈ allCliques G then w (cliqueEquiv G ⟨C, hC⟩) else 0

private lemma mulVec_eq_sum_weights {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ) (i : Fin (Fintype.card V)) :
    (coverMatrixReal G).mulVec w i =
      ((allCliques G).filter ((vertexEquiv V).symm i ∈ ·)).sum (weightsOfVector G w) := by
  classical
  have hmul :
      (coverMatrixReal G).mulVec w i =
        ∑ j : Fin (allCliques G).card,
          (if (vertexEquiv V).symm i ∈ ((cliqueEquiv G).symm j).val then (1 : ℝ) else 0)
            * w j := by
    have hmul' :
        (coverMatrixReal G).mulVec w i =
          ∑ j : Fin (allCliques G).card,
            ((Rat.castHom ℝ)
                (if (vertexEquiv V).symm i ∈ ((cliqueEquiv G).symm j).val then 1 else 0))
              * w j := by
      rfl
    calc
      (coverMatrixReal G).mulVec w i
          = ∑ j : Fin (allCliques G).card,
              ((Rat.castHom ℝ)
                  (if (vertexEquiv V).symm i ∈ ((cliqueEquiv G).symm j).val then 1 else 0))
                * w j := hmul'
      _ = ∑ j : Fin (allCliques G).card,
            (if (vertexEquiv V).symm i ∈ ((cliqueEquiv G).symm j).val then (1 : ℝ) else 0)
              * w j := by
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases h : (vertexEquiv V).symm i ∈ ((cliqueEquiv G).symm j).val <;> simp [h]
  have hsum :
      (∑ j : Fin (allCliques G).card,
          (if (vertexEquiv V).symm i ∈ ((cliqueEquiv G).symm j).val then (1 : ℝ) else 0)
            * w j)
        = (Finset.univ : Finset (allCliques G)).sum
            (fun C => (if (vertexEquiv V).symm i ∈ (C : Finset V) then (1 : ℝ) else 0)
              * w ((cliqueEquiv G) C)) := by
    simpa using
      (Finset.sum_equiv (cliqueEquiv G).symm
        (s := (Finset.univ : Finset (Fin (allCliques G).card)))
        (t := (Finset.univ : Finset (allCliques G)))
        (f := fun j =>
          (if (vertexEquiv V).symm i ∈ ((cliqueEquiv G).symm j).val then (1 : ℝ) else 0)
            * w j)
        (g := fun C =>
          (if (vertexEquiv V).symm i ∈ (C : Finset V) then (1 : ℝ) else 0)
            * w ((cliqueEquiv G) C))
        (by intro j; simp)
        (by intro j _; simp))
  have hweights :
      (Finset.univ : Finset (allCliques G)).sum
          (fun C => (if (vertexEquiv V).symm i ∈ (C : Finset V) then (1 : ℝ) else 0)
            * w ((cliqueEquiv G) C))
        = (Finset.univ : Finset (allCliques G)).sum
            (fun C => (if (vertexEquiv V).symm i ∈ (C : Finset V) then (1 : ℝ) else 0)
              * weightsOfVector G w C) := by
    refine Finset.sum_congr rfl ?_
    intro C hC
    simp [weightsOfVector, C.property]
  have hattach :
      (Finset.univ : Finset (allCliques G)).sum
          (fun C => (if (vertexEquiv V).symm i ∈ (C : Finset V) then (1 : ℝ) else 0)
            * weightsOfVector G w C)
        = (allCliques G).sum
            (fun C => (if (vertexEquiv V).symm i ∈ C then (1 : ℝ) else 0)
              * weightsOfVector G w C) := by
    have h := (Finset.sum_attach (s := allCliques G)
      (f := fun C => (if (vertexEquiv V).symm i ∈ C then (1 : ℝ) else 0)
        * weightsOfVector G w C))
    rw [Finset.attach_eq_univ] at h
    exact h
  have hfilter :
      (allCliques G).sum
          (fun C => (if (vertexEquiv V).symm i ∈ C then (1 : ℝ) else 0)
            * weightsOfVector G w C)
        = ((allCliques G).filter ((vertexEquiv V).symm i ∈ ·)).sum (weightsOfVector G w) := by
    simpa [ite_mul, zero_mul, one_mul] using
      (Finset.sum_filter (s := allCliques G) (p := fun C => (vertexEquiv V).symm i ∈ C)
        (f := weightsOfVector G w)).symm
  calc
    (coverMatrixReal G).mulVec w i
        = ∑ j : Fin (allCliques G).card,
            (if (vertexEquiv V).symm i ∈ ((cliqueEquiv G).symm j).val then (1 : ℝ) else 0)
              * w j := hmul
    _ = (Finset.univ : Finset (allCliques G)).sum
            (fun C => (if (vertexEquiv V).symm i ∈ (C : Finset V) then (1 : ℝ) else 0)
              * w ((cliqueEquiv G) C)) := hsum
    _ = (Finset.univ : Finset (allCliques G)).sum
            (fun C => (if (vertexEquiv V).symm i ∈ (C : Finset V) then (1 : ℝ) else 0)
              * weightsOfVector G w C) := hweights
    _ = (allCliques G).sum
            (fun C => (if (vertexEquiv V).symm i ∈ C then (1 : ℝ) else 0)
              * weightsOfVector G w C) := hattach
    _ = ((allCliques G).filter ((vertexEquiv V).symm i ∈ ·)).sum (weightsOfVector G w) := hfilter

theorem FullCliqueCover.mulVec_toVector {G : SimpleGraph V} (cover : FullCliqueCover G)
    (i : Fin (Fintype.card V)) :
    (coverMatrixReal G).mulVec cover.toVector i =
      ((allCliques G).filter ((vertexEquiv V).symm i ∈ ·)).sum cover.weights := by
  classical
  have hsum := mulVec_eq_sum_weights (G := G) (w := cover.toVector) (i := i)
  have hweights :
      ((allCliques G).filter ((vertexEquiv V).symm i ∈ ·)).sum (weightsOfVector G cover.toVector) =
        ((allCliques G).filter ((vertexEquiv V).symm i ∈ ·)).sum cover.weights := by
    refine Finset.sum_congr rfl ?_
    intro C hC
    have hC' : C ∈ allCliques G := Finset.mem_of_mem_filter _ hC
    simp [weightsOfVector, FullCliqueCover.toVector, hC', Equiv.symm_apply_apply]
  simpa [hweights] using hsum

def fullCoverFeasibleSet (G : SimpleGraph V) :
    Set (Fin (allCliques G).card → ℝ) :=
  {w | (∀ j, 0 ≤ w j) ∧ (∀ i, 1 ≤ (coverMatrixReal G).mulVec w i)}

theorem FullCliqueCover.toVector_feasible {G : SimpleGraph V} (cover : FullCliqueCover G) :
    cover.toVector ∈ fullCoverFeasibleSet G := by
  classical
  refine ⟨?nonneg, ?covers⟩
  · intro j
    have hj : ((cliqueEquiv G).symm j).val ∈ allCliques G := ((cliqueEquiv G).symm j).property
    simpa [FullCliqueCover.toVector] using cover.nonneg _ hj
  · intro i
    have hcov := cover.covers ((vertexEquiv V).symm i)
    simpa [FullCliqueCover.mulVec_toVector] using hcov

noncomputable def FullCliqueCover.ofVector (G : SimpleGraph V)
    (w : Fin (allCliques G).card → ℝ)
    (h_nonneg : ∀ j, 0 ≤ w j)
    (h_cover : ∀ i, 1 ≤ (coverMatrixReal G).mulVec w i) :
    FullCliqueCover G := by
  classical
  let weights := weightsOfVector G w
  refine ⟨weights, ?nonneg, ?covers⟩
  · intro C hC
    simp [weights, weightsOfVector, hC, h_nonneg]
  · intro v
    have hcov := h_cover ((vertexEquiv V) v)
    have hsum :
        (coverMatrixReal G).mulVec w ((vertexEquiv V) v) =
          ((allCliques G).filter (v ∈ ·)).sum weights := by
      simpa [weights] using
        (mulVec_eq_sum_weights (G := G) (w := w) (i := (vertexEquiv V) v))
    simpa [hsum] using hcov

theorem FullCliqueCover.toVector_ofVector {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ)
    (h_nonneg : ∀ j, 0 ≤ w j)
    (h_cover : ∀ i, 1 ≤ (coverMatrixReal G).mulVec w i) :
    (FullCliqueCover.ofVector G w h_nonneg h_cover).toVector = w := by
  classical
  ext j
  simp [FullCliqueCover.ofVector, FullCliqueCover.toVector, weightsOfVector]

noncomputable def fullCoverObjective {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ) : ℝ :=
  Finset.univ.sum w

noncomputable def fullCoverBound (_ : SimpleGraph V) : ℝ :=
  Fintype.card V

def fullCoverBoundedSet (G : SimpleGraph V) :
    Set (Fin (allCliques G).card → ℝ) :=
  {w | w ∈ fullCoverFeasibleSet G ∧ fullCoverObjective w ≤ fullCoverBound G}

private lemma continuous_mulVec_apply {G : SimpleGraph V} (i : Fin (Fintype.card V)) :
    Continuous fun w : Fin (allCliques G).card → ℝ =>
      (coverMatrixReal G).mulVec w i := by
  classical
  -- Expand mulVec into a finite sum of continuous functions.
  have hcont :
      ∀ j : Fin (allCliques G).card,
        Continuous fun w : Fin (allCliques G).card → ℝ =>
          (coverMatrixReal G) i j * w j := by
    intro j
    simpa using
      (continuous_const.mul
        (continuous_apply (ι := Fin (allCliques G).card) (A := fun _ => ℝ) j))
  simpa [coverMatrixReal, Matrix.mulVec, dotProduct] using
    (continuous_finset_sum (s := (Finset.univ : Finset (Fin (allCliques G).card)))
      (f := fun j (w : Fin (allCliques G).card → ℝ) => (coverMatrixReal G) i j * w j)
      (by intro j _; simpa using hcont j))

private lemma continuous_fullCoverObjective {G : SimpleGraph V} :
    Continuous fun w : Fin (allCliques G).card → ℝ => fullCoverObjective w := by
  classical
  simpa [fullCoverObjective] using
    (continuous_finset_sum (s := (Finset.univ : Finset (Fin (allCliques G).card)))
      (f := fun j (w : Fin (allCliques G).card → ℝ) => w j)
      (by
        intro j _
        simpa using
          (continuous_apply (ι := Fin (allCliques G).card) (A := fun _ => ℝ) j)))

private lemma isClosed_fullCoverFeasibleSet {G : SimpleGraph V} :
    IsClosed (fullCoverFeasibleSet G) := by
  classical
  -- Closedness of nonnegativity constraints.
  have hnonneg : IsClosed {w : Fin (allCliques G).card → ℝ | ∀ j, 0 ≤ w j} := by
    have hclosed :
        IsClosed (⋂ j : Fin (allCliques G).card,
          {w : Fin (allCliques G).card → ℝ | 0 ≤ w j}) := by
      refine isClosed_iInter ?_
      intro j
      simpa using
        (isClosed_le continuous_const
          (continuous_apply (ι := Fin (allCliques G).card) (A := fun _ => ℝ) j))
    simpa [Set.setOf_forall] using hclosed
  -- Closedness of cover constraints.
  have hcover :
      IsClosed {w : Fin (allCliques G).card → ℝ | ∀ i, 1 ≤ (coverMatrixReal G).mulVec w i} := by
    have hclosed :
        IsClosed (⋂ i : Fin (Fintype.card V),
          {w : Fin (allCliques G).card → ℝ | 1 ≤ (coverMatrixReal G).mulVec w i}) := by
      refine isClosed_iInter ?_
      intro i
      simpa using (isClosed_le continuous_const (continuous_mulVec_apply (G := G) i))
    simpa [Set.setOf_forall] using hclosed
  simpa [fullCoverFeasibleSet, Set.setOf_and] using hnonneg.inter hcover

private lemma isClosed_fullCoverBoundedSet {G : SimpleGraph V} :
    IsClosed (fullCoverBoundedSet G) := by
  classical
  have hfeas : IsClosed (fullCoverFeasibleSet G) := isClosed_fullCoverFeasibleSet (G := G)
  have hbound :
      IsClosed {w : Fin (allCliques G).card → ℝ | fullCoverObjective w ≤ fullCoverBound G} :=
    isClosed_le continuous_fullCoverObjective continuous_const
  simpa [fullCoverBoundedSet, Set.setOf_and] using hfeas.inter hbound

private lemma fullCoverBoundedSet_subset_Icc {G : SimpleGraph V} :
    fullCoverBoundedSet G ⊆
      Set.Icc (fun _ : Fin (allCliques G).card => (0 : ℝ))
        (fun _ => fullCoverBound G) := by
  intro w hw
  rcases hw with ⟨⟨h_nonneg, _⟩, hsum⟩
  refine ⟨?hle0, ?hleM⟩
  · intro j
    exact h_nonneg j
  · intro j
    have hle : w j ≤ fullCoverObjective w := by
      have := Finset.single_le_sum (f := fun j => w j) (s := Finset.univ)
        (fun j _ => h_nonneg j) (Finset.mem_univ j)
      simpa [fullCoverObjective] using this
    exact hle.trans hsum

private lemma fullCoverBoundedSet_compact {G : SimpleGraph V} :
    IsCompact (fullCoverBoundedSet G) := by
  classical
  refine IsCompact.of_isClosed_subset
    (s := Set.Icc (fun _ : Fin (allCliques G).card => (0 : ℝ))
      (fun _ => fullCoverBound G))
    (t := fullCoverBoundedSet G) ?_ (isClosed_fullCoverBoundedSet (G := G)) ?_
  · simpa using
      (isCompact_Icc (a := fun _ : Fin (allCliques G).card => (0 : ℝ))
        (b := fun _ => fullCoverBound G))
  · exact fullCoverBoundedSet_subset_Icc (G := G)

private lemma fullCoverBoundedSet_nonempty {G : SimpleGraph V} [Nonempty V] :
    (fullCoverBoundedSet G).Nonempty := by
  classical
  -- Use the explicit singleton cover.
  let cliques : Finset (Finset V) := Finset.univ.image (fun v => {v})
  let weights : Finset V → ℝ := fun _ => 1
  let cover : FractionalCliqueCover G :=
    ⟨cliques, weights,
      (fun C hC => by
        rw [Finset.mem_image] at hC
        obtain ⟨v, _, rfl⟩ := hC
        rw [isClique_iff, Set.Pairwise]
        intro x hx y hy hxy
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
        exact (hxy (hx.trans hy.symm)).elim),
      (fun _ _ => by norm_num),
      (fun v => by
        have hv : {v} ∈ cliques := Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
        have hmem : {v} ∈ cliques.filter (v ∈ ·) := by
          simp only [Finset.mem_filter, hv, Finset.mem_singleton, true_and]
        calc (cliques.filter (v ∈ ·)).sum weights
          ≥ weights {v} := Finset.single_le_sum (fun _ _ => by norm_num) hmem
          _ = 1 := rfl)⟩
  let full := cover.toFull
  refine ⟨full.toVector, ?_⟩
  have hfeas : full.toVector ∈ fullCoverFeasibleSet G := full.toVector_feasible
  have hweight : full.totalWeight = Fintype.card V := by
    have hcover_weight : cover.totalWeight = Fintype.card V := by
      unfold FractionalCliqueCover.totalWeight
      have hcard : cliques.card = Fintype.card V := by
        have hinj : Function.Injective (fun v : V => ({v} : Finset V)) := by
          intro v₁ v₂ h
          simpa using h
        simpa [cliques] using (Finset.card_image_of_injective _ hinj)
      calc cover.cliques.sum cover.weights
          = cliques.sum (fun _ => (1 : ℝ)) := by rfl
        _ = cliques.card • (1 : ℝ) := Finset.sum_const 1
        _ = (cliques.card : ℝ) := by ring
        _ = (Fintype.card V : ℝ) := by rw [hcard]
    have hfull : full.totalWeight = cover.totalWeight := by
      simpa [full] using (FractionalCliqueCover.toFull_totalWeight (cover := cover))
    exact hfull.trans hcover_weight
  have hsum_eq : fullCoverObjective full.toVector = full.totalWeight := by
    simp [FullCliqueCover.totalWeight_eq_sum, fullCoverObjective]
  have hsum : fullCoverObjective full.toVector ≤ fullCoverBound G := by
    simp [fullCoverBound, hsum_eq, hweight]
  exact ⟨hfeas, hsum⟩

private lemma exists_fullCover_minimizer {G : SimpleGraph V} [Nonempty V] :
    ∃ w ∈ fullCoverBoundedSet G,
      IsMinOn fullCoverObjective (fullCoverBoundedSet G) w := by
  have hcompact : IsCompact (fullCoverBoundedSet G) := fullCoverBoundedSet_compact (G := G)
  have hnonempty : (fullCoverBoundedSet G).Nonempty := fullCoverBoundedSet_nonempty (G := G)
  have hcont : ContinuousOn fullCoverObjective (fullCoverBoundedSet G) :=
    (continuous_fullCoverObjective.continuousOn)
  obtain ⟨w, hw, hwmin⟩ := hcompact.exists_isMinOn hnonempty hcont
  exact ⟨w, hw, hwmin⟩

noncomputable def weightSupport {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ) : Finset (Fin (allCliques G).card) :=
  Finset.filter (fun j => w j ≠ 0) Finset.univ

noncomputable def tightVertices {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ) : Finset (Fin (Fintype.card V)) :=
  Finset.filter (fun i => (coverMatrixReal G).mulVec w i = 1) Finset.univ

noncomputable def restrictWeight {G : SimpleGraph V}
    (S : Finset (Fin (allCliques G).card)) (w : Fin (allCliques G).card → ℝ) :
    Fin S.card → ℝ :=
  fun j => w ((Finset.equivFin S).symm j)

noncomputable def extendWeight {G : SimpleGraph V}
    (S : Finset (Fin (allCliques G).card)) (u : Fin S.card → ℝ) :
    Fin (allCliques G).card → ℝ :=
  fun j => if h : j ∈ S then u (Finset.equivFin S ⟨j, h⟩) else 0

private lemma restrict_extend_weight {G : SimpleGraph V}
    (S : Finset (Fin (allCliques G).card)) (u : Fin S.card → ℝ) :
    restrictWeight S (extendWeight S u) = u := by
  classical
  ext j
  simp [restrictWeight, extendWeight]

private lemma extend_weight_eq_zero {G : SimpleGraph V}
    (S : Finset (Fin (allCliques G).card)) (u : Fin S.card → ℝ)
    (j : Fin (allCliques G).card) (hj : j ∉ S) :
    extendWeight S u j = 0 := by
  simp [extendWeight, hj]

private lemma weightSupport_extend_subset {G : SimpleGraph V}
    (S : Finset (Fin (allCliques G).card)) (u : Fin S.card → ℝ) :
    weightSupport (extendWeight S u) ⊆ S := by
  classical
  intro j hj
  have hj' : extendWeight S u j ≠ 0 := by
    simpa [weightSupport] using (Finset.mem_filter.mp hj).2
  by_contra hjS
  exact hj' (extend_weight_eq_zero (S := S) (u := u) (j := j) hjS)

private lemma mem_tightVertices_iff {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ) (i : Fin (Fintype.card V)) :
    i ∈ tightVertices (G := G) w ↔ (coverMatrixReal G).mulVec w i = 1 := by
  classical
  simp [tightVertices]

private lemma weightSupport_pos {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ)
    (hw : w ∈ fullCoverFeasibleSet G)
    {j : Fin (allCliques G).card} (hj : j ∈ weightSupport w) : 0 < w j := by
  have hnonneg : 0 ≤ w j := hw.1 j
  have hne : w j ≠ 0 := (Finset.mem_filter.mp hj).2
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

private lemma not_mem_tightVertices_lt {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ)
    (hw : w ∈ fullCoverFeasibleSet G)
    {i : Fin (Fintype.card V)} (hi : i ∉ tightVertices (G := G) w) :
    1 < (coverMatrixReal G).mulVec w i := by
  have hcov : 1 ≤ (coverMatrixReal G).mulVec w i := hw.2 i
  have hneq : (coverMatrixReal G).mulVec w i ≠ 1 := by
    intro h
    exact hi (by simp [tightVertices, h])
  exact lt_of_le_of_ne hcov hneq.symm

private lemma exists_pos_of_sum_zero {n : ℕ} (y : Fin n → ℝ)
    (hne : y ≠ 0) (hsum : (Finset.univ : Finset (Fin n)).sum y = 0) :
    ∃ j, 0 < y j := by
  classical
  by_contra hpos
  have hnonpos : ∀ j ∈ (Finset.univ : Finset (Fin n)), y j ≤ 0 := by
    intro j _
    have : ¬ 0 < y j := by
      intro hj
      exact hpos ⟨j, hj⟩
    exact le_of_not_gt this
  have hzero :
      ∀ j ∈ (Finset.univ : Finset (Fin n)), y j = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hsum
    simpa using this
  have : y = 0 := by
    funext j
    exact hzero j (Finset.mem_univ j)
  exact hne this

private lemma exists_neg_of_sum_zero {n : ℕ} (y : Fin n → ℝ)
    (hne : y ≠ 0) (hsum : (Finset.univ : Finset (Fin n)).sum y = 0) :
    ∃ j, y j < 0 := by
  have hpos := exists_pos_of_sum_zero (n := n) (-y) (by
    intro h
    apply hne
    funext j
    have := congrArg (fun f => f j) h
    simpa using this) ?_
  · rcases hpos with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simpa using (neg_pos.mp hj)
  · simpa [Finset.sum_neg_distrib] using congrArg Neg.neg hsum

private lemma sum_extendWeight {G : SimpleGraph V}
    (S : Finset (Fin (allCliques G).card)) (u : Fin S.card → ℝ) :
    (Finset.univ : Finset (Fin (allCliques G).card)).sum (extendWeight S u) =
      (Finset.univ : Finset (Fin S.card)).sum u := by
  classical
  have hsum :
      (Finset.univ : Finset (Fin S.card)).sum u =
        (S.attach).sum (fun j => extendWeight S u j) := by
    simpa using
      (Finset.sum_equiv (Finset.equivFin S).symm
        (s := (Finset.univ : Finset (Fin S.card)))
        (t := S.attach)
        (f := fun j => u j)
        (g := fun j => extendWeight S u j)
        (by intro j; simp)
        (by intro j _; simp [extendWeight]))
  have hattach :
      (S.attach).sum (fun j => extendWeight S u j) =
        S.sum (fun j => extendWeight S u j) := by
    simpa using (Finset.sum_attach (s := S) (f := fun j => extendWeight S u j))
  have hsum_univ :
      (Finset.univ : Finset (Fin (allCliques G).card)).sum (extendWeight S u) =
        S.sum (fun j => extendWeight S u j) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro j _
      exact Finset.mem_univ j
    · intro j hjS hjnot
      simp [extend_weight_eq_zero (S := S) (u := u) (j := j) hjnot]
  calc
    (Finset.univ : Finset (Fin (allCliques G).card)).sum (extendWeight S u)
        = S.sum (fun j => extendWeight S u j) := hsum_univ
    _ = (S.attach).sum (fun j => extendWeight S u j) := hattach.symm
    _ = (Finset.univ : Finset (Fin S.card)).sum u := hsum.symm

noncomputable def posIndexSet {n : ℕ} (y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.filter (fun j => 0 < y j) Finset.univ

private lemma posIndexSet_nonempty_of_sum_zero {n : ℕ} (y : Fin n → ℝ)
    (hne : y ≠ 0) (hsum : (Finset.univ : Finset (Fin n)).sum y = 0) :
    (posIndexSet y).Nonempty := by
  classical
  obtain ⟨j, hj⟩ := exists_pos_of_sum_zero (n := n) y hne hsum
  refine ⟨j, ?_⟩
  simp [posIndexSet, hj]

noncomputable def minPosRatio {n : ℕ} (w y : Fin n → ℝ)
    (hpos : (posIndexSet y).Nonempty) : ℝ :=
  ((posIndexSet y).image (fun j => w j / y j)).min'
    (Finset.Nonempty.image hpos _)

private lemma minPosRatio_le {n : ℕ} (w y : Fin n → ℝ)
    (hpos : (posIndexSet y).Nonempty) {j : Fin n} (hj : j ∈ posIndexSet y) :
    minPosRatio w y hpos ≤ w j / y j := by
  classical
  have hj' : w j / y j ∈ (posIndexSet y).image (fun j => w j / y j) := by
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  exact Finset.min'_le _ _ hj'

private lemma minPosRatio_pos {n : ℕ} (w y : Fin n → ℝ)
    (hpos : (posIndexSet y).Nonempty)
    (hwpos : ∀ j ∈ posIndexSet y, 0 < w j) :
    0 < minPosRatio w y hpos := by
  classical
  have hmem :
      minPosRatio w y hpos ∈ (posIndexSet y).image (fun j => w j / y j) := by
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨j, hj, hj_eq⟩
  have hy : 0 < y j := by
    simpa [posIndexSet] using hj
  have hw : 0 < w j := hwpos j hj
  have hratio : 0 < w j / y j := div_pos hw hy
  simpa [hj_eq] using hratio

private lemma restrictWeight_pos {G : SimpleGraph V}
    (w : Fin (allCliques G).card → ℝ)
    (hw : w ∈ fullCoverFeasibleSet G)
    (j : Fin (weightSupport w).card) :
    0 < restrictWeight (weightSupport w) w j := by
  classical
  have hj : ((Finset.equivFin (weightSupport w)).symm j).1 ∈ weightSupport w :=
    ((Finset.equivFin (weightSupport w)).symm j).property
  simpa [restrictWeight] using (weightSupport_pos w hw hj)

noncomputable def coverMatrixSub {G : SimpleGraph V}
    (I : Finset (Fin (Fintype.card V)))
    (S : Finset (Fin (allCliques G).card)) :
    Matrix (Fin I.card) (Fin S.card) ℚ :=
  fun i j =>
    coverMatrix G ((Finset.equivFin I).symm i)
      ((Finset.equivFin S).symm j)

private lemma coverMatrixSub_mulVec_eq {G : SimpleGraph V}
    (I : Finset (Fin (Fintype.card V)))
    (S : Finset (Fin (allCliques G).card))
    (w : Fin (allCliques G).card → ℝ) (i : Fin I.card) :
    ((coverMatrixSub (G := G) I S).map (Rat.castHom ℝ)).mulVec (restrictWeight S w) i =
      S.sum
        (fun j => (coverMatrixReal G) ((Finset.equivFin I).symm i) j * w j) := by
  classical
  have hsum :
      (∑ j : Fin S.card,
          (coverMatrixReal G) ((Finset.equivFin I).symm i)
              ((Finset.equivFin S).symm j) *
            w ((Finset.equivFin S).symm j)) =
        (S.attach).sum
          (fun j =>
            (coverMatrixReal G) ((Finset.equivFin I).symm i) j * w j) := by
    simpa using
      (Finset.sum_equiv (Finset.equivFin S).symm
        (s := (Finset.univ : Finset (Fin S.card)))
        (t := S.attach)
        (f := fun j =>
          (coverMatrixReal G) ((Finset.equivFin I).symm i)
              ((Finset.equivFin S).symm j) *
            w ((Finset.equivFin S).symm j))
        (g := fun j =>
          (coverMatrixReal G) ((Finset.equivFin I).symm i) j * w j)
        (by intro j; simp)
        (by intro j _; rfl))
  have hattach :
      (S.attach).sum
          (fun j =>
            (coverMatrixReal G) ((Finset.equivFin I).symm i) j * w j) =
        S.sum
          (fun j =>
            (coverMatrixReal G) ((Finset.equivFin I).symm i) j * w j) := by
    have h := (Finset.sum_attach (s := S)
      (f := fun j =>
        (coverMatrixReal G) ((Finset.equivFin I).symm i) j * w j))
    exact h
  calc
    ((coverMatrixSub (G := G) I S).map (Rat.castHom ℝ)).mulVec (restrictWeight S w) i
        = ∑ j : Fin S.card,
            (coverMatrixReal G) ((Finset.equivFin I).symm i)
                ((Finset.equivFin S).symm j) *
              w ((Finset.equivFin S).symm j) := by
              simp [coverMatrixSub, coverMatrixReal, restrictWeight, Matrix.mulVec, dotProduct]
    _ = (S.attach).sum
          (fun j =>
            (coverMatrixReal G) ((Finset.equivFin I).symm i) j * w j) := hsum
    _ = S.sum
          (fun j =>
            (coverMatrixReal G) ((Finset.equivFin I).symm i) j * w j) := hattach

private lemma coverMatrixReal_mulVec_eq_sum_support {G : SimpleGraph V}
    (S : Finset (Fin (allCliques G).card))
    (w : Fin (allCliques G).card → ℝ)
    (hS : ∀ j, j ∉ S → w j = 0)
    (i : Fin (Fintype.card V)) :
    (coverMatrixReal G).mulVec w i =
      S.sum (fun j => (coverMatrixReal G) i j * w j) := by
  classical
  have hsum :
      (∑ j ∈ S, (coverMatrixReal G) i j * w j) =
        ∑ j ∈ (Finset.univ : Finset (Fin (allCliques G).card)),
          (coverMatrixReal G) i j * w j := by
    refine Finset.sum_subset ?_ ?_
    · intro j _
      exact Finset.mem_univ j
    · intro j hjS hjnot
      simp [hS j hjnot]
  simpa [coverMatrixReal, Matrix.mulVec, dotProduct] using hsum.symm

private lemma exists_minimizer_min_support {G : SimpleGraph V} [Nonempty V] :
    ∃ w, w ∈ fullCoverBoundedSet G ∧
      IsMinOn fullCoverObjective (fullCoverBoundedSet G) w ∧
      ∀ z, z ∈ fullCoverBoundedSet G →
        IsMinOn fullCoverObjective (fullCoverBoundedSet G) z →
          (weightSupport w).card ≤ (weightSupport z).card := by
  classical
  obtain ⟨w0, hw0, hw0min⟩ := exists_fullCover_minimizer (G := G)
  let minimizers : Set (Fin (allCliques G).card → ℝ) :=
    {w | w ∈ fullCoverBoundedSet G ∧
      IsMinOn fullCoverObjective (fullCoverBoundedSet G) w}
  have hmin_nonempty : minimizers.Nonempty := ⟨w0, ⟨hw0, hw0min⟩⟩
  let P := fun k => ∃ w ∈ minimizers, (weightSupport w).card = k
  have hP_exists : ∃ k, P k := by
    refine ⟨(weightSupport w0).card, ?_⟩
    exact ⟨w0, ⟨hw0, hw0min⟩, rfl⟩
  let k0 := Nat.find hP_exists
  obtain ⟨w, hwmin, hcard⟩ := Nat.find_spec hP_exists
  refine ⟨w, hwmin.1, hwmin.2, ?_⟩
  intro z hz hzmin
  have hzP : P (weightSupport z).card := ⟨z, ⟨hz, hzmin⟩, rfl⟩
  have hle := (Nat.find_le (h := hP_exists) hzP)
  exact hcard.symm ▸ hle

private lemma fullCoverObjective_extendWeight {G : SimpleGraph V}
    (S : Finset (Fin (allCliques G).card)) (u : Fin S.card → ℝ) :
    fullCoverObjective (extendWeight S u) =
      (Finset.univ : Finset (Fin S.card)).sum u := by
  classical
  simpa [fullCoverObjective] using sum_extendWeight (S := S) (u := u)

private lemma coverMatrixReal_mulVec_extend_eq {G : SimpleGraph V}
    (I : Finset (Fin (Fintype.card V)))
    (S : Finset (Fin (allCliques G).card)) (u : Fin S.card → ℝ) (i : Fin I.card) :
    (coverMatrixReal G).mulVec (extendWeight S u) ((Finset.equivFin I).symm i) =
      ((coverMatrixSub (G := G) I S).map (Rat.castHom ℝ)).mulVec u i := by
  classical
  have hsum_sub := coverMatrixSub_mulVec_eq (G := G) (I := I) (S := S)
    (w := extendWeight S u) (i := i)
  have hsum_full :
      (coverMatrixReal G).mulVec (extendWeight S u) ((Finset.equivFin I).symm i) =
        S.sum
          (fun j =>
            (coverMatrixReal G) ((Finset.equivFin I).symm i) j * extendWeight S u j) := by
    refine coverMatrixReal_mulVec_eq_sum_support (G := G) (S := S) (w := extendWeight S u)
      (i := (Finset.equivFin I).symm i) ?_
    intro j hj
    exact extend_weight_eq_zero (S := S) (u := u) (j := j) hj
  have hsum_sub' :
      ((coverMatrixSub (G := G) I S).map (Rat.castHom ℝ)).mulVec u i =
        S.sum
          (fun j =>
            (coverMatrixReal G) ((Finset.equivFin I).symm i) j * extendWeight S u j) := by
    simpa [restrict_extend_weight, extendWeight] using hsum_sub
  exact hsum_full.trans hsum_sub'.symm

private lemma fullCoverObjective_eq_min_of_minimizer {G : SimpleGraph V} [Nonempty V]
    (w : Fin (allCliques G).card → ℝ)
    (hw : w ∈ fullCoverBoundedSet G)
    (hwmin : IsMinOn fullCoverObjective (fullCoverBoundedSet G) w) :
    fullCoverObjective w = fractionalCliqueCoverNumber G := by
  classical
  -- Upper bound via the full cover corresponding to w.
  have hw_feas : w ∈ fullCoverFeasibleSet G := hw.1
  let hw_cover : FullCliqueCover G :=
    FullCliqueCover.ofVector G w hw_feas.1 hw_feas.2
  have hw_vec : hw_cover.toVector = w := by
    simpa [hw_cover] using
      (FullCliqueCover.toVector_ofVector (G := G) (w := w) hw_feas.1 hw_feas.2)
  have hw_weight : fullCoverObjective w = hw_cover.totalWeight := by
    have hsum := FullCliqueCover.totalWeight_eq_sum (cover := hw_cover)
    simpa [fullCoverObjective, hw_vec] using hsum.symm
  have hle : fractionalCliqueCoverNumber G ≤ fullCoverObjective w := by
    unfold fractionalCliqueCoverNumber
    have hbdd : BddBelow (Set.range (fun c : FractionalCliqueCover G => c.totalWeight)) := by
      use 0
      intro _ ⟨c, hc⟩
      rw [← hc]
      exact c.totalWeight_nonneg
    let hcover : FractionalCliqueCover G := hw_cover.toCover
    have hweight : hcover.totalWeight = hw_cover.totalWeight := by
      simp [hcover, hw_cover, FullCliqueCover.toCover, FullCliqueCover.totalWeight,
        FractionalCliqueCover.totalWeight]
    have hle' : (⨅ c : FractionalCliqueCover G, c.totalWeight) ≤ hcover.totalWeight :=
      ciInf_le hbdd hcover
    exact hle'.trans (by simp [hweight, hw_weight])
  -- Lower bound: any fractional cover has weight ≥ fullCoverObjective w.
  have hge : fullCoverObjective w ≤ fractionalCliqueCoverNumber G := by
    unfold fractionalCliqueCoverNumber
    refine le_ciInf ?_
    intro cover
    let hfull : FullCliqueCover G := cover.toFull
    have hsum_eq : fullCoverObjective hfull.toVector = hfull.totalWeight := by
      have hsum := FullCliqueCover.totalWeight_eq_sum (cover := hfull)
      simpa [fullCoverObjective] using hsum.symm
    have hweight : hfull.totalWeight = cover.totalWeight := by
      simpa [hfull] using (FractionalCliqueCover.toFull_totalWeight (cover := cover))
    by_cases hbound : fullCoverObjective hfull.toVector ≤ fullCoverBound G
    · have hvec : hfull.toVector ∈ fullCoverBoundedSet G :=
        ⟨hfull.toVector_feasible, hbound⟩
      have hmin := hwmin hvec
      exact (hmin.trans_eq hsum_eq).trans_eq hweight
    · have hwbound : fullCoverObjective w ≤ fullCoverBound G := hw.2
      have hlt : fullCoverBound G < fullCoverObjective hfull.toVector := lt_of_not_ge hbound
      have hlt' : fullCoverBound G < cover.totalWeight := by
        simpa [hsum_eq, hweight] using hlt
      exact le_trans hwbound (le_of_lt hlt')
  exact le_antisymm hge hle

open ConeProgramming

noncomputable def numCliques (G : SimpleGraph V) : ℕ := (allCliques G).card
def numVertices : ℕ := Fintype.card V

noncomputable def coverLP (G : SimpleGraph V) :
    ConeProgramming.RationalLP (Fintype.card V) (numCliques G + Fintype.card V) where
  A := fun i =>
    Fin.addCases (fun j => coverMatrix G i j) (fun j => if j = i then -1 else 0)
  b := fun _ => 1
  c := fun j => Fin.addCases (fun _ => (-1 : ℚ)) (fun _ => 0) j

private def weightPart {m n : ℕ} (x : Fin (m + n) → ℝ) : Fin m → ℝ :=
  fun j => x (Fin.castAdd n j)

private def slackPart {m n : ℕ} (x : Fin (m + n) → ℝ) : Fin n → ℝ :=
  fun j => x (Fin.natAdd m j)

private def assemble {m n : ℕ} (w : Fin m → ℝ) (s : Fin n → ℝ) : Fin (m + n) → ℝ :=
  Fin.addCases w s

private lemma assemble_weightPart {m n : ℕ} (w : Fin m → ℝ) (s : Fin n → ℝ) :
    weightPart (assemble w s) = w := by
  funext j
  simp [weightPart, assemble]

private lemma assemble_slackPart {m n : ℕ} (w : Fin m → ℝ) (s : Fin n → ℝ) :
    slackPart (assemble w s) = s := by
  funext j
  simp [slackPart, assemble]

private lemma assemble_eta {m n : ℕ} (x : Fin (m + n) → ℝ) :
    assemble (weightPart x) (slackPart x) = x := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [assemble, weightPart]
  · simp [assemble, slackPart]

private lemma coverLP_mulVec {G : SimpleGraph V}
    (w : Fin (numCliques G) → ℝ) (s : Fin (Fintype.card V) → ℝ)
    (i : Fin (Fintype.card V)) :
    (coverLP G).toLP.A.mulVec (assemble w s) i =
      (coverMatrixReal G).mulVec w i - s i := by
  classical
  calc
    (coverLP G).toLP.A.mulVec (assemble w s) i
        = (∑ j : Fin (numCliques G), (coverMatrixReal G) i j * w j) +
            ∑ j : Fin (Fintype.card V), (↑(if j = i then (-1 : ℚ) else 0) : ℝ) * s j := by
              simp [Matrix.mulVec, dotProduct, coverLP, ConeProgramming.RationalLP.toLP, assemble,
                coverMatrixReal, Fin.sum_univ_add]
    _ = (coverMatrixReal G).mulVec w i - s i := by
          have hsum :
              (∑ j : Fin (Fintype.card V),
                    (↑(if j = i then (-1 : ℚ) else 0) : ℝ) * s j) = -s i := by
            have hsum' :
                (∑ j : Fin (Fintype.card V),
                      (↑(if j = i then (-1 : ℚ) else 0) : ℝ) * s j) =
                  (↑(if i = i then (-1 : ℚ) else 0) : ℝ) * s i := by
              refine Fintype.sum_eq_single i ?_
              intro j hji
              simp [hji]
            simpa using hsum'
          calc
            (∑ j : Fin (numCliques G), (coverMatrixReal G) i j * w j) +
                ∑ j : Fin (Fintype.card V),
                  (↑(if j = i then (-1 : ℚ) else 0) : ℝ) * s j
                = (∑ j : Fin (numCliques G), (coverMatrixReal G) i j * w j) + (-s i) := by
                    simp [hsum]
            _ = (coverMatrixReal G).mulVec w i - s i := by
                  have hmul :
                      (coverMatrixReal G).mulVec w i =
                        ∑ j : Fin (numCliques G), (coverMatrixReal G) i j * w j := by
                    rfl
                  calc
                    (∑ j : Fin (numCliques G), (coverMatrixReal G) i j * w j) + (-s i)
                        = (coverMatrixReal G).mulVec w i + (-s i) := by
                            rw [hmul]
                    _ = (coverMatrixReal G).mulVec w i - s i := by
                          simp [sub_eq_add_neg]

private lemma coverLP_objective {G : SimpleGraph V} (w : Fin (numCliques G) → ℝ)
    (s : Fin (Fintype.card V) → ℝ) :
    (coverLP G).toLP.objective (assemble w s) = -fullCoverObjective w := by
  classical
  have hsum :
      ∑ j, (coverLP G).toLP.c j * assemble w s j =
        (∑ j : Fin (numCliques G), (-1 : ℝ) * w j) +
          ∑ _j : Fin (Fintype.card V), 0 * s _j := by
    simpa [coverLP, ConeProgramming.RationalLP.toLP, assemble] using
      (Fin.sum_univ_add (a := numCliques G) (b := Fintype.card V)
        (f := fun j => (coverLP G).toLP.c j * assemble w s j))
  calc
    (coverLP G).toLP.objective (assemble w s)
        = ∑ j, (coverLP G).toLP.c j * assemble w s j := by
              simp [LP.objective, dotProduct]
    _ = (∑ j : Fin (numCliques G), (-1 : ℝ) * w j) +
          ∑ _j : Fin (Fintype.card V), 0 * s _j := hsum
    _ = -fullCoverObjective w := by
          simp [fullCoverObjective]; rfl

theorem fractionalCliqueCoverNumber_rational {G : SimpleGraph V} [Nonempty V] :
    ∃ q : ℚ, fractionalCliqueCoverNumber G = q := by
  classical
  obtain ⟨w0, hw0, hw0min⟩ := exists_fullCover_minimizer (G := G)
  have hw0_val : fullCoverObjective w0 = fractionalCliqueCoverNumber G :=
    fullCoverObjective_eq_min_of_minimizer (G := G) w0 hw0 hw0min
  let s0 : Fin (Fintype.card V) → ℝ :=
    fun i => (coverMatrixReal G).mulVec w0 i - 1
  let x0 : Fin (numCliques G + Fintype.card V) → ℝ := assemble w0 s0
  have hx0_feas : (coverLP G).toLP.isFeasible x0 := by
    constructor
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have hnonneg := hw0.1.1 j
        simpa [x0, assemble] using hnonneg
      · have hcov := hw0.1.2 j
        have hnonneg : 0 ≤ (coverMatrixReal G).mulVec w0 j - 1 := by linarith
        simpa [x0, assemble, s0] using hnonneg
    · ext i
      have hmul := coverLP_mulVec (G := G) w0 s0 i
      simpa [x0, s0, coverLP, ConeProgramming.RationalLP.toLP] using hmul
  have hx0_opt : (coverLP G).isOptimalReal x0 := by
    refine ⟨hx0_feas, ?_⟩
    intro x hx
    -- Extract weights and use minimality of w0
    let w : Fin (numCliques G) → ℝ := weightPart x
    let s : Fin (Fintype.card V) → ℝ := slackPart x
    have hx_nonneg := hx.1
    have hx_eq := hx.2
    have hw_feas : w ∈ fullCoverFeasibleSet G := by
      refine ⟨?_, ?_⟩
      · intro j
        have := hx_nonneg (Fin.castAdd (Fintype.card V) j)
        simpa [w, weightPart] using this
      · intro i
        have hmul := coverLP_mulVec (G := G) w s i
        have hmul_eq : (coverMatrixReal G).mulVec w i - s i = 1 := by
          have hx_eq_i := congrArg (fun f => f i) hx_eq
          have hmul' : (coverLP G).toLP.A.mulVec x i =
              (coverMatrixReal G).mulVec w i - s i := by
            simpa [assemble_eta, w, s] using hmul
          have hx_eq_i' : (coverLP G).toLP.A.mulVec x i = 1 := by
            simpa [ConeProgramming.RationalLP.toLP, coverLP] using hx_eq_i
          linarith
        have hs_nonneg : 0 ≤ s i := by
          have := hx_nonneg (Fin.natAdd (numCliques G) i)
          simpa [s, slackPart] using this
        linarith
    have hmin :
        fractionalCliqueCoverNumber G ≤ fullCoverObjective w := by
      unfold fractionalCliqueCoverNumber
      have hbdd : BddBelow (Set.range (fun c : FractionalCliqueCover G => c.totalWeight)) := by
        refine ⟨0, ?_⟩
        intro _ ⟨c, hc⟩
        rw [← hc]
        exact c.totalWeight_nonneg
      let hfull : FullCliqueCover G :=
        FullCliqueCover.ofVector G w hw_feas.1 hw_feas.2
      have hsum : fullCoverObjective w = hfull.totalWeight := by
        have hvec :
            hfull.toVector = w := by
          simpa using
            (FullCliqueCover.toVector_ofVector (G := G) (w := w) hw_feas.1 hw_feas.2)
        have hsum := FullCliqueCover.totalWeight_eq_sum (cover := hfull)
        simpa [fullCoverObjective, hvec] using hsum.symm
      have hle : (⨅ c : FractionalCliqueCover G, c.totalWeight) ≤ hfull.totalWeight :=
        ciInf_le hbdd hfull.toCover
      simpa [hsum] using hle
    have hobj_w0 : (coverLP G).toLP.objective x0 = -fullCoverObjective w0 := by
      simpa [x0, s0] using (coverLP_objective (G := G) w0 s0)
    have hobj_x :
        (coverLP G).toLP.objective x = -fullCoverObjective w := by
      have hx_decomp : assemble w s = x := by
        simpa [w, s] using (assemble_eta x)
      simpa [hx_decomp] using (coverLP_objective (G := G) w s)
    have hle_obj : -fullCoverObjective w ≤ -fullCoverObjective w0 := by
      have hw0_le : fullCoverObjective w0 ≤ fullCoverObjective w := by
        simpa [hw0_val] using hmin
      linarith
    simpa [hobj_w0, hobj_x] using hle_obj
  obtain ⟨xq, hxq, hobjq⟩ :=
    ConeProgramming.RationalLP.exists_rat_optimal (P := coverLP G) x0 hx0_opt
  have hobjq' :
      (coverLP G).toLP.objective (fun j => (xq j : ℝ)) =
        (coverLP G).toLP.objective x0 := hobjq
  have hq_val : (fractionalCliqueCoverNumber G : ℝ) =
      - (coverLP G).toLP.objective (fun j => (xq j : ℝ)) := by
    have hobj_w0 : (coverLP G).toLP.objective x0 = -fullCoverObjective w0 := by
      simpa [x0, s0] using (coverLP_objective (G := G) w0 s0)
    have hfull : fullCoverObjective w0 = fractionalCliqueCoverNumber G := hw0_val
    linarith
  -- objective for rational xq is rational
  let q : ℚ :=
    Finset.univ.sum (fun j : Fin (numCliques G) =>
      xq (Fin.castAdd (Fintype.card V) j))
  refine ⟨q, ?_⟩
  have hobjq'' :
      (coverLP G).toLP.objective (fun j => (xq j : ℝ)) =
        -(q : ℝ) := by
    classical
    have hsum :=
      (Fin.sum_univ_add (a := numCliques G) (b := Fintype.card V)
        (f := fun j => (coverLP G).toLP.c j * (xq j : ℝ)))
    have hq_cast :
        (q : ℝ) =
          ∑ j : Fin (numCliques G), (xq (Fin.castAdd (Fintype.card V) j) : ℝ) := by
      simp [q, Rat.cast_sum]
    calc
      (coverLP G).toLP.objective (fun j => (xq j : ℝ))
          = ∑ j, (coverLP G).toLP.c j * (xq j : ℝ) := by
              simp [LP.objective, dotProduct]
      _ =
          (∑ j : Fin (numCliques G),
              (-1 : ℝ) * (xq (Fin.castAdd (Fintype.card V) j) : ℝ)) +
            ∑ j : Fin (Fintype.card V),
              0 * (xq (Fin.natAdd (numCliques G) j) : ℝ) := by
            simpa [coverLP, ConeProgramming.RationalLP.toLP] using hsum
      _ = -(q : ℝ) := by
            have hsum_neg :
                ∑ j : Fin (numCliques G), (-1 : ℝ) * (xq (Fin.castAdd (Fintype.card V) j) : ℝ) =
                  (-1 : ℝ) *
                    ∑ j : Fin (numCliques G), (xq (Fin.castAdd (Fintype.card V) j) : ℝ) := by
              exact
                (Finset.mul_sum (s := (Finset.univ : Finset (Fin (numCliques G))))
                  (f := fun j => (xq (Fin.castAdd (Fintype.card V) j) : ℝ))
                  (a := (-1 : ℝ))).symm
            simp [hq_cast]
  have hq_val' : (fractionalCliqueCoverNumber G : ℝ) = (q : ℝ) := by
    simpa [hobjq''] using hq_val
  exact_mod_cast hq_val'

end Rationality

/-! ### Fraction Graph Spectral Values -/

/-- For fraction graphs, the fractional clique cover number is p/q. -/
theorem fractionalCliqueCoverNumber_fractionGraph (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    fractionalCliqueCoverNumber_formula
      (FractionGraphBasic.fractionGraph p q) = (p : ℝ) / q := by
  unfold fractionalCliqueCoverNumber_formula
  have hω := FractionGraphBasic.cliqueNum_fractionGraph_eq p q hq h2q
  have hq_ne : (q : ℕ) ≠ 0 := hq.ne'
  simp only [hω, hq_ne, ↓reduceDIte]
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  simp only [hcard]

end AsymptoticSpectrumGraphs
