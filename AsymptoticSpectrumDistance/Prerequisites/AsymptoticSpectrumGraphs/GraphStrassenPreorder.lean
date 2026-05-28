/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphSemiring
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumDuality.Defs

/-!
# Graph Strassen Preorder

This file defines the cohomomorphism preorder as a Strassen preorder on graph classes.

## Main Definitions

* `graphCohom` - The cohomomorphism relation on GraphClass
* `graphStrassenPreorder` - The Strassen preorder on GraphClass

## Main Results

* The cohomomorphism preorder satisfies all Strassen preorder axioms
* Every graph is "gapped" in the sense that 2 ≤_P G^k for some k

## References

* Strassen (1988), The asymptotic spectrum of tensors
-/

namespace AsymptoticSpectrumGraphs

open SimpleGraph
open AsymptoticSpectrumDuality

/-! ### Cohomomorphism respects isomorphism -/

/-- Cohomomorphism respects isomorphism: G ≅ G' and H ≅ H' implies
    (G ≤_G H ↔ G' ≤_G H'). -/
theorem _root_.Cohom.congr {G G' H H' : Graph}
    (hGG' : GraphIso G G') (hHH' : GraphIso H H') :
    Cohom G.graph H.graph ↔ Cohom G'.graph H'.graph := by
  obtain ⟨isoG⟩ := hGG'
  obtain ⟨isoH⟩ := hHH'
  constructor
  · intro hGH
    -- G' →_G G →_G H →_G H'
    have hG'G : Cohom G'.graph G.graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoG.symm)
    have hHH' : Cohom H.graph H'.graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoH)
    exact Cohom.trans (Cohom.trans hG'G hGH) hHH'
  · intro hG'H'
    -- G →_G G' →_G H' →_G H
    have hGG' : Cohom G.graph G'.graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoG)
    have hH'H : Cohom H'.graph H.graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoH.symm)
    exact Cohom.trans (Cohom.trans hGG' hG'H') hH'H

/-! ### Cohomomorphism relation on GraphClass -/

/-- The cohomomorphism relation on graph classes.
    G ≤ H in the graph preorder iff there exists a cohomomorphism G → H. -/
def graphCohom : GraphClass → GraphClass → Prop :=
  Quotient.lift₂ (fun G H => Cohom G.graph H.graph)
    (fun _ _ _ _ hGG' hHH' => propext (Cohom.congr hGG' hHH'))

theorem graphCohom_mk (G H : Graph) :
    graphCohom (GraphClass.mk G) (GraphClass.mk H) = Cohom G.graph H.graph := rfl

/-! ### Cohom lemmas for StrassenPreorder -/

/-- Edgeless graphs are ordered by size: E_n ≤_G E_m iff n ≤ m. -/
theorem edgelessGraph_cohom_iff {n m : ℕ} :
    Cohom (edgelessGraph n) (edgelessGraph m) ↔ n ≤ m := by
  constructor
  · intro ⟨f, hf⟩
    -- f must be injective since distinct vertices in E_n are non-adjacent
    have hinj : Function.Injective f := by
      intro x y hxy
      by_contra hne
      have hnadj : ¬(edgelessGraph n).Adj x y := by simp [edgelessGraph]
      have ⟨hfne, _⟩ := hf x y hne hnadj
      exact hfne hxy
    -- Injective function Fin n → Fin m implies n ≤ m
    have h := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin] at h
    exact h
  · intro h
    -- For n ≤ m, use the canonical embedding Fin n → Fin m
    use Fin.castLE h
    intro x y hxy _hnadj
    constructor
    · intro heq; exact hxy (Fin.castLE_injective h heq)
    · simp [edgelessGraph]

/-- Natural number embedding goes through EdgelessGraph. -/
theorem natCast_graphClass_eq (n : ℕ) :
    (n : GraphClass) = GraphClass.mk (EdgelessGraph n) :=
  GraphClass.natCast_eq_edgeless n

/-- Natural number ordering corresponds to edgeless graph ordering. -/
theorem nat_compat_graphCohom (n m : ℕ) :
    n ≤ m ↔ graphCohom (GraphClass.mk (EdgelessGraph n)) (GraphClass.mk (EdgelessGraph m)) := by
  simp only [graphCohom_mk, EdgelessGraph, edgelessGraph_cohom_iff]

/-! ### The Strassen Preorder -/

/-- The graph Strassen preorder based on cohomomorphism. -/
def graphStrassenPreorder : StrassenPreorder GraphClass where
  rel := graphCohom
  refl := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    change Cohom G.graph G.graph
    exact Cohom.refl G.graph
  trans := by
    intro a b c hab hbc
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨K, rfl⟩ := Quotient.exists_rep c
    change Cohom G.graph H.graph at hab
    change Cohom H.graph K.graph at hbc
    change Cohom G.graph K.graph
    exact Cohom.trans hab hbc
  zero_le := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    simp only [GraphClass.zero_def]
    exact edgelessGraph_zero_cohom_to_any G
  nat_compat := by
    intro n m
    rw [natCast_graphClass_eq, natCast_graphClass_eq]
    exact nat_compat_graphCohom n m
  add_mono := by
    intro a b s hab
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨S, rfl⟩ := Quotient.exists_rep s
    -- hab : graphCohom ⟦G⟧ ⟦H⟧
    -- ⟦G⟧ = Quotient.mk _ G = GraphClass.mk G (definitionally)
    change Cohom G.graph H.graph at hab
    change Cohom (G ⊔ᴳ S).graph (H ⊔ᴳ S).graph
    exact Cohom.disjointUnion_map hab (Cohom.refl S.graph)
  mul_mono := by
    intro a b s hab
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨S, rfl⟩ := Quotient.exists_rep s
    change Cohom G.graph H.graph at hab
    change Cohom (G ⊠ S).graph (H ⊠ S).graph
    simp only [Graph.strongProduct]
    exact Cohom.strongProduct_left S.graph hab
  archimedean := by
    -- For any G and H with H ≠ 0, there exists r such that G ≤ r * H
    intro a b hb
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    -- Use r = |V(G)|
    use Fintype.card G.V
    -- G has cohom to E_n where n = |V(G)|
    have hGtoE := cohom_to_edgeless G
    -- H ≠ 0 means H has at least one vertex
    have hH_nonempty : Nonempty H.V := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      -- H with empty vertex set is isomorphic to E_0
      apply hb
      apply Quotient.sound
      -- GraphIso H (EdgelessGraph 0) since both have empty vertex sets
      refine ⟨⟨⟨fun v => (hempty.false v).elim, fun v => Fin.elim0 v, ?_, ?_⟩, ?_⟩⟩
      · intro v; exact (hempty.false v).elim
      · intro v; exact Fin.elim0 v
      · intro v _; exact (hempty.false v).elim
    -- Get a fixed vertex h₀ in H
    obtain ⟨h₀⟩ := hH_nonempty
    -- E_n embeds into E_n ⊠ H via v ↦ (v, h₀)
    have hE_embed : Cohom (edgelessGraph (Fintype.card G.V))
        (ShannonCapacity.strongProduct (edgelessGraph (Fintype.card G.V)) H.graph) := by
      use fun v => (v, h₀)
      intro u v huv hnadj
      simp only [edgelessGraph] at hnadj
      constructor
      · intro heq
        apply huv
        exact (Prod.mk.inj heq).1
      · simp only [ShannonCapacity.strongProduct]
        intro ⟨_, ⟨heq_or_adj, _⟩⟩
        -- heq_or_adj : u = v ∨ (edgelessGraph ...).Adj u v
        cases heq_or_adj with
        | inl heq => exact huv heq
        | inr hadj => simp [edgelessGraph] at hadj
    -- Compose: G → E_n → E_n ⊠ H = n * H
    change graphCohom _ _
    simp only [natCast_graphClass_eq]
    change Cohom G.graph
        (ShannonCapacity.strongProduct (edgelessGraph (Fintype.card G.V)) H.graph)
    exact Cohom.trans hGtoE hE_embed

/-! ### All graphs are gapped -/

/-- The gapped condition for the graph Strassen preorder.
    An element a is gapped if ∃k > 0, 2 ≤_P a^k. -/
def IsStrictlyGappedGraph (a : GraphClass) : Prop :=
  ∃ k : ℕ, k > 0 ∧ graphStrassenPreorder.rel 2 (a ^ k)

/-- A graph with an independent set of size 2 is gapped.
    Note: Complete graphs K_n are NOT gapped since E_2 cannot have cohom to K_n^k.
    E_1 (single vertex) is also NOT gapped.
    This is needed for asympSubrank = min over spectrum. -/
theorem graphs_with_independent_pair_gapped (G : Graph)
    (hindep : ∃ v₀ v₁ : G.V, v₀ ≠ v₁ ∧ ¬G.graph.Adj v₀ v₁) :
    IsStrictlyGappedGraph (GraphClass.mk G) := by
  -- G has two non-adjacent vertices, so E_2 has cohom to G
  obtain ⟨v₀, v₁, hne, hnadj_G⟩ := hindep
  use 1
  constructor
  · omega
  · simp only [pow_one]
    have h2eq : (2 : GraphClass) = GraphClass.mk (EdgelessGraph 2) := natCast_graphClass_eq 2
    change graphCohom (2 : GraphClass) (GraphClass.mk G)
    rw [h2eq, graphCohom_mk]
    simp only [EdgelessGraph]
    use fun i => if i.val = 0 then v₀ else v₁
    intro u w huw _hnadj_E2
    constructor
    · -- Distinctness: different inputs give different outputs
      intro heq
      fin_cases u <;> fin_cases w <;> simp_all
    · -- Non-adjacency in G: v₀ and v₁ are non-adjacent
      have hnadj_G' : ¬G.graph.Adj v₁ v₀ := fun h => hnadj_G (G.graph.symm h)
      fin_cases u <;> fin_cases w <;> simp_all

/-- Edgeless graphs E_n with n ≥ 2 are gapped. -/
theorem edgeless_gapped (n : ℕ) (hn : 2 ≤ n) :
    IsStrictlyGappedGraph (GraphClass.mk (EdgelessGraph n)) := by
  apply graphs_with_independent_pair_gapped
  use ⟨0, by omega⟩, ⟨1, by omega⟩
  refine ⟨?_, ?_⟩
  · intro h; have := Fin.ext_iff.mp h; simp at this
  · simp only [EdgelessGraph]
    intro h; exact h

end AsymptoticSpectrumGraphs
