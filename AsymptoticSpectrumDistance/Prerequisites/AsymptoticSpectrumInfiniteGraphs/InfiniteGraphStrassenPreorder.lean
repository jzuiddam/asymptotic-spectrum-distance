/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphSemiring
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphStrassenPreorder
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumDuality.Defs

/-!
# Infinite Graph Strassen Preorder

This file defines the cohomomorphism preorder as a Strassen preorder on infinite graph classes,
mirroring `GraphStrassenPreorder.lean` for finite graphs.

## Main Definitions

* `infiniteGraphCohom` - The cohomomorphism relation on InfiniteGraphClass
* `infiniteGraphStrassenPreorder` - The Strassen preorder on InfiniteGraphClass

## Main Results

* The cohomomorphism preorder satisfies all Strassen preorder axioms
* Compactness and duality follow from the abstract theory

## References

* Strassen (1988), The asymptotic spectrum of tensors
* de Boer, Buys, Zuiddam, Distance in the asymptotic spectrum of graphs
-/

-- Suppress stylistic warnings
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.emptyLine false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.cdot false
set_option linter.style.show false
set_option linter.unreachableTactic false

namespace AsymptoticSpectrumInfiniteGraphs

open SimpleGraph
open AsymptoticSpectrumGraphs
open AsymptoticSpectrumDistance
open AsymptoticSpectrumDuality

/-! ### Cohomomorphism respects isomorphism -/

/-- Cohomomorphism respects isomorphism for infinite graphs. -/
theorem InfiniteGraph.Cohom.congr {G G' H H' : InfiniteGraph}
    (hGG' : InfiniteGraphIso G G') (hHH' : InfiniteGraphIso H H') :
    Cohom G.graph H.graph ↔ Cohom G'.graph H'.graph := by
  obtain ⟨isoG⟩ := hGG'; obtain ⟨isoH⟩ := hHH'
  constructor
  · intro hGH
    have hG'G : Cohom G'.graph G.graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoG.symm)
    have hHH' : Cohom H.graph H'.graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoH)
    exact Cohom.trans (Cohom.trans hG'G hGH) hHH'
  · intro hG'H'
    have hGG' : Cohom G.graph G'.graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoG)
    have hH'H : Cohom H'.graph H.graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoH.symm)
    exact Cohom.trans (Cohom.trans hGG' hG'H') hH'H

/-! ### Cohomomorphism relation on InfiniteGraphClass -/

/-- The cohomomorphism relation on infinite graph classes. -/
def infiniteGraphCohom : InfiniteGraphClass → InfiniteGraphClass → Prop :=
  Quotient.lift₂ (fun G H => Cohom G.graph H.graph)
    (fun _ _ _ _ hGG' hHH' => propext (InfiniteGraph.Cohom.congr hGG' hHH'))

theorem infiniteGraphCohom_mk (G H : InfiniteGraph) :
    infiniteGraphCohom (InfiniteGraphClass.mk G) (InfiniteGraphClass.mk H) =
    Cohom G.graph H.graph := rfl

/-! ### Edgeless graph ordering -/

/-- Edgeless infinite graphs are ordered by size: E_n ≤_G E_m iff n ≤ m. -/
theorem infEdgelessGraph_cohom_iff {n m : ℕ} :
    Cohom (InfiniteGraph.edgeless n).graph (InfiniteGraph.edgeless m).graph ↔ n ≤ m := by
  simp only [InfiniteGraph.edgeless]
  exact edgelessGraph_cohom_iff

theorem natCast_infGraphClass_eq (n : ℕ) :
    (n : InfiniteGraphClass) = InfiniteGraphClass.mk (InfiniteGraph.edgeless n) :=
  InfiniteGraphClass.natCast_eq_edgeless n

theorem nat_compat_infGraphCohom (n m : ℕ) :
    n ≤ m ↔ infiniteGraphCohom (InfiniteGraphClass.mk (InfiniteGraph.edgeless n))
                                (InfiniteGraphClass.mk (InfiniteGraph.edgeless m)) := by
  simp only [infiniteGraphCohom_mk]
  exact infEdgelessGraph_cohom_iff.symm

/-! ### The Strassen Preorder -/

/-- The infinite graph Strassen preorder based on cohomomorphism. -/
def infiniteGraphStrassenPreorder : StrassenPreorder InfiniteGraphClass where
  rel := infiniteGraphCohom
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
    simp only [InfiniteGraphClass.zero_def]
    exact InfiniteGraph.edgeless_zero_cohom_to_any G
  nat_compat := by
    intro n m
    rw [natCast_infGraphClass_eq, natCast_infGraphClass_eq]
    exact nat_compat_infGraphCohom n m
  add_mono := by
    intro a b s hab
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨S, rfl⟩ := Quotient.exists_rep s
    change Cohom G.graph H.graph at hab
    change Cohom (G ⊔∞ S).graph (H ⊔∞ S).graph
    exact InfiniteGraph.cohom_disjointUnion_map hab (Cohom.refl S.graph)
  mul_mono := by
    intro a b s hab
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨S, rfl⟩ := Quotient.exists_rep s
    change Cohom G.graph H.graph at hab
    change Cohom (G ⊠∞ S).graph (H ⊠∞ S).graph
    exact InfiniteGraph.cohom_strongProduct_left hab
  archimedean := by
    intro a b hb
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    -- Use k = clique cover number of G
    obtain ⟨k, hk⟩ := InfiniteGraph.cohom_to_edgeless G
    use k
    -- Need: graphCohom G (E_k ⊠ H), i.e., Cohom G → E_k ⊠ H
    -- H ≠ 0 means H has at least one vertex
    have hH_nonempty : Nonempty H.V := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      apply hb
      apply Quotient.sound
      -- H with empty vertex set is isomorphic to E_0
      refine ⟨⟨⟨fun v => (hempty.false v).elim, fun v => Fin.elim0 v, ?_, ?_⟩, ?_⟩⟩
      · intro v; exact (hempty.false v).elim
      · intro v; exact Fin.elim0 v
      · intro v _; exact (hempty.false v).elim
    obtain ⟨h₀⟩ := hH_nonempty
    -- E_k embeds into E_k ⊠ H via v ↦ (v, h₀)
    have hE_embed : Cohom (InfiniteGraph.edgeless k).graph
        (ShannonCapacity.strongProduct (InfiniteGraph.edgeless k).graph H.graph) := by
      use fun v => (v, h₀)
      intro u v huv hnadj
      simp only [InfiniteGraph.edgeless] at hnadj
      constructor
      · intro heq; exact huv (Prod.mk.inj heq).1
      · simp only [ShannonCapacity.strongProduct]
        intro ⟨_, ⟨heq_or_adj, _⟩⟩
        cases heq_or_adj with
        | inl heq => exact huv heq
        | inr hadj => simp [InfiniteGraph.edgeless] at hadj
    change infiniteGraphCohom _ _
    simp only [natCast_infGraphClass_eq]
    change Cohom G.graph
        (ShannonCapacity.strongProduct (InfiniteGraph.edgeless k).graph H.graph)
    exact Cohom.trans hk hE_embed

end AsymptoticSpectrumInfiniteGraphs
