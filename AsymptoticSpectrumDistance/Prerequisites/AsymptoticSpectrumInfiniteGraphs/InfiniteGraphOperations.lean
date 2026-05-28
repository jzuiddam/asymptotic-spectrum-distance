/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.InfiniteGraph

/-!
# Infinite Graph Operations

This file defines operations on infinite graphs (graphs with finite clique covering number)
needed for the asymptotic spectrum theory:
- Strong product G ⊠ H
- Disjoint union G ⊔ H
- Edgeless graphs E_n

## Main Definitions

* `InfiniteGraph.strongProduct` - Strong product of infinite graphs
* `InfiniteGraph.disjointUnion` - Disjoint union of infinite graphs
* `InfiniteGraph.edgeless` - Edgeless graph on n vertices

## References

* de Boer, Buys, Zuiddam, *Distance in the asymptotic spectrum of graphs*
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

/-! ### Strong Product -/

/-- The strong product of two infinite graphs.
    The vertex type is V × W. A clique cover of size k₁ * k₂ is obtained
    by combining clique covers of G (size k₁) and H (size k₂). -/
def InfiniteGraph.strongProduct (G H : InfiniteGraph) : InfiniteGraph where
  V := G.V × H.V
  graph := ShannonCapacity.strongProduct G.graph H.graph
  cliqueCover_finite := by
    obtain ⟨k₁, f₁, hf₁⟩ := G.cliqueCover_finite
    obtain ⟨k₂, f₂, hf₂⟩ := H.cliqueCover_finite
    use k₁ * k₂
    use fun ⟨v, w⟩ => finProdFinEquiv (f₁ v, f₂ w)
    intro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩ heq
    have hinj := finProdFinEquiv.injective heq
    have hf1eq : f₁ u₁ = f₁ v₁ := (Prod.mk.inj hinj).1
    have hf2eq : f₂ u₂ = f₂ v₂ := (Prod.mk.inj hinj).2
    rcases hf₁ u₁ v₁ hf1eq with heq1 | hadj1 <;> rcases hf₂ u₂ v₂ hf2eq with heq2 | hadj2
    · left; exact Prod.ext heq1 heq2
    · right; exact ⟨fun h => H.graph.ne_of_adj hadj2 (Prod.mk.inj h).2, Or.inl heq1, Or.inr hadj2⟩
    · right; exact ⟨fun h => G.graph.ne_of_adj hadj1 (Prod.mk.inj h).1, Or.inr hadj1, Or.inl heq2⟩
    · right; exact ⟨fun h => G.graph.ne_of_adj hadj1 (Prod.mk.inj h).1, Or.inr hadj1, Or.inr hadj2⟩

notation:70 G " ⊠∞ " H => InfiniteGraph.strongProduct G H

/-! ### Disjoint Union -/

/-- The disjoint union of two infinite graphs.
    The vertex type is V ⊕ W. A clique cover of size k₁ + k₂ is obtained
    by combining clique covers of G (size k₁) and H (size k₂). -/
def InfiniteGraph.disjointUnion (G H : InfiniteGraph) : InfiniteGraph where
  V := G.V ⊕ H.V
  graph := disjUnionSimple G.graph H.graph
  cliqueCover_finite := by
    obtain ⟨k₁, f₁, hf₁⟩ := G.cliqueCover_finite
    obtain ⟨k₂, f₂, hf₂⟩ := H.cliqueCover_finite
    use k₁ + k₂
    use Sum.elim (fun v => Fin.castAdd k₂ (f₁ v)) (fun w => Fin.natAdd k₁ (f₂ w))
    intro x y heq
    match x, y with
    | .inl u, .inl v =>
      have hfuv : f₁ u = f₁ v := by
        simp only [Sum.elim_inl, Fin.ext_iff, Fin.val_castAdd] at heq
        exact Fin.ext heq
      rcases hf₁ u v hfuv with h | h
      · left; exact congrArg Sum.inl h
      · right; exact h
    | .inr u, .inr v =>
      have hfuv : f₂ u = f₂ v := by
        simp only [Sum.elim_inr, Fin.ext_iff, Fin.val_natAdd] at heq
        exact Fin.ext (by omega)
      rcases hf₂ u v hfuv with h | h
      · left; exact congrArg Sum.inr h
      · right; exact h
    | .inl u, .inr v =>
      exfalso
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at heq
      have h1 := (f₁ u).isLt; omega
    | .inr u, .inl v =>
      exfalso
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at heq
      have h1 := (f₁ v).isLt; omega

notation:65 G " ⊔∞ " H => InfiniteGraph.disjointUnion G H

/-! ### Edgeless Graphs -/

/-- The edgeless infinite graph on n vertices. -/
def InfiniteGraph.edgeless (n : ℕ) : InfiniteGraph where
  V := Fin n
  graph := ⊥
  cliqueCover_finite := ⟨n, id, fun u v heq => Or.inl heq⟩

/-! ### Cohomomorphism Properties -/

/-- Cohomomorphism for strong product on the first factor for infinite graphs. -/
theorem InfiniteGraph.cohom_strongProduct_left {G G' H : InfiniteGraph}
    (hGG' : Cohom G.graph G'.graph) :
    Cohom (G ⊠∞ H).graph (G' ⊠∞ H).graph := by
  obtain ⟨f, hf⟩ := hGG'
  exact ⟨Prod.map f id, hf.strongProduct_map_fst⟩

/-- Cohomomorphism for disjoint union of infinite graphs. -/
theorem InfiniteGraph.cohom_disjointUnion_map {G G' H H' : InfiniteGraph}
    (hGG' : Cohom G.graph G'.graph) (hHH' : Cohom H.graph H'.graph) :
    Cohom (G ⊔∞ H).graph (G' ⊔∞ H').graph := by
  obtain ⟨f, hf⟩ := hGG'
  obtain ⟨g, hg⟩ := hHH'
  exact ⟨Sum.map f g, hf.disjointUnion_map hg⟩

/-- The empty graph E_0 has a cohomomorphism to any infinite graph. -/
theorem InfiniteGraph.edgeless_zero_cohom_to_any (G : InfiniteGraph) :
    Cohom (InfiniteGraph.edgeless 0).graph G.graph :=
  ⟨fun x => Fin.elim0 x, fun u _ _ _ => Fin.elim0 u⟩

/-- Any infinite graph G has a cohomomorphism to E_k where k is its clique cover number. -/
theorem InfiniteGraph.cohom_to_edgeless (G : InfiniteGraph) :
    ∃ k : ℕ, Cohom G.graph (InfiniteGraph.edgeless k).graph := by
  obtain ⟨k, f, hf⟩ := G.cliqueCover_finite
  use k, f
  intro u v huv hnadj
  constructor
  · intro heq
    rcases hf u v heq with h | h
    · exact huv h
    · exact hnadj h
  · simp [InfiniteGraph.edgeless]

end AsymptoticSpectrumInfiniteGraphs
