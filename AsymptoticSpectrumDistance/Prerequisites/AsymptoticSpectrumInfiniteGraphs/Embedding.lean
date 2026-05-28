/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.Specialization
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.Specialization
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumDuality.Surjectivity

/-!
# Embedding of Finite Graphs into Infinite Graphs

This file establishes the order embedding of finite graphs into infinite graphs
(Lemma 4.4) and the surjectivity of the restriction map on spectra (Theorem 4.5).

## Main Definitions

* `graphToInfiniteGraph` - Embeds a finite graph as an infinite graph
* `graphClassEmbedding` - Ring homomorphism GraphClass →+* InfiniteGraphClass

## Main Results

* `graphClassEmbedding_order_embedding` - Lemma 4.4: the cohomomorphism preorder
  on finite graphs embeds into the preorder on infinite graphs
* `restriction_surjective_graphs` - Theorem 4.5: the restriction map X_∞ → X
  on spectral points is surjective

## References

* de Boer, Buys, Zuiddam, Distance in the asymptotic spectrum of graphs, §4
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

/-! ### Embedding Finite Graphs into Infinite Graphs -/

/-- Embed a finite graph as an infinite graph (forgets Fintype).
    A finite graph automatically has finite clique covering number
    (at most |V| cliques, one per vertex). -/
def graphToInfiniteGraph (G : Graph) : InfiniteGraph where
  V := G.V
  graph := G.graph
  cliqueCover_finite := by
    use Fintype.card G.V
    use Fintype.equivFin G.V
    intro u v heq
    left; exact (Fintype.equivFin G.V).injective heq

/-- The embedding respects graph isomorphism. -/
theorem graphToInfiniteGraph_congr {G G' : Graph}
    (hiso : GraphIso G G') : InfiniteGraphIso (graphToInfiniteGraph G) (graphToInfiniteGraph G') := by
  obtain ⟨iso⟩ := hiso
  exact ⟨iso⟩

/-- Lift the embedding to the quotient types. -/
def graphClassToInfiniteGraphClass : GraphClass → InfiniteGraphClass :=
  Quotient.lift (fun G => InfiniteGraphClass.mk (graphToInfiniteGraph G))
    (fun _ _ h => Quotient.sound (graphToInfiniteGraph_congr h))

theorem graphClassToInfiniteGraphClass_mk (G : Graph) :
    graphClassToInfiniteGraphClass (GraphClass.mk G) =
    InfiniteGraphClass.mk (graphToInfiniteGraph G) := rfl

/-! ### Ring Homomorphism -/

/-- The embedding preserves addition (disjoint union). -/
theorem graphClassToInfiniteGraphClass_add (a b : GraphClass) :
    graphClassToInfiniteGraphClass (a + b) =
    graphClassToInfiniteGraphClass a + graphClassToInfiniteGraphClass b := by
  obtain ⟨G, rfl⟩ := Quotient.exists_rep a
  obtain ⟨H, rfl⟩ := Quotient.exists_rep b
  show graphClassToInfiniteGraphClass (GraphClass.mk G + GraphClass.mk H) =
       graphClassToInfiniteGraphClass (GraphClass.mk G) + graphClassToInfiniteGraphClass (GraphClass.mk H)
  rw [GraphClass.add_def, graphClassToInfiniteGraphClass_mk, graphClassToInfiniteGraphClass_mk,
      graphClassToInfiniteGraphClass_mk, InfiniteGraphClass.add_def]
  apply Quotient.sound
  exact ⟨RelIso.refl _⟩

/-- The embedding preserves multiplication (strong product). -/
theorem graphClassToInfiniteGraphClass_mul (a b : GraphClass) :
    graphClassToInfiniteGraphClass (a * b) =
    graphClassToInfiniteGraphClass a * graphClassToInfiniteGraphClass b := by
  obtain ⟨G, rfl⟩ := Quotient.exists_rep a
  obtain ⟨H, rfl⟩ := Quotient.exists_rep b
  show graphClassToInfiniteGraphClass (GraphClass.mk G * GraphClass.mk H) =
       graphClassToInfiniteGraphClass (GraphClass.mk G) * graphClassToInfiniteGraphClass (GraphClass.mk H)
  rw [GraphClass.mul_def, graphClassToInfiniteGraphClass_mk, graphClassToInfiniteGraphClass_mk,
      graphClassToInfiniteGraphClass_mk, InfiniteGraphClass.mul_def]
  apply Quotient.sound
  exact ⟨RelIso.refl _⟩

/-- The embedding preserves zero. -/
theorem graphClassToInfiniteGraphClass_zero :
    graphClassToInfiniteGraphClass 0 = 0 := by
  rw [GraphClass.zero_def, graphClassToInfiniteGraphClass_mk, InfiniteGraphClass.zero_def]
  apply Quotient.sound
  exact ⟨RelIso.refl _⟩

/-- The embedding preserves one. -/
theorem graphClassToInfiniteGraphClass_one :
    graphClassToInfiniteGraphClass 1 = 1 := by
  rw [GraphClass.one_def, graphClassToInfiniteGraphClass_mk, InfiniteGraphClass.one_def]
  apply Quotient.sound
  exact ⟨RelIso.refl _⟩

/-- The embedding as a ring homomorphism. -/
def graphClassEmbedding : GraphClass →+* InfiniteGraphClass where
  toFun := graphClassToInfiniteGraphClass
  map_zero' := graphClassToInfiniteGraphClass_zero
  map_one' := graphClassToInfiniteGraphClass_one
  map_add' := graphClassToInfiniteGraphClass_add
  map_mul' := graphClassToInfiniteGraphClass_mul

/-! ### Lemma 4.4: Order Embedding -/

/-- Lemma 4.4: The cohomomorphism preorder on finite graphs embeds into the
    cohomomorphism preorder on infinite graphs (order-embedding).
    G ≤ H in finite iff G ≤ H in infinite. -/
theorem graphClassEmbedding_order_embedding (a b : GraphClass) :
    graphStrassenPreorder.rel a b ↔
    infiniteGraphStrassenPreorder.rel (graphClassEmbedding a) (graphClassEmbedding b) := by
  obtain ⟨G, rfl⟩ := Quotient.exists_rep a
  obtain ⟨H, rfl⟩ := Quotient.exists_rep b
  -- Both sides reduce to Cohom G.graph H.graph
  change Cohom G.graph H.graph ↔ Cohom G.graph H.graph
  exact Iff.rfl

/-! ### Restriction Map -/

/-- The restriction map: given a spectral point for infinite graphs,
    restrict to finite graphs. -/
def restrictionMap (ψ : SpectralPointInf) : AsymptoticSpectrumGraphs.SpectralPoint where
  eval := fun G => ψ.eval (graphToInfiniteGraph G)
  normalized := by
    intro n
    -- graphToInfiniteGraph (EdgelessGraph n) and InfiniteGraph.edgeless n have the same graph
    have : InfiniteGraphIso (graphToInfiniteGraph (EdgelessGraph n)) (InfiniteGraph.edgeless n) :=
      ⟨RelIso.refl _⟩
    rw [ψ.eval_congr this]
    exact ψ.normalized n
  mul_strongProduct := by
    intro G H
    have : InfiniteGraphIso (graphToInfiniteGraph (G ⊠ H))
        (graphToInfiniteGraph G ⊠∞ graphToInfiniteGraph H) := ⟨RelIso.refl _⟩
    rw [ψ.eval_congr this]
    exact ψ.mul_strongProduct _ _
  add_disjointUnion := by
    intro G H
    have : InfiniteGraphIso (graphToInfiniteGraph (G ⊔ᴳ H))
        (graphToInfiniteGraph G ⊔∞ graphToInfiniteGraph H) := ⟨RelIso.refl _⟩
    rw [ψ.eval_congr this]
    exact ψ.add_disjointUnion _ _
  mono_cohom := by
    intro G H hcohom
    exact ψ.mono_cohom _ _ hcohom

/-! ### Theorem 4.5: Surjectivity of Restriction -/

/-- Theorem 4.5: The restriction map X_∞ → X on spectral points is surjective.
    For every spectral point φ on finite graphs, there exists a spectral point ψ
    on infinite graphs such that ψ restricted to finite graphs equals φ.

    This follows from the abstract surjectivity theorem (Theorem A.2). -/
theorem restriction_surjective :
    ∀ φ : AsymptoticSpectrumGraphs.SpectralPoint, ∃ ψ : SpectralPointInf, ∀ G : Graph,
      ψ.eval (graphToInfiniteGraph G) = φ.eval G := by
  intro φ
  -- Apply the abstract surjectivity theorem
  have habstract := AsymptoticSpectrumDuality.restriction_surjective
    graphStrassenPreorder infiniteGraphStrassenPreorder
    graphClassEmbedding graphClassEmbedding_order_embedding
    (graphSpectralPointToAbstract φ)
  obtain ⟨ψ_abs, hψ⟩ := habstract
  -- Convert abstract spectral point to concrete
  use abstractToInfGraphSpectralPoint ψ_abs
  intro G
  -- ψ_abs(graphClassEmbedding (GraphClass.mk G)) = (graphSpectralPointToAbstract φ)(GraphClass.mk G)
  have hG := hψ (GraphClass.mk G)
  -- LHS: abstractToInfGraphSpectralPoint ψ_abs applied to graphToInfiniteGraph G
  -- = ψ_abs.toFun (InfiniteGraphClass.mk (graphToInfiniteGraph G))
  -- = ψ_abs.toFun (graphClassEmbedding (GraphClass.mk G))  [by definition]
  -- RHS: φ.eval G = (graphSpectralPointToAbstract φ).toFun (GraphClass.mk G) [by definition]
  simp only [abstractToInfGraphSpectralPoint, graphClassEmbedding, graphClassToInfiniteGraphClass_mk]
  simp only [graphSpectralPointToAbstract, AsymptoticSpectrumGraphs.SpectralPoint.evalClass_mk] at hG
  exact hG

end AsymptoticSpectrumInfiniteGraphs
