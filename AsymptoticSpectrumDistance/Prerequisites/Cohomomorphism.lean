/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphOperations

/-!
# Cohomomorphisms of simple graphs

A **cohomomorphism** from a simple graph `G` to a simple graph `H` is a map
`V(G) → V(H)` that sends distinct non-adjacent vertices to distinct non-adjacent
vertices.  Equivalently, it sends independent sets injectively to independent sets.

These are general graph-theoretic notions, independent of the asymptotic
spectrum machinery, so they live in their own module here.  The definitions
live at root level (no enclosing namespace) so that dot notation `h.foo`
resolves correctly even for downstream theorems declared in other namespaces
(notably the `AsymptoticSpectrumGraphs` namespace which adds graph-operation
specific lemmas like `IsCohom.strongProduct_map_fst`).
-/

open SimpleGraph

/-- A function `f : V → W` is a cohomomorphism from `G` to `H` if it maps
    distinct non-adjacent vertices to distinct non-adjacent vertices.
    Equivalently, it maps independent sets injectively to independent sets.

    Definition 1.4 in the blueprint: A cohomomorphism G → H is a map V(G) → V(H)
    that maps non-edges to non-edges. -/
def IsCohom {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W) : Prop :=
  ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v)

/-- There exists a cohomomorphism from `G` to `H`.
    We write G ≤_G H if there exists a cohomomorphism G → H. -/
def Cohom {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, IsCohom G H f

@[inherit_doc] notation:50 G " ≤_G " H => Cohom G H

/-- Cohomomorphism equivalence: mutual cohomomorphisms `G ≤_G H ∧ H ≤_G G`. -/
def CohomEquiv {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Cohom G H ∧ Cohom H G

/-- Cohomomorphisms compose: if G →co H and H →co K, then G →co K. -/
theorem IsCohom.comp {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}
    {f : V → W} {g : W → X} (hf : IsCohom G H f) (hg : IsCohom H K g) :
    IsCohom G K (g ∘ f) := by
  intro u v huv hnadj
  have hf_uv := hf u v huv hnadj
  exact hg (f u) (f v) hf_uv.1 hf_uv.2

/-- Cohom is transitive. -/
theorem Cohom.trans {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}
    (hGH : G ≤_G H) (hHK : H ≤_G K) : G ≤_G K := by
  obtain ⟨f, hf⟩ := hGH
  obtain ⟨g, hg⟩ := hHK
  exact ⟨g ∘ f, hf.comp hg⟩

/-- The identity is a cohomomorphism. -/
theorem IsCohom.id {V : Type*} (G : SimpleGraph V) : IsCohom G G id := by
  intro u v huv hnadj
  exact ⟨huv, hnadj⟩

/-- Cohom is reflexive. -/
theorem Cohom.refl {V : Type*} (G : SimpleGraph V) : G ≤_G G :=
  ⟨id, IsCohom.id G⟩

/-- Bridge between CohomLE and Cohom: a complement homomorphism gives a cohomomorphism. -/
theorem cohomLE_to_cohom {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (h : G ≤ᶜ H) :
    Cohom G H := by
  obtain ⟨φ⟩ := h
  refine ⟨φ, fun u v huv hnadj => ?_⟩
  -- φ is a homomorphism from Gᶜ to Hᶜ
  -- If u ≠ v and ¬G.Adj u v, then Gᶜ.Adj u v
  have hadj : Gᶜ.Adj u v := by
    simp only [SimpleGraph.compl_adj]
    exact ⟨huv, hnadj⟩
  -- So Hᶜ.Adj (φ u) (φ v)
  have hadj' : Hᶜ.Adj (φ u) (φ v) := φ.map_adj hadj
  simp only [SimpleGraph.compl_adj] at hadj'
  exact hadj'
