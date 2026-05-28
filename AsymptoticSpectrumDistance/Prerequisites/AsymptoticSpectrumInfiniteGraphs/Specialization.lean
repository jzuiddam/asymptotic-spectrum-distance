/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphStrassenPreorder
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumDuality.Duality

/-!
# Specialization for Infinite Graphs

This file connects the abstract asymptotic spectrum theory to the concrete case of
infinite graphs with the cohomomorphism preorder, mirroring `Specialization.lean`
for finite graphs.

## Main Definitions

* `SpectralPointInf` - Spectral points for infinite graphs
* `infGraphSpectralPointToAbstract` - Convert infinite graph SpectralPoint to abstract
* `abstractToInfGraphSpectralPoint` - Convert abstract SpectralPoint to infinite graph

## References

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

/-! ### Spectral Points for Infinite Graphs -/

/-- A spectral point for infinite graphs is a function satisfying the four spectral axioms. -/
structure SpectralPointInf where
  /-- The evaluation function -/
  eval : InfiniteGraph → ℝ
  /-- Normalization: φ(E_n) = n -/
  normalized : ∀ n : ℕ, eval (InfiniteGraph.edgeless n) = n
  /-- Multiplicativity under strong product -/
  mul_strongProduct : ∀ G H : InfiniteGraph, eval (G ⊠∞ H) = eval G * eval H
  /-- Additivity under disjoint union -/
  add_disjointUnion : ∀ G H : InfiniteGraph, eval (G ⊔∞ H) = eval G + eval H
  /-- Monotonicity under cohomomorphism -/
  mono_cohom : ∀ G H : InfiniteGraph, Cohom G.graph H.graph → eval G ≤ eval H

instance : CoeFun SpectralPointInf (fun _ => InfiniteGraph → ℝ) where
  coe := SpectralPointInf.eval

/-! ### Lifting to InfiniteGraphClass -/

/-- A spectral point for infinite graphs respects isomorphism. -/
theorem SpectralPointInf.eval_congr (φ : SpectralPointInf) {G G' : InfiniteGraph}
    (hiso : InfiniteGraphIso G G') : φ.eval G = φ.eval G' := by
  obtain ⟨iso⟩ := hiso
  have h1 : Cohom G.graph G'.graph := cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE iso)
  have h2 : Cohom G'.graph G.graph := cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE iso.symm)
  exact le_antisymm (φ.mono_cohom G G' h1) (φ.mono_cohom G' G h2)

/-- Lift SpectralPointInf.eval to InfiniteGraphClass. -/
def SpectralPointInf.evalClass (φ : SpectralPointInf) : InfiniteGraphClass → ℝ :=
  Quotient.lift φ.eval (fun _ _ h => φ.eval_congr h)

theorem SpectralPointInf.evalClass_mk (φ : SpectralPointInf) (G : InfiniteGraph) :
    φ.evalClass (InfiniteGraphClass.mk G) = φ.eval G := rfl

/-- Non-negativity follows from the axioms: φ(G) ≥ 0 for all G. -/
theorem SpectralPointInf.nonneg (φ : SpectralPointInf) (G : InfiniteGraph) : 0 ≤ φ.eval G := by
  have h0 : φ.eval (InfiniteGraph.edgeless 0) = 0 := by
    have := φ.normalized 0; simp only [Nat.cast_zero] at this; exact this
  have hmono : φ.eval (InfiniteGraph.edgeless 0) ≤ φ.eval G := by
    apply φ.mono_cohom; exact InfiniteGraph.edgeless_zero_cohom_to_any G
  linarith

/-! ### Infinite Graph SpectralPoint → Abstract SpectralPoint -/

/-- Convert an infinite graph SpectralPoint to an abstract SpectralPoint. -/
def infGraphSpectralPointToAbstract (φ : SpectralPointInf) :
    SpectralPoint infiniteGraphStrassenPreorder where
  toFun := φ.evalClass
  map_zero := by
    change φ.evalClass (InfiniteGraphClass.mk (InfiniteGraph.edgeless 0)) = 0
    rw [SpectralPointInf.evalClass_mk]
    have := φ.normalized 0; simp only [Nat.cast_zero] at this; exact this
  map_one := by
    change φ.evalClass (InfiniteGraphClass.mk (InfiniteGraph.edgeless 1)) = 1
    rw [SpectralPointInf.evalClass_mk]
    have := φ.normalized 1; simp only [Nat.cast_one] at this; exact this
  map_add := by
    intro a b
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    change φ.evalClass (InfiniteGraphClass.mk G + InfiniteGraphClass.mk H) =
           φ.evalClass (InfiniteGraphClass.mk G) + φ.evalClass (InfiniteGraphClass.mk H)
    rw [InfiniteGraphClass.add_def, SpectralPointInf.evalClass_mk, SpectralPointInf.evalClass_mk,
        SpectralPointInf.evalClass_mk]
    exact φ.add_disjointUnion G H
  map_mul := by
    intro a b
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    change φ.evalClass (InfiniteGraphClass.mk G * InfiniteGraphClass.mk H) =
           φ.evalClass (InfiniteGraphClass.mk G) * φ.evalClass (InfiniteGraphClass.mk H)
    rw [InfiniteGraphClass.mul_def, SpectralPointInf.evalClass_mk, SpectralPointInf.evalClass_mk,
        SpectralPointInf.evalClass_mk]
    exact φ.mul_strongProduct G H
  monotone := by
    intro a b hab
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    change φ.evalClass (InfiniteGraphClass.mk G) ≤ φ.evalClass (InfiniteGraphClass.mk H)
    rw [SpectralPointInf.evalClass_mk, SpectralPointInf.evalClass_mk]
    change Cohom G.graph H.graph at hab
    exact φ.mono_cohom G H hab
  nonneg := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    change 0 ≤ φ.evalClass (InfiniteGraphClass.mk G)
    rw [SpectralPointInf.evalClass_mk]
    exact φ.nonneg G

/-! ### Abstract SpectralPoint → Infinite Graph SpectralPoint -/

/-- Convert an abstract SpectralPoint for infiniteGraphStrassenPreorder to an
    infinite graph SpectralPoint. -/
def abstractToInfGraphSpectralPoint
    (ψ : SpectralPoint infiniteGraphStrassenPreorder) : SpectralPointInf where
  eval := fun G => ψ.toFun (InfiniteGraphClass.mk G)
  normalized := by
    intro n
    rw [← InfiniteGraphClass.natCast_eq_edgeless]
    induction n with
    | zero => simp only [Nat.cast_zero]; exact ψ.map_zero
    | succ n ih => simp only [Nat.cast_succ]; rw [ψ.map_add, ψ.map_one, ih]
  mul_strongProduct := by
    intro G H
    have h := ψ.map_mul (InfiniteGraphClass.mk G) (InfiniteGraphClass.mk H)
    change ψ.toFun (InfiniteGraphClass.mk (G ⊠∞ H)) = _
    rw [← InfiniteGraphClass.mul_def]; exact h
  add_disjointUnion := by
    intro G H
    have h := ψ.map_add (InfiniteGraphClass.mk G) (InfiniteGraphClass.mk H)
    change ψ.toFun (InfiniteGraphClass.mk (G ⊔∞ H)) = _
    rw [← InfiniteGraphClass.add_def]; exact h
  mono_cohom := by
    intro G H hcohom
    have hmono := ψ.monotone (InfiniteGraphClass.mk G) (InfiniteGraphClass.mk H)
    apply hmono
    change Cohom G.graph H.graph at hcohom
    exact hcohom

/-! ### Equivalence of Spectral Points -/

/-- The conversion from infinite graph SpectralPoint to abstract and back is the identity. -/
theorem infGraphSpectralPoint_roundtrip (φ : SpectralPointInf) :
    abstractToInfGraphSpectralPoint (infGraphSpectralPointToAbstract φ) = φ := by
  cases φ
  simp only [abstractToInfGraphSpectralPoint, infGraphSpectralPointToAbstract,
             SpectralPointInf.evalClass_mk]

/-- The conversion from abstract SpectralPoint to infinite graph and back. -/
theorem abstractInfSpectralPoint_roundtrip
    (ψ : SpectralPoint infiniteGraphStrassenPreorder) :
    infGraphSpectralPointToAbstract (abstractToInfGraphSpectralPoint ψ) = ψ := by
  have hfun : (abstractToInfGraphSpectralPoint ψ).evalClass = ψ.toFun := by
    ext a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    simp only [abstractToInfGraphSpectralPoint]
    rfl
  cases ψ with | mk toFun _ _ _ _ _ _ =>
  simp only [infGraphSpectralPointToAbstract, abstractToInfGraphSpectralPoint] at hfun ⊢
  congr 1

end AsymptoticSpectrumInfiniteGraphs
