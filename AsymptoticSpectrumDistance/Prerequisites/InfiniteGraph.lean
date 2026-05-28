/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import AsymptoticSpectrumDistance.Prerequisites.Cohomomorphism

/-!
# Infinite Graphs with Finite Clique Covering Number

This file defines the general infrastructure for "infinite graphs" -- simple
graphs (with possibly infinite vertex set) whose clique covering number is
finite.  This is the appropriate generalisation of the finite-graph setting
for the asymptotic spectrum distance theory.

The contents of this file are purely general: they do not depend on any
specific construction (e.g. circle graphs, fraction graphs).  Specific
constructions (such as the circle graphs `E_r^o`, `E_r^c`) live downstream
in `Section4/CircleGraphs.lean`.

## Main definitions

* `IsCliqueCover G f` : `f : V → Fin n` colours each clique-cover class.
* `InfiniteGraph` : a simple graph together with a witness that its
  clique covering number is finite.

## Main results

* `cliqueCover_of_cohom` : a cohomomorphism `G → H` pulls back a clique cover
  of `H` to a clique cover of `G` of the same size.

## References

* [de Boer, Buys, Zuiddam] Section 4
-/

namespace AsymptoticSpectrumDistance

open SimpleGraph

/-- A clique cover of a graph: a function f : V → Fin n such that each color class
    is a clique (all vertices with the same color are pairwise adjacent).
    This is the condition: f u = f v → u = v ∨ Adj u v -/
def IsCliqueCover {V : Type*} (G : SimpleGraph V) {n : ℕ} (f : V → Fin n) : Prop :=
  ∀ u v, f u = f v → u = v ∨ G.Adj u v

/-- An infinite graph with a finite clique-fiber cover.
    This is the appropriate generalization of Graph for the asymptotic theory.

    The `cliqueCover_finite` field witnesses that V(G) can be covered by
    finitely many fibers of a map `V → Fin n` such that any two vertices
    sharing a fiber are either equal or G-adjacent (i.e. each fiber is a
    clique; empty fibers are allowed). Existence — not the minimum n — is
    what we require; the existential value is morally the clique-covering
    number `χ̄(G) = χ(Ḡ)` (the chromatic number of the complement). -/
structure InfiniteGraph where
  /-- The vertex type -/
  V : Type*
  /-- The graph structure -/
  graph : SimpleGraph V
  /-- A clique-fiber cover of `V` by `Fin n` for some finite `n`. -/
  cliqueCover_finite : ∃ n : ℕ, ∃ f : V → Fin n, IsCliqueCover graph f

/-- Key lemma: If there's a cohomomorphism G → H and H has a clique cover,
    then G has a clique cover with at most as many cliques.

    Proof: Pull back the clique cover. If C is a clique in H, then f⁻¹(C) is
    a clique in G by the contrapositive of the cohomomorphism condition. -/
theorem cliqueCover_of_cohom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : IsCohom G H f) {n : ℕ} {c : W → Fin n} (hc : IsCliqueCover H c) :
    IsCliqueCover G (c ∘ f) := by
  intro u v heq
  -- heq : c (f u) = c (f v)
  -- From hc, f u = f v ∨ H.Adj (f u) (f v)
  rcases hc (f u) (f v) heq with hfuv | hadj
  · -- Case: f u = f v
    -- From hf, if u ≠ v and ¬G.Adj u v, then f u ≠ f v
    -- Contrapositive: if f u = f v, then u = v ∨ G.Adj u v
    by_cases huv : u = v
    · left; exact huv
    · right
      by_contra hnadj
      have := hf u v huv hnadj
      exact this.1 hfuv
  · -- Case: H.Adj (f u) (f v)
    -- The contrapositive of cohomomorphism: if f(u), f(v) adjacent in H, then u, v adjacent in G
    by_cases huv : u = v
    · left; exact huv
    · right
      by_contra hnadj
      have := hf u v huv hnadj
      exact this.2 hadj

end AsymptoticSpectrumDistance
