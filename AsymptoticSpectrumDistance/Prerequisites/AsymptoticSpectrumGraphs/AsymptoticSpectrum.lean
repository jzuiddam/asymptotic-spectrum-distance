/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.RelClasses
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.StrongProduct
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphOperations
import AsymptoticSpectrumDistance.Prerequisites.Cohomomorphism

/-!
# Asymptotic Spectrum of Graphs

This file defines the asymptotic cohomomorphism preorder and spectral points,
which characterize the asymptotic structure of graph cohomomorphisms.

## Main definitions

* `AsympCohom G H` : Asymptotic cohomomorphism H ≲ G
* `SpectralPoint` : A function φ : Graphs → ℝ≥0 satisfying the spectral axioms
* `AsymptoticSpectrum` : The set Δ(G) of all spectral points

## Main results

* `spectral_duality` : G ≲ H ↔ ∀ φ ∈ Δ(G), φ(G) ≤ φ(H)
* `spectral_join` : φ(G + H) = max(φ(G), φ(H))

## References

* Zuiddam (2019), Asymptotic spectrum of graphs
* Vrana (2019), Probabilistic refinement of asymptotic spectra

-/

namespace AsymptoticSpectrumGraphs

open SimpleGraph

/-! ### Graph universe -/

/-- The type of finite simple graphs with decidable equality.
    This bundles the Fintype and DecidableEq instances needed for
    fractional clique covering number computations and spectral points. -/
structure Graph where
  /-- The vertex type -/
  V : Type*
  /-- The graph structure -/
  graph : SimpleGraph V
  /-- Finiteness of vertex set -/
  [fintype : Fintype V]
  /-- Decidable equality on vertices -/
  [deceq : DecidableEq V]

attribute [instance] Graph.fintype Graph.deceq

/-- Alias for backwards compatibility -/
abbrev FiniteGraph := Graph

/-- Identity conversion for backwards compatibility -/
def Graph.toGraph (G : Graph) : Graph := G

/-! ### Cohomomorphisms

The basic cohomomorphism notions `IsCohom`, `Cohom`, `CohomEquiv`, the
composition / identity / `cohomLE_to_cohom` lemmas, and the `≤_G` notation live
at root namespace in `Prerequisites/Cohomomorphism.lean`.  Because they are at
root namespace, callers that `open AsymptoticSpectrumGraphs` already get them
under the short name (no explicit `export` is needed).  Graph-operation specific
`IsCohom`/`Cohom` lemmas defined below are declared into the root `IsCohom` /
`Cohom` namespace via `_root_.` so that dot notation `hf.foo` continues to work. -/

/-! ### Asymptotic cohomomorphism -/

/-- A function f : ℕ → ℕ is o(n) if f(n)/n → 0 as n → ∞ -/
def IsLittleO (f : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, (f n : ℝ) < ε * n

/-- Asymptotic cohomomorphism: H ≲ G means H^⊠n ≤_G G^⊠(n+o(n)).
    That is, for some function f with f(n)/n → 0, for all n ≥ 1,
    there exists a cohomomorphism from H^⊠n to G^⊠(n+f(n)).

    This defines the asymptotic preorder on graphs from Strassen's theory
    of asymptotic spectra. -/
def AsympCohom (H G : Graph) : Prop :=
  ∃ f : ℕ → ℕ, IsLittleO f ∧
    ∀ n : ℕ, n ≥ 1 →
      Cohom (SimpleGraph.strongPower H.graph n)
        (SimpleGraph.strongPower G.graph (n + f n))

notation:50 H " ≲ " G => AsympCohom H G

/-! ### Edgeless graphs -/

/-- The edgeless graph on n vertices (also called the empty graph or independent set).
    This is E_n = K̄_n, the complement of the complete graph. -/
def edgelessGraph (n : ℕ) : SimpleGraph (Fin n) := ⊥

/-- The edgeless graph as a Graph. -/
def EdgelessGraph (n : ℕ) : Graph := { V := Fin n, graph := edgelessGraph n }

/-- Any graph G has a cohomomorphism to the edgeless graph on |V(G)| vertices.
    This is because the edgeless graph has no edges, so the cohomomorphism
    condition (non-adjacency is preserved) is trivially satisfied.
    We use the canonical bijection G.V ≃ Fin |V| which is injective. -/
theorem cohom_to_edgeless (G : Graph) :
    Cohom G.graph (edgelessGraph (Fintype.card G.V)) := by
  -- Use the canonical equivalence as our cohomomorphism function
  have heq := Fintype.equivFin G.V
  use heq
  intro u v huv _hnadj
  -- IsCohom requires: f u ≠ f v ∧ ¬H.Adj (f u) (f v)
  constructor
  · -- f u ≠ f v: follows from injectivity of heq and u ≠ v
    intro hcontra
    apply huv
    exact heq.injective hcontra
  · -- ¬edgelessGraph.Adj (heq u) (heq v): edgeless graph has no edges
    simp only [edgelessGraph, SimpleGraph.bot_adj, not_false_eq_true]

/-! ### Graph operations -/

/-- Independence number of a bundled `Graph`, equal to `G.graph.indepNum`. -/
noncomputable abbrev Graph.indepNum (G : Graph) : ℕ := G.graph.indepNum

/-- Cohomomorphism predicate on bundled `Graph`s, equal to `Cohom G.graph H.graph`. -/
abbrev Graph.Cohom (G H : Graph) : Prop := _root_.Cohom G.graph H.graph

/-- "Is-cohomomorphism" predicate on bundled `Graph`s, equal to
    `IsCohom G.graph H.graph f`. -/
abbrev Graph.IsCohom (G H : Graph) (f : G.V → H.V) : Prop :=
  _root_.IsCohom G.graph H.graph f

/-- The strong product of two graphs. -/
def Graph.strongProduct (G H : Graph) : Graph :=
  { V := G.V × H.V, graph := ShannonCapacity.strongProduct G.graph H.graph }

/-- The disjoint union of two SimpleGraphs on different vertex types.
    Vertices from G (via Sum.inl) and H (via Sum.inr) are never adjacent to each other. -/
def disjUnionSimple {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inr a, .inr b => H.Adj a b
    | _, _ => False
  symm := by
    intro x y h
    match x, y with
    | .inl a, .inl b => exact G.symm h
    | .inr a, .inr b => exact H.symm h
    | .inl _, .inr _ => exact h.elim
    | .inr _, .inl _ => exact h.elim
  loopless := ⟨by
    intro x
    match x with
    | .inl a => exact G.loopless.irrefl a
    | .inr b => exact H.loopless.irrefl b⟩

/-- The disjoint union of two graphs.
    Vertices from G (via Sum.inl) and H (via Sum.inr) are never adjacent. -/
def Graph.disjointUnion (G H : Graph) : Graph :=
  { V := G.V ⊕ H.V, graph := disjUnionSimple G.graph H.graph }

infixl:70 " ⊠ " => Graph.strongProduct
infixl:65 " ⊔ᴳ " => Graph.disjointUnion

/-- Recursive definition of strong product power: G^⊠n.
    - Base case: G^⊠0 = EdgelessGraph 1 (single vertex, no edges)
    - Inductive: G^⊠(n+1) = G ⊠ G^⊠n -/
def recStrongPowerGraph (G : Graph) : ℕ → Graph
  | 0 => EdgelessGraph 1
  | n + 1 => G ⊠ (recStrongPowerGraph G n)

/-- The strong power at Graph level using function type for vertices. -/
def strongPowerGraph (G : Graph) (m : ℕ) : Graph where
  V := Fin m → G.V
  graph := SimpleGraph.strongPower G.graph m

/-- Vertex type equivalence between recStrongPowerGraph and strongPowerGraph.
    recStrongPowerGraph uses nested products: G.V × (G.V × (... × Fin 1))
    strongPowerGraph uses function type: Fin m → G.V -/
def recStrongPowerGraph_vertex_equiv (G : Graph) : (m : ℕ) →
    (recStrongPowerGraph G m).V ≃ (strongPowerGraph G m).V
  | 0 => {
      -- (recStrongPowerGraph G 0).V = Fin 1
      -- (strongPowerGraph G 0).V = Fin 0 → G.V
      toFun := fun _ => finZeroElim
      invFun := fun _ => ⟨0, by decide⟩
      left_inv := fun x => Fin.ext (Nat.lt_one_iff.mp x.isLt).symm
      right_inv := fun f => funext (fun i => i.elim0)
    }
  | n + 1 =>
      let e := recStrongPowerGraph_vertex_equiv G n
      { toFun := fun ⟨v, rest⟩ => Fin.cons v (e rest)
        invFun := fun f => (f 0, e.symm (Fin.tail f))
        left_inv := fun ⟨v, rest⟩ => by simp [e.symm_apply_apply]
        right_inv := fun f => by
          funext i
          cases i using Fin.cases with
          | zero => rfl
          | succ i => simp only [Fin.cons_succ, Fin.tail, e.apply_symm_apply] }

/-- The adjacency relation in recStrongPowerGraph matches strongPowerGraph under the equivalence.
    This is the key technical lemma showing the two definitions give isomorphic graphs. -/
theorem recStrongPowerGraph_adj_iff (G : Graph) (m : ℕ)
    (p q : (recStrongPowerGraph G m).V) :
    (recStrongPowerGraph G m).graph.Adj p q ↔
    (strongPowerGraph G m).graph.Adj
      (recStrongPowerGraph_vertex_equiv G m p)
      (recStrongPowerGraph_vertex_equiv G m q) := by
  induction m with
  | zero =>
    -- Base case: both graphs have a single vertex, no edges
    simp only [recStrongPowerGraph, strongPowerGraph, EdgelessGraph,
               edgelessGraph, strongPowerGraph]
    simp only [SimpleGraph.strongPower]
    constructor
    · intro h
      exact h.elim
    · intro ⟨hne, _⟩
      -- In Fin 0 → G.V, there's only one element
      exfalso
      apply hne
      funext i
      exact i.elim0
  | succ n ih =>
    obtain ⟨pv, prest⟩ := p
    obtain ⟨qv, qrest⟩ := q
    simp only [recStrongPowerGraph, Graph.strongProduct, strongPowerGraph]
    simp only [ShannonCapacity.strongProduct, SimpleGraph.strongPower]
    simp only [recStrongPowerGraph_vertex_equiv]
    constructor
    · intro ⟨hne, hp, hq⟩
      refine ⟨?_, fun i => ?_⟩
      · intro heq
        apply hne
        have h1 : pv = qv := congrFun heq 0
        have h2 : recStrongPowerGraph_vertex_equiv G n prest =
                  recStrongPowerGraph_vertex_equiv G n qrest := by
          funext i; exact congrFun heq i.succ
        exact Prod.ext h1 ((recStrongPowerGraph_vertex_equiv G n).injective h2)
      · match i with
        | ⟨0, _⟩ => exact hp
        | ⟨j + 1, hj⟩ =>
          cases hq with
          | inl heq =>
            -- prest = qrest, the rest of the function values are equal
            left
            subst heq
            rfl
          | inr hadj =>
            have := (ih prest qrest).mp hadj
            exact this.2 ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    · intro ⟨hne, hall⟩
      refine ⟨?_, ?_, ?_⟩
      · intro heq; cases heq; exact hne rfl
      · exact hall 0
      · by_cases heq : prest = qrest
        · left; exact heq
        · right
          have h_rest_ne : recStrongPowerGraph_vertex_equiv G n prest ≠
                           recStrongPowerGraph_vertex_equiv G n qrest :=
            fun h => heq ((recStrongPowerGraph_vertex_equiv G n).injective h)
          have h_rest_all : ∀ i, recStrongPowerGraph_vertex_equiv G n prest i =
                                 recStrongPowerGraph_vertex_equiv G n qrest i ∨
                            G.graph.Adj (recStrongPowerGraph_vertex_equiv G n prest i)
                                        (recStrongPowerGraph_vertex_equiv G n qrest i) := by
            intro i
            exact hall i.succ
          exact (ih prest qrest).mpr ⟨h_rest_ne, h_rest_all⟩

/-- The SimpleGraph isomorphism between recStrongPowerGraph and strongPowerGraph. -/
def recStrongPowerGraph_iso (G : Graph) (m : ℕ) :
    (recStrongPowerGraph G m).graph ≃g (strongPowerGraph G m).graph where
  toEquiv := recStrongPowerGraph_vertex_equiv G m
  map_rel_iff' := (recStrongPowerGraph_adj_iff G m _ _).symm

/-- The graph join (complete join) of two graphs.
    The join G + H has all edges of G, all edges of H, plus all edges between
    every vertex of G and every vertex of H. This is the complement of disjoint union
    of complements: G + H = (Ḡ ⊔ H̄)̄. -/
def Graph.join (G H : Graph) : Graph :=
  { V := G.V ⊕ H.V, graph := {
    Adj := fun x y => match x, y with
      | .inl a, .inl b => G.graph.Adj a b
      | .inr a, .inr b => H.graph.Adj a b
      | .inl _, .inr _ => True  -- All cross edges
      | .inr _, .inl _ => True  -- All cross edges
    symm := by
      intro x y h
      match x, y with
      | .inl a, .inl b => exact G.graph.symm h
      | .inr a, .inr b => exact H.graph.symm h
      | .inl _, .inr _ => exact trivial
      | .inr _, .inl _ => exact trivial
    loopless := ⟨by
      intro x h
      match x with
      | .inl a => exact G.graph.irrefl h
      | .inr a => exact H.graph.irrefl h⟩
  }}

notation:60 G " +ᴳ " H => Graph.join G H

/-! ### Cohomomorphisms and graph operations -/

/-- A cohomomorphism on the first factor of a strong product.
    If f : G → G' is a cohomomorphism, then (f × id) : G ⊠ H → G' ⊠ H is too. -/
theorem _root_.IsCohom.strongProduct_map_fst {V V' W : Type*}
    {G : SimpleGraph V} {G' : SimpleGraph V'} {H : SimpleGraph W}
    {f : V → V'} (hf : IsCohom G G' f) :
    IsCohom (ShannonCapacity.strongProduct G H)
            (ShannonCapacity.strongProduct G' H)
            (Prod.map f _root_.id) := by
  intro ⟨a, x⟩ ⟨b, y⟩ hne hnadj
  simp only [ShannonCapacity.strongProduct, Prod.map_apply] at hnadj ⊢
  -- Strong product Adj: (a,x) ~ (b,y) ↔ (a,x) ≠ (b,y) ∧ (a=b ∨ G~ab) ∧ (x=y ∨ H~xy)
  -- hnadj: ¬((a,x) ≠ (b,y) ∧ (a=b ∨ G.Adj a b) ∧ (x=y ∨ H.Adj x y))
  -- Since hne: (a,x) ≠ (b,y), hnadj simplifies to: ¬((a=b ∨ G~ab) ∧ (x=y ∨ H~xy))
  have hnadj' : ¬((a = b ∨ G.Adj a b) ∧ (x = y ∨ H.Adj x y)) := by
    intro ⟨h1, h2⟩
    exact hnadj ⟨hne, h1, h2⟩
  -- Split cases based on whether a = b
  by_cases hab : a = b
  · -- a = b, so from hnadj', we get ¬(x = y ∨ H.Adj x y)
    have hxy_stuff : ¬(x = y ∨ H.Adj x y) := fun h => hnadj' ⟨Or.inl hab, h⟩
    push_neg at hxy_stuff
    have ⟨hxy, hnadj_H⟩ := hxy_stuff
    constructor
    · -- (f a, x) ≠ (f b, y)
      intro heq
      exact hxy (Prod.mk.inj heq).2
    · -- ¬Adj in target
      intro ⟨_, _, hH⟩
      exact hH.elim hxy hnadj_H
  · -- a ≠ b
    -- Need: ¬G.Adj a b to use hf
    -- From hnadj': ¬((a = b ∨ G.Adj a b) ∧ (x = y ∨ H.Adj x y))
    -- Either ¬(a = b ∨ G.Adj a b) OR ¬(x = y ∨ H.Adj x y)
    by_cases hG : G.Adj a b
    · -- G.Adj a b, so from hnadj' we get ¬(x = y ∨ H.Adj x y)
      have hxy_stuff : ¬(x = y ∨ H.Adj x y) := fun h => hnadj' ⟨Or.inr hG, h⟩
      push_neg at hxy_stuff
      have ⟨hxy, hnadj_H⟩ := hxy_stuff
      constructor
      · intro heq; exact hxy (Prod.mk.inj heq).2
      · intro ⟨_, _, hH⟩; exact hH.elim hxy hnadj_H
    · -- ¬G.Adj a b, so we can use hf
      have ⟨hfne, hfnadj⟩ := hf a b hab hG
      constructor
      · intro heq; exact hfne (Prod.mk.inj heq).1
      · intro ⟨_, hG', _⟩; exact hG'.elim hfne hfnadj

/-- Cohom is preserved by strong product on the first factor. -/
theorem _root_.Cohom.strongProduct_left {V V' W : Type*}
    {G : SimpleGraph V} {G' : SimpleGraph V'} (H : SimpleGraph W)
    (hGG' : G ≤_G G') :
    ShannonCapacity.strongProduct G H ≤_G ShannonCapacity.strongProduct G' H := by
  obtain ⟨f, hf⟩ := hGG'
  exact ⟨Prod.map f _root_.id, hf.strongProduct_map_fst⟩

/-- A cohomomorphism on both components of a disjoint union.
    If f : G → G' and g : H → H' are cohomomorphisms, then
    Sum.map f g : G ⊔ H → G' ⊔ H' is too. -/
theorem _root_.IsCohom.disjointUnion_map {V V' W W' : Type*}
    {G : SimpleGraph V} {G' : SimpleGraph V'}
    {H : SimpleGraph W} {H' : SimpleGraph W'}
    {f : V → V'} {g : W → W'}
    (hf : IsCohom G G' f) (hg : IsCohom H H' g) :
    IsCohom (disjUnionSimple G H) (disjUnionSimple G' H') (Sum.map f g) := by
  intro x y hxy hnadj
  match x, y with
  | .inl a, .inl b =>
    simp only [disjUnionSimple, Sum.map_inl] at hnadj ⊢
    have hab : a ≠ b := fun h => hxy (congrArg Sum.inl h)
    have ⟨hfne, hfnadj⟩ := hf a b hab hnadj
    exact ⟨fun h => hfne (Sum.inl.inj h), hfnadj⟩
  | .inr a, .inr b =>
    simp only [disjUnionSimple, Sum.map_inr] at hnadj ⊢
    have hab : a ≠ b := fun h => hxy (congrArg Sum.inr h)
    have ⟨hgne, hgnadj⟩ := hg a b hab hnadj
    exact ⟨fun h => hgne (Sum.inr.inj h), hgnadj⟩
  | .inl a, .inr b =>
    simp only [disjUnionSimple, Sum.map_inl, Sum.map_inr] at hnadj ⊢
    exact ⟨Sum.inl_ne_inr, False.elim⟩
  | .inr a, .inl b =>
    simp only [disjUnionSimple, Sum.map_inr, Sum.map_inl] at hnadj ⊢
    exact ⟨Sum.inr_ne_inl, False.elim⟩

/-- Cohom is preserved by disjoint union. -/
theorem _root_.Cohom.disjointUnion_map {V V' W W' : Type*}
    {G : SimpleGraph V} {G' : SimpleGraph V'}
    {H : SimpleGraph W} {H' : SimpleGraph W'}
    (hGG' : G ≤_G G') (hHH' : H ≤_G H') :
    disjUnionSimple G H ≤_G disjUnionSimple G' H' := by
  obtain ⟨f, hf⟩ := hGG'
  obtain ⟨g, hg⟩ := hHH'
  exact ⟨Sum.map f g, hf.disjointUnion_map hg⟩

/-- Cohom is preserved by strong power.
    If G ≤_G H, then G^⊠n ≤_G H^⊠n for all n. -/
theorem _root_.Cohom.strongPower {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hGH : G ≤_G H) (n : ℕ) :
    SimpleGraph.strongPower G n ≤_G SimpleGraph.strongPower H n := by
  obtain ⟨f, hf⟩ := hGH
  -- Define the induced function on Fin n → V
  let fn := fun x : Fin n → V => fun i => f (x i)
  -- Use the existing theorem
  have hfn := SimpleGraph.strongPower_cohomomorphism_of_cohomomorphism G H f hf n
  exact ⟨fn, hfn⟩

/-- The left injection inl is a cohomomorphism from G to G +ᴳ H.
    Non-adjacent pairs in G remain non-adjacent when embedded into the join. -/
theorem _root_.IsCohom.join_inl (G H : Graph) :
    IsCohom G.graph (G +ᴳ H).graph Sum.inl := by
  intro a b hab hnadj
  simp only [Graph.join] at *
  constructor
  · intro heq; exact hab (Sum.inl.inj heq)
  · intro hadj; exact hnadj hadj  -- (G +ᴳ H).Adj (inl a) (inl b) = G.Adj a b

/-- The right injection inr is a cohomomorphism from H to G +ᴳ H. -/
theorem _root_.IsCohom.join_inr (G H : Graph) :
    IsCohom H.graph (G +ᴳ H).graph Sum.inr := by
  intro a b hab hnadj
  simp only [Graph.join] at *
  constructor
  · intro heq; exact hab (Sum.inr.inj heq)
  · intro hadj; exact hnadj hadj  -- (G +ᴳ H).Adj (inr a) (inr b) = H.Adj a b

/-- G has a cohomomorphism to G +ᴳ H via the left injection. -/
theorem _root_.Cohom.join_left (G H : Graph) : G.graph ≤_G (G +ᴳ H).graph :=
  ⟨Sum.inl, IsCohom.join_inl G H⟩

/-- H has a cohomomorphism to G +ᴳ H via the right injection. -/
theorem _root_.Cohom.join_right (G H : Graph) : H.graph ≤_G (G +ᴳ H).graph :=
  ⟨Sum.inr, IsCohom.join_inr G H⟩

/-- A cohomomorphism on both components of a graph join.
    If f : G → G' and g : H → H' are cohomomorphisms, then
    Sum.map f g : G +ᴳ H → G' +ᴳ H' is too.

    Key insight: In a graph join, non-edges only exist within components
    (cross-edges are always present), so component-wise cohoms suffice. -/
theorem _root_.IsCohom.join_map {G G' H H' : Graph}
    {f : G.V → G'.V} {g : H.V → H'.V}
    (hf : IsCohom G.graph G'.graph f) (hg : IsCohom H.graph H'.graph g) :
    IsCohom (G +ᴳ H).graph (G' +ᴳ H').graph (Sum.map f g) := by
  intro x y hxy hnadj
  match x, y with
  | .inl a, .inl b =>
    simp only [Graph.join, Sum.map_inl] at hnadj ⊢
    have hab : a ≠ b := fun h => hxy (congrArg Sum.inl h)
    have ⟨hfne, hfnadj⟩ := hf a b hab hnadj
    exact ⟨fun h => hfne (Sum.inl.inj h), hfnadj⟩
  | .inr a, .inr b =>
    simp only [Graph.join, Sum.map_inr] at hnadj ⊢
    have hab : a ≠ b := fun h => hxy (congrArg Sum.inr h)
    have ⟨hgne, hgnadj⟩ := hg a b hab hnadj
    exact ⟨fun h => hgne (Sum.inr.inj h), hgnadj⟩
  | .inl _, .inr _ =>
    -- Cross-edges: always adjacent in both source and target
    simp only [Graph.join] at hnadj
    -- hnadj says ¬True, contradiction
    exact (hnadj trivial).elim
  | .inr _, .inl _ =>
    simp only [Graph.join] at hnadj
    exact (hnadj trivial).elim

/-- Cohom is preserved by graph join. -/
theorem _root_.Cohom.join_map' {G G' H H' : Graph}
    (hGG' : G.graph ≤_G G'.graph) (hHH' : H.graph ≤_G H'.graph) :
    (G +ᴳ H).graph ≤_G (G' +ᴳ H').graph := by
  obtain ⟨f, hf⟩ := hGG'
  obtain ⟨g, hg⟩ := hHH'
  exact ⟨Sum.map f g, hf.join_map hg⟩

/-- If both components of a join have cohoms to the same target,
    so does the join.

    Key insight: Non-edges in G +ᴳ H only exist within components.
    The combined map Sum.elim f g sends each component using its cohom,
    and since cross-edges in the source are always present (so never non-edges),
    they don't constrain the map. -/
theorem _root_.IsCohom.join_to_common {G H K : Graph}
    {f : G.V → K.V} {g : H.V → K.V}
    (hf : IsCohom G.graph K.graph f) (hg : IsCohom H.graph K.graph g) :
    IsCohom (G +ᴳ H).graph K.graph (Sum.elim f g) := by
  intro x y hxy hnadj
  match x, y with
  | .inl a, .inl b =>
    simp only [Graph.join, Sum.elim_inl] at hnadj ⊢
    have hab : a ≠ b := fun h => hxy (congrArg Sum.inl h)
    exact hf a b hab hnadj
  | .inr a, .inr b =>
    simp only [Graph.join, Sum.elim_inr] at hnadj ⊢
    have hab : a ≠ b := fun h => hxy (congrArg Sum.inr h)
    exact hg a b hab hnadj
  | .inl _, .inr _ =>
    -- Cross-edges are always adjacent in G +ᴳ H
    simp only [Graph.join] at hnadj
    exact (hnadj trivial).elim
  | .inr _, .inl _ =>
    simp only [Graph.join] at hnadj
    exact (hnadj trivial).elim

/-- If both components of a join have cohoms to the same target,
    so does the join (Cohom version). -/
theorem _root_.Cohom.join_to_common (G H K : Graph)
    (hGK : G.graph ≤_G K.graph) (hHK : H.graph ≤_G K.graph) :
    (G +ᴳ H).graph ≤_G K.graph := by
  obtain ⟨f, hf⟩ := hGK
  obtain ⟨g, hg⟩ := hHK
  exact ⟨Sum.elim f g, hf.join_to_common hg⟩

/-! ### Spectral points -/

/-- A spectral point is a function from graphs to non-negative reals
    satisfying the four spectral axioms.

    The four axioms are:
    (i)   φ(E_n) = n for edgeless graphs on n vertices (including E_0 = 0)
    (ii)  φ(G ⊠ H) = φ(G) · φ(H) (multiplicative under strong product)
    (iii) φ(G ⊔ H) = φ(G) + φ(H) (additive under disjoint union)
    (iv)  G ≤_G H implies φ(G) ≤ φ(H) (monotone under cohomomorphism)

    These axioms characterize graph parameters in the asymptotic spectrum.
    Examples include Shannon capacity Θ, fractional clique cover number χ̄_f,
    and Lovász theta function ϑ. -/
structure SpectralPoint where
  /-- The evaluation function mapping graphs to non-negative reals -/
  eval : Graph → ℝ

  /-- Axiom (i): Normalization - φ(E_n) = n for edgeless graphs.
      This includes φ(E_0) = 0 for the empty graph. -/
  normalized : ∀ n : ℕ, eval (EdgelessGraph n) = n

  /-- Axiom (ii): Multiplicativity - φ(G ⊠ H) = φ(G) · φ(H).
      The parameter is multiplicative under strong product. -/
  mul_strongProduct : ∀ G H : Graph, eval (G ⊠ H) = eval G * eval H

  /-- Axiom (iii): Additivity - φ(G ⊔ H) = φ(G) + φ(H).
      The parameter is additive under disjoint union. -/
  add_disjointUnion : ∀ G H : Graph, eval (G ⊔ᴳ H) = eval G + eval H

  /-- Axiom (iv): Monotonicity - G ≤_G H implies φ(G) ≤ φ(H).
      The parameter is monotone under the cohomomorphism preorder. -/
  mono_cohom : ∀ G H : Graph, (∃ f, IsCohom G.graph H.graph f) → eval G ≤ eval H

instance : CoeFun SpectralPoint (fun _ => Graph → ℝ) where
  coe := SpectralPoint.eval

/-- The empty graph E_0 has a cohomomorphism to any graph G.
    Since E_0 has no vertices, the empty function is trivially a cohomomorphism. -/
theorem edgelessGraph_zero_cohom_to_any (G : Graph) : Cohom (edgelessGraph 0) G.graph := by
  use fun x => (Fin.elim0 x : G.V)
  intro u v _ _
  exact Fin.elim0 u

/-- Non-negativity follows from the axioms: φ(G) ≥ 0 for all G.
    Proof: E_0 has φ(E_0) = 0, and E_0 ≤_G G for any G (empty function is a cohomomorphism),
    so by monotonicity 0 = φ(E_0) ≤ φ(G). -/
theorem SpectralPoint.nonneg (φ : SpectralPoint) (G : Graph) : 0 ≤ φ.eval G := by
  -- φ(E_0) = 0 by normalized axiom
  have h0 : φ.eval (EdgelessGraph 0) = 0 := by
    have := φ.normalized 0
    simp only [Nat.cast_zero] at this
    exact this
  -- E_0 ≤_G G, so φ(E_0) ≤ φ(G) by monotonicity
  have hmono : φ.eval (EdgelessGraph 0) ≤ φ.eval G := by
    apply φ.mono_cohom
    exact edgelessGraph_zero_cohom_to_any G
  -- Combine: 0 = φ(E_0) ≤ φ(G)
  rw [← h0]
  exact hmono

/-- Spectral evaluation of recursive strong power by induction. -/
theorem eval_recStrongPowerGraph (φ : SpectralPoint) (G : Graph) (m : ℕ) :
    φ.eval (recStrongPowerGraph G m) = φ.eval G ^ m := by
  induction m with
  | zero =>
    simp only [recStrongPowerGraph, pow_zero]
    have h := φ.normalized 1
    simp only [Nat.cast_one] at h
    exact h
  | succ n ih =>
    simp only [recStrongPowerGraph, pow_succ]
    rw [φ.mul_strongProduct]
    rw [ih]
    ring

/-- The asymptotic spectrum Δ(G) is the set of all spectral points -/
def AsymptoticSpectrum : Set SpectralPoint := Set.univ

notation "Δ(G)" => AsymptoticSpectrum

end AsymptoticSpectrumGraphs
