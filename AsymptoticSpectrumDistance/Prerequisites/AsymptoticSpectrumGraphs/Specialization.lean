/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphStrassenPreorder
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumDuality.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumDuality.SpectrumDuality
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphOperations
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.FractionalCliqueCover
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Cases

/-!
# Specialization to Graphs

This file connects the abstract asymptotic spectrum theory to the concrete
case of graphs with the cohomomorphism preorder.

## Main Definitions

* `graphSpectralPointToAbstract` - Convert graph SpectralPoint to abstract SpectralPoint
* `abstractToGraphSpectralPoint` - Convert abstract SpectralPoint to graph SpectralPoint

## Main Results

* Graph and abstract spectral points are equivalent
* Graph asymptotic rank/subrank = abstract definitions

## References

* Strassen (1988), The asymptotic spectrum of tensors
-/

namespace AsymptoticSpectrumGraphs

open SimpleGraph
open AsymptoticSpectrumDuality

/-! ### Lifting Graph SpectralPoint to GraphClass -/

/-- A graph SpectralPoint respects isomorphism: φ(G) = φ(G') if G ≅ G'. -/
theorem SpectralPoint.eval_congr (φ : SpectralPoint) {G G' : Graph}
    (hiso : GraphIso G G') : φ.eval G = φ.eval G' := by
  -- If G ≅ G', then G ≤_G G' and G' ≤_G G, so by monotonicity we get equality
  obtain ⟨iso⟩ := hiso
  have h1 : Cohom G.graph G'.graph := cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE iso)
  have h2 : Cohom G'.graph G.graph := cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE iso.symm)
  exact le_antisymm (φ.mono_cohom G G' h1) (φ.mono_cohom G' G h2)

/-- Lift graph SpectralPoint.eval to GraphClass. -/
def SpectralPoint.evalClass (φ : SpectralPoint) : GraphClass → ℝ :=
  Quotient.lift φ.eval (fun _ _ h => φ.eval_congr h)

theorem SpectralPoint.evalClass_mk (φ : SpectralPoint) (G : Graph) :
    φ.evalClass (GraphClass.mk G) = φ.eval G := rfl

/-! ### Graph SpectralPoint → Abstract SpectralPoint -/

/-- Convert a graph SpectralPoint to an abstract SpectralPoint for graphStrassenPreorder. -/
def graphSpectralPointToAbstract (φ : SpectralPoint) :
    AsymptoticSpectrumDuality.SpectralPoint graphStrassenPreorder where
  toFun := φ.evalClass
  map_zero := by
    change φ.evalClass (GraphClass.mk (EdgelessGraph 0)) = 0
    rw [SpectralPoint.evalClass_mk]
    have := φ.normalized 0
    simp only [Nat.cast_zero] at this
    exact this
  map_one := by
    change φ.evalClass (GraphClass.mk (EdgelessGraph 1)) = 1
    rw [SpectralPoint.evalClass_mk]
    have := φ.normalized 1
    simp only [Nat.cast_one] at this
    exact this
  map_add := by
    intro a b
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    change φ.evalClass (GraphClass.mk G + GraphClass.mk H) =
           φ.evalClass (GraphClass.mk G) + φ.evalClass (GraphClass.mk H)
    rw [GraphClass.add_def, SpectralPoint.evalClass_mk, SpectralPoint.evalClass_mk,
        SpectralPoint.evalClass_mk]
    exact φ.add_disjointUnion G H
  map_mul := by
    intro a b
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    change φ.evalClass (GraphClass.mk G * GraphClass.mk H) =
           φ.evalClass (GraphClass.mk G) * φ.evalClass (GraphClass.mk H)
    rw [GraphClass.mul_def, SpectralPoint.evalClass_mk, SpectralPoint.evalClass_mk,
        SpectralPoint.evalClass_mk]
    exact φ.mul_strongProduct G H
  monotone := by
    intro a b hab
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    change φ.evalClass (GraphClass.mk G) ≤ φ.evalClass (GraphClass.mk H)
    rw [SpectralPoint.evalClass_mk, SpectralPoint.evalClass_mk]
    -- hab : graphCohom ⟦G⟧ ⟦H⟧ = Cohom G.graph H.graph
    change Cohom G.graph H.graph at hab
    exact φ.mono_cohom G H hab
  nonneg := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    change 0 ≤ φ.evalClass (GraphClass.mk G)
    rw [SpectralPoint.evalClass_mk]
    exact φ.nonneg G

/-! ### Abstract SpectralPoint → Graph SpectralPoint -/

/-- Convert an abstract SpectralPoint for graphStrassenPreorder to a graph SpectralPoint. -/
def abstractToGraphSpectralPoint
    (ψ : AsymptoticSpectrumDuality.SpectralPoint graphStrassenPreorder) :
    SpectralPoint where
  eval := fun G => ψ.toFun (GraphClass.mk G)
  normalized := by
    intro n
    -- Need to show ψ(E_n) = n, where E_n = EdgelessGraph n represents (n : GraphClass)
    -- By natCast_eq_edgeless: (n : GraphClass) = GraphClass.mk (EdgelessGraph n)
    -- Then ψ.toFun n = n follows from map_zero, map_one, map_add by induction
    rw [← GraphClass.natCast_eq_edgeless]
    -- Now need ψ.toFun (n : GraphClass) = (n : ℝ)
    induction n with
    | zero =>
      simp only [Nat.cast_zero]
      exact ψ.map_zero
    | succ n ih =>
      simp only [Nat.cast_succ]
      rw [ψ.map_add, ψ.map_one, ih]
  mul_strongProduct := by
    intro G H
    have h := ψ.map_mul (GraphClass.mk G) (GraphClass.mk H)
    change ψ.toFun (GraphClass.mk (G ⊠ H)) = _
    rw [← GraphClass.mul_def]
    exact h
  add_disjointUnion := by
    intro G H
    have h := ψ.map_add (GraphClass.mk G) (GraphClass.mk H)
    change ψ.toFun (GraphClass.mk (G ⊔ᴳ H)) = _
    rw [← GraphClass.add_def]
    exact h
  mono_cohom := by
    intro G H hcohom
    have hmono := ψ.monotone (GraphClass.mk G) (GraphClass.mk H)
    apply hmono
    change Cohom G.graph H.graph at hcohom
    exact hcohom

/-! ### Equivalence of Spectral Points -/

/-- The conversion from graph SpectralPoint to abstract and back is the identity. -/
theorem graphSpectralPoint_roundtrip (φ : SpectralPoint) :
    abstractToGraphSpectralPoint (graphSpectralPointToAbstract φ) = φ := by
  cases φ
  simp only [abstractToGraphSpectralPoint, graphSpectralPointToAbstract,
             SpectralPoint.evalClass_mk]

/-- The conversion from abstract SpectralPoint to graph and back. -/
theorem abstractSpectralPoint_roundtrip
    (ψ : AsymptoticSpectrumDuality.SpectralPoint graphStrassenPreorder) :
    graphSpectralPointToAbstract (abstractToGraphSpectralPoint ψ) = ψ := by
  -- Need to show equality of SpectralPoint structures
  -- Key: (abstractToGraphSpectralPoint ψ).evalClass = ψ.toFun
  have hfun : (abstractToGraphSpectralPoint ψ).evalClass = ψ.toFun := by
    ext a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    -- evalClass (⟦G⟧) = φ.eval G = ψ.toFun (GraphClass.mk G) = ψ.toFun ⟦G⟧
    simp only [abstractToGraphSpectralPoint]
    rfl
  cases ψ with | mk toFun _ _ _ _ _ _ =>
  simp only [graphSpectralPointToAbstract, abstractToGraphSpectralPoint] at hfun ⊢
  congr 1

/-! ### Graph Asymptotic Rank/Subrank via Abstract Definition -/

/-- The asymptotic rank of a graph class via the abstract definition. -/
noncomputable def graphAsympRank (a : GraphClass) : ℝ :=
  graphStrassenPreorder.asympRank a

/-- The asymptotic subrank of a graph class via the abstract definition. -/
noncomputable def graphAsympSubrank (a : GraphClass) : ℝ :=
  graphStrassenPreorder.asympSubrank a

/-- The graph asymptotic rank equals the supremum over abstract spectral points.
    This follows from asympRank_eq_iSup_spectrum in the abstract theory. -/
theorem graphAsympRank_eq_iSup_spectrum
    [Nonempty (AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder)]
    (a : GraphClass)
    (ha : ∃ φ : AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder,
          1 ≤ AsymptoticSpectrumDuality.AsymptoticSpectrum.eval
                graphStrassenPreorder a φ) :
    graphAsympRank a =
      ⨆ φ : AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder,
        AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder a φ := by
  unfold graphAsympRank
  exact graphStrassenPreorder.asympRank_eq_iSup_spectrum a ha

/-! ### Graph Rank and Subrank (non-asymptotic) -/

/-- The rank of a graph class: smallest n such that G ≤_coh E_n.
    This equals the clique cover number χ̄(G) = χ(Gᶜ). -/
noncomputable def graphRank (a : GraphClass) : ℕ :=
  graphStrassenPreorder.rank a

/-- The subrank of a graph class: largest n such that E_n ≤_coh G.
    This equals the independence number α(G). -/
noncomputable def graphSubrank (a : GraphClass) : ℕ :=
  graphStrassenPreorder.subrank a

/-- The subrank of a graph equals its independence number.
    E_n ≤_coh G iff G has an independent set of size n. -/
theorem graphSubrank_eq_indepNum (G : Graph) :
    graphSubrank (GraphClass.mk G) = G.graph.indepNum := by
  simp only [graphSubrank, StrassenPreorder.subrank, SimpleGraph.indepNum]
  -- subrank = sSup { n : ℕ | graphCohom n G }
  -- indepNum = sSup { s.card | s is independent set }
  -- These are equal since E_n →_coh G iff G has independent set of size n
  congr 1
  ext n
  simp only [Set.mem_setOf_eq, graphStrassenPreorder]
  -- Rewrite n : GraphClass to EdgelessGraph n
  have hnat : (n : GraphClass) = GraphClass.mk (EdgelessGraph n) := GraphClass.natCast_eq_edgeless n
  rw [hnat, graphCohom_mk]
  simp only [EdgelessGraph]
  constructor
  · -- If E_n →_coh G, then G has an independent set of size n
    intro ⟨f, hf⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      by_contra hne
      have hnadj : ¬(edgelessGraph n).Adj x y := by simp [edgelessGraph]
      have ⟨hfne, _⟩ := hf x y hne hnadj
      exact hfne hxy
    -- The image of f is an independent set of size n
    have himg : G.graph.IsNIndepSet n (Finset.univ.map ⟨f, hinj⟩) := by
      constructor
      · -- IsIndepSet: pairwise non-adjacent
        intro v hv w hw hvw
        simp only [Finset.coe_map, Finset.coe_univ, Set.image_univ, Set.mem_range] at hv hw
        obtain ⟨x, rfl⟩ := hv
        obtain ⟨y, rfl⟩ := hw
        have hxy : x ≠ y := fun h => hvw (congrArg f h)
        exact (hf x y hxy (by simp [edgelessGraph])).2
      · -- Card = n
        simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact ⟨_, himg⟩
  · -- If G has an independent set of size n, then E_n →_coh G
    intro ⟨s, hs⟩
    obtain ⟨hindep, hcard⟩ := hs
    -- Get an equivalence between Fin n and s
    have hcard' : Fintype.card s = n := by
      simp only [Fintype.card_coe]
      exact hcard
    let e : Fin n ≃ s := (Fintype.equivFinOfCardEq hcard').symm
    use fun i => (e i).val
    intro x y hxy _hnadj
    constructor
    · intro heq
      have : e x = e y := Subtype.ext heq
      exact hxy (e.injective this)
    · intro hadj
      have hx : (e x).val ∈ s := (e x).property
      have hy : (e y).val ∈ s := (e y).property
      have hne : (e x).val ≠ (e y).val := by
        intro h
        exact hxy (e.injective (Subtype.ext h))
      exact hindep hx hy hne hadj

/-- Cohomomorphism to edgeless graph is equivalent to coloring the complement.
    G →_coh E_n iff Gᶜ is n-colorable. -/
theorem cohom_edgeless_iff_compl_colorable (G : Graph) (n : ℕ) :
    Cohom G.graph (edgelessGraph n) ↔ G.graphᶜ.Colorable n := by
  constructor
  · -- Cohomomorphism → Coloring
    intro ⟨f, hf⟩
    -- f is a valid coloring of Gᶜ: adjacent in Gᶜ means non-adjacent in G
    refine ⟨SimpleGraph.Coloring.mk f ?_⟩
    intro v w hadj
    -- hadj : Gᶜ.Adj v w means v ≠ w ∧ ¬G.Adj v w
    simp only [SimpleGraph.compl_adj] at hadj
    obtain ⟨hne, hnadj⟩ := hadj
    -- Apply cohomomorphism property
    exact (hf v w hne hnadj).1
  · -- Coloring → Cohomomorphism
    intro ⟨c⟩
    use c
    intro u v huv hnadj
    constructor
    · -- f(u) ≠ f(v)
      apply c.valid
      simp only [SimpleGraph.compl_adj]
      exact ⟨huv, hnadj⟩
    · -- ¬E_n.Adj f(u) f(v) (trivial since E_n has no edges)
      simp [edgelessGraph]

/-- The rank of a graph equals its clique cover number (= chromatic number of complement).
    G ≤_coh E_n iff G can be partitioned into n cliques. -/
theorem graphRank_eq_cliqueCoverNum (G : Graph) :
    graphRank (GraphClass.mk G) = G.graphᶜ.chromaticNumber := by
  classical
  -- Any graph on n vertices is n-colorable (use identity coloring)
  have hcol : G.graphᶜ.Colorable (Fintype.card G.V) := by
    refine ⟨SimpleGraph.Coloring.mk (Fintype.equivFin G.V) ?_⟩
    intro v w hadj
    exact (Fintype.equivFin G.V).injective.ne hadj.ne
  rw [SimpleGraph.Colorable.chromaticNumber_eq_sInf hcol]
  -- Show the two ℕ values are equal
  simp only [graphRank, StrassenPreorder.rank]
  congr 1
  -- Both are infima of the same set (up to equivalent characterizations)
  apply le_antisymm
  · -- Nat.find { n | G ≤_coh E_n } ≤ sInf { n | Gᶜ.Colorable n }
    -- Take n = sInf {colorable}, show G ≤_coh E_n
    have hinf := Nat.sInf_mem (⟨Fintype.card G.V, hcol⟩ : { n | G.graphᶜ.Colorable n }.Nonempty)
    simp only [Set.mem_setOf_eq] at hinf
    have hcohom : Cohom G.graph (edgelessGraph (sInf {n | G.graphᶜ.Colorable n})) :=
      (cohom_edgeless_iff_compl_colorable G _).mpr hinf
    have hrel : graphStrassenPreorder.rel (GraphClass.mk G)
        (sInf {n | G.graphᶜ.Colorable n} : ℕ) := by
      simp only [graphStrassenPreorder]
      rw [GraphClass.natCast_eq_edgeless, graphCohom_mk, EdgelessGraph]
      exact hcohom
    exact Nat.find_le hrel
  · -- sInf { n | Gᶜ.Colorable n } ≤ Nat.find { n | G ≤_coh E_n }
    -- Take n = Nat.find, show Gᶜ.Colorable n
    have hfind := Nat.find_spec (graphStrassenPreorder.exists_rel_nat (GraphClass.mk G))
    simp only [graphStrassenPreorder] at hfind
    rw [GraphClass.natCast_eq_edgeless, graphCohom_mk, EdgelessGraph] at hfind
    have hcolorable : G.graphᶜ.Colorable (Nat.find (graphStrassenPreorder.exists_rel_nat
        (GraphClass.mk G))) :=
      (cohom_edgeless_iff_compl_colorable G _).mp hfind
    exact Nat.sInf_le hcolorable

/-! ### Gapped Graph Condition -/

/-- IsStrictlyGappedGraph implies the abstract IsGapped condition. -/
theorem IsStrictlyGappedGraph_implies_IsGapped (a : GraphClass) :
    IsStrictlyGappedGraph a → graphStrassenPreorder.IsGapped a := by
  intro ⟨k, hk_pos, hrel⟩
  exact Or.inl ⟨k, hk_pos, hrel⟩

/-- Every graph class satisfies the generalized IsGapped condition.
    This follows from the trichotomy: every graph is either
    - the empty graph (equivalent to 0),
    - a complete graph (equivalent to 1), or
    - has an independent pair (strictly gapped). -/
theorem graph_isGapped (a : GraphClass) : graphStrassenPreorder.IsGapped a := by
  -- We show that every graph is gapped by analyzing the representative
  obtain ⟨G, rfl⟩ := Quotient.exists_rep a
  -- Case split on whether G has at least 2 non-adjacent vertices
  by_cases hindep : ∃ v₀ v₁ : G.V, v₀ ≠ v₁ ∧ ¬G.graph.Adj v₀ v₁
  · -- Case: G has independent pair → strictly gapped
    exact IsStrictlyGappedGraph_implies_IsGapped _ (graphs_with_independent_pair_gapped G hindep)
  · -- Case: G is a complete graph (or has ≤ 1 vertex)
    push_neg at hindep
    -- Either G has 0 or 1 vertices, or all pairs are adjacent
    by_cases hempty : IsEmpty G.V
    · -- G is the empty graph, equivalent to 0
      right; left
      change graphCohom (GraphClass.mk G) 0
      rw [GraphClass.zero_def, graphCohom_mk]
      simp only [EdgelessGraph]
      use fun v => hempty.elim v
      intro v; exact hempty.elim v
    · -- G has at least one vertex
      rw [not_isEmpty_iff] at hempty
      obtain ⟨v₀⟩ := hempty
      by_cases hsize : ∀ v : G.V, v = v₀
      · -- G has exactly one vertex, equivalent to 1
        right; right
        have h1eq : ((1 : ℕ) : GraphClass) = GraphClass.mk (EdgelessGraph 1) :=
          GraphClass.natCast_eq_edgeless 1
        simp only [Nat.cast_one] at h1eq
        constructor
        · -- G ≤ 1: G →_G E_1
          change graphCohom (GraphClass.mk G) (1 : GraphClass)
          rw [h1eq, graphCohom_mk]
          simp only [EdgelessGraph]
          use fun _ => ⟨0, by omega⟩
          intro u v huv hnadj
          have := hsize u
          have := hsize v
          simp_all
        · -- 1 ≤ G: E_1 →_G G
          change graphCohom (1 : GraphClass) (GraphClass.mk G)
          rw [h1eq, graphCohom_mk]
          simp only [EdgelessGraph]
          use fun _ => v₀
          intro u v huv
          fin_cases u; fin_cases v; simp_all
      · -- G has ≥ 2 vertices and all pairs are adjacent (complete graph)
        -- Complete graphs are equivalent to 1
        push_neg at hsize
        obtain ⟨v₁, hv₁_ne⟩ := hsize
        have hadj := hindep v₀ v₁ hv₁_ne.symm
        -- G is a complete graph on ≥ 2 vertices
        right; right
        have h1eq : ((1 : ℕ) : GraphClass) = GraphClass.mk (EdgelessGraph 1) :=
          GraphClass.natCast_eq_edgeless 1
        simp only [Nat.cast_one] at h1eq
        constructor
        · -- G ≤ 1: map all to single vertex
          change graphCohom (GraphClass.mk G) (1 : GraphClass)
          rw [h1eq, graphCohom_mk]
          simp only [EdgelessGraph]
          use fun _ => ⟨0, by omega⟩
          intro u v huv hnadj
          -- All distinct pairs in G are adjacent, so hnadj can't hold
          exfalso
          exact hnadj (hindep u v huv)
        · -- 1 ≤ G: map the single vertex to any vertex of G
          change graphCohom (1 : GraphClass) (GraphClass.mk G)
          rw [h1eq, graphCohom_mk]
          simp only [EdgelessGraph]
          use fun _ => v₀
          intro u v huv
          fin_cases u; fin_cases v; simp_all

/-- The graph asymptotic subrank equals the infimum over abstract spectral points.
    This holds for ALL graph classes (no hypothesis needed) since every graph
    is either empty, complete, or has an independent pair. -/
theorem graphAsympSubrank_eq_iInf_spectrum
    [Nonempty (AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder)]
    (a : GraphClass) :
    graphAsympSubrank a =
      ⨅ φ : AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder,
        AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder a φ := by
  unfold graphAsympSubrank
  exact graphStrassenPreorder.asympSubrank_eq_iInf_spectrum a (graph_isGapped a)

/-- For any graph, there exists a spectral point achieving the minimum.
    This follows from asympSubrank_eq_min_spectrum in the abstract theory. -/
theorem graphAsympSubrank_eq_min_spectrum
    [Nonempty (AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder)]
    (a : GraphClass) :
    ∃ φ : AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder,
      graphAsympSubrank a =
        AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder a φ := by
  unfold graphAsympSubrank
  exact graphStrassenPreorder.asympSubrank_eq_min_spectrum a (graph_isGapped a)

/-! ### Asymptotic Rank and Fractional Clique Cover -/

/-- The fractional clique cover number as an abstract spectral point. -/
noncomputable def chibar_abstractSpectralPoint :
    AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder :=
  ⟨(graphSpectralPointToAbstract chibar_spectralPoint).toFun,
   (graphSpectralPointToAbstract chibar_spectralPoint).map_zero,
   (graphSpectralPointToAbstract chibar_spectralPoint).map_one,
   (graphSpectralPointToAbstract chibar_spectralPoint).map_add,
   (graphSpectralPointToAbstract chibar_spectralPoint).map_mul,
   (graphSpectralPointToAbstract chibar_spectralPoint).monotone,
   (graphSpectralPointToAbstract chibar_spectralPoint).nonneg⟩

/-- The abstract asymptotic spectrum is nonempty (witnessed by χ̄_f). -/
instance : Nonempty (AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder) :=
  ⟨chibar_abstractSpectralPoint⟩

/-- χ̄_f evaluated on a GraphClass via the abstract spectral point. -/
theorem chibar_abstractSpectralPoint_eval (a : GraphClass) :
    AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder a
      chibar_abstractSpectralPoint =
    chibar_spectralPoint.evalClass a := rfl

/-- For Graph G, the abstract spectral evaluation matches χ̄_f. -/
theorem chibar_abstractSpectralPoint_eval_mk (G : Graph) :
    AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder
      (GraphClass.mk G) chibar_abstractSpectralPoint =
    χ̄_f G := by
  simp only [chibar_abstractSpectralPoint_eval, SpectralPoint.evalClass_mk]
  rfl

/-- The graph asymptotic rank is at least χ̄_f(G). -/
theorem chibar_le_graphAsympRank (G : Graph) :
    χ̄_f G ≤ graphAsympRank (GraphClass.mk G) := by
  unfold graphAsympRank
  have heval := chibar_abstractSpectralPoint_eval_mk G
  rw [← heval]
  exact graphStrassenPreorder.spectralPoint_le_asympRank
    chibar_abstractSpectralPoint (GraphClass.mk G)

/-! ### Logarithmic Bound (Theorem 64.13 from Schrijver) -/

/-- Relationship between clique number and independence number under complement. -/
theorem cliqueNum_eq_indepNum_compl {V : Type*} (G : SimpleGraph V) :
    G.cliqueNum = Gᶜ.indepNum := by
  rw [SimpleGraph.indepNum_compl]

set_option linter.unusedFintypeInType false in
/-- For a finite graph, the chromatic number is finite. -/
theorem chromaticNumber_ne_top_of_fintype {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.chromaticNumber ≠ ⊤ := by
  rw [SimpleGraph.chromaticNumber_ne_top_iff_exists]
  exact ⟨Fintype.card V, SimpleGraph.colorable_of_fintype G⟩

/-- The graph rank equals chromaticNumber.toNat of the complement. -/
theorem graphRank_eq_chromaticNumber_toNat (G : Graph) :
    graphRank (GraphClass.mk G) = G.graphᶜ.chromaticNumber.toNat := by
  have hrank_eq := graphRank_eq_cliqueCoverNum G
  have hne_top := chromaticNumber_ne_top_of_fintype G.graphᶜ
  have hcoe : (G.graphᶜ.chromaticNumber.toNat : ℕ∞) = G.graphᶜ.chromaticNumber :=
    ENat.coe_toNat hne_top
  rw [← hcoe] at hrank_eq
  exact Nat.cast_injective hrank_eq

/-- Given a coloring, the weight of a vertex is 1/(size of its color class). -/
private noncomputable def coloringWeight {V : Type*} [Fintype V] [DecidableEq V]
    {α : Type*} [DecidableEq α] {G : SimpleGraph V}
    (C : G.Coloring α) (v : V) : ℝ :=
  1 / (Finset.univ.filter (fun w => C w = C v)).card

/-- The sum of weights over a color class equals 1. -/
private lemma coloringWeight_sum_colorClass {V : Type*} [Fintype V] [DecidableEq V]
    {α : Type*} [DecidableEq α] {G : SimpleGraph V}
    (C : G.Coloring α) (c : α) (hne : (Finset.univ.filter (fun v => C v = c)).Nonempty) :
    (Finset.univ.filter (fun v => C v = c)).sum (coloringWeight C) = 1 := by
  unfold coloringWeight
  have hcard : (Finset.univ.filter (fun v => C v = c)).card ≠ 0 := by
    simp only [Finset.card_ne_zero]
    exact hne
  have heq : ∀ v ∈ Finset.univ.filter (fun v => C v = c),
      (Finset.univ.filter (fun w => C w = C v)).card =
      (Finset.univ.filter (fun w => C w = c)).card := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv]
  rw [Finset.sum_congr rfl (fun v hv => by rw [heq v hv])]
  simp only [Finset.sum_const]
  rw [nsmul_eq_mul, mul_div_cancel₀]
  exact Nat.cast_ne_zero.mpr hcard

/-- For a surjective coloring with n colors, the total weight equals n. -/
private lemma coloringWeight_total_surjective {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (n : ℕ) (_hn : 0 < n)
    (C : G.Coloring (Fin n)) (hsurj : Function.Surjective C) :
    Finset.univ.sum (coloringWeight C) = n := by
  have hpartition : Finset.univ = Finset.univ.biUnion (fun c : Fin n =>
      Finset.univ.filter (fun v => C v = c)) := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, exists_eq']
  rw [hpartition, Finset.sum_biUnion]
  · have heq : ∀ c : Fin n, (Finset.univ.filter (fun v => C v = c)).sum (coloringWeight C) = 1 := by
      intro c
      apply coloringWeight_sum_colorClass
      obtain ⟨v, hv⟩ := hsurj c
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
    simp only [heq, Finset.sum_const, Finset.card_fin]
    simp only [nsmul_eq_mul, mul_one]
  · intro c₁ _ c₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro v _ hv1 hv2
    exact hne (hv1.symm.trans hv2)

set_option linter.unusedFintypeInType false in
/-- Existence of a maximum-cardinality independent set in a nonempty Finset. -/
private lemma exists_maxIndepSet {V : Type*} [Fintype V]
    (G : SimpleGraph V) (remaining : Finset V) (hne : remaining.Nonempty) :
    ∃ M : Finset V, M ⊆ remaining ∧ IsAntichain G.Adj (M : Set V) ∧ M.Nonempty ∧
      ∀ T : Finset V, T ⊆ remaining → IsAntichain G.Adj (T : Set V) → T.card ≤ M.card := by
  classical
  -- Define: S is independent iff no two distinct elements are adjacent
  let isIndep : Finset V → Prop := fun S => ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬G.Adj a b
  -- Use Finset.exists_max_image on the set of independent subsets
  let indepSubsets := remaining.powerset.filter (fun S => isIndep S)
  -- indepSubsets is nonempty (contains singletons)
  obtain ⟨v, hv⟩ := hne
  have hsing_indep : isIndep {v} := by
    intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    exact (hab (ha.trans hb.symm)).elim
  have hsing_mem : {v} ∈ indepSubsets := by
    simp only [indepSubsets, Finset.mem_filter, Finset.mem_powerset,
      Finset.singleton_subset_iff, hv, hsing_indep, and_self]
  have hne_indep : indepSubsets.Nonempty := ⟨{v}, hsing_mem⟩
  -- Pick maximum element
  obtain ⟨M, hM_mem, hM_max⟩ := Finset.exists_max_image indepSubsets Finset.card hne_indep
  simp only [indepSubsets, Finset.mem_filter, Finset.mem_powerset] at hM_mem
  -- Convert isIndep to IsAntichain
  have hM_antichain : IsAntichain G.Adj (M : Set V) := by
    intro a ha b hb hab
    exact hM_mem.2 a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
  refine ⟨M, hM_mem.1, hM_antichain, ?_, ?_⟩
  · -- M is nonempty (has card ≥ 1 since singleton is in indepSubsets)
    have hle := hM_max {v} hsing_mem
    simp only [Finset.card_singleton] at hle
    have hcard_pos : 0 < M.card := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hle)
    exact Finset.card_pos.mp hcard_pos
  · -- M has maximum cardinality
    intro T hT_sub hT_antichain
    have hT_indep : isIndep T := by
      intro a ha b hb hab
      exact hT_antichain (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
    have hT_mem : T ∈ indepSubsets := by
      simp only [indepSubsets, Finset.mem_filter, Finset.mem_powerset, hT_sub, hT_indep, and_self]
    exact hM_max T hT_mem

/-- Pick a maximum independent set using Classical.choose -/
private noncomputable def maxIndepSetIn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (remaining : Finset V) : Finset V :=
  if hne : remaining.Nonempty then
    Classical.choose (exists_maxIndepSet G remaining hne)
  else ∅

/-- Properties of maxIndepSetIn when remaining is nonempty -/
private lemma maxIndepSetIn_spec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (remaining : Finset V) (hne : remaining.Nonempty) :
    (maxIndepSetIn G remaining) ⊆ remaining ∧
    IsAntichain G.Adj ((maxIndepSetIn G remaining) : Set V) ∧
    (maxIndepSetIn G remaining).Nonempty ∧
    ∀ T : Finset V, T ⊆ remaining → IsAntichain G.Adj (T : Set V) →
      T.card ≤ (maxIndepSetIn G remaining).card := by
  unfold maxIndepSetIn
  simp only [hne, ↓reduceDIte]
  exact Classical.choose_spec (exists_maxIndepSet G remaining hne)

/-- Build greedy color classes via well-founded recursion on cardinality -/
private noncomputable def greedyColorClassesAux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : (remaining : Finset V) → List (Finset V)
  | remaining =>
    if hne : remaining.Nonempty then
      let M := maxIndepSetIn G remaining
      have hM_sub : M ⊆ remaining := (maxIndepSetIn_spec G remaining hne).1
      have hM_ne : M.Nonempty := (maxIndepSetIn_spec G remaining hne).2.2.1
      have _ : (remaining \ M).card < remaining.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hM_sub hM_ne)
      M :: greedyColorClassesAux G (remaining \ M)
    else []
termination_by remaining => remaining.card

/-- The greedy color classes for a graph -/
private noncomputable def greedyColorClasses {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : List (Finset V) :=
  greedyColorClassesAux G Finset.univ

/-- Greedy color classes are nonempty for nonempty vertex set -/
private lemma greedyColorClasses_ne_nil {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] : greedyColorClasses G ≠ [] := by
  unfold greedyColorClasses greedyColorClassesAux
  simp only [Finset.univ_nonempty, ↓reduceDIte, ne_eq, List.cons_ne_nil, not_false_eq_true]

set_option linter.style.induction false in
/-- Each greedy color class is an independent set (auxiliary lemma) -/
private lemma greedyColorClassesAux_indep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (remaining : Finset V) (M : Finset V)
    (hM : M ∈ greedyColorClassesAux G remaining) :
    IsAntichain G.Adj (M : Set V) := by
  induction' h : remaining.card using Nat.strong_induction_on with n ih generalizing remaining M
  unfold greedyColorClassesAux at hM
  by_cases hne : remaining.Nonempty
  · simp only [hne, ↓reduceDIte, List.mem_cons] at hM
    cases hM with
    | inl heq =>
      rw [heq]
      exact (maxIndepSetIn_spec G remaining hne).2.1
    | inr htail =>
      have hM_sub : maxIndepSetIn G remaining ⊆ remaining :=
        (maxIndepSetIn_spec G remaining hne).1
      have hM_ne : (maxIndepSetIn G remaining).Nonempty :=
        (maxIndepSetIn_spec G remaining hne).2.2.1
      have h_lt : (remaining \ maxIndepSetIn G remaining).card < remaining.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hM_sub hM_ne)
      exact ih (remaining \ maxIndepSetIn G remaining).card (h ▸ h_lt)
        (remaining \ maxIndepSetIn G remaining) M htail rfl
  · simp only [hne, ↓reduceDIte, List.not_mem_nil] at hM

/-- Each greedy color class is an independent set -/
private lemma greedyColorClasses_indep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset V) (hM : M ∈ greedyColorClasses G) :
    IsAntichain G.Adj (M : Set V) := by
  unfold greedyColorClasses at hM
  exact greedyColorClassesAux_indep G Finset.univ M hM

set_option linter.style.induction false in
/-- Greedy color classes cover all of remaining (aux) -/
private lemma greedyColorClassesAux_cover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (remaining : Finset V) :
    ∀ v ∈ remaining, ∃ M ∈ greedyColorClassesAux G remaining, v ∈ M := by
  induction' h : remaining.card using Nat.strong_induction_on with n ih generalizing remaining
  unfold greedyColorClassesAux
  by_cases hne : remaining.Nonempty
  · simp only [hne, ↓reduceDIte]
    intro v hv
    by_cases hv_in_M : v ∈ maxIndepSetIn G remaining
    · exact ⟨maxIndepSetIn G remaining, List.mem_cons.mpr (Or.inl rfl), hv_in_M⟩
    · have hv_remain : v ∈ remaining \ maxIndepSetIn G remaining := by
        simp only [Finset.mem_sdiff, hv, hv_in_M, not_false_eq_true, and_self]
      have hM_sub : maxIndepSetIn G remaining ⊆ remaining :=
        (maxIndepSetIn_spec G remaining hne).1
      have hM_ne : (maxIndepSetIn G remaining).Nonempty :=
        (maxIndepSetIn_spec G remaining hne).2.2.1
      have h_lt : (remaining \ maxIndepSetIn G remaining).card < remaining.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hM_sub hM_ne)
      obtain ⟨M', hM'_mem, hv_M'⟩ := ih (remaining \ maxIndepSetIn G remaining).card
        (h ▸ h_lt) (remaining \ maxIndepSetIn G remaining) rfl v hv_remain
      exact ⟨M', List.mem_cons_of_mem _ hM'_mem, hv_M'⟩
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    intro v hv
    rw [hne] at hv
    exact (Finset.notMem_empty v hv).elim

/-- Greedy color classes cover all vertices -/
private lemma greedyColorClasses_cover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ∃ M ∈ greedyColorClasses G, v ∈ M := by
  unfold greedyColorClasses
  exact greedyColorClassesAux_cover G Finset.univ v (Finset.mem_univ v)

set_option linter.style.induction false in
/-- Every greedy color class is a subset of the remaining set -/
private lemma greedyColorClassesAux_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (remaining : Finset V) (M : Finset V)
    (hM : M ∈ greedyColorClassesAux G remaining) :
    M ⊆ remaining := by
  induction' h : remaining.card using Nat.strong_induction_on with n ih generalizing remaining M
  unfold greedyColorClassesAux at hM
  by_cases hne : remaining.Nonempty
  · simp only [hne, ↓reduceDIte] at hM
    have hM_sub : maxIndepSetIn G remaining ⊆ remaining :=
      (maxIndepSetIn_spec G remaining hne).1
    have hM_ne : (maxIndepSetIn G remaining).Nonempty :=
      (maxIndepSetIn_spec G remaining hne).2.2.1
    have h_lt : (remaining \ maxIndepSetIn G remaining).card < remaining.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hM_sub hM_ne)
    rw [List.mem_cons] at hM
    rcases hM with hhead | htail
    · rw [hhead]
      exact hM_sub
    · have hsub_tail := ih (remaining \ maxIndepSetIn G remaining).card (h ▸ h_lt)
        (remaining \ maxIndepSetIn G remaining) M htail rfl
      exact fun v hv => (Finset.mem_sdiff.mp (hsub_tail hv)).1
  · simp only [hne, ↓reduceDIte, List.not_mem_nil] at hM

set_option linter.style.induction false in
/-- Greedy color classes are pairwise disjoint (aux) -/
private lemma greedyColorClassesAux_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (remaining : Finset V) :
    (greedyColorClassesAux G remaining).Pairwise Disjoint := by
  induction' h : remaining.card using Nat.strong_induction_on with n ih generalizing remaining
  unfold greedyColorClassesAux
  by_cases hne : remaining.Nonempty
  · simp only [hne, ↓reduceDIte]
    have hM_sub : maxIndepSetIn G remaining ⊆ remaining :=
      (maxIndepSetIn_spec G remaining hne).1
    have hM_ne : (maxIndepSetIn G remaining).Nonempty :=
      (maxIndepSetIn_spec G remaining hne).2.2.1
    have h_lt : (remaining \ maxIndepSetIn G remaining).card < remaining.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hM_sub hM_ne)
    have ih_tail := ih (remaining \ maxIndepSetIn G remaining).card (h ▸ h_lt)
      (remaining \ maxIndepSetIn G remaining) rfl
    rw [List.pairwise_cons]
    constructor
    · intro M' hM'
      rw [Finset.disjoint_left]
      intro v hv_M hv_M'
      -- M' is in the tail, so M' ⊆ remaining \ maxIndepSetIn
      have hM'_sub : M' ⊆ remaining \ maxIndepSetIn G remaining :=
        greedyColorClassesAux_subset G (remaining \ maxIndepSetIn G remaining) M' hM'
      have hv_sdiff : v ∈ remaining \ maxIndepSetIn G remaining := hM'_sub hv_M'
      simp only [Finset.mem_sdiff] at hv_sdiff
      exact hv_sdiff.2 hv_M
    · exact ih_tail
  · simp only [hne, ↓reduceDIte, List.Pairwise.nil]

/-- Greedy color classes are pairwise disjoint -/
private lemma greedyColorClasses_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (greedyColorClasses G).Pairwise Disjoint := by
  unfold greedyColorClasses
  exact greedyColorClassesAux_disjoint G Finset.univ

set_option linter.style.induction false in
/-- Every greedy color class is nonempty (from maxIndepSetIn which is always nonempty) -/
private lemma greedyColorClassesAux_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (remaining : Finset V) (M : Finset V)
    (hM : M ∈ greedyColorClassesAux G remaining) :
    M.Nonempty := by
  induction' h : remaining.card using Nat.strong_induction_on with n ih generalizing remaining M
  unfold greedyColorClassesAux at hM
  by_cases hne : remaining.Nonempty
  · simp only [hne, ↓reduceDIte] at hM
    have hM_ne : (maxIndepSetIn G remaining).Nonempty :=
      (maxIndepSetIn_spec G remaining hne).2.2.1
    have h_lt : (remaining \ maxIndepSetIn G remaining).card < remaining.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset (maxIndepSetIn_spec G remaining hne).1 hM_ne)
    rw [List.mem_cons] at hM
    rcases hM with hhead | htail
    · rw [hhead]; exact hM_ne
    · exact ih (remaining \ maxIndepSetIn G remaining).card (h ▸ h_lt)
        (remaining \ maxIndepSetIn G remaining) M htail rfl
  · simp only [hne, ↓reduceDIte, List.not_mem_nil] at hM

/-- Every greedy color class is nonempty -/
private lemma greedyColorClasses_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) (hi : i < (greedyColorClasses G).length) :
    ((greedyColorClasses G)[i]'hi).Nonempty := by
  unfold greedyColorClasses
  apply greedyColorClassesAux_nonempty G Finset.univ
  exact List.getElem_mem hi

/-- Find the index of the color class containing vertex v -/
private noncomputable def greedyColorIndex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  let colorClasses := greedyColorClasses G
  colorClasses.findIdx (fun M => v ∈ M)

private lemma greedyColorIndex_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    greedyColorIndex G v < (greedyColorClasses G).length := by
  unfold greedyColorIndex
  have hcover := greedyColorClasses_cover G v
  obtain ⟨M, hM_mem, hv_M⟩ := hcover
  apply List.findIdx_lt_length_of_exists
  exact ⟨M, hM_mem, decide_eq_true hv_M⟩

private lemma greedyColorIndex_mem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∈ (greedyColorClasses G)[greedyColorIndex G v]'(greedyColorIndex_lt G v) := by
  have hlt := greedyColorIndex_lt G v
  unfold greedyColorIndex at hlt ⊢
  have h := @List.findIdx_getElem _ (fun M => v ∈ M) (greedyColorClasses G) hlt
  simp only [decide_eq_true_eq] at h
  exact h

/-- Vertices with color index ≥ i are exactly those in later color classes.
    Key relationship between greedyColorIndex and the greedy algorithm structure. -/
private lemma greedyColorIndex_ge_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (i : ℕ)
    (_hi : i < (greedyColorClasses G).length) :
    i ≤ greedyColorIndex G v ↔
    ∃ j, i ≤ j ∧ ∃ (hj : j < (greedyColorClasses G).length),
      v ∈ (greedyColorClasses G)[j]'hj := by
  constructor
  · intro hge
    exact ⟨greedyColorIndex G v, hge, greedyColorIndex_lt G v, greedyColorIndex_mem G v⟩
  · intro ⟨j, hij, hj_lt, hv_j⟩
    -- v is in colorClass[j], so greedyColorIndex G v = j (by uniqueness from disjointness)
    have hdisjoint := greedyColorClasses_disjoint G
    have hv_idx := greedyColorIndex_mem G v
    have hidx_lt := greedyColorIndex_lt G v
    -- v is in both colorClass[j] and colorClass[greedyColorIndex G v]
    -- By disjointness, j = greedyColorIndex G v, so i ≤ j = greedyColorIndex G v
    by_contra hne
    push_neg at hne
    -- hne : greedyColorIndex G v < i, but we know i ≤ j
    -- We need to show j = greedyColorIndex G v, which would contradict hne with hij
    have hj_eq : j = greedyColorIndex G v := by
      by_contra hneq
      rcases Nat.lt_or_gt_of_ne hneq with hlt | hgt
      · -- j < greedyColorIndex G v
        rw [List.pairwise_iff_getElem] at hdisjoint
        have hdisj := hdisjoint j (greedyColorIndex G v) hj_lt hidx_lt hlt
        rw [Finset.disjoint_left] at hdisj
        exact hdisj hv_j hv_idx
      · -- greedyColorIndex G v < j
        rw [List.pairwise_iff_getElem] at hdisjoint
        have hdisj := hdisjoint (greedyColorIndex G v) j hidx_lt hj_lt hgt
        rw [Finset.disjoint_left] at hdisj
        exact hdisj hv_idx hv_j
    omega

/-- Membership in a foldr union of Finsets -/
private lemma mem_foldr_union {V : Type*} [DecidableEq V]
    (L : List (Finset V)) (v : V) :
    v ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ L, v ∈ S := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (hv | ⟨S, hS, hvS⟩)
      · exact ⟨hd, Or.inl rfl, hv⟩
      · exact ⟨S, Or.inr hS, hvS⟩
    · rintro ⟨S, (rfl | hS), hvS⟩
      · exact Or.inl hvS
      · exact Or.inr ⟨S, hS, hvS⟩

/-- The remaining set at step i is the union of colorClasses[i..] -/
private noncomputable def remainingAtStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) : Finset V :=
  ((greedyColorClasses G).drop i).foldr (· ∪ ·) ∅

set_option linter.style.induction false in
/-- For greedyColorClassesAux G S, the remaining set after the first i elements
    equals the foldr union of elements from position i onward -/
private lemma greedyColorClassesAux_remaining {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ((greedyColorClassesAux G S).drop 0).foldr (· ∪ ·) ∅ = S := by
  induction' h : S.card using Nat.strong_induction_on with n ih generalizing S
  unfold greedyColorClassesAux
  by_cases hne : S.Nonempty
  · simp only [hne, ↓reduceDIte, List.drop_zero, List.foldr_cons]
    have hM_sub : maxIndepSetIn G S ⊆ S := (maxIndepSetIn_spec G S hne).1
    have hM_ne : (maxIndepSetIn G S).Nonempty := (maxIndepSetIn_spec G S hne).2.2.1
    have h_lt : (S \ maxIndepSetIn G S).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hM_sub hM_ne)
    have ih' := ih (S \ maxIndepSetIn G S).card (h ▸ h_lt) (S \ maxIndepSetIn G S) rfl
    rw [List.drop_zero] at ih'
    rw [ih']
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hv | ⟨hv1, hv2⟩)
      · exact hM_sub hv
      · exact hv1
    · intro hv
      by_cases hv_M : v ∈ maxIndepSetIn G S
      · exact Or.inl hv_M
      · exact Or.inr ⟨hv, hv_M⟩
  · simp only [hne, ↓reduceDIte, List.drop_zero, List.foldr_nil]
    exact (Finset.not_nonempty_iff_eq_empty.mp hne).symm

/-- The union of all greedy color classes equals univ -/
private lemma greedyColorClasses_union_eq_univ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (greedyColorClasses G).foldr (· ∪ ·) ∅ = Finset.univ := by
  unfold greedyColorClasses
  have := greedyColorClassesAux_remaining G Finset.univ
  simp only [List.drop_zero] at this
  exact this

set_option linter.style.induction false in
/-- The i-th element of greedyColorClassesAux is maxIndepSetIn of the remaining elements' union -/
private lemma greedyColorClassesAux_getElem_eq_maxIndep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (i : ℕ)
    (hi : i < (greedyColorClassesAux G S).length) :
    (greedyColorClassesAux G S)[i] =
      maxIndepSetIn G (((greedyColorClassesAux G S).drop i).foldr (· ∪ ·) ∅) := by
  induction' h : S.card using Nat.strong_induction_on with n ih generalizing S i
  unfold greedyColorClassesAux at hi ⊢
  by_cases hne : S.Nonempty
  · simp only [hne, ↓reduceDIte] at hi ⊢
    have hM_sub : maxIndepSetIn G S ⊆ S := (maxIndepSetIn_spec G S hne).1
    have hM_ne : (maxIndepSetIn G S).Nonempty := (maxIndepSetIn_spec G S hne).2.2.1
    have h_lt : (S \ maxIndepSetIn G S).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hM_sub hM_ne)
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.drop_zero, List.foldr_cons]
      have ih' := greedyColorClassesAux_remaining G (S \ maxIndepSetIn G S)
      simp only [List.drop_zero] at ih'
      rw [ih']
      -- Need to show maxIndepSetIn G S = maxIndepSetIn G (maxIndepSetIn G S ∪ (S \ M))
      -- But maxIndepSetIn G S ∪ (S \ M) = S, so this is trivial
      congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hv
        by_cases hv_M : v ∈ maxIndepSetIn G S
        · exact Or.inl hv_M
        · exact Or.inr ⟨hv, hv_M⟩
      · rintro (hv | ⟨hv1, hv2⟩)
        · exact hM_sub hv
        · exact hv1
    | succ j =>
      simp only [List.getElem_cons_succ, List.drop_succ_cons]
      have hj : j < (greedyColorClassesAux G (S \ maxIndepSetIn G S)).length := by
        simp only [List.length_cons] at hi
        omega
      exact ih (S \ maxIndepSetIn G S).card (h ▸ h_lt) (S \ maxIndepSetIn G S) j hj rfl
  · simp only [hne, ↓reduceDIte, List.length_nil] at hi
    omega

/-- greedyColorClasses[i] is the max independent set in remainingAtStep G i -/
private lemma greedyColorClasses_getElem_eq_maxIndep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) (hi : i < (greedyColorClasses G).length) :
    (greedyColorClasses G)[i] = maxIndepSetIn G (remainingAtStep G i) := by
  unfold greedyColorClasses remainingAtStep
  exact greedyColorClassesAux_getElem_eq_maxIndep G Finset.univ i hi

/-- Membership in a dropped list -/
private lemma mem_drop_iff {α : Type*} (L : List α) (i : ℕ) (x : α) :
    x ∈ L.drop i ↔ ∃ k : ℕ, L[i + k]? = some x := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    rw [List.getElem?_drop] at hj
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    use j
    rw [List.getElem?_drop]
    exact hj

/-- A vertex is in remainingAtStep i iff its colorIndex is ≥ i -/
private lemma mem_remainingAtStep_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (i : ℕ)
    (_hi : i < (greedyColorClasses G).length) :
    v ∈ remainingAtStep G i ↔ i ≤ greedyColorIndex G v := by
  unfold remainingAtStep
  rw [mem_foldr_union]
  constructor
  · intro ⟨M, hM_mem, hv_M⟩
    rw [mem_drop_iff] at hM_mem
    obtain ⟨k, hMk⟩ := hM_mem
    -- M = colorClasses[i + k], v ∈ M, so colorIndex(v) = i + k ≥ i
    have hik_lt : i + k < (greedyColorClasses G).length := by
      by_contra hc
      simp only [not_lt] at hc
      simp only [List.getElem?_eq_none hc, reduceCtorEq] at hMk
    -- v is in colorClasses[i+k], so colorIndex(v) = i+k (by disjointness)
    have hv_idx := greedyColorIndex_mem G v
    have hdisjoint := greedyColorClasses_disjoint G
    have hidx_lt := greedyColorIndex_lt G v
    -- By disjointness, v can only be in one color class
    by_contra hlt
    push_neg at hlt
    have hik_eq : i + k = greedyColorIndex G v := by
      by_contra hneq
      rw [List.pairwise_iff_getElem] at hdisjoint
      rcases Nat.lt_or_gt_of_ne hneq with h1 | h2
      · have hdisj := hdisjoint (i + k) (greedyColorIndex G v) hik_lt hidx_lt h1
        rw [Finset.disjoint_left] at hdisj
        have hv_ik : v ∈ (greedyColorClasses G)[i + k] := by
          simp only [List.getElem?_eq_getElem hik_lt, Option.some.injEq] at hMk
          rw [hMk]; exact hv_M
        exact hdisj hv_ik hv_idx
      · have hdisj := hdisjoint (greedyColorIndex G v) (i + k) hidx_lt hik_lt h2
        rw [Finset.disjoint_left] at hdisj
        have hv_ik : v ∈ (greedyColorClasses G)[i + k] := by
          simp only [List.getElem?_eq_getElem hik_lt, Option.some.injEq] at hMk
          rw [hMk]; exact hv_M
        exact hdisj hv_idx hv_ik
    omega
  · intro hge
    have hidx_lt := greedyColorIndex_lt G v
    use (greedyColorClasses G)[greedyColorIndex G v]'hidx_lt
    constructor
    · rw [mem_drop_iff]
      use greedyColorIndex G v - i
      have hsum_eq : i + (greedyColorIndex G v - i) = greedyColorIndex G v :=
        Nat.add_sub_cancel' hge
      rw [hsum_eq]
      rw [List.getElem?_eq_getElem hidx_lt]
    · exact greedyColorIndex_mem G v

/-- At step i, colorClasses[i] has maximum cardinality among all independent sets
    contained in the union of colorClasses[i..]. -/
private lemma greedyColorClass_max_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) (hi : i < (greedyColorClasses G).length)
    (T : Finset V) (hT_indep : IsAntichain G.Adj (T : Set V))
    (hT_late : ∀ w ∈ T, i ≤ greedyColorIndex G w) :
    T.card ≤ ((greedyColorClasses G)[i]'hi).card := by
  -- T ⊆ remainingAtStep G i (since all vertices in T have colorIndex ≥ i)
  have hT_sub : T ⊆ remainingAtStep G i := by
    intro w hw
    rw [mem_remainingAtStep_iff G w i hi]
    exact hT_late w hw
  -- colorClasses[i] = maxIndepSetIn G (remainingAtStep G i)
  have h_eq := greedyColorClasses_getElem_eq_maxIndep G i hi
  -- remainingAtStep G i is nonempty (contains at least colorClasses[i])
  have h_ne : (remainingAtStep G i).Nonempty := by
    unfold remainingAtStep
    rw [Finset.Nonempty]
    have hM_ne := greedyColorClasses_nonempty G i hi
    obtain ⟨v, hv⟩ := hM_ne
    use v
    rw [mem_foldr_union]
    refine ⟨(greedyColorClasses G)[i], ?_, hv⟩
    rw [mem_drop_iff]
    use 0
    simp only [add_zero, List.getElem?_eq_getElem hi]
  -- By maxIndepSetIn_spec, T.card ≤ colorClasses[i].card
  rw [h_eq]
  exact (maxIndepSetIn_spec G (remainingAtStep G i) h_ne).2.2.2 T hT_sub hT_indep

/-- Key bound: for any vertex v in an independent set S, the color class containing v
    has size at least equal to the number of vertices in S with color index ≥ colorIndex(v). -/
private lemma colorClass_card_ge_tail {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hS : IsAntichain G.Adj (S : Set V))
    (v : V) (_hv : v ∈ S) :
    (S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w)).card ≤
    ((greedyColorClasses G)[greedyColorIndex G v]'(greedyColorIndex_lt G v)).card := by
  -- Apply greedyColorClass_max_card to T = S.filter(colorIndex(v) ≤ colorIndex(_))
  set T := S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w) with hT_def
  have hT_indep : IsAntichain G.Adj (T : Set V) := by
    intro a ha b hb hab
    rw [hT_def] at ha hb
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    exact hS ha.1 hb.1 hab
  have hT_late : ∀ w ∈ T, greedyColorIndex G v ≤ greedyColorIndex G w := by
    intro w hw
    rw [hT_def] at hw
    exact (Finset.mem_filter.mp hw).2
  exact greedyColorClass_max_card G (greedyColorIndex G v) (greedyColorIndex_lt G v)
    T hT_indep hT_late

/-- The coloring weight of a vertex is at most 1/(tail size) -/
private lemma coloringWeight_le_inv_tail {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hS : IsAntichain G.Adj (S : Set V))
    (C : G.Coloring (Fin (greedyColorClasses G).length)) (_hsurj : Function.Surjective C)
    (v : V) (hv : v ∈ S)
    (hcolor_eq : ∀ w, C w = ⟨greedyColorIndex G w, greedyColorIndex_lt G w⟩) :
    coloringWeight C v ≤
      1 / (S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w)).card := by
  -- coloringWeight C v = 1 / |{w : C w = C v}|
  unfold coloringWeight
  have hidx_lt := greedyColorIndex_lt G v
  -- {w : C w = C v} = {w : greedyColorIndex w = greedyColorIndex v}
  have h_colorClass_eq : (Finset.univ.filter (fun w => C w = C v)).card =
      ((greedyColorClasses G)[greedyColorIndex G v]'hidx_lt).card := by
    have heq : Finset.univ.filter (fun w => C w = C v) =
        (greedyColorClasses G)[greedyColorIndex G v]'hidx_lt := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcolor_eq v, hcolor_eq w]
      simp only [Fin.mk.injEq]
      constructor
      · intro heq'
        have := greedyColorIndex_mem G w
        simp only [heq'] at this
        exact this
      · intro hw
        -- w ∈ colorClasses[colorIndex v], by disjointness colorIndex w = colorIndex v
        have hdisjoint := greedyColorClasses_disjoint G
        have hw_idx := greedyColorIndex_lt G w
        by_contra hne
        rw [List.pairwise_iff_getElem] at hdisjoint
        rcases Nat.lt_or_gt_of_ne hne with h1 | h2
        · have hdisj := hdisjoint (greedyColorIndex G w) (greedyColorIndex G v) hw_idx hidx_lt h1
          rw [Finset.disjoint_left] at hdisj
          exact hdisj (greedyColorIndex_mem G w) hw
        · have hdisj := hdisjoint (greedyColorIndex G v) (greedyColorIndex G w) hidx_lt hw_idx h2
          rw [Finset.disjoint_left] at hdisj
          exact hdisj hw (greedyColorIndex_mem G w)
    exact congrArg Finset.card heq
  rw [h_colorClass_eq]
  -- Now need: 1 / |colorClasses[colorIndex v]| ≤ 1 / |tail|
  -- i.e., |tail| ≤ |colorClasses[colorIndex v]|
  have h_tail_le := colorClass_card_ge_tail G S hS v hv
  -- Convert to Real division inequality
  have h_colorClass_ne : (((greedyColorClasses G)[greedyColorIndex G v]'hidx_lt).card : ℝ) ≠ 0 := by
    have hne := greedyColorClasses_nonempty G (greedyColorIndex G v) hidx_lt
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_ne_zero]
    exact hne
  have h_tail_ne : (0 : ℝ) < (S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w)).card
      ∨ (S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w)).card = 0 := by
    rcases eq_or_ne (S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w)).card 0 with
      h | h
    · right; exact h
    · left; exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
  rcases h_tail_ne with h_pos | h_zero
  · apply one_div_le_one_div_of_le h_pos
    exact Nat.cast_le.mpr h_tail_le
  · -- tail is empty, but v is in the tail (since greedyColorIndex v ≤ greedyColorIndex v)
    exfalso
    have hv_in_tail : v ∈ S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w) := by
      simp only [Finset.mem_filter, le_refl, and_true]
      exact hv
    rw [Finset.card_eq_zero] at h_zero
    rw [h_zero] at hv_in_tail
    exact Finset.notMem_empty v hv_in_tail

/-- The sum of 1/(tail sizes) over a finite set S is at most H_k, where k = |S|.
    Here, the tail of v is {w ∈ S : f(w) ≥ f(v)} for a given rank function f.

    Key insight: Sort S by f to get v_1, ..., v_k. For v_i, tail size ≥ k - i + 1,
    so 1/(tail size) ≤ 1/(k - i + 1). Summing gives ≤ H_k. -/
private lemma tail_sum_le_harmonic {V : Type*}
    (S : Finset V) (f : V → ℕ) :
    S.sum (fun v => (1 : ℝ) / (S.filter (fun w => f v ≤ f w)).card) ≤ harmonic S.card := by
  classical
  -- If S is empty, the result is trivial
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    norm_num
  -- Use induction on |S|
  induction S using Finset.strongInduction with
  | _ S ih =>
    -- Find the element with minimum f value
    have hmin := Finset.exists_min_image S f hne
    obtain ⟨v₀, hv₀_mem, hv₀_min⟩ := hmin
    -- For v₀, the tail is all of S
    have htail_v₀ : S.filter (fun w => f v₀ ≤ f w) = S := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · intro ⟨hw, _⟩; exact hw
      · intro hw; exact ⟨hw, hv₀_min w hw⟩
    -- Split the sum: S = {v₀} ∪ (S \ {v₀})
    rw [← Finset.insert_erase hv₀_mem, Finset.sum_insert (Finset.notMem_erase v₀ S)]
    -- Term for v₀: 1/|S|
    have hv₀_term : (1 : ℝ) / (S.filter (fun w => f v₀ ≤ f w)).card = 1 / S.card := by
      rw [htail_v₀]
    simp only [Finset.insert_erase hv₀_mem]
    rw [hv₀_term]
    -- For other elements, bound by induction on S \ {v₀}
    by_cases hS_single : S.card = 1
    · -- S = {v₀}, so the sum is just 1/1 = 1 = H_1
      have hempty : S.erase v₀ = ∅ := by
        have hcard : (S.erase v₀).card = 0 := by
          rw [Finset.card_erase_of_mem hv₀_mem, hS_single]
        exact Finset.card_eq_zero.mp hcard
      rw [hempty, Finset.sum_empty, add_zero, hS_single]
      -- 1/1 = 1 ≤ H_1 = 1
      simp only [Nat.cast_one, one_div, inv_one]
      have h1 : harmonic 1 = 1 := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, harmonic_succ, harmonic_zero, zero_add]
        norm_num
      simp only [h1, Rat.cast_one, le_refl]
    · -- S.card ≥ 2
      have hS_ge2 : 2 ≤ S.card := by
        have hpos : 0 < S.card := Finset.card_pos.mpr hne
        omega
      have hS'_ssubset : S.erase v₀ ⊂ S := Finset.erase_ssubset hv₀_mem
      have hS'_ne : (S.erase v₀).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        have hcard : (S.erase v₀).card = 0 := Finset.card_eq_zero.mpr h
        rw [Finset.card_erase_of_mem hv₀_mem] at hcard
        omega
      -- For w ∈ S \ {v₀}, the tail {w' ∈ S : f(w) ≤ f(w')} ⊇ tail in S \ {v₀}
      -- So 1/|tail_S| ≤ 1/|tail_{S\v₀}|
      have htail_superset : ∀ w ∈ S.erase v₀,
          (S.erase v₀).filter (fun w' => f w ≤ f w') ⊆ S.filter (fun w' => f w ≤ f w') := by
        intro w _ w' hw'
        simp only [Finset.mem_filter, Finset.mem_erase] at hw' ⊢
        exact ⟨hw'.1.2, hw'.2⟩
      have hsum_le : (S.erase v₀).sum (fun v =>
          (1 : ℝ) / (S.filter (fun w => f v ≤ f w)).card) ≤
          (S.erase v₀).sum (fun v =>
          (1 : ℝ) / ((S.erase v₀).filter (fun w => f v ≤ f w)).card) := by
        apply Finset.sum_le_sum
        intro w hw
        have hsub := htail_superset w hw
        have hcard_le := Finset.card_le_card hsub
        have hne_tail : ((S.erase v₀).filter (fun w' => f w ≤ f w')).Nonempty := by
          use w
          simp only [Finset.mem_filter, Finset.mem_erase]
          exact ⟨⟨Finset.ne_of_mem_erase hw, Finset.mem_of_mem_erase hw⟩, le_refl _⟩
        have hpos : 0 < ((S.erase v₀).filter (fun w' => f w ≤ f w')).card :=
          Finset.card_pos.mpr hne_tail
        apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hpos)
        exact Nat.cast_le.mpr hcard_le
      -- Now apply induction
      have hih := ih (S.erase v₀) hS'_ssubset hS'_ne
      calc (1 : ℝ) / S.card +
            (S.erase v₀).sum (fun v => (1 : ℝ) / (S.filter (fun w => f v ≤ f w)).card)
          ≤ 1 / S.card + (S.erase v₀).sum
            (fun v => (1 : ℝ) / ((S.erase v₀).filter (fun w => f v ≤ f w)).card) := by
            gcongr
        _ ≤ 1 / S.card + harmonic (S.erase v₀).card := by
            gcongr
        _ = 1 / S.card + harmonic (S.card - 1) := by
            rw [Finset.card_erase_of_mem hv₀_mem]
        _ = harmonic S.card := by
            have hcard_pos : 0 < S.card := Finset.card_pos.mpr hne
            have hscard : S.card = (S.card - 1) + 1 := by omega
            conv_rhs => rw [hscard, harmonic_succ]
            simp only [Nat.sub_add_cancel hcard_pos]
            rw [Rat.cast_add, add_comm]
            congr 1
            simp only [Rat.cast_inv, Rat.cast_natCast, one_div]

private theorem greedy_coloring_harmonic_bound {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] {G : SimpleGraph V} :
    ∃ (n : ℕ) (_hn : 0 < n) (C : G.Coloring (Fin n)) (_hsurj : Function.Surjective C),
      ∀ (S : Finset V), IsAntichain G.Adj S → S.sum (coloringWeight C) ≤ harmonic S.card := by
  classical
  -- Build greedy color classes
  let colorClasses := greedyColorClasses G
  have hne_list : colorClasses ≠ [] := greedyColorClasses_ne_nil G
  let n := colorClasses.length
  have hn : 0 < n := List.length_pos_of_ne_nil hne_list
  -- Each vertex is in exactly one color class
  have hcover := greedyColorClasses_cover G
  have hindep := greedyColorClasses_indep G
  have hdisjoint := greedyColorClasses_disjoint G
  -- Define the coloring function
  let colorFn : V → Fin n := fun v => ⟨greedyColorIndex G v, greedyColorIndex_lt G v⟩
  -- The greedy coloring: prove it's a valid coloring
  have hvalid : ∀ v w : V, G.Adj v w → colorFn v ≠ colorFn w := by
    intro v w hvw heq
    have hv_mem := greedyColorIndex_mem G v
    have hw_mem := greedyColorIndex_mem G w
    have heq' : greedyColorIndex G v = greedyColorIndex G w := by
      simp only [colorFn, Fin.mk.injEq] at heq
      exact heq
    -- v and w are in the same color class (class at index v's color)
    have hM_indep := hindep _ (List.getElem_mem (greedyColorIndex_lt G v))
    -- Use eq_of_heq to transport hw_mem through the index equality
    have hw_mem' : w ∈ (greedyColorClasses G)[greedyColorIndex G v]'(greedyColorIndex_lt G v) := by
      have : (greedyColorClasses G)[greedyColorIndex G w]'(greedyColorIndex_lt G w) =
             (greedyColorClasses G)[greedyColorIndex G v]'(greedyColorIndex_lt G v) := by
        simp only [heq']
      rw [← this]
      exact hw_mem
    exact hM_indep hv_mem hw_mem' (G.ne_of_adj hvw) hvw
  let C : G.Coloring (Fin n) := ⟨colorFn, fun hvw => hvalid _ _ hvw⟩
  -- Prove surjectivity: each color class is nonempty
  have hsurj : Function.Surjective C := by
    intro ⟨i, hi⟩
    -- The i-th color class is nonempty
    have hne_class : (colorClasses[i]'hi).Nonempty := by
      apply greedyColorClasses_nonempty G i hi
    obtain ⟨v, hv⟩ := hne_class
    use v
    simp only [C, Fin.ext_iff]
    change greedyColorIndex G v = i
    rw [greedyColorIndex, List.findIdx_eq hi]
    constructor
    · simp only [decide_eq_true_eq]
      exact hv
    · intro j hji
      simp only [decide_eq_false_iff_not]
      intro hv_j
      rw [List.pairwise_iff_getElem] at hdisjoint
      have hj_lt : j < n := Nat.lt_trans hji hi
      have hdisj := hdisjoint j i hj_lt hi hji
      rw [Finset.disjoint_left] at hdisj
      exact hdisj hv_j hv
  use n, hn, C, hsurj
  -- Now prove the harmonic bound using the helper lemmas above
  intro S hS
  have hcolor_eq : ∀ w, C w = ⟨greedyColorIndex G w, greedyColorIndex_lt G w⟩ := fun w => rfl
  -- Step 1: Each weight is bounded by 1/(tail size)
  have hweight_bound : ∀ v ∈ S, coloringWeight C v ≤
      1 / (S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w)).card := by
    intro v hv
    exact coloringWeight_le_inv_tail G S hS C hsurj v hv hcolor_eq
  -- Step 2: Sum of 1/(tail sizes) ≤ H_k
  -- Key insight: sort S by colorIndex. For the i-th element (from smallest colorIndex),
  -- tail size ≥ k - i + 1, so 1/(tail size) ≤ 1/(k - i + 1)
  -- Therefore: Σ 1/(tail size) ≤ Σ_{i=1}^{k} 1/(k - i + 1) = H_k
  calc S.sum (coloringWeight C)
    ≤ S.sum (fun v => (1 : ℝ) /
        (S.filter (fun w => greedyColorIndex G v ≤ greedyColorIndex G w)).card) := by
        apply Finset.sum_le_sum
        intro v hv
        exact hweight_bound v hv
    _ ≤ harmonic S.card := by
        -- Use the tail-sum bound
        exact tail_sum_le_harmonic S (fun v => greedyColorIndex G v)

/-- For a graph with chromatic number χ, the greedy packing bound gives:
    χ ≤ (1 + ln α) · fractionalCliqueCoverNumber -/
private theorem greedy_packing_gives_bound {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (H : SimpleGraph V) :
    (H.chromaticNumber.toNat : ℝ) ≤ (1 + Real.log H.indepNum) *
      fractionalCliqueCoverNumber Hᶜ := by
  obtain ⟨n, hn, C, hsurj, hbound⟩ := @greedy_coloring_harmonic_bound V _ _ _ H
  have htotal : Finset.univ.sum (coloringWeight C) = n :=
    coloringWeight_total_surjective n hn C hsurj
  have hcolorable : H.Colorable n := ⟨C⟩
  have hchi_le_n : H.chromaticNumber ≤ n := hcolorable.chromaticNumber_le
  have hchi_ne_top : H.chromaticNumber ≠ ⊤ := chromaticNumber_ne_top_of_fintype H
  have hchi_toNat_le : H.chromaticNumber.toNat ≤ n :=
    ENat.toNat_le_of_le_coe hchi_le_n
  have hlog_bound : ∀ (S : Finset V), IsAntichain H.Adj S →
      S.sum (coloringWeight C) ≤ 1 + Real.log H.indepNum := by
    intro S hS_antichain
    have hS_isIndep : H.IsIndepSet S := hS_antichain
    calc S.sum (coloringWeight C)
      ≤ harmonic S.card := hbound S hS_antichain
      _ ≤ 1 + Real.log S.card := by
          by_cases hS_empty : S.card = 0
          · simp only [hS_empty, harmonic_zero, Nat.cast_zero, Real.log_zero, add_zero]
            norm_num
          · exact harmonic_le_one_add_log S.card
      _ ≤ 1 + Real.log H.indepNum := by
          by_cases hS_empty : S.card = 0
          · simp only [hS_empty, Nat.cast_zero, Real.log_zero, add_zero]
            have hlog_nonneg : 0 ≤ Real.log H.indepNum := by
              by_cases hα : H.indepNum = 0
              · simp [hα]
              · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hα)
            linarith
          · gcongr
            exact Nat.cast_le.mpr hS_isIndep.card_le_indepNum
  by_cases hα : H.indepNum = 0
  · exfalso
    have hv : V := Classical.arbitrary V
    have hsing : H.IsIndepSet ({hv} : Finset V) := by
      rw [SimpleGraph.IsIndepSet, Set.Pairwise]
      intro a ha b hb _
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
      exact H.loopless.irrefl hv
    have hone_le : 1 ≤ H.indepNum := by
      have hcard : ({hv} : Finset V).card = 1 := Finset.card_singleton hv
      have hle := hsing.card_le_indepNum
      omega
    omega
  have hα_pos : 0 < H.indepNum := Nat.pos_of_ne_zero hα
  have hlogα_pos : 0 < 1 + Real.log H.indepNum := by
    have h1 : (1 : ℝ) ≤ H.indepNum := by exact_mod_cast hα_pos
    have hlog_nonneg : 0 ≤ Real.log H.indepNum := Real.log_nonneg h1
    linarith
  have hcover_exists : Nonempty (FractionalCliqueCover Hᶜ) := by
    apply FractionalCliqueCover.exists_singleton
  let scaledWeights : V → ℝ := fun v => coloringWeight C v / (1 + Real.log H.indepNum)
  have hfi_nonneg : ∀ v, 0 ≤ scaledWeights v := by
    intro v
    apply div_nonneg
    · unfold coloringWeight
      apply div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      exact Nat.cast_nonneg _
    · linarith
  have hfi_clique : ∀ C' : Finset V, Hᶜ.IsClique C' → C'.sum scaledWeights ≤ 1 := by
    intro S hS_clique
    have hS_antichain : IsAntichain H.Adj S := by
      intro a ha b hb hab hadj
      have hclique := hS_clique ha hb (H.ne_of_adj hadj)
      rw [SimpleGraph.compl_adj] at hclique
      exact hclique.2 hadj
    calc S.sum scaledWeights
      = S.sum (fun v => coloringWeight C v / (1 + Real.log H.indepNum)) := rfl
      _ = (S.sum (coloringWeight C)) / (1 + Real.log H.indepNum) := by
          rw [Finset.sum_div]
      _ ≤ (1 + Real.log H.indepNum) / (1 + Real.log H.indepNum) := by
          apply div_le_div_of_nonneg_right (hlog_bound S hS_antichain)
          linarith
      _ = 1 := div_self (ne_of_gt hlogα_pos)
  let hfi : FractionalIndependentSet Hᶜ :=
    ⟨scaledWeights, hfi_nonneg, hfi_clique⟩
  have hfi_total : hfi.totalWeight = n / (1 + Real.log H.indepNum) := by
    unfold FractionalIndependentSet.totalWeight
    have hweights_eq : hfi.weights = scaledWeights := rfl
    rw [hweights_eq]
    conv_lhs =>
      rw [show scaledWeights =
        (fun v => coloringWeight C v / (1 + Real.log H.indepNum)) from rfl]
    rw [← Finset.sum_div, htotal]
  have hfi_bound : n / (1 + Real.log H.indepNum) ≤
      fractionalIndependenceNumber Hᶜ := by
    rw [← hfi_total]
    unfold fractionalIndependenceNumber
    apply le_ciSup
    use Fintype.card V
    intro _ ⟨fi, hfi_eq⟩
    rw [← hfi_eq]
    exact fi.totalWeight_le_card
  have hduality := lp_duality Hᶜ
  calc (H.chromaticNumber.toNat : ℝ)
    ≤ n := Nat.cast_le.mpr hchi_toNat_le
    _ = (n / (1 + Real.log H.indepNum)) * (1 + Real.log H.indepNum) := by
        field_simp
    _ ≤ (fractionalIndependenceNumber Hᶜ) * (1 + Real.log H.indepNum) := by
        apply mul_le_mul_of_nonneg_right hfi_bound (le_of_lt hlogα_pos)
    _ = (fractionalCliqueCoverNumber Hᶜ) * (1 + Real.log H.indepNum) := by
        rw [← hduality]
    _ = (1 + Real.log H.indepNum) * fractionalCliqueCoverNumber Hᶜ := by
        ring

/-- The logarithmic bound: χ̄(G) ≤ (1 + ln ω(G)) · χ̄_f(G).
    This is Theorem 64.13 from Schrijver (applied to clique covers). -/
theorem logarithmic_bound (G : Graph) (hω : 1 ≤ G.graph.cliqueNum) :
    (graphRank (GraphClass.mk G) : ℝ) ≤
    (1 + Real.log G.graph.cliqueNum) * χ̄_f G := by
  have hrank_eq : graphRank (GraphClass.mk G) = G.graphᶜ.chromaticNumber.toNat :=
    graphRank_eq_chromaticNumber_toNat G
  rw [hrank_eq]
  have hclique_eq : G.graph.cliqueNum = G.graphᶜ.indepNum := cliqueNum_eq_indepNum_compl G.graph
  rw [hclique_eq]
  have hcompl_compl : G.graphᶜᶜ = G.graph := compl_compl G.graph
  have hnonempty : Nonempty G.V := by
    by_contra hempty
    simp only [not_nonempty_iff] at hempty
    have hzero : G.graph.cliqueNum = 0 := by
      rw [SimpleGraph.cliqueNum]
      apply le_antisymm
      · apply csSup_le
        · exact ⟨0, ∅, SimpleGraph.isNClique_empty.mpr rfl⟩
        · intro n ⟨s, hs⟩
          have hempty_s : s = ∅ := Finset.eq_empty_of_isEmpty s
          rw [hempty_s, SimpleGraph.isNClique_empty] at hs
          omega
      · exact Nat.zero_le _
    omega
  classical
  have hbound := @greedy_packing_gives_bound G.V _ _ hnonempty G.graphᶜ
  rw [hcompl_compl] at hbound
  have hchibar_eq : χ̄_f G = fractionalCliqueCoverNumber G.graph := rfl
  rw [hchibar_eq]
  exact hbound

/-! ### Clique Number Multiplicativity for Strong Products -/

set_option linter.unusedFintypeInType false in
/-- Clique number is multiplicative under strong product:
    ω(G ⊠ H) = ω(G) * ω(H).

    A clique in G ⊠ H corresponds exactly to a product of cliques in G and H. -/
theorem cliqueNum_strongProduct {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (ShannonCapacity.strongProduct G H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  classical
  apply le_antisymm
  · -- Upper bound: any clique in G ⊠ H has size ≤ ω(G) * ω(H)
    obtain ⟨s, hs⟩ := (ShannonCapacity.strongProduct G H).exists_isNClique_cliqueNum
    rw [SimpleGraph.isNClique_iff] at hs
    -- Project to coordinates
    let projG : V × W → V := Prod.fst
    let projH : V × W → W := Prod.snd
    have hG_clique : G.IsClique ((s.image projG) : Set V) := by
      intro u hu v hv huv
      rw [Finset.coe_image, Set.mem_image] at hu hv
      obtain ⟨⟨u1, u2⟩, hu1, rfl⟩ := hu
      obtain ⟨⟨v1, v2⟩, hv1, rfl⟩ := hv
      dsimp only [projG] at huv ⊢
      have hne : (⟨u1, u2⟩ : V × W) ≠ ⟨v1, v2⟩ := by
        intro heq
        simp only [Prod.mk.injEq] at heq
        exact huv heq.1
      have hadj := hs.1 hu1 hv1 hne
      simp only [ShannonCapacity.strongProduct] at hadj
      obtain ⟨_, hl, _⟩ := hadj
      -- hl : u1 = v1 ∨ G.Adj u1 v1
      rcases hl with heq | hadj_G
      · exact (huv heq).elim
      · exact hadj_G
    have hH_clique : H.IsClique ((s.image projH) : Set W) := by
      intro u hu v hv huv
      rw [Finset.coe_image, Set.mem_image] at hu hv
      obtain ⟨⟨u1, u2⟩, hu1, rfl⟩ := hu
      obtain ⟨⟨v1, v2⟩, hv1, rfl⟩ := hv
      dsimp only [projH] at huv ⊢
      have hne : (⟨u1, u2⟩ : V × W) ≠ ⟨v1, v2⟩ := by
        intro heq
        simp only [Prod.mk.injEq] at heq
        exact huv heq.2
      have hadj := hs.1 hu1 hv1 hne
      simp only [ShannonCapacity.strongProduct] at hadj
      obtain ⟨_, _, hr⟩ := hadj
      -- hr : u2 = v2 ∨ H.Adj u2 v2
      rcases hr with heq | hadj_H
      · exact (huv heq).elim
      · exact hadj_H
    have hG_bound := hG_clique.card_le_cliqueNum
    have hH_bound := hH_clique.card_le_cliqueNum
    -- s injects into (image projG) ×ˢ (image projH)
    have hcard : s.card ≤ (s.image projG).card * (s.image projH).card := by
      have h : s.card ≤ ((s.image projG) ×ˢ (s.image projH)).card := by
        apply Finset.card_le_card
        intro ⟨u, v⟩ huv
        simp only [Finset.mem_product]
        exact ⟨Finset.mem_image_of_mem projG huv, Finset.mem_image_of_mem projH huv⟩
      rw [Finset.card_product] at h
      exact h
    calc (ShannonCapacity.strongProduct G H).cliqueNum = s.card := hs.2.symm
      _ ≤ (s.image projG).card * (s.image projH).card := hcard
      _ ≤ G.cliqueNum * H.cliqueNum := Nat.mul_le_mul hG_bound hH_bound
  · -- Lower bound: product of max cliques gives a clique
    obtain ⟨sG, hsG⟩ := G.maximumClique_exists
    obtain ⟨sH, hsH⟩ := H.maximumClique_exists
    have hG_card := SimpleGraph.maximumClique_card_eq_cliqueNum sG hsG
    have hH_card := SimpleGraph.maximumClique_card_eq_cliqueNum sH hsH
    let prodSet : Finset (V × W) := sG ×ˢ sH
    have hprod_clique :
        (ShannonCapacity.strongProduct G H).IsClique (prodSet : Set (V × W)) := by
      intro ⟨u1, u2⟩ hu ⟨v1, v2⟩ hv hne
      rw [Finset.coe_product] at hu hv
      simp only [Set.mem_prod, Finset.mem_coe] at hu hv
      simp only [ShannonCapacity.strongProduct, ne_eq]
      -- Need: hne ∧ (u1 = v1 ∨ G.Adj u1 v1) ∧ (u2 = v2 ∨ H.Adj u2 v2)
      refine ⟨hne, ?_, ?_⟩
      · by_cases h : u1 = v1
        · left; exact h
        · right; exact hsG.isClique hu.1 hv.1 h
      · by_cases h : u2 = v2
        · left; exact h
        · right; exact hsH.isClique hu.2 hv.2 h
    calc G.cliqueNum * H.cliqueNum = sG.card * sH.card := by rw [hG_card, hH_card]
      _ = prodSet.card := (Finset.card_product sG sH).symm
      _ ≤ (ShannonCapacity.strongProduct G H).cliqueNum := hprod_clique.card_le_cliqueNum

/-- Clique number of n-fold strong product power equals ω(G)^n. -/
theorem cliqueNum_recStrongPowerGraph (G : Graph) (n : ℕ) :
    (recStrongPowerGraph G n).graph.cliqueNum = G.graph.cliqueNum ^ n := by
  classical
  induction n with
  | zero =>
    simp only [recStrongPowerGraph, pow_zero]
    simp only [EdgelessGraph, edgelessGraph, SimpleGraph.cliqueNum]
    apply le_antisymm
    · have hbdd : BddAbove { n_1 | ∃ s, (⊥ : SimpleGraph (Fin 1)).IsNClique n_1 s } := by
        use 1
        intro k ⟨s, hs⟩
        rw [SimpleGraph.isNClique_iff] at hs
        have hsub : s.card ≤ Fintype.card (Fin 1) := Finset.card_le_card (Finset.subset_univ _)
        simp only [Fintype.card_fin] at hsub
        omega
      apply csSup_le
      · use 0, ∅
        exact SimpleGraph.isNClique_empty.mpr rfl
      intro k ⟨s, hs⟩
      have hsub : s.card ≤ Fintype.card (Fin 1) := Finset.card_le_card (Finset.subset_univ _)
      simp only [Fintype.card_fin] at hsub
      rw [SimpleGraph.isNClique_iff] at hs
      omega
    · -- cliqueNum ≥ 1 because the single vertex forms a clique
      have h1 : (⊥ : SimpleGraph (Fin 1)).IsClique ({0} : Finset (Fin 1)) := by
        intro u hu v hv huv
        -- In a singleton set, u = v, contradicting huv
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
        subst hu hv
        exact (huv rfl).elim
      have : ({0} : Finset (Fin 1)).card ≤ (⊥ : SimpleGraph (Fin 1)).cliqueNum :=
        h1.card_le_cliqueNum
      simp only [Finset.card_singleton] at this
      exact this
  | succ n ih =>
    simp only [recStrongPowerGraph, pow_succ]
    rw [Graph.strongProduct]
    have heq := @cliqueNum_strongProduct G.V (recStrongPowerGraph G n).V _ _
      G.graph (recStrongPowerGraph G n).graph
    simp only [heq, ih]
    ring

/-- χ̄_f(G^n) = χ̄_f(G)^n: multiplicativity of fractional clique cover under strong powers. -/
theorem chibar_recStrongPowerGraph (G : Graph) (n : ℕ) :
    χ̄_f (recStrongPowerGraph G n) = (χ̄_f G) ^ n := by
  induction n with
  | zero =>
    simp only [recStrongPowerGraph, pow_zero]
    -- EdgelessGraph 1 = { V := Fin 1, graph := edgelessGraph 1 } = { V := Fin 1, graph := ⊥ }
    have h : χ̄_f (EdgelessGraph 1) = 1 := by
      simp only [EdgelessGraph, edgelessGraph]
      have h1 := fractionalCliqueCovering_normalized 1
      simp only [Nat.cast_one] at h1
      exact h1
    exact h
  | succ k ih =>
    simp only [recStrongPowerGraph, pow_succ]
    -- recStrongPowerGraph G (k+1) = G ⊠ recStrongPowerGraph G k
    have h : χ̄_f (G ⊠ recStrongPowerGraph G k) = χ̄_f G * χ̄_f (recStrongPowerGraph G k) :=
      fractionalCliqueCovering_mul_strongProduct G (recStrongPowerGraph G k)
    rw [h, ih]
    ring

end AsymptoticSpectrumGraphs
