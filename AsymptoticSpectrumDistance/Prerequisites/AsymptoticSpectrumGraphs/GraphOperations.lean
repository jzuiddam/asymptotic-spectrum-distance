/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.Linarith
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.StrongProduct

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

/-!
# Graph Operations for Asymptotic Spectrum

This file defines graph operations needed for the theory of asymptotic spectrum:
- Strong product G ⊠ H
- Join G + H
- Costrong product G * H
- Lexicographic product G ∘ H
- G-join

## Main definitions

* `SimpleGraph.strongProduct` : The strong product of two graphs
* `SimpleGraph.join` : The join of two graphs
* `SimpleGraph.costrongProduct` : The costrong product
* `SimpleGraph.lexProduct` : The lexicographic product
* `SimpleGraph.gJoin` : The G-join operation

## References

* [Vrana, *Probabilistic refinement of the asymptotic spectrum of graphs*]
* [Zuiddam, *The asymptotic spectrum of graphs*]
-/

universe u v

namespace SimpleGraph

variable {V : Type u} {W : Type v}

/-! ### Strong Product

Defined in `ShannonCapacity` namespace (see `StrongProduct.lean`); the `⊠`
infix and `strongProduct_adj` lemma live there. -/

/-! ### Disjoint Union -/

/-- Disjoint union of graphs -/
def disjointUnion (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inl v' => G.Adj v v'
    | Sum.inr w, Sum.inr w' => H.Adj w w'
    | _, _ => False
  symm := by
    intro x y h
    cases x <;> cases y <;> first | exact False.elim h | exact G.symm h | exact H.symm h
  loopless := ⟨by
    intro x h
    cases x <;> first | exact G.irrefl h | exact H.irrefl h⟩

infixl:65 " ⊔ᵍ " => disjointUnion

theorem disjointUnion_adj_inl {G : SimpleGraph V} {H : SimpleGraph W} {v v' : V} :
    (G ⊔ᵍ H).Adj (Sum.inl v) (Sum.inl v') ↔ G.Adj v v' := Iff.rfl

theorem disjointUnion_adj_inr {G : SimpleGraph V} {H : SimpleGraph W} {w w' : W} :
    (G ⊔ᵍ H).Adj (Sum.inr w) (Sum.inr w') ↔ H.Adj w w' := Iff.rfl

theorem disjointUnion_not_adj_mix {G : SimpleGraph V} {H : SimpleGraph W}
    {v : V} {w : W} : ¬(G ⊔ᵍ H).Adj (Sum.inl v) (Sum.inr w) := False.elim

/-! ### Join -/

/-- The join G + H is the complement of the disjoint union of complements:
    G + H = compl(compl(G) ⊔ compl(H)) -/
def join (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj x y := x ≠ y ∧ match x, y with
    | Sum.inl v, Sum.inl v' => G.Adj v v'
    | Sum.inr w, Sum.inr w' => H.Adj w w'
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
  symm := by
    intro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    cases x <;> cases y <;> first | trivial | exact G.symm h | exact H.symm h
  loopless := ⟨fun _ ⟨hne, _⟩ => (hne rfl).elim⟩

infixl:65 " +ᵍ " => join

/-- In the join, vertices from different parts are always adjacent -/
theorem join_adj_inl_inr {G : SimpleGraph V} {H : SimpleGraph W} (v : V) (w : W) :
    (G +ᵍ H).Adj (Sum.inl v) (Sum.inr w) := ⟨Sum.inl_ne_inr, trivial⟩

theorem join_adj_inr_inl {G : SimpleGraph V} {H : SimpleGraph W} (w : W) (v : V) :
    (G +ᵍ H).Adj (Sum.inr w) (Sum.inl v) := ⟨Sum.inr_ne_inl, trivial⟩

/-- In the join, adjacency within the left part equals adjacency in G. -/
theorem join_adj_inl_inl {G : SimpleGraph V} {H : SimpleGraph W} {v v' : V} :
    (G +ᵍ H).Adj (Sum.inl v) (Sum.inl v') ↔ G.Adj v v' := by
  simp only [join]
  constructor
  · intro ⟨_, hadj⟩; exact hadj
  · intro hadj
    have hne : (Sum.inl v : V ⊕ W) ≠ Sum.inl v' := by
      intro h
      have heq : v = v' := Sum.inl.inj h
      exact G.irrefl (heq ▸ hadj)
    exact ⟨hne, hadj⟩

/-- In the join, adjacency within the right part equals adjacency in H. -/
theorem join_adj_inr_inr {G : SimpleGraph V} {H : SimpleGraph W} {w w' : W} :
    (G +ᵍ H).Adj (Sum.inr w) (Sum.inr w') ↔ H.Adj w w' := by
  simp only [join]
  constructor
  · intro ⟨_, hadj⟩; exact hadj
  · intro hadj
    have hne : (Sum.inr w : V ⊕ W) ≠ Sum.inr w' := by
      intro h
      have heq : w = w' := Sum.inr.inj h
      exact H.irrefl (heq ▸ hadj)
    exact ⟨hne, hadj⟩

/-- The complement of a join is the disjoint union of complements: (G + H)ᶜ = Gᶜ ⊔ Hᶜ -/
theorem compl_join (G : SimpleGraph V) (H : SimpleGraph W) :
    (G +ᵍ H)ᶜ = Gᶜ ⊔ᵍ Hᶜ := by
  ext x y
  simp only [compl_adj, join, disjointUnion, ne_eq]
  cases x <;> cases y
  · -- inl v, inl v'
    simp only [Sum.inl.injEq, not_and, true_and]
    constructor
    · intro ⟨hne, hnadj⟩
      exact ⟨hne, hnadj hne⟩
    · intro ⟨hne, hnadj⟩
      exact ⟨hne, fun _ => hnadj⟩
  · -- inl v, inr w
    simp only [Sum.inl_ne_inr, not_true_eq_false, not_and, not_false_eq_true, implies_true,
               and_true, and_false]
  · -- inr w, inl v
    simp only [Sum.inr_ne_inl, not_true_eq_false, not_and, not_false_eq_true, implies_true,
               and_true, and_false]
  · -- inr w, inr w'
    simp only [Sum.inr.injEq, not_and, true_and]
    constructor
    · intro ⟨hne, hnadj⟩
      exact ⟨hne, hnadj hne⟩
    · intro ⟨hne, hnadj⟩
      exact ⟨hne, fun _ => hnadj⟩

/-! ### Costrong Product -/

/-- The costrong product G * H = compl(compl(G) ⊠ compl(H)) -/
def costrongProduct (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) :=
  (Gᶜ ⊠ Hᶜ)ᶜ

infixl:70 " *ᵍ " => costrongProduct

/-! ### Lexicographic Product -/

/-- The lexicographic product G ∘ H has V(G) × V(H) as vertices and
    (g,h) ~ (g',h') iff g ~ g' or (g = g' and h ~ h') -/
def lexProduct (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) where
  Adj := fun ⟨g, h⟩ ⟨g', h'⟩ => G.Adj g g' ∨ (g = g' ∧ H.Adj h h')
  symm := by
    intro ⟨g, h⟩ ⟨g', h'⟩ h_adj
    rcases h_adj with hG | ⟨heq, hH⟩
    · left; exact G.symm hG
    · right; exact ⟨heq.symm, H.symm hH⟩
  loopless := ⟨by
    intro ⟨g, h⟩ h_adj
    rcases h_adj with hG | ⟨_, hH⟩
    · exact G.irrefl hG
    · exact H.irrefl hH⟩

infixl:70 " ∘ᵍ " => lexProduct

theorem lexProduct_adj {G : SimpleGraph V} {H : SimpleGraph W} {x y : V × W} :
    (G ∘ᵍ H).Adj x y ↔ G.Adj x.1 y.1 ∨ (x.1 = y.1 ∧ H.Adj x.2 y.2) := Iff.rfl

/-- Complement distributes over lexicographic product -/
theorem compl_lexProduct (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ∘ᵍ H)ᶜ = Gᶜ ∘ᵍ Hᶜ := by
  ext ⟨g, h⟩ ⟨g', h'⟩
  simp only [compl_adj, lexProduct_adj, compl_adj, ne_eq, Prod.mk.injEq, not_or, not_and]
  constructor
  · intro ⟨hne, hnadj_G, hnadj_H⟩
    by_cases heq : g = g'
    · subst heq
      right
      refine ⟨rfl, hne rfl, hnadj_H rfl⟩
    · left
      exact ⟨heq, hnadj_G⟩
  · intro h_adj
    rcases h_adj with ⟨hne_g, hnadj_G⟩ | ⟨heq_g, hne_h, hnadj_H⟩
    · refine ⟨fun heq => absurd heq hne_g, hnadj_G, fun heq => absurd heq hne_g⟩
    · subst heq_g
      refine ⟨fun _ => hne_h, G.loopless.irrefl g, fun _ => hnadj_H⟩

/-- Strong product ≤ Lexicographic product ≤ Costrong product -/
theorem strongProduct_le_lexProduct (G : SimpleGraph V) (H : SimpleGraph W) :
    G ⊠ H ≤ G ∘ᵍ H := by
  intro ⟨g, h⟩ ⟨g', h'⟩ ⟨_, hG, hH⟩
  rcases hG with heq | hG_adj
  · subst heq
    rcases hH with heq | hH_adj
    · subst heq; simp_all
    · right; exact ⟨rfl, hH_adj⟩
  · left; exact hG_adj

theorem lexProduct_le_costrongProduct (G : SimpleGraph V) (H : SimpleGraph W) :
    G ∘ᵍ H ≤ G *ᵍ H := by
  intro ⟨g, h⟩ ⟨g', h'⟩ h_lex
  unfold costrongProduct
  simp only [compl_adj, ShannonCapacity.strongProduct_adj, ne_eq, Prod.mk.injEq]
  rcases h_lex with hG | ⟨heq_g, hH⟩
  · -- Case: G.Adj g g'
    refine ⟨fun heq => (G.ne_of_adj hG) heq.1, ?_⟩
    intro ⟨_, h1, _⟩
    rcases h1 with heq_g | hnadj_G
    · subst heq_g
      exact G.irrefl hG
    · exact hnadj_G.2 hG
  · -- Case: g = g' and H.Adj h h'
    subst heq_g
    refine ⟨fun heq => (H.ne_of_adj hH) heq.2, ?_⟩
    intro ⟨hne, _, h2⟩
    rcases h2 with heq_h | hnadj_H
    · apply hne
      exact ⟨rfl, heq_h⟩
    · exact hnadj_H.2 hH

/-! ### G-join -/

/-- The G-join of a family of graphs indexed by vertices of G.
    V(G ∘ (H_v)) = Σ v, V(H_v)
    (v,h) ~ (v',h') iff v ~ v' in G, or (v = v' and h ~ h' in H_v) -/
def gJoin {ι : Type*} (G : SimpleGraph ι) (H : ι → Type*)
    (Hgraph : ∀ i, SimpleGraph (H i)) : SimpleGraph (Σ i, H i) where
  Adj := fun ⟨v, h⟩ ⟨v', h'⟩ =>
    G.Adj v v' ∨ (∃ heq : v = v', (Hgraph v).Adj h (heq ▸ h'))
  symm := by
    intro ⟨v, h⟩ ⟨v', h'⟩ h_adj
    rcases h_adj with hG | ⟨heq, hH⟩
    · left; exact G.symm hG
    · right
      subst heq
      exact ⟨rfl, (Hgraph v).symm hH⟩
  loopless := ⟨by
    intro ⟨v, h⟩ h_adj
    rcases h_adj with hG | ⟨_, hH⟩
    · exact G.irrefl hG
    · exact (Hgraph v).irrefl hH⟩

/-! ### Cohomomorphism Order -/

/-- H ≤ G in the cohomomorphism order if there exists a homomorphism compl(H) → compl(G) -/
def CohomLE (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Nonempty (Hᶜ →g Gᶜ)

notation:50 G " ≤ᶜ " H => CohomLE H G

theorem cohomLE_refl (G : SimpleGraph V) : G ≤ᶜ G :=
  ⟨Hom.id⟩

theorem cohomLE_trans {U : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph U}
    (hGH : G ≤ᶜ H) (hHK : H ≤ᶜ K) : G ≤ᶜ K := by
  obtain ⟨φ⟩ := hGH
  obtain ⟨ψ⟩ := hHK
  exact ⟨ψ.comp φ⟩

/-- Induced subgraphs satisfy the cohomomorphism order -/
theorem induce_cohomLE (G : SimpleGraph V) (S : Set V) : G.induce S ≤ᶜ G := by
  unfold CohomLE
  refine ⟨⟨Subtype.val, ?_⟩⟩
  intro ⟨s, hs⟩ ⟨s', hs'⟩ h_adj
  simp only [compl_adj] at h_adj ⊢
  constructor
  · intro heq
    exact h_adj.1 (Subtype.ext heq)
  · exact h_adj.2

/-- A graph isomorphism induces a homomorphism on complements.
    If φ : G ≃g H, then the same function is a homomorphism Gᶜ →g Hᶜ. -/
def Iso.toComplHom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    Gᶜ →g Hᶜ where
  toFun := φ
  map_rel' := by
    intro x y hadj
    simp only [compl_adj] at hadj ⊢
    constructor
    · intro heq
      exact hadj.1 (φ.injective heq)
    · intro h_adj_H
      -- h_adj_H : H.Adj (φ x) (φ y)
      -- hadj.2 : ¬G.Adj x y
      -- φ.map_rel_iff : H.Adj (φ x) (φ y) ↔ G.Adj x y
      -- From h_adj_H and mp, we get G.Adj x y, contradicting hadj.2
      exact hadj.2 (φ.map_rel_iff.mp h_adj_H)

/-- A graph isomorphism induces CohomLE in both directions. -/
theorem Iso.toCohomLE {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) : G ≤ᶜ H :=
  ⟨φ.toComplHom⟩

/-! ### Strong Power -/

/-- The n-th strong power of a graph G^⊠n.
    Vertices are functions `Fin n → V`, and two vertices f, g are adjacent iff
    f ≠ g and for all i, either f(i) = g(i) or f(i) ~ g(i) in G. -/
def strongPower (G : SimpleGraph V) (n : ℕ) : SimpleGraph (Fin n → V) where
  Adj f g := f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj (f i) (g i)
  symm := by
    intro f g ⟨hne, h⟩
    refine ⟨hne.symm, fun i => ?_⟩
    cases h i with
    | inl heq => left; exact heq.symm
    | inr hadj => right; exact hadj.symm
  loopless := ⟨fun _ ⟨hne, _⟩ => (hne rfl).elim⟩

/-- A cohomomorphism from G to H extends to a cohomomorphism from G^⊠n to H^⊠n. -/
theorem strongPower_cohomomorphism_of_cohomomorphism (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v))
    (n : ℕ) :
    let fn := fun x : Fin n → V => fun i => f (x i)
    ∀ x y, x ≠ y → ¬(strongPower G n).Adj x y →
      fn x ≠ fn y ∧ ¬(strongPower H n).Adj (fn x) (fn y) := by
  intro fn x y hxy hnadj
  simp only [strongPower] at hnadj ⊢
  have hnadj' : ∃ i, x i ≠ y i ∧ ¬G.Adj (x i) (y i) := by
    by_contra h
    push_neg at h
    apply hnadj
    constructor
    · exact hxy
    · intro i
      by_cases heq : x i = y i
      · left; exact heq
      · right; exact h i heq
  obtain ⟨i, hne_i, hnadj_i⟩ := hnadj'
  have hf_i := hf (x i) (y i) hne_i hnadj_i
  constructor
  · intro heq
    have : f (x i) = f (y i) := congr_fun heq i
    exact hf_i.1 this
  · intro ⟨_, hadj⟩
    cases hadj i with
    | inl heq => exact hf_i.1 heq
    | inr h => exact hf_i.2 h

/-! ### Independence Number under Isomorphism -/

set_option linter.unusedFintypeInType false in
/-- A cohomomorphism from G to H implies α(G) ≤ α(H).
    A cohomomorphism maps distinct non-adjacent pairs to distinct non-adjacent pairs,
    so it maps independent sets injectively to independent sets. -/
theorem independenceNumber_le_of_cohomomorphism [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v)) :
    G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_indep : G.IsIndepSet (S : Set V) :=
    (SimpleGraph.isMaximumIndepSet_iff G S).1 hSmax |>.1
  let fS := S.image f
  have hfS_indep : H.IsIndepSet (fS : Set W) := by
    apply (SimpleGraph.isIndepSet_iff H).2
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    have hxy : x ≠ y := fun h => huv (by simp [h])
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS_indep
    have hnadj : ¬ G.Adj x y := hpair (by simpa using hx) (by simpa using hy) hxy
    exact fun hadj => (hf x y hxy hnadj).2 hadj
  have hf_inj : Set.InjOn f ↑S := by
    intro x hx y hy hxy
    by_contra hne
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS_indep
    have hnadj : ¬ G.Adj x y := hpair (by simpa using hx) (by simpa using hy) hne
    exact (hf x y hne hnadj).1 hxy
  have hcard : fS.card = S.card := Finset.card_image_of_injOn hf_inj
  have hle : S.card ≤ H.indepNum := by
    simpa [hcard] using SimpleGraph.IsIndepSet.card_le_indepNum (G := H) (t := fS) hfS_indep
  have hS_card : S.card = G.indepNum := by
    simpa using SimpleGraph.maximumIndepSet_card_eq_indepNum (G := G) S hSmax
  calc G.indepNum = S.card := hS_card.symm
    _ ≤ H.indepNum := hle

/-- A graph isomorphism is a cohomomorphism. -/
private lemma iso_is_cohomomorphism' {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v) := by
  intro u v huv hnadj
  exact ⟨fun h => huv (f.injective h), fun hadj => hnadj (f.map_rel_iff'.mp hadj)⟩

set_option linter.unusedFintypeInType false in
/-- Independence number is monotone under graph isomorphisms. -/
private lemma indepNum_le_of_iso' [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.indepNum ≤ H.indepNum :=
  independenceNumber_le_of_cohomomorphism G H f (iso_is_cohomomorphism' f)

set_option linter.unusedFintypeInType false in
/-- Independence number is preserved under graph isomorphism.
    This follows because isomorphisms bijectively map independent sets to independent sets. -/
theorem independenceNumber_iso [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.indepNum = H.indepNum :=
  le_antisymm (indepNum_le_of_iso' f) (indepNum_le_of_iso' f.symm)

/-- Key lemma: Independence number is bounded by fractional clique cover weight.
If we have cliques covering each vertex with total weight ≥ 1, and total weight is W,
then any independent set has size ≤ W, so α(G) ≤ W.

Proof: Each clique contains at most 1 element of an independent set S.
Counting (clique, vertex) pairs two ways:
- Sum over cliques: ≤ W (each clique contributes weight × (at most 1))
- Sum over S: ≥ |S| (each vertex covered with weight ≥ 1)
Therefore |S| ≤ W. -/
theorem independenceNumber_le_of_clique_cover {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V)
    (cliques : Finset (Finset V)) (weights : Finset V → ℝ)
    (hclique : ∀ C ∈ cliques, G.IsClique C)
    (hpos : ∀ C ∈ cliques, weights C ≥ 0)
    (hcover : ∀ v : V, (cliques.filter (v ∈ ·)).sum weights ≥ 1)
    (W : ℝ) (hW : cliques.sum weights ≤ W) :
    (G.indepNum : ℝ) ≤ W := by
  classical
  haveI := Fintype.ofFinite V
  by_cases hW_pos : W < 0
  · have hsum_nonneg : 0 ≤ cliques.sum weights := Finset.sum_nonneg (fun C hC => hpos C hC)
    linarith
  push_neg at hW_pos
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_indep : G.IsIndepSet (S : Set V) :=
    (SimpleGraph.isMaximumIndepSet_iff G S).1 hSmax |>.1
  have hone : ∀ C ∈ cliques, (S.filter (· ∈ C)).card ≤ 1 := by
    intro C hC
    by_contra h
    push_neg at h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    rw [Finset.mem_filter] at hu hv
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS_indep
    have hnadj := hpair (by simpa using hu.1) (by simpa using hv.1) huv
    have hadj := hclique C hC hu.2 hv.2 huv
    exact hnadj hadj
  have hleft : (S.card : ℝ) ≤ S.sum (fun v => (cliques.filter (v ∈ ·)).sum weights) := by
    calc (S.card : ℝ) = S.sum (fun _ => (1 : ℝ)) := by simp
      _ ≤ S.sum (fun v => (cliques.filter (v ∈ ·)).sum weights) := by
          apply Finset.sum_le_sum
          intro v _
          exact hcover v
  have hright : S.sum (fun v => (cliques.filter (v ∈ ·)).sum weights) ≤ W := by
    calc S.sum (fun v => (cliques.filter (v ∈ ·)).sum weights)
        = S.sum (fun v => cliques.sum (fun C => if v ∈ C then weights C else 0)) := by
            congr 1; ext v; exact Finset.sum_filter _ _
      _ = cliques.sum (fun C => S.sum (fun v => if v ∈ C then weights C else 0)) := by
            rw [Finset.sum_comm]
      _ = cliques.sum (fun C => weights C * (S.filter (· ∈ C)).card) := by
            congr 1; ext C
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ cliques.sum (fun C => weights C * 1) := by
            apply Finset.sum_le_sum
            intro C hC
            apply mul_le_mul_of_nonneg_left _ (hpos C hC)
            exact_mod_cast hone C hC
      _ = cliques.sum weights := by simp
      _ ≤ W := hW
  have hS_card : S.card = G.indepNum := by
    simpa using
      (SimpleGraph.maximumIndepSet_card_eq_indepNum (G := G) S hSmax)
  have hS_le : (S.card : ℝ) ≤ W := le_trans hleft hright
  simpa [hS_card] using hS_le

end SimpleGraph

namespace ShannonCapacity

variable {U V W : Type*}

/-- Associativity of the strong product as a graph isomorphism:
    `(A ⊠ B) ⊠ C ≃g A ⊠ (B ⊠ C)`. -/
def strongProduct_assoc_iso (A : SimpleGraph U) (B : SimpleGraph V) (C : SimpleGraph W) :
    (A ⊠ B) ⊠ C ≃g A ⊠ (B ⊠ C) where
  toEquiv := Equiv.prodAssoc U V W
  map_rel_iff' := by
    intro ⟨⟨a₁, b₁⟩, c₁⟩ ⟨⟨a₂, b₂⟩, c₂⟩
    simp only [strongProduct, Equiv.prodAssoc_apply, ne_eq, Prod.mk.injEq]
    tauto

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Independence number is invariant under re-associating the strong product. -/
theorem indepNum_strongProduct_assoc
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (A : SimpleGraph U) (B : SimpleGraph V) (C : SimpleGraph W) :
    ((A ⊠ B) ⊠ C).indepNum = (A ⊠ (B ⊠ C)).indepNum :=
  SimpleGraph.independenceNumber_iso (strongProduct_assoc_iso A B C)

end ShannonCapacity
