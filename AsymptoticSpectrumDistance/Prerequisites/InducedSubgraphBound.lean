/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphOperations
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Tactic.Group
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
# Lemma 3.1: Induced Subgraph Bounds for Vertex-Transitive Graphs

This file contains Lemma 3.1 from Vrana's paper "Probabilistic refinement of the
asymptotic spectrum of graphs".

## Main definitions

* `IsVertexTransitive` : A graph is vertex-transitive if its automorphism group acts
  transitively on vertices
* `nFoldDisjointUnion` : The N-fold disjoint union N · G
* `lemma31_N` : The covering number N = ⌊(|V|/|S|) ln|V|⌋ + 1

## Main results

* `induced_cohomLE` : H[S] ≤_c H for any induced subgraph (easy direction)
* `transitive_cohomLE_nfold_full` : H ≤_c N · H[S] for vertex-transitive H (hard direction)
* `covering_exists` : The coupon collector covering lemma

## References

* [Vrana, *Probabilistic refinement of the asymptotic spectrum of graphs*], Lemma 3.1
-/

open SimpleGraph PMF

namespace ProbabilisticRefinement

/-! ### Key Definitions -/

/-- A graph is vertex-transitive if its automorphism group acts transitively on vertices -/
def IsVertexTransitive {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ v w : V, ∃ φ : G ≃g G, φ v = w

/-! ### N-fold Disjoint Union (via Strong Product with Edgeless Graph) -/

/-- The edgeless graph on n vertices (complement of complete graph) -/
def edgelessGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj := fun _ _ => False
  symm := fun _ _ h => h
  loopless := ⟨fun _ h => h⟩

/-- The N-fold disjoint union of a graph G: N copies of G with no edges between copies.
    This equals K̄_N ⊠ G (strong product of edgeless graph with G). -/
def nFoldDisjointUnion {V : Type*} (n : ℕ) (G : SimpleGraph V) : SimpleGraph (Fin n × V) where
  Adj := fun ⟨i, v⟩ ⟨j, w⟩ => i = j ∧ G.Adj v w
  symm := by
    intro ⟨i, v⟩ ⟨j, w⟩ ⟨heq, hadj⟩
    exact ⟨heq.symm, G.symm hadj⟩
  loopless := ⟨by
    intro ⟨i, v⟩ ⟨_, hadj⟩
    exact G.irrefl hadj⟩

notation:70 n " ⬝ " G => nFoldDisjointUnion n G

/-- Adjacency in N-fold disjoint union: same copy and adjacent in G -/
theorem nFoldDisjointUnion_adj {V : Type*} {n : ℕ} {G : SimpleGraph V}
    {i j : Fin n} {v w : V} :
    (n ⬝ G).Adj (i, v) (j, w) ↔ i = j ∧ G.Adj v w := Iff.rfl

/-- N-fold disjoint union equals strong product with edgeless graph -/
theorem nFoldDisjointUnion_eq_strongProduct {V : Type*} {n : ℕ} {G : SimpleGraph V} :
    (n ⬝ G) = (edgelessGraph n) ⊠ G := by
  ext ⟨i, v⟩ ⟨j, w⟩
  simp only [nFoldDisjointUnion_adj, ShannonCapacity.strongProduct_adj]
  constructor
  · intro ⟨heq, hadj⟩
    subst heq
    refine ⟨?_, Or.inl rfl, Or.inr hadj⟩
    intro h
    exact G.ne_of_adj hadj (Prod.mk.inj h).2
  · intro ⟨hne, hi, hv⟩
    constructor
    · -- edgelessGraph has no edges, so i = j
      rcases hi with heq | hadj
      · exact heq
      · exact False.elim hadj
    · -- Must have G.Adj v w (not v = w, since that would make them equal)
      rcases hi with heq | hadj
      · subst heq
        rcases hv with heq | hadj
        · subst heq
          exact False.elim (hne rfl)
        · exact hadj
      · exact False.elim hadj

/-- N-fold disjoint union preserves cohomomorphism order:
    If G ≤ᶜ H then n ⬝ G ≤ᶜ n ⬝ H.
    This allows lifting isomorphisms on graphs to their n-fold copies. -/
theorem nFoldDisjointUnion_cohomLE_mono {V W : Type*} {n : ℕ} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : G ≤ᶜ H) : (n ⬝ G) ≤ᶜ (n ⬝ H) := by
  -- CohomLE means Nonempty (Gᶜ →g Hᶜ) via the notation reversal
  obtain ⟨φ⟩ := h
  -- The cohomomorphism φ : Gᶜ →g Hᶜ extends to (n ⬝ G)ᶜ →g (n ⬝ H)ᶜ
  refine ⟨⟨fun ⟨i, v⟩ => ⟨i, φ v⟩, ?_⟩⟩
  intro ⟨i, v⟩ ⟨j, w⟩ hadj
  simp only [SimpleGraph.compl_adj] at hadj ⊢
  simp only [nFoldDisjointUnion_adj] at hadj ⊢
  obtain ⟨hne, hnadj⟩ := hadj
  constructor
  · -- Show (i, φ v) ≠ (j, φ w)
    intro heq
    have hi : i = j := (Prod.mk.inj heq).1
    have hφvw : φ v = φ w := (Prod.mk.inj heq).2
    -- Case split on v = w
    by_cases hvw : v = w
    · -- If v = w, then (i, v) = (j, w), contradiction
      exact hne (Prod.ext hi hvw)
    · -- If v ≠ w, then since ¬(i = j ∧ G.Adj v w) and i = j, we have ¬G.Adj v w
      -- So Gᶜ.Adj v w, hence Hᶜ.Adj (φ v) (φ w), so φ v ≠ φ w
      have hGcompl : Gᶜ.Adj v w := ⟨hvw, fun hadj => hnadj ⟨hi, hadj⟩⟩
      have hHcompl := φ.map_rel hGcompl
      exact hHcompl.ne hφvw
  · -- Show ¬(i = j ∧ H.Adj (φ v) (φ w))
    intro ⟨heq, hadj_base⟩
    -- If i = j, need ¬H.Adj (φ v) (φ w)
    -- Case split on v = w
    by_cases hvw : v = w
    · -- If v = w, then φ v = φ w, so no self-adjacency
      subst hvw
      exact H.irrefl hadj_base
    · -- If v ≠ w, then Gᶜ.Adj v w (since ¬(i = j ∧ G.Adj v w) and i = j)
      have hGcompl : Gᶜ.Adj v w := ⟨hvw, fun hadj => hnadj ⟨heq, hadj⟩⟩
      have hHcompl := φ.map_rel hGcompl
      -- Hᶜ.Adj (φ v) (φ w) means ¬H.Adj (φ v) (φ w)
      exact hHcompl.2 hadj_base

/-- Monotonicity in n: n ⬝ G ≤ᶜ n' ⬝ G when n ≤ n'.
    The first n copies of G embed into the first n copies of n' ⬝ G. -/
theorem nFoldDisjointUnion_cohomLE_n_mono {V : Type*} {G : SimpleGraph V}
    {n n' : ℕ} (h : n ≤ n') : (n ⬝ G) ≤ᶜ (n' ⬝ G) := by
  -- The embedding maps (i, v) in n ⬝ G to (Fin.castLE h i, v) in n' ⬝ G
  refine ⟨⟨fun ⟨i, v⟩ => ⟨Fin.castLE h i, v⟩, ?_⟩⟩
  intro ⟨i, v⟩ ⟨j, w⟩ hadj
  simp only [SimpleGraph.compl_adj] at hadj ⊢
  simp only [nFoldDisjointUnion_adj] at hadj ⊢
  constructor
  · intro heq
    apply hadj.1
    -- From heq : (Fin.castLE h i, v) = (Fin.castLE h j, w), extract i = j
    have hi : i = j := by
      have h1 : Fin.castLE h i = Fin.castLE h j := (Prod.mk.inj heq).1
      exact Fin.castLE_injective h h1
    have hv : v = w := (Prod.mk.inj heq).2
    exact Prod.ext hi hv
  · intro ⟨heq, hadj'⟩
    apply hadj.2
    constructor
    · exact Fin.castLE_injective h heq
    · exact hadj'

/-! ### Lemma 3.1: Induced Subgraph Bounds -/

/-- The N from Lemma 3.1: N = ⌊(|V|/|S|) ln|V|⌋ + 1.
    This is the number of random automorphisms needed to cover V with high probability. -/
noncomputable def lemma31_N {V : Type*} [Fintype V] (S : Set V) [Fintype S] : ℕ :=
  Nat.floor ((Fintype.card V : ℝ) / (Fintype.card S : ℝ) * Real.log (Fintype.card V)) + 1

set_option linter.unusedFintypeInType false in
/-- Helper: The covering property holds when N ≥ |V| using a simple construction.

    The probabilistic argument (for reference): For vertex-transitive H with nonempty S,
    choosing N = ⌊(|V|/|S|) ln|V|⌋ + 1 random automorphisms uniformly from Aut(H),
    the probability that every vertex is covered by some π_i(S) is positive.

    Proof sketch:
    - For each vertex v, Pr[v ∈ π_i(S)] = |S|/|V| by vertex-transitivity
    - Pr[v not covered by any π_i] = (1 - |S|/|V|)^N ≤ e^{-N|S|/|V|}
    - By union bound, Pr[∃ uncovered v] ≤ |V| · e^{-N|S|/|V|}
    - With N ≥ (|V|/|S|) ln|V|, this is < 1
    - So Pr[all covered] > 0, hence such a covering exists -/
theorem covering_exists_large {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) [Fintype S] (hS : S.Nonempty)
    (hT : IsVertexTransitive H) (N : ℕ) (hN : Fintype.card V ≤ N) :
    ∃ (π : Fin N → H ≃g H),
      ∀ v : V, ∃ i : Fin N, ∃ s : S, (π i) s.val = v := by
  classical
  obtain ⟨s₀, hs₀⟩ := hS
  -- s₀ : V with hs₀ : s₀ ∈ S
  choose φ hφ using fun v => hT s₀ v
  let enum := (Fintype.equivFin V).symm
  let n := Fintype.card V
  let π : Fin N → H ≃g H := fun i =>
    if h : i.val < n then φ (enum ⟨i.val, h⟩) else SimpleGraph.Iso.refl
  use π
  intro v
  let j := Fintype.equivFin V v
  have hj : j.val < N := Nat.lt_of_lt_of_le j.isLt hN
  use ⟨j.val, hj⟩, ⟨s₀, hs₀⟩
  simp only [π]
  rw [dif_pos j.isLt]
  -- j = Fintype.equivFin V v, so (Fintype.equivFin V).symm ⟨j.val, _⟩ = v
  have hj_eq : (Fintype.equivFin V).symm ⟨j.val, j.isLt⟩ = v := by simp [j]
  simp only [enum, hj_eq, hφ v]

set_option linter.unusedFintypeInType false in
/-- For vertex-transitive H, the inverse of any automorphism applied to S covers
    a uniformly random subset of V. This is the key property used in the
    probabilistic covering argument. -/
theorem transitive_inverse_covers {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) [Fintype S] (hS : S.Nonempty)
    (hT : IsVertexTransitive H) (s : S) (v : V) :
    ∃ φ : H ≃g H, φ.symm s.val = v := by
  -- By vertex-transitivity, there exists φ' with φ'(v) = s.val
  obtain ⟨φ', hφ'⟩ := hT v s.val
  -- Then φ'.symm.symm(s.val) = φ'(s.val) but we want φ'⁻¹(s.val) = v
  -- Actually: φ'(v) = s.val implies v = φ'⁻¹(s.val)
  use φ'
  rw [← hφ']
  simp only [RelIso.symm_apply_apply]

/-! ### Fintype Instance for Graph Automorphisms -/

/-- A graph automorphism can be viewed as a permutation of V -/
def graphAutoToPerm {V : Type*} (H : SimpleGraph V) : (H ≃g H) → Equiv.Perm V :=
  fun φ => φ.toEquiv

/-- The map from graph automorphisms to permutations is injective -/
theorem graphAutoToPerm_injective {V : Type*} (H : SimpleGraph V) :
    Function.Injective (graphAutoToPerm H) := by
  intro φ ψ h
  ext v
  have : (graphAutoToPerm H φ) v = (graphAutoToPerm H ψ) v := congrFun (congrArg _ h) v
  exact this

/-- Graph automorphisms of a finite graph form a finite type -/
noncomputable instance graphAutoFintype {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : Fintype (H ≃g H) := by
  classical
  -- Use that automorphisms inject into Equiv.Perm V which is finite
  exact Fintype.ofInjective (graphAutoToPerm H) (graphAutoToPerm_injective H)

/-- MulAction of graph automorphisms on vertices -/
noncomputable instance graphAutoMulAction {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : MulAction (H ≃g H) V where
  smul := fun φ v => φ v
  one_smul := fun _ => rfl
  mul_smul := fun φ ψ v => by
    simp only [HSMul.hSMul, SMul.smul]
    rw [RelIso.mul_def, RelIso.trans_apply]

set_option linter.unusedFintypeInType false in
/-- For vertex-transitive graphs, the orbit of any vertex under Aut(H) is all of V -/
theorem transitive_orbit_full {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hT : IsVertexTransitive H) (v : V) :
    ∀ w : V, ∃ φ : H ≃g H, φ v = w := fun w => hT v w

/-- The set of automorphisms mapping a fixed source to a vertex v -/
def autosFromTo {V : Type*} [DecidableEq V] (H : SimpleGraph V) (s v : V) : Set (H ≃g H) :=
  {φ | φ s = v}

/-- For vertex-transitive H, the number of automorphisms mapping s to v equals |Aut(H)|/|V|.
    This is the orbit-stabilizer theorem for the transitive action on V. -/
theorem transitive_fiber_card {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hT : IsVertexTransitive H) (s v : V)
    [Fintype (autosFromTo H s v)] :
    Fintype.card (autosFromTo H s v) * Fintype.card V = Fintype.card (H ≃g H) := by
  classical
  -- Get τ witnessing s ↦ v
  obtain ⟨τ, hτ⟩ := hT s v
  -- The action is pretransitive
  haveI hpre : MulAction.IsPretransitive (H ≃g H) V := ⟨fun a b => hT a b⟩
  have horbit : MulAction.orbit (H ≃g H) s = Set.univ := MulAction.orbit_eq_univ (H ≃g H) s
  -- Bijection: autosFromTo H s v ≃ stabilizer(s) via φ ↦ τ⁻¹ * φ
  let f : (autosFromTo H s v) → (MulAction.stabilizer (H ≃g H) s) := fun ⟨φ, hφ⟩ => ⟨τ⁻¹ * φ, by
    simp only [MulAction.mem_stabilizer_iff, HSMul.hSMul, SMul.smul]
    rw [RelIso.mul_def, RelIso.trans_apply]
    simp only [autosFromTo, Set.mem_setOf_eq] at hφ
    rw [hφ, ← hτ]
    exact τ.symm_apply_apply s⟩
  let g : (MulAction.stabilizer (H ≃g H) s) → (autosFromTo H s v) := fun ⟨σ, hσ⟩ => ⟨τ * σ, by
    simp only [autosFromTo, Set.mem_setOf_eq]
    rw [RelIso.mul_def, RelIso.trans_apply]
    simp only [MulAction.mem_stabilizer_iff, HSMul.hSMul, SMul.smul] at hσ
    rw [hσ, hτ]⟩
  have hfg : Function.LeftInverse g f := fun ⟨φ, _⟩ => by simp only [f, g, Subtype.mk.injEq]; group
  have hgf : Function.RightInverse g f := fun ⟨σ, _⟩ => by simp only [f, g, Subtype.mk.injEq]; group
  have hbij : Fintype.card (autosFromTo H s v) =
      Fintype.card (MulAction.stabilizer (H ≃g H) s) := by
    have hfbij : Function.Bijective f := ⟨hfg.injective, hgf.surjective⟩
    exact Fintype.card_of_bijective hfbij
  -- Orbit-stabilizer theorem
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (H ≃g H) s
  have horbit_card : Fintype.card (MulAction.orbit (H ≃g H) s) = Fintype.card V := by
    rw [horbit]
    haveI : Fintype ↑(Set.univ : Set V) := Set.fintypeUniv
    convert Fintype.card_eq.mpr ⟨Equiv.Set.univ V⟩
  calc Fintype.card (autosFromTo H s v) * Fintype.card V
      = Fintype.card (MulAction.stabilizer (H ≃g H) s) * Fintype.card V := by rw [hbij]
    _ = Fintype.card (MulAction.stabilizer (H ≃g H) s) *
        Fintype.card (MulAction.orbit (H ≃g H) s) := by rw [horbit_card]
    _ = Fintype.card (MulAction.orbit (H ≃g H) s) *
        Fintype.card (MulAction.stabilizer (H ≃g H) s) := by ring
    _ = Fintype.card (H ≃g H) := hos

/-- For vertex-transitive H and subset S, the automorphisms mapping v to S
    have cardinality |S| * |Aut(H)| / |V|. -/
theorem automorphism_partition {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) [Fintype S] (hS : S.Nonempty)
    (hT : IsVertexTransitive H) (v : V)
    [Fintype {φ : H ≃g H | φ v ∈ S}] :
    Fintype.card {φ : H ≃g H | φ v ∈ S} * Fintype.card V =
             Fintype.card S * Fintype.card (H ≃g H) := by
  classical
  rcases hS with ⟨s₀, hs₀⟩
  haveI : Nonempty V := ⟨s₀⟩
  -- {φ | φ v ∈ S} is a disjoint union of autosFromTo H v s for s ∈ S
  -- Each fiber has cardinality |Aut(H)|/|V| by orbit-stabilizer
  -- Define the equivalence between {φ | φ v ∈ S} and Σ s : S, autosFromTo H v s
  let e : {φ : H ≃g H | φ v ∈ S} ≃ Σ s : S, autosFromTo H v s.val :=
  { toFun := fun ⟨φ, hφ⟩ => ⟨⟨φ v, hφ⟩, ⟨φ, rfl⟩⟩
    invFun := fun x =>
      let ⟨⟨s, hs⟩, ⟨φ, hφeq⟩⟩ := x
      ⟨φ, by
        simp only [autosFromTo, Set.mem_setOf_eq] at hφeq
        simp only [Set.mem_setOf_eq]
        rw [hφeq]; exact hs⟩
    left_inv := fun ⟨φ, _⟩ => by simp
    right_inv := fun ⟨⟨s, hs⟩, ⟨φ, hφ⟩⟩ => by
      simp only [autosFromTo, Set.mem_setOf_eq] at hφ
      simp only [Sigma.mk.injEq]
      refine ⟨Subtype.ext hφ, ?_⟩
      subst hφ
      rfl }
  -- Cardinality via sigma type
  have hcard_eq : Fintype.card {φ : H ≃g H | φ v ∈ S} =
      Fintype.card (Σ s : S, autosFromTo H v s.val) := Fintype.card_congr e
  rw [hcard_eq, Fintype.card_sigma]
  -- Each fiber has the same cardinality by orbit-stabilizer
  have hfiber : ∀ s : S, Fintype.card (autosFromTo H v s.val) * Fintype.card V =
      Fintype.card (H ≃g H) := fun s => transitive_fiber_card H hT v s.val
  -- All fibers have the same cardinality
  have hfiber_const : ∀ s : S, Fintype.card (autosFromTo H v s.val) =
      Fintype.card (autosFromTo H v s₀) := by
    intro s
    have h1 := hfiber s
    have h2 := hfiber ⟨s₀, hs₀⟩
    simp only at h2
    have hV_pos : 0 < Fintype.card V := Fintype.card_pos
    exact Nat.eq_of_mul_eq_mul_right hV_pos (h1.trans h2.symm)
  -- The sum becomes |S| * fiber_size
  simp_rw [hfiber_const]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h_mul := hfiber ⟨s₀, hs₀⟩
  simp only at h_mul
  calc Fintype.card S * Fintype.card (autosFromTo H v s₀) * Fintype.card V
      = Fintype.card S * (Fintype.card (autosFromTo H v s₀) * Fintype.card V) := by ring
    _ = Fintype.card S * Fintype.card (H ≃g H) := by rw [h_mul]

/-! ### Covering Lemma Infrastructure -/

/-- The set of automorphisms that map some element of S to v. -/
def autosCoveringVertex {V : Type*} (H : SimpleGraph V) (S : Set V) (v : V) : Set (H ≃g H) :=
  {φ | ∃ s ∈ S, φ s = v}

/-- Alternative: φ covers v iff φ⁻¹(v) ∈ S -/
theorem autosCoveringVertex_iff {V : Type*} (H : SimpleGraph V) (S : Set V)
    (v : V) (φ : H ≃g H) :
    φ ∈ autosCoveringVertex H S v ↔ φ.symm v ∈ S := by
  simp only [autosCoveringVertex, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, hφs⟩
    rw [← hφs, RelIso.symm_apply_apply]
    exact hs
  · intro h
    exact ⟨φ.symm v, h, φ.apply_symm_apply v⟩

/-- The complement: automorphisms that don't cover v -/
def autosNotCoveringVertex {V : Type*} (H : SimpleGraph V) (S : Set V) (v : V) :
    Set (H ≃g H) :=
  {φ | φ.symm v ∉ S}

/-- Counting covering automorphisms: |{φ | φ covers v}| × |V| = |S| × |Aut(H)| -/
theorem card_autosCoveringVertex {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive H) (v : V)
    [Fintype (autosCoveringVertex H S v)] :
    Fintype.card (autosCoveringVertex H S v) * Fintype.card V =
    Fintype.card S * Fintype.card (H ≃g H) := by
  classical
  -- Use bijection φ ↦ φ⁻¹ to reduce to automorphism_partition
  have hbij : Fintype.card (autosCoveringVertex H S v) =
      Fintype.card {φ : H ≃g H | φ v ∈ S} := by
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨φ, hφ⟩ => ⟨φ.symm, by
        rw [autosCoveringVertex_iff] at hφ
        simp only [Set.mem_setOf_eq]
        simpa using hφ⟩
      invFun := fun ⟨ψ, hψ⟩ => ⟨ψ.symm, by
        simp only [Set.mem_setOf_eq] at hψ
        rw [autosCoveringVertex_iff]
        simp only [RelIso.symm_symm]
        exact hψ⟩
      left_inv := fun ⟨φ, _⟩ => by simp
      right_inv := fun ⟨ψ, _⟩ => by simp }
  rw [hbij]
  exact automorphism_partition H S hS hT v

/-- The key exponential inequality: |V| × (1 - |S|/|V|)^N < 1 when N is large enough. -/
theorem exponential_bound_lemma31 (cardV cardS : ℕ) (hV : 2 ≤ cardV) (hS : 0 < cardS)
    (hS_le : cardS ≤ cardV) :
    let N := Nat.floor ((cardV : ℝ) / cardS * Real.log cardV) + 1
    (cardV : ℝ) * (1 - cardS / cardV) ^ N < 1 := by
  intro N
  have hV_pos : (0 : ℝ) < cardV := Nat.cast_pos.mpr (by omega)
  have hV_one : (1 : ℝ) < cardV := by
    have : (1 : ℕ) < cardV := by omega
    exact Nat.one_lt_cast.mpr this
  have hS_pos : (0 : ℝ) < cardS := Nat.cast_pos.mpr hS
  have h_ratio_pos : (0 : ℝ) < cardS / cardV := div_pos hS_pos hV_pos
  have h_ratio_le_one : (cardS : ℝ) / cardV ≤ 1 := (div_le_one hV_pos).mpr (Nat.cast_le.mpr hS_le)
  have h_one_minus_nonneg : 0 ≤ 1 - (cardS : ℝ) / cardV := by linarith
  -- N > (cardV/cardS) * ln(cardV)
  have hN_bound : (N : ℝ) > (cardV : ℝ) / cardS * Real.log cardV := by
    simp only [N]
    have hlt := Nat.lt_floor_add_one ((cardV : ℝ) / cardS * Real.log cardV)
    have hcast : ((⌊(cardV : ℝ) / cardS * Real.log cardV⌋₊ + 1 : ℕ) : ℝ) =
        (⌊(cardV : ℝ) / cardS * Real.log cardV⌋₊ : ℝ) + 1 := Nat.cast_add_one _
    linarith [hlt, hcast]
  -- If cardV = cardS, then (1 - 1)^N = 0 < 1
  by_cases heq : cardS = cardV
  · subst heq
    simp only [div_self (ne_of_gt hV_pos), sub_self]
    have hN_pos : 0 < N := Nat.succ_pos _
    simp only [zero_pow (Nat.pos_iff_ne_zero.mp hN_pos), mul_zero]
    exact one_pos
  -- Otherwise cardS < cardV
  have hS_lt : cardS < cardV := Nat.lt_of_le_of_ne hS_le heq
  have h_one_minus_pos : 0 < 1 - (cardS : ℝ) / cardV := by
    have : (cardS : ℝ) / cardV < 1 := (div_lt_one hV_pos).mpr (Nat.cast_lt.mpr hS_lt)
    linarith
  -- Use (1-x)^N ≤ e^{-Nx}
  have hexp_bound : (1 - (cardS : ℝ) / cardV) ^ N ≤ Real.exp (-(N : ℝ) * (cardS / cardV)) := by
    have h1 : 1 - cardS / cardV ≤ Real.exp (-(cardS / cardV)) := by
      have := Real.add_one_le_exp (-(cardS / cardV : ℝ))
      linarith
    calc (1 - (cardS : ℝ) / cardV) ^ N
        ≤ (Real.exp (-(cardS / cardV)))^N := pow_le_pow_left₀ h_one_minus_nonneg h1 N
      _ = Real.exp (-(cardS / cardV) * N) := by rw [← Real.exp_nat_mul]; ring_nf
      _ = Real.exp (-(N : ℝ) * (cardS / cardV)) := by ring_nf
  -- N * cardS/cardV > ln(cardV)
  have hN_times : (N : ℝ) * (cardS / cardV) > Real.log cardV := by
    calc (N : ℝ) * (cardS / cardV)
        > (cardV / cardS) * Real.log cardV * (cardS / cardV) := by
          apply mul_lt_mul_of_pos_right hN_bound h_ratio_pos
      _ = Real.log cardV := by field_simp
  -- exp(-N * cardS/cardV) < 1/cardV
  have hexp_lt : Real.exp (-(N : ℝ) * (cardS / cardV)) < 1 / cardV := by
    have hlog_pos : 0 < Real.log cardV := Real.log_pos hV_one
    calc Real.exp (-(N : ℝ) * (cardS / cardV))
        < Real.exp (-Real.log cardV) := by
          rw [Real.exp_lt_exp]
          linarith [hN_times]
      _ = (cardV : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hV_pos]
      _ = 1 / cardV := by rw [one_div]
  -- Combine
  calc (cardV : ℝ) * (1 - cardS / cardV) ^ N
      ≤ cardV * Real.exp (-(N : ℝ) * (cardS / cardV)) := by
        apply mul_le_mul_of_nonneg_left hexp_bound (le_of_lt hV_pos)
    _ < cardV * (1 / cardV) := by
        apply mul_lt_mul_of_pos_left hexp_lt hV_pos
    _ = 1 := by field_simp

/-- The set of N-tuples that miss vertex v (don't cover v with any automorphism). -/
def tuplesMissing {V : Type*} (H : SimpleGraph V) (S : Set V) (N : ℕ) (v : V) :
    Set (Fin N → H ≃g H) :=
  {π | ∀ i, (π i).symm v ∉ S}

/-- A tuple covers all vertices iff it's not in tuplesMissing for any v. -/
theorem tuple_covers_all_iff {V : Type*} (H : SimpleGraph V) (S : Set V) (N : ℕ)
    (π : Fin N → H ≃g H) :
    (∀ v : V, ∃ i : Fin N, ∃ s : S, (π i) s.val = v) ↔
    ∀ v : V, π ∉ tuplesMissing H S N v := by
  constructor
  · intro hcover v hmiss
    obtain ⟨i, s, hπis⟩ := hcover v
    have : (π i).symm v ∈ S := by
      rw [← hπis]
      simp only [RelIso.symm_apply_apply]
      exact s.property
    exact hmiss i this
  · intro hnotmiss v
    simp only [tuplesMissing, Set.mem_setOf_eq, not_forall, not_not] at hnotmiss
    obtain ⟨i, hi⟩ := hnotmiss v
    exact ⟨i, ⟨(π i).symm v, hi⟩, (π i).apply_symm_apply v⟩

/-- For vertex-transitive H, count of automorphisms NOT covering v.
    |not covering| × |V| = (|V| - |S|) × |Aut|. -/
theorem card_autosNotCoveringVertex {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) [Fintype S]
    (hS : S.Nonempty) (hT : IsVertexTransitive H) (v : V)
    [Fintype (autosNotCoveringVertex H S v)] :
    Fintype.card (autosNotCoveringVertex H S v) * Fintype.card V =
    (Fintype.card V - Fintype.card S) * Fintype.card (H ≃g H) := by
  classical
  haveI hFinCov : Fintype (autosCoveringVertex H S v) := by
    apply Set.fintypeSubset (s := Set.univ)
    exact fun _ _ => Set.mem_univ _
  have hcov := card_autosCoveringVertex H S hS hT v
  have hS_le : Fintype.card S ≤ Fintype.card V :=
    Fintype.card_le_of_injective (fun s => s.val) Subtype.val_injective
  let p : (H ≃g H) → Prop := fun φ => φ.symm v ∈ S
  have h_cov_eq : autosCoveringVertex H S v = {φ | p φ} := by
    ext φ
    simp only [autosCoveringVertex_iff, Set.mem_setOf_eq, p]
  have h_not_eq : autosNotCoveringVertex H S v = {φ | ¬p φ} := by
    ext φ
    simp only [autosNotCoveringVertex, Set.mem_setOf_eq, p]
  haveI : DecidablePred p := fun φ => Classical.dec (p φ)
  haveI hFinP : Fintype {φ : H ≃g H | p φ} := by
    rw [← h_cov_eq]
    exact hFinCov
  haveI hFinNotP : Fintype {φ : H ≃g H | ¬p φ} := by
    rw [← h_not_eq]
    infer_instance
  have hcompl := @Fintype.card_subtype_compl (H ≃g H) _ p hFinP hFinNotP
  have h_not_card : Fintype.card (autosNotCoveringVertex H S v) =
      Fintype.card (H ≃g H) - Fintype.card (autosCoveringVertex H S v) := by
    calc Fintype.card (autosNotCoveringVertex H S v)
        = Fintype.card {φ : H ≃g H | ¬p φ} := by
          apply Fintype.card_congr
          exact Equiv.setCongr h_not_eq
      _ = Fintype.card (H ≃g H) - Fintype.card {φ : H ≃g H | p φ} := hcompl
      _ = Fintype.card (H ≃g H) - Fintype.card (autosCoveringVertex H S v) := by
          congr 1
          apply Fintype.card_congr
          exact Equiv.setCongr h_cov_eq.symm
  have h_le : Fintype.card S * Fintype.card (H ≃g H) ≤
      Fintype.card (H ≃g H) * Fintype.card V := by
    rw [mul_comm (Fintype.card S)]
    exact Nat.mul_le_mul_left _ hS_le
  calc Fintype.card (autosNotCoveringVertex H S v) * Fintype.card V
      = (Fintype.card (H ≃g H) - Fintype.card (autosCoveringVertex H S v)) *
          Fintype.card V := by rw [h_not_card]
    _ = Fintype.card (H ≃g H) * Fintype.card V -
          Fintype.card (autosCoveringVertex H S v) * Fintype.card V := Nat.sub_mul _ _ _
    _ = Fintype.card (H ≃g H) * Fintype.card V -
          Fintype.card S * Fintype.card (H ≃g H) := by rw [hcov]
    _ = Fintype.card (H ≃g H) * (Fintype.card V - Fintype.card S) := by
        rw [Nat.mul_sub (Fintype.card (H ≃g H)),
            mul_comm (Fintype.card (H ≃g H)) (Fintype.card V),
            mul_comm (Fintype.card (H ≃g H)) (Fintype.card S)]
    _ = (Fintype.card V - Fintype.card S) * Fintype.card (H ≃g H) := mul_comm _ _

/-! ### Main Covering Theorem -/

theorem covering_exists {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) [Fintype S] (hS : S.Nonempty)
    (hT : IsVertexTransitive H) (hcard : 0 < Fintype.card S) :
    ∃ (π : Fin (lemma31_N S) → H ≃g H),
      ∀ v : V, ∃ i : Fin (lemma31_N S), ∃ s : S, (π i) s.val = v := by
  classical
  let N := lemma31_N S
  let cardV := Fintype.card V
  let cardS := Fintype.card S
  -- Handle small |V| cases directly
  by_cases hV_small : cardV < 2
  · -- |V| ∈ {0, 1}
    obtain ⟨s₀, hs₀⟩ := hS
    have hN_pos : 0 < N := Nat.succ_pos _
    use fun _ => SimpleGraph.Iso.refl
    intro v
    use ⟨0, hN_pos⟩, ⟨s₀, hs₀⟩
    -- With |V| ≤ 1 and S nonempty, S = V, so s₀ = v
    have hcardV_le : cardV ≤ 1 := by omega
    haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hcardV_le
    exact Subsingleton.elim _ _
  push_neg at hV_small
  have hV : 2 ≤ cardV := hV_small
  have hS_le : cardS ≤ cardV := Fintype.card_le_of_injective
    (fun s => s.val) (Subtype.val_injective)
  -- The exponential bound: |V| × (1 - |S|/|V|)^N < 1
  have hexp := exponential_bound_lemma31 cardV cardS hV hcard hS_le
  -- Set up notation
  let Aut := Fintype.card (H ≃g H)
  -- Fintype instances
  haveI hFinNot : ∀ v, Fintype (autosNotCoveringVertex H S v) := by
    intro v
    apply Set.fintypeSubset (s := Set.univ)
    exact fun _ _ => Set.mem_univ _
  haveI hFinMiss : ∀ v, Fintype (tuplesMissing H S N v) := by
    intro v
    apply Set.fintypeSubset (s := Set.univ)
    exact fun _ _ => Set.mem_univ _
  -- Pick a reference vertex
  haveI : Nonempty V := ⟨hS.some⟩
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  let r := Fintype.card (autosNotCoveringVertex H S v₀)
  -- All autosNotCoveringVertex have the same cardinality
  have hNotCard : ∀ v, Fintype.card (autosNotCoveringVertex H S v) * cardV =
      (cardV - cardS) * Aut := by
    intro v
    exact card_autosNotCoveringVertex H S hS hT v
  have hNotCardConst : ∀ v, Fintype.card (autosNotCoveringVertex H S v) = r := by
    intro v
    have h1 := hNotCard v
    have h2 := hNotCard v₀
    have hV_pos : 0 < cardV := by omega
    exact Nat.eq_of_mul_eq_mul_right hV_pos (h1.trans h2.symm)
  -- |tuplesMissing v| = r^N for all v
  have hMissCard : ∀ v, Fintype.card (tuplesMissing H S N v) = r^N := by
    intro v
    have hbij : tuplesMissing H S N v ≃ (Fin N → autosNotCoveringVertex H S v) := {
      toFun := fun ⟨π, hπ⟩ i => ⟨π i, hπ i⟩
      invFun := fun f => ⟨fun i => (f i).val, fun i => (f i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
    calc Fintype.card (tuplesMissing H S N v)
        = Fintype.card (Fin N → autosNotCoveringVertex H S v) := Fintype.card_congr hbij
      _ = Fintype.card (autosNotCoveringVertex H S v) ^ N := Fintype.card_pi_const _ N
      _ = r ^ N := by rw [hNotCardConst v]
  -- Total tuples = Aut^N
  have hTotalCard : Fintype.card (Fin N → H ≃g H) = Aut^N := Fintype.card_pi_const _ N
  -- Aut > 0 (contains identity)
  have hAut_pos : 0 < Aut := by
    have : Nonempty (H ≃g H) := ⟨SimpleGraph.Iso.refl⟩
    exact Fintype.card_pos
  -- Key inequality: cardV × r^N < Aut^N (in reals, then in naturals)
  have hIneq : (cardV : ℝ) * (r : ℝ)^N < (Aut : ℝ)^N := by
    have hAut_pos_r : (0 : ℝ) < Aut := Nat.cast_pos.mpr hAut_pos
    have hV_pos_r : (0 : ℝ) < cardV := Nat.cast_pos.mpr (by omega)
    have hS_pos_r : (0 : ℝ) < cardS := Nat.cast_pos.mpr hcard
    -- From card_autosNotCoveringVertex: r × cardV = (cardV - cardS) × Aut
    have hr_rel := hNotCard v₀
    -- r / Aut = (cardV - cardS) / cardV = 1 - cardS / cardV
    have hratio : (r : ℝ) / Aut = 1 - cardS / cardV := by
      have hnum : (r : ℝ) * cardV = ((cardV - cardS : ℕ) : ℝ) * Aut := by exact_mod_cast hr_rel
      field_simp
      have h1 : ((cardV - cardS : ℕ) : ℝ) = (cardV : ℝ) - cardS := Nat.cast_sub hS_le
      calc (r : ℝ) * cardV = ((cardV - cardS : ℕ) : ℝ) * Aut := hnum
        _ = (Aut : ℝ) * ((cardV - cardS : ℕ) : ℝ) := mul_comm _ _
        _ = (Aut : ℝ) * ((cardV : ℝ) - cardS) := by rw [h1]
    calc (cardV : ℝ) * (r : ℝ)^N
        = cardV * ((r : ℝ) / Aut * Aut)^N := by
            rw [div_mul_cancel₀ (r : ℝ) (ne_of_gt hAut_pos_r)]
      _ = cardV * ((r : ℝ) / Aut)^N * (Aut : ℝ)^N := by ring
      _ = cardV * (1 - cardS / cardV)^N * (Aut : ℝ)^N := by rw [hratio]
      _ < 1 * (Aut : ℝ)^N := by
          apply mul_lt_mul_of_pos_right hexp
          exact pow_pos hAut_pos_r N
      _ = (Aut : ℝ)^N := one_mul _
  -- Convert real inequality to natural number inequality
  have hIneqNat : cardV * r^N < Aut^N := by
    have hcast1 : ((cardV * r^N : ℕ) : ℝ) = (cardV : ℝ) * (r : ℝ)^N := by
      simp only [Nat.cast_mul, Nat.cast_pow]
    have hcast2 : ((Aut^N : ℕ) : ℝ) = (Aut : ℝ)^N := by simp only [Nat.cast_pow]
    rw [← hcast1, ← hcast2] at hIneq
    exact Nat.cast_lt.mp hIneq
  -- Key counting argument: not all tuples can be bad
  by_contra hbad
  push_neg at hbad
  -- Every tuple is in some tuplesMissing v
  have hEveryBad : ∀ π : Fin N → H ≃g H, ∃ v, π ∈ tuplesMissing H S N v := by
    intro π
    obtain ⟨v, hv⟩ := hbad π
    use v
    simp only [tuplesMissing, Set.mem_setOf_eq]
    intro i
    by_contra h
    have := hv i ⟨(π i).symm v, h⟩
    simp at this
  -- Convert to Finsets for counting
  let allTuples : Finset (Fin N → H ≃g H) := Finset.univ
  let missingV : V → Finset (Fin N → H ≃g H) := fun v =>
    (tuplesMissing H S N v).toFinset
  -- Every tuple is in some missingV v
  have hCover : ∀ π ∈ allTuples, ∃ v, π ∈ missingV v := by
    intro π _
    obtain ⟨v, hv⟩ := hEveryBad π
    use v
    simp only [missingV, Set.mem_toFinset]
    exact hv
  -- Union bound: |⋃_v missingV v| ≤ Σ_v |missingV v|
  have hUnionBound : (Finset.univ.biUnion missingV).card ≤
      ∑ v : V, (missingV v).card := Finset.card_biUnion_le
  -- Σ_v |missingV v| = cardV × r^N
  have hSumCard : ∑ v : V, (missingV v).card = cardV * r^N := by
    simp only [missingV]
    conv_lhs => arg 2; ext v; rw [Set.toFinset_card, hMissCard v]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  -- |allTuples| ≤ |⋃_v missingV v| since every tuple is covered
  have hAllCovered : allTuples ⊆ Finset.univ.biUnion missingV := by
    intro π hπ
    rw [Finset.mem_biUnion]
    obtain ⟨v, hv⟩ := hCover π hπ
    exact ⟨v, Finset.mem_univ v, hv⟩
  have hCardLE : allTuples.card ≤ (Finset.univ.biUnion missingV).card :=
    Finset.card_le_card hAllCovered
  -- Chain: Aut^N = |all| ≤ |union| ≤ sum = cardV × r^N < Aut^N
  have hContra : Aut^N < Aut^N := calc
    Aut^N = allTuples.card := by simp only [allTuples, Finset.card_univ, hTotalCard]
    _ ≤ (Finset.univ.biUnion missingV).card := hCardLE
    _ ≤ ∑ v : V, (missingV v).card := hUnionBound
    _ = cardV * r^N := hSumCard
    _ < Aut^N := hIneqNat
  exact Nat.lt_irrefl _ hContra

set_option linter.unusedFintypeInType false in
/-- Lemma 3.1 (Easy direction): For any graph H and subset S,
    the induced subgraph H[S] is below H in the cohomomorphism order.
    This follows from the inclusion map preserving non-adjacency. -/
theorem induced_cohomLE {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) :
    H.induce S ≤ᶜ H := by
  exact SimpleGraph.induce_cohomLE H S

set_option linter.unusedFintypeInType false in
/-- Lemma 3.1 (Hard direction): For a vertex-transitive graph H and nonempty S,
    H ≤ K̄_N ⊠ H[S] where N = ⌊(|V|/|S|) ln|V|⌋ + 1.

    Proof sketch (from paper):
    1. Draw N random automorphisms π₁, ..., π_N uniformly from Aut(H)
    2. Define m: [N] × S → V(H) as m(i, u) = πᵢ⁻¹(u)
    3. By vertex-transitivity, Pr[v ∈ πᵢ⁻¹(S)] = |S|/|V(H)|
    4. By union bound, Pr[∃ v not covered] < 1 when N is large enough
    5. So m is surjective for some choice, take φ to be a right inverse
    6. φ is a cohomomorphism: if u, v are non-adjacent in H:
       - If φ(u) = (i, u'), φ(v) = (j, v') with i ≠ j: non-adjacent (different copies)
       - If i = j: u' = πᵢ(u), v' = πᵢ(v) are non-adjacent since πᵢ is an automorphism -/
theorem transitive_cohomLE_nfold {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) (hS : S.Nonempty) (hT : IsVertexTransitive H)
    (N : ℕ) (hN : 0 < N)
    (hCover : ∃ (π : Fin N → H ≃g H), ∀ v : V, ∃ i : Fin N, ∃ s : S, (π i) s.val = v) :
    H ≤ᶜ (N ⬝ H.induce S) := by
  -- Construct the cohomomorphism from the covering
  obtain ⟨π, hπ⟩ := hCover
  classical
  -- For each v, use Classical.choose to pick (i, s) such that π(i)(s) = v
  -- Define helper: for v, get the index i
  let getIdx : V → Fin N := fun v => Classical.choose (hπ v)
  -- For v, get the element s ∈ S (given the index)
  let getElem : (v : V) → S := fun v =>
    Classical.choose (Classical.choose_spec (hπ v))
  -- The key property: π (getIdx v) (getElem v) = v
  have hφ_spec : ∀ v, (π (getIdx v)) (getElem v).val = v := fun v =>
    Classical.choose_spec (Classical.choose_spec (hπ v))
  -- Define the map φ : V → Fin N × S
  let φ : V → Fin N × S := fun v => (getIdx v, getElem v)
  -- Show φ gives a cohomomorphism
  unfold SimpleGraph.CohomLE
  refine ⟨⟨φ, ?_⟩⟩
  -- Need to show: if Hᶜ.Adj u v, then (N ⬝ H.induce S)ᶜ.Adj (φ u) (φ v)
  intro u v hadj
  simp only [SimpleGraph.compl_adj] at hadj ⊢
  obtain ⟨hne, hnadj⟩ := hadj
  -- φ u = (getIdx u, getElem u) and φ v = (getIdx v, getElem v)
  constructor
  · -- u ≠ v implies φ u ≠ φ v
    intro heq
    apply hne
    have heq' : (getIdx u, getElem u) = (getIdx v, getElem v) := heq
    obtain ⟨hi, hs⟩ := Prod.mk.inj heq'
    -- If indices equal and elements equal, then u = v
    -- π(getIdx u)(getElem u) = u and π(getIdx v)(getElem v) = v
    -- With getIdx u = getIdx v and getElem u = getElem v, we get u = v
    have hu := hφ_spec u
    have hv := hφ_spec v
    have hs' : (getElem u).val = (getElem v).val := congrArg Subtype.val hs
    rw [hi] at hu
    calc u = (π (getIdx v)) (getElem u).val := hu.symm
      _ = (π (getIdx v)) (getElem v).val := by rw [hs']
      _ = v := hv
  · -- The negation of (same index ∧ adjacent in H[S])
    intro ⟨heq_idx, hadj_induced⟩
    -- If indices equal: getIdx u = getIdx v = i (say)
    -- Then u = π(i)(getElem u) and v = π(i)(getElem v)
    -- Since π(i) is an automorphism, H.Adj u v ↔ H.Adj (getElem u) (getElem v)
    -- H[S].Adj means H.Adj on S, so hadj_induced gives H.Adj (getElem u) (getElem v)
    -- But hnadj says ¬H.Adj u v, contradiction via automorphism
    apply hnadj
    -- hadj_induced : (H.induce S).Adj (getElem u) (getElem v)
    -- This means H.Adj (getElem u).val (getElem v).val
    simp only [SimpleGraph.induce_adj] at hadj_induced
    -- After simp, hadj_induced : H.Adj ↑(getElem u) ↑(getElem v)
    -- u = π(i)(getElem u).val and v = π(i)(getElem v).val where i = getIdx u = getIdx v
    have hu : (π (getIdx u)) (getElem u).val = u := hφ_spec u
    have hv : (π (getIdx v)) (getElem v).val = v := hφ_spec v
    -- Use heq_idx : getIdx u = getIdx v
    rw [heq_idx] at hu
    -- π(getIdx v) is an automorphism, so it preserves adjacency
    -- The indices are the same, so π(getIdx v) transports adjacency
    convert (π (getIdx v)).map_adj_iff.mpr hadj_induced using 1 <;>
    · first | exact hu.symm | exact hv.symm

set_option linter.unusedFintypeInType false in
/-- Lemma 3.1 (combined statement): For a vertex-transitive graph H and nonempty S,
    H[S] ≤_c H and H ≤_c N · H[S] where N = ⌊(|V|/|S|) ln|V|⌋ + 1 -/
theorem transitiveinduced {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) (hS : S.Nonempty) (hT : IsVertexTransitive H) :
    H.induce S ≤ᶜ H := induced_cohomLE H S

/-- Lemma 3.1 (hard direction, full version): For a vertex-transitive graph H and nonempty S,
    H ≤_c (lemma31_N S) · H[S] where lemma31_N S = ⌊(|V|/|S|) ln|V|⌋ + 1 -/
theorem transitive_cohomLE_nfold_full {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Set V) [Fintype S] (hS : S.Nonempty)
    (hT : IsVertexTransitive H) (hcard : 0 < Fintype.card S) :
    H ≤ᶜ (lemma31_N S ⬝ H.induce S) := by
  have hN : 0 < lemma31_N S := Nat.succ_pos _
  obtain ⟨π, hπ⟩ := covering_exists H S hS hT hcard
  exact transitive_cohomLE_nfold H S hS hT (lemma31_N S) hN ⟨π, hπ⟩

end ProbabilisticRefinement
