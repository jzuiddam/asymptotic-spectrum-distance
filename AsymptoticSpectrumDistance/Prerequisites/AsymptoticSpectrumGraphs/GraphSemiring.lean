/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum

/-!
# Graph Semiring Structure

This file defines the commutative semiring structure on graph isomorphism classes.

## Main Definitions

* `GraphIso G H` - Graph isomorphism between G and H
* `GraphClass` - Quotient type of graphs by isomorphism
* `CommSemiring GraphClass` - The graph semiring with + = disjoint union, × = strong product

## Operations

* **Addition**: Disjoint union G ⊔ H
* **Multiplication**: Strong product G ⊠ H
* **Zero**: Empty graph E₀ (no vertices)
* **One**: Single vertex graph E₁ = K₁

## Natural Numbers

The natural number n is represented by E_n (edgeless graph on n vertices).
This is consistent with fraction graph notation E_{p/q}.

## References

* Strassen (1988), The asymptotic spectrum of tensors
-/

namespace AsymptoticSpectrumGraphs

open SimpleGraph

/-! ### Graph Isomorphism -/

/-- Two graphs G and H are isomorphic if there's a graph isomorphism between them. -/
def GraphIso (G H : Graph) : Prop :=
  Nonempty (G.graph ≃g H.graph)

theorem GraphIso.refl (G : Graph) : GraphIso G G :=
  ⟨RelIso.refl _⟩

theorem GraphIso.symm {G H : Graph} (h : GraphIso G H) : GraphIso H G := by
  obtain ⟨φ⟩ := h
  exact ⟨φ.symm⟩

theorem GraphIso.trans {G H K : Graph} (hGH : GraphIso G H) (hHK : GraphIso H K) :
    GraphIso G K := by
  obtain ⟨φ⟩ := hGH
  obtain ⟨ψ⟩ := hHK
  exact ⟨φ.trans ψ⟩

/-- GraphIso is an equivalence relation -/
theorem graphIso_equivalence : Equivalence GraphIso :=
  ⟨GraphIso.refl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

instance graphSetoid : Setoid Graph :=
  ⟨GraphIso, graphIso_equivalence⟩

/-- The type of graph isomorphism classes. -/
abbrev GraphClass : Type _ := Quotient graphSetoid

namespace GraphClass

/-- Lift a graph to its isomorphism class -/
def mk (G : Graph) : GraphClass := Quotient.mk' G

/-- The empty graph E₀ -/
def empty : GraphClass := mk (EdgelessGraph 0)

/-- The single vertex graph E₁ = K₁ -/
def single : GraphClass := mk (EdgelessGraph 1)

/-! ### Operations respecting isomorphism -/

/-- Disjoint union respects isomorphism -/
theorem disjointUnion_congr {G G' H H' : Graph}
    (hGG' : GraphIso G G') (hHH' : GraphIso H H') :
    GraphIso (G ⊔ᴳ H) (G' ⊔ᴳ H') := by
  obtain ⟨φ⟩ := hGG'
  obtain ⟨ψ⟩ := hHH'
  refine ⟨⟨⟨Sum.map φ ψ, Sum.map φ.symm ψ.symm, ?_, ?_⟩, ?_⟩⟩
  · intro x
    match x with
    | .inl a => simp only [Sum.map_inl]; exact congrArg Sum.inl (φ.symm_apply_apply a)
    | .inr b => simp only [Sum.map_inr]; exact congrArg Sum.inr (ψ.symm_apply_apply b)
  · intro x
    match x with
    | .inl a => simp only [Sum.map_inl]; exact congrArg Sum.inl (φ.apply_symm_apply a)
    | .inr b => simp only [Sum.map_inr]; exact congrArg Sum.inr (ψ.apply_symm_apply b)
  · intro x y
    simp only [Graph.disjointUnion]
    match x, y with
    | .inl a, .inl b => simp only [disjUnionSimple]; exact φ.map_rel_iff
    | .inr a, .inr b => simp only [disjUnionSimple]; exact ψ.map_rel_iff
    | .inl _, .inr _ => simp only [disjUnionSimple]; exact Iff.rfl
    | .inr _, .inl _ => simp only [disjUnionSimple]; exact Iff.rfl

/-- Strong product respects isomorphism -/
theorem strongProduct_congr {G G' H H' : Graph}
    (hGG' : GraphIso G G') (hHH' : GraphIso H H') :
    GraphIso (G ⊠ H) (G' ⊠ H') := by
  obtain ⟨φ⟩ := hGG'
  obtain ⟨ψ⟩ := hHH'
  refine ⟨⟨⟨Prod.map φ ψ, Prod.map φ.symm ψ.symm, ?_, ?_⟩, ?_⟩⟩
  · intro ⟨a, b⟩
    simp only [Prod.map_apply]
    exact Prod.ext (φ.symm_apply_apply a) (ψ.symm_apply_apply b)
  · intro ⟨a, b⟩
    simp only [Prod.map_apply]
    exact Prod.ext (φ.apply_symm_apply a) (ψ.apply_symm_apply b)
  · intro ⟨a, x⟩ ⟨b, y⟩
    simp only [Graph.strongProduct, ShannonCapacity.strongProduct]
    constructor
    · intro ⟨hne, h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        apply hne
        have := Prod.mk.inj heq
        exact Prod.ext (congrArg φ this.1) (congrArg ψ this.2)
      · cases h1 with
        | inl heq => exact Or.inl (φ.injective heq)
        | inr hadj => exact Or.inr (φ.map_rel_iff.mp hadj)
      · cases h2 with
        | inl heq => exact Or.inl (ψ.injective heq)
        | inr hadj => exact Or.inr (ψ.map_rel_iff.mp hadj)
    · intro ⟨hne, h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        apply hne
        have := Prod.mk.inj heq
        exact Prod.ext (φ.injective this.1) (ψ.injective this.2)
      · cases h1 with
        | inl heq => exact Or.inl (congrArg φ heq)
        | inr hadj => exact Or.inr (φ.map_rel_iff.mpr hadj)
      · cases h2 with
        | inl heq => exact Or.inl (congrArg ψ heq)
        | inr hadj => exact Or.inr (ψ.map_rel_iff.mpr hadj)

/-- Addition on GraphClass (disjoint union) -/
def add : GraphClass → GraphClass → GraphClass :=
  Quotient.lift₂ (fun G H => mk (G ⊔ᴳ H))
    (fun _ _ _ _ hGG' hHH' => Quotient.sound (disjointUnion_congr hGG' hHH'))

/-- Multiplication on GraphClass (strong product) -/
def mul : GraphClass → GraphClass → GraphClass :=
  Quotient.lift₂ (fun G H => mk (G ⊠ H))
    (fun _ _ _ _ hGG' hHH' => Quotient.sound (strongProduct_congr hGG' hHH'))

/-! ### Semiring Laws -/

-- These graph isomorphism lemmas establish the semiring structure.
-- The proofs construct explicit equivalences and verify edge preservation.

-- Associativity of disjoint union: (G ⊔ H) ⊔ K ≅ G ⊔ (H ⊔ K)
theorem disjointUnion_assoc (G H K : Graph) :
    GraphIso ((G ⊔ᴳ H) ⊔ᴳ K) (G ⊔ᴳ (H ⊔ᴳ K)) := by
  refine ⟨⟨Equiv.sumAssoc G.V H.V K.V, ?_⟩⟩
  intro x y
  simp only [Graph.disjointUnion, disjUnionSimple]
  match x, y with
  | .inl (.inl a), .inl (.inl b) => simp only [Equiv.sumAssoc]; exact Iff.rfl
  | .inl (.inr a), .inl (.inr b) => simp only [Equiv.sumAssoc]; exact Iff.rfl
  | .inr a, .inr b => simp only [Equiv.sumAssoc]; exact Iff.rfl
  | .inl (.inl _), .inl (.inr _) => simp only [Equiv.sumAssoc]; exact Iff.rfl
  | .inl (.inr _), .inl (.inl _) => simp only [Equiv.sumAssoc]; exact Iff.rfl
  | .inl (.inl _), .inr _ => simp only [Equiv.sumAssoc]; exact Iff.rfl
  | .inl (.inr _), .inr _ => simp only [Equiv.sumAssoc]; exact Iff.rfl
  | .inr _, .inl (.inl _) => simp only [Equiv.sumAssoc]; exact Iff.rfl
  | .inr _, .inl (.inr _) => simp only [Equiv.sumAssoc]; exact Iff.rfl

-- Commutativity of disjoint union: G ⊔ H ≅ H ⊔ G
theorem disjointUnion_comm (G H : Graph) :
    GraphIso (G ⊔ᴳ H) (H ⊔ᴳ G) := by
  refine ⟨⟨Equiv.sumComm G.V H.V, ?_⟩⟩
  intro x y
  simp only [Graph.disjointUnion, disjUnionSimple, Equiv.sumComm_apply]
  match x, y with
  | .inl a, .inl b => exact Iff.rfl
  | .inr a, .inr b => exact Iff.rfl
  | .inl _, .inr _ => exact Iff.rfl
  | .inr _, .inl _ => exact Iff.rfl

-- Empty graph is identity for disjoint union: E₀ ⊔ G ≅ G
theorem disjointUnion_empty_left (G : Graph) :
    GraphIso (EdgelessGraph 0 ⊔ᴳ G) G := by
  let e : Fin 0 ⊕ G.V ≃ G.V := Equiv.emptySum (Fin 0) G.V
  refine ⟨⟨e, ?_⟩⟩
  intro x y
  match x, y with
  | .inr a, .inr b =>
    simp only [Graph.disjointUnion, disjUnionSimple]
    exact Iff.rfl

-- Associativity of strong product: (G ⊠ H) ⊠ K ≅ G ⊠ (H ⊠ K)
theorem strongProduct_assoc (G H K : Graph) :
    GraphIso ((G ⊠ H) ⊠ K) (G ⊠ (H ⊠ K)) := by
  refine ⟨⟨Equiv.prodAssoc G.V H.V K.V, ?_⟩⟩
  intro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  show ((G ⊠ (H ⊠ K)).graph.Adj (a, b, c) (a', b', c'))
       ↔ ((G ⊠ H ⊠ K).graph.Adj ((a, b), c) ((a', b'), c'))
  simp only [Graph.strongProduct, ShannonCapacity.strongProduct, ne_eq, Prod.mk.injEq]
  tauto

-- Commutativity of strong product: G ⊠ H ≅ H ⊠ G
theorem strongProduct_comm (G H : Graph) :
    GraphIso (G ⊠ H) (H ⊠ G) := by
  refine ⟨⟨Equiv.prodComm _ _, ?_⟩⟩
  intro ⟨a, b⟩ ⟨c, d⟩
  show ((H ⊠ G).graph.Adj (b, a) (d, c)) ↔ ((G ⊠ H).graph.Adj (a, b) (c, d))
  simp only [Graph.strongProduct, ShannonCapacity.strongProduct, ne_eq, Prod.mk.injEq]
  constructor
  · intro ⟨hne, h1, h2⟩
    exact ⟨fun ⟨hbd, hac⟩ => hne ⟨hac, hbd⟩, h2, h1⟩
  · intro ⟨hne, h1, h2⟩
    exact ⟨fun ⟨hac, hbd⟩ => hne ⟨hbd, hac⟩, h2, h1⟩

-- Single vertex is identity for strong product: E₁ ⊠ G ≅ G
theorem strongProduct_single_left (G : Graph) :
    GraphIso (EdgelessGraph 1 ⊠ G) G := by
  let e : Fin 1 × G.V ≃ G.V :=
    { toFun := fun ⟨_, v⟩ => v
      invFun := fun v => ⟨0, v⟩
      left_inv := fun ⟨i, v⟩ => by simp only [Prod.mk.injEq, and_true]; exact (Fin.eq_zero i).symm
      right_inv := fun v => rfl }
  refine ⟨⟨e, ?_⟩⟩
  intro ⟨i, a⟩ ⟨j, b⟩
  change G.graph.Adj a b ↔ (EdgelessGraph 1 ⊠ G).graph.Adj (i, a) (j, b)
  simp only [Graph.strongProduct, ShannonCapacity.strongProduct, EdgelessGraph, edgelessGraph,
             ne_eq, Prod.mk.injEq]
  have hi : i = ⟨0, by decide⟩ := Fin.eq_zero i
  have hj : j = ⟨0, by decide⟩ := Fin.eq_zero j
  subst hi hj
  simp only [true_or, true_and]
  constructor
  · intro hadj
    exact ⟨G.graph.ne_of_adj hadj, Or.inr hadj⟩
  · intro ⟨hne, h2⟩
    rcases h2 with h2_eq | h2_adj
    · exact (hne h2_eq).elim
    · exact h2_adj

-- Distributivity: G ⊠ (H ⊔ K) ≅ (G ⊠ H) ⊔ (G ⊠ K)
theorem strongProduct_disjointUnion_left (G H K : Graph) :
    GraphIso (G ⊠ (H ⊔ᴳ K)) ((G ⊠ H) ⊔ᴳ (G ⊠ K)) := by
  -- Build explicit equivalence
  let e : G.V × (H.V ⊕ K.V) ≃ (G.V × H.V) ⊕ (G.V × K.V) :=
    { toFun := fun ⟨g, s⟩ => match s with
        | .inl h => .inl (g, h)
        | .inr k => .inr (g, k)
      invFun := fun x => match x with
        | .inl (g, h) => (g, .inl h)
        | .inr (g, k) => (g, .inr k)
      left_inv := fun ⟨g, s⟩ => by cases s <;> rfl
      right_inv := fun x => by cases x <;> rfl }
  refine ⟨⟨e, ?_⟩⟩
  -- Prove adjacency preservation
  intro x y
  obtain ⟨g, s⟩ := x
  obtain ⟨g', s'⟩ := y
  simp only [Graph.strongProduct, ShannonCapacity.strongProduct, Graph.disjointUnion,
             disjUnionSimple]
  -- Case split on the sum types
  rcases s with h | k <;> rcases s' with h' | k'
  · -- inl.inl: both in H (simp reduces match and proves automatically)
    simp only [e, ne_eq, Prod.mk.injEq, Sum.inl.injEq]
  · -- inl.inr: H vs K (different components, never adjacent)
    simp only [e, ne_eq, Prod.mk.injEq]
    constructor
    · intro hf; exact hf.elim
    · intro ⟨_, _, h⟩
      rcases h with heq | hf
      · cases heq
      · exact hf.elim
  · -- inr.inl: K vs H (different components, never adjacent)
    simp only [e, ne_eq, Prod.mk.injEq]
    constructor
    · intro hf; exact hf.elim
    · intro ⟨_, _, h⟩
      rcases h with heq | hf
      · cases heq
      · exact hf.elim
  · -- inr.inr: both in K (simp reduces match and proves automatically)
    simp only [e, ne_eq, Prod.mk.injEq, Sum.inr.injEq]

-- Zero annihilation: E₀ ⊠ G ≅ E₀
theorem strongProduct_empty_left (G : Graph) :
    GraphIso (EdgelessGraph 0 ⊠ G) (EdgelessGraph 0) := by
  let e : Fin 0 × G.V ≃ Fin 0 :=
    { toFun := fun ⟨i, _⟩ => i.elim0
      invFun := fun i => i.elim0
      left_inv := fun ⟨i, _⟩ => i.elim0
      right_inv := fun i => i.elim0 }
  refine ⟨⟨e, ?_⟩⟩
  intro ⟨i, _⟩ _
  exact i.elim0

/-! ### CommSemiring Instance -/

instance : Zero GraphClass := ⟨empty⟩
instance : One GraphClass := ⟨single⟩
instance : Add GraphClass := ⟨add⟩
instance : Mul GraphClass := ⟨mul⟩

theorem add_def (G H : Graph) : mk G + mk H = mk (G ⊔ᴳ H) := rfl
theorem mul_def (G H : Graph) : mk G * mk H = mk (G ⊠ H) := rfl
theorem zero_def : (0 : GraphClass) = mk (EdgelessGraph 0) := rfl
theorem one_def : (1 : GraphClass) = mk (EdgelessGraph 1) := rfl

instance : AddCommMonoid GraphClass where
  add_assoc := by
    intro a b c
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨K, rfl⟩ := Quotient.exists_rep c
    exact Quotient.sound (disjointUnion_assoc G H K)
  zero_add := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    exact Quotient.sound (disjointUnion_empty_left G)
  add_zero := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    exact Quotient.sound ((disjointUnion_comm _ _).trans (disjointUnion_empty_left G))
  add_comm := by
    intro a b
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    exact Quotient.sound (disjointUnion_comm G H)
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

instance : Monoid GraphClass where
  mul_assoc := by
    intro a b c
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨K, rfl⟩ := Quotient.exists_rep c
    exact Quotient.sound (strongProduct_assoc G H K)
  one_mul := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    exact Quotient.sound (strongProduct_single_left G)
  mul_one := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    exact Quotient.sound ((strongProduct_comm _ _).trans (strongProduct_single_left G))
  npow := npowRec
  npow_zero := fun _ => rfl
  npow_succ := fun _ _ => rfl

instance : CommSemiring GraphClass where
  mul_comm := by
    intro a b
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    exact Quotient.sound (strongProduct_comm G H)
  left_distrib := by
    intro a b c
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨K, rfl⟩ := Quotient.exists_rep c
    exact Quotient.sound (strongProduct_disjointUnion_left G H K)
  right_distrib := by
    intro a b c
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    obtain ⟨H, rfl⟩ := Quotient.exists_rep b
    obtain ⟨K, rfl⟩ := Quotient.exists_rep c
    have h1 := strongProduct_comm (G ⊔ᴳ H) K
    have h2 := strongProduct_disjointUnion_left K G H
    have h3 : GraphIso ((K ⊠ G) ⊔ᴳ (K ⊠ H)) ((G ⊠ K) ⊔ᴳ (H ⊠ K)) :=
      disjointUnion_congr (strongProduct_comm K G) (strongProduct_comm K H)
    exact Quotient.sound (h1.trans (h2.trans h3))
  zero_mul := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    exact Quotient.sound (strongProduct_empty_left G)
  mul_zero := by
    intro a
    obtain ⟨G, rfl⟩ := Quotient.exists_rep a
    exact Quotient.sound ((strongProduct_comm G _).trans (strongProduct_empty_left G))

/-! ### Natural Number Embedding -/

/-- Disjoint union of edgeless graphs is edgeless on the sum. -/
theorem edgeless_disjointUnion_iso (n m : ℕ) :
    GraphIso (EdgelessGraph n ⊔ᴳ EdgelessGraph m) (EdgelessGraph (n + m)) := by
  -- Need to construct isomorphism Fin n ⊕ Fin m ≃ Fin (n + m)
  -- Use finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  refine ⟨⟨⟨e, e.symm, e.symm_apply_apply, e.apply_symm_apply⟩, ?_⟩⟩
  -- Need to show adjacency is preserved (both graphs have no edges)
  intro x y
  simp only [Graph.disjointUnion, EdgelessGraph, edgelessGraph, disjUnionSimple]
  match x, y with
  | .inl _, .inl _ => simp
  | .inr _, .inr _ => simp
  | .inl _, .inr _ => simp
  | .inr _, .inl _ => simp

/-- E_n (edgeless graph on n vertices) represents the natural number n -/
theorem natCast_eq_edgeless (n : ℕ) : (n : GraphClass) = mk (EdgelessGraph n) := by
  induction n with
  | zero => rfl  -- 0 = mk (EdgelessGraph 0) by definition
  | succ n ih =>
    -- (n + 1 : GraphClass) = n + 1 = mk (EdgelessGraph n) + mk (EdgelessGraph 1)
    simp only [Nat.cast_succ]
    rw [ih, one_def]
    -- Now have: mk (EdgelessGraph n) + mk (EdgelessGraph 1) = mk (EdgelessGraph (n + 1))
    rw [add_def]
    -- Need: mk (EdgelessGraph n ⊔ᴳ EdgelessGraph 1) = mk (EdgelessGraph (n + 1))
    exact Quotient.sound (edgeless_disjointUnion_iso n 1)

end GraphClass

end AsymptoticSpectrumGraphs
