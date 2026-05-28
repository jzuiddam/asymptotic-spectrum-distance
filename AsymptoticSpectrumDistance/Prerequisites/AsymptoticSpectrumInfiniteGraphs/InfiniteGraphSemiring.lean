/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphOperations

/-!
# Infinite Graph Semiring Structure

This file defines the commutative semiring structure on infinite graph isomorphism classes,
mirroring `GraphSemiring.lean` for finite graphs.

## Main Definitions

* `InfiniteGraphIso G H` - Graph isomorphism between infinite graphs G and H
* `InfiniteGraphClass` - Quotient type of infinite graphs by isomorphism
* `CommSemiring InfiniteGraphClass` - The semiring with + = disjoint union, × = strong product

## Operations

* **Addition**: Disjoint union G ⊔ H
* **Multiplication**: Strong product G ⊠ H
* **Zero**: Empty graph E₀ (no vertices)
* **One**: Single vertex graph E₁

## Natural Numbers

The natural number n is represented by E_n (edgeless graph on n vertices).

## References

* Strassen (1988), The asymptotic spectrum of tensors
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

/-! ### Infinite Graph Isomorphism -/

/-- Two infinite graphs G and H are isomorphic if there's a graph isomorphism between them. -/
def InfiniteGraphIso (G H : InfiniteGraph) : Prop :=
  Nonempty (G.graph ≃g H.graph)

theorem InfiniteGraphIso.refl (G : InfiniteGraph) : InfiniteGraphIso G G :=
  ⟨RelIso.refl _⟩

theorem InfiniteGraphIso.symm {G H : InfiniteGraph} (h : InfiniteGraphIso G H) :
    InfiniteGraphIso H G := by
  obtain ⟨φ⟩ := h; exact ⟨φ.symm⟩

theorem InfiniteGraphIso.trans {G H K : InfiniteGraph}
    (hGH : InfiniteGraphIso G H) (hHK : InfiniteGraphIso H K) : InfiniteGraphIso G K := by
  obtain ⟨φ⟩ := hGH; obtain ⟨ψ⟩ := hHK; exact ⟨φ.trans ψ⟩

theorem infiniteGraphIso_equivalence : Equivalence InfiniteGraphIso :=
  ⟨InfiniteGraphIso.refl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

instance infiniteGraphSetoid : Setoid InfiniteGraph :=
  ⟨InfiniteGraphIso, infiniteGraphIso_equivalence⟩

/-- The type of infinite graph isomorphism classes. -/
abbrev InfiniteGraphClass : Type _ := Quotient infiniteGraphSetoid

namespace InfiniteGraphClass

/-- Lift an infinite graph to its isomorphism class -/
def mk (G : InfiniteGraph) : InfiniteGraphClass := Quotient.mk' G

/-- The empty graph E₀ -/
def empty : InfiniteGraphClass := mk (InfiniteGraph.edgeless 0)

/-- The single vertex graph E₁ -/
def single : InfiniteGraphClass := mk (InfiniteGraph.edgeless 1)

/-! ### Operations respecting isomorphism -/

/-- Disjoint union respects isomorphism -/
theorem disjointUnion_congr {G G' H H' : InfiniteGraph}
    (hGG' : InfiniteGraphIso G G') (hHH' : InfiniteGraphIso H H') :
    InfiniteGraphIso (G ⊔∞ H) (G' ⊔∞ H') := by
  obtain ⟨φ⟩ := hGG'; obtain ⟨ψ⟩ := hHH'
  refine ⟨⟨⟨Sum.map φ ψ, Sum.map φ.symm ψ.symm, ?_, ?_⟩, ?_⟩⟩
  · intro x; match x with
    | .inl a => simp only [Sum.map_inl]; exact congrArg Sum.inl (φ.symm_apply_apply a)
    | .inr b => simp only [Sum.map_inr]; exact congrArg Sum.inr (ψ.symm_apply_apply b)
  · intro x; match x with
    | .inl a => simp only [Sum.map_inl]; exact congrArg Sum.inl (φ.apply_symm_apply a)
    | .inr b => simp only [Sum.map_inr]; exact congrArg Sum.inr (ψ.apply_symm_apply b)
  · intro x y
    simp only [InfiniteGraph.disjointUnion, disjUnionSimple]
    match x, y with
    | .inl a, .inl b => simp only [disjUnionSimple]; exact φ.map_rel_iff
    | .inr a, .inr b => simp only [disjUnionSimple]; exact ψ.map_rel_iff
    | .inl _, .inr _ => simp only [disjUnionSimple]; exact Iff.rfl
    | .inr _, .inl _ => simp only [disjUnionSimple]; exact Iff.rfl

/-- Strong product respects isomorphism -/
theorem strongProduct_congr {G G' H H' : InfiniteGraph}
    (hGG' : InfiniteGraphIso G G') (hHH' : InfiniteGraphIso H H') :
    InfiniteGraphIso (G ⊠∞ H) (G' ⊠∞ H') := by
  obtain ⟨φ⟩ := hGG'; obtain ⟨ψ⟩ := hHH'
  refine ⟨⟨⟨Prod.map φ ψ, Prod.map φ.symm ψ.symm, ?_, ?_⟩, ?_⟩⟩
  · intro ⟨a, b⟩
    simp only [Prod.map_apply]
    exact Prod.ext (φ.symm_apply_apply a) (ψ.symm_apply_apply b)
  · intro ⟨a, b⟩
    simp only [Prod.map_apply]
    exact Prod.ext (φ.apply_symm_apply a) (ψ.apply_symm_apply b)
  · intro ⟨a, x⟩ ⟨b, y⟩
    simp only [InfiniteGraph.strongProduct, ShannonCapacity.strongProduct]
    constructor
    · intro ⟨hne, h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · intro heq; apply hne
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
      · intro heq; apply hne
        have := Prod.mk.inj heq
        exact Prod.ext (φ.injective this.1) (ψ.injective this.2)
      · cases h1 with
        | inl heq => exact Or.inl (congrArg φ heq)
        | inr hadj => exact Or.inr (φ.map_rel_iff.mpr hadj)
      · cases h2 with
        | inl heq => exact Or.inl (congrArg ψ heq)
        | inr hadj => exact Or.inr (ψ.map_rel_iff.mpr hadj)

/-- Addition on InfiniteGraphClass (disjoint union) -/
def add : InfiniteGraphClass → InfiniteGraphClass → InfiniteGraphClass :=
  Quotient.lift₂ (fun G H => mk (G ⊔∞ H))
    (fun _ _ _ _ hGG' hHH' => Quotient.sound (disjointUnion_congr hGG' hHH'))

/-- Multiplication on InfiniteGraphClass (strong product) -/
def mul : InfiniteGraphClass → InfiniteGraphClass → InfiniteGraphClass :=
  Quotient.lift₂ (fun G H => mk (G ⊠∞ H))
    (fun _ _ _ _ hGG' hHH' => Quotient.sound (strongProduct_congr hGG' hHH'))

/-! ### Semiring Laws -/

theorem disjointUnion_assoc (G H K : InfiniteGraph) :
    InfiniteGraphIso ((G ⊔∞ H) ⊔∞ K) (G ⊔∞ (H ⊔∞ K)) := by
  refine ⟨⟨Equiv.sumAssoc G.V H.V K.V, ?_⟩⟩
  intro x y
  simp only [InfiniteGraph.disjointUnion, disjUnionSimple]
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

theorem disjointUnion_comm (G H : InfiniteGraph) :
    InfiniteGraphIso (G ⊔∞ H) (H ⊔∞ G) := by
  refine ⟨⟨Equiv.sumComm G.V H.V, ?_⟩⟩
  intro x y
  simp only [InfiniteGraph.disjointUnion, disjUnionSimple, Equiv.sumComm_apply]
  match x, y with
  | .inl a, .inl b => exact Iff.rfl
  | .inr a, .inr b => exact Iff.rfl
  | .inl _, .inr _ => exact Iff.rfl
  | .inr _, .inl _ => exact Iff.rfl

theorem disjointUnion_empty_left (G : InfiniteGraph) :
    InfiniteGraphIso (InfiniteGraph.edgeless 0 ⊔∞ G) G := by
  let e : Fin 0 ⊕ G.V ≃ G.V := Equiv.emptySum (Fin 0) G.V
  refine ⟨⟨e, ?_⟩⟩
  intro x y
  match x, y with
  | .inr a, .inr b =>
    simp only [InfiniteGraph.disjointUnion, disjUnionSimple]
    exact Iff.rfl

theorem strongProduct_assoc (G H K : InfiniteGraph) :
    InfiniteGraphIso ((G ⊠∞ H) ⊠∞ K) (G ⊠∞ (H ⊠∞ K)) := by
  refine ⟨⟨Equiv.prodAssoc G.V H.V K.V, ?_⟩⟩
  intro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  show ((G ⊠∞ (H ⊠∞ K)).graph.Adj (a, (b, c)) (a', (b', c')))
       ↔ (((G ⊠∞ H) ⊠∞ K).graph.Adj ((a, b), c) ((a', b'), c'))
  simp only [InfiniteGraph.strongProduct, ShannonCapacity.strongProduct, ne_eq, Prod.mk.injEq]
  tauto

theorem strongProduct_comm (G H : InfiniteGraph) :
    InfiniteGraphIso (G ⊠∞ H) (H ⊠∞ G) := by
  refine ⟨⟨Equiv.prodComm _ _, ?_⟩⟩
  intro ⟨a, b⟩ ⟨c, d⟩
  show ((H ⊠∞ G).graph.Adj (b, a) (d, c)) ↔ ((G ⊠∞ H).graph.Adj (a, b) (c, d))
  simp only [InfiniteGraph.strongProduct, ShannonCapacity.strongProduct, ne_eq, Prod.mk.injEq]
  constructor
  · intro ⟨hne, h1, h2⟩
    exact ⟨fun ⟨hbd, hac⟩ => hne ⟨hac, hbd⟩, h2, h1⟩
  · intro ⟨hne, h1, h2⟩
    exact ⟨fun ⟨hac, hbd⟩ => hne ⟨hbd, hac⟩, h2, h1⟩

theorem strongProduct_single_left (G : InfiniteGraph) :
    InfiniteGraphIso (InfiniteGraph.edgeless 1 ⊠∞ G) G := by
  let e : Fin 1 × G.V ≃ G.V :=
    { toFun := fun ⟨_, v⟩ => v
      invFun := fun v => ⟨0, v⟩
      left_inv := fun ⟨i, v⟩ => by simp only [Prod.mk.injEq, and_true]; exact (Fin.eq_zero i).symm
      right_inv := fun v => rfl }
  refine ⟨⟨e, ?_⟩⟩
  intro ⟨i, a⟩ ⟨j, b⟩
  change G.graph.Adj a b ↔ (InfiniteGraph.edgeless 1 ⊠∞ G).graph.Adj (i, a) (j, b)
  simp only [InfiniteGraph.strongProduct, ShannonCapacity.strongProduct, InfiniteGraph.edgeless,
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

theorem strongProduct_disjointUnion_left (G H K : InfiniteGraph) :
    InfiniteGraphIso (G ⊠∞ (H ⊔∞ K)) ((G ⊠∞ H) ⊔∞ (G ⊠∞ K)) := by
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
  intro x y
  obtain ⟨g, s⟩ := x; obtain ⟨g', s'⟩ := y
  simp only [InfiniteGraph.strongProduct, ShannonCapacity.strongProduct, InfiniteGraph.disjointUnion,
             disjUnionSimple]
  rcases s with h | k <;> rcases s' with h' | k'
  · simp only [e, ne_eq, Prod.mk.injEq, Sum.inl.injEq]
  · simp only [e, ne_eq, Prod.mk.injEq]
    constructor
    · intro hf; exact hf.elim
    · intro ⟨_, _, h⟩
      rcases h with heq | hf
      · cases heq
      · exact hf.elim
  · simp only [e, ne_eq, Prod.mk.injEq]
    constructor
    · intro hf; exact hf.elim
    · intro ⟨_, _, h⟩
      rcases h with heq | hf
      · cases heq
      · exact hf.elim
  · simp only [e, ne_eq, Prod.mk.injEq, Sum.inr.injEq]

theorem strongProduct_empty_left (G : InfiniteGraph) :
    InfiniteGraphIso (InfiniteGraph.edgeless 0 ⊠∞ G) (InfiniteGraph.edgeless 0) := by
  let e : Fin 0 × G.V ≃ Fin 0 :=
    { toFun := fun ⟨i, _⟩ => i.elim0
      invFun := fun i => i.elim0
      left_inv := fun ⟨i, _⟩ => i.elim0
      right_inv := fun i => i.elim0 }
  refine ⟨⟨e, ?_⟩⟩
  intro ⟨i, _⟩ _; exact i.elim0

/-! ### CommSemiring Instance -/

instance : Zero InfiniteGraphClass := ⟨empty⟩
instance : One InfiniteGraphClass := ⟨single⟩
instance : Add InfiniteGraphClass := ⟨add⟩
instance : Mul InfiniteGraphClass := ⟨mul⟩

theorem add_def (G H : InfiniteGraph) : mk G + mk H = mk (G ⊔∞ H) := rfl
theorem mul_def (G H : InfiniteGraph) : mk G * mk H = mk (G ⊠∞ H) := rfl
theorem zero_def : (0 : InfiniteGraphClass) = mk (InfiniteGraph.edgeless 0) := rfl
theorem one_def : (1 : InfiniteGraphClass) = mk (InfiniteGraph.edgeless 1) := rfl

instance : AddCommMonoid InfiniteGraphClass where
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

instance : Monoid InfiniteGraphClass where
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

instance : CommSemiring InfiniteGraphClass where
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
    have h1 := strongProduct_comm (G ⊔∞ H) K
    have h2 := strongProduct_disjointUnion_left K G H
    have h3 : InfiniteGraphIso ((K ⊠∞ G) ⊔∞ (K ⊠∞ H)) ((G ⊠∞ K) ⊔∞ (H ⊠∞ K)) :=
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
    InfiniteGraphIso (InfiniteGraph.edgeless n ⊔∞ InfiniteGraph.edgeless m)
                     (InfiniteGraph.edgeless (n + m)) := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  refine ⟨⟨⟨e, e.symm, e.symm_apply_apply, e.apply_symm_apply⟩, ?_⟩⟩
  intro x y
  simp only [InfiniteGraph.disjointUnion, InfiniteGraph.edgeless, disjUnionSimple]
  match x, y with
  | .inl _, .inl _ => simp
  | .inr _, .inr _ => simp
  | .inl _, .inr _ => simp
  | .inr _, .inl _ => simp

/-- E_n (edgeless graph on n vertices) represents the natural number n -/
theorem natCast_eq_edgeless (n : ℕ) :
    (n : InfiniteGraphClass) = mk (InfiniteGraph.edgeless n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.cast_succ]
    rw [ih, one_def, add_def]
    exact Quotient.sound (edgeless_disjointUnion_iso n 1)

end InfiniteGraphClass

end AsymptoticSpectrumInfiniteGraphs
