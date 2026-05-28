/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Iterated strong product over `Fin k`

Defines `bigStrongProduct` : a `Fin k`-indexed strong product of a family
of `SimpleGraph`s. Two distinct tuples `u, v : ∀ i, V i` are adjacent iff
at every coordinate `i` either `u i = v i` or `(G i).Adj (u i) (v i)`.

This is the natural generalization of the binary `strongProduct` and
underpins the unified `α_k` discontinuity formalism.

## Main definitions

* `bigStrongProduct G` : `SimpleGraph (∀ i, V i)`.

## Main results

* `bigStrongProduct_zero_iso` : `bigStrongProduct G ≃g ⊥` on `PUnit` for `k = 0`
  (single isolated vertex).
* `bigStrongProduct_succ_iso` : `bigStrongProduct G ≃g (G 0) ⊠ bigStrongProduct (G ∘ Fin.succ)`,
  the recursive characterization.
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.StrongProduct
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphOperations

open AsymptoticSpectrumGraphs

namespace ShannonCapacity

variable {k : ℕ} {V : Fin k → Type*}

/-- Iterated strong product of a `Fin k`-indexed family of `SimpleGraph`s.
    Vertices are tuples `u : ∀ i : Fin k, V i`. Two distinct tuples `u, v`
    are adjacent iff at every coordinate `i` either `u i = v i` or
    `(G i).Adj (u i) (v i)`. -/
def bigStrongProduct (G : ∀ i, SimpleGraph (V i)) : SimpleGraph (∀ i, V i) where
  Adj u v := u ≠ v ∧ ∀ i, u i = v i ∨ (G i).Adj (u i) (v i)
  symm := by
    rintro u v ⟨hne, h⟩
    refine ⟨Ne.symm hne, fun i => ?_⟩
    rcases h i with heq | hadj
    · exact Or.inl heq.symm
    · exact Or.inr hadj.symm
  loopless := ⟨fun _ ⟨hne, _⟩ => (hne rfl).elim⟩

/-- Bundled `Graph` version of `bigStrongProduct`: iterated strong product
    of a `Fin k`-indexed family of `Graph`s. -/
def Graph.bigStrongProduct {k : ℕ} (G : Fin k → AsymptoticSpectrumGraphs.Graph) :
    AsymptoticSpectrumGraphs.Graph where
  V := ∀ i, (G i).V
  graph := ShannonCapacity.bigStrongProduct (fun i => (G i).graph)

@[simp] theorem bigStrongProduct_adj
    {G : ∀ i, SimpleGraph (V i)} {u v : ∀ i, V i} :
    (bigStrongProduct G).Adj u v ↔
      u ≠ v ∧ ∀ i, u i = v i ∨ (G i).Adj (u i) (v i) :=
  Iff.rfl

/-! ## Recursive characterization

`bigStrongProduct` over `Fin (k+1)` is graph-isomorphic to the strong product
of `G 0` with `bigStrongProduct (G ∘ Fin.succ)`. This bridges to the binary
`strongProduct` so existing lemmas chain through. -/

/-- `Fin 0 → V` is a singleton type, so `bigStrongProduct G` over `Fin 0`
    has no edges (trivially: there's only one vertex). -/
def bigStrongProduct_zero_iso {V : Fin 0 → Type*}
    (G : ∀ i, SimpleGraph (V i)) :
    bigStrongProduct G ≃g (⊥ : SimpleGraph PUnit) where
  toEquiv := {
    toFun := fun _ => PUnit.unit
    invFun := fun _ i => Fin.elim0 i
    left_inv := fun u => funext fun i => Fin.elim0 i
    right_inv := fun _ => rfl
  }
  map_rel_iff' := by
    intro u v
    constructor
    · intro h; exact h.elim
    · rintro ⟨hne, _⟩
      apply hne
      funext i
      exact Fin.elim0 i

/-- For `k = k'+1`, `bigStrongProduct G ≃g (G 0) ⊠ bigStrongProduct (G ∘ Fin.succ)`,
    via `(u : ∀ i : Fin (k+1), V i) ↦ (u 0, fun i => u i.succ)`. -/
def bigStrongProduct_succ_iso {k : ℕ} {V : Fin (k + 1) → Type*}
    (G : ∀ i, SimpleGraph (V i)) :
    bigStrongProduct G ≃g
      strongProduct (G 0) (bigStrongProduct (fun i : Fin k => G i.succ)) where
  toEquiv := {
    toFun := fun u => (u 0, fun i => u i.succ)
    invFun := fun p => Fin.cases p.1 p.2
    left_inv := fun u => funext fun i => by
      cases i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    right_inv := fun ⟨a, b⟩ => by simp
  }
  map_rel_iff' := by
    intro u v
    constructor
    · -- (strongProduct ...).Adj (u 0, u-tail) (v 0, v-tail) → bigStrongProduct.Adj u v
      rintro ⟨hne_prod, h0, htail⟩
      refine ⟨?_, ?_⟩
      · intro heq
        apply hne_prod
        rw [heq]
      · intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ j =>
          rcases htail with h_eq | ⟨_, h_adj⟩
          · exact Or.inl (congrFun h_eq j)
          · exact h_adj j
    · -- bigStrongProduct.Adj u v → (strongProduct ...).Adj
      rintro ⟨hne, h⟩
      refine ⟨?_, h 0, ?_⟩
      · intro heq
        apply hne
        funext i
        cases i using Fin.cases with
        | zero => exact (Prod.mk.inj heq).1
        | succ j =>
          have htail : (fun i : Fin k => u i.succ) = (fun i : Fin k => v i.succ) :=
            (Prod.mk.inj heq).2
          exact congrFun htail j
      · by_cases htail : (fun i : Fin k => u i.succ) = (fun i : Fin k => v i.succ)
        · exact Or.inl htail
        · exact Or.inr ⟨htail, fun j => h j.succ⟩

/-! ## Lift inner-factor iso through outer strongProduct -/

/-- Lift an iso on the second factor through the strong product:
    `H ≃g H' → G ⊠ H ≃g G ⊠ H'`. -/
def strongProduct_right_iso {V W W' : Type*} (G : SimpleGraph V)
    {H : SimpleGraph W} {H' : SimpleGraph W'} (e : H ≃g H') :
    strongProduct G H ≃g strongProduct G H' where
  toEquiv := Equiv.prodCongr (Equiv.refl V) e.toEquiv
  map_rel_iff' := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    simp only [strongProduct, Equiv.prodCongr_apply, Equiv.refl_apply,
      Prod.map_apply, Prod.mk.injEq, ne_eq, RelIso.coe_fn_toEquiv]
    constructor
    · rintro ⟨hne, h1, h2⟩
      refine ⟨?_, h1, ?_⟩
      · intro heq
        apply hne
        exact ⟨heq.1, congrArg e heq.2⟩
      · cases h2 with
        | inl heq => exact Or.inl (e.injective heq)
        | inr hadj => exact Or.inr (e.map_rel_iff.mp hadj)
    · rintro ⟨hne, h1, h2⟩
      refine ⟨?_, h1, ?_⟩
      · intro heq
        apply hne
        exact ⟨heq.1, e.injective heq.2⟩
      · cases h2 with
        | inl heq => exact Or.inl (congrArg e heq)
        | inr hadj => exact Or.inr (e.map_rel_iff.mpr hadj)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Independence number is preserved under inner-factor iso. -/
theorem indepNum_strongProduct_right_iso {V W W' : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype W'] [DecidableEq W']
    (G : SimpleGraph V) {H : SimpleGraph W} {H' : SimpleGraph W'} (e : H ≃g H') :
    (strongProduct G H).indepNum = (strongProduct G H').indepNum :=
  SimpleGraph.independenceNumber_iso (strongProduct_right_iso G e)

/-! ## Strip a trivial right factor

`G ⊠ ⊥-PUnit ≃g G`: tensoring with the single-vertex empty graph is identity. -/

/-- `G ⊠ (⊥ : SimpleGraph PUnit) ≃g G` via `Equiv.prodPUnit`.

    `map_rel_iff'` direction: `G.Adj (e p) (e q) ↔ (strongProduct G ⊥).Adj p q`,
    where `e p = p.1` collapses the trivial second factor. -/
def strongProduct_botPUnit_right_iso {V : Type*} (G : SimpleGraph V) :
    strongProduct G (⊥ : SimpleGraph PUnit) ≃g G where
  toEquiv := Equiv.prodPUnit V
  map_rel_iff' := by
    rintro ⟨a, _⟩ ⟨b, _⟩
    constructor
    · -- G.Adj a b → (strongProduct G ⊥).Adj (a, _) (b, _)
      intro hadj
      refine ⟨?_, Or.inr hadj, Or.inl (Subsingleton.elim _ _)⟩
      intro heq
      exact G.irrefl ((Prod.mk.inj heq).1 ▸ hadj)
    · -- (strongProduct G ⊥).Adj (a, _) (b, _) → G.Adj a b
      rintro ⟨hne, h1, _⟩
      rcases h1 with heq | hadj
      · exact (hne (Prod.ext heq (Subsingleton.elim _ _))).elim
      · exact hadj

/-! ## Permutation invariance

Permuting the family `G : ∀ i, SimpleGraph (V i)` by `σ : Equiv.Perm (Fin k)`
yields a graph-isomorphic iterated strong product. The vertex bijection is
`Equiv.piCongrLeft V σ` (sending `u : ∀ b, V b` to `fun a => u (σ a)` via
`.symm`). -/

/-- `bigStrongProduct G ≃g bigStrongProduct (G ∘ σ)` for any
    `σ : Equiv.Perm (Fin k)`. -/
def bigStrongProduct_perm_iso {k : ℕ} {V : Fin k → Type*}
    (G : ∀ i, SimpleGraph (V i)) (σ : Equiv.Perm (Fin k)) :
    bigStrongProduct G ≃g bigStrongProduct (fun i => G (σ i)) where
  toEquiv := (Equiv.piCongrLeft V σ).symm
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨hne, h⟩
      refine ⟨fun heq => hne (congrArg _ heq), fun b => ?_⟩
      obtain ⟨a, rfl⟩ : ∃ a, σ a = b := σ.surjective b
      rcases h a with heq | hadj
      · left; simpa using heq
      · right; simpa using hadj
    · rintro ⟨hne, h⟩
      refine ⟨fun heq => hne ((Equiv.piCongrLeft V σ).symm.injective heq),
              fun a => ?_⟩
      rcases h (σ a) with heq | hadj
      · left; simpa using heq
      · right; simpa using hadj

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Independence number is invariant under permuting the family. -/
theorem indepNum_bigStrongProduct_perm {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, SimpleGraph (V i)) (σ : Equiv.Perm (Fin k)) :
    (bigStrongProduct G).indepNum =
      (bigStrongProduct (fun i => G (σ i))).indepNum :=
  SimpleGraph.independenceNumber_iso (bigStrongProduct_perm_iso G σ)

/-! ## Cohomomorphism monotonicity per factor -/

/-- Per-factor cohomomorphism lifts to a cohomomorphism on the whole
    iterated strong product. -/
theorem bigStrongProduct_cohom_mono {k : ℕ} {V V' : Fin k → Type*}
    {G : ∀ i, SimpleGraph (V i)} {G' : ∀ i, SimpleGraph (V' i)}
    (h : ∀ i, ∃ f : V i → V' i, IsCohom (G i) (G' i) f) :
    ∃ F : (∀ i, V i) → (∀ i, V' i),
      IsCohom (bigStrongProduct G) (bigStrongProduct G') F := by
  -- Build the per-coord function family.
  classical
  choose f hf using h
  refine ⟨fun u i => f i (u i), ?_⟩
  -- Show this is a cohom: ∀ u v, u ≠ v → ¬Adj u v → F u ≠ F v ∧ ¬ Adj (F u) (F v).
  intro u v huv hnadj
  simp only [bigStrongProduct_adj, not_and, not_forall, not_or] at hnadj
  -- hnadj : u = v ∨ ∃ i, u i ≠ v i ∧ ¬ G i.Adj (u i) (v i)
  -- huv : u ≠ v, so the first disjunct is excluded.
  rcases hnadj huv with ⟨i₀, hne_i₀, hnadj_i₀⟩
  -- Apply hf at index i₀: f i₀ (u i₀) ≠ f i₀ (v i₀) ∧ ¬ G' i₀.Adj.
  have ⟨hne_f, hnadj_f⟩ := hf i₀ (u i₀) (v i₀) hne_i₀ hnadj_i₀
  refine ⟨?_, ?_⟩
  · -- F u ≠ F v: differs at i₀.
    intro heq
    exact hne_f (congrFun heq i₀)
  · -- ¬ (bigStrong G').Adj (F u) (F v): provide i₀ as witness.
    simp only [bigStrongProduct_adj, not_and, not_forall, not_or]
    intro _
    exact ⟨i₀, hne_f, hnadj_f⟩

end ShannonCapacity
