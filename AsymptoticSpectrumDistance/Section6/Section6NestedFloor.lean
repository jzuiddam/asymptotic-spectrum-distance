/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Nested Floor Bound for Products of Fraction Graphs

Proves the nested floor bound (Theorem 6.4 from the paper):
for products of fraction graphs E_{p₁/q₁} ⊠ ⋯ ⊠ E_{pₖ/qₖ}, the independence number is
bounded by a nested floor expression.

The paper states the bound in the **left-nested** form
  ⌊⋯⌊⌊p₁/q₁⌋ · p₂/q₂⌋ ⋯ · pₖ/qₖ⌋,
where the floor is applied innermost to `p₁/q₁` and the multiplications grow outward.

This file proves the equivalent **right-nested** form
  ⌊(p₁/q₁) · ⌊(p₂/q₂) · ⋯ · ⌊pₖ/qₖ⌋ ⋯ ⌋⌋,
where the floor is applied innermost to `pₖ/qₖ` and the multiplications grow outward.
These two forms differ only by the order of the factors (the left-hand side is
invariant under permutation), so the paper and Lean forms are interchangeable by
reversing the list of factors.

Concrete versions are given for k = 1, 2, 3, plus the general list-indexed
form for arbitrary k.

## Main results

- `fractionGraph_indepNum_le`: α(E_{p/q}) ≤ ⌊p/q⌋₊
- `nested_floor_two`: α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) ≤ ⌊(p₁/q₁) · ⌊p₂/q₂⌋₊⌋₊
- `nested_floor_three`: three-factor version
- `nested_floor_list`: k-fold version, for an arbitrary list of (p, q) pairs
-/
import AsymptoticSpectrumDistance.Section6.Section6Hales
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphOperations
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.BigStrongProduct
import AsymptoticSpectrumDistance.Section3.FractionGraphsDefs

open ShannonCapacity

namespace Section6

/-! ## Base case: independence number of a single fraction graph -/

/-- α(E_{p/q}) ≤ p/q as reals (from the fractional clique cover). -/
theorem fractionGraph_indepNum_le_real (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    ((fractionGraph p q).indepNum : ℝ) ≤ (p : ℝ) / q := by
  obtain ⟨cliques, weights, hclique, hpos, hcover, hsum⟩ :=
    fractionalCliqueCover_fractionGraph p q hq h2q
  exact independenceNumber_le_of_clique_cover _ cliques weights hclique hpos hcover _ hsum

/-- α(E_{p/q}) ≤ ⌊p/q⌋₊ (base case of the nested floor bound). -/
theorem fractionGraph_indepNum_le (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    (fractionGraph p q).indepNum ≤ ⌊(p : ℝ) / q⌋₊ := by
  apply Nat.le_floor
  exact_mod_cast fractionGraph_indepNum_le_real p q hq h2q

/-! ## Two-factor nested floor bound -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Nested floor bound for two fraction graphs:
    α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) ≤ ⌊(p₁/q₁) · ⌊p₂/q₂⌋₊⌋₊ -/
theorem nested_floor_two (p₁ q₁ p₂ q₂ : ℕ)
    [NeZero p₁] [NeZero p₂]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂) :
    (strongProduct (fractionGraph p₁ q₁) (fractionGraph p₂ q₂)).indepNum ≤
    ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂⌋₊⌋₊ := by
  obtain ⟨cliques, weights, hclique, hpos, hcover, hsum⟩ :=
    fractionalCliqueCover_fractionGraph p₁ q₁ hq₁ h2q₁
  have h1 := hales_inequality (fractionGraph p₁ q₁) (fractionGraph p₂ q₂)
    cliques weights hclique hpos hcover ((p₁ : ℝ) / q₁) hsum
  have h2 := fractionGraph_indepNum_le p₂ q₂ hq₂ h2q₂
  calc (strongProduct (fractionGraph p₁ q₁) (fractionGraph p₂ q₂)).indepNum
      ≤ ⌊(p₁ : ℝ) / q₁ * (fractionGraph p₂ q₂).indepNum⌋₊ := h1
    _ ≤ ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂⌋₊⌋₊ := by
        apply Nat.floor_le_floor
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast h2
        · positivity

/-! ## Three-factor nested floor bound -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Nested floor bound for three fraction graphs:
    α(E_{p₁/q₁} ⊠ (E_{p₂/q₂} ⊠ E_{p₃/q₃})) ≤ ⌊(p₁/q₁) · ⌊(p₂/q₂) · ⌊p₃/q₃⌋₊⌋₊⌋₊ -/
theorem nested_floor_three (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤
    ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂ * ⌊(p₃ : ℝ) / q₃⌋₊⌋₊⌋₊ := by
  obtain ⟨cliques, weights, hclique, hpos, hcover, hsum⟩ :=
    fractionalCliqueCover_fractionGraph p₁ q₁ hq₁ h2q₁
  have h1 := hales_inequality (fractionGraph p₁ q₁)
    (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))
    cliques weights hclique hpos hcover ((p₁ : ℝ) / q₁) hsum
  have h2 := nested_floor_two p₂ q₂ p₃ q₃ hq₂ h2q₂ hq₃ h2q₃
  calc (strongProduct (fractionGraph p₁ q₁)
        (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum
      ≤ ⌊(p₁ : ℝ) / q₁ *
        ↑(strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃)).indepNum⌋₊ := h1
    _ ≤ ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂ * ⌊(p₃ : ℝ) / q₃⌋₊⌋₊⌋₊ := by
        apply Nat.floor_le_floor
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast h2
        · positivity

/-! ## General k-fold nested floor bound (list-indexed) -/

/-- Vertex type for a list-indexed product of fraction graphs.
    Empty list ↦ `PUnit` (single vertex); cons ↦ product. -/
def fractionGraphListVertex : List (ℕ+ × ℕ+) → Type
  | [] => PUnit
  | (p, _) :: rest => ZMod p × fractionGraphListVertex rest

instance : ∀ l, Fintype (fractionGraphListVertex l)
  | [] => inferInstanceAs (Fintype PUnit)
  | (p, _) :: rest =>
      letI : Fintype (fractionGraphListVertex rest) :=
        instFintypeFractionGraphListVertex rest
      inferInstanceAs (Fintype (ZMod p × _))

instance : ∀ l, DecidableEq (fractionGraphListVertex l)
  | [] => inferInstanceAs (DecidableEq PUnit)
  | (p, _) :: rest =>
      letI : DecidableEq (fractionGraphListVertex rest) :=
        instDecidableEqFractionGraphListVertex rest
      inferInstanceAs (DecidableEq (ZMod p × _))

/-- The strong product of fraction graphs over a list of `(p, q)` pairs. -/
def fractionGraphListProduct :
    (l : List (ℕ+ × ℕ+)) → SimpleGraph (fractionGraphListVertex l)
  | [] => ⊥
  | (p, q) :: rest =>
      strongProduct (fractionGraph (p : ℕ) (q : ℕ)) (fractionGraphListProduct rest)

/-- The nested floor expression for a list of fractions:
    `nestedFloorList [(p₁,q₁), …, (pₖ,qₖ)] = ⌊(p₁/q₁)·⌊…·⌊pₖ/qₖ⌋⌋⌋`. -/
noncomputable def nestedFloorList : List (ℕ+ × ℕ+) → ℕ
  | [] => 1
  | (p, q) :: rest => ⌊(p : ℝ) / q * nestedFloorList rest⌋₊

/-- Empty product: independence number is `1` (the trivial graph on `PUnit`). -/
theorem fractionGraphListProduct_nil_indepNum :
    (fractionGraphListProduct []).indepNum = 1 := by
  change (⊥ : SimpleGraph PUnit).indepNum = 1
  have h_indep : (⊥ : SimpleGraph PUnit).IsIndepSet ({PUnit.unit} : Finset PUnit) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro x _ y _ hxy
    exact (hxy (Subsingleton.elim x y)).elim
  have h_ge : 1 ≤ (⊥ : SimpleGraph PUnit).indepNum := by
    have h := h_indep.card_le_indepNum
    simpa using h
  have h_le : (⊥ : SimpleGraph PUnit).indepNum ≤ 1 := by
    rw [SimpleGraph.indepNum]
    apply csSup_le
    · refine ⟨0, ∅, ?_, by simp⟩
      rw [SimpleGraph.isIndepSet_iff]; intro x hx; simp at hx
    · rintro n ⟨s, _, rfl⟩
      have := s.card_le_univ (α := PUnit)
      simpa using this
  omega

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Theorem 6.4** (`th:nested-floor`, k-fold form): For any list of pairs
    `(p_i, q_i)` with `2·q_i ≤ p_i`,
    `α(E_{p_1/q_1} ⊠ ⋯ ⊠ E_{p_k/q_k}) ≤ ⌊(p_1/q_1)·⌊⋯·⌊p_k/q_k⌋⌋⌋`. -/
theorem nested_floor_list (l : List (ℕ+ × ℕ+))
    (hl : ∀ pq ∈ l, 2 * (pq.2 : ℕ) ≤ (pq.1 : ℕ)) :
    (fractionGraphListProduct l).indepNum ≤ nestedFloorList l := by
  induction l with
  | nil =>
    rw [fractionGraphListProduct_nil_indepNum]
    simp [nestedFloorList]
  | cons pq rest ih =>
    obtain ⟨p, q⟩ := pq
    have h2q : 2 * (q : ℕ) ≤ (p : ℕ) := hl _ List.mem_cons_self
    have hl' : ∀ pq' ∈ rest, 2 * (pq'.2 : ℕ) ≤ (pq'.1 : ℕ) :=
      fun pq' hpq' => hl pq' (List.mem_cons_of_mem _ hpq')
    obtain ⟨cliques, weights, hclique, hpos, hcover, hsum⟩ :=
      fractionalCliqueCover_fractionGraph (p : ℕ) (q : ℕ) q.pos h2q
    have h1 := hales_inequality (fractionGraph (p : ℕ) (q : ℕ))
      (fractionGraphListProduct rest)
      cliques weights hclique hpos hcover ((p : ℝ) / q) hsum
    have h2 := ih hl'
    change (strongProduct (fractionGraph (p : ℕ) (q : ℕ))
          (fractionGraphListProduct rest)).indepNum ≤ _
    calc (strongProduct (fractionGraph (p : ℕ) (q : ℕ))
            (fractionGraphListProduct rest)).indepNum
        ≤ ⌊(p : ℝ) / q * (fractionGraphListProduct rest).indepNum⌋₊ := h1
      _ ≤ ⌊(p : ℝ) / q * nestedFloorList rest⌋₊ := by
          apply Nat.floor_le_floor
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast h2
          · positivity

/-- Proof of `main_nested_floor`: single-step induction lemma used in the
    proof of Theorem 6.4. For any graph G and fraction graph E_{p/q},
    `α(E_{p/q} ⊠ G) ≤ ⌊(p/q) · α(G)⌋`. -/
theorem nested_floor {V : Type*} [Finite V]
    (p q : ℕ+) (h2q : 2 * q ≤ p)
    (G : SimpleGraph V) :
    (fractionGraph p q ⊠ G).indepNum ≤
    ⌊(p : ℝ) / q * G.indepNum⌋₊ := by
  classical
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨cliques, weights, hclique, hpos, hcover, hsum⟩ :=
    fractionalCliqueCover_fractionGraph p q q.pos h2q
  exact Section6.hales_inequality (fractionGraph p q) G
    cliques weights hclique hpos hcover ((p : ℝ) / q) hsum

/-! ## Left-associated wrapper for paper-API delegation (Main.lean)

`nested_floor_three_main` restates `nested_floor_three` in the left-associated
form `(A ⊠ B ⊠ C).indepNum ≤ ...` (matching the paper-API shape used by
`Main.main_nested_floor_three`), delegating via `indepNum_strongProduct_assoc`. -/

/-- Left-assoc wrapper for `nested_floor_three`. -/
theorem nested_floor_three_main (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ+)
    (h2q₁ : 2 * q₁ ≤ p₁) (h2q₂ : 2 * q₂ ≤ p₂) (h2q₃ : 2 * q₃ ≤ p₃) :
    (fractionGraph p₁ q₁ ⊠ fractionGraph p₂ q₂ ⊠ fractionGraph p₃ q₃).indepNum ≤
    ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂ * ⌊(p₃ : ℝ) / q₃⌋₊⌋₊⌋₊ := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact nested_floor_three p₁ q₁ p₂ q₂ p₃ q₃
    q₁.pos h2q₁ q₂.pos h2q₂ q₃.pos h2q₃

/-- Bundled-form wrapper for `nested_floor_list`: bounds the indep number of
    the `Graph.bigStrongProduct` of bundled `FractionGraph`s over `Fin l.length`.
    The proof builds a graph iso to the recursive `fractionGraphListProduct`,
    then transports via `independenceNumber_iso`. -/
theorem nested_floor_list_bundled (l : List (ℕ+ × ℕ+))
    (hl : ∀ pq ∈ l, 2 * (pq.2 : ℕ) ≤ (pq.1 : ℕ)) :
    (Graph.bigStrongProduct (fun i : Fin l.length =>
        AsymptoticSpectrumDistance.FractionGraph (l[i].1) (l[i].2))).indepNum ≤
    nestedFloorList l := by
  have iso : ∀ l' : List (ℕ+ × ℕ+),
      bigStrongProduct (fun i : Fin l'.length =>
        fractionGraph (l'[i].1 : ℕ) (l'[i].2 : ℕ)) ≃g
        fractionGraphListProduct l' := by
    intro l'
    induction l' with
    | nil => exact bigStrongProduct_zero_iso _
    | cons pq rest ih =>
        rcases pq with ⟨p, q⟩
        exact (bigStrongProduct_succ_iso _).trans (strongProduct_right_iso _ ih)
  simpa [← SimpleGraph.independenceNumber_iso (iso l)] using nested_floor_list l hl

end Section6
