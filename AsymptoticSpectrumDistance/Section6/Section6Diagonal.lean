/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Theorem 6.14: Diagonal Step Function

For p/q ∈ ℚ ∩ [2,3], the function α(E_{p/q}^⊠3) is a right-continuous step function:

    α(E_{p/q}^⊠3) = 8   for p/q ∈ [2, 5/2)
                   = 10  for p/q ∈ [5/2, 8/3)
                   = 12  for p/q ∈ [8/3, 11/4)
                   = 13  for p/q ∈ [11/4, 14/5)
                   = 14  for p/q ∈ [14/5, 3)
                   = 27  for p/q = 3

This follows from Theorem 6.9 (the 12 discontinuity values in Section6Alpha3.lean)
by restricting to symmetric triples (r, r, r).

The proof requires:
1. **Monotonicity**: α(E_{p₁/q₁}^⊠3) ≤ α(E_{p₂/q₂}^⊠3) when p₁/q₁ ≤ p₂/q₂.
   This gives lower bounds at non-boundary points.
2. **Upper bounds**: For intervals 4 and 5, the nested floor bound is tight.
   For intervals 1-3, the nested floor is NOT tight, and the upper bound requires
   the completeness of the discontinuity list (Lemma 6.6 + Lemma 6.13) or generalized
   Baumert arguments.

## References

- Theorem 6.14
- Theorem 6.9: the 12 discontinuity values
-/
import AsymptoticSpectrumDistance.Section6.Section6Alpha3
import AsymptoticSpectrumDistance.Section6.Section6NumeratorBound
import AsymptoticSpectrumDistance.Section3.VertexRemoval
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## Monotonicity of α₃ on the diagonal

The key ingredient: α(E_{p₁/q₁}^⊠3) ≤ α(E_{p₂/q₂}^⊠3) when p₁/q₁ ≤ p₂/q₂.

This follows from the existence of a cohomomorphism E_{p₁/q₁} → E_{p₂/q₂} when
p₁/q₁ ≤ p₂/q₂, which lifts to the 3-fold strong product via the Strassen preorder.

The cohomomorphism is constructed by iterating the one-step Stern-Brocot embedding
from `VertexRemoval.lean` (Lemma 6.6). Each step adds one vertex while preserving
the non-adjacency structure. -/

/-- One-step cohomomorphism: E_{p'/q'} ≤_G E_{p/q} for Stern-Brocot neighbors.
    When p*q' - q*p' = 1 (Bezout condition), the embed function from VertexRemoval.lean
    gives a cohomomorphism from fractionGraph p' q' to fractionGraph p q. -/
lemma cohom_fractionGraph_of_bezout {p q p' q' : ℕ}
    [NeZero p] [NeZero p']
    (hp' : 0 < p') (hp'_lt : p' < p)
    (hq' : 0 < q') (hq'_lt : q' < q)
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p)
    (hcoprime : Nat.Coprime p q)
    (hbezout : p * q' - q * p' = 1) :
    fractionGraph p' q' ≤_G fractionGraph p q := by
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨_, g, _, hg⟩ := Lemma66.lemma_6_6 hp' hp'_lt hp_pos hq' hq'_lt hq h2q hcoprime hbezout 0
  refine ⟨g, fun u v huv hnadj => ?_⟩
  have hkpq_adj : (Lemma66.Kpq p' q').Adj u v :=
    (Kpq_adj_iff_not_fractionGraph_adj u v huv).mpr hnadj
  obtain ⟨hkpq_guv, _, _⟩ := hg u v hkpq_adj
  exact ⟨hkpq_guv.ne,
         (Kpq_adj_iff_not_fractionGraph_adj (g u) (g v) hkpq_guv.ne).mp hkpq_guv⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Cohomomorphisms lift to the 3-fold strong product via the Strassen preorder.
    If G ≤_G H (there exists a cohomomorphism from G to H), then
    α(G ⊠ G ⊠ G) ≤ α(H ⊠ H ⊠ H). -/
lemma indepNum_strongProduct3_le_of_cohom {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hGH : G ≤_G H) :
    (strongProduct G (strongProduct G G)).indepNum ≤
    (strongProduct H (strongProduct H H)).indepNum := by
  have h : strongProduct G (strongProduct G G) ≤_G strongProduct H (strongProduct H H) :=
    (Cohom.strongProduct_left _ hGH).trans
      (Cohom.strongProduct_right _ ((Cohom.strongProduct_left _ hGH).trans
        (Cohom.strongProduct_right _ hGH)))
  obtain ⟨f, hf⟩ := h
  exact independenceNumber_le_of_cohomomorphism _ _ f hf

/-- General cohomomorphism: E_{p₁/q₁} ≤_G E_{p₂/q₂} when p₁/q₁ ≤ p₂/q₂.
    This is `fractionGraph_cohomomorphism` (Lemma 3.2) with the rational
    ordering condition converted from p₁ * q₂ ≤ p₂ * q₁. -/
lemma cohom_fractionGraph_monotone (p₁ q₁ p₂ q₂ : ℕ) [NeZero p₁] [NeZero p₂]
    (hq₁ : 0 < q₁) (_h2q₁ : 2 * q₁ ≤ p₁)
    (_hq₂ : 0 < q₂) (_h2q₂ : 2 * q₂ ≤ p₂)
    (hle : p₁ * q₂ ≤ p₂ * q₁) :
    fractionGraph p₁ q₁ ≤_G fractionGraph p₂ q₂ := by
  have hle_rat : (p₁ : ℚ) / q₁ ≤ (p₂ : ℚ) / q₂ := by
    rw [div_le_div_iff₀ (by exact_mod_cast hq₁ : (0:ℚ) < q₁) (by positivity)]
    exact_mod_cast hle
  exact ⟨_, fractionGraph_cohomomorphism p₁ q₁ p₂ q₂ hq₁ hle_rat |>.choose_spec⟩

/-- Monotonicity: α(E_{p₁/q₁}^⊠3) ≤ α(E_{p₂/q₂}^⊠3) when p₁/q₁ ≤ p₂/q₂.
The condition p₁/q₁ ≤ p₂/q₂ is expressed as p₁ * q₂ ≤ p₂ * q₁.
Follows from `cohom_fractionGraph_monotone` + `indepNum_strongProduct3_le_of_cohom`. -/
lemma alpha3_diagonal_monotone (p₁ q₁ p₂ q₂ : ℕ) [NeZero p₁] [NeZero p₂]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂)
    (hle : p₁ * q₂ ≤ p₂ * q₁) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₁ q₁) (fractionGraph p₁ q₁))).indepNum ≤
    (strongProduct (fractionGraph p₂ q₂)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₂ q₂))).indepNum :=
  indepNum_strongProduct3_le_of_cohom
    (cohom_fractionGraph_monotone p₁ q₁ p₂ q₂ hq₁ h2q₁ hq₂ h2q₂ hle)

/-! ## Helper for floor computations

`floor_val` (`⌊a⌋₊ = n` from `n ≤ a < n+1`) is in
`Section6UpperBoundsCommon` (transitively imported via `Section6Alpha3`). -/

/-! ## Theorem 6.14: Six interval cases

Each theorem handles one interval of the step function.
Intervals are specified by cross-multiplication conditions on p, q. -/

/-- **Interval 4**: α(E_{p/q}^⊠3) = 13 for p/q ∈ [11/4, 14/5).

Upper bound: nested floor gives exactly 13 (tight on this interval).
Lower bound: monotonicity from α₃(11/4, 11/4, 11/4) = 13. -/
theorem alpha3_diagonal_interval_4 (p q : ℕ) [NeZero p]
    (hq : 0 < q)
    (h_lb : 11 * q ≤ 4 * p) (h_ub : 5 * p < 14 * q) :
    (strongProduct (fractionGraph p q)
      (strongProduct (fractionGraph p q) (fractionGraph p q))).indepNum = 13 := by
  have h2q : 2 * q ≤ p := by omega
  apply le_antisymm
  · -- Upper bound: nested floor = 13 on [11/4, 14/5)
    -- ⌊p/q⌋ = 2, ⌊(p/q)·2⌋ = 5, ⌊(p/q)·5⌋ = 13
    have hq' : (0:ℝ) < q := by exact_mod_cast hq
    have hp3q : p < 3 * q := by nlinarith
    calc _ ≤ ⌊(p:ℝ)/q * ⌊(p:ℝ)/q * ⌊(p:ℝ)/q⌋₊⌋₊⌋₊ :=
            nested_floor_three p q p q p q hq h2q hq h2q hq h2q
      _ = 13 := by
        have h1 : ⌊(p : ℝ) / q⌋₊ = 2 := floor_val (by positivity)
          (by rw [le_div_iff₀ hq']; norm_cast)
          (by rw [div_lt_iff₀ hq']; norm_cast)
        rw [h1]; push_cast
        have h2 : ⌊(p : ℝ) / q * 2⌋₊ = 5 := by
          rw [show (p : ℝ) / q * 2 = (2 * (p : ℝ)) / q from by ring]
          exact floor_val (by positivity)
            (by rw [le_div_iff₀ hq']; norm_cast; nlinarith)
            (by rw [div_lt_iff₀ hq']; norm_cast; nlinarith)
        rw [h2]; push_cast
        rw [show (p : ℝ) / q * 5 = (5 * (p : ℝ)) / q from by ring]
        exact floor_val (by positivity)
          (by rw [le_div_iff₀ hq']; norm_cast; nlinarith)
          (by rw [div_lt_iff₀ hq']; norm_cast)
  · -- Lower bound: monotonicity from (11/4, 11/4, 11/4)
    calc 13 = (strongProduct (fractionGraph 11 4)
        (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).indepNum :=
          alpha3_11o4_11o4_11o4.symm
      _ ≤ _ := alpha3_diagonal_monotone 11 4 p q (by omega) (by omega) hq h2q
          (by nlinarith)

/-- **Interval 5**: α(E_{p/q}^⊠3) = 14 for p/q ∈ [14/5, 3).

Upper bound: nested floor gives exactly 14 (tight on this interval).
Lower bound: monotonicity from α₃(14/5, 14/5, 14/5) = 14. -/
theorem alpha3_diagonal_interval_5 (p q : ℕ) [NeZero p]
    (hq : 0 < q)
    (h_lb : 14 * q ≤ 5 * p) (h_ub : p < 3 * q) :
    (strongProduct (fractionGraph p q)
      (strongProduct (fractionGraph p q) (fractionGraph p q))).indepNum = 14 := by
  have h2q : 2 * q ≤ p := by omega
  apply le_antisymm
  · -- Upper bound: nested floor = 14 on [14/5, 3)
    -- ⌊p/q⌋ = 2, ⌊(p/q)·2⌋ = 5, ⌊(p/q)·5⌋ = 14
    have hq' : (0:ℝ) < q := by exact_mod_cast hq
    calc _ ≤ ⌊(p:ℝ)/q * ⌊(p:ℝ)/q * ⌊(p:ℝ)/q⌋₊⌋₊⌋₊ :=
            nested_floor_three p q p q p q hq h2q hq h2q hq h2q
      _ = 14 := by
        have h1 : ⌊(p : ℝ) / q⌋₊ = 2 := floor_val (by positivity)
          (by rw [le_div_iff₀ hq']; norm_cast)
          (by rw [div_lt_iff₀ hq']; norm_cast)
        rw [h1]; push_cast
        have h2 : ⌊(p : ℝ) / q * 2⌋₊ = 5 := by
          rw [show (p : ℝ) / q * 2 = (2 * (p : ℝ)) / q from by ring]
          exact floor_val (by positivity)
            (by rw [le_div_iff₀ hq']; norm_cast; nlinarith)
            (by rw [div_lt_iff₀ hq']; norm_cast; nlinarith)
        rw [h2]; push_cast
        rw [show (p : ℝ) / q * 5 = (5 * (p : ℝ)) / q from by ring]
        exact floor_val (by positivity)
          (by rw [le_div_iff₀ hq']; norm_cast)
          (by rw [div_lt_iff₀ hq']; norm_cast; nlinarith)
  · -- Lower bound: monotonicity from (14/5, 14/5, 14/5)
    calc 14 = (strongProduct (fractionGraph 14 5)
        (strongProduct (fractionGraph 14 5) (fractionGraph 14 5))).indepNum :=
          alpha3_14o5_14o5_14o5.symm
      _ ≤ _ := alpha3_diagonal_monotone 14 5 p q (by omega) (by omega) hq h2q
          (by nlinarith)

-- Intervals 1 and 2 are proved at the end of this file, after all infrastructure.

/-! ## Permutation isomorphism: swap first two factors of a triple product

The map (a, (b, c)) ↦ (b, (a, c)) is an isomorphism
  G ⊠ (H ⊠ K) ≃g H ⊠ (G ⊠ K)
This is constructed directly from the definition of strongProduct. -/

/-- Swap first two factors: G ⊠ (H ⊠ K) ≃g H ⊠ (G ⊠ K). -/
def strongProduct_swap12_iso {V W X : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph X) :
    strongProduct G (strongProduct H K) ≃g strongProduct H (strongProduct G K) where
  toEquiv := {
    toFun := fun ⟨a, b, c⟩ => ⟨b, a, c⟩
    invFun := fun ⟨b, a, c⟩ => ⟨a, b, c⟩
    left_inv := fun ⟨_, _, _⟩ => rfl
    right_inv := fun ⟨_, _, _⟩ => rfl
  }
  map_rel_iff' := by
    intro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩
    simp only [strongProduct, Equiv.coe_fn_mk, ne_eq, Prod.mk.injEq]
    tauto

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Independence number is invariant under swapping the first two factors. -/
lemma indepNum_strongProduct_swap12 {V W X : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype X] [DecidableEq X]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph X) :
    (strongProduct G (strongProduct H K)).indepNum =
    (strongProduct H (strongProduct G K)).indepNum :=
  independenceNumber_iso (strongProduct_swap12_iso G H K)

/-- Swap last two factors: G ⊠ (H ⊠ K) ≃g G ⊠ (K ⊠ H). -/
def strongProduct_swap23_iso {V W X : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph X) :
    strongProduct G (strongProduct H K) ≃g strongProduct G (strongProduct K H) where
  toEquiv := {
    toFun := fun ⟨a, b, c⟩ => ⟨a, c, b⟩
    invFun := fun ⟨a, c, b⟩ => ⟨a, b, c⟩
    left_inv := fun ⟨_, _, _⟩ => rfl
    right_inv := fun ⟨_, _, _⟩ => rfl
  }
  map_rel_iff' := by
    intro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩
    simp only [strongProduct, Equiv.coe_fn_mk, ne_eq, Prod.mk.injEq]
    tauto

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Independence number is invariant under swapping the last two factors. -/
lemma indepNum_strongProduct_swap23 {V W X : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype X] [DecidableEq X]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph X) :
    (strongProduct G (strongProduct H K)).indepNum =
    (strongProduct G (strongProduct K H)).indepNum :=
  independenceNumber_iso (strongProduct_swap23_iso G H K)

/-! ## First-factor monotonicity for strong products

If G ≤_G G' (cohomomorphism), then α(G ⊠ H) ≤ α(G' ⊠ H). -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Monotonicity in the first factor: if G ≤_G G', then α(G ⊠ H) ≤ α(G' ⊠ H). -/
private lemma indepNum_strongProduct_le_of_cohom_left
    {V V' W : Type*} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {G' : SimpleGraph V'} (H : SimpleGraph W)
    (hcohom : G ≤_G G') :
    (strongProduct G H).indepNum ≤ (strongProduct G' H).indepNum := by
  have h : strongProduct G H ≤_G strongProduct G' H :=
    Cohom.strongProduct_left H hcohom
  obtain ⟨f, hf⟩ := h
  exact independenceNumber_le_of_cohomomorphism _ _ f hf

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Monotonicity for mixed triples: if all three ratios are ≤ 8/3,
    then α(E_{p₁/q₁} ⊠ (E_{p₂/q₂} ⊠ E_{p₃/q₃})) ≤ 12. -/
private lemma mixed_triple_le_of_all_le_8o3
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ) [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃)
    (hle₁ : p₁ * 3 ≤ 8 * q₁)
    (hle₂ : p₂ * 3 ≤ 8 * q₂)
    (hle₃ : p₃ * 3 ≤ 8 * q₃) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 12 := by
  -- By first-factor monotonicity: α(p₁/q₁, ...) ≤ α(8/3, ...)
  calc _ ≤ (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum := by
        apply indepNum_strongProduct_le_of_cohom_left
        exact cohom_fractionGraph_monotone p₁ q₁ 8 3
          hq₁ h2q₁ (by omega) (by omega) (by nlinarith)
    -- By second-factor monotonicity: α(8/3, p₂/q₂, p₃/q₃) ≤ α(8/3, 8/3, p₃/q₃)
    _ ≤ (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph p₃ q₃))).indepNum := by
        have hcohom₂ := cohom_fractionGraph_monotone p₂ q₂ 8 3
          hq₂ h2q₂ (by omega) (by omega) (by nlinarith)
        have h_inner : strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃) ≤_G
            strongProduct (fractionGraph 8 3) (fractionGraph p₃ q₃) :=
          Cohom.strongProduct_left _ hcohom₂
        have h_outer : strongProduct (fractionGraph 8 3)
              (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃)) ≤_G
            strongProduct (fractionGraph 8 3)
              (strongProduct (fractionGraph 8 3) (fractionGraph p₃ q₃)) :=
          Cohom.strongProduct_right _ h_inner
        obtain ⟨f, hf⟩ := h_outer
        exact independenceNumber_le_of_cohomomorphism _ _ f hf
    -- By third-factor monotonicity: α(8/3, 8/3, p₃/q₃) ≤ α(8/3, 8/3, 8/3)
    _ ≤ (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum := by
        have hcohom₃ := cohom_fractionGraph_monotone p₃ q₃ 8 3
          hq₃ h2q₃ (by omega) (by omega) (by nlinarith)
        -- E_{p₃/q₃} ≤_G E_{8/3} lifts to inner product, then to outer product
        have h_inner : strongProduct (fractionGraph 8 3) (fractionGraph p₃ q₃) ≤_G
            strongProduct (fractionGraph 8 3) (fractionGraph 8 3) :=
          Cohom.strongProduct_right _ hcohom₃
        have h_outer : strongProduct (fractionGraph 8 3)
              (strongProduct (fractionGraph 8 3) (fractionGraph p₃ q₃)) ≤_G
            strongProduct (fractionGraph 8 3)
              (strongProduct (fractionGraph 8 3) (fractionGraph 8 3)) :=
          Cohom.strongProduct_right _ h_inner
        obtain ⟨f, hf⟩ := h_outer
        exact independenceNumber_le_of_cohomomorphism _ _ f hf
    _ = 12 := alpha3_8o3_8o3_8o3

/-! ## General mixed-triple upper bound

The key lemma: for any triple with all ratios in [2, 11/4), α ≤ 12.
Proved by strong induction on p₁ + p₂ + p₃.

The induction works as follows:
- **Base case**: If all ratios ≤ 8/3, use `mixed_triple_le_of_all_le_8o3`.
- **Inductive step**: Some ratio > 8/3. Put it first (via swap12).
  - If not coprime: reduce GCD (smaller numerator, same ratio, ≤ by cohomomorphism).
  - If coprime: p₁ ≥ 19 > 13 (since coprime fractions in (8/3, 11/4) have numerator ≥ 19).
    Nested floor gives α ≤ 13. If α ≤ 12, done.
    If α = 13: apply `numerator_bound` to get (a, b) with a < p₁ and α(a/b, p₂, p₃) ≥ 13.
    By IH (sum decreases), α(a/b, p₂, p₃) ≤ 12. Contradiction. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Nested floor gives ≤ 13 for any triple with all ratios in [2, 11/4) and ≥ 2. -/
private lemma nested_floor_le_13
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    (hq₁ : 0 < q₁) (_h2q₁ : 2 * q₁ ≤ p₁) (hub₁ : 4 * p₁ < 11 * q₁)
    (hq₂ : 0 < q₂) (_h2q₂ : 2 * q₂ ≤ p₂) (hub₂ : 4 * p₂ < 11 * q₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) (hub₃ : 4 * p₃ < 11 * q₃) :
    ⌊(p₁:ℝ)/q₁ * ⌊(p₂:ℝ)/q₂ * ⌊(p₃:ℝ)/q₃⌋₊⌋₊⌋₊ ≤ 13 := by
  have hq₁' : (0:ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂' : (0:ℝ) < q₂ := by exact_mod_cast hq₂
  have hq₃' : (0:ℝ) < q₃ := by exact_mod_cast hq₃
  have hp₃_lt : p₃ < 3 * q₃ := by nlinarith
  have h1 : ⌊(p₃ : ℝ) / q₃⌋₊ = 2 := floor_val (by positivity)
    (by rw [le_div_iff₀ hq₃']; norm_cast)
    (by rw [div_lt_iff₀ hq₃']; norm_cast)
  rw [h1]; push_cast
  -- floor(p₂/q₂ * 2) ≤ 5
  have hp₂_lt : p₂ < 3 * q₂ := by nlinarith
  have h2_le : ⌊(p₂ : ℝ) / q₂ * 2⌋₊ ≤ 5 := by
    rw [show (p₂ : ℝ) / q₂ * 2 = (2 * (p₂ : ℝ)) / q₂ from by ring]
    have : (2 * (p₂ : ℝ)) / q₂ < 6 := by
      rw [div_lt_iff₀ hq₂']
      exact_mod_cast (show 2 * p₂ < 6 * q₂ from by nlinarith)
    exact Nat.lt_add_one_iff.mp (Nat.floor_lt (by positivity) |>.mpr this)
  -- floor(p₁/q₁ * floor(...)) ≤ 13
  calc ⌊(p₁ : ℝ) / q₁ * ↑⌊(p₂ : ℝ) / q₂ * 2⌋₊⌋₊
      ≤ ⌊(p₁ : ℝ) / q₁ * 5⌋₊ := by
        apply Nat.floor_le_floor
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast h2_le
    _ ≤ 13 := by
        rw [show (p₁ : ℝ) / q₁ * 5 = (5 * (p₁ : ℝ)) / q₁ from by ring]
        have : (5 * (p₁ : ℝ)) / q₁ < 14 := by
          rw [div_lt_iff₀ hq₁']
          exact_mod_cast (show 5 * p₁ < 14 * q₁ from by nlinarith)
        exact Nat.lt_add_one_iff.mp (Nat.floor_lt (by positivity) |>.mpr this)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Auxiliary: reduce factor 1 assuming coprime and ratio > 8/3.
    If α ≤ 12, we're done. If α = 13, numerator_bound gives a contradiction
    with the IH applied to a triple with smaller sum of numerators. -/
private lemma alpha3_mixed_le_12_coprime_step
    {n : ℕ}
    (IH : ∀ m < n, ∀ p₁' q₁' p₂' q₂' p₃' q₃' : ℕ,
      p₁' + p₂' + p₃' ≤ m →
      [NeZero p₁'] → [NeZero p₂'] → [NeZero p₃'] →
      0 < q₁' → 2 * q₁' ≤ p₁' → 4 * p₁' < 11 * q₁' →
      0 < q₂' → 2 * q₂' ≤ p₂' → 4 * p₂' < 11 * q₂' →
      0 < q₃' → 2 * q₃' ≤ p₃' → 4 * p₃' < 11 * q₃' →
      (strongProduct (fractionGraph p₁' q₁')
        (strongProduct (fractionGraph p₂' q₂') (fractionGraph p₃' q₃'))).indepNum ≤ 12)
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hsum : p₁ + p₂ + p₃ ≤ n)
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hub₁ : 4 * p₁ < 11 * q₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂) (hub₂ : 4 * p₂ < 11 * q₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) (hub₃ : 4 * p₃ < 11 * q₃)
    (hbig₁ : 8 * q₁ < p₁ * 3)
    (hcop₁ : Nat.Coprime p₁ q₁) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 12 := by
  -- Step 1: Nested floor gives α ≤ 13
  set α := (strongProduct (fractionGraph p₁ q₁)
    (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum
  have hα_le_13 : α ≤ 13 :=
    (nested_floor_three p₁ q₁ p₂ q₂ p₃ q₃ hq₁ h2q₁ hq₂ h2q₂ hq₃ h2q₃).trans
      (nested_floor_le_13 p₁ q₁ p₂ q₂ p₃ q₃
        hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃)
  -- Step 2: If α ≤ 12, done
  by_contra h_not_le
  push_neg at h_not_le
  -- So α ≥ 13, combined with ≤ 13 gives α = 13
  -- p₁ ≥ 14 > 13 = α (from hbig₁: 8*q₁ < 3*p₁ and 2*q₁ ≤ p₁)
  have hp₁_ge : p₁ ≥ 14 := by omega
  -- Apply numerator_bound (requires α < p₁, coprime, q₁ ≥ 2)
  have hq₁_ge2 : 2 ≤ q₁ := by nlinarith
  obtain ⟨a, b, ha_pos, hb_pos, ha_lt_p₁, h2b_le_a, _, hab_lt, hα_ge⟩ :=
    numerator_bound p₁ q₁ p₂ q₂ p₃ q₃ hq₁_ge2 h2q₁ hcop₁
      hq₂ h2q₂ hq₃ h2q₃ (by omega : α < p₁)
  -- a/b < p₁/q₁ < 11/4, so 4*a < 11*b
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  have hub_a : 4 * a < 11 * b := by
    suffices h : (4 * a : ℚ) < 11 * b by exact_mod_cast h
    have hb_pos_rat : (0 : ℚ) < b := Nat.cast_pos.mpr hb_pos
    have hq₁_pos_rat : (0 : ℚ) < q₁ := Nat.cast_pos.mpr hq₁
    have hub₁_rat : (4 : ℚ) * p₁ < 11 * q₁ := by exact_mod_cast hub₁
    have h2 : (p₁ : ℚ) / q₁ < 11 / 4 := by
      rw [div_lt_div_iff₀ hq₁_pos_rat (by norm_num : (0:ℚ) < 4)]; linarith
    have h3 : (a : ℚ) / b < 11 / 4 := hab_lt.trans h2
    rw [div_lt_div_iff₀ hb_pos_rat (by norm_num : (0:ℚ) < 4)] at h3; linarith
  -- Apply IH (a + p₂ + p₃ < p₁ + p₂ + p₃ since a < p₁)
  have h_IH := IH (a + p₂ + p₃) (by omega) a b p₂ q₂ p₃ q₃ (le_refl _)
    hb_pos h2b_le_a hub_a hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃
  -- hα_ge: α ≤ α(a/b, p₂, p₃), h_IH: α(a/b, p₂, p₃) ≤ 12, but α ≥ 13
  have : α ≤ 12 := le_trans hα_ge h_IH
  omega

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- General upper bound: for any triple with all ratios in [2, 11/4),
    α(E_{p₁/q₁} ⊠ (E_{p₂/q₂} ⊠ E_{p₃/q₃})) ≤ 12.
    Proved by strong induction on p₁ + p₂ + p₃. -/
private lemma alpha3_mixed_le_12 :
    ∀ n : ℕ, ∀ p₁ q₁ p₂ q₂ p₃ q₃ : ℕ,
    p₁ + p₂ + p₃ ≤ n →
    [NeZero p₁] → [NeZero p₂] → [NeZero p₃] →
    0 < q₁ → 2 * q₁ ≤ p₁ → 4 * p₁ < 11 * q₁ →
    0 < q₂ → 2 * q₂ ≤ p₂ → 4 * p₂ < 11 * q₂ →
    0 < q₃ → 2 * q₃ ≤ p₃ → 4 * p₃ < 11 * q₃ →
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 12 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro p₁ q₁ p₂ q₂ p₃ q₃ hsum _ _ _ hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃
    -- Case 1: All three ratios ≤ 8/3
    by_cases h_all_le : p₁ * 3 ≤ 8 * q₁ ∧ p₂ * 3 ≤ 8 * q₂ ∧ p₃ * 3 ≤ 8 * q₃
    · exact mixed_triple_le_of_all_le_8o3 p₁ q₁ p₂ q₂ p₃ q₃
        hq₁ h2q₁ hq₂ h2q₂ hq₃ h2q₃ h_all_le.1 h_all_le.2.1 h_all_le.2.2
    · -- Case 2: Some ratio > 8/3. Find which one and put it first.
      simp only [not_and_or, not_le] at h_all_le
      -- Reduce to the case where factor 1 has ratio > 8/3
      suffices h_reduced : ∀ (p₁' q₁' p₂' q₂' p₃' q₃' : ℕ),
          p₁' + p₂' + p₃' ≤ n →
          [NeZero p₁'] → [NeZero p₂'] → [NeZero p₃'] →
          0 < q₁' → 2 * q₁' ≤ p₁' → 4 * p₁' < 11 * q₁' →
          0 < q₂' → 2 * q₂' ≤ p₂' → 4 * p₂' < 11 * q₂' →
          0 < q₃' → 2 * q₃' ≤ p₃' → 4 * p₃' < 11 * q₃' →
          8 * q₁' < p₁' * 3 →
          (strongProduct (fractionGraph p₁' q₁')
            (strongProduct (fractionGraph p₂' q₂')
              (fractionGraph p₃' q₃'))).indepNum ≤ 12 by
        rcases h_all_le with h1 | h2 | h3
        · exact h_reduced p₁ q₁ p₂ q₂ p₃ q₃ hsum
            hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃ h1
        · rw [indepNum_strongProduct_swap12]
          exact h_reduced p₂ q₂ p₁ q₁ p₃ q₃ (by omega)
            hq₂ h2q₂ hub₂ hq₁ h2q₁ hub₁ hq₃ h2q₃ hub₃ h2
        · -- Swap23 then swap12: (1,2,3) → (1,3,2) → (3,1,2)
          rw [indepNum_strongProduct_swap23, indepNum_strongProduct_swap12]
          exact h_reduced p₃ q₃ p₁ q₁ p₂ q₂ (by omega)
            hq₃ h2q₃ hub₃ hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ h3
      -- Now prove: if factor 1 has ratio > 8/3 (strictly), then α ≤ 12
      intro p₁' q₁' p₂' q₂' p₃' q₃' hsum' _ _ _
        hq₁' h2q₁' hub₁' hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃' hbig₁'
      -- Subcase: coprime or not
      by_cases hcop : Nat.Coprime p₁' q₁'
      · -- Coprime: apply numerator_bound
        exact alpha3_mixed_le_12_coprime_step IH p₁' q₁' p₂' q₂' p₃' q₃'
          hsum' hq₁' h2q₁' hub₁' hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃' hbig₁' hcop
      · -- Not coprime: GCD reduction
        set g := Nat.gcd p₁' q₁' with hg_def
        have hg_ne_zero : g ≠ 0 := by
          simp only [hg_def]; exact Nat.gcd_ne_zero_left (NeZero.ne p₁')
        have hg_gt1 : g > 1 := by
          simp only [Nat.Coprime] at hcop; omega
        have hg_pos : 0 < g := by omega
        have hg_dvd_p : g ∣ p₁' := hg_def ▸ Nat.gcd_dvd_left p₁' q₁'
        have hg_dvd_q : g ∣ q₁' := hg_def ▸ Nat.gcd_dvd_right p₁' q₁'
        set p₀ := p₁' / g with hp₀_def
        set q₀ := q₁' / g with hq₀_def
        have hp₁'_eq : p₁' = g * p₀ := by
          rw [hp₀_def, mul_comm]; exact (Nat.div_mul_cancel hg_dvd_p).symm
        have hq₁'_eq : q₁' = g * q₀ := by
          rw [hq₀_def, mul_comm]; exact (Nat.div_mul_cancel hg_dvd_q).symm
        have hp₀_pos : 0 < p₀ := by
          rw [hp₀_def]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_p) hg_pos
        have hp₀_lt : p₀ < p₁' := by
          calc p₀ = 1 * p₀ := (one_mul _).symm
            _ < g * p₀ := (Nat.mul_lt_mul_right hp₀_pos).mpr hg_gt1
            _ = p₁' := hp₁'_eq.symm
        have hq₀_pos : 0 < q₀ := by
          rw [hq₀_def]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_q) hg_pos
        have h2q₀ : 2 * q₀ ≤ p₀ := by
          have h := h2q₁'; rw [hp₁'_eq, hq₁'_eq] at h
          exact Nat.le_of_mul_le_mul_left (show g * (2 * q₀) ≤ g * p₀ by nlinarith) hg_pos
        have hub₀ : 4 * p₀ < 11 * q₀ := by
          have h := hub₁'; rw [hp₁'_eq, hq₁'_eq] at h
          exact lt_of_mul_lt_mul_left (show g * (4 * p₀) < g * (11 * q₀) by nlinarith)
            (Nat.zero_le g)
        haveI : NeZero p₀ := ⟨by omega⟩
        -- Cohomomorphism: E_{p₁'/q₁'} ≤_G E_{p₀/q₀} (same ratio, same graph)
        have hle_ratio : p₁' * q₀ ≤ p₀ * q₁' := by
          rw [hp₁'_eq, hq₁'_eq]; nlinarith
        have hcohom : fractionGraph p₁' q₁' ≤_G fractionGraph p₀ q₀ :=
          cohom_fractionGraph_monotone p₁' q₁' p₀ q₀
            hq₁' h2q₁' hq₀_pos h2q₀ hle_ratio
        -- α(p₁'/q₁', p₂, p₃) ≤ α(p₀/q₀, p₂, p₃) ≤ 12 (by IH)
        calc _ ≤ (strongProduct (fractionGraph p₀ q₀)
              (strongProduct (fractionGraph p₂' q₂')
                (fractionGraph p₃' q₃'))).indepNum :=
              indepNum_strongProduct_le_of_cohom_left _ hcohom
          _ ≤ 12 := IH (p₀ + p₂' + p₃') (by omega) p₀ q₀ p₂' q₂' p₃' q₃'
                (le_refl _) hq₀_pos h2q₀ hub₀ hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃'

/-- **Interval 3**: α(E_{p/q}^⊠3) = 12 for p/q ∈ [8/3, 11/4).

Lower bound: monotonicity from α₃(8/3, 8/3, 8/3) = 12.
Upper bound: from `alpha3_mixed_le_12` applied to the diagonal triple. -/
theorem alpha3_diagonal_interval_3 (p q : ℕ) [NeZero p]
    (hq : 0 < q)
    (h_lb : 8 * q ≤ 3 * p) (h_ub : 4 * p < 11 * q) :
    (strongProduct (fractionGraph p q)
      (strongProduct (fractionGraph p q) (fractionGraph p q))).indepNum = 12 := by
  have h2q : 2 * q ≤ p := by omega
  apply le_antisymm
  · exact alpha3_mixed_le_12 (p + p + p) p q p q p q (le_refl _)
      hq h2q h_ub hq h2q h_ub hq h2q h_ub
  · calc 12 = (strongProduct (fractionGraph 8 3)
        (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum :=
          alpha3_8o3_8o3_8o3.symm
      _ ≤ _ := alpha3_diagonal_monotone 8 3 p q (by omega) (by omega) hq h2q
          (by nlinarith)

/-! ## Interval 1 infrastructure: mixed triple bound for [2, 5/2)

Analogous to `alpha3_mixed_le_12` but for the interval [2, 5/2) with bound 8.
Base case: all ratios ≤ 7/3 → α ≤ α(E_{7/3}³) ≤ 8 (from `alpha3_7o3_7o3_7o3_le`).
Inductive step: some ratio > 7/3 → coprime p₁ ≥ 12 > 9 ≥ α → numerator_bound. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Base case: if all three ratios ≤ 7/3, then α ≤ 8 (via factor-by-factor
    monotonicity to E_{7/3}³). -/
private lemma mixed_triple_le_of_all_le_7o3
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ) [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃)
    (hle₁ : p₁ * 3 ≤ 7 * q₁)
    (hle₂ : p₂ * 3 ≤ 7 * q₂)
    (hle₃ : p₃ * 3 ≤ 7 * q₃) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 8 := by
  calc _ ≤ (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum := by
        apply indepNum_strongProduct_le_of_cohom_left
        exact cohom_fractionGraph_monotone p₁ q₁ 7 3
          hq₁ h2q₁ (by omega) (by omega) (by nlinarith)
    _ ≤ (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3) (fractionGraph p₃ q₃))).indepNum := by
        have hcohom₂ := cohom_fractionGraph_monotone p₂ q₂ 7 3
          hq₂ h2q₂ (by omega) (by omega) (by nlinarith)
        have h_inner : strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃) ≤_G
            strongProduct (fractionGraph 7 3) (fractionGraph p₃ q₃) :=
          Cohom.strongProduct_left _ hcohom₂
        have h_outer : strongProduct (fractionGraph 7 3)
              (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃)) ≤_G
            strongProduct (fractionGraph 7 3)
              (strongProduct (fractionGraph 7 3) (fractionGraph p₃ q₃)) :=
          Cohom.strongProduct_right _ h_inner
        obtain ⟨f, hf⟩ := h_outer
        exact independenceNumber_le_of_cohomomorphism _ _ f hf
    _ ≤ (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3) (fractionGraph 7 3))).indepNum := by
        have hcohom₃ := cohom_fractionGraph_monotone p₃ q₃ 7 3
          hq₃ h2q₃ (by omega) (by omega) (by nlinarith)
        have h_inner : strongProduct (fractionGraph 7 3) (fractionGraph p₃ q₃) ≤_G
            strongProduct (fractionGraph 7 3) (fractionGraph 7 3) :=
          Cohom.strongProduct_right _ hcohom₃
        have h_outer : strongProduct (fractionGraph 7 3)
              (strongProduct (fractionGraph 7 3) (fractionGraph p₃ q₃)) ≤_G
            strongProduct (fractionGraph 7 3)
              (strongProduct (fractionGraph 7 3) (fractionGraph 7 3)) :=
          Cohom.strongProduct_right _ h_inner
        obtain ⟨f, hf⟩ := h_outer
        exact independenceNumber_le_of_cohomomorphism _ _ f hf
    _ ≤ 8 := alpha3_7o3_7o3_7o3_le

/-- Nested floor ≤ 9 for all triples in [2, 5/2). -/
private lemma nested_floor_le_9_lt_5o2
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    (hq₁ : 0 < q₁) (_h2q₁ : 2 * q₁ ≤ p₁) (hub₁ : 2 * p₁ < 5 * q₁)
    (hq₂ : 0 < q₂) (_h2q₂ : 2 * q₂ ≤ p₂) (hub₂ : 2 * p₂ < 5 * q₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) (hub₃ : 2 * p₃ < 5 * q₃) :
    ⌊(p₁:ℝ)/q₁ * ⌊(p₂:ℝ)/q₂ * ⌊(p₃:ℝ)/q₃⌋₊⌋₊⌋₊ ≤ 9 := by
  have hq₁' : (0:ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂' : (0:ℝ) < q₂ := by exact_mod_cast hq₂
  have hq₃' : (0:ℝ) < q₃ := by exact_mod_cast hq₃
  have h1 : ⌊(p₃ : ℝ) / q₃⌋₊ = 2 := floor_val (by positivity)
    (by rw [le_div_iff₀ hq₃']; norm_cast)
    (by rw [div_lt_iff₀ hq₃']; norm_cast; nlinarith)
  rw [h1]; push_cast
  have h2_le : ⌊(p₂ : ℝ) / q₂ * 2⌋₊ ≤ 4 := by
    rw [show (p₂ : ℝ) / q₂ * 2 = (2 * (p₂ : ℝ)) / q₂ from by ring]
    have : (2 * (p₂ : ℝ)) / q₂ < 5 := by
      rw [div_lt_iff₀ hq₂']
      exact_mod_cast (show 2 * p₂ < 5 * q₂ from hub₂)
    exact Nat.lt_add_one_iff.mp (Nat.floor_lt (by positivity) |>.mpr this)
  calc ⌊(p₁ : ℝ) / q₁ * ↑⌊(p₂ : ℝ) / q₂ * 2⌋₊⌋₊
      ≤ ⌊(p₁ : ℝ) / q₁ * 4⌋₊ := by
        apply Nat.floor_le_floor
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast h2_le
    _ ≤ 9 := by
        rw [show (p₁ : ℝ) / q₁ * 4 = (4 * (p₁ : ℝ)) / q₁ from by ring]
        have : (4 * (p₁ : ℝ)) / q₁ < 10 := by
          rw [div_lt_iff₀ hq₁']
          exact_mod_cast (show 4 * p₁ < 10 * q₁ from by nlinarith)
        exact Nat.lt_add_one_iff.mp (Nat.floor_lt (by positivity) |>.mpr this)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Coprime inductive step for interval 1: if p₁/q₁ > 7/3 and coprime,
    then p₁ ≥ 12 > 9 ≥ α, so numerator_bound applies. -/
private lemma alpha3_mixed_le_8_coprime_step
    {n : ℕ}
    (IH : ∀ m < n, ∀ p₁' q₁' p₂' q₂' p₃' q₃' : ℕ,
      p₁' + p₂' + p₃' ≤ m →
      [NeZero p₁'] → [NeZero p₂'] → [NeZero p₃'] →
      0 < q₁' → 2 * q₁' ≤ p₁' → 2 * p₁' < 5 * q₁' →
      0 < q₂' → 2 * q₂' ≤ p₂' → 2 * p₂' < 5 * q₂' →
      0 < q₃' → 2 * q₃' ≤ p₃' → 2 * p₃' < 5 * q₃' →
      (strongProduct (fractionGraph p₁' q₁')
        (strongProduct (fractionGraph p₂' q₂') (fractionGraph p₃' q₃'))).indepNum ≤ 8)
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hsum : p₁ + p₂ + p₃ ≤ n)
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hub₁ : 2 * p₁ < 5 * q₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂) (hub₂ : 2 * p₂ < 5 * q₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) (hub₃ : 2 * p₃ < 5 * q₃)
    (hbig₁ : 7 * q₁ < p₁ * 3)
    (hcop₁ : Nat.Coprime p₁ q₁) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 8 := by
  set α := (strongProduct (fractionGraph p₁ q₁)
    (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum
  have hα_le_9 : α ≤ 9 :=
    (nested_floor_three p₁ q₁ p₂ q₂ p₃ q₃ hq₁ h2q₁ hq₂ h2q₂ hq₃ h2q₃).trans
      (nested_floor_le_9_lt_5o2 p₁ q₁ p₂ q₂ p₃ q₃
        hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃)
  by_contra h_not_le
  push_neg at h_not_le
  -- p₁ ≥ 12 > 9 ≥ α (coprime p₁/q₁ ∈ (7/3, 5/2) forces q₁ ≥ 5, p₁ ≥ 12)
  have hp₁_ge : p₁ ≥ 12 := by omega
  have hq₁_ge2 : 2 ≤ q₁ := by nlinarith
  obtain ⟨a, b, ha_pos, hb_pos, ha_lt_p₁, h2b_le_a, _, hab_lt, hα_ge⟩ :=
    numerator_bound p₁ q₁ p₂ q₂ p₃ q₃ hq₁_ge2 h2q₁ hcop₁
      hq₂ h2q₂ hq₃ h2q₃ (by omega : α < p₁)
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  have hub_a : 2 * a < 5 * b := by
    suffices h : (2 * a : ℚ) < 5 * b by exact_mod_cast h
    have hb_pos_rat : (0 : ℚ) < b := Nat.cast_pos.mpr hb_pos
    have hq₁_pos_rat : (0 : ℚ) < q₁ := Nat.cast_pos.mpr hq₁
    have hub₁_rat : (2 : ℚ) * p₁ < 5 * q₁ := by exact_mod_cast hub₁
    have h2 : (p₁ : ℚ) / q₁ < 5 / 2 := by
      rw [div_lt_div_iff₀ hq₁_pos_rat (by norm_num : (0:ℚ) < 2)]; linarith
    have h3 : (a : ℚ) / b < 5 / 2 := hab_lt.trans h2
    rw [div_lt_div_iff₀ hb_pos_rat (by norm_num : (0:ℚ) < 2)] at h3; linarith
  have h_IH := IH (a + p₂ + p₃) (by omega) a b p₂ q₂ p₃ q₃ (le_refl _)
    hb_pos h2b_le_a hub_a hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃
  have : α ≤ 8 := le_trans hα_ge h_IH
  omega

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Mixed triple bound for interval 1: for all triples with all ratios in [2, 5/2),
    α(E_{p₁/q₁} ⊠ (E_{p₂/q₂} ⊠ E_{p₃/q₃})) ≤ 8.
    Proved by strong induction on p₁ + p₂ + p₃. -/
private lemma alpha3_mixed_le_8 :
    ∀ n : ℕ, ∀ p₁ q₁ p₂ q₂ p₃ q₃ : ℕ,
    p₁ + p₂ + p₃ ≤ n →
    [NeZero p₁] → [NeZero p₂] → [NeZero p₃] →
    0 < q₁ → 2 * q₁ ≤ p₁ → 2 * p₁ < 5 * q₁ →
    0 < q₂ → 2 * q₂ ≤ p₂ → 2 * p₂ < 5 * q₂ →
    0 < q₃ → 2 * q₃ ≤ p₃ → 2 * p₃ < 5 * q₃ →
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 8 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro p₁ q₁ p₂ q₂ p₃ q₃ hsum _ _ _ hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃
    -- Case 1: All three ratios ≤ 7/3
    by_cases h_all_le : p₁ * 3 ≤ 7 * q₁ ∧ p₂ * 3 ≤ 7 * q₂ ∧ p₃ * 3 ≤ 7 * q₃
    · exact mixed_triple_le_of_all_le_7o3 p₁ q₁ p₂ q₂ p₃ q₃
        hq₁ h2q₁ hq₂ h2q₂ hq₃ h2q₃ h_all_le.1 h_all_le.2.1 h_all_le.2.2
    · -- Case 2: Some ratio > 7/3. Put it first via swap.
      simp only [not_and_or, not_le] at h_all_le
      suffices h_reduced : ∀ (p₁' q₁' p₂' q₂' p₃' q₃' : ℕ),
          p₁' + p₂' + p₃' ≤ n →
          [NeZero p₁'] → [NeZero p₂'] → [NeZero p₃'] →
          0 < q₁' → 2 * q₁' ≤ p₁' → 2 * p₁' < 5 * q₁' →
          0 < q₂' → 2 * q₂' ≤ p₂' → 2 * p₂' < 5 * q₂' →
          0 < q₃' → 2 * q₃' ≤ p₃' → 2 * p₃' < 5 * q₃' →
          7 * q₁' < p₁' * 3 →
          (strongProduct (fractionGraph p₁' q₁')
            (strongProduct (fractionGraph p₂' q₂')
              (fractionGraph p₃' q₃'))).indepNum ≤ 8 by
        rcases h_all_le with h1 | h2 | h3
        · exact h_reduced p₁ q₁ p₂ q₂ p₃ q₃ hsum
            hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃ h1
        · rw [indepNum_strongProduct_swap12]
          exact h_reduced p₂ q₂ p₁ q₁ p₃ q₃ (by omega)
            hq₂ h2q₂ hub₂ hq₁ h2q₁ hub₁ hq₃ h2q₃ hub₃ h2
        · rw [indepNum_strongProduct_swap23, indepNum_strongProduct_swap12]
          exact h_reduced p₃ q₃ p₁ q₁ p₂ q₂ (by omega)
            hq₃ h2q₃ hub₃ hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ h3
      -- Now prove: if factor 1 has ratio > 7/3, then α ≤ 8
      intro p₁' q₁' p₂' q₂' p₃' q₃' hsum' _ _ _
        hq₁' h2q₁' hub₁' hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃' hbig₁'
      by_cases hcop : Nat.Coprime p₁' q₁'
      · exact alpha3_mixed_le_8_coprime_step IH p₁' q₁' p₂' q₂' p₃' q₃'
          hsum' hq₁' h2q₁' hub₁' hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃' hbig₁' hcop
      · -- Not coprime: GCD reduction
        set g := Nat.gcd p₁' q₁' with hg_def
        have hg_ne_zero : g ≠ 0 := by
          simp only [hg_def]; exact Nat.gcd_ne_zero_left (NeZero.ne p₁')
        have hg_gt1 : g > 1 := by
          simp only [Nat.Coprime] at hcop; omega
        have hg_pos : 0 < g := by omega
        have hg_dvd_p : g ∣ p₁' := hg_def ▸ Nat.gcd_dvd_left p₁' q₁'
        have hg_dvd_q : g ∣ q₁' := hg_def ▸ Nat.gcd_dvd_right p₁' q₁'
        set p₀ := p₁' / g with hp₀_def
        set q₀ := q₁' / g with hq₀_def
        have hp₁'_eq : p₁' = g * p₀ := by
          rw [hp₀_def, mul_comm]; exact (Nat.div_mul_cancel hg_dvd_p).symm
        have hq₁'_eq : q₁' = g * q₀ := by
          rw [hq₀_def, mul_comm]; exact (Nat.div_mul_cancel hg_dvd_q).symm
        have hp₀_pos : 0 < p₀ := by
          rw [hp₀_def]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_p) hg_pos
        have hp₀_lt : p₀ < p₁' := by
          calc p₀ = 1 * p₀ := (one_mul _).symm
            _ < g * p₀ := (Nat.mul_lt_mul_right hp₀_pos).mpr hg_gt1
            _ = p₁' := hp₁'_eq.symm
        have hq₀_pos : 0 < q₀ := by
          rw [hq₀_def]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_q) hg_pos
        have h2q₀ : 2 * q₀ ≤ p₀ := by
          have h := h2q₁'; rw [hp₁'_eq, hq₁'_eq] at h
          exact Nat.le_of_mul_le_mul_left (show g * (2 * q₀) ≤ g * p₀ by nlinarith) hg_pos
        have hub₀ : 2 * p₀ < 5 * q₀ := by
          have h := hub₁'; rw [hp₁'_eq, hq₁'_eq] at h
          exact lt_of_mul_lt_mul_left (show g * (2 * p₀) < g * (5 * q₀) by nlinarith)
            (Nat.zero_le g)
        haveI : NeZero p₀ := ⟨by omega⟩
        have hle_ratio : p₁' * q₀ ≤ p₀ * q₁' := by
          rw [hp₁'_eq, hq₁'_eq]; nlinarith
        have hcohom : fractionGraph p₁' q₁' ≤_G fractionGraph p₀ q₀ :=
          cohom_fractionGraph_monotone p₁' q₁' p₀ q₀
            hq₁' h2q₁' hq₀_pos h2q₀ hle_ratio
        calc _ ≤ (strongProduct (fractionGraph p₀ q₀)
              (strongProduct (fractionGraph p₂' q₂')
                (fractionGraph p₃' q₃'))).indepNum :=
              indepNum_strongProduct_le_of_cohom_left _ hcohom
          _ ≤ 8 := IH (p₀ + p₂' + p₃') (by omega) p₀ q₀ p₂' q₂' p₃' q₃'
                (le_refl _) hq₀_pos h2q₀ hub₀ hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃'

/-! ## Interval 2 infrastructure: mixed triple bound for [2, 8/3)

Analogous to `alpha3_mixed_le_8` but for the interval [2, 8/3) with bound 10.
Base case: all ratios ≤ 5/2 → α ≤ α(E_{5/2}³) ≤ 10 (from `alpha3_5o2_5o2_5o2_le`).
Inductive step: some ratio > 5/2 → coprime p₁ ≥ 13 > 12 ≥ α → numerator_bound.

Uses `alpha3_mixed_le_12` (from interval 3) as a stepping stone: α ≤ 12 < p₁. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Base case: if all three ratios ≤ 5/2, then α ≤ 10 (via factor-by-factor
    monotonicity to E_{5/2}³). -/
private lemma mixed_triple_le_of_all_le_5o2
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ) [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃)
    (hle₁ : 2 * p₁ ≤ 5 * q₁)
    (hle₂ : 2 * p₂ ≤ 5 * q₂)
    (hle₃ : 2 * p₃ ≤ 5 * q₃) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 10 := by
  calc _ ≤ (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum := by
        apply indepNum_strongProduct_le_of_cohom_left
        exact cohom_fractionGraph_monotone p₁ q₁ 5 2
          hq₁ h2q₁ (by omega) (by omega) (by nlinarith)
    _ ≤ (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph p₃ q₃))).indepNum := by
        have hcohom₂ := cohom_fractionGraph_monotone p₂ q₂ 5 2
          hq₂ h2q₂ (by omega) (by omega) (by nlinarith)
        have h_inner : strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃) ≤_G
            strongProduct (fractionGraph 5 2) (fractionGraph p₃ q₃) :=
          Cohom.strongProduct_left _ hcohom₂
        have h_outer : strongProduct (fractionGraph 5 2)
              (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃)) ≤_G
            strongProduct (fractionGraph 5 2)
              (strongProduct (fractionGraph 5 2) (fractionGraph p₃ q₃)) :=
          Cohom.strongProduct_right _ h_inner
        obtain ⟨f, hf⟩ := h_outer
        exact independenceNumber_le_of_cohomomorphism _ _ f hf
    _ ≤ (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 5 2))).indepNum := by
        have hcohom₃ := cohom_fractionGraph_monotone p₃ q₃ 5 2
          hq₃ h2q₃ (by omega) (by omega) (by nlinarith)
        have h_inner : strongProduct (fractionGraph 5 2) (fractionGraph p₃ q₃) ≤_G
            strongProduct (fractionGraph 5 2) (fractionGraph 5 2) :=
          Cohom.strongProduct_right _ hcohom₃
        have h_outer : strongProduct (fractionGraph 5 2)
              (strongProduct (fractionGraph 5 2) (fractionGraph p₃ q₃)) ≤_G
            strongProduct (fractionGraph 5 2)
              (strongProduct (fractionGraph 5 2) (fractionGraph 5 2)) :=
          Cohom.strongProduct_right _ h_inner
        obtain ⟨f, hf⟩ := h_outer
        exact independenceNumber_le_of_cohomomorphism _ _ f hf
    _ ≤ 10 := alpha3_5o2_5o2_5o2_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Coprime inductive step for interval 2: if p₁/q₁ > 5/2 and coprime,
    then p₁ ≥ 13 > 12 ≥ α (via alpha3_mixed_le_12), so numerator_bound applies. -/
private lemma alpha3_mixed_le_10_coprime_step
    {n : ℕ}
    (IH : ∀ m < n, ∀ p₁' q₁' p₂' q₂' p₃' q₃' : ℕ,
      p₁' + p₂' + p₃' ≤ m →
      [NeZero p₁'] → [NeZero p₂'] → [NeZero p₃'] →
      0 < q₁' → 2 * q₁' ≤ p₁' → 3 * p₁' < 8 * q₁' →
      0 < q₂' → 2 * q₂' ≤ p₂' → 3 * p₂' < 8 * q₂' →
      0 < q₃' → 2 * q₃' ≤ p₃' → 3 * p₃' < 8 * q₃' →
      (strongProduct (fractionGraph p₁' q₁')
        (strongProduct (fractionGraph p₂' q₂') (fractionGraph p₃' q₃'))).indepNum ≤ 10)
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hsum : p₁ + p₂ + p₃ ≤ n)
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hub₁ : 3 * p₁ < 8 * q₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂) (hub₂ : 3 * p₂ < 8 * q₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) (hub₃ : 3 * p₃ < 8 * q₃)
    (hbig₁ : 5 * q₁ < 2 * p₁)
    (hcop₁ : Nat.Coprime p₁ q₁) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 10 := by
  set α := (strongProduct (fractionGraph p₁ q₁)
    (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum
  -- Use alpha3_mixed_le_12: α ≤ 12 (since [2, 8/3) ⊂ [2, 11/4))
  have hα_le_12 : α ≤ 12 :=
    alpha3_mixed_le_12 (p₁ + p₂ + p₃) p₁ q₁ p₂ q₂ p₃ q₃ (le_refl _)
      hq₁ h2q₁ (by nlinarith) hq₂ h2q₂ (by nlinarith) hq₃ h2q₃ (by nlinarith)
  by_contra h_not_le
  push_neg at h_not_le
  -- p₁ ≥ 13 > 12 ≥ α (coprime p₁/q₁ ∈ (5/2, 8/3) forces q₁ ≥ 5, p₁ ≥ 13)
  have hp₁_ge : p₁ ≥ 13 := by omega
  have hq₁_ge2 : 2 ≤ q₁ := by omega
  obtain ⟨a, b, ha_pos, hb_pos, ha_lt_p₁, h2b_le_a, _, hab_lt, hα_ge⟩ :=
    numerator_bound p₁ q₁ p₂ q₂ p₃ q₃ hq₁_ge2 h2q₁ hcop₁
      hq₂ h2q₂ hq₃ h2q₃ (by omega : α < p₁)
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  have hub_a : 3 * a < 8 * b := by
    suffices h : (3 * a : ℚ) < 8 * b by exact_mod_cast h
    have hb_pos_rat : (0 : ℚ) < b := Nat.cast_pos.mpr hb_pos
    have hq₁_pos_rat : (0 : ℚ) < q₁ := Nat.cast_pos.mpr hq₁
    have hub₁_rat : (3 : ℚ) * p₁ < 8 * q₁ := by exact_mod_cast hub₁
    have h2 : (p₁ : ℚ) / q₁ < 8 / 3 := by
      rw [div_lt_div_iff₀ hq₁_pos_rat (by norm_num : (0:ℚ) < 3)]; linarith
    have h3 : (a : ℚ) / b < 8 / 3 := hab_lt.trans h2
    rw [div_lt_div_iff₀ hb_pos_rat (by norm_num : (0:ℚ) < 3)] at h3; linarith
  have h_IH := IH (a + p₂ + p₃) (by omega) a b p₂ q₂ p₃ q₃ (le_refl _)
    hb_pos h2b_le_a hub_a hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃
  have : α ≤ 10 := le_trans hα_ge h_IH
  omega

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Mixed triple bound for interval 2: for all triples with all ratios in [2, 8/3),
    α(E_{p₁/q₁} ⊠ (E_{p₂/q₂} ⊠ E_{p₃/q₃})) ≤ 10.
    Proved by strong induction on p₁ + p₂ + p₃. -/
private lemma alpha3_mixed_le_10 :
    ∀ n : ℕ, ∀ p₁ q₁ p₂ q₂ p₃ q₃ : ℕ,
    p₁ + p₂ + p₃ ≤ n →
    [NeZero p₁] → [NeZero p₂] → [NeZero p₃] →
    0 < q₁ → 2 * q₁ ≤ p₁ → 3 * p₁ < 8 * q₁ →
    0 < q₂ → 2 * q₂ ≤ p₂ → 3 * p₂ < 8 * q₂ →
    0 < q₃ → 2 * q₃ ≤ p₃ → 3 * p₃ < 8 * q₃ →
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 10 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro p₁ q₁ p₂ q₂ p₃ q₃ hsum _ _ _ hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃
    -- Case 1: All three ratios ≤ 5/2
    by_cases h_all_le : 2 * p₁ ≤ 5 * q₁ ∧ 2 * p₂ ≤ 5 * q₂ ∧ 2 * p₃ ≤ 5 * q₃
    · exact mixed_triple_le_of_all_le_5o2 p₁ q₁ p₂ q₂ p₃ q₃
        hq₁ h2q₁ hq₂ h2q₂ hq₃ h2q₃ h_all_le.1 h_all_le.2.1 h_all_le.2.2
    · -- Case 2: Some ratio > 5/2. Put it first via swap.
      simp only [not_and_or, not_le] at h_all_le
      suffices h_reduced : ∀ (p₁' q₁' p₂' q₂' p₃' q₃' : ℕ),
          p₁' + p₂' + p₃' ≤ n →
          [NeZero p₁'] → [NeZero p₂'] → [NeZero p₃'] →
          0 < q₁' → 2 * q₁' ≤ p₁' → 3 * p₁' < 8 * q₁' →
          0 < q₂' → 2 * q₂' ≤ p₂' → 3 * p₂' < 8 * q₂' →
          0 < q₃' → 2 * q₃' ≤ p₃' → 3 * p₃' < 8 * q₃' →
          5 * q₁' < 2 * p₁' →
          (strongProduct (fractionGraph p₁' q₁')
            (strongProduct (fractionGraph p₂' q₂')
              (fractionGraph p₃' q₃'))).indepNum ≤ 10 by
        rcases h_all_le with h1 | h2 | h3
        · exact h_reduced p₁ q₁ p₂ q₂ p₃ q₃ hsum
            hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃ h1
        · rw [indepNum_strongProduct_swap12]
          exact h_reduced p₂ q₂ p₁ q₁ p₃ q₃ (by omega)
            hq₂ h2q₂ hub₂ hq₁ h2q₁ hub₁ hq₃ h2q₃ hub₃ h2
        · rw [indepNum_strongProduct_swap23, indepNum_strongProduct_swap12]
          exact h_reduced p₃ q₃ p₁ q₁ p₂ q₂ (by omega)
            hq₃ h2q₃ hub₃ hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ h3
      -- Now prove: if factor 1 has ratio > 5/2, then α ≤ 10
      intro p₁' q₁' p₂' q₂' p₃' q₃' hsum' _ _ _
        hq₁' h2q₁' hub₁' hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃' hbig₁'
      by_cases hcop : Nat.Coprime p₁' q₁'
      · exact alpha3_mixed_le_10_coprime_step IH p₁' q₁' p₂' q₂' p₃' q₃'
          hsum' hq₁' h2q₁' hub₁' hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃' hbig₁' hcop
      · -- Not coprime: GCD reduction
        set g := Nat.gcd p₁' q₁' with hg_def
        have hg_ne_zero : g ≠ 0 := by
          simp only [hg_def]; exact Nat.gcd_ne_zero_left (NeZero.ne p₁')
        have hg_gt1 : g > 1 := by
          simp only [Nat.Coprime] at hcop; omega
        have hg_pos : 0 < g := by omega
        have hg_dvd_p : g ∣ p₁' := hg_def ▸ Nat.gcd_dvd_left p₁' q₁'
        have hg_dvd_q : g ∣ q₁' := hg_def ▸ Nat.gcd_dvd_right p₁' q₁'
        set p₀ := p₁' / g with hp₀_def
        set q₀ := q₁' / g with hq₀_def
        have hp₁'_eq : p₁' = g * p₀ := by
          rw [hp₀_def, mul_comm]; exact (Nat.div_mul_cancel hg_dvd_p).symm
        have hq₁'_eq : q₁' = g * q₀ := by
          rw [hq₀_def, mul_comm]; exact (Nat.div_mul_cancel hg_dvd_q).symm
        have hp₀_pos : 0 < p₀ := by
          rw [hp₀_def]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_p) hg_pos
        have hp₀_lt : p₀ < p₁' := by
          calc p₀ = 1 * p₀ := (one_mul _).symm
            _ < g * p₀ := (Nat.mul_lt_mul_right hp₀_pos).mpr hg_gt1
            _ = p₁' := hp₁'_eq.symm
        have hq₀_pos : 0 < q₀ := by
          rw [hq₀_def]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_q) hg_pos
        have h2q₀ : 2 * q₀ ≤ p₀ := by
          have h := h2q₁'; rw [hp₁'_eq, hq₁'_eq] at h
          exact Nat.le_of_mul_le_mul_left (show g * (2 * q₀) ≤ g * p₀ by nlinarith) hg_pos
        have hub₀ : 3 * p₀ < 8 * q₀ := by
          have h := hub₁'; rw [hp₁'_eq, hq₁'_eq] at h
          exact lt_of_mul_lt_mul_left (show g * (3 * p₀) < g * (8 * q₀) by nlinarith)
            (Nat.zero_le g)
        haveI : NeZero p₀ := ⟨by omega⟩
        have hle_ratio : p₁' * q₀ ≤ p₀ * q₁' := by
          rw [hp₁'_eq, hq₁'_eq]; nlinarith
        have hcohom : fractionGraph p₁' q₁' ≤_G fractionGraph p₀ q₀ :=
          cohom_fractionGraph_monotone p₁' q₁' p₀ q₀
            hq₁' h2q₁' hq₀_pos h2q₀ hle_ratio
        calc _ ≤ (strongProduct (fractionGraph p₀ q₀)
              (strongProduct (fractionGraph p₂' q₂')
                (fractionGraph p₃' q₃'))).indepNum :=
              indepNum_strongProduct_le_of_cohom_left _ hcohom
          _ ≤ 10 := IH (p₀ + p₂' + p₃') (by omega) p₀ q₀ p₂' q₂' p₃' q₃'
                (le_refl _) hq₀_pos h2q₀ hub₀ hq₂' h2q₂' hub₂' hq₃' h2q₃' hub₃'

/-! ## Public wrapper for `alpha3_mixed_le_10` (used by per-disc α₃ proofs)

`alpha3_mixed_le_10` is private to this file (induction-shaped). The wrapper
specializes the `n = p₁ + p₂ + p₃` case so callers don't need to mention the
induction parameter. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For all triples with each ratio in `[2, 8/3)`, `α(E_{p₁/q₁} ⊠ E_{p₂/q₂} ⊠
    E_{p₃/q₃}) ≤ 10`. Public wrapper around the private induction lemma
    `alpha3_mixed_le_10`. -/
theorem alpha3_le_10_of_lt_8o3 (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hub₁ : 3 * p₁ < 8 * q₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂) (hub₂ : 3 * p₂ < 8 * q₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) (hub₃ : 3 * p₃ < 8 * q₃) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 10 :=
  alpha3_mixed_le_10 (p₁ + p₂ + p₃) p₁ q₁ p₂ q₂ p₃ q₃ (le_refl _)
    hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For all triples with each ratio in `[2, 5/2)`, `α(E_{p₁/q₁} ⊠ E_{p₂/q₂} ⊠
    E_{p₃/q₃}) ≤ 8`. Public wrapper around the private induction lemma
    `alpha3_mixed_le_8`. Used by per-disc α₃ proofs (e.g., `(9/4, 7/3, 5/2)`)
    to bound configurations whose ratios are all strictly below `5/2`. -/
theorem alpha3_le_8_of_lt_5o2 (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hub₁ : 2 * p₁ < 5 * q₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂) (hub₂ : 2 * p₂ < 5 * q₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) (hub₃ : 2 * p₃ < 5 * q₃) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 8 :=
  alpha3_mixed_le_8 (p₁ + p₂ + p₃) p₁ q₁ p₂ q₂ p₃ q₃ (le_refl _)
    hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For all triples with each ratio in `[2, 11/4)`, `α(E_{p₁/q₁} ⊠ E_{p₂/q₂} ⊠
    E_{p₃/q₃}) ≤ 12`. Public wrapper around the private induction lemma
    `alpha3_mixed_le_12`. Used by per-disc α₃ proofs (e.g., `(11/4)³`)
    to bound configurations whose ratios are all strictly below `11/4`. -/
theorem alpha3_le_12_of_lt_11o4 (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hub₁ : 4 * p₁ < 11 * q₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂) (hub₂ : 4 * p₂ < 11 * q₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) (hub₃ : 4 * p₃ < 11 * q₃) :
    (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤ 12 :=
  alpha3_mixed_le_12 (p₁ + p₂ + p₃) p₁ q₁ p₂ q₂ p₃ q₃ (le_refl _)
    hq₁ h2q₁ hub₁ hq₂ h2q₂ hub₂ hq₃ h2q₃ hub₃

/-! ## Interval 1 and 2 theorems (proved using the infrastructure above) -/

/-- **Interval 1**: α(E_{p/q}^⊠3) = 8 for p/q ∈ [2, 5/2).

Upper bound: from `alpha3_mixed_le_8` via strong induction + Baumert for E_{7/3}³.
Lower bound: from monotonicity using α(E_2³) = 8 (`alpha3_2_2_2`). -/
theorem alpha3_diagonal_interval_1 (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) (h_ub : 2 * p < 5 * q) :
    (strongProduct (fractionGraph p q)
      (strongProduct (fractionGraph p q) (fractionGraph p q))).indepNum = 8 := by
  apply le_antisymm
  · exact alpha3_mixed_le_8 (p + p + p) p q p q p q (le_refl _)
      hq h2q h_ub hq h2q h_ub hq h2q h_ub
  · calc 8 = (strongProduct (fractionGraph 2 1)
        (strongProduct (fractionGraph 2 1) (fractionGraph 2 1))).indepNum :=
          alpha3_2_2_2.symm
      _ ≤ _ := alpha3_diagonal_monotone 2 1 p q (by omega) (by omega) hq h2q
          (by nlinarith)

/-- **Interval 2**: α(E_{p/q}^⊠3) = 10 for p/q ∈ [5/2, 8/3).

Requires upper bound via Baumert for C₅³ + mixed triple bound. -/
theorem alpha3_diagonal_interval_2 (p q : ℕ) [NeZero p]
    (hq : 0 < q)
    (h_lb : 5 * q ≤ 2 * p) (h_ub : 3 * p < 8 * q) :
    (strongProduct (fractionGraph p q)
      (strongProduct (fractionGraph p q) (fractionGraph p q))).indepNum = 10 := by
  have h2q : 2 * q ≤ p := by omega
  apply le_antisymm
  · exact alpha3_mixed_le_10 (p + p + p) p q p q p q (le_refl _)
      hq h2q h_ub hq h2q h_ub hq h2q h_ub
  · -- Lower bound: α(E_2 ⊠ E_{5/2}²) = 10, and E_2 ≤_G E_{5/2} ≤_G E_{p/q}
    calc 10 = (strongProduct (fractionGraph 2 1)
          (strongProduct (fractionGraph 5 2) (fractionGraph 5 2))).indepNum :=
            alpha3_2_5o2_5o2.symm
      _ ≤ (strongProduct (fractionGraph 5 2)
          (strongProduct (fractionGraph 5 2) (fractionGraph 5 2))).indepNum := by
            apply indepNum_strongProduct_le_of_cohom_left
            exact cohom_fractionGraph_monotone 2 1 5 2
              (by omega) (by omega) (by omega) (by omega) (by nlinarith)
      _ ≤ _ := alpha3_diagonal_monotone 5 2 p q (by omega) (by omega) hq h2q
            (by nlinarith)

/-! ## Left-associated wrappers for paper-API delegation (Main.lean)

Each `_main` wrapper restates an `alpha3_diagonal_*` theorem in the
left-associated form `(A ⊠ B ⊠ C).indepNum = N` (matching the paper-API shape
used by `Main.lean`), delegating via `indepNum_strongProduct_assoc`.

`alpha3_diagonal_point_3_main` additionally packages the sandwich proof
(monotonicity in both directions against `α₃(3, 3, 3) = 27`) used by
`Main.main_diagonal_point_3`. -/

/-- Left-assoc wrapper for `alpha3_diagonal_interval_1`. -/
theorem alpha3_diagonal_interval_1_main (p q : ℕ+)
    (h2q : 2 * q ≤ p) (h_ub : 2 * p < 5 * q) :
    (fractionGraph p q ⊠ fractionGraph p q ⊠ fractionGraph p q).indepNum = 8 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_diagonal_interval_1 p q q.pos h2q h_ub

/-- Left-assoc wrapper for `alpha3_diagonal_interval_2`. -/
theorem alpha3_diagonal_interval_2_main (p q : ℕ+)
    (h_lb : 5 * q ≤ 2 * p) (h_ub : 3 * p < 8 * q) :
    (fractionGraph p q ⊠ fractionGraph p q ⊠ fractionGraph p q).indepNum = 10 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_diagonal_interval_2 p q q.pos h_lb h_ub

/-- Left-assoc wrapper for `alpha3_diagonal_interval_3`. -/
theorem alpha3_diagonal_interval_3_main (p q : ℕ+)
    (h_lb : 8 * q ≤ 3 * p) (h_ub : 4 * p < 11 * q) :
    (fractionGraph p q ⊠ fractionGraph p q ⊠ fractionGraph p q).indepNum = 12 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_diagonal_interval_3 p q q.pos h_lb h_ub

/-- Left-assoc wrapper for `alpha3_diagonal_interval_4`. -/
theorem alpha3_diagonal_interval_4_main (p q : ℕ+)
    (h_lb : 11 * q ≤ 4 * p) (h_ub : 5 * p < 14 * q) :
    (fractionGraph p q ⊠ fractionGraph p q ⊠ fractionGraph p q).indepNum = 13 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_diagonal_interval_4 p q q.pos h_lb h_ub

/-- Left-assoc wrapper for `alpha3_diagonal_interval_5`. -/
theorem alpha3_diagonal_interval_5_main (p q : ℕ+)
    (h_lb : 14 * q ≤ 5 * p) (h_ub : p < 3 * q) :
    (fractionGraph p q ⊠ fractionGraph p q ⊠ fractionGraph p q).indepNum = 14 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_diagonal_interval_5 p q q.pos h_lb h_ub

/-- Left-assoc wrapper for the endpoint `p/q = 3`: `α(E_{p/q}^⊠3) = 27`.
    Sandwich proof via monotonicity against `alpha3_3_3_3` in both directions. -/
theorem alpha3_diagonal_point_3_main (p q : ℕ+) (hpq : p = 3 * q) :
    (fractionGraph p q ⊠ fractionGraph p q ⊠ fractionGraph p q).indepNum = 27 := by
  have hpq' : (p : ℕ) = 3 * (q : ℕ) := by rw [hpq]; rfl
  have h2q : 2 * (q : ℕ) ≤ p := by have := q.pos; omega
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  refine le_antisymm ?_ ?_
  · -- α(E_{p/q}^⊠3) ≤ α(E_{3/1}^⊠3) = 27 (monotone with p/q ≤ 3)
    calc _ ≤ (strongProduct (fractionGraph 3 1)
              (strongProduct (fractionGraph 3 1) (fractionGraph 3 1))).indepNum :=
          alpha3_diagonal_monotone p q 3 1 q.pos h2q
            (by omega) (by omega) (by omega)
      _ = 27 := alpha3_3_3_3
  · -- 27 = α(E_{3/1}^⊠3) ≤ α(E_{p/q}^⊠3) (monotone with 3 ≤ p/q)
    calc 27 = (strongProduct (fractionGraph 3 1)
              (strongProduct (fractionGraph 3 1) (fractionGraph 3 1))).indepNum :=
          alpha3_3_3_3.symm
      _ ≤ _ := alpha3_diagonal_monotone 3 1 p q (by omega) (by omega) q.pos h2q
            (by omega)

end Section6
