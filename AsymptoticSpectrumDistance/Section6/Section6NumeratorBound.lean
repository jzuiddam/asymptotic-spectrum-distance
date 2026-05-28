/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Lemma 6.13: Numerator Bound (k=3)

Contrapositive formulation: if max{p₁,...,p_k} > α_k(p₁/q₁,...,p_k/q_k),
then we can replace the largest fraction by a smaller one without decreasing α_k.

More precisely, for k=3: if p₁ > α₃(p₁/q₁, p₂/q₂, p₃/q₃), then there exist
a, b with a/b < p₁/q₁ and α₃(a/b, p₂/q₂, p₃/q₃) ≥ α₃(p₁/q₁, p₂/q₂, p₃/q₃).

## Proof strategy

1. **Pigeonhole**: The max IS S has |S| < p₁, so some v ∈ ZMod p₁ is not in π₁(S).
2. **Vertex removal**: By Lemma 6.6, E_{p₁/q₁}[V \ {v}] has cohoms to/from E_{a/b}.
3. **IS embedding**: Extend the partial cohom to a total map and show S maps
   injectively to an IS of E_{a/b} ⊠ (E_{p₂/q₂} ⊠ E_{p₃/q₃}).
4. **Conclude**: |S| ≤ α(E_{a/b} ⊠ ...).

## References

- Lemma 6.13
-/
import AsymptoticSpectrumDistance.Section3.FractionGraphs

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open ShannonCapacity Lemma66 FractionGraphBasic AsymptoticSpectrumDistance

namespace Section6

/-! ## Pigeonhole for product Finsets -/

/-- If S is a finset of pairs with |S| < p₁, then some element of ZMod p₁
    is not the first coordinate of any element of S. -/
lemma exists_fst_not_mem_image {X : Type*} [DecidableEq X]
    (p₁ : ℕ) [NeZero p₁]
    (S : Finset (ZMod p₁ × X)) (hS : S.card < p₁) :
    ∃ v : ZMod p₁, ∀ s ∈ S, s.1 ≠ v := by
  classical
  have himg_lt : (S.image Prod.fst).card < (Finset.univ : Finset (ZMod p₁)).card := by
    simp only [Finset.card_univ, ZMod.card]
    exact lt_of_le_of_lt Finset.card_image_le hS
  have hss : S.image Prod.fst ⊂ Finset.univ :=
    Finset.ssubset_univ_iff.mpr (Finset.card_lt_iff_ne_univ _ |>.mp himg_lt)
  obtain ⟨v, _, hv⟩ := Finset.exists_of_ssubset hss
  exact ⟨v, fun s hs hc => hv (Finset.mem_image.mpr ⟨s, hs, hc⟩)⟩

/-! ## IS embedding under partial cohomomorphism -/

/-- Core lemma: Given a partial cohomomorphism f on V \ {v} and an IS of
    strongProduct G₁ H that avoids v in the first coordinate, we can
    embed it into strongProduct G₂ H. -/
lemma indepNum_ge_of_partial_cohom
    {V W₁ W₂ : Type*} [Fintype V] [DecidableEq V]
    [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    {G₁ : SimpleGraph V} {G₂ : SimpleGraph W₁}
    (H : SimpleGraph W₂)
    (f : V → W₁) (v : V)
    (hf : ∀ u₁ u₂ : V, u₁ ≠ v → u₂ ≠ v → u₁ ≠ u₂ → ¬G₁.Adj u₁ u₂ →
          f u₁ ≠ f u₂ ∧ ¬G₂.Adj (f u₁) (f u₂))
    (S : Finset (V × W₂))
    (hS_indep : (strongProduct G₁ H).IsIndepSet ↑S)
    (hS_avoid : ∀ s ∈ S, s.1 ≠ v) :
    S.card ≤ (strongProduct G₂ H).indepNum := by
  classical
  -- Define φ = Prod.map f id
  let φ : V × W₂ → W₁ × W₂ := Prod.map f id
  -- Show φ is injective on S
  have hφ_inj : Set.InjOn φ ↑S := by
    intro ⟨x₁, y₁⟩ hxy₁ ⟨x₂, y₂⟩ hxy₂ heq
    simp only [φ, Prod.map, id] at heq
    obtain ⟨hf_eq, hy_eq⟩ := Prod.mk.inj heq
    -- Three cases on x₁ vs x₂
    by_cases hx_eq : x₁ = x₂
    · exact Prod.ext hx_eq hy_eq
    · -- x₁ ≠ x₂: use IS property to derive contradiction
      have hx₁_ne_v := hS_avoid ⟨x₁, y₁⟩ (Finset.mem_coe.mp hxy₁)
      have hx₂_ne_v := hS_avoid ⟨x₂, y₂⟩ (Finset.mem_coe.mp hxy₂)
      have hpair_ne : (x₁, y₁) ≠ (x₂, y₂) := by
        intro h; exact hx_eq (Prod.mk.inj h).1
      have hpair := (SimpleGraph.isIndepSet_iff _).1 hS_indep
        hxy₁ hxy₂ hpair_ne
      -- Not adjacent in strong product means ¬(adj_or_eq × adj_or_eq) or equal
      -- Since distinct and in IS, not adjacent in strongProduct
      -- Two sub-cases: either ¬(G₁.Adj x₁ x₂ ∨ x₁ = x₂) or ¬(H.Adj y₁ y₂ ∨ y₁ = y₂)
      -- Since x₁ ≠ x₂, (x₁ = x₂) is false. Check G₁.Adj:
      by_cases hadj : G₁.Adj x₁ x₂
      · -- If G₁.Adj x₁ x₂, then for non-adjacency in strongProduct we need
        -- ¬(H.Adj y₁ y₂ ∨ y₁ = y₂), i.e., y₁ ≠ y₂ ∧ ¬H.Adj y₁ y₂
        -- But hy_eq says y₁ = y₂, and adjacency in G₁ plus y₁ = y₂ gives
        -- strongProduct adjacency, contradicting IS
        exfalso; apply hpair
        exact ⟨hpair_ne, Or.inr hadj, Or.inl hy_eq⟩
      · -- ¬G₁.Adj x₁ x₂: IsCohom gives f x₁ ≠ f x₂
        exact absurd hf_eq (hf x₁ x₂ hx₁_ne_v hx₂_ne_v hx_eq hadj).1
  -- Show φ(S) is an IS of strongProduct G₂ H
  have hφS_indep : (strongProduct G₂ H).IsIndepSet ↑(S.image φ) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab hadj
    rw [Finset.coe_image] at ha hb
    obtain ⟨⟨x₁, y₁⟩, hxy₁, rfl⟩ := ha
    obtain ⟨⟨x₂, y₂⟩, hxy₂, rfl⟩ := hb
    simp only [φ, Prod.map, id, strongProduct] at hadj
    obtain ⟨_, h1, h2⟩ := hadj
    -- h1 : f x₁ = f x₂ ∨ G₂.Adj (f x₁) (f x₂)
    -- h2 : y₁ = y₂ ∨ H.Adj y₁ y₂
    have hx₁_ne_v := hS_avoid ⟨x₁, y₁⟩ hxy₁
    have hx₂_ne_v := hS_avoid ⟨x₂, y₂⟩ hxy₂
    have hpair_ne : (x₁, y₁) ≠ (x₂, y₂) := by
      intro h; apply hab; simp [φ, h]
    have hpair := (SimpleGraph.isIndepSet_iff _).1 hS_indep
      (Finset.mem_coe.mpr hxy₁) (Finset.mem_coe.mpr hxy₂) hpair_ne
    -- Non-adjacent in strongProduct G₁ H means
    -- ¬(hpair_ne ∧ (x₁=x₂ ∨ G₁.Adj) ∧ (y₁=y₂ ∨ H.Adj))
    -- i.e., ¬(x₁=x₂ ∨ G₁.Adj) ∨ ¬(y₁=y₂ ∨ H.Adj)
    by_cases hx_eq : x₁ = x₂
    · -- x₁ = x₂: then non-adj in product requires ¬(y₁ = y₂ ∨ H.Adj y₁ y₂)
      have hG₁_cond : x₁ = x₂ ∨ G₁.Adj x₁ x₂ := Or.inl hx_eq
      -- Since in IS, ¬Adj in strongProduct G₁ H, so ¬(y₁ = y₂ ∨ H.Adj y₁ y₂)
      have : ¬(y₁ = y₂ ∨ H.Adj y₁ y₂) := by
        intro hy_cond
        exact hpair ⟨hpair_ne, hG₁_cond, hy_cond⟩
      push_neg at this
      -- But h2 says y₁ = y₂ ∨ H.Adj y₁ y₂, contradiction
      exact this.2 (h2.elim (absurd · this.1) id)
    · -- x₁ ≠ x₂: check if G₁.Adj x₁ x₂
      by_cases hadj_G₁ : G₁.Adj x₁ x₂
      · -- G₁.Adj x₁ x₂: then non-adj in product requires ¬(y₁ = y₂ ∨ H.Adj y₁ y₂)
        have : ¬(y₁ = y₂ ∨ H.Adj y₁ y₂) := by
          intro hy_cond
          exact hpair ⟨hpair_ne, Or.inr hadj_G₁, hy_cond⟩
        push_neg at this
        exact this.2 (h2.elim (absurd · this.1) id)
      · -- ¬G₁.Adj x₁ x₂: IsCohom gives f x₁ ≠ f x₂ ∧ ¬G₂.Adj (f x₁) (f x₂)
        have ⟨hf_ne, hf_nadj⟩ := hf x₁ x₂ hx₁_ne_v hx₂_ne_v hx_eq hadj_G₁
        -- But h1 says f x₁ = f x₂ ∨ G₂.Adj (f x₁) (f x₂), contradiction
        exact (h1.elim (absurd · hf_ne) (absurd · hf_nadj))
  -- Conclude
  have hcard : (S.image φ).card = S.card := Finset.card_image_of_injOn hφ_inj
  calc S.card = (S.image φ).card := hcard.symm
    _ ≤ (strongProduct G₂ H).indepNum :=
        SimpleGraph.IsIndepSet.card_le_indepNum hφS_indep

/-! ## Main theorem: Numerator Bound -/

/-- Lemma 6.13 (contrapositive, k=3): If the independence number of
    E_{p₁/q₁} ⊠ (E_{p₂/q₂} ⊠ E_{p₃/q₃}) is less than p₁, then there exist
    a, b with a/b < p₁/q₁ such that replacing p₁/q₁ by a/b does not decrease
    the independence number. -/
theorem numerator_bound (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ)
    [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 2 ≤ q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hcop₁ : Nat.Coprime p₁ q₁)
    (_hq₂ : 0 < q₂) (_h2q₂ : 2 * q₂ ≤ p₂)
    (_hq₃ : 0 < q₃) (_h2q₃ : 2 * q₃ ≤ p₃)
    (hp₁_big : (strongProduct (fractionGraph p₁ q₁)
        (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum < p₁) :
    ∃ (a b : ℕ) (ha : 0 < a) (_hb : 0 < b),
      a < p₁ ∧ 2 * b ≤ a ∧ Nat.Coprime a b ∧
      (a : ℚ) / b < (p₁ : ℚ) / q₁ ∧
      haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
      (strongProduct (fractionGraph p₁ q₁)
          (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤
      (strongProduct (fractionGraph a b)
          (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum := by
  -- Abbreviate the graph
  set G := strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃)) with hG_def
  set H := strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃)
  -- Step 1: Get a maximum independent set S
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_indep : G.IsIndepSet ↑S := (SimpleGraph.isMaximumIndepSet_iff G S).1 hSmax |>.1
  have hS_card : S.card = G.indepNum :=
    SimpleGraph.maximumIndepSet_card_eq_indepNum S hSmax
  -- Step 2: Pigeonhole — find v not in first projection of S
  have hS_lt_p₁ : S.card < p₁ := hS_card ▸ hp₁_big
  obtain ⟨v, hv⟩ := exists_fst_not_mem_image p₁ S hS_lt_p₁
  -- Step 3: Vertex removal — get a, b and cohomomorphism
  have hp₁_pos : 0 < p₁ := NeZero.pos p₁
  have hq₁_pos : 0 < q₁ := by omega
  have hpq : q₁ < p₁ := Nat.lt_of_lt_of_le (by omega : q₁ < 2 * q₁) h2q₁
  obtain ⟨a, b, ha_pos, ha_lt_p₁, hb_pos, hb_lt_q₁, hbezout⟩ :=
    sternBrocotPredecessor_exists p₁ q₁ hp₁_pos hq₁ hcop₁ hpq
  haveI ha_ne : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  -- Step 4: Derive properties of a, b
  have hab_coprime : Nat.Coprime a b := coprime_p'_q' hbezout
  have hab_lt : (a : ℚ) / b < (p₁ : ℚ) / q₁ :=
    sternBrocot_predecessor_lt p₁ q₁ a b ha_lt_p₁ hb_lt_q₁ hb_pos hbezout
  -- Derive 2 * b ≤ a
  have ha_ge2 : 2 ≤ a := by
    by_contra ha_lt2
    push_neg at ha_lt2
    have ha_eq1 : a = 1 := by omega
    rw [ha_eq1] at hbezout
    have hpb : p₁ * b = q₁ + 1 := by omega
    have hb_le1 : b ≤ 1 := by
      have hle : p₁ * b ≤ p₁ * 1 := by
        calc p₁ * b = q₁ + 1 := hpb
          _ ≤ q₁ + q₁ := by omega
          _ = 2 * q₁ := by ring
          _ ≤ p₁ := h2q₁
          _ = p₁ * 1 := by ring
      exact Nat.le_of_mul_le_mul_left hle (by omega : 0 < p₁)
    have hb_eq1 : b = 1 := by omega
    rw [hb_eq1] at hpb; omega -- p₁ = q₁ + 1 contradicts 2 * q₁ ≤ p₁ when q₁ ≥ 2
  have h2b_le_a : 2 * b ≤ a :=
    two_q'_le_p'_of_bezout ha_pos ha_ge2 hb_pos hb_lt_q₁ hq₁ h2q₁ hbezout
  -- Step 5: Get the forward cohomomorphism (IsCohom, includes injectivity)
  -- Use fractionGraph_remove_vertex_equiv directly (it finds its own a', b')
  -- then identify them with a, b via uniqueness
  obtain ⟨a', b', ha'_pos, hb'_pos, ha'_lt, hb'_lt, hbezout',
    ⟨f_sub, hf_sub⟩, _⟩ :=
    fractionGraph_remove_vertex_equiv p₁ q₁ hq₁ h2q₁ hcop₁ v
  haveI : NeZero a' := ⟨Nat.pos_iff_ne_zero.mp ha'_pos⟩
  have ⟨ha'_eq, hb'_eq⟩ := sternBrocotPredecessor_unique p₁ q₁ a' b' a b hcop₁
    ha'_pos ha'_lt hb'_pos hb'_lt ha_pos ha_lt_p₁ hb_pos hb_lt_q₁ hbezout' hbezout
  -- f_sub : {x : ZMod p₁ | x ≠ v} → ZMod a' is IsCohom
  -- Since a' = a and b' = b, we can cast
  -- Extend to total function
  let f' : ZMod p₁ → ZMod a := fun x =>
    if h : x = v then 0
    else ha'_eq ▸ f_sub ⟨x, h⟩
  -- Build the partial cohom property for f'
  have hf'_partial : ∀ u₁ u₂ : ZMod p₁, u₁ ≠ v → u₂ ≠ v → u₁ ≠ u₂ →
      ¬(fractionGraph p₁ q₁).Adj u₁ u₂ →
      f' u₁ ≠ f' u₂ ∧ ¬(fractionGraph a b).Adj (f' u₁) (f' u₂) := by
    intro u₁ u₂ hu₁ hu₂ hne hnadj
    simp only [f', hu₁, hu₂, dif_neg, not_false_eq_true]
    have hne_sub : (⟨u₁, hu₁⟩ : {x : ZMod p₁ | x ≠ v}) ≠ ⟨u₂, hu₂⟩ := by
      intro h; exact hne (Subtype.mk.inj h)
    have hnadj_ind : ¬((fractionGraph p₁ q₁).induce {x : ZMod p₁ | x ≠ v}).Adj
        ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ := by
      simp only [SimpleGraph.induce_adj, Set.mem_setOf_eq, ne_eq]
      exact fun hadj => hnadj hadj
    have h := hf_sub ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ hne_sub hnadj_ind
    subst ha'_eq; subst hb'_eq
    exact h
  -- Apply indepNum_ge_of_partial_cohom
  have hbound := indepNum_ge_of_partial_cohom H f' v hf'_partial S hS_indep hv
  -- Package result
  use a, b, ha_pos, hb_pos, ha_lt_p₁, h2b_le_a, hab_coprime, hab_lt
  calc G.indepNum = S.card := hS_card.symm
    _ ≤ (strongProduct (fractionGraph a b) H).indepNum := hbound

end Section6
