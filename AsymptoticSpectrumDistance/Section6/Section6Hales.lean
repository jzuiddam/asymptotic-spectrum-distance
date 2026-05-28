/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Hales Inequality for Strong Products

Proves the Hales inequality: for any graph G with a fractional clique cover of weight W
and any graph H, α(G ⊠ H) ≤ W · α(H).

As an immediate corollary (since α is a natural number):
α(G ⊠ H) ≤ ⌊W · α(H)⌋₊.

## Proof idea

Take a maximum independent set S in G ⊠ H. For each clique C in the cover of G,
the projection of S onto the H-coordinate for pairs with first coordinate in C
is an independent set in H of size ≤ α(H). Double-counting (switching the order
of summation) gives |S| ≤ W · α(H).

## Main results

- `hales_inequality_real`: α(G ⊠ H) ≤ W · α(H) as reals
- `hales_inequality`: α(G ⊠ H) ≤ ⌊W · α(H)⌋₊
-/
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.StrongProduct

open ShannonCapacity

namespace Section6

/-! ## Hales inequality -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Hales inequality** (real-valued version).

For any graph G with a fractional clique cover of weight ≤ W, and any graph H:
  α(G ⊠ H) ≤ W · α(H)

This generalizes `independenceNumber_le_of_clique_cover` from the base graph to the
strong product. The key additional ingredient is that each clique of G induces at most
α(H) pairs in any independent set of G ⊠ H (via the second-coordinate projection). -/
theorem hales_inequality_real {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (cliques : Finset (Finset V)) (weights : Finset V → ℝ)
    (hclique : ∀ C ∈ cliques, G.IsClique C)
    (hpos : ∀ C ∈ cliques, weights C ≥ 0)
    (hcover : ∀ v : V, (cliques.filter (v ∈ ·)).sum weights ≥ 1)
    (CW : ℝ) (hCW : cliques.sum weights ≤ CW) :
    ((strongProduct G H).indepNum : ℝ) ≤ CW * H.indepNum := by
  classical
  -- Degenerate case
  by_cases hCW_nonneg : CW < 0
  · linarith [Finset.sum_nonneg (fun C (hC : C ∈ cliques) => hpos C hC)]
  push_neg at hCW_nonneg
  -- Take a maximum independent set S in G ⊠ H
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := strongProduct G H)
  have hS_indep : (strongProduct G H).IsIndepSet (S : Set (V × W)) :=
    (SimpleGraph.isMaximumIndepSet_iff _ S).1 hSmax |>.1
  have hS_pairwise := (SimpleGraph.isIndepSet_iff _).1 hS_indep
  have hS_card : S.card = (strongProduct G H).indepNum :=
    SimpleGraph.maximumIndepSet_card_eq_indepNum S hSmax
  -- Key lemma: for each clique C, |{p ∈ S : p.1 ∈ C}| ≤ α(H)
  have hproj : ∀ C ∈ cliques,
      (S.filter (fun p => p.1 ∈ C)).card ≤ H.indepNum := by
    intro C hC
    set SC := S.filter (fun p => p.1 ∈ C)
    -- π₂ is injective on SC (if two pairs have the same second coord and
    -- first coords in a clique, they'd be adjacent, contradicting independence)
    have hinj : Set.InjOn Prod.snd (SC : Set (V × W)) := by
      intro a ha b hb heq
      simp only [SC, Finset.mem_coe, Finset.mem_filter] at ha hb
      have h2 : a.2 = b.2 := heq
      have h1 : a.1 = b.1 := by
        by_contra hne
        exact hS_pairwise (by simpa using ha.1) (by simpa using hb.1)
          (fun h => hne (congr_arg Prod.fst h))
          ⟨fun h => hne (congr_arg Prod.fst h),
           Or.inr (hclique C hC ha.2 hb.2 hne), Or.inl h2⟩
      exact Prod.ext h1 h2
    -- The image SC.image Prod.snd is independent in H
    have himage_indep : H.IsIndepSet (↑(SC.image Prod.snd) : Set W) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro w₁ hw₁ w₂ hw₂ hne hadj
      rw [Finset.mem_coe, Finset.mem_image] at hw₁ hw₂
      obtain ⟨a, ha, rfl⟩ := hw₁
      obtain ⟨b, hb, rfl⟩ := hw₂
      simp only [SC, Finset.mem_filter] at ha hb
      have hne_ab : a ≠ b := fun h => hne (congr_arg Prod.snd h)
      have : a.1 = b.1 ∨ G.Adj a.1 b.1 := by
        by_cases heq : a.1 = b.1
        · left; exact heq
        · right; exact hclique C hC ha.2 hb.2 heq
      exact hS_pairwise (by simpa using ha.1) (by simpa using hb.1) hne_ab
        ⟨hne_ab, this, Or.inr hadj⟩
    -- Combine: |SC| = |image| ≤ α(H)
    calc SC.card
        = (SC.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ H.indepNum := SimpleGraph.IsIndepSet.card_le_indepNum himage_indep
  -- Double counting (left side): |S| ≤ Σ_{p∈S} Σ_{C∋p.1} w_C
  have hleft : (S.card : ℝ) ≤
      S.sum (fun p => (cliques.filter (p.1 ∈ ·)).sum weights) := by
    calc (S.card : ℝ) = S.sum (fun _ => (1 : ℝ)) := by simp
      _ ≤ S.sum (fun p => (cliques.filter (p.1 ∈ ·)).sum weights) :=
        Finset.sum_le_sum fun p _ => hcover p.1
  -- Double counting (right side): Σ_{p∈S} Σ_{C∋p.1} w_C ≤ W · α(H)
  have hright : S.sum (fun p => (cliques.filter (p.1 ∈ ·)).sum weights) ≤
      CW * H.indepNum := by
    calc S.sum (fun p => (cliques.filter (p.1 ∈ ·)).sum weights)
        = S.sum (fun p => cliques.sum
            (fun C => if p.1 ∈ C then weights C else 0)) := by
          congr 1; ext p; rw [Finset.sum_filter]
      _ = cliques.sum (fun C => S.sum
            (fun p => if p.1 ∈ C then weights C else 0)) :=
          Finset.sum_comm
      _ = cliques.sum (fun C =>
            weights C * (S.filter (fun p => p.1 ∈ C)).card) := by
          congr 1; ext C
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ cliques.sum (fun C => weights C * H.indepNum) := by
          apply Finset.sum_le_sum; intro C hC
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hproj C hC) (hpos C hC)
      _ = cliques.sum weights * H.indepNum := by
          rw [← Finset.sum_mul]
      _ ≤ CW * H.indepNum :=
          mul_le_mul_of_nonneg_right hCW (by positivity)
  -- Combine
  calc ((strongProduct G H).indepNum : ℝ)
      = (S.card : ℝ) := by exact_mod_cast hS_card.symm
    _ ≤ S.sum (fun p => (cliques.filter (p.1 ∈ ·)).sum weights) := hleft
    _ ≤ CW * H.indepNum := hright

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Hales inequality** (natural number version with floor).

α(G ⊠ H) ≤ ⌊W · α(H)⌋₊ for any fractional clique cover of G with weight ≤ W. -/
theorem hales_inequality {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (cliques : Finset (Finset V)) (weights : Finset V → ℝ)
    (hclique : ∀ C ∈ cliques, G.IsClique C)
    (hpos : ∀ C ∈ cliques, weights C ≥ 0)
    (hcover : ∀ v : V, (cliques.filter (v ∈ ·)).sum weights ≥ 1)
    (CW : ℝ) (hCW : cliques.sum weights ≤ CW) :
    (strongProduct G H).indepNum ≤ ⌊CW * H.indepNum⌋₊ := by
  apply Nat.le_floor
  exact_mod_cast hales_inequality_real G H cliques weights hclique hpos hcover CW hCW

end Section6
