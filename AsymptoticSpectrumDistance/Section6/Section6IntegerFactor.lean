/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Integer Factor Lemma for Strong Products

Proves that α(E_{n/1} ⊠ G) = n · α(G) for any graph G and n ≥ 2.

E_{n/1} is the edgeless graph on ZMod n (since distMod ≥ 1 for distinct vertices),
so the strong product E_{n/1} ⊠ G decomposes into n independent copies of G.

## Main results

- `fractionGraph_one_not_adj`: E_{n/1} has no edges
- `fractionGraph_one_indepNum`: α(E_{n/1}) = n
- `indepNum_strongProduct_edgeless_fraction`: α(E_{n/1} ⊠ G) = n · α(G)
-/
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor

open ShannonCapacity

namespace Section6

/-- E_{n/1} has no edges: for distinct u, v in ZMod n, distMod n u v ≥ 1 > 0. -/
private lemma fractionGraph_one_not_adj (n : ℕ) [NeZero n]
    (u v : ZMod n) : ¬(fractionGraph n 1).Adj u v := by
  intro ⟨huv, hd⟩
  simp only [distMod] at hd
  have hpos : 0 < (u - v).val := by
    rw [Nat.pos_iff_ne_zero]
    intro h; exact huv (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h))
  have hsub : 0 < n - (u - v).val := Nat.sub_pos_of_lt (ZMod.val_lt _)
  omega

/-- α(E_{n/1}) = n: the edgeless fraction graph has independence number equal to its size. -/
theorem fractionGraph_one_indepNum (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (fractionGraph n 1).indepNum = n := by
  apply le_antisymm
  · calc (fractionGraph n 1).indepNum
        ≤ ⌊(n : ℝ) / (1 : ℕ)⌋₊ := fractionGraph_indepNum_le n 1 (by omega) hn
      _ = n := by simp
  · have h_indep : (fractionGraph n 1).IsIndepSet
        (↑(Finset.univ : Finset (ZMod n)) : Set (ZMod n)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro a _ b _ _ hadj
      exact fractionGraph_one_not_adj n a b hadj
    calc n = (Finset.univ : Finset (ZMod n)).card := by simp [ZMod.card]
      _ ≤ (fractionGraph n 1).indepNum :=
        SimpleGraph.IsIndepSet.card_le_indepNum h_indep

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{n/1} ⊠ G) = n · α(G) for n ≥ 2.

Upper bound from the Hales inequality with χ̄_f(E_{n/1}) = n.
Lower bound from n disjoint copies of a maximum independent set of G. -/
theorem indepNum_strongProduct_edgeless_fraction
    {W : Type*} [Fintype W] [DecidableEq W]
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (G : SimpleGraph W) :
    (strongProduct (fractionGraph n 1) G).indepNum = n * G.indepNum := by
  apply le_antisymm
  · -- Upper bound: Hales inequality with fractional clique cover
    obtain ⟨cliques, weights, hclique, hpos, hcover, hsum⟩ :=
      fractionalCliqueCover_fractionGraph n 1 (by omega) hn
    have h := hales_inequality (fractionGraph n 1) G cliques weights
      hclique hpos hcover (n : ℝ) (by simpa using hsum)
    rwa [show (n : ℝ) * (G.indepNum : ℝ) = ↑(n * G.indepNum) from by push_cast; ring,
      Nat.floor_natCast] at h
  · -- Lower bound: Finset.univ ×ˢ S independent, card = n * α(G)
    classical
    obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
    have hS_indep : G.IsIndepSet (S : Set W) :=
      (SimpleGraph.isMaximumIndepSet_iff G S).1 hSmax |>.1
    have hS_card : S.card = G.indepNum :=
      SimpleGraph.maximumIndepSet_card_eq_indepNum S hSmax
    set T : Finset (ZMod n × W) := Finset.univ ×ˢ S
    have hT_card : T.card = n * G.indepNum := by
      simp [T, Finset.card_product, ZMod.card, hS_card]
    have hT_indep : (strongProduct (fractionGraph n 1) G).IsIndepSet
        (↑T : Set (ZMod n × W)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne hadj
      rw [Finset.mem_coe, Finset.mem_product] at ha hb
      obtain ⟨_, h_fst, h_snd⟩ := hadj
      rcases h_fst with h_eq | h_adj
      · have hne2 : a.2 ≠ b.2 := fun h => hne (Prod.ext h_eq h)
        rcases h_snd with h_eq2 | h_adj2
        · exact hne2 h_eq2
        · exact (SimpleGraph.isIndepSet_iff G).1 hS_indep
            (Finset.mem_coe.mpr ha.2) (Finset.mem_coe.mpr hb.2) hne2 h_adj2
      · exact fractionGraph_one_not_adj n a.1 b.1 h_adj
    calc n * G.indepNum
        = T.card := hT_card.symm
      _ ≤ (strongProduct (fractionGraph n 1) G).indepNum :=
        SimpleGraph.IsIndepSet.card_le_indepNum hT_indep

end Section6
