/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shared Infrastructure for the Section 6 Baumert Slicing Bridges

This file collects the small helper lemmas that are shared between two or more of
the per-bridge files in `Section6UpperBoundsBridge_*.lean`.

It is the common base that every bridge file imports. Helpers used by exactly one
bridge live with that bridge.

## Contents

* `fiber_bound_clique` — the core lemma underlying the Baumert slicing technique.
* `floor_val` — small numeric helper for `Nat.floor`.
* `fractionGraph_adj_translate` — translation invariance of `fractionGraph`
  adjacency.
* `alpha_*` lemmas: `α(G ⊠ H) = …` for the various `G ⊠ H` arising as the inner
  fiber bound in some bridge.
* `*_clique_E*` lemmas: `{i, i+1, …}` is a clique of `E_{p/q}`.
* `five_distinct_zmod13`, `ip_uniform13` — shared IP infrastructure for the
  bound-#7/#8/#9 family.
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Fiber bound lemma

The key lemma enabling the Baumert slicing technique: for any IS S in G ⊠ H and
any clique C of G, the C-fiber {p ∈ S : p.1 ∈ C} has cardinality ≤ α(H).

This formalizes the observation from [BMRRS, Computation]: "any packing of the
p³-torus may be considered as the juxtaposition of p packings for the p²-torus"
— more precisely, it bounds the number of elements in the independent set whose
first coordinate lies in any given clique of G, by showing the second coordinates
form an independent set in H.

This is also the basis for the Hales inequality (`hales_inequality` in
Section6Hales.lean), which gives the nested floor bound. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For any IS S in G ⊠ H and clique C of G,
    |{p ∈ S : p.1 ∈ C}| ≤ α(H). -/
lemma fiber_bound_clique {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (S : Finset (V × W)) (hS : (strongProduct G H).IsIndepSet ↑S)
    (C : Finset V) (hC : G.IsClique ↑C) :
    (S.filter (fun p => p.1 ∈ C)).card ≤ H.indepNum := by
  classical
  have hS_pw := (SimpleGraph.isIndepSet_iff _).1 hS
  set SC := S.filter (fun p => p.1 ∈ C)
  have hinj : Set.InjOn Prod.snd (SC : Set (V × W)) := by
    intro a ha b hb heq
    simp only [SC, Finset.mem_coe, Finset.mem_filter] at ha hb
    have h2 : a.2 = b.2 := heq
    have h1 : a.1 = b.1 := by
      by_contra hne
      exact hS_pw (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1)
        (fun h => hne (congr_arg Prod.fst h))
        ⟨fun h => hne (congr_arg Prod.fst h),
         Or.inr (hC (Finset.mem_coe.mpr ha.2) (Finset.mem_coe.mpr hb.2) hne),
         Or.inl h2⟩
    exact Prod.ext h1 h2
  have himage : H.IsIndepSet (↑(SC.image Prod.snd) : Set W) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro w₁ hw₁ w₂ hw₂ hne hadj
    rw [Finset.mem_coe, Finset.mem_image] at hw₁ hw₂
    obtain ⟨a, ha, rfl⟩ := hw₁; obtain ⟨b, hb, rfl⟩ := hw₂
    simp only [SC, Finset.mem_filter] at ha hb
    exact hS_pw (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1)
      (fun h => hne (congr_arg Prod.snd h))
      ⟨fun h => hne (congr_arg Prod.snd h),
       if heq : a.1 = b.1 then Or.inl heq
       else Or.inr (hC (Finset.mem_coe.mpr ha.2) (Finset.mem_coe.mpr hb.2) heq),
       Or.inr hadj⟩
  calc SC.card = (SC.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ H.indepNum := SimpleGraph.IsIndepSet.card_le_indepNum himage

/-! ## Numeric and translation helpers -/

/-- Small helper for `Nat.floor`: if `n ≤ a < n + 1` and `0 ≤ a` then `⌊a⌋₊ = n`. -/
lemma floor_val {a : ℝ} {n : ℕ} (ha : 0 ≤ a)
    (h_le : (n : ℝ) ≤ a) (h_lt : a < (n : ℝ) + 1) :
    ⌊a⌋₊ = n :=
  (Nat.floor_eq_iff ha).mpr ⟨h_le, by exact_mod_cast h_lt⟩

/-- Translation invariance of `fractionGraph` adjacency (right-addition variant;
thin wrapper around the canonical `FractionGraphBasic.fractionGraph_adj_add_left`,
which states the same identity for left-addition). -/
lemma fractionGraph_adj_translate (p q : ℕ) [NeZero p] (a b δ : ZMod p) :
    (fractionGraph p q).Adj (a + δ) (b + δ) ↔ (fractionGraph p q).Adj a b := by
  rw [add_comm a δ, add_comm b δ]; exact fractionGraph_adj_add_left p q δ a b

/-! ## α-values used as fiber bounds across bridges -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{8/3}²) = 5, used for the fiber bound in the Baumert argument. -/
lemma alpha_8o3_sq :
    (strongProduct (fractionGraph 8 3) (fractionGraph 8 3)).indepNum = 5 := by
  rw [theorem_6_5 8 3 8 3 (by omega) (by omega) (by omega) (by omega)]
  push_cast; simp only [min_self]
  have h1 : ⌊(8:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1]; push_cast
  exact floor_val (by positivity) (by norm_num) (by norm_num)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{5/2} ⊠ E_{8/3}) = 5, used for the fiber bound. -/
lemma alpha_5o2_8o3 :
    (strongProduct (fractionGraph 5 2) (fractionGraph 8 3)).indepNum = 5 := by
  rw [theorem_6_5 5 2 8 3 (by omega) (by omega) (by omega) (by omega)]
  push_cast
  have h1 : ⌊(8:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h2 : ⌊(5:ℝ)/2⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1, h2]; push_cast
  have h3 : ⌊(5:ℝ)/2 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h4 : ⌊(8:ℝ)/3 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h3, h4]; simp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{7/3}²) = 4, used for the fiber bound in the Baumert argument. -/
lemma alpha_7o3_sq :
    (strongProduct (fractionGraph 7 3) (fractionGraph 7 3)).indepNum = 4 := by
  rw [theorem_6_5 7 3 7 3 (by omega) (by omega) (by omega) (by omega)]
  push_cast; simp only [min_self]
  have h1 : ⌊(7:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1]; push_cast
  exact floor_val (by positivity) (by norm_num) (by norm_num)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(C₅²) = 5, used for the fiber bound in the C₅³ Baumert argument. -/
lemma alpha_5o2_sq :
    (strongProduct (fractionGraph 5 2) (fractionGraph 5 2)).indepNum = 5 := by
  rw [theorem_6_5 5 2 5 2 (by omega) (by omega) (by omega) (by omega)]
  push_cast; simp only [min_self]
  have h1 : ⌊(5:ℝ)/2⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1]; push_cast
  exact floor_val (by positivity) (by norm_num) (by norm_num)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{9/4} ⊠ E_{5/2}) = 4, used for the fiber bound in the case 9
    Baumert argument. -/
lemma alpha_9o4_5o2 :
    (strongProduct (fractionGraph 9 4) (fractionGraph 5 2)).indepNum = 4 := by
  rw [theorem_6_5 9 4 5 2 (by omega) (by omega) (by omega) (by omega)]
  push_cast
  have h1 : ⌊(9:ℝ)/4⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h2 : ⌊(5:ℝ)/2⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1, h2]; push_cast
  have h3 : ⌊(9:ℝ)/4 * 2⌋₊ = 4 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h4 : ⌊(5:ℝ)/2 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h3, h4]; simp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{9/4} ⊠ E_{8/3}) = 4, used for the fiber bound in the (9/4, 9/4, 8/3)
    Baumert argument. min(⌊2·8/3⌋, ⌊2·9/4⌋) = min(5, 4) = 4. -/
lemma alpha_9o4_8o3 :
    (strongProduct (fractionGraph 9 4) (fractionGraph 8 3)).indepNum = 4 := by
  rw [theorem_6_5 9 4 8 3 (by omega) (by omega) (by omega) (by omega)]
  push_cast
  have h1 : ⌊(9:ℝ)/4⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h2 : ⌊(8:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1, h2]; push_cast
  have h3 : ⌊(9:ℝ)/4 * 2⌋₊ = 4 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h4 : ⌊(8:ℝ)/3 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h3, h4]; simp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{5/2} ⊠ E_{11/4}) = 5, used for the fiber bound in the
    (5/2, 5/2, 11/4) mixed Baumert argument. -/
lemma alpha_5o2_11o4 :
    (strongProduct (fractionGraph 5 2) (fractionGraph 11 4)).indepNum = 5 := by
  rw [theorem_6_5 5 2 11 4 (by omega) (by omega) (by omega) (by omega)]
  push_cast
  have h1 : ⌊(5:ℝ)/2⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h2 : ⌊(11:ℝ)/4⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1, h2]; push_cast
  have h3 : ⌊(5:ℝ)/2 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h4 : ⌊(11:ℝ)/4 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h3, h4]; simp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{8/3} ⊠ E_{11/4}) = 5, used for the fiber bound in bound #7. -/
lemma alpha_8o3_11o4 :
    (strongProduct (fractionGraph 8 3) (fractionGraph 11 4)).indepNum = 5 := by
  rw [theorem_6_5 8 3 11 4 (by omega) (by omega) (by omega) (by omega)]
  push_cast
  have h1 : ⌊(8:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h2 : ⌊(11:ℝ)/4⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1, h2]; push_cast
  have h3 : ⌊(8:ℝ)/3 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  have h4 : ⌊(11:ℝ)/4 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h3, h4]; simp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{11/4}²) = 5, used for the fiber bound in bound #8. -/
lemma alpha_11o4_sq :
    (strongProduct (fractionGraph 11 4) (fractionGraph 11 4)).indepNum = 5 := by
  rw [theorem_6_5 11 4 11 4 (by omega) (by omega) (by omega) (by omega)]
  push_cast; simp only [min_self]
  have h1 : ⌊(11:ℝ)/4⌋₊ = 2 :=
    floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1]; push_cast
  exact floor_val (by positivity) (by norm_num) (by norm_num)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{11/4} ⊠ E_{13/5}) = 5, used for the fiber bound in bound #9. -/
lemma alpha_11o4_13o5 :
    (strongProduct (fractionGraph 11 4) (fractionGraph 13 5)).indepNum = 5 := by
  rw [theorem_6_5 11 4 13 5 (by omega) (by omega) (by omega) (by omega)]
  push_cast
  have h1 : ⌊(11:ℝ)/4⌋₊ = 2 :=
    floor_val (by positivity) (by norm_num) (by norm_num)
  have h2 : ⌊(13:ℝ)/5⌋₊ = 2 :=
    floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1, h2]; push_cast
  have h3 : ⌊(11:ℝ)/4 * 2⌋₊ = 5 :=
    floor_val (by positivity) (by norm_num) (by norm_num)
  have h4 : ⌊(13:ℝ)/5 * 2⌋₊ = 5 :=
    floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h3, h4]; simp

/-! ## Cycle-clique lemmas: `{i, i+1, …}` is a clique of `E_{p/q}` -/

set_option linter.style.nativeDecide false in
/-- {i, i+1, i+2} is a clique of E_{8/3} for all i. -/
lemma three_clique_E83 (i : ZMod 8) :
    (fractionGraph 8 3).IsClique ↑({i, i + 1, i + 2} : Finset (ZMod 8)) := by
  have h0 : (fractionGraph 8 3).IsClique ↑({(0 : ZMod 8), 1, 2} : Finset (ZMod 8)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    refine ⟨hab, ?_⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | native_decide
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  have hfg := (fractionGraph_adj_translate 8 3 (a - i) (b - i) i).mpr
  simp only [sub_add_cancel] at hfg
  apply hfg; apply h0
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl <;> simp [sub_self, add_sub_cancel_left]
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases hb with rfl | rfl | rfl <;> simp [sub_self, add_sub_cancel_left]
  · intro heq; exact hab (by calc a = (a - i) + i := by ring
                                   _ = (b - i) + i := by rw [heq]
                                   _ = b := by ring)

set_option linter.style.nativeDecide false in
/-- {i, i+1, i+2} is a clique of E_{7/3} for all i. -/
lemma three_clique_E73 (i : ZMod 7) :
    (fractionGraph 7 3).IsClique ↑({i, i + 1, i + 2} : Finset (ZMod 7)) := by
  have h0 :
      (fractionGraph 7 3).IsClique
        ↑({(0 : ZMod 7), 1, 2} : Finset (ZMod 7)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    refine ⟨hab, ?_⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | native_decide
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  have hfg := (fractionGraph_adj_translate 7 3 (a - i) (b - i) i).mpr
  simp only [sub_add_cancel] at hfg
  apply hfg; apply h0
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl <;> simp [sub_self, add_sub_cancel_left]
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases hb with rfl | rfl | rfl <;> simp [sub_self, add_sub_cancel_left]
  · intro heq; exact hab (by calc a = (a - i) + i := by ring
                                   _ = (b - i) + i := by rw [heq]
                                   _ = b := by ring)

set_option linter.style.nativeDecide false in
/-- {i, i+1} is a clique of E_{5/2} for all i. -/
lemma edge_clique_E52 (i : ZMod 5) :
    (fractionGraph 5 2).IsClique ↑({i, i + 1} : Finset (ZMod 5)) := by
  have h0 : (fractionGraph 5 2).IsClique ↑({(0 : ZMod 5), 1} : Finset (ZMod 5)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    refine ⟨hab, ?_⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first | exact absurd rfl hab | native_decide
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  have hfg := (fractionGraph_adj_translate 5 2 (a - i) (b - i) i).mpr
  simp only [sub_add_cancel] at hfg
  apply hfg; apply h0
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl <;> simp [sub_self, add_sub_cancel_left]
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases hb with rfl | rfl <;> simp [sub_self, add_sub_cancel_left]
  · intro heq; exact hab (by calc a = (a - i) + i := by ring
                                   _ = (b - i) + i := by rw [heq]
                                   _ = b := by ring)

set_option linter.style.nativeDecide false in
/-- {i, i+1, i+2, i+3} is a clique of E_{9/4} for all i. -/
lemma four_clique_E94 (i : ZMod 9) :
    (fractionGraph 9 4).IsClique
      ↑({i, i + 1, i + 2, i + 3} : Finset (ZMod 9)) := by
  have h0 : (fractionGraph 9 4).IsClique
      ↑({(0 : ZMod 9), 1, 2, 3} : Finset (ZMod 9)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    refine ⟨hab, ?_⟩
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hab | native_decide
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  have hfg := (fractionGraph_adj_translate 9 4 (a - i) (b - i) i).mpr
  simp only [sub_add_cancel] at hfg
  apply hfg; apply h0
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl | rfl <;> simp [sub_self, add_sub_cancel_left]
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases hb with rfl | rfl | rfl | rfl <;> simp [sub_self, add_sub_cancel_left]
  · intro heq; exact hab (by calc a = (a - i) + i := by ring
                                   _ = (b - i) + i := by rw [heq]
                                   _ = b := by ring)

set_option linter.style.nativeDecide false in
/-- {i, i+1, i+2, i+3, i+4} is a clique of E_{13/5} for all i. -/
lemma five_clique_E135 (i : ZMod 13) :
    (fractionGraph 13 5).IsClique
      ↑({i, i + 1, i + 2, i + 3, i + 4} : Finset (ZMod 13)) := by
  have h0 : (fractionGraph 13 5).IsClique
      ↑({(0 : ZMod 13), 1, 2, 3, 4} : Finset (ZMod 13)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    refine ⟨hab, ?_⟩
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hab | native_decide
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  have hfg := (fractionGraph_adj_translate 13 5 (a - i) (b - i) i).mpr
  simp only [sub_add_cancel] at hfg
  apply hfg; apply h0
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      simp [sub_self, add_sub_cancel_left]
  · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      simp [sub_self, add_sub_cancel_left]
  · intro heq; exact hab (by calc a = (a - i) + i := by ring
                                   _ = (b - i) + i := by rw [heq]
                                   _ = b := by ring)

/-! ## ZMod 13 IP infrastructure (shared between bounds #7, #8, #9) -/

set_option linter.style.nativeDecide false in
/-- Consecutive offsets 0,1,2,3,4 are pairwise distinct in ZMod 13. -/
lemma five_distinct_zmod13 (i : ZMod 13) :
    i ≠ i + 1 ∧ i ≠ i + 2 ∧ i ≠ i + 3 ∧ i ≠ i + 4 ∧
    (i + 1 : ZMod 13) ≠ i + 2 ∧ (i + 1 : ZMod 13) ≠ i + 3 ∧
    (i + 1 : ZMod 13) ≠ i + 4 ∧
    (i + 2 : ZMod 13) ≠ i + 3 ∧ (i + 2 : ZMod 13) ≠ i + 4 ∧
    (i + 3 : ZMod 13) ≠ i + 4 := by
  revert i; decide

/-- Layer sizes satisfying sum=13 and all cyclic 5-windows ≤ 5 are uniformly 1.
    Proof: each window sums to exactly 5 (sum of all 13 windows = 5·13 = 65,
    bound is 13·5 = 65, slack 0). Hence s(i) = s(i+5) (sliding window).
    Since gcd(5, 13) = 1, all s(i) are equal. Then 13·s(0) = 13, so s(0) = 1.

    Generic over the inner graph; reused for bounds #7, #8, #9. -/
lemma ip_uniform13 (s : ZMod 13 → ℕ)
    (hsum : ∑ i : ZMod 13, s i = 13)
    (hquint : ∀ i : ZMod 13,
      s i + s (i + 1) + s (i + 2) + s (i + 3) + s (i + 4) ≤ 5) :
    ∀ i : ZMod 13, s i = 1 := by
  -- Total sum of all 13 cyclic 5-window sums = 5·(total) = 5·13 = 65.
  -- This equals 13·5 (the upper bound), so each window sums to exactly 5.
  -- Sum of windows
  have hsum_windows : ∑ i : ZMod 13,
      (s i + s (i + 1) + s (i + 2) + s (i + 3) + s (i + 4)) = 65 := by
    have h_eq : ∀ k : ZMod 13,
        (∑ i : ZMod 13, s (i + k)) = ∑ i : ZMod 13, s i := by
      intro k
      have := Equiv.sum_comp (Equiv.addRight k) s
      simpa [Equiv.addRight] using this
    simp only [Finset.sum_add_distrib, h_eq, hsum]
  -- Each window equals 5 exactly
  have hwin5 : ∀ i : ZMod 13,
      s i + s (i + 1) + s (i + 2) + s (i + 3) + s (i + 4) = 5 := by
    intro i
    by_contra hne
    have hlt : s i + s (i + 1) + s (i + 2) + s (i + 3) + s (i + 4) < 5 := by
      have := hquint i; omega
    have hlt' : ∑ j : ZMod 13,
        (s j + s (j + 1) + s (j + 2) + s (j + 3) + s (j + 4)) < 65 := by
      calc ∑ j : ZMod 13,
            (s j + s (j + 1) + s (j + 2) + s (j + 3) + s (j + 4))
          = (s i + s (i + 1) + s (i + 2) + s (i + 3) + s (i + 4)) +
            ∑ j ∈ Finset.univ.erase i,
              (s j + s (j + 1) + s (j + 2) + s (j + 3) + s (j + 4)) := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
        _ ≤ 4 + ∑ j ∈ Finset.univ.erase i,
              (s j + s (j + 1) + s (j + 2) + s (j + 3) + s (j + 4)) := by
            apply Nat.add_le_add_right; omega
        _ ≤ 4 + ∑ j ∈ Finset.univ.erase i, 5 := by
            apply Nat.add_le_add_left
            apply Finset.sum_le_sum
            intro j _; exact hquint j
        _ = 4 + 12 * 5 := by simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
        _ = 64 := by norm_num
        _ < 65 := by norm_num
    omega
  -- Two consecutive windows give s(i) = s(i+5).
  have hshift : ∀ i : ZMod 13, s i = s (i + 5) := by
    intro i
    have h1 := hwin5 i
    have h2 := hwin5 (i + 1)
    have he1 : i + 1 + 1 = i + 2 := by ring
    have he2 : i + 1 + 2 = i + 3 := by ring
    have he3 : i + 1 + 3 = i + 4 := by ring
    have he4 : i + 1 + 4 = i + 5 := by ring
    rw [he1, he2, he3, he4] at h2
    omega
  -- gcd(5,13)=1 ⇒ all s(j) equal s(0). The orbit of 0 under +5 in ZMod 13:
  -- 0, 5, 10, 15=2, 20=7, 25=12, 30=4, 35=9, 40=1, 45=6, 50=11, 55=3, 60=8, 65=0.
  have hall_eq : ∀ j : ZMod 13, s j = s 0 := by
    intro j
    -- enumerate the orbit explicitly
    have h0 : s (5 : ZMod 13) = s 0 := by
      have := hshift 0; simp at this; omega
    have h1 : s (10 : ZMod 13) = s 0 := by
      have h := hshift 5; rw [h0] at h
      have : (5 + 5 : ZMod 13) = 10 := by decide
      rw [this] at h; omega
    have h2 : s (2 : ZMod 13) = s 0 := by
      have h := hshift 10; rw [h1] at h
      have : (10 + 5 : ZMod 13) = 2 := by decide
      rw [this] at h; omega
    have h3 : s (7 : ZMod 13) = s 0 := by
      have h := hshift 2; rw [h2] at h
      have : (2 + 5 : ZMod 13) = 7 := by decide
      rw [this] at h; omega
    have h4 : s (12 : ZMod 13) = s 0 := by
      have h := hshift 7; rw [h3] at h
      have : (7 + 5 : ZMod 13) = 12 := by decide
      rw [this] at h; omega
    have h5 : s (4 : ZMod 13) = s 0 := by
      have h := hshift 12; rw [h4] at h
      have : (12 + 5 : ZMod 13) = 4 := by decide
      rw [this] at h; omega
    have h6 : s (9 : ZMod 13) = s 0 := by
      have h := hshift 4; rw [h5] at h
      have : (4 + 5 : ZMod 13) = 9 := by decide
      rw [this] at h; omega
    have h7 : s (1 : ZMod 13) = s 0 := by
      have h := hshift 9; rw [h6] at h
      have : (9 + 5 : ZMod 13) = 1 := by decide
      rw [this] at h; omega
    have h8 : s (6 : ZMod 13) = s 0 := by
      have h := hshift 1; rw [h7] at h
      have : (1 + 5 : ZMod 13) = 6 := by decide
      rw [this] at h; omega
    have h9 : s (11 : ZMod 13) = s 0 := by
      have h := hshift 6; rw [h8] at h
      have : (6 + 5 : ZMod 13) = 11 := by decide
      rw [this] at h; omega
    have h10 : s (3 : ZMod 13) = s 0 := by
      have h := hshift 11; rw [h9] at h
      have : (11 + 5 : ZMod 13) = 3 := by decide
      rw [this] at h; omega
    have h11 : s (8 : ZMod 13) = s 0 := by
      have h := hshift 3; rw [h10] at h
      have : (3 + 5 : ZMod 13) = 8 := by decide
      rw [this] at h; omega
    fin_cases j
    · rfl
    · exact h7
    · exact h2
    · exact h10
    · exact h5
    · exact h0
    · exact h8
    · exact h3
    · exact h11
    · exact h6
    · exact h1
    · exact h9
    · exact h4
  -- 13·s(0) = 13, so s(0) = 1
  have hsum0 : 13 * s 0 = 13 := by
    have heq : ∑ j : ZMod 13, s j = ∑ _j : ZMod 13, s 0 :=
      Finset.sum_congr rfl (fun j _ => hall_eq j)
    have hcard : (Finset.univ : Finset (ZMod 13)).card = 13 := by decide
    rw [heq] at hsum
    rw [Finset.sum_const, hcard, smul_eq_mul] at hsum
    exact hsum
  have hs0 : s 0 = 1 := by omega
  intro i; rw [hall_eq i, hs0]

/-! ## Case 8 IP infrastructure (shared between the case 8, 8/3²·11/4 and
    8/3·11/4² bridges) -/

set_option linter.style.nativeDecide false in
/-- Consecutive elements `i, i+1, i+2` are distinct in `ZMod 8`. -/
lemma three_distinct_zmod8 (i : ZMod 8) :
    i ≠ i + 1 ∧ i ≠ i + 2 ∧ (i + 1 : ZMod 8) ≠ i + 2 := by
  revert i; decide

/-- Case 8 canonical layer sizes: `(1,2,1,2,2,1,2,2)`. -/
def canonical_sizes : Fin 8 → ℕ
  | 0 => 1 | 1 => 2 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 1 | 6 => 2 | 7 => 2

/-- Is `s` a rotation of the case 8 canonical size vector? -/
def is_rotation_of_canonical (s : Fin 8 → ℕ) : Bool :=
  (List.finRange 8).any fun k =>
    (List.finRange 8).all fun i =>
      s i == canonical_sizes ⟨(i.val + k.val) % 8, Nat.mod_lt _ (by omega)⟩

set_option linter.style.nativeDecide false in
/-- Finite version of the case 8 IP rotation lemma, proved by `native_decide`. -/
lemma ip_rotation_fin6 :
    ∀ s : Fin 8 → Fin 6,
    (Finset.univ.sum fun i => (s i).val) = 13 →
    (∀ i : Fin 8,
      (s i).val + (s ⟨(i.val + 1) % 8, Nat.mod_lt _ (by omega)⟩).val +
      (s ⟨(i.val + 2) % 8, Nat.mod_lt _ (by omega)⟩).val ≤ 5) →
    ∃ k : Fin 8, ∀ i : Fin 8,
      (s i).val = canonical_sizes ⟨(i.val + k.val) % 8, Nat.mod_lt _ (by omega)⟩ := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Layer sizes satisfying sum=13 and triple≤5 are a rotation of
    `(1,2,1,2,2,1,2,2)`. -/
lemma ip_rotation (s : Fin 8 → ℕ)
    (hsum : ∑ i : Fin 8, s i = 13)
    (htrip : ∀ i : Fin 8,
      s i + s ⟨(i.val + 1) % 8, Nat.mod_lt _ (by omega)⟩ +
      s ⟨(i.val + 2) % 8, Nat.mod_lt _ (by omega)⟩ ≤ 5) :
    ∃ k : Fin 8, ∀ i : Fin 8,
      s i = canonical_sizes ⟨(i.val + k.val) % 8, Nat.mod_lt _ (by omega)⟩ := by
  have hle : ∀ i : Fin 8, s i ≤ 5 := fun i => by have := htrip i; omega
  let s' : Fin 8 → Fin 6 := fun i => ⟨s i, by have := hle i; omega⟩
  have hsum' : (Finset.univ.sum fun i => (s' i).val) = 13 := hsum
  have htrip' : ∀ i : Fin 8,
      (s' i).val + (s' ⟨(i.val + 1) % 8, Nat.mod_lt _ (by omega)⟩).val +
      (s' ⟨(i.val + 2) % 8, Nat.mod_lt _ (by omega)⟩).val ≤ 5 := by
    intro i; simp only [s']; exact htrip i
  obtain ⟨k, hk⟩ := ip_rotation_fin6 s' hsum' htrip'
  exact ⟨k, fun i => by have := hk i; simp only [s'] at this; exact this⟩

/-! ## Case 7 IP infrastructure (shared between the case 7 and 5/2·8/3² bridges) -/

set_option linter.style.nativeDecide false in
/-- Consecutive elements `i, i+1` are distinct in `ZMod 5`. -/
lemma two_distinct_zmod5 (i : ZMod 5) : i ≠ i + 1 := by
  revert i; decide

/-- Case 7 canonical layer sizes: `(2,2,3,2,3)`. -/
def canonical_sizes7 : Fin 5 → ℕ
  | 0 => 2 | 1 => 2 | 2 => 3 | 3 => 2 | 4 => 3

/-- Is `s` a rotation of the case 7 canonical size vector? -/
def is_rotation_of_canonical7 (s : Fin 5 → ℕ) : Bool :=
  (List.finRange 5).any fun k =>
    (List.finRange 5).all fun i =>
      s i == canonical_sizes7 ⟨(i.val + k.val) % 5, Nat.mod_lt _ (by omega)⟩

set_option linter.style.nativeDecide false in
/-- Finite version of the case 7 IP rotation lemma. -/
lemma ip_rotation7_fin6 :
    ∀ s : Fin 5 → Fin 6,
    (Finset.univ.sum fun i => (s i).val) = 12 →
    (∀ i : Fin 5,
      (s i).val + (s ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩).val ≤ 5) →
    ∃ k : Fin 5, ∀ i : Fin 5,
      (s i).val = canonical_sizes7 ⟨(i.val + k.val) % 5, Nat.mod_lt _ (by omega)⟩ := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Layer sizes satisfying sum=12 and pair≤5 are a rotation of `(2,2,3,2,3)`. -/
lemma ip_rotation7 (s : Fin 5 → ℕ)
    (hsum : ∑ i : Fin 5, s i = 12)
    (hpair : ∀ i : Fin 5,
      s i + s ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩ ≤ 5) :
    ∃ k : Fin 5, ∀ i : Fin 5,
      s i = canonical_sizes7 ⟨(i.val + k.val) % 5, Nat.mod_lt _ (by omega)⟩ := by
  have hle : ∀ i : Fin 5, s i ≤ 5 := fun i => by have := hpair i; omega
  let s' : Fin 5 → Fin 6 := fun i => ⟨s i, by have := hle i; omega⟩
  have hsum' : (Finset.univ.sum fun i => (s' i).val) = 12 := hsum
  have hpair' : ∀ i : Fin 5,
      (s' i).val + (s' ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩).val ≤ 5 := by
    intro i; simp only [s']; exact hpair i
  obtain ⟨k, hk⟩ := ip_rotation7_fin6 s' hsum' hpair'
  exact ⟨k, fun i => by have := hk i; simp only [s'] at this; exact this⟩

end Section6
