/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Section 6 Baumert Bridge: α(E_{8/3} ⊠ E_{11/4} ⊠ E_{13/5}) ≤ 12 (alpha3_83_114_135_le)

Bridge file split off from `Section6UpperBounds.lean`.

See `Section6UpperBoundsCommon` for the shared infrastructure
(`fiber_bound_clique`, `floor_val`, `alpha_*`, `*_clique_E*`, etc.).
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_135
import Mathlib.Data.Bool.AllAny
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Mixed-multiset Baumert bridge: α(E_{8/3} ⊠ E_{11/4} ⊠ E_{13/5}) ≤ 12

Bound #7 of paper Theorem 6.9 case 11 (the (11/4, 11/4, 11/4) discontinuity at
α₃ = 13). The nested floor bound gives α ≤ 13. The Baumert slicing technique
with WLOG translation by `Z₈ × Z₁₁` (a symmetry of E_{8/3} ⊠ E_{11/4})
bringing the unique element of layer 0 to `(0,0)` rules out α = 13. See
`caseMixed83_114_135_check_true`.

Slicing analysis: slice by the E_{13/5} coordinate, giving 13 layers in
E_{8/3} ⊠ E_{11/4} (88 verts, α = 5). The 5-clique {i,…,i+4} of E_{13/5}
gives 5-window sum ≤ 5. Sum of 13 cyclic 5-window constraints = 5·13 = 65,
equal to max 13·5 = 65. Tight: every window sums to exactly 5, forcing all
13 layer sizes equal (gcd(5,13)=1), hence all = 1. -/


/-- The fiber of S over a single layer i (bound #7, Z₁₃ layers,
    inner Z₈×Z₁₁). -/
private def layerFiber13_88 (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11)))
    (i : ZMod 13) :=
  S.filter (fun p => p.1 = i)

private lemma layerFiber13_88_disjoint
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11)))
    (i j : ZMod 13) (hij : i ≠ j) :
    Disjoint (layerFiber13_88 S i) (layerFiber13_88 S j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [layerFiber13_88, Finset.mem_filter] at hx hy
  exact hij (hx.2 ▸ hy.2)

private lemma layer13_88_sum_eq_card
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11))) :
    ∑ i : ZMod 13, (layerFiber13_88 S i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [layerFiber13_88, Finset.mem_biUnion, Finset.mem_univ,
      Finset.mem_filter, true_and]
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x.1, h, rfl⟩⟩
  · intro i _ j _ hij
    exact layerFiber13_88_disjoint S i j hij

private lemma quintuple_filter_eq13_88
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11))) (i : ZMod 13) :
    S.filter (fun p =>
      p.1 ∈ ({i, i + 1, i + 2, i + 3, i + 4} : Finset (ZMod 13))) =
    layerFiber13_88 S i ∪ layerFiber13_88 S (i + 1) ∪
      layerFiber13_88 S (i + 2) ∪ layerFiber13_88 S (i + 3) ∪
      layerFiber13_88 S (i + 4) := by
  ext x; simp only [layerFiber13_88, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto


private lemma quintuple_bound_sum13
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11))) (i : ZMod 13)
    (hfbc : (S.filter (fun p =>
      p.1 ∈ ({i, i + 1, i + 2, i + 3, i + 4} : Finset (ZMod 13)))).card ≤ 5) :
    (layerFiber13_88 S i).card + (layerFiber13_88 S (i + 1)).card +
    (layerFiber13_88 S (i + 2)).card + (layerFiber13_88 S (i + 3)).card +
    (layerFiber13_88 S (i + 4)).card ≤ 5 := by
  rw [quintuple_filter_eq13_88] at hfbc
  obtain ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ :=
    five_distinct_zmod13 i
  have d12 : Disjoint (layerFiber13_88 S i) (layerFiber13_88 S (i + 1)) :=
    layerFiber13_88_disjoint S _ _ h01
  have h_u12 := Finset.card_union_of_disjoint d12
  have d3_with_12 :
      Disjoint (layerFiber13_88 S i ∪ layerFiber13_88 S (i + 1))
        (layerFiber13_88 S (i + 2)) := by
    rw [Finset.disjoint_union_left]
    exact ⟨layerFiber13_88_disjoint S _ _ h02,
      layerFiber13_88_disjoint S _ _ h12⟩
  have h_u123 := Finset.card_union_of_disjoint d3_with_12
  have d4_with_123 :
      Disjoint (layerFiber13_88 S i ∪ layerFiber13_88 S (i + 1) ∪
        layerFiber13_88 S (i + 2)) (layerFiber13_88 S (i + 3)) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact layerFiber13_88_disjoint S _ _ h03
    · exact layerFiber13_88_disjoint S _ _ h13
    · exact layerFiber13_88_disjoint S _ _ h23
  have h_u1234 := Finset.card_union_of_disjoint d4_with_123
  have d5_with_1234 :
      Disjoint (layerFiber13_88 S i ∪ layerFiber13_88 S (i + 1) ∪
        layerFiber13_88 S (i + 2) ∪ layerFiber13_88 S (i + 3))
        (layerFiber13_88 S (i + 4)) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left,
        Finset.disjoint_union_left]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact layerFiber13_88_disjoint S _ _ h04
    · exact layerFiber13_88_disjoint S _ _ h14
    · exact layerFiber13_88_disjoint S _ _ h24
    · exact layerFiber13_88_disjoint S _ _ h34
  have h_u12345 := Finset.card_union_of_disjoint d5_with_1234
  linarith


/-- Translate S by shifting the inner two coordinates (bound #7,
    Z₈ × Z₁₁). -/
private def translateSnd83_114 (δ : ZMod 8 × ZMod 11)
    (x : ZMod 13 × (ZMod 8 × ZMod 11)) : ZMod 13 × (ZMod 8 × ZMod 11) :=
  (x.1, (x.2.1 + δ.1, x.2.2 + δ.2))

private lemma translateSnd83_114_injective (δ : ZMod 8 × ZMod 11) :
    Function.Injective (translateSnd83_114 δ) := by
  intro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [translateSnd83_114, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext h1 (Prod.ext (add_right_cancel h2) (add_right_cancel h3))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Inner-coordinate translation preserves the IS property (bound #7). -/
private lemma translateSnd83_114_IS (δ : ZMod 8 × ZMod 11)
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11)))
    (hIS : (strongProduct (fractionGraph 13 5)
      (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 13 5)
      (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))).IsIndepSet
      ↑(S.image (translateSnd83_114 δ)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2, a3⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2, b3⟩, hb, rfl⟩ := hy
  simp only [translateSnd83_114] at hne hadj
  have hne' : (a1, a2, a3) ≠ (b1, b2, b3) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg (Prod.fst ∘ Prod.snd) h
    have h3 : a3 = b3 := congr_arg (Prod.snd ∘ Prod.snd) h
    subst h1; subst h2; subst h3; exact hne rfl
  obtain ⟨_, h_first, h_inner⟩ := hadj
  have h_inner_back : (a2, a3) = (b2, b3) ∨ (strongProduct (fractionGraph 8 3)
      (fractionGraph 11 4)).Adj (a2, a3) (b2, b3) := by
    rcases h_inner with heq | ⟨hne_shifted, h2_or, h3_or⟩
    · left
      have e2 : a2 + δ.1 = b2 + δ.1 := congr_arg Prod.fst heq
      have e3 : a3 + δ.2 = b3 + δ.2 := congr_arg Prod.snd heq
      exact Prod.ext (add_right_cancel e2) (add_right_cancel e3)
    · right
      have hne_inner : (a2, a3) ≠ (b2, b3) := fun h => by
        have h2 : a2 = b2 := congr_arg Prod.fst h
        have h3 : a3 = b3 := congr_arg Prod.snd h
        apply hne_shifted
        exact Prod.ext (h2 ▸ rfl) (h3 ▸ rfl)
      refine ⟨hne_inner, ?_, ?_⟩
      · exact h2_or.imp (fun h => add_right_cancel h)
          (fractionGraph_adj_translate 8 3 a2 b2 δ.1).mp
      · exact h3_or.imp (fun h => add_right_cancel h)
          (fractionGraph_adj_translate 11 4 a3 b3 δ.2).mp
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', h_first, h_inner_back⟩

private lemma translateSnd83_114_layerFiber (δ : ZMod 8 × ZMod 11)
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11))) (i : ZMod 13) :
    (layerFiber13_88 (S.image (translateSnd83_114 δ)) i).card =
    (layerFiber13_88 S i).card := by
  have : layerFiber13_88 (S.image (translateSnd83_114 δ)) i =
      (layerFiber13_88 S i).image (translateSnd83_114 δ) := by
    ext ⟨j, a, b⟩
    simp only [layerFiber13_88, Finset.mem_filter, Finset.mem_image,
      translateSnd83_114]
    constructor
    · rintro ⟨⟨⟨i', a', b'⟩, hi', heq⟩, hj⟩
      have h1 : i' = j := congr_arg Prod.fst heq
      have h2 : a' + δ.1 = a := congr_arg (Prod.fst ∘ Prod.snd) heq
      have h3 : b' + δ.2 = b := congr_arg (Prod.snd ∘ Prod.snd) heq
      refine ⟨⟨i', a', b'⟩, ⟨hi', h1.trans hj⟩, ?_⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · rintro ⟨⟨i', a', b'⟩, ⟨hi', heq⟩, htr⟩
      have h1 : i' = j := congr_arg Prod.fst htr
      have h2 : a' + δ.1 = a := congr_arg (Prod.fst ∘ Prod.snd) htr
      have h3 : b' + δ.2 = b := congr_arg (Prod.snd ∘ Prod.snd) htr
      exact ⟨⟨⟨i', a', b'⟩, hi', Prod.ext h1 (Prod.ext h2 h3)⟩, h1 ▸ heq⟩
  rw [this, Finset.card_image_of_injective _ (translateSnd83_114_injective δ)]

set_option linter.style.nativeDecide false in
/-- Bridge: `crossNonAdj83_114 a b = true` iff the formal adj-or-eq condition
    fails for E_{8/3} ⊠ E_{11/4}. -/
private lemma crossNonAdj83_114_spec (a b : ZMod 8 × ZMod 11) :
    crossNonAdj83_114 a b = true ↔
    ¬((a.1 = b.1 ∨ (fractionGraph 8 3).Adj a.1 b.1) ∧
      (a.2 = b.2 ∨ (fractionGraph 11 4).Adj a.2 b.2)) := by
  revert a b; native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- From IS property and first-coordinate adj-or-eq, derive
    crossNonAdj83_114. -/
private lemma cross_compat_of_IS_83_114
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11)))
    (hIS : (strongProduct (fractionGraph 13 5)
      (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))).IsIndepSet ↑S)
    (x y : ZMod 13 × (ZMod 8 × ZMod 11))
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h1 : x.1 = y.1 ∨ (fractionGraph 13 5).Adj x.1 y.1) :
    crossNonAdj83_114 x.2 y.2 = true := by
  rw [crossNonAdj83_114_spec]
  intro ⟨hc1, hc2⟩
  have hnadj : ¬(strongProduct (fractionGraph 13 5)
      (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))).Adj x y :=
    (SimpleGraph.isIndepSet_iff _).mp hIS
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  apply hnadj
  refine ⟨hxy, h1, ?_⟩
  by_cases heq : x.2 = y.2
  · exact Or.inl heq
  · refine Or.inr ⟨heq, hc1, hc2⟩

/-- Extract the unique witness from a single-element layer (bound #7). -/
private lemma extract_single_from_layer13_88
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11))) (i : ZMod 13)
    (hcard : (layerFiber13_88 S i).card = 1) :
    ∃ a : ZMod 8 × ZMod 11, (i, a) ∈ S := by
  obtain ⟨⟨j, a⟩, hja⟩ := Finset.card_pos.mp
    (by omega : 0 < (layerFiber13_88 S i).card)
  rw [layerFiber13_88, Finset.mem_filter] at hja
  exact ⟨a, hja.2 ▸ hja.1⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.nativeDecide false in
/-- Bound #7 mixed-multiset Baumert contradiction: an IS of size 13 in
    E_{8/3} ⊠ E_{11/4} ⊠ E_{13/5} satisfying the 5-window fiber bound 5
    cannot exist. -/
private lemma case83_114_135_baumert_contradiction
    (S : Finset (ZMod 13 × (ZMod 8 × ZMod 11)))
    (hSis : (strongProduct (fractionGraph 13 5)
      (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))).IsIndepSet ↑S)
    (hScard : S.card = 13)
    (hfbc : ∀ i : ZMod 13,
      (S.filter (fun p =>
        p.1 ∈ ({i, i + 1, i + 2, i + 3, i + 4} : Finset (ZMod 13)))).card ≤ 5) :
    False := by
  -- Layer sizes are all 1 (no rotation needed; the IP forces uniform 1)
  have hsize : ∀ j : ZMod 13, (layerFiber13_88 S j).card = 1 := by
    apply ip_uniform13 (fun i => (layerFiber13_88 S i).card)
    · rw [layer13_88_sum_eq_card]; exact hScard
    · intro i; exact quintuple_bound_sum13 S i (hfbc i)
  -- Extract the unique witness in layer 0
  obtain ⟨w0₁, hw0₁⟩ := extract_single_from_layer13_88 S 0 (hsize 0)
  -- Translate so that w0 = (0, 0): inner shift δ = (-w0₁.1, -w0₁.2)
  let δ : ZMod 8 × ZMod 11 := (-w0₁.1, -w0₁.2)
  set S' := S.image (translateSnd83_114 δ) with hS'_def
  have hIS' := translateSnd83_114_IS δ S hSis
  have hsize' : ∀ j : ZMod 13, (layerFiber13_88 S' j).card = 1 := by
    intro j
    rw [translateSnd83_114_layerFiber δ S j]
    exact hsize j
  -- Cross-compat
  have hcc := cross_compat_of_IS_83_114 S' hIS'
  have hne_layer : ∀ (i j : ZMod 13) (a b : ZMod 8 × ZMod 11),
      i ≠ j → (i, a) ≠ (j, b) :=
    fun _ _ _ _ hij h => hij (congr_arg Prod.fst h)
  have cc : ∀ (i j : ZMod 13) (a b : ZMod 8 × ZMod 11),
      (i, a) ∈ S' → (j, b) ∈ S' → i ≠ j →
      (fractionGraph 13 5).Adj i j →
      crossNonAdj83_114 a b = true :=
    fun i j a b ha hb hij hadj =>
      hcc _ _ ha hb (hne_layer i j a b hij) (Or.inr hadj)
  have cc_eq : ∀ (i : ZMod 13) (a b : ZMod 8 × ZMod 11),
      (i, a) ∈ S' → (i, b) ∈ S' → a ≠ b →
      crossNonAdj83_114 a b = true :=
    fun i a b ha hb hab =>
      hcc _ _ ha hb (fun h => hab (congr_arg Prod.snd h)) (Or.inl rfl)
  -- compatWith83_114 via cc and cc_eq
  have compat_of_list : ∀ (i : ZMod 13) (a : ZMod 8 × ZMod 11)
      (ws : List (ZMod 13 × (ZMod 8 × ZMod 11))),
      (i, a) ∈ S' →
      (∀ w ∈ ws, w ∈ S' ∧ (i ≠ w.1 → (fractionGraph 13 5).Adj i w.1) ∧
        (i = w.1 → a ≠ w.2)) →
      compatWith83_114 a (ws.map Prod.snd) = true := by
    intro i a ws hia hws
    simp only [compatWith83_114, List.all_eq_true, List.mem_map]
    rintro b ⟨⟨j, b'⟩, hjb_mem, rfl⟩
    have ⟨hjb_S, hadj, hneq⟩ := hws _ hjb_mem
    by_cases hij : i = j
    · subst hij; exact cc_eq i a b' hia hjb_S (hneq rfl)
    · exact cc i j a b' hia hjb_S hij (hadj hij)
  -- Extract witnesses for layers 0..12
  obtain ⟨w0, hw0⟩ := extract_single_from_layer13_88 S' 0 (hsize' 0)
  -- Show w0 = (0, 0): (0, (0,0)) ∈ S' from translation
  have h_zero_in_S' : ((0 : ZMod 13), ((0 : ZMod 8), (0 : ZMod 11))) ∈ S' := by
    rw [hS'_def, Finset.mem_image]
    refine ⟨(0, w0₁), hw0₁, ?_⟩
    simp only [translateSnd83_114, δ]
    ext
    · rfl
    · change w0₁.1 + (- w0₁.1) = 0; ring
    · change w0₁.2 + (- w0₁.2) = 0; ring
  have hfib0 : layerFiber13_88 S' 0 = {(0, w0)} := by
    have hcard0 : (layerFiber13_88 S' 0).card = 1 := hsize' 0
    have hsubset : ({(0, w0)} : Finset (ZMod 13 × (ZMod 8 × ZMod 11))) ⊆
        layerFiber13_88 S' 0 := by
      intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      rw [layerFiber13_88, Finset.mem_filter]; exact ⟨hw0, rfl⟩
    have hpair_card : ({(0, w0)} :
        Finset (ZMod 13 × (ZMod 8 × ZMod 11))).card = 1 :=
      Finset.card_singleton _
    exact (Finset.eq_of_subset_of_card_le hsubset
      (by rw [hcard0, hpair_card])).symm
  have h_zero_in_fib : ((0 : ZMod 13), ((0 : ZMod 8), (0 : ZMod 11))) ∈
      layerFiber13_88 S' 0 := by
    rw [layerFiber13_88, Finset.mem_filter]; exact ⟨h_zero_in_S', rfl⟩
  rw [hfib0] at h_zero_in_fib
  simp only [Finset.mem_singleton, Prod.mk.injEq] at h_zero_in_fib
  have hw0_zero : w0 = (0, 0) := h_zero_in_fib.2.symm
  subst hw0_zero
  -- Continue extracting witnesses for layers 1..12
  obtain ⟨w1, hw1⟩ := extract_single_from_layer13_88 S' 1 (hsize' 1)
  obtain ⟨w2, hw2⟩ := extract_single_from_layer13_88 S' 2 (hsize' 2)
  obtain ⟨w3, hw3⟩ := extract_single_from_layer13_88 S' 3 (hsize' 3)
  obtain ⟨w4, hw4⟩ := extract_single_from_layer13_88 S' 4 (hsize' 4)
  obtain ⟨w5, hw5⟩ := extract_single_from_layer13_88 S' 5 (hsize' 5)
  obtain ⟨w6, hw6⟩ := extract_single_from_layer13_88 S' 6 (hsize' 6)
  obtain ⟨w7, hw7⟩ := extract_single_from_layer13_88 S' 7 (hsize' 7)
  obtain ⟨w8, hw8⟩ := extract_single_from_layer13_88 S' 8 (hsize' 8)
  obtain ⟨w9, hw9⟩ := extract_single_from_layer13_88 S' 9 (hsize' 9)
  obtain ⟨w10, hw10⟩ := extract_single_from_layer13_88 S' 10 (hsize' 10)
  obtain ⟨w11, hw11⟩ := extract_single_from_layer13_88 S' 11 (hsize' 11)
  obtain ⟨w12, hw12⟩ := extract_single_from_layer13_88 S' 12 (hsize' 12)
  -- Adjacency facts in C₁₃ (E_{13/5}): pairs at cyclic distance ≤ 4 are adjacent.
  -- We need adjacency for all relevant pairs (i, j) appearing in the chain.
  have adj01 : (fractionGraph 13 5).Adj 0 1 := by decide
  have adj02 : (fractionGraph 13 5).Adj 0 2 := by decide
  have adj03 : (fractionGraph 13 5).Adj 0 3 := by decide
  have adj04 : (fractionGraph 13 5).Adj 0 4 := by decide
  have adj09 : (fractionGraph 13 5).Adj 0 9 := by decide
  have adj0_10 : (fractionGraph 13 5).Adj 0 10 := by decide
  have adj0_11 : (fractionGraph 13 5).Adj 0 11 := by decide
  have adj0_12 : (fractionGraph 13 5).Adj 0 12 := by decide
  have adj12 : (fractionGraph 13 5).Adj 1 2 := by decide
  have adj13 : (fractionGraph 13 5).Adj 1 3 := by decide
  have adj14 : (fractionGraph 13 5).Adj 1 4 := by decide
  have adj15 : (fractionGraph 13 5).Adj 1 5 := by decide
  have adj1_10 : (fractionGraph 13 5).Adj 1 10 := by decide
  have adj1_11 : (fractionGraph 13 5).Adj 1 11 := by decide
  have adj1_12 : (fractionGraph 13 5).Adj 1 12 := by decide
  have adj23 : (fractionGraph 13 5).Adj 2 3 := by decide
  have adj24 : (fractionGraph 13 5).Adj 2 4 := by decide
  have adj25 : (fractionGraph 13 5).Adj 2 5 := by decide
  have adj26 : (fractionGraph 13 5).Adj 2 6 := by decide
  have adj2_11 : (fractionGraph 13 5).Adj 2 11 := by decide
  have adj2_12 : (fractionGraph 13 5).Adj 2 12 := by decide
  have adj34 : (fractionGraph 13 5).Adj 3 4 := by decide
  have adj35 : (fractionGraph 13 5).Adj 3 5 := by decide
  have adj36 : (fractionGraph 13 5).Adj 3 6 := by decide
  have adj37 : (fractionGraph 13 5).Adj 3 7 := by decide
  have adj3_12 : (fractionGraph 13 5).Adj 3 12 := by decide
  have adj45 : (fractionGraph 13 5).Adj 4 5 := by decide
  have adj46 : (fractionGraph 13 5).Adj 4 6 := by decide
  have adj47 : (fractionGraph 13 5).Adj 4 7 := by decide
  have adj48 : (fractionGraph 13 5).Adj 4 8 := by decide
  have adj56 : (fractionGraph 13 5).Adj 5 6 := by decide
  have adj57 : (fractionGraph 13 5).Adj 5 7 := by decide
  have adj58 : (fractionGraph 13 5).Adj 5 8 := by decide
  have adj59 : (fractionGraph 13 5).Adj 5 9 := by decide
  have adj67 : (fractionGraph 13 5).Adj 6 7 := by decide
  have adj68 : (fractionGraph 13 5).Adj 6 8 := by decide
  have adj69 : (fractionGraph 13 5).Adj 6 9 := by decide
  have adj6_10 : (fractionGraph 13 5).Adj 6 10 := by decide
  have adj78 : (fractionGraph 13 5).Adj 7 8 := by decide
  have adj79 : (fractionGraph 13 5).Adj 7 9 := by decide
  have adj7_10 : (fractionGraph 13 5).Adj 7 10 := by decide
  have adj7_11 : (fractionGraph 13 5).Adj 7 11 := by decide
  have adj89 : (fractionGraph 13 5).Adj 8 9 := by decide
  have adj8_10 : (fractionGraph 13 5).Adj 8 10 := by decide
  have adj8_11 : (fractionGraph 13 5).Adj 8 11 := by decide
  have adj8_12 : (fractionGraph 13 5).Adj 8 12 := by decide
  have adj9_10 : (fractionGraph 13 5).Adj 9 10 := by decide
  have adj9_11 : (fractionGraph 13 5).Adj 9 11 := by decide
  have adj9_12 : (fractionGraph 13 5).Adj 9 12 := by decide
  have adj10_11 : (fractionGraph 13 5).Adj 10 11 := by decide
  have adj10_12 : (fractionGraph 13 5).Adj 10 12 := by decide
  have adj11_12 : (fractionGraph 13 5).Adj 11 12 := by decide
  -- Layer 1: cross-compat against [s0]
  have cn_1_0 := cc 1 0 w1 (0, 0) hw1 hw0 (by decide) adj01.symm
  -- Layer 2: compat with [s0, s1]
  have cpt_2 := compat_of_list 2 w2 [(0, ((0:ZMod 8), (0:ZMod 11))), (1, w1)] hw2
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw0, fun _ => adj02.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 3: compat with [s0, s1, s2]
  have cpt_3 := compat_of_list 3 w3 [(0, ((0:ZMod 8), (0:ZMod 11))), (1, w1), (2, w2)] hw3
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw0, fun _ => adj03.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj13.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj23.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 4: compat with [s0, s1, s2, s3]
  have cpt_4 := compat_of_list 4 w4
    [(0, ((0:ZMod 8), (0:ZMod 11))), (1, w1), (2, w2), (3, w3)] hw4
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw0, fun _ => adj04.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj14.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj24.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw3, fun _ => adj34.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 5: compat with [s1, s2, s3, s4]
  have cpt_5 := compat_of_list 5 w5 [(1, w1), (2, w2), (3, w3), (4, w4)] hw5
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw1, fun _ => adj15.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj25.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw3, fun _ => adj35.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw4, fun _ => adj45.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 6: compat with [s2, s3, s4, s5]
  have cpt_6 := compat_of_list 6 w6 [(2, w2), (3, w3), (4, w4), (5, w5)] hw6
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw2, fun _ => adj26.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw3, fun _ => adj36.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw4, fun _ => adj46.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj56.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 7: compat with [s3, s4, s5, s6]
  have cpt_7 := compat_of_list 7 w7 [(3, w3), (4, w4), (5, w5), (6, w6)] hw7
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw3, fun _ => adj37.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw4, fun _ => adj47.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj57.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw6, fun _ => adj67.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 8: compat with [s4, s5, s6, s7]
  have cpt_8 := compat_of_list 8 w8 [(4, w4), (5, w5), (6, w6), (7, w7)] hw8
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw4, fun _ => adj48.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj58.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw6, fun _ => adj68.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw7, fun _ => adj78.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 9: compat with [s5, s6, s7, s8, s0] (s9 vs s0 at distance 4)
  have cpt_9 := compat_of_list 9 w9
    [(5, w5), (6, w6), (7, w7), (8, w8), (0, ((0:ZMod 8), (0:ZMod 11)))] hw9
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw5, fun _ => adj59.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw6, fun _ => adj69.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw7, fun _ => adj79.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw8, fun _ => adj89.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj09.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 10: compat with [s6, s7, s8, s9, s0, s1]
  have cpt_10 := compat_of_list 10 w10
    [(6, w6), (7, w7), (8, w8), (9, w9),
     (0, ((0:ZMod 8), (0:ZMod 11))), (1, w1)] hw10
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw6, fun _ => adj6_10.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw7, fun _ => adj7_10.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw8, fun _ => adj8_10.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw9, fun _ => adj9_10.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj0_10.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj1_10.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 11: compat with [s7, s8, s9, s10, s0, s1, s2]
  have cpt_11 := compat_of_list 11 w11
    [(7, w7), (8, w8), (9, w9), (10, w10),
     (0, ((0:ZMod 8), (0:ZMod 11))), (1, w1), (2, w2)] hw11
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw7, fun _ => adj7_11.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw8, fun _ => adj8_11.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw9, fun _ => adj9_11.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw10, fun _ => adj10_11.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj0_11.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj1_11.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj2_11.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 12: compat with [s8, s9, s10, s11, s0, s1, s2, s3]
  have cpt_12 := compat_of_list 12 w12
    [(8, w8), (9, w9), (10, w10), (11, w11),
     (0, ((0:ZMod 8), (0:ZMod 11))), (1, w1), (2, w2), (3, w3)] hw12
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw8, fun _ => adj8_12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw9, fun _ => adj9_12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw10, fun _ => adj10_12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj11_12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj0_12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj1_12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj2_12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw3, fun _ => adj3_12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Normalize List.map Prod.snd in compat hypotheses
  simp only [List.map] at cpt_2
  simp only [List.map] at cpt_3
  simp only [List.map] at cpt_4
  simp only [List.map] at cpt_5
  simp only [List.map] at cpt_6
  simp only [List.map] at cpt_7
  simp only [List.map] at cpt_8
  simp only [List.map] at cpt_9
  simp only [List.map] at cpt_10
  simp only [List.map] at cpt_11
  simp only [List.map] at cpt_12
  -- Show caseMixed83_114_135_check = false, contradicting the chain-search.
  -- The hardcoded s0 = (0, 0) in caseMixed83_114_135_check matches w0 = (0, 0).
  have s0_eq : ((⟨0, by decide⟩, ⟨0, by decide⟩) : Fin 8 × Fin 11) =
      ((0 : ZMod 8), (0 : ZMod 11)) := rfl
  exfalso
  have hf : caseMixed83_114_135_check = false := by
    unfold caseMixed83_114_135_check
    simp only [s0_eq, Bool.not_eq_false']
    apply List.any_of_mem (mem_verts83_114 w1)
    simp only [cn_1_0, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w2)
    simp only [cpt_2, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w3)
    simp only [cpt_3, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w4)
    simp only [cpt_4, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w5)
    simp only [cpt_5, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w6)
    simp only [cpt_6, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w7)
    simp only [cpt_7, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w8)
    simp only [cpt_8, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w9)
    simp only [cpt_9, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w10)
    simp only [cpt_10, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w11)
    simp only [cpt_11, Bool.true_and]
    apply List.any_of_mem (mem_verts83_114 w12)
    simp only [cpt_12]
  exact absurd caseMixed83_114_135_check_true (by rw [hf]; decide)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Mixed multiset upper bound (bound #7)**:
    α(E_{8/3} ⊠ (E_{11/4} ⊠ E_{13/5})) ≤ 12.

The nested floor bound gives α ≤ 13. The Baumert slicing technique with WLOG
translation by `Z₈ × Z₁₁` (a symmetry of E_{8/3} ⊠ E_{11/4}) bringing the
unique element of layer 0 to `(0, 0)` rules out α = 13: the IP forces all 13
layer sizes to be 1, and direct layer-assignment search over
E_{8/3} ⊠ E_{11/4} with `s0 = (0, 0)` finds no valid configuration. See
`caseMixed83_114_135_check_true`. -/
theorem alpha3_83_114_135_le :
    (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 13 5))).indepNum ≤ 12 := by
  -- We work in the equivalent reordering E_{13/5} ⊠ (E_{8/3} ⊠ E_{11/4})
  -- so that the slicing factor (E_{13/5}) is outermost.
  -- α is invariant under associativity and commutativity of strongProduct.
  -- Step 1: show α(E_{13/5} ⊠ (E_{8/3} ⊠ E_{11/4})) ≤ 12 directly.
  have hbound : (strongProduct (fractionGraph 13 5)
      (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))).indepNum ≤ 12 := by
    by_contra hge; push_neg at hge
    have hle : (strongProduct (fractionGraph 13 5)
        (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))).indepNum ≤ 13 := by
      have h := nested_floor_three 13 5 8 3 11 4
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have h1 : ⌊(11:ℝ)/4⌋₊ = 2 :=
        floor_val (by positivity) (by norm_num) (by norm_num)
      simp only [Nat.cast_ofNat, h1] at h; norm_cast at h
      have h2 : ⌊(8:ℝ)/3 * 2⌋₊ = 5 :=
        floor_val (by positivity) (by norm_num) (by norm_num)
      rw [h2] at h; norm_cast at h
      have h3 : ⌊(13:ℝ)/5 * 5⌋₊ = 13 :=
        floor_val (by positivity) (by norm_num) (by norm_num)
      rw [h3] at h; exact h
    have heq : (strongProduct (fractionGraph 13 5)
        (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))).indepNum = 13 := by
      omega
    obtain ⟨S, hSndp⟩ := SimpleGraph.exists_isNIndepSet_indepNum
      (G := strongProduct (fractionGraph 13 5)
        (strongProduct (fractionGraph 8 3) (fractionGraph 11 4)))
    rw [heq] at hSndp
    -- 5-clique-fiber bound from α(E_{8/3} ⊠ E_{11/4}) = 5
    have hfbc : ∀ i : ZMod 13,
        (S.filter (fun p =>
          p.1 ∈ ({i, i + 1, i + 2, i + 3, i + 4} : Finset (ZMod 13)))).card ≤ 5 := by
      intro i
      have h := fiber_bound_clique (fractionGraph 13 5)
        (strongProduct (fractionGraph 8 3) (fractionGraph 11 4))
        S hSndp.isIndepSet ({i, i + 1, i + 2, i + 3, i + 4})
        (five_clique_E135 i)
      rwa [alpha_8o3_11o4] at h
    exact case83_114_135_baumert_contradiction S hSndp.isIndepSet
      hSndp.card_eq hfbc
  -- Step 2: transfer via comm/assoc to the canonical ordering.
  -- (E_{8/3} ⊠ (E_{11/4} ⊠ E_{13/5})).indepNum
  --   = ((E_{8/3} ⊠ E_{11/4}) ⊠ E_{13/5}).indepNum   (assoc)
  --   = (E_{13/5} ⊠ (E_{8/3} ⊠ E_{11/4})).indepNum   (comm)
  rw [← ShannonCapacity.indepNum_strongProduct_assoc,
      indepNum_strongProduct_comm]
  exact hbound

end Section6
