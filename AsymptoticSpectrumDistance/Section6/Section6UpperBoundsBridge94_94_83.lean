/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Section 6 Baumert Bridge: α(E_{9/4}² ⊠ E_{8/3}) ≤ 8 (alpha3_9o4_9o4_8o3_le)

Bridge file. Closes the (8, 9) tier in the converse direction of paper
Theorem 6.9 by establishing α(E_{9/4} ⊠ E_{9/4} ⊠ E_{8/3}) ≤ 8.

See `Section6UpperBoundsCommon` for the shared infrastructure
(`fiber_bound_clique`, `floor_val`, `alpha_*`, `*_clique_E*`, etc.).
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed94_94_83
import Mathlib.Data.Bool.AllAny
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Mixed-multiset Baumert bridge: α(E_{9/4}² ⊠ E_{8/3}) ≤ 8

The nested floor bound gives α ≤ 9. The Baumert slicing technique with
WLOG translation by `Z₉ × Z₈` (a symmetry of E_{9/4} ⊠ E_{8/3}) bringing
the unique element of layer 0 to `(0,0)` rules out α = 9. See
`caseMixed94_83_check_true`.

Slicing analysis: slice by the first E_{9/4} coordinate, giving 9 layers
in E_{9/4} ⊠ E_{8/3} (α = 4). The 4-clique {i,i+1,i+2,i+3} of E_{9/4}
gives quadruple sum ≤ 4. Sum of 9 quadruple constraints = 4·9 = 36, equal
to max 9·4 = 36. Tight: every quadruple sums to exactly 4, forcing all
layer sizes equal, and hence 1. -/

/-- The fiber of S over a single layer i (Z₉ layers, inner Z₉×Z₈). -/
private def layerFiber9M_83 (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8))) (i : ZMod 9) :=
  S.filter (fun p => p.1 = i)

private lemma layerFiber9M_83_disjoint (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8)))
    (i j : ZMod 9) (hij : i ≠ j) :
    Disjoint (layerFiber9M_83 S i) (layerFiber9M_83 S j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [layerFiber9M_83, Finset.mem_filter] at hx hy
  exact hij (hx.2 ▸ hy.2)

private lemma layer9M_83_sum_eq_card (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8))) :
    ∑ i : ZMod 9, (layerFiber9M_83 S i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [layerFiber9M_83, Finset.mem_biUnion, Finset.mem_univ,
      Finset.mem_filter, true_and]
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x.1, h, rfl⟩⟩
  · intro i _ j _ hij
    exact layerFiber9M_83_disjoint S i j hij

private lemma quadruple_filter_eq9_83 (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8)))
    (i : ZMod 9) :
    S.filter (fun p =>
      p.1 ∈ ({i, i + 1, i + 2, i + 3} : Finset (ZMod 9))) =
    layerFiber9M_83 S i ∪ layerFiber9M_83 S (i + 1) ∪
      layerFiber9M_83 S (i + 2) ∪ layerFiber9M_83 S (i + 3) := by
  ext x; simp only [layerFiber9M_83, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

set_option linter.style.nativeDecide false in
/-- Consecutive offsets 0,1,2,3 are pairwise distinct in ZMod 9. -/
private lemma four_distinct_zmod9_83 (i : ZMod 9) :
    i ≠ i + 1 ∧ i ≠ i + 2 ∧ i ≠ i + 3 ∧
    (i + 1 : ZMod 9) ≠ i + 2 ∧ (i + 1 : ZMod 9) ≠ i + 3 ∧
    (i + 2 : ZMod 9) ≠ i + 3 := by
  revert i; decide

private lemma quadruple_bound_sum9_83
    (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8))) (i : ZMod 9)
    (hfbc : (S.filter (fun p =>
      p.1 ∈ ({i, i + 1, i + 2, i + 3} : Finset (ZMod 9)))).card ≤ 4) :
    (layerFiber9M_83 S i).card + (layerFiber9M_83 S (i + 1)).card +
    (layerFiber9M_83 S (i + 2)).card + (layerFiber9M_83 S (i + 3)).card ≤ 4 := by
  rw [quadruple_filter_eq9_83] at hfbc
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := four_distinct_zmod9_83 i
  -- Disjointness of unions
  have d12 : Disjoint (layerFiber9M_83 S i) (layerFiber9M_83 S (i + 1)) :=
    layerFiber9M_83_disjoint S _ _ h01
  have h_union12 := Finset.card_union_of_disjoint d12
  have d3_with_12 :
      Disjoint (layerFiber9M_83 S i ∪ layerFiber9M_83 S (i + 1))
        (layerFiber9M_83 S (i + 2)) := by
    rw [Finset.disjoint_union_left]
    exact ⟨layerFiber9M_83_disjoint S _ _ h02,
      layerFiber9M_83_disjoint S _ _ h12⟩
  have h_union123 := Finset.card_union_of_disjoint d3_with_12
  have d4_with_123 :
      Disjoint (layerFiber9M_83 S i ∪ layerFiber9M_83 S (i + 1) ∪
        layerFiber9M_83 S (i + 2)) (layerFiber9M_83 S (i + 3)) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact layerFiber9M_83_disjoint S _ _ h03
    · exact layerFiber9M_83_disjoint S _ _ h13
    · exact layerFiber9M_83_disjoint S _ _ h23
  have h_union1234 := Finset.card_union_of_disjoint d4_with_123
  linarith

set_option linter.style.nativeDecide false in
/-- Finite IP: every ZMod 9 → Fin 5 with sum 9 and all 9 cyclic quadruple
    sums ≤ 4 must be uniformly 1. Proved by `native_decide` over 5^9 ≈ 2M cases. -/
private lemma ip_uniform94_83_zmod_fin5 :
    ∀ s : ZMod 9 → Fin 5,
    (Finset.univ.sum fun i => (s i).val) = 9 →
    (∀ i : ZMod 9,
      (s i).val + (s (i + 1)).val + (s (i + 2)).val + (s (i + 3)).val ≤ 4) →
    ∀ i : ZMod 9, (s i).val = 1 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Layer sizes satisfying sum=9 and quadruple≤4 are uniformly 1. -/
private lemma ip_uniform94_83 (s : ZMod 9 → ℕ)
    (hsum : ∑ i : ZMod 9, s i = 9)
    (hquad : ∀ i : ZMod 9,
      s i + s (i + 1) + s (i + 2) + s (i + 3) ≤ 4) :
    ∀ i : ZMod 9, s i = 1 := by
  have hle : ∀ i : ZMod 9, s i ≤ 4 := fun i => by have := hquad i; omega
  let s' : ZMod 9 → Fin 5 := fun i => ⟨s i, by have := hle i; omega⟩
  have hsum' : (Finset.univ.sum fun i => (s' i).val) = 9 := hsum
  have hquad' : ∀ i : ZMod 9,
      (s' i).val + (s' (i + 1)).val + (s' (i + 2)).val + (s' (i + 3)).val ≤ 4 := by
    intro i; simp only [s']; exact hquad i
  intro i
  have := ip_uniform94_83_zmod_fin5 s' hsum' hquad' i
  simp only [s'] at this; exact this

/-- Translate S by shifting the inner two coordinates (Z₉ × Z₈). -/
private def translateSnd94_83 (δ : ZMod 9 × ZMod 8)
    (x : ZMod 9 × (ZMod 9 × ZMod 8)) : ZMod 9 × (ZMod 9 × ZMod 8) :=
  (x.1, (x.2.1 + δ.1, x.2.2 + δ.2))

private lemma translateSnd94_83_injective (δ : ZMod 9 × ZMod 8) :
    Function.Injective (translateSnd94_83 δ) := by
  intro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [translateSnd94_83, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext h1 (Prod.ext (add_right_cancel h2) (add_right_cancel h3))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Inner-coordinate translation preserves the IS property. -/
private lemma translateSnd94_83_IS (δ : ZMod 9 × ZMod 8)
    (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))).IsIndepSet
      ↑(S.image (translateSnd94_83 δ)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2, a3⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2, b3⟩, hb, rfl⟩ := hy
  simp only [translateSnd94_83] at hne hadj
  have hne' : (a1, a2, a3) ≠ (b1, b2, b3) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg (Prod.fst ∘ Prod.snd) h
    have h3 : a3 = b3 := congr_arg (Prod.snd ∘ Prod.snd) h
    subst h1; subst h2; subst h3; exact hne rfl
  -- Decompose adjacency in the strong product
  obtain ⟨_, h_first, h_inner⟩ := hadj
  have h_inner_back : (a2, a3) = (b2, b3) ∨ (strongProduct (fractionGraph 9 4)
      (fractionGraph 8 3)).Adj (a2, a3) (b2, b3) := by
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
          (fractionGraph_adj_translate 9 4 a2 b2 δ.1).mp
      · exact h3_or.imp (fun h => add_right_cancel h)
          (fractionGraph_adj_translate 8 3 a3 b3 δ.2).mp
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', h_first, h_inner_back⟩

private lemma translateSnd94_83_layerFiber (δ : ZMod 9 × ZMod 8)
    (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8))) (i : ZMod 9) :
    (layerFiber9M_83 (S.image (translateSnd94_83 δ)) i).card =
    (layerFiber9M_83 S i).card := by
  have : layerFiber9M_83 (S.image (translateSnd94_83 δ)) i =
      (layerFiber9M_83 S i).image (translateSnd94_83 δ) := by
    ext ⟨j, a, b⟩
    simp only [layerFiber9M_83, Finset.mem_filter, Finset.mem_image, translateSnd94_83]
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
  rw [this, Finset.card_image_of_injective _ (translateSnd94_83_injective δ)]

set_option linter.style.nativeDecide false in
/-- Every element of `Fin 9 × Fin 8` is in `verts94_83`. -/
private lemma mem_verts94_83' (v : Fin 9 × Fin 8) : v ∈ verts94_83 := by
  revert v; native_decide

set_option linter.style.nativeDecide false in
/-- Bridge: `crossNonAdj94_83 a b = true` iff the formal adj-or-eq condition fails
    for E_{9/4} ⊠ E_{8/3}. -/
private lemma crossNonAdj94_83_spec (a b : ZMod 9 × ZMod 8) :
    crossNonAdj94_83 a b = true ↔
    ¬((a.1 = b.1 ∨ (fractionGraph 9 4).Adj a.1 b.1) ∧
      (a.2 = b.2 ∨ (fractionGraph 8 3).Adj a.2 b.2)) := by
  revert a b; native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- From IS property and first-coordinate adj-or-eq, derive crossNonAdj94_83. -/
private lemma cross_compat_of_IS_94_83
    (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))).IsIndepSet ↑S)
    (x y : ZMod 9 × (ZMod 9 × ZMod 8))
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h1 : x.1 = y.1 ∨ (fractionGraph 9 4).Adj x.1 y.1) :
    crossNonAdj94_83 x.2 y.2 = true := by
  rw [crossNonAdj94_83_spec]
  intro ⟨hc1, hc2⟩
  have hnadj : ¬(strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))).Adj x y :=
    (SimpleGraph.isIndepSet_iff _).mp hIS
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  apply hnadj
  refine ⟨hxy, h1, ?_⟩
  by_cases heq : x.2 = y.2
  · exact Or.inl heq
  · refine Or.inr ⟨heq, hc1, hc2⟩

/-- Extract the unique witness from a single-element layer. -/
private lemma extract_single_from_layer9M_83
    (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8))) (i : ZMod 9)
    (hcard : (layerFiber9M_83 S i).card = 1) :
    ∃ a : ZMod 9 × ZMod 8, (i, a) ∈ S := by
  obtain ⟨⟨j, a⟩, hja⟩ := Finset.card_pos.mp
    (by omega : 0 < (layerFiber9M_83 S i).card)
  rw [layerFiber9M_83, Finset.mem_filter] at hja
  exact ⟨a, hja.2 ▸ hja.1⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.nativeDecide false in
/-- Mixed-multiset Baumert contradiction for (9/4, 9/4, 8/3): an IS of size 9 in
    E_{9/4} ⊠ E_{9/4} ⊠ E_{8/3} satisfying the quadruple-fiber bound 4
    cannot exist. -/
private lemma case94_83_baumert_contradiction
    (S : Finset (ZMod 9 × (ZMod 9 × ZMod 8)))
    (hSis : (strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))).IsIndepSet ↑S)
    (hScard : S.card = 9)
    (hfbc : ∀ i : ZMod 9,
      (S.filter (fun p =>
        p.1 ∈ ({i, i + 1, i + 2, i + 3} : Finset (ZMod 9)))).card ≤ 4) :
    False := by
  -- Layer sizes are all 1 (no rotation needed; the IP forces uniform 1)
  have hsize : ∀ j : ZMod 9, (layerFiber9M_83 S j).card = 1 := by
    apply ip_uniform94_83 (fun i => (layerFiber9M_83 S i).card)
    · rw [layer9M_83_sum_eq_card]; exact hScard
    · intro i; exact quadruple_bound_sum9_83 S i (hfbc i)
  -- Extract the unique witness in layer 0
  obtain ⟨w0₁, hw0₁⟩ := extract_single_from_layer9M_83 S 0 (hsize 0)
  -- Translate so that w0 = (0, 0): inner shift δ = (-w0₁.1, -w0₁.2)
  let δ : ZMod 9 × ZMod 8 := (-w0₁.1, -w0₁.2)
  set S' := S.image (translateSnd94_83 δ) with hS'_def
  have hIS' := translateSnd94_83_IS δ S hSis
  have hsize' : ∀ j : ZMod 9, (layerFiber9M_83 S' j).card = 1 := by
    intro j
    rw [translateSnd94_83_layerFiber δ S j]
    exact hsize j
  -- Cross-compat
  have hcc := cross_compat_of_IS_94_83 S' hIS'
  have hne_layer : ∀ (i j : ZMod 9) (a b : ZMod 9 × ZMod 8),
      i ≠ j → (i, a) ≠ (j, b) :=
    fun _ _ _ _ hij h => hij (congr_arg Prod.fst h)
  have cc : ∀ (i j : ZMod 9) (a b : ZMod 9 × ZMod 8),
      (i, a) ∈ S' → (j, b) ∈ S' → i ≠ j →
      (fractionGraph 9 4).Adj i j →
      crossNonAdj94_83 a b = true :=
    fun i j a b ha hb hij hadj =>
      hcc _ _ ha hb (hne_layer i j a b hij) (Or.inr hadj)
  -- Same-layer compat: not actually needed since each layer has size 1, but
  -- we include it for the compat_of_list helper to support layer-0's `s0`.
  have cc_eq : ∀ (i : ZMod 9) (a b : ZMod 9 × ZMod 8),
      (i, a) ∈ S' → (i, b) ∈ S' → a ≠ b →
      crossNonAdj94_83 a b = true :=
    fun i a b ha hb hab =>
      hcc _ _ ha hb (fun h => hab (congr_arg Prod.snd h)) (Or.inl rfl)
  -- compatWith94_83 via cc and cc_eq (case 7 / case 8 style)
  have compat_of_list : ∀ (i : ZMod 9) (a : ZMod 9 × ZMod 8)
      (ws : List (ZMod 9 × (ZMod 9 × ZMod 8))),
      (i, a) ∈ S' →
      (∀ w ∈ ws, w ∈ S' ∧ (i ≠ w.1 → (fractionGraph 9 4).Adj i w.1) ∧
        (i = w.1 → a ≠ w.2)) →
      compatWith94_83 a (ws.map Prod.snd) = true := by
    intro i a ws hia hws
    simp only [compatWith94_83, List.all_eq_true, List.mem_map]
    rintro b ⟨⟨j, b'⟩, hjb_mem, rfl⟩
    have ⟨hjb_S, hadj, hneq⟩ := hws _ hjb_mem
    by_cases hij : i = j
    · subst hij; exact cc_eq i a b' hia hjb_S (hneq rfl)
    · exact cc i j a b' hia hjb_S hij (hadj hij)
  -- Extract witnesses for layers 0..8
  obtain ⟨w0, hw0⟩ := extract_single_from_layer9M_83 S' 0 (hsize' 0)
  -- Show w0 = (0, 0): (0, (0,0)) ∈ S' from translation
  have h_zero_in_S' : ((0 : ZMod 9), ((0 : ZMod 9), (0 : ZMod 8))) ∈ S' := by
    rw [hS'_def, Finset.mem_image]
    refine ⟨(0, w0₁), hw0₁, ?_⟩
    simp only [translateSnd94_83, δ]
    ext
    · rfl
    · change w0₁.1 + (- w0₁.1) = 0; ring
    · change w0₁.2 + (- w0₁.2) = 0; ring
  have hfib0 : layerFiber9M_83 S' 0 = {(0, w0)} := by
    have hcard0 : (layerFiber9M_83 S' 0).card = 1 := hsize' 0
    have hsubset : ({(0, w0)} : Finset (ZMod 9 × (ZMod 9 × ZMod 8))) ⊆
        layerFiber9M_83 S' 0 := by
      intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      rw [layerFiber9M_83, Finset.mem_filter]; exact ⟨hw0, rfl⟩
    have hpair_card : ({(0, w0)} : Finset (ZMod 9 × (ZMod 9 × ZMod 8))).card = 1 :=
      Finset.card_singleton _
    exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard0, hpair_card])).symm
  have h_zero_in_fib : ((0 : ZMod 9), ((0 : ZMod 9), (0 : ZMod 8))) ∈
      layerFiber9M_83 S' 0 := by
    rw [layerFiber9M_83, Finset.mem_filter]; exact ⟨h_zero_in_S', rfl⟩
  rw [hfib0] at h_zero_in_fib
  simp only [Finset.mem_singleton, Prod.mk.injEq] at h_zero_in_fib
  have hw0_zero : w0 = (0, 0) := h_zero_in_fib.2.symm
  subst hw0_zero
  -- Continue extracting witnesses for layers 1..8
  obtain ⟨w1, hw1⟩ := extract_single_from_layer9M_83 S' 1 (hsize' 1)
  obtain ⟨w2, hw2⟩ := extract_single_from_layer9M_83 S' 2 (hsize' 2)
  obtain ⟨w3, hw3⟩ := extract_single_from_layer9M_83 S' 3 (hsize' 3)
  obtain ⟨w4, hw4⟩ := extract_single_from_layer9M_83 S' 4 (hsize' 4)
  obtain ⟨w5, hw5⟩ := extract_single_from_layer9M_83 S' 5 (hsize' 5)
  obtain ⟨w6, hw6⟩ := extract_single_from_layer9M_83 S' 6 (hsize' 6)
  obtain ⟨w7, hw7⟩ := extract_single_from_layer9M_83 S' 7 (hsize' 7)
  obtain ⟨w8, hw8⟩ := extract_single_from_layer9M_83 S' 8 (hsize' 8)
  -- Adjacency facts in C₉ (E_{9/4}): pairs at cyclic distance ≤ 3 are adjacent
  have adj01 : (fractionGraph 9 4).Adj 0 1 := by decide
  have adj02 : (fractionGraph 9 4).Adj 0 2 := by decide
  have adj03 : (fractionGraph 9 4).Adj 0 3 := by decide
  have adj06 : (fractionGraph 9 4).Adj 0 6 := by decide
  have adj07 : (fractionGraph 9 4).Adj 0 7 := by decide
  have adj08 : (fractionGraph 9 4).Adj 0 8 := by decide
  have adj12 : (fractionGraph 9 4).Adj 1 2 := by decide
  have adj13 : (fractionGraph 9 4).Adj 1 3 := by decide
  have adj14 : (fractionGraph 9 4).Adj 1 4 := by decide
  have adj17 : (fractionGraph 9 4).Adj 1 7 := by decide
  have adj18 : (fractionGraph 9 4).Adj 1 8 := by decide
  have adj23 : (fractionGraph 9 4).Adj 2 3 := by decide
  have adj24 : (fractionGraph 9 4).Adj 2 4 := by decide
  have adj25 : (fractionGraph 9 4).Adj 2 5 := by decide
  have adj28 : (fractionGraph 9 4).Adj 2 8 := by decide
  have adj34 : (fractionGraph 9 4).Adj 3 4 := by decide
  have adj35 : (fractionGraph 9 4).Adj 3 5 := by decide
  have adj36 : (fractionGraph 9 4).Adj 3 6 := by decide
  have adj45 : (fractionGraph 9 4).Adj 4 5 := by decide
  have adj46 : (fractionGraph 9 4).Adj 4 6 := by decide
  have adj47 : (fractionGraph 9 4).Adj 4 7 := by decide
  have adj56 : (fractionGraph 9 4).Adj 5 6 := by decide
  have adj57 : (fractionGraph 9 4).Adj 5 7 := by decide
  have adj58 : (fractionGraph 9 4).Adj 5 8 := by decide
  have adj67 : (fractionGraph 9 4).Adj 6 7 := by decide
  have adj68 : (fractionGraph 9 4).Adj 6 8 := by decide
  have adj78 : (fractionGraph 9 4).Adj 7 8 := by decide
  -- Layer 1: cross-compat against [s0]
  have cn_1_0 := cc 1 0 w1 (0, 0) hw1 hw0 (by decide) adj01.symm
  -- Layer 2: compat with [s0, s1]
  have cpt_2 := compat_of_list 2 w2 [(0, (0, 0)), (1, w1)] hw2
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw0, fun _ => adj02.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 3: compat with [s0, s1, s2]
  have cpt_3 := compat_of_list 3 w3 [(0, (0, 0)), (1, w1), (2, w2)] hw3
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw0, fun _ => adj03.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj13.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj23.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 4: compat with [s1, s2, s3]
  have cpt_4 := compat_of_list 4 w4 [(1, w1), (2, w2), (3, w3)] hw4
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw1, fun _ => adj14.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj24.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw3, fun _ => adj34.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 5: compat with [s2, s3, s4]
  have cpt_5 := compat_of_list 5 w5 [(2, w2), (3, w3), (4, w4)] hw5
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw2, fun _ => adj25.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw3, fun _ => adj35.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw4, fun _ => adj45.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 6: compat with [s3, s4, s5, s0] (s6 vs s0 at distance 3)
  have cpt_6 := compat_of_list 6 w6 [(3, w3), (4, w4), (5, w5), (0, (0, 0))] hw6
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw3, fun _ => adj36.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw4, fun _ => adj46.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj56.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj06.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 7: compat with [s4, s5, s6, s0, s1] (s7 vs s0 at distance 2, s7 vs s1 at distance 3)
  have cpt_7 := compat_of_list 7 w7
    [(4, w4), (5, w5), (6, w6), (0, (0, 0)), (1, w1)] hw7
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw4, fun _ => adj47.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj57.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw6, fun _ => adj67.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj07.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj17.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 8: compat with [s5, s6, s7, s0, s1, s2]
  have cpt_8 := compat_of_list 8 w8
    [(5, w5), (6, w6), (7, w7), (0, (0, 0)), (1, w1), (2, w2)] hw8
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw5, fun _ => adj58.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw6, fun _ => adj68.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw7, fun _ => adj78.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj08.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw1, fun _ => adj18.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj28.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Normalize List.map Prod.snd in compat hypotheses
  simp only [List.map] at cpt_2 cpt_3 cpt_4 cpt_5 cpt_6 cpt_7 cpt_8
  -- Show caseMixed94_83_check = false, contradicting caseMixed94_83_check_true.
  -- The hardcoded s0 = (0, 0) in caseMixed94_83_check matches w0 = (0, 0) here.
  have s0_eq : ((⟨0, by decide⟩, ⟨0, by decide⟩) : Fin 9 × Fin 8) =
      ((0 : ZMod 9), (0 : ZMod 8)) := rfl
  exfalso
  have hf : caseMixed94_83_check = false := by
    unfold caseMixed94_83_check
    simp only [s0_eq, Bool.not_eq_false']
    apply List.any_of_mem (mem_verts94_83 w1)
    simp only [cn_1_0, Bool.true_and]
    apply List.any_of_mem (mem_verts94_83 w2)
    simp only [cpt_2, Bool.true_and]
    apply List.any_of_mem (mem_verts94_83 w3)
    simp only [cpt_3, Bool.true_and]
    apply List.any_of_mem (mem_verts94_83 w4)
    simp only [cpt_4, Bool.true_and]
    apply List.any_of_mem (mem_verts94_83 w5)
    simp only [cpt_5, Bool.true_and]
    apply List.any_of_mem (mem_verts94_83 w6)
    simp only [cpt_6, Bool.true_and]
    apply List.any_of_mem (mem_verts94_83 w7)
    simp only [cpt_7, Bool.true_and]
    apply List.any_of_mem (mem_verts94_83 w8)
    simp only [cpt_8]
  exact absurd caseMixed94_83_check_true (by rw [hf]; decide)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Mixed multiset upper bound (9/4, 9/4, 8/3)**:
    α(E_{9/4} ⊠ (E_{9/4} ⊠ E_{8/3})) ≤ 8.

The nested floor bound gives α ≤ 9. The Baumert slicing technique with WLOG
translation by `Z₉ × Z₈` (a symmetry of E_{9/4} ⊠ E_{8/3}) bringing the unique
element of layer 0 to `(0, 0)` rules out α = 9: the IP forces all 9 layer
sizes to be 1, and direct layer-assignment search over E_{9/4} ⊠ E_{8/3} with
`s0 = (0, 0)` finds no valid configuration. See `caseMixed94_83_check_true`. -/
theorem alpha3_9o4_9o4_8o3_le :
    (strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))).indepNum ≤ 8 := by
  by_contra hge; push_neg at hge
  have hle : (strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))).indepNum ≤ 9 := by
    have h := nested_floor_three 9 4 9 4 8 3
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have h1 : ⌊(8:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
    simp only [Nat.cast_ofNat, h1] at h; norm_cast at h
    have h2 : ⌊(9:ℝ)/4 * 2⌋₊ = 4 := floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h2] at h; norm_cast at h
    have h3 : ⌊(9:ℝ)/4 * 4⌋₊ = 9 := floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h3] at h; exact h
  have heq : (strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))).indepNum = 9 := by omega
  obtain ⟨S, hSndp⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3)))
  rw [heq] at hSndp
  -- Quadruple-fiber bound from α(E_{9/4} ⊠ E_{8/3}) = 4
  have hfbc : ∀ i : ZMod 9,
      (S.filter (fun p =>
        p.1 ∈ ({i, i + 1, i + 2, i + 3} : Finset (ZMod 9)))).card ≤ 4 := by
    intro i
    have h := fiber_bound_clique (fractionGraph 9 4)
      (strongProduct (fractionGraph 9 4) (fractionGraph 8 3))
      S hSndp.isIndepSet ({i, i + 1, i + 2, i + 3}) (four_clique_E94 i)
    rwa [alpha_9o4_8o3] at h
  exact case94_83_baumert_contradiction S hSndp.isIndepSet hSndp.card_eq hfbc

end Section6
