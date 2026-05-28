/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Section 6 Baumert Bridge: α(E_{8/3} ⊠ E_{11/4}²) ≤ 12 (alpha3_83_114_114_le)

Bridge file split off from `Section6UpperBounds.lean`.

See `Section6UpperBoundsCommon` for the shared infrastructure
(`fiber_bound_clique`, `floor_val`, `alpha_*`, `*_clique_E*`, etc.).
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed83_114_114
import Mathlib.Data.Bool.AllAny
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Mixed-multiset Baumert bridge: α(E_{8/3} ⊠ E_{11/4}²) ≤ 12

Bound #6: slice by E_{8/3}, 8 layers in E_{11/4}² (121 verts, α = 5),
canonical sizes (1,2,1,2,2,1,2,2). -/

private def enc114_114'_z (v : ZMod 11 × ZMod 11) : ℕ := v.1.val * 11 + v.2.val

private lemma enc114_114'_z_injective : Function.Injective enc114_114'_z := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [enc114_114'_z] at h
  have ha1 : a1.val < 11 := a1.isLt
  have ha2 : a2.val < 11 := a2.isLt
  have hb1 : b1.val < 11 := b1.isLt
  have hb2 : b2.val < 11 := b2.isLt
  have h1 : a1.val = b1.val := by omega
  have h2 : a2.val = b2.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- The fiber of S over a single layer i (bound #6, Z₈ outer layers,
    inner Z₁₁ × Z₁₁). -/
private def layerFiber8_121 (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11)))
    (i : ZMod 8) :=
  S.filter (fun p => p.1 = i)

private lemma layerFiber8_121_disjoint
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11)))
    (i j : ZMod 8) (hij : i ≠ j) :
    Disjoint (layerFiber8_121 S i) (layerFiber8_121 S j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [layerFiber8_121, Finset.mem_filter] at hx hy
  exact hij (hx.2 ▸ hy.2)

private lemma layer8_121_sum_eq_card
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11))) :
    ∑ i : ZMod 8, (layerFiber8_121 S i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [layerFiber8_121, Finset.mem_biUnion, Finset.mem_univ,
      Finset.mem_filter, true_and]
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x.1, h, rfl⟩⟩
  · intro i _ j _ hij
    exact layerFiber8_121_disjoint S i j hij

private lemma triple_filter_eq8_121
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11))) (i : ZMod 8) :
    S.filter (fun p => p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 8))) =
    layerFiber8_121 S i ∪ layerFiber8_121 S (i + 1) ∪
      layerFiber8_121 S (i + 2) := by
  ext x; simp only [layerFiber8_121, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

private lemma triple_bound_sum8_121
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11))) (i : ZMod 8)
    (hfbc : (S.filter
      (fun p => p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 8)))).card ≤ 5) :
    (layerFiber8_121 S i).card + (layerFiber8_121 S (i + 1)).card +
    (layerFiber8_121 S (i + 2)).card ≤ 5 := by
  rw [triple_filter_eq8_121] at hfbc
  obtain ⟨h01, h02, h12⟩ := three_distinct_zmod8 i
  have h1 := Finset.card_union_of_disjoint (layerFiber8_121_disjoint S _ _ h01)
  have h23 :
      Disjoint (layerFiber8_121 S i ∪ layerFiber8_121 S (i + 1))
        (layerFiber8_121 S (i + 2)) := by
    rw [Finset.disjoint_union_left]
    exact ⟨layerFiber8_121_disjoint S _ _ h02, layerFiber8_121_disjoint S _ _ h12⟩
  have h2 := Finset.card_union_of_disjoint h23
  linarith

private def translateFst8_121 (k : ZMod 8) (x : ZMod 8 × (ZMod 11 × ZMod 11)) :
    ZMod 8 × (ZMod 11 × ZMod 11) :=
  (x.1 + k, x.2)

private lemma translateFst8_121_injective (k : ZMod 8) :
    Function.Injective (translateFst8_121 k) := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [translateFst8_121, Prod.mk.injEq] at h
  exact Prod.ext (add_right_cancel h.1) h.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma translateFst8_121_IS (k : ZMod 8)
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11)))
    (hIS : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).IsIndepSet
      ↑(S.image (translateFst8_121 k)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2⟩, hb, rfl⟩ := hy
  simp only [translateFst8_121] at hne hadj
  have hne' : (a1, a2) ≠ (b1, b2) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg Prod.snd h
    subst h1; subst h2; exact hne rfl
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', hadj.2.1.imp (fun h => add_right_cancel h)
      (fractionGraph_adj_translate 8 3 a1 b1 k).mp, hadj.2.2⟩

private lemma translateFst8_121_layerFiber (k : ZMod 8)
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11))) (i : ZMod 8) :
    (layerFiber8_121 (S.image (translateFst8_121 k)) (i + k)).card =
    (layerFiber8_121 S i).card := by
  have : layerFiber8_121 (S.image (translateFst8_121 k)) (i + k) =
      (layerFiber8_121 S i).image (translateFst8_121 k) := by
    ext ⟨j, a⟩
    simp only [layerFiber8_121, Finset.mem_filter, Finset.mem_image,
      translateFst8_121]
    constructor
    · rintro ⟨⟨⟨i', a'⟩, hi', heq⟩, hj⟩
      have h1 : i' + k = j := congr_arg Prod.fst heq
      have h2 : a' = a := congr_arg Prod.snd heq
      refine ⟨⟨i', a'⟩, ⟨hi', add_right_cancel (h1 ▸ hj)⟩, ?_⟩
      exact Prod.ext h1 h2
    · rintro ⟨⟨i', a'⟩, ⟨hi', heq⟩, htr⟩
      have h1 : i' + k = j := congr_arg Prod.fst htr
      have h2 : a' = a := congr_arg Prod.snd htr
      exact ⟨⟨⟨i', a'⟩, hi', Prod.ext h1 h2⟩, h1 ▸ heq ▸ rfl⟩
  rw [this, Finset.card_image_of_injective _ (translateFst8_121_injective k)]

private def translateSnd114_114' (δ : ZMod 11 × ZMod 11)
    (x : ZMod 8 × (ZMod 11 × ZMod 11)) : ZMod 8 × (ZMod 11 × ZMod 11) :=
  (x.1, (x.2.1 + δ.1, x.2.2 + δ.2))

private lemma translateSnd114_114'_injective (δ : ZMod 11 × ZMod 11) :
    Function.Injective (translateSnd114_114' δ) := by
  intro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [translateSnd114_114', Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext h1 (Prod.ext (add_right_cancel h2) (add_right_cancel h3))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma translateSnd114_114'_IS (δ : ZMod 11 × ZMod 11)
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11)))
    (hIS : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).IsIndepSet
      ↑(S.image (translateSnd114_114' δ)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2, a3⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2, b3⟩, hb, rfl⟩ := hy
  simp only [translateSnd114_114'] at hne hadj
  have hne' : (a1, a2, a3) ≠ (b1, b2, b3) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg (Prod.fst ∘ Prod.snd) h
    have h3 : a3 = b3 := congr_arg (Prod.snd ∘ Prod.snd) h
    subst h1; subst h2; subst h3; exact hne rfl
  obtain ⟨_, h_first, h_inner⟩ := hadj
  have h_inner_back : (a2, a3) = (b2, b3) ∨ (strongProduct (fractionGraph 11 4)
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
          (fractionGraph_adj_translate 11 4 a2 b2 δ.1).mp
      · exact h3_or.imp (fun h => add_right_cancel h)
          (fractionGraph_adj_translate 11 4 a3 b3 δ.2).mp
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', h_first, h_inner_back⟩

private lemma translateSnd114_114'_layerFiber (δ : ZMod 11 × ZMod 11)
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11))) (i : ZMod 8) :
    (layerFiber8_121 (S.image (translateSnd114_114' δ)) i).card =
    (layerFiber8_121 S i).card := by
  have : layerFiber8_121 (S.image (translateSnd114_114' δ)) i =
      (layerFiber8_121 S i).image (translateSnd114_114' δ) := by
    ext ⟨j, a, b⟩
    simp only [layerFiber8_121, Finset.mem_filter, Finset.mem_image,
      translateSnd114_114']
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
  rw [this, Finset.card_image_of_injective _ (translateSnd114_114'_injective δ)]

set_option linter.style.nativeDecide false in
private lemma crossNonAdj114_114'_spec (a b : ZMod 11 × ZMod 11) :
    crossNonAdj114_114' a b = true ↔
    ¬((a.1 = b.1 ∨ (fractionGraph 11 4).Adj a.1 b.1) ∧
      (a.2 = b.2 ∨ (fractionGraph 11 4).Adj a.2 b.2)) := by
  revert a b; native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma cross_compat_of_IS_83_114_114
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11)))
    (hIS : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).IsIndepSet ↑S)
    (x y : ZMod 8 × (ZMod 11 × ZMod 11))
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h1 : x.1 = y.1 ∨ (fractionGraph 8 3).Adj x.1 y.1) :
    crossNonAdj114_114' x.2 y.2 = true := by
  rw [crossNonAdj114_114'_spec]
  intro ⟨hc1, hc2⟩
  have hnadj : ¬(strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).Adj x y :=
    (SimpleGraph.isIndepSet_iff _).mp hIS
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  apply hnadj
  refine ⟨hxy, h1, ?_⟩
  by_cases heq : x.2 = y.2
  · exact Or.inl heq
  · refine Or.inr ⟨heq, hc1, hc2⟩

private lemma extract_single_from_layer8_121
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11))) (i : ZMod 8)
    (hcard : (layerFiber8_121 S i).card = 1) :
    ∃ a : ZMod 11 × ZMod 11, (i, a) ∈ S := by
  obtain ⟨⟨j, a⟩, hja⟩ := Finset.card_pos.mp
    (by omega : 0 < (layerFiber8_121 S i).card)
  rw [layerFiber8_121, Finset.mem_filter] at hja
  exact ⟨a, hja.2 ▸ hja.1⟩

private lemma extract_ordered_pair_from_layer8_121
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11))) (i : ZMod 8)
    (hcard : (layerFiber8_121 S i).card = 2) :
    ∃ a b : ZMod 11 × ZMod 11,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ a ≠ b ∧ enc114_114'_z a < enc114_114'_z b := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, hne, hfib⟩ := Finset.card_eq_two.mp hcard
  have h1 : (i1, a) ∈ layerFiber8_121 S i := hfib ▸ Finset.mem_insert_self _ _
  have h2 : (i2, b) ∈ layerFiber8_121 S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  rw [layerFiber8_121, Finset.mem_filter] at h1 h2
  obtain ⟨h1m, h1e⟩ := h1; obtain ⟨h2m, h2e⟩ := h2
  subst h1e; subst h2e
  have hab : a ≠ b := fun h => hne (Prod.ext rfl h)
  rcases Nat.lt_or_gt_of_ne (fun h => hab (enc114_114'_z_injective h)) with hlt | hgt
  · exact ⟨a, b, h1m, h2m, hab, hlt⟩
  · exact ⟨b, a, h2m, h1m, hab.symm, hgt⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.nativeDecide false in
private lemma case83_114_114_baumert_contradiction
    (S : Finset (ZMod 8 × (ZMod 11 × ZMod 11)))
    (hSis : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).IsIndepSet ↑S)
    (hScard : S.card = 13)
    (hfbc : ∀ i : ZMod 8,
      (S.filter
        (fun p => p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 8)))).card ≤ 5) :
    False := by
  obtain ⟨k, hk⟩ := ip_rotation (fun i => (layerFiber8_121 S i).card)
    (by change ∑ i, (layerFiber8_121 S i).card = 13;
        rw [layer8_121_sum_eq_card]; exact hScard)
    (fun i => triple_bound_sum8_121 S i (hfbc i))
  let κ : ZMod 8 := k
  set S₁ := S.image (translateFst8_121 κ) with hS₁_def
  have hIS₁ := translateFst8_121_IS κ S hSis
  have hcanon₁ : ∀ j : ZMod 8, (layerFiber8_121 S₁ j).card = canonical_sizes j := by
    intro j
    have h := translateFst8_121_layerFiber κ S (j - κ)
    rw [sub_add_cancel] at h
    rw [h, hk (j - κ)]
    congr 1
    ext
    change ((j - κ).val + κ.val) % 8 = j.val
    rw [← ZMod.val_add, sub_add_cancel]
  obtain ⟨w0₁, hw0₁⟩ := extract_single_from_layer8_121 S₁ 0
    (by rw [hcanon₁]; rfl)
  let δ : ZMod 11 × ZMod 11 := (-w0₁.1, -w0₁.2)
  set S' := S₁.image (translateSnd114_114' δ) with hS'_def
  have hIS' := translateSnd114_114'_IS δ S₁ hIS₁
  have hcanon : ∀ j : ZMod 8, (layerFiber8_121 S' j).card = canonical_sizes j := by
    intro j
    rw [translateSnd114_114'_layerFiber δ S₁ j]
    exact hcanon₁ j
  have hcc := cross_compat_of_IS_83_114_114 S' hIS'
  have hne_layer : ∀ (i j : ZMod 8) (a b : ZMod 11 × ZMod 11),
      i ≠ j → (i, a) ≠ (j, b) :=
    fun _ _ _ _ hij h => hij (congr_arg Prod.fst h)
  have cc : ∀ (i j : ZMod 8) (a b : ZMod 11 × ZMod 11),
      (i, a) ∈ S' → (j, b) ∈ S' → i ≠ j →
      (fractionGraph 8 3).Adj i j →
      crossNonAdj114_114' a b = true :=
    fun i j a b ha hb hij hadj =>
      hcc _ _ ha hb (hne_layer i j a b hij) (Or.inr hadj)
  have cc_eq : ∀ (i : ZMod 8) (a b : ZMod 11 × ZMod 11),
      (i, a) ∈ S' → (i, b) ∈ S' → a ≠ b →
      crossNonAdj114_114' a b = true :=
    fun i a b ha hb hab =>
      hcc _ _ ha hb (fun h => hab (congr_arg Prod.snd h)) (Or.inl rfl)
  have compat_of_list : ∀ (i : ZMod 8) (a : ZMod 11 × ZMod 11)
      (ws : List (ZMod 8 × (ZMod 11 × ZMod 11))),
      (i, a) ∈ S' →
      (∀ w ∈ ws, w ∈ S' ∧ (i ≠ w.1 → (fractionGraph 8 3).Adj i w.1) ∧
        (i = w.1 → a ≠ w.2)) →
      compatWith114_114' a (ws.map Prod.snd) = true := by
    intro i a ws hia hws
    simp only [compatWith114_114', List.all_eq_true, List.mem_map]
    rintro b ⟨⟨j, b'⟩, hjb_mem, rfl⟩
    obtain ⟨hjb_S, hadj, hneq⟩ := hws _ hjb_mem
    by_cases hij : i = j
    · subst hij; exact cc_eq i a b' hia hjb_S (hneq rfl)
    · exact cc i j a b' hia hjb_S hij (hadj hij)
  obtain ⟨w0, hw0⟩ := extract_single_from_layer8_121 S' 0 (by rw [hcanon]; rfl)
  have h_zero_in_S' : ((0 : ZMod 8), ((0 : ZMod 11), (0 : ZMod 11))) ∈ S' := by
    rw [hS'_def, Finset.mem_image]
    refine ⟨(0, w0₁), hw0₁, ?_⟩
    simp only [translateSnd114_114', δ]
    ext
    · rfl
    · change w0₁.1 + (- w0₁.1) = 0; ring
    · change w0₁.2 + (- w0₁.2) = 0; ring
  have hfib0 : layerFiber8_121 S' 0 = {(0, w0)} := by
    have hcard0 : (layerFiber8_121 S' 0).card = 1 := by rw [hcanon]; rfl
    have hsubset : ({(0, w0)} : Finset (ZMod 8 × (ZMod 11 × ZMod 11))) ⊆
        layerFiber8_121 S' 0 := by
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      rw [layerFiber8_121, Finset.mem_filter]; exact ⟨hw0, rfl⟩
    have hpair_card : ({(0, w0)} :
        Finset (ZMod 8 × (ZMod 11 × ZMod 11))).card = 1 :=
      Finset.card_singleton _
    exact (Finset.eq_of_subset_of_card_le hsubset
      (by rw [hcard0, hpair_card])).symm
  have h_zero_in_fib : ((0 : ZMod 8), ((0 : ZMod 11), (0 : ZMod 11))) ∈
      layerFiber8_121 S' 0 := by
    rw [layerFiber8_121, Finset.mem_filter]; exact ⟨h_zero_in_S', rfl⟩
  rw [hfib0] at h_zero_in_fib
  simp only [Finset.mem_singleton, Prod.mk.injEq] at h_zero_in_fib
  have hw0_zero : w0 = (0, 0) := h_zero_in_fib.2.symm
  subst hw0_zero
  obtain ⟨w10, w11, hw10, hw11, hne1, hlt1⟩ :=
    extract_ordered_pair_from_layer8_121 S' 1 (by rw [hcanon]; rfl)
  obtain ⟨w2, hw2⟩ := extract_single_from_layer8_121 S' 2
    (by rw [hcanon]; rfl)
  obtain ⟨w30, w31, hw30, hw31, hne3, hlt3⟩ :=
    extract_ordered_pair_from_layer8_121 S' 3 (by rw [hcanon]; rfl)
  obtain ⟨w40, w41, hw40, hw41, hne4, hlt4⟩ :=
    extract_ordered_pair_from_layer8_121 S' 4 (by rw [hcanon]; rfl)
  obtain ⟨w5, hw5⟩ := extract_single_from_layer8_121 S' 5
    (by rw [hcanon]; rfl)
  obtain ⟨w60, w61, hw60, hw61, hne6, hlt6⟩ :=
    extract_ordered_pair_from_layer8_121 S' 6 (by rw [hcanon]; rfl)
  obtain ⟨w70, w71, hw70, hw71, hne7, hlt7⟩ :=
    extract_ordered_pair_from_layer8_121 S' 7 (by rw [hcanon]; rfl)
  have adj01 : (fractionGraph 8 3).Adj 0 1 := by decide
  have adj12 : (fractionGraph 8 3).Adj 1 2 := by decide
  have adj02 : (fractionGraph 8 3).Adj 0 2 := by decide
  have adj13 : (fractionGraph 8 3).Adj 1 3 := by decide
  have adj23 : (fractionGraph 8 3).Adj 2 3 := by decide
  have adj24 : (fractionGraph 8 3).Adj 2 4 := by decide
  have adj34 : (fractionGraph 8 3).Adj 3 4 := by decide
  have adj35 : (fractionGraph 8 3).Adj 3 5 := by decide
  have adj45 : (fractionGraph 8 3).Adj 4 5 := by decide
  have adj46 : (fractionGraph 8 3).Adj 4 6 := by decide
  have adj56 : (fractionGraph 8 3).Adj 5 6 := by decide
  have adj06 : (fractionGraph 8 3).Adj 0 6 := by decide
  have adj57 : (fractionGraph 8 3).Adj 5 7 := by decide
  have adj67 : (fractionGraph 8 3).Adj 6 7 := by decide
  have adj07 : (fractionGraph 8 3).Adj 0 7 := by decide
  have adj17 : (fractionGraph 8 3).Adj 1 7 := by decide
  have cn_10_0 := cc 1 0 w10 (0, 0) hw10 hw0 (by decide) adj01.symm
  have cn_10_11 := cc_eq 1 w10 w11 hw10 hw11 hne1
  have cn_11_0 := cc 1 0 w11 (0, 0) hw11 hw0 (by decide) adj01.symm
  have cpt_v2 := compat_of_list 2 w2
    [(0, ((0:ZMod 11), (0:ZMod 11))), (1, w10), (1, w11)] hw2
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw0, fun _ => adj02.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw10, fun _ => adj12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj12.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v30 := compat_of_list 3 w30 [(1, w10), (1, w11), (2, w2)] hw30
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw10, fun _ => adj13.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj13.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj23.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v31 := compat_of_list 3 w31 [(1, w10), (1, w11), (2, w2)] hw31
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw10, fun _ => adj13.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj13.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj23.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v40 := compat_of_list 4 w40 [(2, w2), (3, w30), (3, w31)] hw40
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw2, fun _ => adj24.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw30, fun _ => adj34.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj34.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v41 := compat_of_list 4 w41 [(2, w2), (3, w30), (3, w31)] hw41
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw2, fun _ => adj24.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw30, fun _ => adj34.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj34.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v5 := compat_of_list 5 w5 [(3, w30), (3, w31), (4, w40), (4, w41)] hw5
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw30, fun _ => adj35.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj35.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw40, fun _ => adj45.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw41, fun _ => adj45.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v60 := compat_of_list 6 w60 [(4, w40), (4, w41), (5, w5),
      (0, ((0:ZMod 11), (0:ZMod 11)))] hw60
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw40, fun _ => adj46.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw41, fun _ => adj46.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj56.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj06.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v61 := compat_of_list 6 w61 [(4, w40), (4, w41), (5, w5),
      (0, ((0:ZMod 11), (0:ZMod 11)))] hw61
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw40, fun _ => adj46.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw41, fun _ => adj46.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj56.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj06.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v70 := compat_of_list 7 w70
    [(5, w5), (6, w60), (6, w61),
     (0, ((0:ZMod 11), (0:ZMod 11))), (1, w10), (1, w11)] hw70
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw5, fun _ => adj57.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw60, fun _ => adj67.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw61, fun _ => adj67.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj07.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw10, fun _ => adj17.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj17.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_v71 := compat_of_list 7 w71
    [(5, w5), (6, w60), (6, w61),
     (0, ((0:ZMod 11), (0:ZMod 11))), (1, w10), (1, w11)] hw71
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw5, fun _ => adj57.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw60, fun _ => adj67.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw61, fun _ => adj67.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj07.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw10, fun _ => adj17.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj17.symm,
            fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cn_30_31 := cc_eq 3 w30 w31 hw30 hw31 hne3
  have cn_40_41 := cc_eq 4 w40 w41 hw40 hw41 hne4
  have cn_60_61 := cc_eq 6 w60 w61 hw60 hw61 hne6
  have cn_70_71 := cc_eq 7 w70 w71 hw70 hw71 hne7
  simp only [List.map] at cpt_v2
  simp only [List.map] at cpt_v30 cpt_v31
  simp only [List.map] at cpt_v40 cpt_v41 cpt_v5
  simp only [List.map] at cpt_v60 cpt_v61 cpt_v70 cpt_v71
  have v0_eq : ((⟨0, by decide⟩, ⟨0, by decide⟩) : Fin 11 × Fin 11) =
      ((0 : ZMod 11), (0 : ZMod 11)) := rfl
  exfalso
  have hf : caseMixed83_114_114_check = false := by
    unfold caseMixed83_114_114_check
    simp only [Bool.not_eq_false']
    apply List.any_of_mem (mem_verts114_114' w10)
    unfold innerSearch_v10_114_114
    simp only [v0_eq, cn_10_0, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w11)
    simp only [show enc114_114' w10 = enc114_114'_z w10 from rfl,
               show enc114_114' w11 = enc114_114'_z w11 from rfl,
               decide_eq_true hlt1, cn_10_11, cn_11_0, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w2)
    simp only [cpt_v2, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w30)
    simp only [cpt_v30, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w31)
    simp only [show enc114_114' w30 = enc114_114'_z w30 from rfl,
               show enc114_114' w31 = enc114_114'_z w31 from rfl,
               decide_eq_true hlt3, cn_30_31, cpt_v31, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w40)
    simp only [cpt_v40, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w41)
    simp only [show enc114_114' w40 = enc114_114'_z w40 from rfl,
               show enc114_114' w41 = enc114_114'_z w41 from rfl,
               decide_eq_true hlt4, cn_40_41, cpt_v41, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w5)
    simp only [cpt_v5, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w60)
    simp only [cpt_v60, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w61)
    simp only [show enc114_114' w60 = enc114_114'_z w60 from rfl,
               show enc114_114' w61 = enc114_114'_z w61 from rfl,
               decide_eq_true hlt6, cn_60_61, cpt_v61, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w70)
    simp only [cpt_v70, Bool.true_and]
    apply List.any_of_mem (mem_verts114_114' w71)
    simp only [show enc114_114' w70 = enc114_114'_z w70 from rfl,
               show enc114_114' w71 = enc114_114'_z w71 from rfl,
               decide_eq_true hlt7, cn_70_71, cpt_v71, Bool.true_and]
  exact absurd caseMixed83_114_114_check_true (by rw [hf]; decide)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Mixed multiset upper bound (bound #6)**:
    α(E_{8/3} ⊠ (E_{11/4} ⊠ E_{11/4})) ≤ 12. -/
theorem alpha3_83_114_114_le :
    (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).indepNum ≤ 12 := by
  by_contra hge; push_neg at hge
  have hle : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).indepNum ≤ 13 := by
    have h := nested_floor_three 8 3 11 4 11 4
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have h1 : ⌊(11:ℝ)/4⌋₊ = 2 :=
      floor_val (by positivity) (by norm_num) (by norm_num)
    simp only [Nat.cast_ofNat, h1] at h; norm_cast at h
    have h2 : ⌊(11:ℝ)/4 * 2⌋₊ = 5 :=
      floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h2] at h; norm_cast at h
    have h3 : ⌊(8:ℝ)/3 * 5⌋₊ = 13 :=
      floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h3] at h; exact h
  have heq : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).indepNum = 13 := by
    omega
  obtain ⟨S, hSndp⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4)))
  rw [heq] at hSndp
  have hfbc : ∀ i : ZMod 8,
      (S.filter (fun p =>
        p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 8)))).card ≤ 5 := by
    intro i
    have h := fiber_bound_clique (fractionGraph 8 3)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))
      S hSndp.isIndepSet ({i, i + 1, i + 2}) (three_clique_E83 i)
    rwa [alpha_11o4_sq] at h
  exact case83_114_114_baumert_contradiction S hSndp.isIndepSet
    hSndp.card_eq hfbc


end Section6
