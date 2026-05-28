/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Section 6 Baumert Bridge: α(E_{7/3}³) ≤ 8 (alpha3_7o3_7o3_7o3_le)

Bridge file split off from `Section6UpperBounds.lean`.

See `Section6UpperBoundsCommon` for the shared infrastructure
(`fiber_bound_clique`, `floor_val`, `alpha_*`, `*_clique_E*`, etc.).
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsInterval1
import Mathlib.Data.Bool.AllAny
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Case E_{7/3}³ Baumert bridge

E_{7/3} has 7 vertices and 3-cliques {i, i+1, i+2}. The nested floor gives
α(E_{7/3}³) ≤ 9. We rule out α = 9 using the Baumert slicing technique
with `case73_check_true`. -/


/-- The fiber of S over a single layer i (E_{7/3}³, Z₇ layers). -/
private def layerFiber7
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))) (i : ZMod 7) :=
  S.filter (fun p => p.1 = i)

private lemma layerFiber7_disjoint
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7)))
    (i j : ZMod 7) (hij : i ≠ j) :
    Disjoint (layerFiber7 S i) (layerFiber7 S j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [layerFiber7, Finset.mem_filter] at hx hy
  exact hij (hx.2 ▸ hy.2)

private lemma layer7_sum_eq_card
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))) :
    ∑ i : ZMod 7, (layerFiber7 S i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1; ext x
    simp only [layerFiber7, Finset.mem_biUnion, Finset.mem_univ,
      Finset.mem_filter, true_and]
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x.1, h, rfl⟩⟩
  · intro i _ j _ hij; exact layerFiber7_disjoint S i j hij

private lemma triple_filter_eq7
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))) (i : ZMod 7) :
    S.filter (fun p =>
      p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 7))) =
    layerFiber7 S i ∪ layerFiber7 S (i + 1) ∪
      layerFiber7 S (i + 2) := by
  ext x; simp only [layerFiber7, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

set_option linter.style.nativeDecide false in
private lemma three_distinct_zmod7 (i : ZMod 7) :
    i ≠ i + 1 ∧ i ≠ i + 2 ∧ (i + 1 : ZMod 7) ≠ i + 2 := by
  revert i; decide

private lemma triple_bound_sum7
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))) (i : ZMod 7)
    (hfbc : (S.filter (fun p =>
      p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 7)))).card ≤ 4) :
    (layerFiber7 S i).card + (layerFiber7 S (i + 1)).card +
    (layerFiber7 S (i + 2)).card ≤ 4 := by
  rw [triple_filter_eq7] at hfbc
  have hd := three_distinct_zmod7 i
  have h1 :=
    Finset.card_union_of_disjoint (layerFiber7_disjoint S _ _ hd.1)
  have h23 : Disjoint (layerFiber7 S i ∪ layerFiber7 S (i + 1))
      (layerFiber7 S (i + 2)) := by
    rw [Finset.disjoint_union_left]
    exact ⟨layerFiber7_disjoint S _ _ hd.2.1,
      layerFiber7_disjoint S _ _ hd.2.2⟩
  have h2 := Finset.card_union_of_disjoint h23
  linarith

/-- Case E_{7/3}³ canonical layer sizes: (1,2,1,1,2,1,1). -/
private def canonical_sizes73 : Fin 7 → ℕ
  | 0 => 1 | 1 => 2 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 1 | 6 => 1

set_option linter.style.nativeDecide false in
private lemma ip_rotation73_fin5 :
    ∀ s : Fin 7 → Fin 5,
    (Finset.univ.sum fun i => (s i).val) = 9 →
    (∀ i : Fin 7,
      (s i).val +
      (s ⟨(i.val + 1) % 7, Nat.mod_lt _ (by omega)⟩).val +
      (s ⟨(i.val + 2) % 7, Nat.mod_lt _ (by omega)⟩).val ≤ 4) →
    ∃ k : Fin 7, ∀ i : Fin 7,
      (s i).val = canonical_sizes73
        ⟨(i.val + k.val) % 7, Nat.mod_lt _ (by omega)⟩ := by
  native_decide

set_option linter.style.nativeDecide false in
private lemma ip_rotation73 (s : Fin 7 → ℕ)
    (hsum : ∑ i : Fin 7, s i = 9)
    (htrip : ∀ i : Fin 7,
      s i + s ⟨(i.val + 1) % 7, Nat.mod_lt _ (by omega)⟩ +
      s ⟨(i.val + 2) % 7, Nat.mod_lt _ (by omega)⟩ ≤ 4) :
    ∃ k : Fin 7, ∀ i : Fin 7,
      s i = canonical_sizes73
        ⟨(i.val + k.val) % 7, Nat.mod_lt _ (by omega)⟩ := by
  have hle : ∀ i : Fin 7, s i ≤ 4 := fun i => by
    have := htrip i; omega
  let s' : Fin 7 → Fin 5 := fun i => ⟨s i, by have := hle i; omega⟩
  have hsum' : (Finset.univ.sum fun i => (s' i).val) = 9 := hsum
  have htrip' : ∀ i : Fin 7,
      (s' i).val +
      (s' ⟨(i.val + 1) % 7, Nat.mod_lt _ (by omega)⟩).val +
      (s' ⟨(i.val + 2) % 7, Nat.mod_lt _ (by omega)⟩).val ≤ 4 := by
    intro i; simp only [s']; exact htrip i
  obtain ⟨k, hk⟩ := ip_rotation73_fin5 s' hsum' htrip'
  exact ⟨k, fun i => by have := hk i; simp only [s'] at this; exact this⟩

private def translateFst7
    (k : ZMod 7) (x : ZMod 7 × (ZMod 7 × ZMod 7)) :
    ZMod 7 × (ZMod 7 × ZMod 7) :=
  (x.1 + k, x.2)

private lemma translateFst7_injective (k : ZMod 7) :
    Function.Injective (translateFst7 k) := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [translateFst7, Prod.mk.injEq] at h
  exact Prod.ext (add_right_cancel h.1) h.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma translateFst7_IS (k : ZMod 7)
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7)))
    (hIS : (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3)
        (fractionGraph 7 3))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3)
        (fractionGraph 7 3))).IsIndepSet
      ↑(S.image (translateFst7 k)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2⟩, hb, rfl⟩ := hy
  simp only [translateFst7] at hne hadj
  have hne' : (a1, a2) ≠ (b1, b2) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg Prod.snd h
    subst h1; subst h2; exact hne rfl
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', hadj.2.1.imp (fun h => add_right_cancel h)
      (fractionGraph_adj_translate 7 3 a1 b1 k).mp, hadj.2.2⟩

private lemma translateFst7_layerFiber (k : ZMod 7)
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))) (i : ZMod 7) :
    (layerFiber7 (S.image (translateFst7 k)) (i + k)).card =
    (layerFiber7 S i).card := by
  have : layerFiber7 (S.image (translateFst7 k)) (i + k) =
      (layerFiber7 S i).image (translateFst7 k) := by
    ext ⟨j, a⟩
    simp only [layerFiber7, Finset.mem_filter, Finset.mem_image,
      translateFst7]
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
  rw [this,
    Finset.card_image_of_injective _ (translateFst7_injective k)]

set_option linter.style.nativeDecide false in
private lemma mem_verts73 (v : Fin 7 × Fin 7) : v ∈ verts73 := by
  revert v; native_decide

set_option linter.style.nativeDecide false in
/-- Bridge: `crossNonAdj73 a b = true` iff the formal E_{7/3}²
    adj-or-eq condition fails. -/
private lemma crossNonAdj73_spec (a b : ZMod 7 × ZMod 7) :
    crossNonAdj73 a b = true ↔
    ¬((a.1 = b.1 ∨ (fractionGraph 7 3).Adj a.1 b.1) ∧
      (a.2 = b.2 ∨ (fractionGraph 7 3).Adj a.2 b.2)) := by
  revert a b; native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma cross_compat_of_IS73
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7)))
    (hIS : (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3)
        (fractionGraph 7 3))).IsIndepSet ↑S)
    (x y : ZMod 7 × (ZMod 7 × ZMod 7))
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h1 : x.1 = y.1 ∨ (fractionGraph 7 3).Adj x.1 y.1) :
    crossNonAdj73 x.2 y.2 = true := by
  rw [crossNonAdj73_spec]
  intro ⟨hc1, hc2⟩
  have hnadj : ¬(strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3)
        (fractionGraph 7 3))).Adj x y :=
    (SimpleGraph.isIndepSet_iff _).mp hIS
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  apply hnadj
  refine ⟨hxy, ?_, ?_⟩
  · exact h1
  · by_cases heq : x.2 = y.2
    · exact Or.inl heq
    · exact Or.inr ⟨heq, hc1, hc2⟩

private lemma enc73_injective : Function.Injective enc73 := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [enc73] at h
  have ha1 := a1.isLt; have ha2 := a2.isLt
  have hb1 := b1.isLt; have hb2 := b2.isLt
  have h1 : a1.val = b1.val := by omega
  have h2 : a2.val = b2.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

private lemma extract_single_from_layer7
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))) (i : ZMod 7)
    (hcard : (layerFiber7 S i).card = 1) :
    ∃ a : ZMod 7 × ZMod 7, (i, a) ∈ S := by
  obtain ⟨⟨j, a⟩, hja⟩ := Finset.card_pos.mp
    (by omega : 0 < (layerFiber7 S i).card)
  rw [layerFiber7, Finset.mem_filter] at hja
  exact ⟨a, hja.2 ▸ hja.1⟩

private lemma extract_ordered_pair_from_layer7
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))) (i : ZMod 7)
    (hcard : (layerFiber7 S i).card = 2) :
    ∃ a b : ZMod 7 × ZMod 7,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ a ≠ b ∧
      enc73 a < enc73 b := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, hne, hfib⟩ :=
    Finset.card_eq_two.mp hcard
  have h1 : (i1, a) ∈ layerFiber7 S i :=
    hfib ▸ Finset.mem_insert_self _ _
  have h2 : (i2, b) ∈ layerFiber7 S i :=
    hfib ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))
  rw [layerFiber7, Finset.mem_filter] at h1 h2
  obtain ⟨h1m, h1e⟩ := h1; obtain ⟨h2m, h2e⟩ := h2
  subst h1e; subst h2e
  have hab : a ≠ b := fun h => hne (Prod.ext rfl h)
  rcases Nat.lt_or_gt_of_ne
    (fun h => hab (enc73_injective h)) with hlt | hgt
  · exact ⟨a, b, h1m, h2m, hab, hlt⟩
  · exact ⟨b, a, h2m, h1m, hab.symm, hgt⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.nativeDecide false in
private lemma case73_baumert_contradiction
    (S : Finset (ZMod 7 × (ZMod 7 × ZMod 7)))
    (hSis : (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3)
        (fractionGraph 7 3))).IsIndepSet ↑S)
    (hScard : S.card = 9)
    (hfbc : ∀ i : ZMod 7,
      (S.filter (fun p =>
        p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 7)))).card
          ≤ 4) :
    False := by
  -- IP rotation
  obtain ⟨k, hk⟩ := ip_rotation73
    (fun i => (layerFiber7 S i).card)
    (by change ∑ i, (layerFiber7 S i).card = 9
        rw [layer7_sum_eq_card]; exact hScard)
    (fun i => triple_bound_sum7 S i (hfbc i))
  -- Translate to canonical sizes
  let κ : ZMod 7 := k
  set S' := S.image (translateFst7 κ) with hS'_def
  have hIS' := translateFst7_IS κ S hSis
  have hcanon : ∀ j : ZMod 7,
      (layerFiber7 S' j).card = canonical_sizes73 j := by
    intro j
    have h := translateFst7_layerFiber κ S (j - κ)
    rw [sub_add_cancel] at h
    rw [h, hk (j - κ)]
    congr 1; ext
    change ((j - κ).val + κ.val) % 7 = j.val
    rw [← ZMod.val_add, sub_add_cancel]
  -- Universal cross-compat
  have hcc := cross_compat_of_IS73 S' hIS'
  have hne_layer : ∀ (i j : ZMod 7)
      (a b : ZMod 7 × ZMod 7),
      i ≠ j → (i, a) ≠ (j, b) :=
    fun _ _ _ _ hij h => hij (congr_arg Prod.fst h)
  have cc : ∀ (i j : ZMod 7)
      (a b : ZMod 7 × ZMod 7),
      (i, a) ∈ S' → (j, b) ∈ S' → i ≠ j →
      (fractionGraph 7 3).Adj i j →
      crossNonAdj73 a b = true :=
    fun i j a b ha hb hij hadj =>
      hcc _ _ ha hb (hne_layer i j a b hij) (Or.inr hadj)
  have cc_eq : ∀ (i : ZMod 7)
      (a b : ZMod 7 × ZMod 7),
      (i, a) ∈ S' → (i, b) ∈ S' → a ≠ b →
      crossNonAdj73 a b = true :=
    fun i a b ha hb hab =>
      hcc _ _ ha hb (fun h => hab (congr_arg Prod.snd h))
        (Or.inl rfl)
  -- Helper: compatWith73 via cc and cc_eq
  have compat_of_list : ∀ (i : ZMod 7)
      (a : ZMod 7 × ZMod 7)
      (ws : List (ZMod 7 × (ZMod 7 × ZMod 7))),
      (i, a) ∈ S' →
      (∀ w ∈ ws, w ∈ S' ∧
        (i ≠ w.1 → (fractionGraph 7 3).Adj i w.1) ∧
        (i = w.1 → a ≠ w.2)) →
      compatWith73 a (ws.map Prod.snd) = true := by
    intro i a ws hia hws
    simp only [compatWith73, List.all_eq_true, List.mem_map]
    rintro b ⟨⟨j, b'⟩, hjb_mem, rfl⟩
    have ⟨hjb_S, hadj, hneq⟩ := hws _ hjb_mem
    by_cases hij : i = j
    · subst hij; exact cc_eq i a b' hia hjb_S (hneq rfl)
    · exact cc i j a b' hia hjb_S hij (hadj hij)
  -- Extract witnesses: (1,2,1,1,2,1,1)
  obtain ⟨w0, hw0⟩ := extract_single_from_layer7 S' 0
    (by rw [hcanon]; rfl)
  obtain ⟨w10, w11, hw10, hw11, hne1, hlt1⟩ :=
    extract_ordered_pair_from_layer7 S' 1
      (by rw [hcanon]; rfl)
  obtain ⟨w2, hw2⟩ := extract_single_from_layer7 S' 2
    (by rw [hcanon]; rfl)
  obtain ⟨w3, hw3⟩ := extract_single_from_layer7 S' 3
    (by rw [hcanon]; rfl)
  obtain ⟨w40, w41, hw40, hw41, hne4, hlt4⟩ :=
    extract_ordered_pair_from_layer7 S' 4
      (by rw [hcanon]; rfl)
  obtain ⟨w5, hw5⟩ := extract_single_from_layer7 S' 5
    (by rw [hcanon]; rfl)
  obtain ⟨w6, hw6⟩ := extract_single_from_layer7 S' 6
    (by rw [hcanon]; rfl)
  -- Adjacency facts in E_{7/3}
  have adj01 : (fractionGraph 7 3).Adj 0 1 := by decide
  have adj02 : (fractionGraph 7 3).Adj 0 2 := by decide
  have adj05 : (fractionGraph 7 3).Adj 0 5 := by decide
  have adj06 : (fractionGraph 7 3).Adj 0 6 := by decide
  have adj12 : (fractionGraph 7 3).Adj 1 2 := by decide
  have adj13 : (fractionGraph 7 3).Adj 1 3 := by decide
  have adj16 : (fractionGraph 7 3).Adj 1 6 := by decide
  have adj23 : (fractionGraph 7 3).Adj 2 3 := by decide
  have adj24 : (fractionGraph 7 3).Adj 2 4 := by decide
  have adj34 : (fractionGraph 7 3).Adj 3 4 := by decide
  have adj35 : (fractionGraph 7 3).Adj 3 5 := by decide
  have adj45 : (fractionGraph 7 3).Adj 4 5 := by decide
  have adj46 : (fractionGraph 7 3).Adj 4 6 := by decide
  have adj56 : (fractionGraph 7 3).Adj 5 6 := by decide
  -- crossNonAdj73 for layer 1 pair
  have cn_10_0 :=
    cc 1 0 w10 w0 hw10 hw0 (by decide) adj01.symm
  have cn_10_11 := cc_eq 1 w10 w11 hw10 hw11 hne1
  have cn_11_0 :=
    cc 1 0 w11 w0 hw11 hw0 (by decide) adj01.symm
  -- crossNonAdj73 for layer 4 pair
  have cn_40_41 := cc_eq 4 w40 w41 hw40 hw41 hne4
  -- compatWith73 for layers 2-6
  -- Layer 2: compat with [v0, v10, v11] (adj 0,1)
  have cpt_v2 := compat_of_list 2 w2
    [(0, w0), (1, w10), (1, w11)] hw2
    (by intro w hw
        simp only [List.mem_cons, List.mem_nil_iff,
          or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw0, fun _ => adj02.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw10, fun _ => adj12.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw11, fun _ => adj12.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩)
  -- Layer 3: compat with [v10, v11, v2] (adj 1,2)
  have cpt_v3 := compat_of_list 3 w3
    [(1, w10), (1, w11), (2, w2)] hw3
    (by intro w hw
        simp only [List.mem_cons, List.mem_nil_iff,
          or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw10, fun _ => adj13.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw11, fun _ => adj13.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw2, fun _ => adj23.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩)
  -- Layer 4a (v40): compat with [v2, v3] (adj 2,3)
  have cpt_v40 := compat_of_list 4 w40
    [(2, w2), (3, w3)] hw40
    (by intro w hw
        simp only [List.mem_cons, List.mem_nil_iff,
          or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw2, fun _ => adj24.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw3, fun _ => adj34.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩)
  -- Layer 4b (v41): compat with [v2, v3]
  have cpt_v41 := compat_of_list 4 w41
    [(2, w2), (3, w3)] hw41
    (by intro w hw
        simp only [List.mem_cons, List.mem_nil_iff,
          or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw2, fun _ => adj24.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw3, fun _ => adj34.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩)
  -- Layer 5: compat with [v3, v40, v41, v0] (adj 3,4,0)
  have cpt_v5 := compat_of_list 5 w5
    [(3, w3), (4, w40), (4, w41), (0, w0)] hw5
    (by intro w hw
        simp only [List.mem_cons, List.mem_nil_iff,
          or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw3, fun _ => adj35.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw40, fun _ => adj45.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw41, fun _ => adj45.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw0, fun _ => adj05.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩)
  -- Layer 6: compat with [v40, v41, v5, v0, v10, v11]
  --   (adj 4,5,0,1)
  have cpt_v6 := compat_of_list 6 w6
    [(4, w40), (4, w41), (5, w5), (0, w0),
     (1, w10), (1, w11)] hw6
    (by intro w hw
        simp only [List.mem_cons, List.mem_nil_iff,
          or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw40, fun _ => adj46.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw41, fun _ => adj46.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw5, fun _ => adj56.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw0, fun _ => adj06.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw10, fun _ => adj16.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩
        · exact ⟨hw11, fun _ => adj16.symm,
            fun h => absurd
              (show _ = _ by simpa using h) (by decide)⟩)
  -- Normalize List.map Prod.snd
  simp only [List.map] at cpt_v2 cpt_v3 cpt_v40 cpt_v41
  simp only [List.map] at cpt_v5 cpt_v6
  -- Contradiction via case73_check
  exfalso
  have hf : case73_check = false := by
    unfold case73_check; simp only [Bool.not_eq_false']
    apply List.any_of_mem (mem_verts73 w0)
    apply List.any_of_mem (mem_verts73 w10)
    simp only [cn_10_0, Bool.true_and]
    apply List.any_of_mem (mem_verts73 w11)
    simp only [decide_eq_true hlt1, cn_10_11, cn_11_0,
      Bool.true_and]
    apply List.any_of_mem (mem_verts73 w2)
    simp only [cpt_v2, Bool.true_and]
    apply List.any_of_mem (mem_verts73 w3)
    simp only [cpt_v3, Bool.true_and]
    apply List.any_of_mem (mem_verts73 w40)
    simp only [cpt_v40, Bool.true_and]
    apply List.any_of_mem (mem_verts73 w41)
    simp only [decide_eq_true hlt4, cn_40_41, cpt_v41,
      Bool.true_and]
    apply List.any_of_mem (mem_verts73 w5)
    simp only [cpt_v5, Bool.true_and]
    apply List.any_of_mem (mem_verts73 w6)
    simp only [cpt_v6]
  exact absurd case73_check_true (by rw [hf]; decide)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **E_{7/3}³ upper bound**: α(E_{7/3}³) ≤ 8.

The nested floor bound gives α ≤ 9. The Baumert slicing technique
shows α ≠ 9: slicing into 7 layers forces sizes (1,2,1,1,2,1,1),
and exhaustive search finds no valid assignment.
See `case73_check_true`. -/
theorem alpha3_7o3_7o3_7o3_le :
    (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3)
        (fractionGraph 7 3))).indepNum ≤ 8 := by
  by_contra hge; push_neg at hge
  have hle : (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3)
        (fractionGraph 7 3))).indepNum ≤ 9 := by
    have h := nested_floor_three 7 3 7 3 7 3
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    have h1 : ⌊(7:ℝ)/3⌋₊ = 2 :=
      floor_val (by positivity) (by norm_num) (by norm_num)
    simp only [Nat.cast_ofNat, h1] at h; norm_cast at h
    have h2 : ⌊(7:ℝ)/3 * 2⌋₊ = 4 :=
      floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h2] at h; norm_cast at h
    have h3 : ⌊(7:ℝ)/3 * 4⌋₊ = 9 :=
      floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h3] at h; exact h
  have heq : (strongProduct (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3)
        (fractionGraph 7 3))).indepNum = 9 := by omega
  obtain ⟨S, hSndp⟩ :=
    SimpleGraph.exists_isNIndepSet_indepNum
      (G := strongProduct (fractionGraph 7 3)
        (strongProduct (fractionGraph 7 3)
          (fractionGraph 7 3)))
  rw [heq] at hSndp
  have hfbc : ∀ i : ZMod 7,
      (S.filter (fun p =>
        p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 7)))).card
          ≤ 4 := by
    intro i
    have h := fiber_bound_clique (fractionGraph 7 3)
      (strongProduct (fractionGraph 7 3) (fractionGraph 7 3))
      S hSndp.isIndepSet ({i, i + 1, i + 2})
      (three_clique_E73 i)
    rwa [alpha_7o3_sq] at h
  exact case73_baumert_contradiction S hSndp.isIndepSet
    hSndp.card_eq hfbc

end Section6
