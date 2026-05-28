/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Section 6 Baumert Bridge: α(C₅³) ≤ 10 (alpha3_5o2_5o2_5o2_le)

Bridge file split off from `Section6UpperBounds.lean`.

See `Section6UpperBoundsCommon` for the shared infrastructure
(`fiber_bound_clique`, `floor_val`, `alpha_*`, `*_clique_E*`, etc.).
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge5o2_5o2_8o3
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsInterval2
import Mathlib.Data.Bool.AllAny
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Case C₅³ Baumert bridge

E_{5/2} = C₅ has 5 vertices and edges {i, i+1}. Monotonicity gives
α(C₅³) ≤ α(C₅² ⊠ E_{8/3}) ≤ 11. We rule out α = 11 using the Baumert
slicing technique with `case52_check_true` (7 canonical size vectors). -/


/-- The fiber of S over a single layer i (C₅³, ZMod 5 layers). -/
private def layerFiber52C
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) (i : ZMod 5) :=
  S.filter (fun p => p.1 = i)

private lemma layerFiber52C_disjoint
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5)))
    (i j : ZMod 5) (hij : i ≠ j) :
    Disjoint (layerFiber52C S i) (layerFiber52C S j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [layerFiber52C, Finset.mem_filter] at hx hy
  exact hij (hx.2 ▸ hy.2)

private lemma layer52C_sum_eq_card
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) :
    ∑ i : ZMod 5, (layerFiber52C S i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1; ext x
    simp only [layerFiber52C, Finset.mem_biUnion, Finset.mem_univ,
      Finset.mem_filter, true_and]
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x.1, h, rfl⟩⟩
  · intro i _ j _ hij; exact layerFiber52C_disjoint S i j hij

private lemma pair_filter_eq52C
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) (i : ZMod 5) :
    S.filter (fun p =>
      p.1 ∈ ({i, i + 1} : Finset (ZMod 5))) =
    layerFiber52C S i ∪ layerFiber52C S (i + 1) := by
  ext x; simp only [layerFiber52C, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

private lemma pair_bound_sum52C
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) (i : ZMod 5)
    (hfbc : (S.filter (fun p =>
      p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card ≤ 5) :
    (layerFiber52C S i).card + (layerFiber52C S (i + 1)).card ≤ 5 := by
  rw [pair_filter_eq52C] at hfbc
  rwa [Finset.card_union_of_disjoint
    (layerFiber52C_disjoint S _ _ (two_distinct_zmod5 i))] at hfbc

/-- C₅³ canonical size vector classes (7 classes). -/
private def cs52C (c : Fin 7) : Fin 5 → ℕ := match c with
  | 0 => ![4, 1, 1, 4, 1]
  | 1 => ![4, 1, 2, 3, 1]
  | 2 => ![4, 1, 3, 2, 1]
  | 3 => ![3, 2, 3, 2, 1]
  | 4 => ![3, 2, 3, 1, 2]
  | 5 => ![3, 1, 3, 2, 2]
  | 6 => ![3, 2, 2, 2, 2]

set_option linter.style.nativeDecide false in
private lemma ip_rotation52C_fin6 :
    ∀ s : Fin 5 → Fin 6,
    (Finset.univ.sum fun i => (s i).val) = 11 →
    (∀ i : Fin 5,
      (s i).val +
      (s ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩).val ≤ 5) →
    ∃ (c : Fin 7) (k : Fin 5), ∀ i : Fin 5,
      (s i).val = cs52C c
        ⟨(i.val + k.val) % 5, Nat.mod_lt _ (by omega)⟩ := by
  native_decide

set_option linter.style.nativeDecide false in
private lemma ip_rotation52C (s : Fin 5 → ℕ)
    (hsum : ∑ i : Fin 5, s i = 11)
    (hpair : ∀ i : Fin 5,
      s i + s ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩ ≤ 5) :
    ∃ (c : Fin 7) (k : Fin 5), ∀ i : Fin 5,
      s i = cs52C c
        ⟨(i.val + k.val) % 5, Nat.mod_lt _ (by omega)⟩ := by
  have hle : ∀ i : Fin 5, s i ≤ 5 := fun i => by have := hpair i; omega
  let s' : Fin 5 → Fin 6 := fun i => ⟨s i, by have := hle i; omega⟩
  have hsum' : (Finset.univ.sum fun i => (s' i).val) = 11 := hsum
  have hpair' : ∀ i : Fin 5,
      (s' i).val +
      (s' ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩).val ≤ 5 := by
    intro i; simp only [s']; exact hpair i
  obtain ⟨c, k, hk⟩ := ip_rotation52C_fin6 s' hsum' hpair'
  exact ⟨c, k, fun i => by have := hk i; simp only [s'] at this; exact this⟩

private def translateFst52C
    (k : ZMod 5) (x : ZMod 5 × (ZMod 5 × ZMod 5)) :
    ZMod 5 × (ZMod 5 × ZMod 5) :=
  (x.1 + k, x.2)

private lemma translateFst52C_injective (k : ZMod 5) :
    Function.Injective (translateFst52C k) := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [translateFst52C, Prod.mk.injEq] at h
  exact Prod.ext (add_right_cancel h.1) h.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma translateFst52C_IS (k : ZMod 5)
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5)))
    (hIS : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))).IsIndepSet
      ↑(S.image (translateFst52C k)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2⟩, hb, rfl⟩ := hy
  simp only [translateFst52C] at hne hadj
  have hne' : (a1, a2) ≠ (b1, b2) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg Prod.snd h
    subst h1; subst h2; exact hne rfl
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', hadj.2.1.imp (fun h => add_right_cancel h)
      (fractionGraph_adj_translate 5 2 a1 b1 k).mp, hadj.2.2⟩

private lemma translateFst52C_layerFiber (k : ZMod 5)
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) (i : ZMod 5) :
    (layerFiber52C (S.image (translateFst52C k)) (i + k)).card =
    (layerFiber52C S i).card := by
  have : layerFiber52C (S.image (translateFst52C k)) (i + k) =
      (layerFiber52C S i).image (translateFst52C k) := by
    ext ⟨j, a⟩
    simp only [layerFiber52C, Finset.mem_filter, Finset.mem_image,
      translateFst52C]
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
    Finset.card_image_of_injective _ (translateFst52C_injective k)]

set_option linter.style.nativeDecide false in
/-- Bridge: `crossNonAdj52 a b = true` iff the formal C₅² adj-or-eq condition
    fails. -/
private lemma crossNonAdj52_spec (a b : ZMod 5 × ZMod 5) :
    crossNonAdj52 a b = true ↔
    ¬((a.1 = b.1 ∨ (fractionGraph 5 2).Adj a.1 b.1) ∧
      (a.2 = b.2 ∨ (fractionGraph 5 2).Adj a.2 b.2)) := by
  revert a b; native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma cross_compat_of_IS52C
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5)))
    (hIS : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))).IsIndepSet ↑S)
    (x y : ZMod 5 × (ZMod 5 × ZMod 5))
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h1 : x.1 = y.1 ∨ (fractionGraph 5 2).Adj x.1 y.1) :
    crossNonAdj52 x.2 y.2 = true := by
  rw [crossNonAdj52_spec]
  intro ⟨hc1, hc2⟩
  have hnadj : ¬(strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))).Adj x y :=
    (SimpleGraph.isIndepSet_iff _).mp hIS
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  apply hnadj
  refine ⟨hxy, ?_, ?_⟩
  · exact h1
  · by_cases heq : x.2 = y.2
    · exact Or.inl heq
    · exact Or.inr ⟨heq, hc1, hc2⟩

private lemma enc52_injective : Function.Injective enc52 := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [enc52] at h
  have ha1 := a1.isLt; have ha2 := a2.isLt
  have hb1 := b1.isLt; have hb2 := b2.isLt
  have h1 : a1.val = b1.val := by omega
  have h2 : a2.val = b2.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

private lemma extract_single52C
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) (i : ZMod 5)
    (hcard : 0 < (layerFiber52C S i).card) :
    ∃ a : ZMod 5 × ZMod 5, (i, a) ∈ S := by
  obtain ⟨⟨j, a⟩, hja⟩ := Finset.card_pos.mp hcard
  rw [layerFiber52C, Finset.mem_filter] at hja
  exact ⟨a, hja.2 ▸ hja.1⟩

private lemma extract_ordered_pair52C
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) (i : ZMod 5)
    (hcard : (layerFiber52C S i).card = 2) :
    ∃ a b : ZMod 5 × ZMod 5,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ a ≠ b ∧
      enc52 a < enc52 b := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, hne, hfib⟩ :=
    Finset.card_eq_two.mp hcard
  have h1 : (i1, a) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert_self _ _
  have h2 : (i2, b) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))
  rw [layerFiber52C, Finset.mem_filter] at h1 h2
  obtain ⟨h1m, h1e⟩ := h1; obtain ⟨h2m, h2e⟩ := h2
  subst h1e; subst h2e
  have hab : a ≠ b := fun h => hne (Prod.ext rfl h)
  rcases Nat.lt_or_gt_of_ne
    (fun h => hab (enc52_injective h)) with hlt | hgt
  · exact ⟨a, b, h1m, h2m, hab, hlt⟩
  · exact ⟨b, a, h2m, h1m, hab.symm, hgt⟩

private lemma extract_ordered_triple52C
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) (i : ZMod 5)
    (hcard : (layerFiber52C S i).card = 3) :
    ∃ a b c : ZMod 5 × ZMod 5,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ (i, c) ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      enc52 a < enc52 b ∧ enc52 b < enc52 c := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, ⟨i3, c⟩, hne12, hne13, hne23, hfib⟩ :=
    Finset.card_eq_three.mp hcard
  have hx1 : (i1, a) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert_self _ _
  have hx2 : (i2, b) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
  have hx3 : (i3, c) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr rfl))))
  rw [layerFiber52C, Finset.mem_filter] at hx1 hx2 hx3
  obtain ⟨h1m, h1e⟩ := hx1; obtain ⟨h2m, h2e⟩ := hx2
  obtain ⟨h3m, h3e⟩ := hx3
  subst h1e; subst h2e; subst h3e
  have hab : a ≠ b := fun h => hne12 (Prod.ext rfl h)
  have hac : a ≠ c := fun h => hne13 (Prod.ext rfl h)
  have hbc : b ≠ c := fun h => hne23 (Prod.ext rfl h)
  have hne_enc_ab := fun h => hab (enc52_injective h)
  have hne_enc_ac := fun h => hac (enc52_injective h)
  have hne_enc_bc := fun h => hbc (enc52_injective h)
  rcases Nat.lt_or_gt_of_ne hne_enc_ab with hab' | hab'
  · rcases Nat.lt_or_gt_of_ne hne_enc_bc with hbc' | hbc'
    · exact ⟨a, b, c, h1m, h2m, h3m, hab, hac, hbc, hab', hbc'⟩
    · rcases Nat.lt_or_gt_of_ne hne_enc_ac with hac' | hac'
      · exact ⟨a, c, b, h1m, h3m, h2m, hac, hab, hbc.symm, hac', hbc'⟩
      · exact ⟨c, a, b, h3m, h1m, h2m, hac.symm, hbc.symm, hab, hac', hab'⟩
  · rcases Nat.lt_or_gt_of_ne hne_enc_bc with hbc' | hbc'
    · rcases Nat.lt_or_gt_of_ne hne_enc_ac with hac' | hac'
      · exact ⟨b, a, c, h2m, h1m, h3m, hab.symm, hbc, hac, hab', hac'⟩
      · exact ⟨b, c, a, h2m, h3m, h1m, hbc, hab.symm, hac.symm, hbc', hac'⟩
    · exact ⟨c, b, a, h3m, h2m, h1m, hbc.symm, hac.symm, hab.symm, hbc', hab'⟩

set_option linter.style.longLine false in
private lemma extract_ordered_quad52C
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5))) (i : ZMod 5)
    (hcard : (layerFiber52C S i).card = 4) :
    ∃ a b c d : ZMod 5 × ZMod 5,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ (i, c) ∈ S ∧ (i, d) ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      enc52 a < enc52 b ∧ enc52 b < enc52 c ∧ enc52 c < enc52 d := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, ⟨i3, c⟩, ⟨i4, d⟩,
    hne12, hne13, hne14, hne23, hne24, hne34, hfib⟩ :=
    Finset.card_eq_four.mp hcard
  have hx1 : (i1, a) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert_self _ _
  have hx2 : (i2, b) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
  have hx3 : (i3, c) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self _ _))))
  have hx4 : (i4, d) ∈ layerFiber52C S i :=
    hfib ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr rfl))))))
  rw [layerFiber52C, Finset.mem_filter] at hx1 hx2 hx3 hx4
  obtain ⟨h1m, h1e⟩ := hx1; obtain ⟨h2m, h2e⟩ := hx2
  obtain ⟨h3m, h3e⟩ := hx3; obtain ⟨h4m, h4e⟩ := hx4
  subst h1e; subst h2e; subst h3e; subst h4e
  have hab : a ≠ b := fun h => hne12 (Prod.ext rfl h)
  have hac : a ≠ c := fun h => hne13 (Prod.ext rfl h)
  have had : a ≠ d := fun h => hne14 (Prod.ext rfl h)
  have hbc : b ≠ c := fun h => hne23 (Prod.ext rfl h)
  have hbd : b ≠ d := fun h => hne24 (Prod.ext rfl h)
  have hcd : c ≠ d := fun h => hne34 (Prod.ext rfl h)
  have hne_enc_ab := fun h => hab (enc52_injective h)
  have hne_enc_ac := fun h => hac (enc52_injective h)
  have hne_enc_ad := fun h => had (enc52_injective h)
  have hne_enc_bc := fun h => hbc (enc52_injective h)
  have hne_enc_bd := fun h => hbd (enc52_injective h)
  have hne_enc_cd := fun h => hcd (enc52_injective h)
  -- Sort a, b, c, d by enc52 using nested case splits
  rcases Nat.lt_or_gt_of_ne hne_enc_ab with hab' | hab'
  · -- a < b
    rcases Nat.lt_or_gt_of_ne hne_enc_ac with hac' | hac'
    · -- a < b, a < c
      rcases Nat.lt_or_gt_of_ne hne_enc_bc with hbc' | hbc'
      · -- a < b < c
        rcases Nat.lt_or_gt_of_ne hne_enc_ad with had' | had'
        · -- a < b < c, a < d
          rcases Nat.lt_or_gt_of_ne hne_enc_bd with hbd' | hbd'
          · -- a < b < c, a < d, b < d
            rcases Nat.lt_or_gt_of_ne hne_enc_cd with hcd' | hcd'
            · -- a < b < c < d
              exact ⟨a, b, c, d, h1m, h2m, h3m, h4m, hab, hac, had, hbc, hbd, hcd, hab', hbc', hcd'⟩
            · -- a < b, c > d, b < d < c
              exact ⟨a, b, d, c, h1m, h2m, h4m, h3m, hab, had, hac, hbd, hbc, hcd.symm, hab', hbd', hcd'⟩
          · -- a < b < c, a < d, d < b
            -- d < b < c
            exact ⟨a, d, b, c, h1m, h4m, h2m, h3m, had, hab, hac, hbd.symm, hcd.symm, hbc, had', hbd', hbc'⟩
        · -- a < b < c, d < a
          -- d < a < b < c
          exact ⟨d, a, b, c, h4m, h1m, h2m, h3m, had.symm, hbd.symm, hcd.symm, hab, hac, hbc, had', hab', hbc'⟩
      · -- a < b, c < b, a < c (need to determine a vs c)
        -- c < b
        rcases Nat.lt_or_gt_of_ne hne_enc_ad with had' | had'
        · -- a < c, c < b, a < d
          rcases Nat.lt_or_gt_of_ne hne_enc_cd with hcd' | hcd'
          · -- a, c < b, c < d, a < d, a < c
            rcases Nat.lt_or_gt_of_ne hne_enc_bd with hbd' | hbd'
            · -- a < c < d, b < d ... but c < b so a < c < b and c < d
              -- need b vs d: b < d
              exact ⟨a, c, b, d, h1m, h3m, h2m, h4m, hac, hab, had, hbc.symm, hcd, hbd, hac', hbc', hbd'⟩
            · -- a < c, c < b, c < d, d < b
              exact ⟨a, c, d, b, h1m, h3m, h4m, h2m, hac, had, hab, hcd, hbc.symm, hbd.symm, hac', hcd', hbd'⟩
          · -- a < c, c < b, d < c, a < d
            -- a < d < c < b
            exact ⟨a, d, c, b, h1m, h4m, h3m, h2m, had, hac, hab, hcd.symm, hbd.symm, hbc.symm, had', hcd', hbc'⟩
        · -- a < c, c < b, d < a
          -- d < a < c < b
          exact ⟨d, a, c, b, h4m, h1m, h3m, h2m, had.symm, hcd.symm, hbd.symm, hac, hab, hbc.symm, had', hac', hbc'⟩
    · -- a < b, c < a
      -- c < a < b
      rcases Nat.lt_or_gt_of_ne hne_enc_ad with had' | had'
      · -- c < a < b, a < d
        rcases Nat.lt_or_gt_of_ne hne_enc_bd with hbd' | hbd'
        · -- c < a < b < d
          rcases Nat.lt_or_gt_of_ne hne_enc_cd with hcd' | hcd'
          · exact ⟨c, a, b, d, h3m, h1m, h2m, h4m, hac.symm, hbc.symm, hcd, hab, had, hbd, hac', hab', hbd'⟩
          · -- c < a, a < b, b < d, d < c ... contradiction: c < a < b < d but d < c
            exact absurd (Nat.lt_trans (Nat.lt_trans hac' hab') hbd') (Nat.not_lt.mpr (Nat.le_of_lt hcd'))
        · -- c < a < b, a < d, d < b
          -- c < a < d < b? No need to check c vs d
          rcases Nat.lt_or_gt_of_ne hne_enc_cd with hcd' | hcd'
          · exact ⟨c, a, d, b, h3m, h1m, h4m, h2m, hac.symm, hcd, hbc.symm, had, hab, hbd.symm, hac', had', hbd'⟩
          · -- d < c < a, but a < d: contradiction
            exact absurd had' (Nat.not_lt.mpr (Nat.le_of_lt (Nat.lt_trans hcd' hac')))
      · -- c < a < b, d < a
        rcases Nat.lt_or_gt_of_ne hne_enc_cd with hcd' | hcd'
        · -- c < d, d < a < b
          exact ⟨c, d, a, b, h3m, h4m, h1m, h2m, hcd, hac.symm, hbc.symm, had.symm, hbd.symm, hab, hcd', had', hab'⟩
        · -- d < c < a < b
          exact ⟨d, c, a, b, h4m, h3m, h1m, h2m, hcd.symm, had.symm, hbd.symm, hac.symm, hbc.symm, hab, hcd', hac', hab'⟩
  · -- b < a
    rcases Nat.lt_or_gt_of_ne hne_enc_ac with hac' | hac'
    · -- b < a, a < c
      rcases Nat.lt_or_gt_of_ne hne_enc_bc with hbc' | hbc'
      · -- b < a < c (since b < c by transitivity, but let's use hbc')
        rcases Nat.lt_or_gt_of_ne hne_enc_ad with had' | had'
        · -- b < a < c, a < d
          rcases Nat.lt_or_gt_of_ne hne_enc_bd with hbd' | hbd'
          · -- b < a, a < c, a < d, b < d
            rcases Nat.lt_or_gt_of_ne hne_enc_cd with hcd' | hcd'
            · -- b < a < c < d ... but also a < d
              exact ⟨b, a, c, d, h2m, h1m, h3m, h4m, hab.symm, hbc, hbd, hac, had, hcd, hab', hac', hcd'⟩
            · -- b < a, a < c, a < d, b < d, d < c
              exact ⟨b, a, d, c, h2m, h1m, h4m, h3m, hab.symm, hbd, hbc, had, hac, hcd.symm, hab', had', hcd'⟩
          · -- b < a, a < c, a < d, d < b
            -- d < b < a < c
            exact ⟨d, b, a, c, h4m, h2m, h1m, h3m, hbd.symm, had.symm, hcd.symm, hab.symm, hbc, hac, hbd', hab', hac'⟩
        · -- b < a < c, d < a
          rcases Nat.lt_or_gt_of_ne hne_enc_bd with hbd' | hbd'
          · -- b < d, d < a < c
            exact ⟨b, d, a, c, h2m, h4m, h1m, h3m, hbd, hab.symm, hbc, had.symm, hcd.symm, hac, hbd', had', hac'⟩
          · -- d < b < a < c
            exact ⟨d, b, a, c, h4m, h2m, h1m, h3m, hbd.symm, had.symm, hcd.symm, hab.symm, hbc, hac, hbd', hab', hac'⟩
      · -- b < a, a < c, c < b: contradiction (c < b < a but a < c)
        exact absurd hac' (Nat.not_lt.mpr (Nat.le_of_lt (Nat.lt_trans hbc' hab')))
    · -- b < a, c < a
      rcases Nat.lt_or_gt_of_ne hne_enc_bc with hbc' | hbc'
      · -- b < c < a (b < c, c < a)
        rcases Nat.lt_or_gt_of_ne hne_enc_ad with had' | had'
        · -- b < c < a, a < d ... but we need c < a < d
          rcases Nat.lt_or_gt_of_ne hne_enc_bd with hbd' | hbd'
          · -- b < c < a < d
            exact ⟨b, c, a, d, h2m, h3m, h1m, h4m, hbc, hab.symm, hbd, hac.symm, hcd, had, hbc', hac', had'⟩
          · -- d < b < c < a: contradiction (a < d but d < b < ... < a)
            exact absurd had' (Nat.not_lt.mpr (Nat.le_of_lt (Nat.lt_trans (Nat.lt_trans hbd' hbc') hac')))
        · -- b < c, c < a, d < a
          rcases Nat.lt_or_gt_of_ne hne_enc_bd with hbd' | hbd'
          · -- b < c, c < a, d < a, b < d
            rcases Nat.lt_or_gt_of_ne hne_enc_cd with hcd' | hcd'
            · -- b < d, d < ... hmm, b < c, b < d, c < d
              -- b < c < d? Need c vs d. c < d.
              -- But also c < a and d < a. So b < c < d < a
              exact ⟨b, c, d, a, h2m, h3m, h4m, h1m, hbc, hbd, hab.symm, hcd, hac.symm, had.symm, hbc', hcd', had'⟩
            · -- b < c, c < a, d < a, b < d, d < c
              -- b < d < c < a
              exact ⟨b, d, c, a, h2m, h4m, h3m, h1m, hbd, hbc, hab.symm, hcd.symm, had.symm, hac.symm, hbd', hcd', hac'⟩
          · -- d < b < c < a
            exact ⟨d, b, c, a, h4m, h2m, h3m, h1m, hbd.symm, hcd.symm, had.symm, hbc, hab.symm, hac.symm, hbd', hbc', hac'⟩
      · -- b < a, c < a, c < b
        -- c < b < a
        rcases Nat.lt_or_gt_of_ne hne_enc_ad with had' | had'
        · -- c < b < a, a < d: so c < b < a < d
          exact ⟨c, b, a, d, h3m, h2m, h1m, h4m, hbc.symm, hac.symm, hcd, hab.symm, hbd, had, hbc', hab', had'⟩
        · -- c < b < a, d < a
          rcases Nat.lt_or_gt_of_ne hne_enc_cd with hcd' | hcd'
          · -- c < d, d < a, c < b
            rcases Nat.lt_or_gt_of_ne hne_enc_bd with hbd' | hbd'
            · -- c < b < d ... but c < d and b < d
              -- c < b < d < a? Need b < d: yes hbd'
              exact ⟨c, b, d, a, h3m, h2m, h4m, h1m, hbc.symm, hcd, hac.symm, hbd, hab.symm, had.symm, hbc', hbd', had'⟩
            · -- c < d, d < b, c < b, d < a
              -- c < d < b < a? d < b from hbd'
              exact ⟨c, d, b, a, h3m, h4m, h2m, h1m, hcd, hbc.symm, hac.symm, hbd.symm, had.symm, hab.symm, hcd', hbd', hab'⟩
          · -- d < c < b < a
            exact ⟨d, c, b, a, h4m, h3m, h2m, h1m, hcd.symm, hbd.symm, had.symm, hbc.symm, hac.symm, hab.symm, hcd', hbc', hab'⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.nativeDecide false in
set_option maxHeartbeats 4000000 in
-- The 7-case Baumert search contradiction needs elevated heartbeats for elaboration.
private lemma case52C_baumert_contradiction
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 5)))
    (hSis : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))).IsIndepSet ↑S)
    (hScard : S.card = 11)
    (hfbc : ∀ i : ZMod 5,
      (S.filter (fun p =>
        p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card
          ≤ 5) :
    False := by
  -- IP rotation: obtain canonical class c and rotation k
  obtain ⟨c, k, hk⟩ := ip_rotation52C
    (fun i => (layerFiber52C S i).card)
    (by change ∑ i, (layerFiber52C S i).card = 11
        rw [layer52C_sum_eq_card]; exact hScard)
    (fun i => pair_bound_sum52C S i (hfbc i))
  -- Translate to canonical sizes
  let κ : ZMod 5 := k
  set S' := S.image (translateFst52C κ) with hS'_def
  have hIS' := translateFst52C_IS κ S hSis
  have hcanon : ∀ j : ZMod 5,
      (layerFiber52C S' j).card = cs52C c j := by
    intro j
    have h := translateFst52C_layerFiber κ S (j - κ)
    rw [sub_add_cancel] at h
    rw [h, hk (j - κ)]
    congr 1; ext
    change ((j - κ).val + κ.val) % 5 = j.val
    rw [← ZMod.val_add, sub_add_cancel]
  -- Universal cross-compat
  have hcc := cross_compat_of_IS52C S' hIS'
  have hne_layer : ∀ (i j : ZMod 5)
      (a b : ZMod 5 × ZMod 5),
      i ≠ j → (i, a) ≠ (j, b) :=
    fun _ _ _ _ hij h => hij (congr_arg Prod.fst h)
  have cc : ∀ (i j : ZMod 5)
      (a b : ZMod 5 × ZMod 5),
      (i, a) ∈ S' → (j, b) ∈ S' → i ≠ j →
      (fractionGraph 5 2).Adj i j →
      crossNonAdj52 a b = true :=
    fun i j a b ha hb hij hadj =>
      hcc _ _ ha hb (hne_layer i j a b hij) (Or.inr hadj)
  have cc_eq : ∀ (i : ZMod 5)
      (a b : ZMod 5 × ZMod 5),
      (i, a) ∈ S' → (i, b) ∈ S' → a ≠ b →
      crossNonAdj52 a b = true :=
    fun i a b ha hb hab =>
      hcc _ _ ha hb (fun h => hab (congr_arg Prod.snd h))
        (Or.inl rfl)
  -- Helper: compatWith52 via cc and cc_eq
  have compat_of_list : ∀ (i : ZMod 5)
      (a : ZMod 5 × ZMod 5)
      (ws : List (ZMod 5 × (ZMod 5 × ZMod 5))),
      (i, a) ∈ S' →
      (∀ w ∈ ws, w ∈ S' ∧
        (i ≠ w.1 → (fractionGraph 5 2).Adj i w.1) ∧
        (i = w.1 → a ≠ w.2)) →
      compatWith52 a (ws.map Prod.snd) = true := by
    intro i a ws hia hws
    simp only [compatWith52, List.all_eq_true, List.mem_map]
    rintro b ⟨⟨j, b'⟩, hjb_mem, rfl⟩
    have ⟨hjb_S, hadj, hneq⟩ := hws _ hjb_mem
    by_cases hij : i = j
    · subst hij; exact cc_eq i a b' hia hjb_S (hneq rfl)
    · exact cc i j a b' hia hjb_S hij (hadj hij)
  -- C₅ adjacency facts
  have adj01 : (fractionGraph 5 2).Adj 0 1 := by decide
  have adj12 : (fractionGraph 5 2).Adj 1 2 := by decide
  have adj23 : (fractionGraph 5 2).Adj 2 3 := by decide
  have adj34 : (fractionGraph 5 2).Adj 3 4 := by decide
  have adj04 : (fractionGraph 5 2).Adj 0 4 := by decide
  -- Case split on canonical class
  fin_cases c
  ---- Case c = 0: sizes [4, 1, 1, 4, 1] → case52_check1
  · -- Extract witnesses
    obtain ⟨w00, w01, w02, w03, hw00, hw01, hw02, hw03,
      hne_0001, hne_0002, hne_0003, hne_0102, hne_0103, hne_0203,
      hlt_0001, hlt_0102, hlt_0203⟩ :=
      extract_ordered_quad52C S' 0
        (by rw [hcanon]; native_decide)
    obtain ⟨w1, hw1⟩ := extract_single52C S' 1
      (by rw [hcanon]; native_decide)
    obtain ⟨w2, hw2⟩ := extract_single52C S' 2
      (by rw [hcanon]; native_decide)
    obtain ⟨w30, w31, w32, w33, hw30, hw31, hw32, hw33,
      hne_3031, hne_3032, hne_3033, hne_3132, hne_3133, hne_3233,
      hlt_3031, hlt_3132, hlt_3233⟩ :=
      extract_ordered_quad52C S' 3
        (by rw [hcanon]; native_decide)
    obtain ⟨w4, hw4⟩ := extract_single52C S' 4
      (by rw [hcanon]; native_decide)
    -- crossNonAdj52 for layer 0 quad
    have cn_0001 := cc_eq 0 w00 w01 hw00 hw01 hne_0001
    have cn_0002 := cc_eq 0 w00 w02 hw00 hw02 hne_0002
    have cn_0003 := cc_eq 0 w00 w03 hw00 hw03 hne_0003
    have cn_0102 := cc_eq 0 w01 w02 hw01 hw02 hne_0102
    have cn_0103 := cc_eq 0 w01 w03 hw01 hw03 hne_0103
    have cn_0203 := cc_eq 0 w02 w03 hw02 hw03 hne_0203
    -- crossNonAdj52 for layer 3 quad
    have cn_3031 := cc_eq 3 w30 w31 hw30 hw31 hne_3031
    have cn_3032 := cc_eq 3 w30 w32 hw30 hw32 hne_3032
    have cn_3033 := cc_eq 3 w30 w33 hw30 hw33 hne_3033
    have cn_3132 := cc_eq 3 w31 w32 hw31 hw32 hne_3132
    have cn_3133 := cc_eq 3 w31 w33 hw31 hw33 hne_3133
    have cn_3233 := cc_eq 3 w32 w33 hw32 hw33 hne_3233
    -- compatWith52 for layer 1: compat with [v00, v01, v02, v03]
    have cpt_v1 := compat_of_list 1 w1
      [(0, w00), (0, w01), (0, w02), (0, w03)] hw1
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw03, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 2: compat with [v1]
    have cpt_v2 := compat_of_list 2 w2
      [(1, w1)] hw2
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 3 elements: compat with [v2]
    have cpt_v30 := compat_of_list 3 w30
      [(2, w2)] hw30
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw2, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v31 := compat_of_list 3 w31
      [(2, w2)] hw31
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw2, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v32 := compat_of_list 3 w32
      [(2, w2)] hw32
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw2, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v33 := compat_of_list 3 w33
      [(2, w2)] hw33
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw2, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 4: compat with [v30,v31,v32,v33,v00,v01,v02,v03]
    have cpt_v4 := compat_of_list 4 w4
      [(3, w30), (3, w31), (3, w32), (3, w33),
       (0, w00), (0, w01), (0, w02), (0, w03)] hw4
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨hw30, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw31, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw32, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw33, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw03, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- Normalize List.map Prod.snd
    simp only [List.map] at cpt_v1 cpt_v2 cpt_v30 cpt_v31 cpt_v32 cpt_v33 cpt_v4
    -- Contradiction via case52_check1
    have hf : case52_check1 = false := by
      unfold case52_check1; simp only [Bool.not_eq_false']
      apply List.any_of_mem (mem_verts52 w00)
      apply List.any_of_mem (mem_verts52 w01)
      simp only [decide_eq_true hlt_0001, cn_0001, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w02)
      simp only [decide_eq_true hlt_0102, cn_0002, cn_0102, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w03)
      simp only [decide_eq_true hlt_0203, cn_0003, cn_0103, cn_0203, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w1)
      simp only [cpt_v1, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w2)
      simp only [cpt_v2, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w30)
      simp only [cpt_v30, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w31)
      simp only [decide_eq_true hlt_3031, cn_3031, cpt_v31, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w32)
      simp only [decide_eq_true hlt_3132, cn_3032, cn_3132, cpt_v32, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w33)
      simp only [decide_eq_true hlt_3233, cn_3033, cn_3133, cn_3233, cpt_v33, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w4)
      simp only [cpt_v4]
    have hcheck_true : case52_check1 = true := by
      have h := case52_check_true
      simp only [case52_check, Bool.and_eq_true] at h
      exact h.1.1.1.1.1.1
    exact absurd hcheck_true (by rw [hf]; decide)
  ---- Case c = 1: sizes [4, 1, 2, 3, 1] → case52_check2
  · -- Extract witnesses
    obtain ⟨w00, w01, w02, w03, hw00, hw01, hw02, hw03,
      hne_0001, hne_0002, hne_0003, hne_0102, hne_0103, hne_0203,
      hlt_0001, hlt_0102, hlt_0203⟩ :=
      extract_ordered_quad52C S' 0
        (by rw [hcanon]; native_decide)
    obtain ⟨w1, hw1⟩ := extract_single52C S' 1
      (by rw [hcanon]; native_decide)
    obtain ⟨w20, w21, hw20, hw21, hne_2021, hlt_2021⟩ :=
      extract_ordered_pair52C S' 2
        (by rw [hcanon]; native_decide)
    obtain ⟨w30, w31, w32, hw30, hw31, hw32,
      hne_3031, hne_3032, hne_3132,
      hlt_3031, hlt_3132⟩ :=
      extract_ordered_triple52C S' 3
        (by rw [hcanon]; native_decide)
    obtain ⟨w4, hw4⟩ := extract_single52C S' 4
      (by rw [hcanon]; native_decide)
    -- crossNonAdj52 for layer 0 quad
    have cn_0001 := cc_eq 0 w00 w01 hw00 hw01 hne_0001
    have cn_0002 := cc_eq 0 w00 w02 hw00 hw02 hne_0002
    have cn_0003 := cc_eq 0 w00 w03 hw00 hw03 hne_0003
    have cn_0102 := cc_eq 0 w01 w02 hw01 hw02 hne_0102
    have cn_0103 := cc_eq 0 w01 w03 hw01 hw03 hne_0103
    have cn_0203 := cc_eq 0 w02 w03 hw02 hw03 hne_0203
    -- crossNonAdj52 for layer 2 pair
    have cn_2021 := cc_eq 2 w20 w21 hw20 hw21 hne_2021
    -- crossNonAdj52 for layer 3 triple
    have cn_3031 := cc_eq 3 w30 w31 hw30 hw31 hne_3031
    have cn_3032 := cc_eq 3 w30 w32 hw30 hw32 hne_3032
    have cn_3132 := cc_eq 3 w31 w32 hw31 hw32 hne_3132
    -- compatWith52 for layer 1: compat with [v00, v01, v02, v03]
    have cpt_v1 := compat_of_list 1 w1
      [(0, w00), (0, w01), (0, w02), (0, w03)] hw1
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw03, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 2: compat with [v1]
    have cpt_v20 := compat_of_list 2 w20
      [(1, w1)] hw20
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v21 := compat_of_list 2 w21
      [(1, w1)] hw21
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 3: compat with [v20, v21]
    have cpt_v30 := compat_of_list 3 w30
      [(2, w20), (2, w21)] hw30
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v31 := compat_of_list 3 w31
      [(2, w20), (2, w21)] hw31
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v32 := compat_of_list 3 w32
      [(2, w20), (2, w21)] hw32
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 4: compat with [v30,v31,v32,v00,v01,v02,v03]
    have cpt_v4 := compat_of_list 4 w4
      [(3, w30), (3, w31), (3, w32),
       (0, w00), (0, w01), (0, w02), (0, w03)] hw4
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨hw30, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw31, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw32, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw03, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- Normalize List.map Prod.snd
    simp only [List.map] at cpt_v1 cpt_v20 cpt_v21 cpt_v30 cpt_v31 cpt_v32 cpt_v4
    -- Contradiction via case52_check2
    have hf : case52_check2 = false := by
      unfold case52_check2; simp only [Bool.not_eq_false']
      apply List.any_of_mem (mem_verts52 w00)
      apply List.any_of_mem (mem_verts52 w01)
      simp only [decide_eq_true hlt_0001, cn_0001, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w02)
      simp only [decide_eq_true hlt_0102, cn_0002, cn_0102, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w03)
      simp only [decide_eq_true hlt_0203, cn_0003, cn_0103, cn_0203, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w1)
      simp only [cpt_v1, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w20)
      simp only [cpt_v20, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w21)
      simp only [decide_eq_true hlt_2021, cn_2021, cpt_v21, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w30)
      simp only [cpt_v30, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w31)
      simp only [decide_eq_true hlt_3031, cn_3031, cpt_v31, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w32)
      simp only [decide_eq_true hlt_3132, cn_3032, cn_3132, cpt_v32, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w4)
      simp only [cpt_v4]
    have hcheck_true : case52_check2 = true := by
      have h := case52_check_true
      simp only [case52_check, Bool.and_eq_true] at h
      exact h.1.1.1.1.1.2
    exact absurd hcheck_true (by rw [hf]; decide)
  ---- Case c = 2: sizes [4, 1, 3, 2, 1] → case52_check3
  · -- Extract witnesses
    obtain ⟨w00, w01, w02, w03, hw00, hw01, hw02, hw03,
      hne_0001, hne_0002, hne_0003, hne_0102, hne_0103, hne_0203,
      hlt_0001, hlt_0102, hlt_0203⟩ :=
      extract_ordered_quad52C S' 0
        (by rw [hcanon]; native_decide)
    obtain ⟨w1, hw1⟩ := extract_single52C S' 1
      (by rw [hcanon]; native_decide)
    obtain ⟨w20, w21, w22, hw20, hw21, hw22,
      hne_2021, hne_2022, hne_2122,
      hlt_2021, hlt_2122⟩ :=
      extract_ordered_triple52C S' 2
        (by rw [hcanon]; native_decide)
    obtain ⟨w30, w31, hw30, hw31, hne_3031, hlt_3031⟩ :=
      extract_ordered_pair52C S' 3
        (by rw [hcanon]; native_decide)
    obtain ⟨w4, hw4⟩ := extract_single52C S' 4
      (by rw [hcanon]; native_decide)
    -- crossNonAdj52 for layer 0 quad
    have cn_0001 := cc_eq 0 w00 w01 hw00 hw01 hne_0001
    have cn_0002 := cc_eq 0 w00 w02 hw00 hw02 hne_0002
    have cn_0003 := cc_eq 0 w00 w03 hw00 hw03 hne_0003
    have cn_0102 := cc_eq 0 w01 w02 hw01 hw02 hne_0102
    have cn_0103 := cc_eq 0 w01 w03 hw01 hw03 hne_0103
    have cn_0203 := cc_eq 0 w02 w03 hw02 hw03 hne_0203
    -- crossNonAdj52 for layer 2 triple
    have cn_2021 := cc_eq 2 w20 w21 hw20 hw21 hne_2021
    have cn_2022 := cc_eq 2 w20 w22 hw20 hw22 hne_2022
    have cn_2122 := cc_eq 2 w21 w22 hw21 hw22 hne_2122
    -- crossNonAdj52 for layer 3 pair
    have cn_3031 := cc_eq 3 w30 w31 hw30 hw31 hne_3031
    -- compatWith52 for layer 1: compat with [v00, v01, v02, v03]
    have cpt_v1 := compat_of_list 1 w1
      [(0, w00), (0, w01), (0, w02), (0, w03)] hw1
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw03, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 2: compat with [v1]
    have cpt_v20 := compat_of_list 2 w20
      [(1, w1)] hw20
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v21 := compat_of_list 2 w21
      [(1, w1)] hw21
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v22 := compat_of_list 2 w22
      [(1, w1)] hw22
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 3: compat with [v20, v21, v22]
    have cpt_v30 := compat_of_list 3 w30
      [(2, w20), (2, w21), (2, w22)] hw30
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw22, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v31 := compat_of_list 3 w31
      [(2, w20), (2, w21), (2, w22)] hw31
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw22, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 4: compat with [v30,v31,v00,v01,v02,v03]
    have cpt_v4 := compat_of_list 4 w4
      [(3, w30), (3, w31),
       (0, w00), (0, w01), (0, w02), (0, w03)] hw4
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨hw30, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw31, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw03, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- Normalize List.map Prod.snd
    simp only [List.map] at cpt_v1 cpt_v20 cpt_v21 cpt_v22 cpt_v30 cpt_v31 cpt_v4
    -- Contradiction via case52_check3
    have hf : case52_check3 = false := by
      unfold case52_check3; simp only [Bool.not_eq_false']
      apply List.any_of_mem (mem_verts52 w00)
      apply List.any_of_mem (mem_verts52 w01)
      simp only [decide_eq_true hlt_0001, cn_0001, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w02)
      simp only [decide_eq_true hlt_0102, cn_0002, cn_0102, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w03)
      simp only [decide_eq_true hlt_0203, cn_0003, cn_0103, cn_0203, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w1)
      simp only [cpt_v1, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w20)
      simp only [cpt_v20, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w21)
      simp only [decide_eq_true hlt_2021, cn_2021, cpt_v21, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w22)
      simp only [decide_eq_true hlt_2122, cn_2022, cn_2122, cpt_v22, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w30)
      simp only [cpt_v30, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w31)
      simp only [decide_eq_true hlt_3031, cn_3031, cpt_v31, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w4)
      simp only [cpt_v4]
    have hcheck_true : case52_check3 = true := by
      have h := case52_check_true
      simp only [case52_check, Bool.and_eq_true] at h
      exact h.1.1.1.1.2
    exact absurd hcheck_true (by rw [hf]; decide)
  ---- Case c = 3: sizes [3, 2, 3, 2, 1] → case52_check4
  · -- Extract witnesses
    obtain ⟨w00, w01, w02, hw00, hw01, hw02,
      hne_0001, hne_0002, hne_0102,
      hlt_0001, hlt_0102⟩ :=
      extract_ordered_triple52C S' 0
        (by rw [hcanon]; native_decide)
    obtain ⟨w10, w11, hw10, hw11, hne_1011, hlt_1011⟩ :=
      extract_ordered_pair52C S' 1
        (by rw [hcanon]; native_decide)
    obtain ⟨w20, w21, w22, hw20, hw21, hw22,
      hne_2021, hne_2022, hne_2122,
      hlt_2021, hlt_2122⟩ :=
      extract_ordered_triple52C S' 2
        (by rw [hcanon]; native_decide)
    obtain ⟨w30, w31, hw30, hw31, hne_3031, hlt_3031⟩ :=
      extract_ordered_pair52C S' 3
        (by rw [hcanon]; native_decide)
    obtain ⟨w4, hw4⟩ := extract_single52C S' 4
      (by rw [hcanon]; native_decide)
    -- crossNonAdj52 for layer 0 triple
    have cn_0001 := cc_eq 0 w00 w01 hw00 hw01 hne_0001
    have cn_0002 := cc_eq 0 w00 w02 hw00 hw02 hne_0002
    have cn_0102 := cc_eq 0 w01 w02 hw01 hw02 hne_0102
    -- crossNonAdj52 for layer 1 pair
    have cn_1011 := cc_eq 1 w10 w11 hw10 hw11 hne_1011
    -- crossNonAdj52 for layer 2 triple
    have cn_2021 := cc_eq 2 w20 w21 hw20 hw21 hne_2021
    have cn_2022 := cc_eq 2 w20 w22 hw20 hw22 hne_2022
    have cn_2122 := cc_eq 2 w21 w22 hw21 hw22 hne_2122
    -- crossNonAdj52 for layer 3 pair
    have cn_3031 := cc_eq 3 w30 w31 hw30 hw31 hne_3031
    -- compatWith52 for layer 1: compat with [v00, v01, v02]
    have cpt_v10 := compat_of_list 1 w10
      [(0, w00), (0, w01), (0, w02)] hw10
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v11 := compat_of_list 1 w11
      [(0, w00), (0, w01), (0, w02)] hw11
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 2: compat with [v10, v11]
    have cpt_v20 := compat_of_list 2 w20
      [(1, w10), (1, w11)] hw20
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw10, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw11, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v21 := compat_of_list 2 w21
      [(1, w10), (1, w11)] hw21
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw10, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw11, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v22 := compat_of_list 2 w22
      [(1, w10), (1, w11)] hw22
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw10, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw11, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 3: compat with [v20, v21, v22]
    have cpt_v30 := compat_of_list 3 w30
      [(2, w20), (2, w21), (2, w22)] hw30
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw22, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v31 := compat_of_list 3 w31
      [(2, w20), (2, w21), (2, w22)] hw31
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw22, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 4: compat with [v30,v31,v00,v01,v02]
    have cpt_v4 := compat_of_list 4 w4
      [(3, w30), (3, w31),
       (0, w00), (0, w01), (0, w02)] hw4
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl
          · exact ⟨hw30, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw31, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- Normalize List.map Prod.snd
    simp only [List.map] at cpt_v10 cpt_v11 cpt_v20 cpt_v21 cpt_v22 cpt_v30 cpt_v31 cpt_v4
    -- Contradiction via case52_check4
    have hf : case52_check4 = false := by
      unfold case52_check4; simp only [Bool.not_eq_false']
      apply List.any_of_mem (mem_verts52 w00)
      apply List.any_of_mem (mem_verts52 w01)
      simp only [decide_eq_true hlt_0001, cn_0001, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w02)
      simp only [decide_eq_true hlt_0102, cn_0002, cn_0102, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w10)
      simp only [cpt_v10, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w11)
      simp only [decide_eq_true hlt_1011, cn_1011, cpt_v11, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w20)
      simp only [cpt_v20, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w21)
      simp only [decide_eq_true hlt_2021, cn_2021, cpt_v21, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w22)
      simp only [decide_eq_true hlt_2122, cn_2022, cn_2122, cpt_v22, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w30)
      simp only [cpt_v30, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w31)
      simp only [decide_eq_true hlt_3031, cn_3031, cpt_v31, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w4)
      simp only [cpt_v4]
    have hcheck_true : case52_check4 = true := by
      have h := case52_check_true
      simp only [case52_check, Bool.and_eq_true] at h
      exact h.1.1.1.2
    exact absurd hcheck_true (by rw [hf]; decide)
  ---- Case c = 4: sizes [3, 2, 3, 1, 2] → case52_check5
  · -- Extract witnesses
    obtain ⟨w00, w01, w02, hw00, hw01, hw02,
      hne_0001, hne_0002, hne_0102,
      hlt_0001, hlt_0102⟩ :=
      extract_ordered_triple52C S' 0
        (by rw [hcanon]; native_decide)
    obtain ⟨w10, w11, hw10, hw11, hne_1011, hlt_1011⟩ :=
      extract_ordered_pair52C S' 1
        (by rw [hcanon]; native_decide)
    obtain ⟨w20, w21, w22, hw20, hw21, hw22,
      hne_2021, hne_2022, hne_2122,
      hlt_2021, hlt_2122⟩ :=
      extract_ordered_triple52C S' 2
        (by rw [hcanon]; native_decide)
    obtain ⟨w3, hw3⟩ := extract_single52C S' 3
      (by rw [hcanon]; native_decide)
    obtain ⟨w40, w41, hw40, hw41, hne_4041, hlt_4041⟩ :=
      extract_ordered_pair52C S' 4
        (by rw [hcanon]; native_decide)
    -- crossNonAdj52 for layer 0 triple
    have cn_0001 := cc_eq 0 w00 w01 hw00 hw01 hne_0001
    have cn_0002 := cc_eq 0 w00 w02 hw00 hw02 hne_0002
    have cn_0102 := cc_eq 0 w01 w02 hw01 hw02 hne_0102
    -- crossNonAdj52 for layer 1 pair
    have cn_1011 := cc_eq 1 w10 w11 hw10 hw11 hne_1011
    -- crossNonAdj52 for layer 2 triple
    have cn_2021 := cc_eq 2 w20 w21 hw20 hw21 hne_2021
    have cn_2022 := cc_eq 2 w20 w22 hw20 hw22 hne_2022
    have cn_2122 := cc_eq 2 w21 w22 hw21 hw22 hne_2122
    -- crossNonAdj52 for layer 4 pair
    have cn_4041 := cc_eq 4 w40 w41 hw40 hw41 hne_4041
    -- compatWith52 for layer 1: compat with [v00, v01, v02]
    have cpt_v10 := compat_of_list 1 w10
      [(0, w00), (0, w01), (0, w02)] hw10
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v11 := compat_of_list 1 w11
      [(0, w00), (0, w01), (0, w02)] hw11
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 2: compat with [v10, v11]
    have cpt_v20 := compat_of_list 2 w20
      [(1, w10), (1, w11)] hw20
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw10, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw11, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v21 := compat_of_list 2 w21
      [(1, w10), (1, w11)] hw21
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw10, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw11, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v22 := compat_of_list 2 w22
      [(1, w10), (1, w11)] hw22
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw10, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw11, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 3: compat with [v20, v21, v22]
    have cpt_v3 := compat_of_list 3 w3
      [(2, w20), (2, w21), (2, w22)] hw3
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw22, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 4: compat with [v3,v00,v01,v02]
    have cpt_v40 := compat_of_list 4 w40
      [(3, w3), (0, w00), (0, w01), (0, w02)] hw40
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact ⟨hw3, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v41 := compat_of_list 4 w41
      [(3, w3), (0, w00), (0, w01), (0, w02)] hw41
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact ⟨hw3, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- Normalize List.map Prod.snd
    simp only [List.map] at cpt_v10 cpt_v11 cpt_v20 cpt_v21 cpt_v22 cpt_v3 cpt_v40 cpt_v41
    -- Contradiction via case52_check5
    have hf : case52_check5 = false := by
      unfold case52_check5; simp only [Bool.not_eq_false']
      apply List.any_of_mem (mem_verts52 w00)
      apply List.any_of_mem (mem_verts52 w01)
      simp only [decide_eq_true hlt_0001, cn_0001, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w02)
      simp only [decide_eq_true hlt_0102, cn_0002, cn_0102, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w10)
      simp only [cpt_v10, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w11)
      simp only [decide_eq_true hlt_1011, cn_1011, cpt_v11, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w20)
      simp only [cpt_v20, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w21)
      simp only [decide_eq_true hlt_2021, cn_2021, cpt_v21, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w22)
      simp only [decide_eq_true hlt_2122, cn_2022, cn_2122, cpt_v22, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w3)
      simp only [cpt_v3, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w40)
      simp only [cpt_v40, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w41)
      simp only [decide_eq_true hlt_4041, cn_4041, cpt_v41, Bool.true_and]
    have hcheck_true : case52_check5 = true := by
      have h := case52_check_true
      simp only [case52_check, Bool.and_eq_true] at h
      exact h.1.1.2
    exact absurd hcheck_true (by rw [hf]; decide)
  ---- Case c = 5: sizes [3, 1, 3, 2, 2] → case52_check6
  · -- Extract witnesses
    obtain ⟨w00, w01, w02, hw00, hw01, hw02,
      hne_0001, hne_0002, hne_0102,
      hlt_0001, hlt_0102⟩ :=
      extract_ordered_triple52C S' 0
        (by rw [hcanon]; native_decide)
    obtain ⟨w1, hw1⟩ := extract_single52C S' 1
      (by rw [hcanon]; native_decide)
    obtain ⟨w20, w21, w22, hw20, hw21, hw22,
      hne_2021, hne_2022, hne_2122,
      hlt_2021, hlt_2122⟩ :=
      extract_ordered_triple52C S' 2
        (by rw [hcanon]; native_decide)
    obtain ⟨w30, w31, hw30, hw31, hne_3031, hlt_3031⟩ :=
      extract_ordered_pair52C S' 3
        (by rw [hcanon]; native_decide)
    obtain ⟨w40, w41, hw40, hw41, hne_4041, hlt_4041⟩ :=
      extract_ordered_pair52C S' 4
        (by rw [hcanon]; native_decide)
    -- crossNonAdj52 for layer 0 triple
    have cn_0001 := cc_eq 0 w00 w01 hw00 hw01 hne_0001
    have cn_0002 := cc_eq 0 w00 w02 hw00 hw02 hne_0002
    have cn_0102 := cc_eq 0 w01 w02 hw01 hw02 hne_0102
    -- crossNonAdj52 for layer 2 triple
    have cn_2021 := cc_eq 2 w20 w21 hw20 hw21 hne_2021
    have cn_2022 := cc_eq 2 w20 w22 hw20 hw22 hne_2022
    have cn_2122 := cc_eq 2 w21 w22 hw21 hw22 hne_2122
    -- crossNonAdj52 for layer 3 pair
    have cn_3031 := cc_eq 3 w30 w31 hw30 hw31 hne_3031
    -- crossNonAdj52 for layer 4 pair
    have cn_4041 := cc_eq 4 w40 w41 hw40 hw41 hne_4041
    -- compatWith52 for layer 1: compat with [v00, v01, v02]
    have cpt_v1 := compat_of_list 1 w1
      [(0, w00), (0, w01), (0, w02)] hw1
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 2: compat with [v1]
    have cpt_v20 := compat_of_list 2 w20
      [(1, w1)] hw20
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v21 := compat_of_list 2 w21
      [(1, w1)] hw21
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v22 := compat_of_list 2 w22
      [(1, w1)] hw22
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl
          · exact ⟨hw1, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 3: compat with [v20, v21, v22]
    have cpt_v30 := compat_of_list 3 w30
      [(2, w20), (2, w21), (2, w22)] hw30
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw22, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v31 := compat_of_list 3 w31
      [(2, w20), (2, w21), (2, w22)] hw31
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw22, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 4: compat with [v30,v31,v00,v01,v02]
    have cpt_v40 := compat_of_list 4 w40
      [(3, w30), (3, w31),
       (0, w00), (0, w01), (0, w02)] hw40
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl
          · exact ⟨hw30, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw31, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v41 := compat_of_list 4 w41
      [(3, w30), (3, w31),
       (0, w00), (0, w01), (0, w02)] hw41
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl
          · exact ⟨hw30, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw31, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- Normalize List.map Prod.snd
    simp only [List.map] at cpt_v1 cpt_v20 cpt_v21 cpt_v22 cpt_v30 cpt_v31 cpt_v40 cpt_v41
    -- Contradiction via case52_check6
    have hf : case52_check6 = false := by
      unfold case52_check6; simp only [Bool.not_eq_false']
      apply List.any_of_mem (mem_verts52 w00)
      apply List.any_of_mem (mem_verts52 w01)
      simp only [decide_eq_true hlt_0001, cn_0001, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w02)
      simp only [decide_eq_true hlt_0102, cn_0002, cn_0102, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w1)
      simp only [cpt_v1, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w20)
      simp only [cpt_v20, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w21)
      simp only [decide_eq_true hlt_2021, cn_2021, cpt_v21, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w22)
      simp only [decide_eq_true hlt_2122, cn_2022, cn_2122, cpt_v22, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w30)
      simp only [cpt_v30, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w31)
      simp only [decide_eq_true hlt_3031, cn_3031, cpt_v31, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w40)
      simp only [cpt_v40, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w41)
      simp only [decide_eq_true hlt_4041, cn_4041, cpt_v41, Bool.true_and]
    have hcheck_true : case52_check6 = true := by
      have h := case52_check_true
      simp only [case52_check, Bool.and_eq_true] at h
      exact h.1.2
    exact absurd hcheck_true (by rw [hf]; decide)
  ---- Case c = 6: sizes [3, 2, 2, 2, 2] → case52_check7
  · -- Extract witnesses
    obtain ⟨w00, w01, w02, hw00, hw01, hw02,
      hne_0001, hne_0002, hne_0102,
      hlt_0001, hlt_0102⟩ :=
      extract_ordered_triple52C S' 0
        (by rw [hcanon]; native_decide)
    obtain ⟨w10, w11, hw10, hw11, hne_1011, hlt_1011⟩ :=
      extract_ordered_pair52C S' 1
        (by rw [hcanon]; native_decide)
    obtain ⟨w20, w21, hw20, hw21, hne_2021, hlt_2021⟩ :=
      extract_ordered_pair52C S' 2
        (by rw [hcanon]; native_decide)
    obtain ⟨w30, w31, hw30, hw31, hne_3031, hlt_3031⟩ :=
      extract_ordered_pair52C S' 3
        (by rw [hcanon]; native_decide)
    obtain ⟨w40, w41, hw40, hw41, hne_4041, hlt_4041⟩ :=
      extract_ordered_pair52C S' 4
        (by rw [hcanon]; native_decide)
    -- crossNonAdj52 for layer 0 triple
    have cn_0001 := cc_eq 0 w00 w01 hw00 hw01 hne_0001
    have cn_0002 := cc_eq 0 w00 w02 hw00 hw02 hne_0002
    have cn_0102 := cc_eq 0 w01 w02 hw01 hw02 hne_0102
    -- crossNonAdj52 for layer 1 pair
    have cn_1011 := cc_eq 1 w10 w11 hw10 hw11 hne_1011
    -- crossNonAdj52 for layer 2 pair
    have cn_2021 := cc_eq 2 w20 w21 hw20 hw21 hne_2021
    -- crossNonAdj52 for layer 3 pair
    have cn_3031 := cc_eq 3 w30 w31 hw30 hw31 hne_3031
    -- crossNonAdj52 for layer 4 pair
    have cn_4041 := cc_eq 4 w40 w41 hw40 hw41 hne_4041
    -- compatWith52 for layer 1: compat with [v00, v01, v02]
    have cpt_v10 := compat_of_list 1 w10
      [(0, w00), (0, w01), (0, w02)] hw10
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v11 := compat_of_list 1 w11
      [(0, w00), (0, w01), (0, w02)] hw11
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ⟨hw00, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj01.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 2: compat with [v10, v11]
    have cpt_v20 := compat_of_list 2 w20
      [(1, w10), (1, w11)] hw20
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw10, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw11, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v21 := compat_of_list 2 w21
      [(1, w10), (1, w11)] hw21
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw10, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw11, fun _ => adj12.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 3: compat with [v20, v21]
    have cpt_v30 := compat_of_list 3 w30
      [(2, w20), (2, w21)] hw30
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v31 := compat_of_list 3 w31
      [(2, w20), (2, w21)] hw31
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hw20, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw21, fun _ => adj23.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- compatWith52 for layer 4: compat with [v30,v31,v00,v01,v02]
    have cpt_v40 := compat_of_list 4 w40
      [(3, w30), (3, w31),
       (0, w00), (0, w01), (0, w02)] hw40
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl
          · exact ⟨hw30, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw31, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    have cpt_v41 := compat_of_list 4 w41
      [(3, w30), (3, w31),
       (0, w00), (0, w01), (0, w02)] hw41
      (by intro w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl
          · exact ⟨hw30, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw31, fun _ => adj34.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw00, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw01, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩
          · exact ⟨hw02, fun _ => adj04.symm,
              fun h => absurd (show _ = _ by simpa using h) (by decide)⟩)
    -- Normalize List.map Prod.snd
    simp only [List.map] at cpt_v10 cpt_v11 cpt_v20 cpt_v21 cpt_v30 cpt_v31 cpt_v40 cpt_v41
    -- Contradiction via case52_check7
    have hf : case52_check7 = false := by
      unfold case52_check7; simp only [Bool.not_eq_false']
      apply List.any_of_mem (mem_verts52 w00)
      apply List.any_of_mem (mem_verts52 w01)
      simp only [decide_eq_true hlt_0001, cn_0001, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w02)
      simp only [decide_eq_true hlt_0102, cn_0002, cn_0102, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w10)
      simp only [cpt_v10, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w11)
      simp only [decide_eq_true hlt_1011, cn_1011, cpt_v11, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w20)
      simp only [cpt_v20, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w21)
      simp only [decide_eq_true hlt_2021, cn_2021, cpt_v21, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w30)
      simp only [cpt_v30, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w31)
      simp only [decide_eq_true hlt_3031, cn_3031, cpt_v31, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w40)
      simp only [cpt_v40, Bool.true_and]
      apply List.any_of_mem (mem_verts52 w41)
      simp only [decide_eq_true hlt_4041, cn_4041, cpt_v41, Bool.true_and]
    have hcheck_true : case52_check7 = true := by
      have h := case52_check_true
      simp only [case52_check, Bool.and_eq_true] at h
      exact h.2
    exact absurd hcheck_true (by rw [hf]; decide)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **C₅³ upper bound**: α(C₅³) ≤ 10.

Monotonicity gives α ≤ 11 (from `alpha3_5o2_5o2_8o3_le`).
The Baumert slicing technique shows α ≠ 11: slicing into 5 layers,
IP rotation identifies 7 canonical size vectors, and exhaustive search
finds no valid assignment for any. See `case52_check_true`. -/
theorem alpha3_5o2_5o2_5o2_le :
    (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))).indepNum ≤ 10 := by
  by_contra hge; push_neg at hge
  -- α ≤ 11 from monotonicity: E_{5/2} ≤_G E_{8/3}
  have hle11 : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))).indepNum ≤ 11 := by
    have hcohom : fractionGraph 5 2 ≤_G fractionGraph 8 3 := by
      have hle_rat : (5 : ℚ) / 2 ≤ (8 : ℚ) / 3 := by norm_num
      exact ⟨_, (fractionGraph_cohomomorphism 5 2 8 3 (by omega) hle_rat).choose_spec⟩
    calc _ ≤ (strongProduct (fractionGraph 5 2)
          (strongProduct (fractionGraph 5 2)
            (fractionGraph 8 3))).indepNum := by
          open AsymptoticSpectrumGraphs in
          have h_inner : strongProduct (fractionGraph 5 2)
                (fractionGraph 5 2) ≤_G
              strongProduct (fractionGraph 5 2)
                (fractionGraph 8 3) :=
            Cohom.strongProduct_right _ hcohom
          open AsymptoticSpectrumGraphs in
          have h_outer : strongProduct (fractionGraph 5 2)
                (strongProduct (fractionGraph 5 2)
                  (fractionGraph 5 2)) ≤_G
              strongProduct (fractionGraph 5 2)
                (strongProduct (fractionGraph 5 2)
                  (fractionGraph 8 3)) :=
            Cohom.strongProduct_right _ h_inner
          obtain ⟨f, hf⟩ := h_outer
          exact independenceNumber_le_of_cohomomorphism _ _ f hf
      _ ≤ 11 := alpha3_5o2_5o2_8o3_le
  have heq : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))).indepNum = 11 := by omega
  obtain ⟨S, hSndp⟩ :=
    SimpleGraph.exists_isNIndepSet_indepNum
      (G := strongProduct (fractionGraph 5 2)
        (strongProduct (fractionGraph 5 2)
          (fractionGraph 5 2)))
  rw [heq] at hSndp
  have hfbc : ∀ i : ZMod 5,
      (S.filter (fun p =>
        p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card ≤ 5 := by
    intro i
    have h := fiber_bound_clique (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2)
        (fractionGraph 5 2))
      S hSndp.isIndepSet ({i, i + 1})
      (edge_clique_E52 i)
    rwa [alpha_5o2_sq] at h
  exact case52C_baumert_contradiction S hSndp.isIndepSet
    hSndp.card_eq hfbc

end Section6
