/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Section 6 Baumert Bridge: α(E_{5/2} ⊠ E_{8/3}²) ≤ 11 (alpha3_5o2_8o3_8o3_le)

Bridge file split off from `Section6UpperBounds.lean`.

See `Section6UpperBoundsCommon` for the shared infrastructure
(`fiber_bound_clique`, `floor_val`, `alpha_*`, `*_clique_E*`, etc.).
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsMixed52_83_83
import Mathlib.Data.Bool.AllAny
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Mixed-multiset Baumert bridge: α(E_{5/2} ⊠ E_{8/3}²) ≤ 11

The nested floor bound gives α ≤ 12. The Baumert slicing technique with
WLOG translation by `Z₈ × Z₈` (a symmetry of E_{8/3}²) bringing the first
element of layer 0 to `(0,0)` rules out α = 12. See `caseMixed_check_true`. -/

/-- Encoding for ordered witness extraction, mixed multiset case.
Matches `enc83sq` definitionally on `Fin 8 × Fin 8`. -/
private def enc83sq' (v : ZMod 8 × ZMod 8) : ℕ := v.1.val * 8 + v.2.val

private lemma enc83sq'_injective : Function.Injective enc83sq' := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [enc83sq'] at h
  have ha1 : a1.val < 8 := a1.isLt
  have ha2 : a2.val < 8 := a2.isLt
  have hb1 : b1.val < 8 := b1.isLt
  have hb2 : b2.val < 8 := b2.isLt
  have h1 : a1.val = b1.val := by omega
  have h2 : a2.val = b2.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- The fiber of S over a single layer i (mixed case, Z₅ layers, inner Z₈×Z₈). -/
private def layerFiber5M (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) (i : ZMod 5) :=
  S.filter (fun p => p.1 = i)

private lemma layerFiber5M_disjoint (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8)))
    (i j : ZMod 5) (hij : i ≠ j) :
    Disjoint (layerFiber5M S i) (layerFiber5M S j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [layerFiber5M, Finset.mem_filter] at hx hy
  exact hij (hx.2 ▸ hy.2)

private lemma layer5M_sum_eq_card (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) :
    ∑ i : ZMod 5, (layerFiber5M S i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [layerFiber5M, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x.1, h, rfl⟩⟩
  · intro i _ j _ hij
    exact layerFiber5M_disjoint S i j hij

private lemma pair_filter_eqM (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) (i : ZMod 5) :
    S.filter (fun p => p.1 ∈ ({i, i + 1} : Finset (ZMod 5))) =
    layerFiber5M S i ∪ layerFiber5M S (i + 1) := by
  ext x; simp only [layerFiber5M, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

private lemma pair_bound_sumM (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) (i : ZMod 5)
    (hfbc : (S.filter (fun p => p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card ≤ 5) :
    (layerFiber5M S i).card + (layerFiber5M S (i + 1)).card ≤ 5 := by
  rw [pair_filter_eqM] at hfbc
  rwa [Finset.card_union_of_disjoint
    (layerFiber5M_disjoint S _ _ (two_distinct_zmod5 i))] at hfbc

/-- Translate S by shifting the first coordinate (mixed case, Z₅). -/
private def translateFst5M (k : ZMod 5) (x : ZMod 5 × (ZMod 8 × ZMod 8)) :
    ZMod 5 × (ZMod 8 × ZMod 8) :=
  (x.1 + k, x.2)

private lemma translateFst5M_injective (k : ZMod 5) :
    Function.Injective (translateFst5M k) := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [translateFst5M, Prod.mk.injEq] at h
  exact Prod.ext (add_right_cancel h.1) h.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- First-coordinate translation preserves the IS property (mixed case). -/
private lemma translateFst5M_IS (k : ZMod 5)
    (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet
      ↑(S.image (translateFst5M k)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2⟩, hb, rfl⟩ := hy
  simp only [translateFst5M] at hne hadj
  have hne' : (a1, a2) ≠ (b1, b2) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg Prod.snd h
    subst h1; subst h2; exact hne rfl
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', hadj.2.1.imp (fun h => add_right_cancel h)
      (fractionGraph_adj_translate 5 2 a1 b1 k).mp, hadj.2.2⟩

private lemma translateFst5M_layerFiber (k : ZMod 5)
    (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) (i : ZMod 5) :
    (layerFiber5M (S.image (translateFst5M k)) (i + k)).card =
    (layerFiber5M S i).card := by
  have : layerFiber5M (S.image (translateFst5M k)) (i + k) =
      (layerFiber5M S i).image (translateFst5M k) := by
    ext ⟨j, a⟩
    simp only [layerFiber5M, Finset.mem_filter, Finset.mem_image, translateFst5M]
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
  rw [this, Finset.card_image_of_injective _ (translateFst5M_injective k)]

/-- Translate S by shifting the inner two coordinates (mixed case, Z₈ × Z₈ diagonal). -/
private def translateSnd83sq (δ : ZMod 8 × ZMod 8)
    (x : ZMod 5 × (ZMod 8 × ZMod 8)) : ZMod 5 × (ZMod 8 × ZMod 8) :=
  (x.1, (x.2.1 + δ.1, x.2.2 + δ.2))

private lemma translateSnd83sq_injective (δ : ZMod 8 × ZMod 8) :
    Function.Injective (translateSnd83sq δ) := by
  intro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [translateSnd83sq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext h1 (Prod.ext (add_right_cancel h2) (add_right_cancel h3))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Inner-coordinate translation preserves the IS property (mixed case). -/
private lemma translateSnd83sq_IS (δ : ZMod 8 × ZMod 8)
    (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet
      ↑(S.image (translateSnd83sq δ)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2, a3⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2, b3⟩, hb, rfl⟩ := hy
  simp only [translateSnd83sq] at hne hadj
  have hne' : (a1, a2, a3) ≠ (b1, b2, b3) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg (Prod.fst ∘ Prod.snd) h
    have h3 : a3 = b3 := congr_arg (Prod.snd ∘ Prod.snd) h
    subst h1; subst h2; subst h3; exact hne rfl
  -- Decompose adjacency in the strong product
  obtain ⟨_, h_first, h_inner⟩ := hadj
  -- Translate inner adjacency back
  have h_inner_back : (a2, a3) = (b2, b3) ∨ (strongProduct (fractionGraph 8 3)
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
          (fractionGraph_adj_translate 8 3 a2 b2 δ.1).mp
      · exact h3_or.imp (fun h => add_right_cancel h)
          (fractionGraph_adj_translate 8 3 a3 b3 δ.2).mp
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', h_first, h_inner_back⟩

private lemma translateSnd83sq_layerFiber (δ : ZMod 8 × ZMod 8)
    (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) (i : ZMod 5) :
    (layerFiber5M (S.image (translateSnd83sq δ)) i).card =
    (layerFiber5M S i).card := by
  have : layerFiber5M (S.image (translateSnd83sq δ)) i =
      (layerFiber5M S i).image (translateSnd83sq δ) := by
    ext ⟨j, a, b⟩
    simp only [layerFiber5M, Finset.mem_filter, Finset.mem_image, translateSnd83sq]
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
  rw [this, Finset.card_image_of_injective _ (translateSnd83sq_injective δ)]

set_option linter.style.nativeDecide false in
/-- Bridge: `crossNonAdj83sq a b = true` iff the formal adj-or-eq condition fails
    for E_{8/3}². -/
private lemma crossNonAdj83sq_spec (a b : ZMod 8 × ZMod 8) :
    crossNonAdj83sq a b = true ↔
    ¬((a.1 = b.1 ∨ (fractionGraph 8 3).Adj a.1 b.1) ∧
      (a.2 = b.2 ∨ (fractionGraph 8 3).Adj a.2 b.2)) := by
  revert a b; native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- From IS property and first-coordinate adj-or-eq, derive crossNonAdj83sq (mixed case). -/
private lemma cross_compat_of_IS_mixed
    (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet ↑S)
    (x y : ZMod 5 × (ZMod 8 × ZMod 8))
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h1 : x.1 = y.1 ∨ (fractionGraph 5 2).Adj x.1 y.1) :
    crossNonAdj83sq x.2 y.2 = true := by
  rw [crossNonAdj83sq_spec]
  intro ⟨hc1, hc2⟩
  have hnadj : ¬(strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).Adj x y :=
    (SimpleGraph.isIndepSet_iff _).mp hIS
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  apply hnadj
  refine ⟨hxy, h1, ?_⟩
  by_cases heq : x.2 = y.2
  · exact Or.inl heq
  · refine Or.inr ⟨heq, ?_, ?_⟩
    · exact hc1
    · exact hc2

private lemma extract_ordered_pair5M
    (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) (i : ZMod 5)
    (hcard : (layerFiber5M S i).card = 2) :
    ∃ a b : ZMod 8 × ZMod 8,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ a ≠ b ∧ enc83sq' a < enc83sq' b := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, hne, hfib⟩ := Finset.card_eq_two.mp hcard
  have h1 : (i1, a) ∈ layerFiber5M S i := hfib ▸ Finset.mem_insert_self _ _
  have h2 : (i2, b) ∈ layerFiber5M S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  rw [layerFiber5M, Finset.mem_filter] at h1 h2
  obtain ⟨h1m, h1e⟩ := h1; obtain ⟨h2m, h2e⟩ := h2
  subst h1e; subst h2e
  have hab : a ≠ b := fun h => hne (Prod.ext rfl h)
  rcases Nat.lt_or_gt_of_ne (fun h => hab (enc83sq'_injective h)) with hlt | hgt
  · exact ⟨a, b, h1m, h2m, hab, hlt⟩
  · exact ⟨b, a, h2m, h1m, hab.symm, hgt⟩

private lemma extract_ordered_triple5M
    (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) (i : ZMod 5)
    (hcard : (layerFiber5M S i).card = 3) :
    ∃ a b c : ZMod 8 × ZMod 8,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ (i, c) ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      enc83sq' a < enc83sq' b ∧ enc83sq' b < enc83sq' c := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, ⟨i3, c⟩, hne12, hne13, hne23, hfib⟩ :=
    Finset.card_eq_three.mp hcard
  have h1 : (i1, a) ∈ layerFiber5M S i :=
    hfib ▸ Finset.mem_insert_self _ _
  have h2 : (i2, b) ∈ layerFiber5M S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
  have h3 : (i3, c) ∈ layerFiber5M S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))))
  rw [layerFiber5M, Finset.mem_filter] at h1 h2 h3
  obtain ⟨h1m, h1e⟩ := h1; obtain ⟨h2m, h2e⟩ := h2; obtain ⟨h3m, h3e⟩ := h3
  subst h1e; subst h2e; subst h3e
  have hab : a ≠ b := fun h => hne12 (Prod.ext rfl h)
  have hac : a ≠ c := fun h => hne13 (Prod.ext rfl h)
  have hbc : b ≠ c := fun h => hne23 (Prod.ext rfl h)
  have henc_ab := Nat.lt_or_gt_of_ne (fun h => hab (enc83sq'_injective h))
  have henc_ac := Nat.lt_or_gt_of_ne (fun h => hac (enc83sq'_injective h))
  have henc_bc := Nat.lt_or_gt_of_ne (fun h => hbc (enc83sq'_injective h))
  rcases henc_ab with hab' | hab'
  · rcases henc_ac with hac' | hac'
    · rcases henc_bc with hbc' | hbc'
      · exact ⟨a, b, c, h1m, h2m, h3m, hab, hac, hbc, hab', hbc'⟩
      · exact ⟨a, c, b, h1m, h3m, h2m, hac, hab, hbc.symm, hac', by omega⟩
    · rcases henc_bc with hbc' | hbc'
      · omega
      · exact ⟨c, a, b, h3m, h1m, h2m, hac.symm, hbc.symm, hab, by omega, hab'⟩
  · rcases henc_ac with hac' | hac'
    · rcases henc_bc with hbc' | hbc'
      · exact ⟨b, a, c, h2m, h1m, h3m, hab.symm, hbc, hac, by omega, hac'⟩
      · omega
    · rcases henc_bc with hbc' | hbc'
      · exact ⟨b, c, a, h2m, h3m, h1m, hbc, hab.symm, hac.symm, hbc', by omega⟩
      · exact ⟨c, b, a, h3m, h2m, h1m, hbc.symm, hac.symm, hab.symm, by omega, by omega⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.nativeDecide false in
/-- Mixed-multiset Baumert contradiction: an IS of size 12 in
    E_{5/2} ⊠ E_{8/3}² satisfying the edge-fiber bound 5 cannot exist. -/
private lemma caseMixed_baumert_contradiction
    (S : Finset (ZMod 5 × (ZMod 8 × ZMod 8)))
    (hSis : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet ↑S)
    (hScard : S.card = 12)
    (hfbc : ∀ i : ZMod 5,
      (S.filter (fun p => p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card ≤ 5) :
    False := by
  -- IP rotation
  obtain ⟨k, hk⟩ := ip_rotation7 (fun i => (layerFiber5M S i).card)
    (by change ∑ i, (layerFiber5M S i).card = 12; rw [layer5M_sum_eq_card]; exact hScard)
    (fun i => by
      have := pair_bound_sumM S i (hfbc i)
      convert this using 2)
  -- Translate to canonical sizes via Z₅ shift
  let κ : ZMod 5 := k
  set S₁ := S.image (translateFst5M κ) with hS₁_def
  have hIS₁ := translateFst5M_IS κ S hSis
  have hcanon₁ : ∀ j : ZMod 5, (layerFiber5M S₁ j).card = canonical_sizes7 j := by
    intro j
    have h := translateFst5M_layerFiber κ S (j - κ)
    rw [sub_add_cancel] at h
    rw [h, hk (j - κ)]
    congr 1
    ext
    change ((j - κ).val + κ.val) % 5 = j.val
    rw [← ZMod.val_add, sub_add_cancel]
  -- Extract first witness from layer 0 to compute the inner translation δ
  obtain ⟨w00₁, _w01₁, hw00₁_S₁, _, _, _⟩ := extract_ordered_pair5M S₁ 0
    (by rw [hcanon₁]; rfl)
  -- Translate by δ = (-w00₁.1, -w00₁.2) so that w00 = (0, 0) in the new S
  let δ : ZMod 8 × ZMod 8 := (-w00₁.1, -w00₁.2)
  set S' := S₁.image (translateSnd83sq δ) with hS'_def
  have hIS' := translateSnd83sq_IS δ S₁ hIS₁
  have hcanon : ∀ j : ZMod 5, (layerFiber5M S' j).card = canonical_sizes7 j := by
    intro j
    rw [translateSnd83sq_layerFiber δ S₁ j]
    exact hcanon₁ j
  -- Cross-compat
  have hcc := cross_compat_of_IS_mixed S' hIS'
  have hne_layer : ∀ (i j : ZMod 5) (a b : ZMod 8 × ZMod 8),
      i ≠ j → (i, a) ≠ (j, b) :=
    fun _ _ _ _ hij h => hij (congr_arg Prod.fst h)
  have cc : ∀ (i j : ZMod 5) (a b : ZMod 8 × ZMod 8),
      (i, a) ∈ S' → (j, b) ∈ S' → i ≠ j →
      (fractionGraph 5 2).Adj i j →
      crossNonAdj83sq a b = true :=
    fun i j a b ha hb hij hadj =>
      hcc _ _ ha hb (hne_layer i j a b hij) (Or.inr hadj)
  have cc_eq : ∀ (i : ZMod 5) (a b : ZMod 8 × ZMod 8),
      (i, a) ∈ S' → (i, b) ∈ S' → a ≠ b →
      crossNonAdj83sq a b = true :=
    fun i a b ha hb hab =>
      hcc _ _ ha hb (fun h => hab (congr_arg Prod.snd h)) (Or.inl rfl)
  -- compatWith83sq via cc and cc_eq
  have compat_of_list : ∀ (i : ZMod 5) (a : ZMod 8 × ZMod 8)
      (ws : List (ZMod 5 × (ZMod 8 × ZMod 8))),
      (i, a) ∈ S' →
      (∀ w ∈ ws, w ∈ S' ∧ (i ≠ w.1 → (fractionGraph 5 2).Adj i w.1) ∧
        (i = w.1 → a ≠ w.2)) →
      compatWith83sq a (ws.map Prod.snd) = true := by
    intro i a ws hia hws
    simp only [compatWith83sq, List.all_eq_true, List.mem_map]
    rintro b ⟨w, hw_mem, rfl⟩
    obtain ⟨hw_S, hadj, hneq⟩ := hws w hw_mem
    by_cases hij : i = w.1
    · refine cc_eq i a w.2 hia ?_ (hneq hij)
      cases hij; exact hw_S
    · exact cc i w.1 a w.2 hia hw_S hij (hadj hij)
  -- Re-extract witnesses in S' (after the inner translation, the first
  -- enc-ordered element of layer 0 is (0, 0))
  obtain ⟨w00, w01, hw00, hw01, hne0, hlt0⟩ := extract_ordered_pair5M S' 0
    (by rw [hcanon]; rfl)
  -- Show w00 = (0, 0) by deriving it from the inner translation
  have hw00_zero : w00 = (0, 0) := by
    -- The first witness w00₁ from S₁ gets shifted by δ = -w00₁ to become 0.
    -- After re-extraction in S', we have w00 ∈ S' with smallest enc83sq'.
    -- Membership: (0, (0, 0)) ∈ S' since (0, w00₁) ∈ S₁ shifts to (0, w00₁ + δ) = (0, 0).
    have h_zero_in_S' : ((0 : ZMod 5), ((0 : ZMod 8), (0 : ZMod 8))) ∈ S' := by
      rw [hS'_def]
      rw [Finset.mem_image]
      refine ⟨(0, w00₁), hw00₁_S₁, ?_⟩
      simp only [translateSnd83sq, δ]
      ext
      · rfl
      · change w00₁.1 + (- w00₁.1) = 0; ring
      · change w00₁.2 + (- w00₁.2) = 0; ring
    -- Layer 0 has exactly two elements w00, w01 with enc83sq' w00 < enc83sq' w01.
    -- So {w00, w01} = the layer 0 fiber, and (0, 0) must be one of them.
    have hfib0 : layerFiber5M S' 0 = {(0, w00), (0, w01)} := by
      have hcard0 : (layerFiber5M S' 0).card = 2 := by rw [hcanon]; rfl
      have hsubset : ({(0, w00), (0, w01)} : Finset (ZMod 5 × (ZMod 8 × ZMod 8))) ⊆
          layerFiber5M S' 0 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · show (0, w00) ∈ layerFiber5M S' 0
          rw [layerFiber5M, Finset.mem_filter]; exact ⟨hw00, rfl⟩
        · show (0, w01) ∈ layerFiber5M S' 0
          rw [layerFiber5M, Finset.mem_filter]; exact ⟨hw01, rfl⟩
      have hpair_card : ({(0, w00), (0, w01)} : Finset (ZMod 5 × (ZMod 8 × ZMod 8))).card = 2 :=
        Finset.card_pair (fun h => hne0 (by
          have := congr_arg Prod.snd h; simpa using this))
      exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard0, hpair_card])).symm
    have h_zero_in_fib : ((0 : ZMod 5), ((0 : ZMod 8), (0 : ZMod 8))) ∈ layerFiber5M S' 0 := by
      rw [layerFiber5M, Finset.mem_filter]; exact ⟨h_zero_in_S', rfl⟩
    rw [hfib0] at h_zero_in_fib
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h_zero_in_fib
    -- (0, 0) is either w00 or w01; we want w00 = (0, 0).
    -- Use enc ordering: enc83sq' w00 < enc83sq' w01, and enc83sq' (0, 0) = 0.
    rcases h_zero_in_fib with ⟨_, h00⟩ | ⟨_, h01⟩
    · exact h00.symm
    · -- If w01 = (0, 0), then enc83sq' w01 = 0, so enc83sq' w00 < 0, impossible.
      exfalso
      have : enc83sq' w01 = 0 := by rw [← h01]; rfl
      omega
  -- Continue extracting all witnesses in S'
  obtain ⟨w10, w11, hw10, hw11, hne1, hlt1⟩ := extract_ordered_pair5M S' 1
    (by rw [hcanon]; rfl)
  obtain ⟨w20, w21, w22, hw20, hw21, hw22, hne20, hne21, hne22, hlt20, hlt21⟩ :=
    extract_ordered_triple5M S' 2 (by rw [hcanon]; rfl)
  obtain ⟨w30, w31, hw30, hw31, hne3, hlt3⟩ := extract_ordered_pair5M S' 3
    (by rw [hcanon]; rfl)
  obtain ⟨w40, w41, w42, hw40, hw41, hw42, hne40, hne41, hne42, hlt40, hlt41⟩ :=
    extract_ordered_triple5M S' 4 (by rw [hcanon]; rfl)
  -- Adjacency facts in C₅
  have adj01 : (fractionGraph 5 2).Adj 0 1 := by decide
  have adj12 : (fractionGraph 5 2).Adj 1 2 := by decide
  have adj23 : (fractionGraph 5 2).Adj 2 3 := by decide
  have adj34 : (fractionGraph 5 2).Adj 3 4 := by decide
  have adj40 : (fractionGraph 5 2).Adj 4 0 := by decide
  -- crossNonAdj for within-layer pairs
  have cn_00_01 := cc_eq 0 w00 w01 hw00 hw01 hne0
  have cn_10_11 := cc_eq 1 w10 w11 hw10 hw11 hne1
  have cn_20_21 := cc_eq 2 w20 w21 hw20 hw21 hne20
  have cn_20_22 := cc_eq 2 w20 w22 hw20 hw22 hne21
  have cn_21_22 := cc_eq 2 w21 w22 hw21 hw22 hne22
  have cn_30_31 := cc_eq 3 w30 w31 hw30 hw31 hne3
  have cn_40_41 := cc_eq 4 w40 w41 hw40 hw41 hne40
  have cn_40_42 := cc_eq 4 w40 w42 hw40 hw42 hne41
  have cn_41_42 := cc_eq 4 w41 w42 hw41 hw42 hne42
  -- compatWith83sq conditions via compat_of_list
  have cpt_10 := compat_of_list 1 w10 [(0, w00), (0, w01)] hw10
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw00, fun _ => adj01.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw01, fun _ => adj01.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_11 := compat_of_list 1 w11 [(0, w00), (0, w01)] hw11
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw00, fun _ => adj01.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw01, fun _ => adj01.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_20 := compat_of_list 2 w20 [(1, w10), (1, w11)] hw20
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw10, fun _ => adj12.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj12.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_21 := compat_of_list 2 w21 [(1, w10), (1, w11)] hw21
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw10, fun _ => adj12.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj12.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_22 := compat_of_list 2 w22 [(1, w10), (1, w11)] hw22
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw10, fun _ => adj12.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj12.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_30 := compat_of_list 3 w30 [(2, w20), (2, w21), (2, w22)] hw30
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw20, fun _ => adj23.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw21, fun _ => adj23.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw22, fun _ => adj23.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_31 := compat_of_list 3 w31 [(2, w20), (2, w21), (2, w22)] hw31
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw20, fun _ => adj23.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw21, fun _ => adj23.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw22, fun _ => adj23.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_40 := compat_of_list 4 w40 [(3, w30), (3, w31), (0, w00), (0, w01)] hw40
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw30, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw00, fun _ => adj40, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw01, fun _ => adj40, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_41 := compat_of_list 4 w41 [(3, w30), (3, w31), (0, w00), (0, w01)] hw41
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw30, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw00, fun _ => adj40, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw01, fun _ => adj40, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  have cpt_42 := compat_of_list 4 w42 [(3, w30), (3, w31), (0, w00), (0, w01)] hw42
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw30, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw00, fun _ => adj40, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw01, fun _ => adj40, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Normalize List.map Prod.snd in compat hypotheses
  simp only [List.map] at cpt_10 cpt_11 cpt_20 cpt_21 cpt_22 cpt_30 cpt_31
  simp only [List.map] at cpt_40 cpt_41 cpt_42
  -- Show caseMixed_check = false, contradicting caseMixed_check_true.
  -- The hardcoded s00 = (0, 0) in caseMixed_check matches w00 = (0, 0) here.
  -- Substitute w00 := (0, 0) throughout.
  subst hw00_zero
  -- Replace `(⟨0, _⟩, ⟨0, _⟩) : Fin 8 × Fin 8` (which appears in `caseMixed_check`)
  -- with the term `(0, 0) : ZMod 8 × ZMod 8` (which we have facts about), via defeq.
  have s00_eq : ((⟨0, by decide⟩, ⟨0, by decide⟩) : Fin 8 × Fin 8) =
      ((0 : ZMod 8), (0 : ZMod 8)) := rfl
  exfalso
  have hf : caseMixed_check = false := by
    unfold caseMixed_check
    simp only [s00_eq, Bool.not_eq_false']
    apply List.any_of_mem (mem_verts83sq w01)
    have hlt0' : enc83sq ((0 : ZMod 8), (0 : ZMod 8)) < enc83sq w01 := hlt0
    -- v4.29: decide_eq_true no longer fires via simp due to stricter instance matching
    simp only [cn_00_01, Bool.and_true]
    refine (Bool.and_eq_true _ _).mpr ⟨decide_eq_true hlt0', ?_⟩
    apply List.any_of_mem (mem_verts83sq w10)
    simp only [cpt_10, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w11)
    simp only [show enc83sq w10 = enc83sq' w10 from rfl,
               show enc83sq w11 = enc83sq' w11 from rfl,
               decide_eq_true hlt1, cn_10_11, cpt_11, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w20)
    simp only [cpt_20, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w21)
    simp only [show enc83sq w20 = enc83sq' w20 from rfl,
               show enc83sq w21 = enc83sq' w21 from rfl,
               decide_eq_true hlt20, cn_20_21, cpt_21, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w22)
    simp only [show enc83sq w22 = enc83sq' w22 from rfl,
               decide_eq_true hlt21, cn_20_22, cn_21_22, cpt_22, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w30)
    simp only [cpt_30, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w31)
    simp only [show enc83sq w30 = enc83sq' w30 from rfl,
               show enc83sq w31 = enc83sq' w31 from rfl,
               decide_eq_true hlt3, cn_30_31, cpt_31, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w40)
    simp only [cpt_40, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w41)
    simp only [show enc83sq w40 = enc83sq' w40 from rfl,
               show enc83sq w41 = enc83sq' w41 from rfl,
               decide_eq_true hlt40, cn_40_41, cpt_41, Bool.true_and]
    apply List.any_of_mem (mem_verts83sq w42)
    simp only [show enc83sq w42 = enc83sq' w42 from rfl,
               decide_eq_true hlt41, cn_40_42, cn_41_42, cpt_42, Bool.true_and]
  exact absurd caseMixed_check_true (by rw [hf]; decide)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Mixed multiset upper bound**: α(E_{5/2} ⊠ (E_{8/3} ⊠ E_{8/3})) ≤ 11.

The nested floor bound gives α ≤ 12. The Baumert slicing technique with WLOG
translation by `Z₈ × Z₈` (a symmetry of E_{8/3}²) bringing the first element
of layer 0 to `(0, 0)` rules out α = 12: layer-assignment search over
E_{8/3}² with `s00 = (0, 0)` finds no valid configuration.
See `caseMixed_check_true`. -/
theorem alpha3_5o2_8o3_8o3_le :
    (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum ≤ 11 := by
  by_contra hge; push_neg at hge
  have hle : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum ≤ 12 := by
    have h := nested_floor_three 5 2 8 3 8 3
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have h1 : ⌊(8:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
    simp only [Nat.cast_ofNat, h1] at h; norm_cast at h
    have h2 : ⌊(8:ℝ)/3 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h2] at h; norm_cast at h
    have h3 : ⌊(5:ℝ)/2 * 5⌋₊ = 12 := floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h3] at h; exact h
  have heq : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum = 12 := by omega
  obtain ⟨S, hSndp⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3)))
  rw [heq] at hSndp
  -- Edge-fiber bound from α(E_{8/3}²) = 5
  have hfbc : ∀ i : ZMod 5,
      (S.filter (fun p => p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card ≤ 5 := by
    intro i
    have h := fiber_bound_clique (fractionGraph 5 2)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))
      S hSndp.isIndepSet ({i, i + 1}) (edge_clique_E52 i)
    rwa [alpha_8o3_sq] at h
  exact caseMixed_baumert_contradiction S hSndp.isIndepSet hSndp.card_eq hfbc

end Section6
