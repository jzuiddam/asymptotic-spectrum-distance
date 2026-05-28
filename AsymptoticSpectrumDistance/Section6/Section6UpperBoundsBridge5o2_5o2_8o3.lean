/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Section 6 Baumert Bridge: α(E_{5/2}² ⊠ E_{8/3}) ≤ 11 (alpha3_5o2_5o2_8o3_le)

Bridge file split off from `Section6UpperBounds.lean` (the original "Case 7"
bridge). Slices an IS in `E_{5/2} ⊠ (E_{5/2} ⊠ E_{8/3})` along the leading
`E_{5/2}` factor and rules out cardinality 12 by an exhaustive chain search
(`case7_direct_check_true`).

See `Section6UpperBoundsCommon` for the shared infrastructure
(`fiber_bound_clique`, `floor_val`, `alpha_5o2_8o3`, `edge_clique_E52`, etc.).
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase7
import Mathlib.Data.Bool.AllAny
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Case 7 Baumert contradiction lemma

The following lemma captures the Baumert argument for Case 7:
given an IS S of size 12 in E_{5/2} ⊠ (E_{5/2} ⊠ E_{8/3}) satisfying edge fiber
constraints, derive a contradiction. The proof uses:
1. Fiber decomposition: layer sizes sum to 12
2. IP: edge constraints force sizes to be a rotation of (2,2,3,2,3)
3. Translation invariance: WLOG rotation is canonical
4. `case7_direct_check_true`: exhaustive search finds no valid assignment -/

/-- The fiber of S over a single layer i (Case 7, Z₅ layers). -/
private def layerFiber5 (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8))) (i : ZMod 5) :=
  S.filter (fun p => p.1 = i)

/-- Layer fibers for distinct indices are disjoint (Case 7). -/
private lemma layerFiber5_disjoint (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8)))
    (i j : ZMod 5) (hij : i ≠ j) :
    Disjoint (layerFiber5 S i) (layerFiber5 S j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [layerFiber5, Finset.mem_filter] at hx hy
  exact hij (hx.2 ▸ hy.2)

/-- Layer sizes sum to |S| by fiber decomposition (Case 7). -/
private lemma layer5_sum_eq_card (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8))) :
    ∑ i : ZMod 5, (layerFiber5 S i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [layerFiber5, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x.1, h, rfl⟩⟩
  · intro i _ j _ hij
    exact layerFiber5_disjoint S i j hij

/-- The 2-element filter decomposes as union of single-element filters (Case 7). -/
private lemma pair_filter_eq (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8))) (i : ZMod 5) :
    S.filter (fun p => p.1 ∈ ({i, i + 1} : Finset (ZMod 5))) =
    layerFiber5 S i ∪ layerFiber5 S (i + 1) := by
  ext x; simp only [layerFiber5, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

-- `two_distinct_zmod5` is now in `Section6UpperBoundsCommon`.

/-- Pair fiber bound decomposes into sum of layer sizes (Case 7). -/
private lemma pair_bound_sum (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8))) (i : ZMod 5)
    (hfbc : (S.filter (fun p => p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card ≤ 5) :
    (layerFiber5 S i).card + (layerFiber5 S (i + 1)).card ≤ 5 := by
  rw [pair_filter_eq] at hfbc
  rwa [Finset.card_union_of_disjoint (layerFiber5_disjoint S _ _ (two_distinct_zmod5 i))] at hfbc

-- `canonical_sizes7`, `is_rotation_of_canonical7`, `ip_rotation7_fin6`, and
-- `ip_rotation7` are now in `Section6UpperBoundsCommon`.

/-- Translate S by shifting the first coordinate (Case 7, Z₅). -/
private def translateFst5 (k : ZMod 5) (x : ZMod 5 × (ZMod 5 × ZMod 8)) :
    ZMod 5 × (ZMod 5 × ZMod 8) :=
  (x.1 + k, x.2)

private lemma translateFst5_injective (k : ZMod 5) :
    Function.Injective (translateFst5 k) := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [translateFst5, Prod.mk.injEq] at h
  exact Prod.ext (add_right_cancel h.1) h.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Translation preserves the IS property (Case 7). -/
private lemma translateFst5_IS (k : ZMod 5)
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).IsIndepSet
      ↑(S.image (translateFst5 k)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2⟩, hb, rfl⟩ := hy
  simp only [translateFst5] at hne hadj
  have hne' : (a1, a2) ≠ (b1, b2) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg Prod.snd h
    subst h1; subst h2; exact hne rfl
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', hadj.2.1.imp (fun h => add_right_cancel h)
      (fractionGraph_adj_translate 5 2 a1 b1 k).mp, hadj.2.2⟩

/-- Translation shifts layer fibers (Case 7). -/
private lemma translateFst5_layerFiber (k : ZMod 5)
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8))) (i : ZMod 5) :
    (layerFiber5 (S.image (translateFst5 k)) (i + k)).card =
    (layerFiber5 S i).card := by
  have : layerFiber5 (S.image (translateFst5 k)) (i + k) =
      (layerFiber5 S i).image (translateFst5 k) := by
    ext ⟨j, a⟩
    simp only [layerFiber5, Finset.mem_filter, Finset.mem_image, translateFst5]
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
  rw [this, Finset.card_image_of_injective _ (translateFst5_injective k)]


set_option linter.style.nativeDecide false in
/-- Bridge: `crossNonAdj52_83 a b = true` iff the formal adj-or-eq condition fails. -/
private lemma crossNonAdj52_83_spec (a b : ZMod 5 × ZMod 8) :
    crossNonAdj52_83 a.1 b.1 a.2 b.2 = true ↔
    ¬((a.1 = b.1 ∨ (fractionGraph 5 2).Adj a.1 b.1) ∧
      (a.2 = b.2 ∨ (fractionGraph 8 3).Adj a.2 b.2)) := by
  revert a b; native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- From IS property and first-coordinate adj-or-eq, derive crossNonAdj52_83 (Case 7). -/
private lemma cross_compat_of_IS7
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).IsIndepSet ↑S)
    (x y : ZMod 5 × (ZMod 5 × ZMod 8))
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h1 : x.1 = y.1 ∨ (fractionGraph 5 2).Adj x.1 y.1) :
    crossNonAdj52_83 x.2.1 y.2.1 x.2.2 y.2.2 = true := by
  rw [crossNonAdj52_83_spec]
  intro ⟨hc1, hc2⟩
  have hnadj : ¬(strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).Adj x y :=
    (SimpleGraph.isIndepSet_iff _).mp hIS
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  apply hnadj
  refine ⟨hxy, ?_, ?_⟩
  · exact h1
  · by_cases heq : x.2 = y.2
    · exact Or.inl heq
    · exact Or.inr ⟨heq, hc1, hc2⟩

/-- Encoding for ordered witness extraction (Case 7). -/
private def enc52_83' (v : ZMod 5 × ZMod 8) : ℕ := v.1.val * 8 + v.2.val

private lemma enc52_83'_injective : Function.Injective enc52_83' := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [enc52_83'] at h
  have ha1 : a1.val < 5 := a1.isLt
  have ha2 : a2.val < 8 := a2.isLt
  have hb1 : b1.val < 5 := b1.isLt
  have hb2 : b2.val < 8 := b2.isLt
  have h1 : a1.val = b1.val := by omega
  have h2 : a2.val = b2.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

private lemma extract_ordered_pair5
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8))) (i : ZMod 5)
    (hcard : (layerFiber5 S i).card = 2) :
    ∃ a b : ZMod 5 × ZMod 8,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ a ≠ b ∧ enc52_83' a < enc52_83' b := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, hne, hfib⟩ := Finset.card_eq_two.mp hcard
  have h1 : (i1, a) ∈ layerFiber5 S i := hfib ▸ Finset.mem_insert_self _ _
  have h2 : (i2, b) ∈ layerFiber5 S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  rw [layerFiber5, Finset.mem_filter] at h1 h2
  obtain ⟨h1m, h1e⟩ := h1; obtain ⟨h2m, h2e⟩ := h2
  subst h1e; subst h2e
  have hab : a ≠ b := fun h => hne (Prod.ext rfl h)
  rcases Nat.lt_or_gt_of_ne (fun h => hab (enc52_83'_injective h)) with hlt | hgt
  · exact ⟨a, b, h1m, h2m, hab, hlt⟩
  · exact ⟨b, a, h2m, h1m, hab.symm, hgt⟩

private lemma extract_ordered_triple5
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8))) (i : ZMod 5)
    (hcard : (layerFiber5 S i).card = 3) :
    ∃ a b c : ZMod 5 × ZMod 8,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ (i, c) ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      enc52_83' a < enc52_83' b ∧ enc52_83' b < enc52_83' c := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, ⟨i3, c⟩, hne12, hne13, hne23, hfib⟩ :=
    Finset.card_eq_three.mp hcard
  have h1 : (i1, a) ∈ layerFiber5 S i :=
    hfib ▸ Finset.mem_insert_self _ _
  have h2 : (i2, b) ∈ layerFiber5 S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
  have h3 : (i3, c) ∈ layerFiber5 S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))))
  rw [layerFiber5, Finset.mem_filter] at h1 h2 h3
  obtain ⟨h1m, h1e⟩ := h1; obtain ⟨h2m, h2e⟩ := h2; obtain ⟨h3m, h3e⟩ := h3
  subst h1e; subst h2e; subst h3e
  have hab : a ≠ b := fun h => hne12 (Prod.ext rfl h)
  have hac : a ≠ c := fun h => hne13 (Prod.ext rfl h)
  have hbc : b ≠ c := fun h => hne23 (Prod.ext rfl h)
  -- Sort by enc52_83'
  have henc_ab := Nat.lt_or_gt_of_ne (fun h => hab (enc52_83'_injective h))
  have henc_ac := Nat.lt_or_gt_of_ne (fun h => hac (enc52_83'_injective h))
  have henc_bc := Nat.lt_or_gt_of_ne (fun h => hbc (enc52_83'_injective h))
  -- There are 8 cases from 3 binary choices; 2 are contradictory, 6 are valid permutations
  rcases henc_ab with hab' | hab'
  · rcases henc_ac with hac' | hac'
    · rcases henc_bc with hbc' | hbc'
      -- a<b, a<c, b<c: sorted order (a,b,c)
      · exact ⟨a, b, c, h1m, h2m, h3m, hab, hac, hbc, hab', hbc'⟩
      -- a<b, a<c, b>c: sorted order (a,c,b)
      · exact ⟨a, c, b, h1m, h3m, h2m, hac, hab, hbc.symm, hac', by omega⟩
    · rcases henc_bc with hbc' | hbc'
      -- a<b, a>c, b<c: contradiction (c<a<b<c)
      · omega
      -- a<b, a>c, b>c: sorted order (c,a,b)
      · exact ⟨c, a, b, h3m, h1m, h2m, hac.symm, hbc.symm, hab, by omega, hab'⟩
  · rcases henc_ac with hac' | hac'
    · rcases henc_bc with hbc' | hbc'
      -- a>b, a<c, b<c: sorted order (b,a,c)
      · exact ⟨b, a, c, h2m, h1m, h3m, hab.symm, hbc, hac, by omega, hac'⟩
      -- a>b, a<c, b>c: contradiction (c<b<a<c)
      · omega
    · rcases henc_bc with hbc' | hbc'
      -- a>b, a>c, b<c: sorted order (b,c,a)
      · exact ⟨b, c, a, h2m, h3m, h1m, hbc, hab.symm, hac.symm, hbc', by omega⟩
      -- a>b, a>c, b>c: sorted order (c,b,a)
      · exact ⟨c, b, a, h3m, h2m, h1m, hbc.symm, hac.symm, hab.symm, by omega, by omega⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.nativeDecide false in
private lemma case7_baumert_contradiction
    (S : Finset (ZMod 5 × (ZMod 5 × ZMod 8)))
    (hSis : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).IsIndepSet ↑S)
    (hScard : S.card = 12)
    (hfbc : ∀ i : ZMod 5,
      (S.filter (fun p => p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card ≤ 5) :
    False := by
  -- IP rotation
  obtain ⟨k, hk⟩ := ip_rotation7 (fun i => (layerFiber5 S i).card)
    (by change ∑ i, (layerFiber5 S i).card = 12; rw [layer5_sum_eq_card]; exact hScard)
    (fun i => by
      have := pair_bound_sum S i (hfbc i)
      convert this using 2)
  -- Translate to canonical sizes
  let κ : ZMod 5 := k
  set S' := S.image (translateFst5 κ) with hS'_def
  have hIS' := translateFst5_IS κ S hSis
  have hcanon : ∀ j : ZMod 5, (layerFiber5 S' j).card = canonical_sizes7 j := by
    intro j
    have h := translateFst5_layerFiber κ S (j - κ)
    rw [sub_add_cancel] at h
    rw [h, hk (j - κ)]
    congr 1
    ext
    change ((j - κ).val + κ.val) % 5 = j.val
    rw [← ZMod.val_add, sub_add_cancel]
  -- Cross-compat
  have hcc := cross_compat_of_IS7 S' hIS'
  have hne_layer : ∀ (i j : ZMod 5) (a b : ZMod 5 × ZMod 8),
      i ≠ j → (i, a) ≠ (j, b) :=
    fun _ _ _ _ hij h => hij (congr_arg Prod.fst h)
  have cc : ∀ (i j : ZMod 5) (a b : ZMod 5 × ZMod 8),
      (i, a) ∈ S' → (j, b) ∈ S' → i ≠ j →
      (fractionGraph 5 2).Adj i j →
      crossNonAdj52_83 a.1 b.1 a.2 b.2 = true :=
    fun i j a b ha hb hij hadj =>
      hcc _ _ ha hb (hne_layer i j a b hij) (Or.inr hadj)
  have cc_eq : ∀ (i : ZMod 5) (a b : ZMod 5 × ZMod 8),
      (i, a) ∈ S' → (i, b) ∈ S' → a ≠ b →
      crossNonAdj52_83 a.1 b.1 a.2 b.2 = true :=
    fun i a b ha hb hab =>
      hcc _ _ ha hb (fun h => hab (congr_arg Prod.snd h)) (Or.inl rfl)
  -- Helper: compatWith52_83 via cc and cc_eq
  have compat_of_list : ∀ (i : ZMod 5) (a : ZMod 5 × ZMod 8)
      (ws : List (ZMod 5 × (ZMod 5 × ZMod 8))),
      (i, a) ∈ S' →
      (∀ w ∈ ws, w ∈ S' ∧ (i ≠ w.1 → (fractionGraph 5 2).Adj i w.1) ∧
        (i = w.1 → a ≠ w.2)) →
      compatWith52_83 a (ws.map Prod.snd) = true := by
    intro i a ws hia hws
    simp only [compatWith52_83, List.all_eq_true, List.mem_map]
    rintro b ⟨⟨j, b'⟩, hjb_mem, rfl⟩
    have ⟨hjb_S, hadj, hneq⟩ := hws _ hjb_mem
    by_cases hij : i = j
    · subst hij; exact cc_eq i a b' hia hjb_S (hneq rfl)
    · exact cc i j a b' hia hjb_S hij (hadj hij)
  -- Extract witnesses from each layer
  -- Layer 0 (size 2), Layer 1 (size 2), Layer 2 (size 3), Layer 3 (size 2), Layer 4 (size 3)
  obtain ⟨w00, w01, hw00, hw01, hne0, hlt0⟩ := extract_ordered_pair5 S' 0
    (by rw [hcanon]; rfl)
  obtain ⟨w10, w11, hw10, hw11, hne1, hlt1⟩ := extract_ordered_pair5 S' 1
    (by rw [hcanon]; rfl)
  obtain ⟨w20, w21, w22, hw20, hw21, hw22, hne20, hne21, hne22, hlt20, hlt21⟩ :=
    extract_ordered_triple5 S' 2 (by rw [hcanon]; rfl)
  obtain ⟨w30, w31, hw30, hw31, hne3, hlt3⟩ := extract_ordered_pair5 S' 3
    (by rw [hcanon]; rfl)
  obtain ⟨w40, w41, w42, hw40, hw41, hw42, hne40, hne41, hne42, hlt40, hlt41⟩ :=
    extract_ordered_triple5 S' 4 (by rw [hcanon]; rfl)
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
  -- compatWith52_83 conditions via compat_of_list
  -- Layer 1 compat with [s00, s01] (adj layers 0,1)
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
  -- Layer 2 compat with [s10, s11] (adj layers 1,2)
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
  -- Layer 3 compat with [s20, s21, s22] (adj layers 2,3)
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
  -- Layer 4 compat with [s30, s31, s00, s01] (adj layers 3,4 and 4,0)
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
  -- enc52_83' matches enc52_83 definitionally
  -- Show case7_direct_check = false, contradicting case7_direct_check_true
  exfalso
  have hf : case7_direct_check = false := by
    unfold case7_direct_check; simp only [Bool.not_eq_false']
    apply List.any_of_mem (mem_verts52_83 w00)
    apply List.any_of_mem (mem_verts52_83 w01)
    simp only [show enc52_83 w00 = enc52_83' w00 from rfl,
               show enc52_83 w01 = enc52_83' w01 from rfl,
               decide_eq_true hlt0, cn_00_01, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w10)
    simp only [cpt_10, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w11)
    simp only [show enc52_83 w10 = enc52_83' w10 from rfl,
               show enc52_83 w11 = enc52_83' w11 from rfl,
               decide_eq_true hlt1, cn_10_11, cpt_11, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w20)
    simp only [cpt_20, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w21)
    simp only [show enc52_83 w20 = enc52_83' w20 from rfl,
               show enc52_83 w21 = enc52_83' w21 from rfl,
               decide_eq_true hlt20, cn_20_21, cpt_21, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w22)
    simp only [show enc52_83 w22 = enc52_83' w22 from rfl,
               decide_eq_true hlt21, cn_20_22, cn_21_22, cpt_22, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w30)
    simp only [cpt_30, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w31)
    simp only [show enc52_83 w30 = enc52_83' w30 from rfl,
               show enc52_83 w31 = enc52_83' w31 from rfl,
               decide_eq_true hlt3, cn_30_31, cpt_31, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w40)
    simp only [cpt_40, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w41)
    simp only [show enc52_83 w40 = enc52_83' w40 from rfl,
               show enc52_83 w41 = enc52_83' w41 from rfl,
               decide_eq_true hlt40, cn_40_41, cpt_41, Bool.true_and]
    apply List.any_of_mem (mem_verts52_83 w42)
    simp only [show enc52_83 w42 = enc52_83' w42 from rfl,
               decide_eq_true hlt41, cn_40_42, cn_41_42, cpt_42, Bool.true_and]
  exact absurd case7_direct_check_true (by rw [hf]; decide)

/-! ## Main theorem -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Case 7 upper bound**: α(E_{5/2} ⊠ (E_{5/2} ⊠ E_{8/3})) ≤ 11.

The nested floor bound gives α ≤ 12. The Baumert slicing technique
([BMRRS, Computation], analogous to [BMRRS, Theorem 4] for C₅³) shows α ≠ 12:
direct layer-assignment search over E_{5/2} ⊠ E_{8/3} finds no valid configuration.
See `case7_direct_check_true`. -/
theorem alpha3_5o2_5o2_8o3_le :
    (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).indepNum ≤ 11 := by
  by_contra hge; push_neg at hge
  have hle : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).indepNum ≤ 12 := by
    have h := nested_floor_three 5 2 5 2 8 3
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have h1 : ⌊(8:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
    simp only [Nat.cast_ofNat, h1] at h; norm_cast at h
    have h2 : ⌊(5:ℝ)/2 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h2] at h; norm_cast at h
    have h3 : ⌊(5:ℝ)/2 * 5⌋₊ = 12 := floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h3] at h; exact h
  have heq : (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).indepNum = 12 := by omega
  -- Get IS of size 12
  obtain ⟨S, hSndp⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := strongProduct (fractionGraph 5 2) (strongProduct (fractionGraph 5 2) (fractionGraph 8 3)))
  rw [heq] at hSndp
  -- Derive edge fiber constraints using fiber_bound_clique + α(E_{5/2} ⊠ E_{8/3}) = 5
  have hfbc : ∀ i : ZMod 5,
      (S.filter (fun p => p.1 ∈ ({i, i + 1} : Finset (ZMod 5)))).card ≤ 5 := by
    intro i
    have h := fiber_bound_clique (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))
      S hSndp.isIndepSet ({i, i + 1}) (edge_clique_E52 i)
    rwa [alpha_5o2_8o3] at h
  exact case7_baumert_contradiction S hSndp.isIndepSet hSndp.card_eq hfbc

end Section6
