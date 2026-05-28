/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Section 6 Baumert Bridge: α(E_{8/3}³) ≤ 12 (alpha3_8o3_8o3_8o3_le)

Bridge file split off from `Section6UpperBounds.lean` (the original "Case 8"
bridge). Slices an IS in `E_{8/3}³` into 8 layers in `E_{8/3}²`, derives the
forced layer sizes (1,2,1,2,2,1,2,2), and rules out cardinality 13 by exhaustive
search (`case8_check_true`).

See `Section6UpperBoundsCommon` for the shared infrastructure
(`fiber_bound_clique`, `floor_val`, `alpha_8o3_sq`, `three_clique_E83`, etc.).
-/
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase8
import Mathlib.Data.Bool.AllAny
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems

set_option linter.style.nativeDecide false

open ShannonCapacity

namespace Section6

/-! ## Case 8 Baumert contradiction lemma

The following lemma captures the combinatorial heart of the Baumert argument:
given an IS S of size 13 in E_{8/3}³ satisfying the 3-clique fiber constraints,
derive a contradiction. The proof uses:
1. Fiber decomposition: layer sizes sum to 13
2. IP: the 3-clique constraints force sizes to be a rotation of (1,2,1,2,2,1,2,2)
3. Translation invariance: WLOG rotation is canonical
4. `case8_check_true`: exhaustive search finds no valid assignment -/

/-- The fiber of S over a single layer i. -/
private def layerFiber (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8))) (i : ZMod 8) :=
  S.filter (fun p => p.1 = i)

/-- Layer fibers for distinct indices are disjoint. -/
private lemma layerFiber_disjoint (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8)))
    (i j : ZMod 8) (hij : i ≠ j) :
    Disjoint (layerFiber S i) (layerFiber S j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [layerFiber, Finset.mem_filter] at hx hy
  exact hij (hx.2 ▸ hy.2)

/-- Layer sizes sum to |S| by fiber decomposition. -/
private lemma layer_sum_eq_card (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8))) :
    ∑ i : ZMod 8, (layerFiber S i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [layerFiber, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x.1, h, rfl⟩⟩
  · intro i _ j _ hij
    exact layerFiber_disjoint S i j hij

/-- The 3-element filter decomposes as union of single-element filters. -/
private lemma triple_filter_eq (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8))) (i : ZMod 8) :
    S.filter (fun p => p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 8))) =
    layerFiber S i ∪ layerFiber S (i + 1) ∪ layerFiber S (i + 2) := by
  ext x; simp only [layerFiber, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

-- `three_distinct_zmod8` is now in `Section6UpperBoundsCommon`.

/-- Triple fiber bound decomposes into sum of layer sizes. -/
private lemma triple_bound_sum (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8))) (i : ZMod 8)
    (hfbc : (S.filter (fun p => p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 8)))).card ≤ 5) :
    (layerFiber S i).card + (layerFiber S (i + 1)).card +
    (layerFiber S (i + 2)).card ≤ 5 := by
  rw [triple_filter_eq] at hfbc
  have hd := three_distinct_zmod8 i
  have h1 := Finset.card_union_of_disjoint (layerFiber_disjoint S _ _ hd.1)
  have h23 : Disjoint (layerFiber S i ∪ layerFiber S (i + 1)) (layerFiber S (i + 2)) := by
    rw [Finset.disjoint_union_left]
    exact ⟨layerFiber_disjoint S _ _ hd.2.1, layerFiber_disjoint S _ _ hd.2.2⟩
  have h2 := Finset.card_union_of_disjoint h23
  linarith

/-- IP feasibility check: every 8-tuple summing to 13 with all consecutive-triple
    constraints ≤ 5 must be a rotation of (1,2,1,2,2,1,2,2).
    We check this by native_decide on {0,...,5}⁸. -/
private def ip_solutions : List (Fin 8 → ℕ) :=
  let sizes := List.range 6  -- 0..5
  sizes.flatMap fun s0 => sizes.flatMap fun s1 => sizes.flatMap fun s2 =>
  sizes.flatMap fun s3 => sizes.flatMap fun s4 => sizes.flatMap fun s5 =>
  sizes.flatMap fun s6 => sizes.map fun s7 =>
    fun i : Fin 8 => match i with
      | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3
      | 4 => s4 | 5 => s5 | 6 => s6 | 7 => s7

-- `canonical_sizes` and `is_rotation_of_canonical` are now in
-- `Section6UpperBoundsCommon`.

/-! ### Part A: Bridge lemma -/

-- `mem_verts83` is provided by `Section6UpperBoundsCase8_Common`.

set_option linter.style.nativeDecide false in
/-- Bridge: `crossNonAdj83 a b = true` iff the formal E_{8/3}² adj-or-eq condition fails. -/
private lemma crossNonAdj83_spec (a b : ZMod 8 × ZMod 8) :
    crossNonAdj83 a b = true ↔
    ¬((a.1 = b.1 ∨ (fractionGraph 8 3).Adj a.1 b.1) ∧
      (a.2 = b.2 ∨ (fractionGraph 8 3).Adj a.2 b.2)) := by
  revert a b; native_decide

/-! ### Part B: Cross-layer non-adjacency from IS -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- From IS property and first-coordinate adj-or-eq, derive `crossNonAdj83` on projections. -/
private lemma cross_compat_of_IS
    (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet ↑S)
    (x y : ZMod 8 × (ZMod 8 × ZMod 8))
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h1 : x.1 = y.1 ∨ (fractionGraph 8 3).Adj x.1 y.1) :
    crossNonAdj83 x.2 y.2 = true := by
  rw [crossNonAdj83_spec]
  intro ⟨hc1, hc2⟩
  have hnadj : ¬(strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).Adj x y :=
    (SimpleGraph.isIndepSet_iff _).mp hIS
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  apply hnadj
  refine ⟨hxy, ?_, ?_⟩
  · exact h1
  · by_cases heq : x.2 = y.2
    · exact Or.inl heq
    · exact Or.inr ⟨heq, hc1, hc2⟩

/-! ### Part C: IP bridge to rotation -/

-- `ip_rotation_fin6` and `ip_rotation` are now in `Section6UpperBoundsCommon`.

/-! ### Part D: Translation map -/

/-- Translate S by shifting the first coordinate. -/
private def translateFst (k : ZMod 8) (x : ZMod 8 × (ZMod 8 × ZMod 8)) :
    ZMod 8 × (ZMod 8 × ZMod 8) :=
  (x.1 + k, x.2)

private lemma translateFst_injective (k : ZMod 8) : Function.Injective (translateFst k) := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [translateFst, Prod.mk.injEq] at h
  exact Prod.ext (add_right_cancel h.1) h.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Translation preserves the IS property. -/
private lemma translateFst_IS (k : ZMod 8)
    (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8)))
    (hIS : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet ↑S) :
    (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet
      ↑(S.image (translateFst k)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨⟨a1, a2⟩, ha, rfl⟩ := hx
  obtain ⟨⟨b1, b2⟩, hb, rfl⟩ := hy
  simp only [translateFst] at hne hadj
  have hne' : (a1, a2) ≠ (b1, b2) := fun h => by
    have h1 : a1 = b1 := congr_arg Prod.fst h
    have h2 : a2 = b2 := congr_arg Prod.snd h
    subst h1; subst h2; exact hne rfl
  exact (SimpleGraph.isIndepSet_iff _).mp hIS
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne'
    ⟨hne', hadj.2.1.imp (fun h => add_right_cancel h)
      (fractionGraph_adj_translate 8 3 a1 b1 k).mp, hadj.2.2⟩

/-- Translation shifts layer fibers. -/
private lemma translateFst_layerFiber (k : ZMod 8)
    (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8))) (i : ZMod 8) :
    (layerFiber (S.image (translateFst k)) (i + k)).card = (layerFiber S i).card := by
  have : layerFiber (S.image (translateFst k)) (i + k) =
      (layerFiber S i).image (translateFst k) := by
    ext ⟨j, a⟩
    simp only [layerFiber, Finset.mem_filter, Finset.mem_image, translateFst]
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
  rw [this, Finset.card_image_of_injective _ (translateFst_injective k)]

/-! ### Part E: Main contradiction -/

private lemma enc83_injective : Function.Injective enc83 := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [enc83] at h
  have ha1 := a1.isLt; have ha2 := a2.isLt
  have hb1 := b1.isLt; have hb2 := b2.isLt
  have h1 : a1.val = b1.val := by omega
  have h2 : a2.val = b2.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

private lemma extract_single_from_layer
    (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8))) (i : ZMod 8)
    (hcard : (layerFiber S i).card = 1) :
    ∃ a : ZMod 8 × ZMod 8, (i, a) ∈ S := by
  obtain ⟨⟨j, a⟩, hja⟩ := Finset.card_pos.mp (by omega : 0 < (layerFiber S i).card)
  rw [layerFiber, Finset.mem_filter] at hja
  exact ⟨a, hja.2 ▸ hja.1⟩

private lemma extract_ordered_pair_from_layer
    (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8))) (i : ZMod 8)
    (hcard : (layerFiber S i).card = 2) :
    ∃ a b : ZMod 8 × ZMod 8,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ a ≠ b ∧ enc83 a < enc83 b := by
  obtain ⟨⟨i1, a⟩, ⟨i2, b⟩, hne, hfib⟩ := Finset.card_eq_two.mp hcard
  have h1 : (i1, a) ∈ layerFiber S i := hfib ▸ Finset.mem_insert_self _ _
  have h2 : (i2, b) ∈ layerFiber S i :=
    hfib ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  rw [layerFiber, Finset.mem_filter] at h1 h2
  obtain ⟨h1m, h1e⟩ := h1
  obtain ⟨h2m, h2e⟩ := h2
  subst h1e; subst h2e
  have hab : a ≠ b := fun h => hne (Prod.ext rfl h)
  rcases Nat.lt_or_gt_of_ne (fun h => hab (enc83_injective h)) with hlt | hgt
  · exact ⟨a, b, h1m, h2m, hab, hlt⟩
  · exact ⟨b, a, h2m, h1m, hab.symm, hgt⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma case8_baumert_contradiction
    (S : Finset (ZMod 8 × (ZMod 8 × ZMod 8)))
    (hSis : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).IsIndepSet ↑S)
    (hScard : S.card = 13)
    (hfbc : ∀ i : ZMod 8,
      (S.filter (fun p => p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 8)))).card ≤ 5) :
    False := by
  -- IP rotation
  obtain ⟨k, hk⟩ := ip_rotation (fun i => (layerFiber S i).card)
    (by change ∑ i, (layerFiber S i).card = 13; rw [layer_sum_eq_card]; exact hScard)
    (fun i => triple_bound_sum S i (hfbc i))
  -- Translate to canonical sizes — cast rotation index to ZMod 8
  let κ : ZMod 8 := k
  set S' := S.image (translateFst κ) with hS'_def
  have hIS' := translateFst_IS κ S hSis
  have hcanon : ∀ j : ZMod 8, (layerFiber S' j).card = canonical_sizes j := by
    intro j
    have h := translateFst_layerFiber κ S (j - κ)
    rw [sub_add_cancel] at h
    rw [h, hk (j - κ)]
    congr 1
    ext
    change ((j - κ).val + κ.val) % 8 = j.val
    rw [← ZMod.val_add, sub_add_cancel]
  -- Universal cross-compat
  have hcc := cross_compat_of_IS S' hIS'
  -- Helper for distinctness across layers
  have hne_layer : ∀ (i j : ZMod 8) (a b : ZMod 8 × ZMod 8),
      i ≠ j → (i, a) ≠ (j, b) :=
    fun _ _ _ _ hij h => hij (congr_arg Prod.fst h)
  -- Helper for cross-layer crossNonAdj83
  have cc : ∀ (i j : ZMod 8) (a b : ZMod 8 × ZMod 8),
      (i, a) ∈ S' → (j, b) ∈ S' → i ≠ j →
      (fractionGraph 8 3).Adj i j →
      crossNonAdj83 a b = true :=
    fun i j a b ha hb hij hadj =>
      hcc _ _ ha hb (hne_layer i j a b hij) (Or.inr hadj)
  -- Same-layer crossNonAdj83
  have cc_eq : ∀ (i : ZMod 8) (a b : ZMod 8 × ZMod 8),
      (i, a) ∈ S' → (i, b) ∈ S' → a ≠ b →
      crossNonAdj83 a b = true :=
    fun i a b ha hb hab =>
      hcc _ _ ha hb (fun h => hab (congr_arg Prod.snd h)) (Or.inl rfl)
  -- Extract witnesses from each layer
  obtain ⟨w0, hw0⟩ := extract_single_from_layer S' 0
    (by rw [hcanon]; rfl)
  obtain ⟨w10, w11, hw10, hw11, hne1, hlt1⟩ := extract_ordered_pair_from_layer S' 1
    (by rw [hcanon]; rfl)
  obtain ⟨w2, hw2⟩ := extract_single_from_layer S' 2
    (by rw [hcanon]; rfl)
  obtain ⟨w30, w31, hw30, hw31, hne3, hlt3⟩ := extract_ordered_pair_from_layer S' 3
    (by rw [hcanon]; rfl)
  obtain ⟨w40, w41, hw40, hw41, hne4, hlt4⟩ := extract_ordered_pair_from_layer S' 4
    (by rw [hcanon]; rfl)
  obtain ⟨w5, hw5⟩ := extract_single_from_layer S' 5
    (by rw [hcanon]; rfl)
  obtain ⟨w60, w61, hw60, hw61, hne6, hlt6⟩ := extract_ordered_pair_from_layer S' 6
    (by rw [hcanon]; rfl)
  obtain ⟨w70, w71, hw70, hw71, hne7, hlt7⟩ := extract_ordered_pair_from_layer S' 7
    (by rw [hcanon]; rfl)
  -- Adjacency facts (all pairs at distance ≤ 2 in E_{8/3})
  -- cc i j a b : crossNonAdj83 a b, needs (frG 8 3).Adj i j
  -- Helper: prove compatWith83 using cc
  have compat_of_list : ∀ (i : ZMod 8) (a : ZMod 8 × ZMod 8)
      (ws : List (ZMod 8 × (ZMod 8 × ZMod 8))),
      (i, a) ∈ S' →
      (∀ w ∈ ws, w ∈ S' ∧ (i ≠ w.1 → (fractionGraph 8 3).Adj i w.1) ∧
        (i = w.1 → a ≠ w.2)) →
      compatWith83 a (ws.map Prod.snd) = true := by
    intro i a ws hia hws
    simp only [compatWith83, List.all_eq_true, List.mem_map]
    rintro b ⟨⟨j, b'⟩, hjb_mem, rfl⟩
    have ⟨hjb_S, hadj, hneq⟩ := hws _ hjb_mem
    by_cases hij : i = j
    · subst hij; exact cc_eq i a b' hia hjb_S (hneq rfl)
    · exact cc i j a b' hia hjb_S hij (hadj hij)
  -- Derive contradiction via case8_check
  -- Adjacency facts between layers in E_{8/3}
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
  -- crossNonAdj83 conditions for v0/v10/v11 (layers 0,1)
  have cn_10_0 := cc 1 0 w10 w0 hw10 hw0 (by decide) adj01.symm
  have cn_10_11 := cc_eq 1 w10 w11 hw10 hw11 hne1
  have cn_11_0 := cc 1 0 w11 w0 hw11 hw0 (by decide) adj01.symm
  -- compatWith83 conditions via compat_of_list
  -- Layer 2 (v2): compat with [v0, v10, v11] — layers 0,1,1
  have cpt_v2 := compat_of_list 2 w2 [(0, w0), (1, w10), (1, w11)] hw2
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw0, fun _ => adj02.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw10, fun _ => adj12.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj12.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 3a (v30): compat with [v10, v11, v2] — layers 1,1,2
  have cpt_v30 := compat_of_list 3 w30 [(1, w10), (1, w11), (2, w2)] hw30
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw10, fun _ => adj13.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj13.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj23.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 3b (v31): compat with [v10, v11, v2]
  have cpt_v31 := compat_of_list 3 w31 [(1, w10), (1, w11), (2, w2)] hw31
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw10, fun _ => adj13.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj13.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw2, fun _ => adj23.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 4a (v40): compat with [v2, v30, v31] — layers 2,3,3
  have cpt_v40 := compat_of_list 4 w40 [(2, w2), (3, w30), (3, w31)] hw40
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw2, fun _ => adj24.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw30, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 4b (v41): compat with [v2, v30, v31]
  have cpt_v41 := compat_of_list 4 w41 [(2, w2), (3, w30), (3, w31)] hw41
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨hw2, fun _ => adj24.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw30, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj34.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 5 (v5): compat with [v30, v31, v40, v41] — layers 3,3,4,4
  have cpt_v5 := compat_of_list 5 w5 [(3, w30), (3, w31), (4, w40), (4, w41)] hw5
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw30, fun _ => adj35.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw31, fun _ => adj35.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw40, fun _ => adj45.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw41, fun _ => adj45.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 6a (v60): compat with [v40, v41, v5, v0] — layers 4,4,5,0
  have cpt_v60 := compat_of_list 6 w60 [(4, w40), (4, w41), (5, w5), (0, w0)] hw60
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw40, fun _ => adj46.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw41, fun _ => adj46.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj56.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj06.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 6b (v61): compat with [v40, v41, v5, v0]
  have cpt_v61 := compat_of_list 6 w61 [(4, w40), (4, w41), (5, w5), (0, w0)] hw61
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨hw40, fun _ => adj46.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw41, fun _ => adj46.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw5, fun _ => adj56.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj06.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 7a (v70): compat with [v5, v60, v61, v0, v10, v11] — layers 5,6,6,0,1,1
  have cpt_v70 := compat_of_list 7 w70
    [(5, w5), (6, w60), (6, w61), (0, w0), (1, w10), (1, w11)] hw70
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw5, fun _ => adj57.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw60, fun _ => adj67.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw61, fun _ => adj67.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj07.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw10, fun _ => adj17.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj17.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Layer 7b (v71): compat with [v5, v60, v61, v0, v10, v11]
  have cpt_v71 := compat_of_list 7 w71
    [(5, w5), (6, w60), (6, w61), (0, w0), (1, w10), (1, w11)] hw71
    (by intro w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hw5, fun _ => adj57.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw60, fun _ => adj67.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw61, fun _ => adj67.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw0, fun _ => adj07.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw10, fun _ => adj17.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩
        · exact ⟨hw11, fun _ => adj17.symm, fun h => by dsimp at h; exact absurd h (by decide)⟩)
  -- Additional crossNonAdj83 for within-layer pairs
  have cn_30_31 := cc_eq 3 w30 w31 hw30 hw31 hne3
  have cn_40_41 := cc_eq 4 w40 w41 hw40 hw41 hne4
  have cn_60_61 := cc_eq 6 w60 w61 hw60 hw61 hne6
  have cn_70_71 := cc_eq 7 w70 w71 hw70 hw71 hne7
  -- Helper: crossNonAdj83 implies ≠
  have ne_of_cn : ∀ a b : Fin 8 × Fin 8,
      crossNonAdj83 a b = true → a ≠ b := by
    intro a b h heq; subst heq
    have : crossNonAdj83 a a = false := by revert a; native_decide
    rw [this] at h; exact absurd h (by decide)
  -- v2 crossNonAdj83 facts (needed for the bne conditions in case8_check)
  have cn_v2_v0 := cc 2 0 w2 w0 hw2 hw0 (by decide) adj02.symm
  have cn_v2_v10 := cc 2 1 w2 w10 hw2 hw10 (by decide) adj12.symm
  have cn_v2_v11 := cc 2 1 w2 w11 hw2 hw11 (by decide) adj12.symm
  -- Normalize List.map Prod.snd in compat hypotheses to match case8_check's lists
  simp only [List.map] at cpt_v2
  simp only [List.map] at cpt_v30 cpt_v31
  simp only [List.map] at cpt_v40 cpt_v41 cpt_v5
  simp only [List.map] at cpt_v60 cpt_v61 cpt_v70 cpt_v71
  -- Contradiction: case8_check_true says true, but our witnesses show false
  exfalso
  have hf : case8_check = false := by
    unfold case8_check; simp only [Bool.not_eq_false']
    apply List.any_of_mem (mem_verts83 w0)
    unfold innerSearch_v0_case8
    apply List.any_of_mem (mem_verts83 w10)
    simp only [cn_10_0, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w11)
    simp only [decide_eq_true hlt1, cn_10_11, cn_11_0, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w2)
    simp only [beq_false_of_ne (ne_of_cn _ _ cn_v2_v0),
               beq_false_of_ne (ne_of_cn _ _ cn_v2_v10),
               beq_false_of_ne (ne_of_cn _ _ cn_v2_v11),
               Bool.not_false, cpt_v2, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w30)
    simp only [cpt_v30, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w31)
    simp only [decide_eq_true hlt3, cn_30_31, cpt_v31, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w40)
    simp only [cpt_v40, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w41)
    simp only [decide_eq_true hlt4, cn_40_41, cpt_v41, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w5)
    simp only [cpt_v5, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w60)
    simp only [cpt_v60, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w61)
    simp only [decide_eq_true hlt6, cn_60_61, cpt_v61, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w70)
    simp only [cpt_v70, Bool.true_and]
    apply List.any_of_mem (mem_verts83 w71)
    simp only [decide_eq_true hlt7, cn_70_71, cpt_v71, Bool.true_and]
  exact absurd case8_check_true (by rw [hf]; decide)

/-! ## Main theorem -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Case 8 upper bound**: α(E_{8/3} ⊠ (E_{8/3} ⊠ E_{8/3})) ≤ 12.

The nested floor bound gives α ≤ 13. The Baumert slicing technique
([BMRRS, Lemma 3], for C₁₃³ → 252) shows α ≠ 13: slicing into 8 layers
forces sizes (1,2,1,2,2,1,2,2), and exhaustive search finds no valid
assignment. See `case8_check_true`. -/
theorem alpha3_8o3_8o3_8o3_le :
    (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum ≤ 12 := by
  by_contra hge; push_neg at hge
  have hle : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum ≤ 13 := by
    have h := nested_floor_three 8 3 8 3 8 3
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have h1 : ⌊(8:ℝ)/3⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
    simp only [Nat.cast_ofNat, h1] at h; norm_cast at h
    have h2 : ⌊(8:ℝ)/3 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h2] at h; norm_cast at h
    have h3 : ⌊(8:ℝ)/3 * 5⌋₊ = 13 := floor_val (by positivity) (by norm_num) (by norm_num)
    rw [h3] at h; exact h
  have heq : (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum = 13 := by omega
  -- Get IS of size 13
  obtain ⟨S, hSndp⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := strongProduct (fractionGraph 8 3) (strongProduct (fractionGraph 8 3) (fractionGraph 8 3)))
  rw [heq] at hSndp
  -- Derive 3-clique fiber constraints using fiber_bound_clique + α(E_{8/3}²) = 5
  have hfbc : ∀ i : ZMod 8,
      (S.filter (fun p => p.1 ∈ ({i, i + 1, i + 2} : Finset (ZMod 8)))).card ≤ 5 := by
    intro i
    have h := fiber_bound_clique (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))
      S hSndp.isIndepSet ({i, i + 1, i + 2}) (three_clique_E83 i)
    rwa [alpha_8o3_sq] at h
  exact case8_baumert_contradiction S hSndp.isIndepSet hSndp.card_eq hfbc

end Section6
