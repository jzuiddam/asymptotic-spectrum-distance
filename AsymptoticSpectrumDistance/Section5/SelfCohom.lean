/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section3.Convergence
import AsymptoticSpectrumDistance.Section5.ConvexRound

set_option linter.unnecessarySimpa false

/-!
# Self-Cohomomorphisms: Core Infrastructure

This file contains the core infrastructure for characterizing self-cohomomorphisms
of fraction graphs and circle graphs. The continuity proof, gap lemma, and
non-equivalence theorem are in `SelfCohomContinuity.lean`.

## Main results

* `fractionGraph_selfCohom_isIso` : Self-cohomomorphisms of E_{p/q} are isomorphisms
* `fractionGraph_selfIso_form` : Self-isomorphisms are rotations ± reflections
* `fractionGraph_iso_consecutive_or_reversed` : Cyclic order from graph isomorphisms
* `fractionGraph_iso_preserves_arc_containment` : Arc containment from isomorphisms
* `insertion_same_gap_of_both_iso_to_fraction` : Same gap property
* `fractionGraph_iso_arc_containment_disjunction` : Disjunction for arc containment
* `same_slot_of_shared_skeleton` : Same slot property for shared skeleton

## References

* [de Boer, Buys, Zuiddam] Section 5
* [BJH02] Bang-Jensen, Huang, "Convex-Round Graphs are Circular-Perfect", J. Graph Theory 40 (2002)
-/

namespace AsymptoticSpectrumDistance

open Universality AsymptoticSpectrumGraphs SimpleGraph FractionGraphBasic

/-! ### Self-Cohomomorphisms of Fraction Graphs -/

/-! Helper definitions for fraction graphs -/

def arc (p q : ℕ) [NeZero p] (x : ZMod p) : Finset (ZMod p) :=
  (Finset.range q).image (fun i : ℕ => x + (i : ZMod p))

lemma mem_arc_iff (p q : ℕ) [NeZero p] (x v : ZMod p) :
    v ∈ arc p q x ↔ ∃ i < q, v = x + (i : ZMod p) := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

lemma arc_add_left (p q : ℕ) [NeZero p] (c x : ZMod p) :
    (arc p q (x + c)) = (arc p q x).image (fun v => v + c) := by
  classical
  ext v
  constructor
  · intro hv
    rcases (mem_arc_iff p q (x + c) v).1 hv with ⟨i, hi, rfl⟩
    have hx : x + (i : ZMod p) ∈ arc p q x := by
      exact (mem_arc_iff p q x (x + (i : ZMod p))).2 ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨x + (i : ZMod p), hx, by abel⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    rcases (mem_arc_iff p q x w).1 hw with ⟨i, hi, rfl⟩
    exact (mem_arc_iff p q (x + c) (x + (i : ZMod p) + c)).2
      ⟨i, hi, by abel⟩

lemma arc_inter_eq (p q : ℕ) [NeZero p] (h2q : 2 * q ≤ p)
    (x : ZMod p) (k : ℕ) (hk : k < q) :
    (arc p q x ∩ arc p q (x + (k : ZMod p))) =
      arc p (q - k) (x + (k : ZMod p)) := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hx, hy⟩
    rcases (mem_arc_iff p q x v).1 hx with ⟨i, hi, hvi⟩
    rcases (mem_arc_iff p q (x + (k : ZMod p)) v).1 hy with ⟨j, hj, hvj⟩
    have h_eq : (i : ZMod p) = ((k + j : ℕ) : ZMod p) := by
      have h1 : x + (i : ZMod p) = x + ((k + j : ℕ) : ZMod p) := by
        calc
          x + (i : ZMod p) = v := by simp [hvi]
          _ = x + (k : ZMod p) + (j : ZMod p) := by simp [hvj, add_assoc]
          _ = x + ((k + j : ℕ) : ZMod p) := by
                simp [Nat.cast_add, add_assoc]
      exact (add_left_cancel_iff.mp h1)
    have hkq : k + j < p := by
      have : k + j < 2 * q := by omega
      exact lt_of_lt_of_le this h2q
    have hval :
        (i : ZMod p).val = ((k + j : ℕ) : ZMod p).val := congrArg ZMod.val h_eq
    have hi' : i < p := lt_of_lt_of_le hi (by omega)
    have hkj' : k + j < p := hkq
    have hnat : i = k + j := by
      simpa [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hkj', -Nat.cast_add] using hval
    have hj' : j < q - k := by
      have hk_le : k ≤ q := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hk (Nat.le_succ _))
      have : k + j < q := by simpa [hnat] using hi
      omega
    have hvi' : v = x + (k : ZMod p) + (j : ZMod p) := by
      simpa [hnat, add_assoc] using hvi
    exact (mem_arc_iff p (q - k) (x + (k : ZMod p)) v).2 ⟨j, hj', hvi'⟩
  · intro hv
    rcases (mem_arc_iff p (q - k) (x + (k : ZMod p)) v).1 hv with ⟨j, hj, hvj⟩
    have hkj : k + j < q := by
      have hk_le : k ≤ q := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hk (Nat.le_succ _))
      omega
    have hmem1 : v ∈ arc p q x := by
      refine (mem_arc_iff p q x v).2 ?_
      refine ⟨k + j, hkj, ?_⟩
      simp [hvj, add_assoc]
    have hmem2 : v ∈ arc p q (x + (k : ZMod p)) := by
      refine (mem_arc_iff p q (x + (k : ZMod p)) v).2 ?_
      exact ⟨j, lt_of_lt_of_le hj (Nat.sub_le _ _), hvj⟩
    exact Finset.mem_inter.mpr ⟨hmem1, hmem2⟩

lemma arc_card (p q : ℕ) [NeZero p] (h2q : 2 * q ≤ p) (x : ZMod p) :
    (arc p q x).card = q := by
  classical
  have hq_le_p : q ≤ p := by omega
  have h_inj : Set.InjOn (fun i : ℕ => x + (i : ZMod p)) (Finset.range q) := by
    intro i hi j hj h_eq
    have hij : (i : ZMod p) = (j : ZMod p) := by
      exact (add_left_cancel_iff.mp h_eq)
    have hi' : i < p := lt_of_lt_of_le (Finset.mem_range.mp hi) hq_le_p
    have hj' : j < p := lt_of_lt_of_le (Finset.mem_range.mp hj) hq_le_p
    have hval : (i : ZMod p).val = (j : ZMod p).val := congrArg ZMod.val hij
    simpa [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] using hval
  have hcard := Finset.card_image_of_injOn h_inj
  simpa [arc] using hcard

lemma arc_inter_card (p q : ℕ) [NeZero p] (h2q : 2 * q ≤ p)
    (x : ZMod p) (k : ℕ) (hk : k < q) :
    (arc p q x ∩ arc p q (x + (k : ZMod p))).card = q - k := by
  have h2q' : 2 * (q - k) ≤ p := by omega
  simp [arc_inter_eq p q h2q x k hk, arc_card p (q - k) h2q' _]

lemma arc_isClique (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    (x : ZMod p) : (fractionGraph p q).IsClique (arc p q x) := by
  classical
  rw [SimpleGraph.isClique_iff]
  intro u hu v hv huv
  have hu' : u ∈ arc p q x := by simpa using hu
  have hv' : v ∈ arc p q x := by simpa using hv
  rcases Finset.mem_image.mp hu' with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hv' with ⟨b, hb, rfl⟩
  have hclique := FractionGraphBasic.isClique_range_fractionGraph p q hq h2q
  have hclique' :
      (↑((Finset.range q).image (fun i : ℕ => (i : ZMod p))) :
          Set (ZMod p)).Pairwise (fractionGraph p q).Adj := by
    simpa [SimpleGraph.isClique_iff] using hclique
  have ha' : (a : ZMod p) ∈ (Finset.range q).image (fun i : ℕ => (i : ZMod p)) := by
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hb' : (b : ZMod p) ∈ (Finset.range q).image (fun i : ℕ => (i : ZMod p)) := by
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have huv' : (a : ZMod p) ≠ (b : ZMod p) := by
    intro h_eq
    apply huv
    simp [h_eq]
  have hadj : (fractionGraph p q).Adj (a : ZMod p) (b : ZMod p) :=
    hclique' ha' hb' huv'
  exact (fractionGraph_adj_add_left p q x (a : ZMod p) (b : ZMod p)).2 hadj

lemma exists_pair_dist_eq_q_sub_one (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (S : Finset (ZMod p))
    (hclique : (fractionGraph p q).IsClique S) (hcard : S.card = q) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ FractionGraphBasic.distMod p u v = q - 1 := by
  classical
  by_contra h
  have hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → FractionGraphBasic.distMod p u v < q - 1 := by
    intro u hu v hv huv
    have hadj : (fractionGraph p q).Adj u v := by
      have hclique' := hclique
      rw [SimpleGraph.isClique_iff] at hclique'
      exact hclique' hu hv huv
    have hdist_lt_q : FractionGraphBasic.distMod p u v < q := by
      simpa [fractionGraph] using hadj.2
    have hdist_ne : FractionGraphBasic.distMod p u v ≠ q - 1 := by
      intro hdist_eq
      apply h
      exact ⟨u, hu, v, hv, huv, hdist_eq⟩
    have hle : FractionGraphBasic.distMod p u v ≤ q - 1 := by
      have : FractionGraphBasic.distMod p u v < (q - 1) + 1 := by
        omega
      exact Nat.lt_succ_iff.mp this
    exact lt_of_le_of_ne hle (by exact hdist_ne)
  have hq' : 0 < q - 1 := by omega
  have h2q' : 2 * (q - 1) ≤ p := by omega
  have hcard_le :
      S.card ≤ q - 1 :=
    FractionGraphBasic.finset_card_le_of_pairwise_dist_lt p (q - 1) hq' h2q' S hpair
  omega

lemma isClique_image_add (p q : ℕ) [NeZero p] (S : Finset (ZMod p)) (c : ZMod p)
    (hS : (fractionGraph p q).IsClique S) :
    (fractionGraph p q).IsClique (S.image (fun v => v + c)) := by
  classical
  rw [SimpleGraph.isClique_iff] at hS ⊢
  intro u hu v hv huv
  rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
  rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
  have huv' : u' ≠ v' := by
    intro h_eq
    apply huv
    simp [h_eq]
  have hadj := hS hu' hv' huv'
  have hadj' : (fractionGraph p q).Adj (c + u') (c + v') := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (fractionGraph_adj_add_left p q c u' v').2 hadj
  simpa [add_comm, add_left_comm, add_assoc] using hadj'

lemma card_image_add (p : ℕ) [NeZero p] (S : Finset (ZMod p)) (c : ZMod p) :
    (S.image (fun v => v + c)).card = S.card := by
  classical
  refine Finset.card_image_of_injective _ ?_
  intro u v h
  exact (add_right_cancel_iff.mp h)

lemma nonadj_low_high (p q : ℕ) [NeZero p] (h2q : 2 * q ≤ p)
    (i : ℕ) (hi : i < q) :
    ¬(fractionGraph p q).Adj (i : ZMod p) (i + (p - q) : ℕ) := by
  intro hadj
  have hdist_lt : FractionGraphBasic.distMod p (i : ZMod p) (i + (p - q) : ℕ) < q := by
    simpa [fractionGraph] using hadj.2
  have hi_lt_p : i < p := by omega
  have hhigh_lt_p : i + (p - q) < p := by omega
  have hle_val :
      ((i : ℕ) : ZMod p).val ≤ ((i + (p - q) : ℕ) : ZMod p).val := by
    rw [ZMod.val_natCast_of_lt hi_lt_p, ZMod.val_natCast_of_lt hhigh_lt_p]
    omega
  have hdiff_ge :
      q ≤ ((i + (p - q) : ℕ) : ZMod p).val - ((i : ℕ) : ZMod p).val := by
    rw [ZMod.val_natCast_of_lt hi_lt_p, ZMod.val_natCast_of_lt hhigh_lt_p]
    omega
  have hdiff_le :
      ((i + (p - q) : ℕ) : ZMod p).val - ((i : ℕ) : ZMod p).val ≤ p - q := by
    rw [ZMod.val_natCast_of_lt hi_lt_p, ZMod.val_natCast_of_lt hhigh_lt_p]
    omega
  have hdist_ge :=
    FractionGraphBasic.distMod_ge_q_of_val_diff_in_range p q h2q
      (i : ZMod p) (i + (p - q) : ℕ) hle_val hdiff_ge hdiff_le
  exact (not_lt_of_ge hdist_ge) hdist_lt

lemma nonadj_high_low_next (p q : ℕ) [NeZero p] (h2q' : 2 * q + 1 ≤ p)
    (i : ℕ) (hi : i + 1 < q) :
    ¬(fractionGraph p q).Adj (i + (p - q) : ℕ) (i + 1 : ℕ) := by
  intro hadj
  have hdist_lt : FractionGraphBasic.distMod p (i + 1 : ℕ) (i + (p - q) : ℕ) < q := by
    simpa [fractionGraph, FractionGraphBasic.distMod_comm] using hadj.2
  have hi_lt_p : i + 1 < p := by omega
  have hhigh_lt_p : i + (p - q) < p := by omega
  have hle_val :
      ((i + 1 : ℕ) : ZMod p).val ≤ ((i + (p - q) : ℕ) : ZMod p).val := by
    rw [ZMod.val_natCast_of_lt hi_lt_p, ZMod.val_natCast_of_lt hhigh_lt_p]
    omega
  have hdiff_ge :
      q ≤ ((i + (p - q) : ℕ) : ZMod p).val - ((i + 1 : ℕ) : ZMod p).val := by
    rw [ZMod.val_natCast_of_lt hi_lt_p, ZMod.val_natCast_of_lt hhigh_lt_p]
    omega
  have hdiff_le :
      ((i + (p - q) : ℕ) : ZMod p).val - ((i + 1 : ℕ) : ZMod p).val ≤ p - q := by
    rw [ZMod.val_natCast_of_lt hi_lt_p, ZMod.val_natCast_of_lt hhigh_lt_p]
    omega
  have hdist_ge :=
    FractionGraphBasic.distMod_ge_q_of_val_diff_in_range p q (by omega : 2 * q ≤ p)
      (i + 1 : ℕ) (i + (p - q) : ℕ) hle_val hdiff_ge hdiff_le
  exact (not_lt_of_ge hdist_ge) hdist_lt

lemma clique_eq_arc_of_zero (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q' : 2 * q + 1 ≤ p)
    (S : Finset (ZMod p))
    (hclique : (fractionGraph p q).IsClique S) (hcard : S.card = q)
    (h0 : (0 : ZMod p) ∈ S) :
    ∃ k ≤ q, S = arc p q (p - q + k : ℕ) := by
  classical
  have hq_pos : 0 < q := by omega
  let low : ℕ → ZMod p := fun i => (i : ZMod p)
  let high : ℕ → ZMod p := fun i => (i + (p - q) : ℕ)
  have hnot_both : ∀ i < q, ¬(low i ∈ S ∧ high i ∈ S) := by
    intro i hi hboth
    have hclique' := hclique
    rw [SimpleGraph.isClique_iff] at hclique'
    have hneq : low i ≠ high i := by
      intro h_eq
      have hi_lt_p : i < p := by omega
      have hhigh_lt_p : i + (p - q) < p := by omega
      have hval : i = i + (p - q) := by
        simpa [low, high, ZMod.val_natCast_of_lt hi_lt_p,
          ZMod.val_natCast_of_lt hhigh_lt_p, -Nat.cast_add] using
          congrArg ZMod.val h_eq
      have hval' : i + 0 = i + (p - q) := by
        simpa using hval
      have hzero : 0 = p - q := Nat.add_left_cancel hval'
      have hpq : p = q := by omega
      omega
    have hadj := hclique' hboth.1 hboth.2 hneq
    exact (nonadj_low_high p q (by omega : 2 * q ≤ p) i hi) hadj
  have hval_range : ∀ v ∈ S, v.val < q ∨ v.val > p - q := by
    intro v hv
    by_cases hv0 : v = 0
    · left
      simpa [hv0] using hq_pos
    · have hclique' := hclique
      rw [SimpleGraph.isClique_iff] at hclique'
      have hadj := hclique' h0 hv (by simpa [eq_comm] using hv0)
      have hdist : FractionGraphBasic.distMod p v 0 < q := by
        simpa [fractionGraph, FractionGraphBasic.distMod_comm] using hadj.2
      have hdist' : min v.val (p - v.val) < q := by
        simpa [FractionGraphBasic.distMod] using hdist
      by_cases hlt : v.val < q
      · left; exact hlt
      · right
        have hmin : p - v.val < q := by
          have hmin_eq : min v.val (p - v.val) = p - v.val := by
            exact min_eq_right (by omega)
          simpa [hmin_eq] using hdist'
        omega
  let idx : ZMod p → ℕ := fun v =>
    if h : v.val < q then v.val else v.val - (p - q)
  have hidx_lt : ∀ v ∈ S, idx v < q := by
    intro v hv
    by_cases h : v.val < q
    · simp [idx, h]
    · have hhigh : v.val > p - q := by
        rcases hval_range v hv with hlow | hhigh
        · exact (h (by exact hlow)).elim
        · exact hhigh
      have hv_lt_p : v.val < p := ZMod.val_lt v
      have : v.val - (p - q) < q := by omega
      simp [idx, h, this]
  have hidx_inj : ∀ v1 ∈ S, ∀ v2 ∈ S, idx v1 = idx v2 → v1 = v2 := by
    intro v1 hv1 v2 hv2 hidx
    by_cases h1 : v1.val < q
    · by_cases h2 : v2.val < q
      · have hvals : v1.val = v2.val := by
          simpa [idx, h1, h2] using hidx
        exact ZMod.val_injective p hvals
      · have hvals : v1.val = v2.val - (p - q) := by
          simpa [idx, h1, h2] using hidx
        let i := v1.val
        have hiq : i < q := h1
        have hv1_eq : v1 = low i := by
          apply ZMod.val_injective
          have hi_lt_p : i < p := by omega
          simp [i, low]
        have hv2_eq : v2 = high i := by
          apply ZMod.val_injective
          have hhigh_lt_p : i + (p - q) < p := by omega
          have hle : p - q ≤ v2.val := by
            rcases hval_range v2 hv2 with hlow | hhigh
            · exact (h2 hlow).elim
            · exact Nat.le_of_lt hhigh
          have hv2_val : v2.val = i + (p - q) :=
            Nat.eq_add_of_sub_eq hle (by simpa [i] using hvals.symm)
          simp [high, ZMod.val_natCast_of_lt hhigh_lt_p, hv2_val, -Nat.cast_add]
        exfalso
        exact (hnot_both i hiq) ⟨by simpa [hv1_eq] using hv1, by simpa [hv2_eq] using hv2⟩
    · by_cases h2 : v2.val < q
      · have hvals : v1.val - (p - q) = v2.val := by
          simpa [idx, h1, h2] using hidx
        let i := v2.val
        have hiq : i < q := h2
        have hv2_eq : v2 = low i := by
          apply ZMod.val_injective
          have hi_lt_p : i < p := by omega
          simp [i, low]
        have hv1_eq : v1 = high i := by
          apply ZMod.val_injective
          have hhigh_lt_p : i + (p - q) < p := by omega
          have hle : p - q ≤ v1.val := by
            rcases hval_range v1 hv1 with hlow | hhigh
            · exact (h1 hlow).elim
            · exact Nat.le_of_lt hhigh
          have hv1_val : v1.val = i + (p - q) :=
            Nat.eq_add_of_sub_eq hle (by simpa [i] using hvals)
          simp [high, ZMod.val_natCast_of_lt hhigh_lt_p, hv1_val, -Nat.cast_add]
        exfalso
        exact (hnot_both i hiq) ⟨by simpa [hv2_eq] using hv2, by simpa [hv1_eq] using hv1⟩
      · have hvals : v1.val - (p - q) = v2.val - (p - q) := by
          simpa [idx, h1, h2] using hidx
        have hle1 : p - q ≤ v1.val := by
          rcases hval_range v1 hv1 with hlow | hhigh
          · exact (h1 hlow).elim
          · exact Nat.le_of_lt hhigh
        have hle2 : p - q ≤ v2.val := by
          rcases hval_range v2 hv2 with hlow | hhigh
          · exact (h2 hlow).elim
          · exact Nat.le_of_lt hhigh
        have hvals' : v1.val = v2.val := by
          calc
            v1.val = (v1.val - (p - q)) + (p - q) := by
              exact Nat.eq_add_of_sub_eq hle1 rfl
            _ = (v2.val - (p - q)) + (p - q) := by simpa [hvals]
            _ = v2.val := by
              symm
              exact Nat.eq_add_of_sub_eq hle2 rfl
        exact ZMod.val_injective p hvals'
  have hidx_surj : ∀ i < q, ∃ v ∈ S, idx v = i := by
    intro i hi
    have hsubset : S.image idx ⊆ Finset.range q := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      exact Finset.mem_range.mpr (hidx_lt w hw)
    have hcard_image' : (S.image idx).card = S.card := by
      refine Finset.card_image_of_injOn ?_
      intro v1 hv1 v2 hv2 h
      exact hidx_inj v1 hv1 v2 hv2 h
    have hcard_image : (S.image idx).card = q := by
      simpa [hcard] using hcard_image'
    have hcard_le : (Finset.range q).card ≤ (S.image idx).card := by
      simpa [hcard_image, Finset.card_range] using (le_rfl : q ≤ q)
    have hEq : S.image idx = Finset.range q :=
      Finset.eq_of_subset_of_card_le hsubset hcard_le
    have : i ∈ S.image idx := by
      simpa [hEq] using (Finset.mem_range.mpr hi)
    rcases Finset.mem_image.mp this with ⟨v, hv, hv_eq⟩
    exact ⟨v, hv, hv_eq⟩
  have hpair : ∀ i < q, (low i ∈ S) ∨ (high i ∈ S) := by
    intro i hi
    rcases hidx_surj i hi with ⟨v, hv, hidxv⟩
    by_cases hvlow : v.val < q
    · have hv_eq : v = low i := by
        apply ZMod.val_injective
        have hi_lt_p : i < p := by omega
        have hv_val : v.val = i := by simpa [idx, hvlow] using hidxv
        simp [low, ZMod.val_natCast_of_lt hi_lt_p, hv_val]
      left
      simpa [hv_eq] using hv
    · have hv_eq : v = high i := by
        apply ZMod.val_injective
        have hhigh_lt_p : i + (p - q) < p := by omega
        have hle : p - q ≤ v.val := by
          rcases hval_range v hv with hlow | hhigh
          · exact (hvlow hlow).elim
          · exact Nat.le_of_lt hhigh
        have hv_val : v.val = i + (p - q) := by
          have : v.val - (p - q) = i := by simpa [idx, hvlow] using hidxv
          exact Nat.eq_add_of_sub_eq hle this
        simp [high, ZMod.val_natCast_of_lt hhigh_lt_p, hv_val, -Nat.cast_add]
      right
      simpa [hv_eq] using hv
  have hhigh_step : ∀ i, i + 1 < q → high i ∈ S → high (i + 1) ∈ S := by
    intro i hi hhi
    have hnot_low : low (i + 1) ∉ S := by
      intro hlow
      have hclique' := hclique
      rw [SimpleGraph.isClique_iff] at hclique'
      have hneq : high i ≠ low (i + 1) := by
        intro h_eq
        have hhigh_lt_p : i + (p - q) < p := by omega
        have hli_lt_p : i + 1 < p := by omega
        have hval := congrArg ZMod.val h_eq
        have hval' : i + (p - q) = i + 1 := by
          simpa [high, low, ZMod.val_natCast_of_lt hhigh_lt_p,
            ZMod.val_natCast_of_lt hli_lt_p, -Nat.cast_add] using hval
        have hpq : p - q = 1 := by omega
        omega
      have hadj := hclique' hhi hlow hneq
      exact (nonadj_high_low_next p q h2q' i hi) hadj
    rcases hpair (i + 1) (by omega) with hlow | hhigh
    · exact (hnot_low hlow).elim
    · exact hhigh
  by_cases hhigh_empty : ∀ i < q, high i ∉ S
  · refine ⟨q, le_rfl, ?_⟩
    have hq_le_p : q ≤ p := by omega
    have hzero : S = arc p q (0 : ZMod p) := by
      ext v
      constructor
      · intro hv
        have hv_val_lt : v.val < q := by
          rcases hval_range v hv with hlow | hhigh
          · exact hlow
          · have hi : v.val - (p - q) < q := by
              have hle : p - q ≤ v.val := Nat.le_of_lt hhigh
              have hq_le_p : q ≤ p := by omega
              have hv_lt_p : v.val < p := ZMod.val_lt v
              have hlt : v.val < q + (p - q) := by
                have hsum : q + (p - q) = p := by
                  calc
                    q + (p - q) = (p - q) + q := by ac_rfl
                    _ = p := Nat.sub_add_cancel hq_le_p
                simpa [hsum] using hv_lt_p
              exact (Nat.sub_lt_iff_lt_add hle).2 hlt
            have hv_eq : v = high (v.val - (p - q)) := by
              apply ZMod.val_injective
              have hhigh_lt_p : v.val - (p - q) + (p - q) < p := by omega
              have hv_val : v.val = v.val - (p - q) + (p - q) := by omega
              calc
                v.val = v.val - (p - q) + (p - q) := hv_val
                _ = (high (v.val - (p - q))).val := by
                  simp [high, ZMod.val_natCast_of_lt hhigh_lt_p, -Nat.cast_add]
            have hhigh_mem : high (v.val - (p - q)) ∈ S := by
              have hv' := hv
              rw [hv_eq] at hv'
              simpa using hv'
            exact (hhigh_empty _ hi hhigh_mem).elim
        refine (mem_arc_iff p q 0 v).2 ?_
        refine ⟨v.val, hv_val_lt, ?_⟩
        have hv_lt_p : v.val < p := ZMod.val_lt v
        simp
      · intro hv
        rcases (mem_arc_iff p q 0 v).1 hv with ⟨i, hi, hv_eq⟩
        have : low i ∈ S := by
          rcases hpair i hi with h | h
          · exact h
          · exact (hhigh_empty i hi h).elim
        simpa [low, hv_eq] using this
    have hcast : ((p - q + q : ℕ) : ZMod p) = (0 : ZMod p) := by
      have hx : p - q + q = p := Nat.sub_add_cancel hq_le_p
      simpa [hx] using (ZMod.natCast_self p)
    calc
      S = arc p q (0 : ZMod p) := hzero
      _ = arc p q ((p - q + q : ℕ) : ZMod p) := by simpa [hcast]
  · let highIdx : Finset ℕ := (Finset.range q).filter (fun i => high i ∈ S)
    have highIdx_nonempty : highIdx.Nonempty := by
      by_contra h
      have hnone : ∀ i < q, high i ∉ S := by
        intro i hi hhi
        have : i ∈ highIdx := by
          simp [highIdx, hi, hhi]
        exact (h ⟨i, this⟩).elim
      exact hhigh_empty hnone
    let k := highIdx.min' highIdx_nonempty
    have hk_lt : k < q := by
      have : k ∈ Finset.range q := (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
      exact Finset.mem_range.mp this
    have hk_mem : high k ∈ S := by
      have : k ∈ highIdx := Finset.min'_mem _ _
      exact (Finset.mem_filter.mp this).2
    have hlow_lt : ∀ i < k, low i ∈ S := by
      intro i hi
      have hnot_high : high i ∉ S := by
        intro hhi
        have : i ∈ highIdx := by
          simp [highIdx, hhi, Finset.mem_range.mpr (lt_trans hi hk_lt)]
        have hmin := Finset.min'_le _ _ this
        omega
      rcases hpair i (lt_trans hi hk_lt) with h | h
      · exact h
      · exact (hnot_high h).elim
    have hhigh_ge : ∀ i < q, k ≤ i → high i ∈ S := by
      have hhigh_ge_aux : ∀ d, k + d < q → high (k + d) ∈ S := by
        intro d hd
        induction d with
        | zero =>
            simpa [Nat.add_zero] using hk_mem
        | succ d ih =>
            have hcurr : high (k + d) ∈ S := ih (by omega)
            have hnext := hhigh_step (k + d) (by omega) hcurr
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
      intro i hi hik
      have hki : k + (i - k) = i := Nat.add_sub_of_le hik
      have hkd : k + (i - k) < q := by simpa [hki] using hi
      have hmem := hhigh_ge_aux (i - k) hkd
      simpa [hki] using hmem
    refine ⟨k, Nat.le_of_lt_succ (Nat.lt_succ_of_lt hk_lt), ?_⟩
    ext v
    constructor
    · intro hv
      by_cases hvlow : v.val < q
      · have hv_eq : v = low v.val := by
          apply ZMod.val_injective
          have hv_lt_p : v.val < p := ZMod.val_lt v
          simp [low]
        have hlow : v.val < k := by
          by_contra hnk
          have hnk' : k ≤ v.val := by omega
          have hhigh := hhigh_ge v.val hvlow hnk'
          have hlow_mem : low v.val ∈ S := by
            have hv' := hv
            rw [hv_eq] at hv'
            simpa using hv'
          exact (hnot_both v.val hvlow) ⟨hlow_mem, hhigh⟩
        refine (mem_arc_iff p q _ v).2 ?_
        refine ⟨q - k + v.val, by omega, ?_⟩
        have hkq : k ≤ q := by omega
        have hq_le_p : q ≤ p := by omega
        have hsum : (p - q + k) + (q - k + v.val) = p + v.val := by
          calc
            (p - q + k) + (q - k + v.val)
                = (p - q) + (k + (q - k)) + v.val := by omega
            _ = (p - q) + q + v.val := by
                have hk : k + (q - k) = q := by
                  have hk' : q - k + k = q := Nat.sub_add_cancel hkq
                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk'
                simpa [hk, Nat.add_assoc]
            _ = p + v.val := by
                have hqq : (p - q) + q = p := Nat.sub_add_cancel hq_le_p
                simpa [hqq, Nat.add_assoc]
        have hsum_cast :
            ((p - q + k : ℕ) : ZMod p) + ((q - k + v.val : ℕ) : ZMod p) =
              ((p + v.val : ℕ) : ZMod p) := by
          calc
            ((p - q + k : ℕ) : ZMod p) + ((q - k + v.val : ℕ) : ZMod p)
                = ((p - q + k + (q - k + v.val) : ℕ) : ZMod p) := by
                    simp [Nat.cast_add, add_assoc]
            _ = ((p + v.val : ℕ) : ZMod p) := by simpa [hsum]
        have hsum_cast' :
            ((p - q + k : ℕ) : ZMod p) + ((q - k + v.val : ℕ) : ZMod p) =
              (v.val : ZMod p) := by
          calc
            _ = ((p + v.val : ℕ) : ZMod p) := hsum_cast
            _ = (v.val : ZMod p) := by
                have hcast : ((p + v.val : ℕ) : ZMod p) =
                    (p : ZMod p) + (v.val : ZMod p) := by
                  simp [Nat.cast_add]
                calc
                  ((p + v.val : ℕ) : ZMod p)
                      = (p : ZMod p) + (v.val : ZMod p) := hcast
                  _ = (v.val : ZMod p) := by
                    simp
        have hv_val_eq : v = (v.val : ZMod p) := by
          simpa [low] using hv_eq
        calc
          v = (v.val : ZMod p) := hv_val_eq
          _ = ((p - q + k : ℕ) : ZMod p) + ((q - k + v.val : ℕ) : ZMod p) := by
              symm
              exact hsum_cast'
      · have hvhigh : v.val > p - q := by
          rcases hval_range v hv with h | h
          · exact (hvlow (by exact h)).elim
          · exact h
        have hv_eq : v = high (v.val - (p - q)) := by
          apply ZMod.val_injective
          have hle : p - q ≤ v.val := Nat.le_of_lt hvhigh
          have hhigh_lt_p : v.val - (p - q) + (p - q) < p := by
            have hsum : v.val - (p - q) + (p - q) = v.val := Nat.sub_add_cancel hle
            simpa [hsum] using (ZMod.val_lt v)
          have hv_val : v.val = v.val - (p - q) + (p - q) := by
            simpa [Nat.sub_add_cancel hle] using (rfl : v.val = v.val)
          calc
            v.val = v.val - (p - q) + (p - q) := hv_val
            _ = (high (v.val - (p - q))).val := by
              simp [high, ZMod.val_natCast_of_lt hhigh_lt_p, -Nat.cast_add]
        have hidx_ge : k ≤ v.val - (p - q) := by
          by_contra hnk
          have hlt : v.val - (p - q) < k := Nat.lt_of_not_ge hnk
          have hlow := hlow_lt (v.val - (p - q)) hlt
          have hidx_lt : v.val - (p - q) < q := by
            have hle : p - q ≤ v.val := Nat.le_of_lt hvhigh
            have hv_lt_p : v.val < p := ZMod.val_lt v
            have hq_le_p : q ≤ p := by omega
            have hlt' : v.val < q + (p - q) := by
              have hsum : q + (p - q) = p := by
                calc
                  q + (p - q) = (p - q) + q := by ac_rfl
                  _ = p := Nat.sub_add_cancel hq_le_p
              simpa [hsum] using hv_lt_p
            exact (Nat.sub_lt_iff_lt_add hle).2 hlt'
          have hhigh_mem : high (v.val - (p - q)) ∈ S := by
            have hv' := hv
            rw [hv_eq] at hv'
            simpa using hv'
          exact (hnot_both _ hidx_lt) ⟨hlow, hhigh_mem⟩
        refine (mem_arc_iff p q _ v).2 ?_
        have hidx_lt' : v.val - (p - q) < q := by
          have := hidx_lt v hv
          simpa [idx, hvlow] using this
        have hlt : v.val - (p - q) - k < q := by
          exact lt_of_le_of_lt (Nat.sub_le _ _) hidx_lt'
        refine ⟨v.val - (p - q) - k, hlt, ?_⟩
        have hk_le : k ≤ v.val - (p - q) := hidx_ge
        have hsum : (p - q + k) + (v.val - (p - q) - k) = v.val := by
          calc
            (p - q + k) + (v.val - (p - q) - k)
                = (p - q) + (k + (v.val - (p - q) - k)) := by omega
            _ = (p - q) + (v.val - (p - q)) := by
                have hk : k + (v.val - (p - q) - k) = v.val - (p - q) :=
                  Nat.add_sub_of_le hk_le
                simpa [hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = v.val := by omega
        have hsum_cast :
            ((p - q + k : ℕ) : ZMod p) + ((v.val - (p - q) - k : ℕ) : ZMod p) =
              (v.val : ZMod p) := by
          calc
            ((p - q + k : ℕ) : ZMod p) + ((v.val - (p - q) - k : ℕ) : ZMod p)
                = ((p - q + k + (v.val - (p - q) - k) : ℕ) : ZMod p) := by
                    simp [Nat.cast_add, add_assoc]
            _ = ((v.val : ℕ) : ZMod p) := by simpa [hsum]
        have hv_cast : high (v.val - (p - q)) = (v.val : ZMod p) := by
          have hle : p - q ≤ v.val := Nat.le_of_lt hvhigh
          have hv_val : v.val = v.val - (p - q) + (p - q) :=
            (Nat.sub_add_cancel hle).symm
          calc
            high (v.val - (p - q)) =
                ((v.val - (p - q) + (p - q) : ℕ) : ZMod p) := rfl
            _ = (v.val : ZMod p) := by
              exact (congrArg (fun t : ℕ => (t : ZMod p)) hv_val).symm
        have hv_val_eq : v = (v.val : ZMod p) := by
          calc
            v = high (v.val - (p - q)) := hv_eq
            _ = (v.val : ZMod p) := hv_cast
        calc
          v = (v.val : ZMod p) := hv_val_eq
          _ = ((p - q + k : ℕ) : ZMod p) + ((v.val - (p - q) - k : ℕ) : ZMod p) := by
              symm
              exact hsum_cast
    · intro hv
      rcases (mem_arc_iff p q _ v).1 hv with ⟨i, hi, hv_eq⟩
      by_cases hi' : i < q - k
      · have : high (k + i) ∈ S := by
          have hki : k + i < q := by omega
          exact hhigh_ge (k + i) hki (by omega)
        simpa [high, hv_eq, add_assoc, add_left_comm, add_comm] using this
      · have : low (i - (q - k)) ∈ S := by
          have hilow : i - (q - k) < k := by omega
          exact hlow_lt (i - (q - k)) hilow
        have hkq : k ≤ q := by omega
        have hiq : q - k ≤ i := by omega
        have hsum : (p - q + k) + i = p + (i - (q - k)) := by
          calc
            (p - q + k) + i
                = (p - q + k) + ((q - k) + (i - (q - k))) := by
                    have := Nat.add_sub_of_le hiq
                    simpa [Nat.add_assoc] using this.symm
            _ = (p - q + k + (q - k)) + (i - (q - k)) := by omega
            _ = (p - q + q) + (i - (q - k)) := by
                have hk : k + (q - k) = q := by
                  have hk' : q - k + k = q := Nat.sub_add_cancel hkq
                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk'
                simpa [hk, Nat.add_assoc]
            _ = p + (i - (q - k)) := by
                have hq_le_p : q ≤ p := by omega
                simpa [Nat.sub_add_cancel hq_le_p, Nat.add_assoc]
        have hv_eq' : v = low (i - (q - k)) := by
          calc
            v = ((p - q + k : ℕ) : ZMod p) + (i : ZMod p) := by
                simpa [hv_eq]
            _ = ((p - q + k + i : ℕ) : ZMod p) := by
                simp [Nat.cast_add, add_assoc]
            _ = ((p + (i - (q - k)) : ℕ) : ZMod p) := by
                simpa [hsum, Nat.cast_add]
            _ = ((i - (q - k) : ℕ) : ZMod p) := by
                simp [Nat.cast_add]
            _ = low (i - (q - k)) := by
                simp [low]
        simpa [hv_eq'] using this

lemma two_mul_add_one_le_of_coprime (p q : ℕ) (hq : 2 ≤ q)
    (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q) :
    2 * q + 1 ≤ p := by
  have hne : p ≠ 2 * q := by
    intro hpeq
    have hdiv : q ∣ p := by
      refine ⟨2, ?_⟩
      simp [hpeq, Nat.mul_comm]
    have hgcd : Nat.gcd p q = q := Nat.gcd_eq_right hdiv
    have hgcd' : Nat.gcd p q = 1 := (Nat.coprime_iff_gcd_eq_one.mp hcoprime)
    have hq1 : q = 1 := by simpa [hgcd] using hgcd'
    omega
  have hlt : 2 * q < p := lt_of_le_of_ne h2q (by simpa [eq_comm] using hne)
  exact Nat.succ_le_of_lt hlt

lemma clique_eq_arc (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (S : Finset (ZMod p))
    (hclique : (fractionGraph p q).IsClique S) (hcard : S.card = q) :
    ∃ x : ZMod p, S = arc p q x := by
  classical
  have h2q' : 2 * q + 1 ≤ p := two_mul_add_one_le_of_coprime p q hq h2q hcoprime
  have hq_pos : 0 < q := by omega
  have hS_nonempty : S.Nonempty := by
    have : S.card ≠ 0 := by simpa [hcard] using (ne_of_gt hq_pos)
    exact Finset.card_ne_zero.mp this
  obtain ⟨v0, hv0⟩ := hS_nonempty
  let S' : Finset (ZMod p) := S.image (fun v => v - v0)
  have hclique' : (fractionGraph p q).IsClique S' := by
    classical
    rw [SimpleGraph.isClique_iff] at hclique ⊢
    intro u hu v hv huv
    rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
    rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
    have huv' : u' ≠ v' := by
      intro h
      apply huv
      simpa [h]
    have hadj := hclique hu' hv' huv'
    have hadj' := (fractionGraph_adj_add_left p q (-v0) u' v').2 hadj
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hadj'
  have hcard' : S'.card = q := by
    have hcard'' : S'.card = S.card := by
      refine Finset.card_image_of_injective _ ?_
      intro u v h
      have h' := congrArg (fun t => t + v0) h
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
    simpa [hcard] using hcard''
  have h0 : (0 : ZMod p) ∈ S' := by
    refine Finset.mem_image.mpr ?_
    exact ⟨v0, hv0, by simp⟩
  rcases clique_eq_arc_of_zero p q hq h2q' S' hclique' hcard' h0 with ⟨k, hk, hS'⟩
  have hS_img : S = (S'.image (fun v => v + v0)) := by
    ext v
    constructor
    · intro hv
      refine Finset.mem_image.mpr ?_
      refine ⟨v - v0, ?_, by abel⟩
      exact Finset.mem_image.mpr ⟨v, hv, by simp⟩
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, hw_eq⟩
      rcases Finset.mem_image.mp hw with ⟨u, hu, hwu⟩
      have hv' : v = u := by
        calc
          v = w + v0 := by simpa [hw_eq]
          _ = u - v0 + v0 := by simpa [hwu]
          _ = u := by abel
      simpa [hv'] using hu
  have hS_arc :
      S = arc p q ((p - q + k : ℕ) + v0) := by
    calc
      S = (S'.image (fun v => v + v0)) := hS_img
      _ = (arc p q (p - q + k : ℕ)).image (fun v => v + v0) := by simpa [hS']
      _ = arc p q ((p - q + k : ℕ) + v0) := by
            symm
            exact arc_add_left p q v0 (p - q + k : ℕ)
  exact ⟨(p - q + k : ℕ) + v0, by simpa [add_comm, add_left_comm, add_assoc] using hS_arc⟩

lemma arc_eq_iff (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (x y : ZMod p) :
    arc p q x = arc p q y ↔ x = y := by
  classical
  constructor
  · intro hxy
    have hq_pos : 0 < q := by omega
    have hx : x ∈ arc p q x := by
      exact (mem_arc_iff p q x x).2 ⟨0, hq_pos, by simp⟩
    have hy : y ∈ arc p q y := by
      exact (mem_arc_iff p q y y).2 ⟨0, hq_pos, by simp⟩
    have hx' : x ∈ arc p q y := by simpa [hxy] using hx
    have hy' : y ∈ arc p q x := by simpa [hxy] using hy
    rcases (mem_arc_iff p q y x).1 hx' with ⟨i, hi, hxi⟩
    rcases (mem_arc_iff p q x y).1 hy' with ⟨j, hj, hyj⟩
    have hsum : ((i + j : ℕ) : ZMod p) = 0 := by
      have : x = x + ((i + j : ℕ) : ZMod p) := by
        calc
          x = y + (i : ZMod p) := hxi
          _ = (x + (j : ZMod p)) + (i : ZMod p) := by simpa [hyj, add_assoc]
          _ = x + ((j + i : ℕ) : ZMod p) := by
                simp [Nat.cast_add, add_assoc]
          _ = x + ((i + j : ℕ) : ZMod p) := by
                simp [Nat.add_comm]
      have h' : x + ((i + j : ℕ) : ZMod p) = x + 0 := by
        simpa [add_comm] using this
      exact add_left_cancel h'
    have hij_lt : i + j < p := by omega
    have hsum_nat : i + j = 0 := by
      have hdiv : p ∣ i + j :=
        (ZMod.natCast_eq_zero_iff (i + j) p).1 hsum
      exact Nat.eq_zero_of_dvd_of_lt hdiv hij_lt
    rcases Nat.add_eq_zero_iff.mp hsum_nat with ⟨hi0, hj0⟩
    have hx0 : x = y := by
      calc
        x = y + (i : ZMod p) := hxi
        _ = y := by simpa [hi0]
    exact hx0
  · intro hxy
    simpa [hxy]

lemma arc_inter_card_translate (p q : ℕ) [NeZero p] (x y c : ZMod p) :
    (arc p q (x + c) ∩ arc p q (y + c)).card = (arc p q x ∩ arc p q y).card := by
  classical
  have h_inj : Function.Injective (fun v : ZMod p => v + c) := by
    intro u v h
    exact add_right_cancel_iff.mp h
  have h1 := arc_add_left p q c x
  have h2 := arc_add_left p q c y
  calc
    (arc p q (x + c) ∩ arc p q (y + c)).card
        = ((arc p q x).image (fun v => v + c) ∩ (arc p q y).image (fun v => v + c)).card := by
            simpa [h1, h2]
    _ = ((arc p q x ∩ arc p q y).image (fun v => v + c)).card := by
            have h := (Finset.image_inter (arc p q x) (arc p q y) h_inj)
            simpa [h] using rfl
    _ = (arc p q x ∩ arc p q y).card := by
            exact Finset.card_image_of_injective _ h_inj

lemma arc_inter_card_zero_eq_q_sub_one (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (k : ℕ) (hk : k < p) :
    (arc p q 0 ∩ arc p q (k : ZMod p)).card = q - 1 ↔ k = 1 ∨ k = p - 1 := by
  classical
  have hq_pos : 0 < q := by omega
  have hq_le_p : q ≤ p := by omega
  by_cases hk0 : k = 0
  · subst hk0
    have hcard : (arc p q 0 ∩ arc p q ((0 : ℕ) : ZMod p)).card = q := by
      have := arc_inter_card p q h2q (0 : ZMod p) 0 (by omega)
      simpa using this
    constructor
    · intro h
      have h' : (arc p q 0 ∩ arc p q ((0 : ℕ) : ZMod p)).card = q - 1 := by
        simpa only using h
      have : q = q - 1 := by simpa only [hcard] using h'
      omega
    · intro h
      rcases h with h | h
      · omega
      · omega
  by_cases hk_lt_q : k < q
  · have hcard : (arc p q 0 ∩ arc p q (k : ZMod p)).card = q - k := by
      have := arc_inter_card p q h2q (0 : ZMod p) k hk_lt_q
      simpa using this
    constructor
    · intro h
      have : q - k = q - 1 := by simpa [hcard] using h
      have hk1 : k = 1 := by omega
      exact Or.inl hk1
    · intro hk1
      rcases hk1 with rfl | hk1
      · simpa using hcard
      · omega
  have hk_ge_q : q ≤ k := Nat.le_of_not_lt hk_lt_q
  by_cases hk_le_pq : k ≤ p - q
  · have hcard : (arc p q 0 ∩ arc p q (k : ZMod p)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      rcases Finset.mem_inter.mp hv with ⟨hv0, hvk⟩
      rcases (mem_arc_iff p q 0 v).1 hv0 with ⟨i, hi, hvi⟩
      rcases (mem_arc_iff p q (k : ZMod p) v).1 hvk with ⟨j, hj, hvj⟩
      have hi_lt_p : i < p := lt_of_lt_of_le hi hq_le_p
      have hkj_lt_p : k + j < p := by omega
      have hvi' : v = (i : ZMod p) := by simpa using hvi
      have hkj_cast : ((k + j : ℕ) : ZMod p) = (k : ZMod p) + (j : ZMod p) := by
        simpa using (Nat.cast_add (α := ZMod p) k j)
      have hvj' : v = ((k + j : ℕ) : ZMod p) := by
        calc
          v = (k : ZMod p) + (j : ZMod p) := hvj
          _ = ((k + j : ℕ) : ZMod p) := hkj_cast.symm
      have hval_i : v.val = i := by
        have hval := congrArg ZMod.val hvi'
        simpa [ZMod.val_natCast_of_lt hi_lt_p] using hval
      have hval_kj : v.val = k + j := by
        have hval := congrArg ZMod.val hvj'
        simpa only [ZMod.val_natCast_of_lt hkj_lt_p] using hval
      have hnat : i = k + j := by
        calc
          i = v.val := by symm; exact hval_i
          _ = k + j := hval_kj
      have hle : q ≤ i := by
        have hk_le : q ≤ k := hk_ge_q
        have hk_le_kj : k ≤ k + j := Nat.le_add_right _ _
        have hk_le_i : k ≤ i := by simpa [hnat] using hk_le_kj
        exact le_trans hk_le hk_le_i
      have : False := by omega
      exact this.elim
    constructor
    · intro h
      have : 0 = q - 1 := by simpa [hcard] using h
      omega
    · intro h
      rcases h with h | h
      · omega
      · omega
  have hk_gt_pq : p - q < k := lt_of_not_ge hk_le_pq
  set s : ℕ := p - k
  have hs_pos : 0 < s := by omega
  have hs_lt_q : s < q := by omega
  have hk_eq : k = p - s := by
    dsimp [s]
    omega
  have hcard : (arc p q 0 ∩ arc p q (k : ZMod p)).card = q - s := by
    have hcard' := arc_inter_card p q h2q ((p - s : ℕ) : ZMod p) s hs_lt_q
    have hx : ((p - s : ℕ) : ZMod p) + (s : ZMod p) = 0 := by
      calc
        ((p - s : ℕ) : ZMod p) + (s : ZMod p)
            = ((p - s + s : ℕ) : ZMod p) := by simp [Nat.cast_add]
        _ = ((p : ℕ) : ZMod p) := by
              have : p - s + s = p := by omega
              simpa [this]
        _ = 0 := by simp
    have hcard'' : (arc p q ((p - s : ℕ) : ZMod p) ∩ arc p q 0).card = q - s := by
      simpa [hx] using hcard'
    have hk_eq' : (k : ZMod p) = ((p - s : ℕ) : ZMod p) := by
      simpa [hk_eq]
    simpa [hk_eq', Finset.inter_comm] using hcard''
  constructor
  · intro h
    have : q - s = q - 1 := by simpa [hcard] using h
    have hs1 : s = 1 := by omega
    have hk1 : k = p - 1 := by simpa [hk_eq, hs1]
    exact Or.inr hk1
  · intro hk1
    rcases hk1 with hk1 | hk1
    · omega
    · have hs1 : s = 1 := by omega
      simpa [hcard, hs1] using (rfl : q - 1 = q - 1)

lemma arc_one_eq_singleton (p : ℕ) [NeZero p] (x : ZMod p) :
    arc p 1 x = {x} := by
  classical
  ext v
  constructor
  · intro hv
    rcases (mem_arc_iff p 1 x v).1 hv with ⟨i, hi, rfl⟩
    have hi0 : i = 0 := by omega
    simp [hi0]
  · intro hv
    rcases Finset.mem_singleton.mp hv with rfl
    exact (mem_arc_iff p 1 v v).2 ⟨0, by omega, by simp⟩

lemma arc_inter_card_eq_q_sub_one_iff (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (x y : ZMod p) :
    (arc p q x ∩ arc p q y).card = q - 1 ↔ y = x + 1 ∨ y = x - 1 := by
  classical
  have htrans := arc_inter_card_translate p q x y (-x)
  have htrans' :
      (arc p q 0 ∩ arc p q (y - x)).card = (arc p q x ∩ arc p q y).card := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htrans
  set k : ℕ := (y - x).val
  have hk : k < p := by simpa [k] using (ZMod.val_lt (y - x))
  have hk_eq : (k : ZMod p) = y - x := by
    simpa [k] using (ZMod.natCast_zmod_val (y - x))
  have hzero :
      (arc p q 0 ∩ arc p q (y - x)).card = q - 1 ↔ k = 1 ∨ k = p - 1 := by
    simpa [hk_eq] using (arc_inter_card_zero_eq_q_sub_one p q hq h2q k hk)
  constructor
  · intro h
    have hk' : k = 1 ∨ k = p - 1 := hzero.1 (by simpa [htrans'] using h)
    rcases hk' with hk1 | hk1
    · have hdiff : y - x = (1 : ZMod p) := by
        have : y - x = (k : ZMod p) := hk_eq.symm
        simpa [hk1] using this
      left
      calc
        y = (y - x) + x := by abel
        _ = 1 + x := by simpa [hdiff]
        _ = x + 1 := by abel
    · have hdiff : y - x = ((p - 1 : ℕ) : ZMod p) := by
        have : y - x = (k : ZMod p) := hk_eq.symm
        simpa [hk1] using this
      have hneg : ((p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
        have hsum : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
          have h : p - 1 + 1 = p := by omega
          calc
            ((p - 1 : ℕ) : ZMod p) + 1 = ((p - 1 + 1 : ℕ) : ZMod p) := by
              simp [Nat.cast_add]
            _ = ((p : ℕ) : ZMod p) := by simpa [h]
            _ = 0 := by simp
        simpa using (eq_neg_of_add_eq_zero_left hsum)
      right
      calc
        y = (y - x) + x := by abel
        _ = (-1) + x := by simpa [hdiff, hneg]
        _ = x - 1 := by abel
  · intro h
    rcases h with h | h
    · have hdiff : y - x = (1 : ZMod p) := by
        calc
          y - x = (x + 1) - x := by simpa [h]
          _ = 1 := by abel
      have hk1 : k = 1 := by
        have hval := congrArg ZMod.val hdiff
        have h1 : (1 : ZMod p).val = 1 := by
          have h1' : (1 : ℕ) < p := by omega
          change (ZMod.val (1 : ZMod p) = 1)
          simpa using (ZMod.val_natCast_of_lt (n := p) (a := 1) h1')
        simpa [k, h1] using hval
      exact (htrans'.symm ▸ hzero.2 (Or.inl hk1))
    · have hdiff : y - x = (-1 : ZMod p) := by
        calc
          y - x = (x - 1) - x := by simpa [h]
          _ = -1 := by abel
      have hneg : ((p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
        have hsum : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
          have h : p - 1 + 1 = p := by omega
          calc
            ((p - 1 : ℕ) : ZMod p) + 1 = ((p - 1 + 1 : ℕ) : ZMod p) := by
              simp [Nat.cast_add]
            _ = ((p : ℕ) : ZMod p) := by simpa [h]
            _ = 0 := by simp
        simpa using (eq_neg_of_add_eq_zero_left hsum)
      have hk1 : k = p - 1 := by
        have hdiff' : y - x = ((p - 1 : ℕ) : ZMod p) := by
          simpa [hneg] using hdiff
        have hval := congrArg ZMod.val hdiff'
        have hp1 : (p - 1 : ℕ) < p := by omega
        simpa [k, ZMod.val_natCast_of_lt hp1] using hval
      exact (htrans'.symm ▸ hzero.2 (Or.inr hk1))

noncomputable def nonAdjFinset (p q : ℕ) [NeZero p] (u : ZMod p) :
    Finset (ZMod p) :=
by
  classical
  exact (Finset.univ.filter fun v => v ≠ u ∧ ¬(fractionGraph p q).Adj u v)

lemma nonAdjFinset_translate (p q : ℕ) [NeZero p] (c u : ZMod p) :
    (nonAdjFinset p q u).image (fun v => v + c) = nonAdjFinset p q (u + c) := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    have hw' : w ≠ u ∧ ¬(fractionGraph p q).Adj u w := by
      simpa [nonAdjFinset] using hw
    rcases hw' with ⟨hw_ne, hw_nonadj⟩
    have hne : w + c ≠ u + c := by
      intro h_eq
      apply hw_ne
      exact (add_right_cancel_iff.mp h_eq)
    have hnonadj : ¬(fractionGraph p q).Adj (u + c) (w + c) := by
      intro hadj
      apply hw_nonadj
      have hadj' : (fractionGraph p q).Adj (c + u) (c + w) := by
        simpa [add_comm, add_left_comm, add_assoc] using hadj
      exact (fractionGraph_adj_add_left p q c u w).1 hadj'
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨hne, hnonadj⟩
  · intro hv
    refine Finset.mem_image.mpr ?_
    refine ⟨v - c, ?_, by abel⟩
    have hv' : v ≠ u + c ∧ ¬(fractionGraph p q).Adj (u + c) v := by
      simpa [nonAdjFinset] using hv
    rcases hv' with ⟨hv_ne, hv_nonadj⟩
    have hne : v - c ≠ u := by
      intro h_eq
      apply hv_ne
      have : v = u + c := by
        calc
          v = v - c + c := by abel
          _ = u + c := by simp [h_eq]
      simp [this]
    have hnonadj : ¬(fractionGraph p q).Adj u (v - c) := by
      intro hadj
      apply hv_nonadj
      have hadj' : (fractionGraph p q).Adj (c + u) (c + (v - c)) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          ((fractionGraph_adj_add_left p q c u (v - c)).2 hadj)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hadj'
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨hne, hnonadj⟩

/-- Helper: Corestricting a cohomomorphism to its image gives a cohomomorphism
    to the induced subgraph on the image. -/
theorem isCohom_corestrict {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : IsCohom G H f) (S : Set W) (hS : ∀ v, f v ∈ S) :
    IsCohom G (H.induce S) (fun v => ⟨f v, hS v⟩) := by
  intro u v huv hnadj
  -- (H.induce S).Adj a b ↔ H.Adj ↑a ↑b is definitional (induce_adj is Iff.rfl)
  -- So hnadj : ¬(H.induce S).Adj ⟨f u, _⟩ ⟨f v, _⟩ is definitionally ¬H.Adj (f u) (f v)
  have hresult := hf u v huv hnadj
  constructor
  · intro heq
    exact hresult.1 (Subtype.ext_iff.mp heq)
  · exact hresult.2

/-- If S ⊆ T, then the inclusion map gives a cohomomorphism from G.induce S to G.induce T. -/
theorem induced_subset_cohom {V : Type*} (G : SimpleGraph V) (S T : Set V) (hST : S ⊆ T) :
    Cohom (G.induce S) (G.induce T) := by
  -- The map is the set inclusion: s ↦ ⟨s.val, hST s.property⟩
  refine ⟨fun s => ⟨s.val, hST s.property⟩, fun u v huv hnadj => ?_⟩
  constructor
  · intro heq
    have h := Subtype.mk.inj heq
    exact huv (Subtype.ext h)
  · -- hnadj : ¬(G.induce T).Adj ... means ¬G.Adj u.val v.val
    simp only [SimpleGraph.induce_adj] at hnadj ⊢
    intro hadj
    exact hnadj hadj

/-- Lemma 5.1: For coprime p/q ≥ 2 with q ≥ 2, any self-cohomomorphism of E_{p/q}
    is an isomorphism (i.e., E_{p/q}^c is a core).

    Proof: If f is not surjective, then Im(f) is a proper subset.
    There exists v ∉ Im(f), so Im(f) ⊆ V \ {v}.
    By vertex removal, E_{p/q}[V \ {v}] ≃ E_{p'/q'} with p'/q' < p/q.
    The composition gives a cohomomorphism E_{p/q} → E_{p'/q'}.
    By ordering, p/q ≤ p'/q', contradiction with p'/q' < p/q.

    Note: Requires q ≥ 2 since for q = 1 (edgeless graph), any function is
    a cohomomorphism, including non-bijective ones. -/
theorem fractionGraph_selfCohom_isIso (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : IsCohom (fractionGraph p q) (fractionGraph p q) f) :
    Function.Bijective f := by
  -- For finite types, surjectivity ⟺ bijectivity
  -- We prove surjectivity by contradiction
  rw [← Finite.surjective_iff_bijective]
  by_contra hnsurj
  -- f is not surjective, so there exists v ∉ Im(f)
  simp only [Function.Surjective, not_forall, not_exists] at hnsurj
  obtain ⟨v, hv⟩ := hnsurj
  -- Let S = {x : ZMod p | x ≠ v}
  set S : Set (ZMod p) := {x | x ≠ v} with hS_def
  -- Im(f) ⊆ S
  have hfS : ∀ u, f u ∈ S := fun u => by
    simp only [hS_def, Set.mem_setOf_eq]
    exact hv u
  -- The corestriction f' : E_{p/q} → E_{p/q}[S] is a cohomomorphism
  have hf' : IsCohom (fractionGraph p q) ((fractionGraph p q).induce S) (fun u => ⟨f u, hfS u⟩) :=
    isCohom_corestrict f hf S hfS
  -- By fractionGraph_remove_vertex_equiv, E_{p/q}[S] ~ E_{p'/q'} (bidirectional cohomomorphisms)
  have hremove := fractionGraph_remove_vertex_equiv p q hq h2q hcoprime v
  obtain ⟨p', q', hp'_pos, hq'_pos, hp'_lt, hq'_lt, heq, hcohom_fwd, _hcohom_bwd⟩ := hremove
  -- Get 2 * q' ≤ p' from the Stern-Brocot properties
  have h2q' : 2 * q' ≤ p' := by
    -- From p * q' - q * p' = 1 and 2q ≤ p, we get 2q * q' ≤ p * q' = q * p' + 1.
    -- Case q = 1: q' < q = 1 contradicts q' > 0.
    -- Case q ≥ 2: 2q * q' ≤ q * p' + 1 < q * (p' + 1), so 2 * q' < p' + 1.
    have h1 : p * q' = q * p' + 1 := by omega
    have h2 : 2 * q * q' ≤ p * q' := Nat.mul_le_mul_right q' h2q
    rw [h1] at h2
    by_cases hq_eq_1 : q = 1
    · -- q = 1: q' < q = 1 with q' > 0 is impossible
      omega
    · -- q ≥ 2: 2q * q' ≤ q * p' + 1 < q * p' + q = q * (p' + 1), so 2 * q' < p' + 1
      have hq_ge_2 : 2 ≤ q := by omega
      have h3 : q * (2 * q') < q * (p' + 1) := by
        calc q * (2 * q') = 2 * q * q' := by ring
          _ ≤ q * p' + 1 := h2
          _ < q * p' + q := by omega
          _ = q * (p' + 1) := by ring
      have h4 : 2 * q' < p' + 1 := Nat.lt_of_mul_lt_mul_left h3
      omega
  haveI : NeZero p' := ⟨Nat.pos_iff_ne_zero.mp hp'_pos⟩
  -- The cohomomorphism E_{p/q}[S] → E_{p'/q'} composed with f': E_{p/q} → E_{p/q}[S]
  -- gives E_{p/q} → E_{p'/q'}
  have hcohom : Cohom (fractionGraph p q) (fractionGraph p' q') := by
    -- Get the cohomomorphism function from hcohom_fwd
    obtain ⟨φ, hφ⟩ := hcohom_fwd
    -- Define the composite map: g u = φ ⟨f u, hfS u⟩
    let g : ZMod p → ZMod p' := fun u => φ ⟨f u, hfS u⟩
    refine ⟨g, fun u w huw hnadj => ?_⟩
    -- hnadj : ¬(fractionGraph p q).Adj u w (source non-adjacency)
    -- Apply hf' to get induced subgraph non-adjacency
    have hf'_result := hf' u w huw hnadj
    -- hf'_result : ⟨f u, _⟩ ≠ ⟨f w, _⟩ ∧ ¬((fractionGraph p q).induce S).Adj ⟨f u, _⟩ ⟨f w, _⟩
    -- Apply the cohomomorphism property of φ
    exact hφ ⟨f u, hfS u⟩ ⟨f w, hfS w⟩ hf'_result.1 hf'_result.2
  -- By fractionGraph_ordering_reverse: Cohom E_{p/q} E_{p'/q'} → p/q ≤ p'/q'
  have hq_pos : 0 < q := by omega
  have hle := fractionGraph_ordering_reverse p q p' q' hq_pos hq'_pos h2q h2q' hcohom
  -- But by sternBrocot_predecessor_lt: p'/q' < p/q
  have hlt := sternBrocot_predecessor_lt p q p' q' hp'_lt hq'_lt hq'_pos heq
  -- Contradiction
  exact (lt_irrefl _ (lt_of_lt_of_le hlt hle))

/-- Lemma 5.2: For coprime p/q ≥ 2 with q ≥ 2, any self-isomorphism of E_{p/q}
    has the form f(x) = a + x or f(x) = a - x for some a ∈ ℤ_p.

    Proof outline:
    1. Maximum cliques in E_{p/q} are exactly the q-intervals {x, x+1, ..., x+(q-1)} for x ∈ ZMod p
       (there are p such intervals, each of size q = clique number)
    2. Any graph isomorphism maps maximum cliques to maximum cliques bijectively
    3. Two intervals I_x = {x, ..., x+(q-1)} and I_y = {y, ..., y+(q-1)} share exactly q-1 vertices
       iff |x - y| = 1 (mod p). This defines a cycle graph C_p on the set of intervals.
    4. The bijection on intervals induced by f is an automorphism of C_p
    5. Automorphisms of C_p are rotations (I_x ↦ I_{x+a}) or reflections (I_x ↦ I_{a-x})
    6. For rotations: f(I_x) = I_{x+a} implies f({x,...,x+q-1}) = {x+a,...,x+a+q-1}
       Since f is a cohom and bijection, f(k) = k + a for all k
    7. For reflections: similarly f(k) = a - k for all k -/
theorem fractionGraph_selfIso_form (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : Function.Bijective f)
    (hf_cohom : IsCohom (fractionGraph p q) (fractionGraph p q) f) :
    ∃ a : ZMod p, (∀ x, f x = a + x) ∨ (∀ x, f x = a - x) := by
  classical
  have hf_inj : Function.Injective f := hf.1
  -- Translate-invariance of non-neighbor sets (cardinality only).
  have hnonadj_card : ∀ u, (nonAdjFinset p q u).card = (nonAdjFinset p q 0).card := by
    intro u
    have htrans := nonAdjFinset_translate p q u 0
    have hcard_image :
        ((nonAdjFinset p q 0).image (fun v => v + u)).card = (nonAdjFinset p q 0).card := by
      refine Finset.card_image_of_injective _ ?_
      intro x y hxy
      exact (add_right_cancel_iff.mp hxy)
    -- use the translation identity to rewrite
    have hcard_trans :
        ((nonAdjFinset p q 0).image (fun v => v + u)).card = (nonAdjFinset p q u).card := by
      simpa [zero_add] using (congrArg Finset.card htrans)
    calc
      (nonAdjFinset p q u).card
          = ((nonAdjFinset p q 0).image (fun v => v + u)).card := hcard_trans.symm
      _ = (nonAdjFinset p q 0).card := hcard_image
  -- The image of the non-neighbor set is exactly the non-neighbor set.
  have hnonadj_image_eq : ∀ u, (nonAdjFinset p q u).image f = nonAdjFinset p q (f u) := by
    intro u
    have hsubset : (nonAdjFinset p q u).image f ⊆ nonAdjFinset p q (f u) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      have hw' : w ≠ u ∧ ¬(fractionGraph p q).Adj u w := by
        simpa [nonAdjFinset] using hw
      rcases hw' with ⟨hw_ne, hw_nonadj⟩
      have hne : u ≠ w := by simpa [ne_comm] using hw_ne
      have hco := hf_cohom u w hne hw_nonadj
      have hco' : f w ≠ f u ∧ ¬(fractionGraph p q).Adj (f u) (f w) := by
        exact ⟨by simpa [ne_comm] using hco.1, hco.2⟩
      simpa [nonAdjFinset] using hco'
    have hcard_image :
        ((nonAdjFinset p q u).image f).card = (nonAdjFinset p q u).card := by
      simpa using (Finset.card_image_of_injective _ hf_inj)
    have hcard_eq :
        ((nonAdjFinset p q u).image f).card = (nonAdjFinset p q (f u)).card := by
      calc
        ((nonAdjFinset p q u).image f).card
            = (nonAdjFinset p q u).card := hcard_image
        _ = (nonAdjFinset p q (f u)).card := by
              calc
                (nonAdjFinset p q u).card
                    = (nonAdjFinset p q 0).card := hnonadj_card u
                _ = (nonAdjFinset p q (f u)).card := (hnonadj_card (f u)).symm
    have hcard_le : (nonAdjFinset p q (f u)).card ≤ ((nonAdjFinset p q u).image f).card :=
      hcard_eq.symm.le
    exact Finset.eq_of_subset_of_card_le hsubset hcard_le
  -- f preserves adjacency since it is bijective and preserves non-neighbors.
  have hf_adj : ∀ u v, (fractionGraph p q).Adj u v → (fractionGraph p q).Adj (f u) (f v) := by
    intro u v huv
    by_contra hnonadj
    have hne_uv : u ≠ v := by
      have h' : u ≠ v ∧ FractionGraphBasic.distMod p u v < q := by
        simpa [fractionGraph] using huv
      exact h'.1
    have hne_f : f v ≠ f u := by
      intro h_eq
      exact hne_uv (hf_inj h_eq).symm
    have hfv_in : f v ∈ nonAdjFinset p q (f u) := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨hne_f, hnonadj⟩
    have himage_eq := hnonadj_image_eq u
    have hfv_in' : f v ∈ (nonAdjFinset p q u).image f := by
      simpa [himage_eq] using hfv_in
    rcases Finset.mem_image.mp hfv_in' with ⟨w, hw, hw_eq⟩
    have hw_eq' : w = v := hf_inj hw_eq
    have hw_nonadj : ¬(fractionGraph p q).Adj u v := by
      have hw' : ¬(fractionGraph p q).Adj u w := by
        have hw' : w ≠ u ∧ ¬(fractionGraph p q).Adj u w := by
          simpa [nonAdjFinset] using hw
        exact hw'.2
      simpa [hw_eq'] using hw'
    exact hw_nonadj huv
  -- Map each arc to an arc.
  have hq_pos : 0 < q := by omega
  have harc_clique : ∀ x, (fractionGraph p q).IsClique (arc p q x) := by
    intro x
    exact arc_isClique p q hq_pos h2q x
  have harc_card : ∀ x, (arc p q x).card = q := by
    intro x
    exact arc_card p q h2q x
  have harc_image : ∀ x, ∃ y, (arc p q x).image f = arc p q y := by
    intro x
    have hclique_image : (fractionGraph p q).IsClique ((arc p q x).image f) := by
      classical
      rw [SimpleGraph.isClique_iff]
      intro u hu v hv huv
      have hu' : u ∈ (arc p q x).image f := by
        exact hu
      have hv' : v ∈ (arc p q x).image f := by
        exact hv
      rcases Finset.mem_image.mp hu' with ⟨u', hu_mem, rfl⟩
      rcases Finset.mem_image.mp hv' with ⟨v', hv_mem, rfl⟩
      have huv' : u' ≠ v' := by
        intro h_eq
        apply huv
        simp [h_eq]
      have hu'' : u' ∈ (arc p q x : Set (ZMod p)) := by
        exact hu_mem
      have hv'' : v' ∈ (arc p q x : Set (ZMod p)) := by
        exact hv_mem
      have hadj := (harc_clique x) hu'' hv'' huv'
      exact hf_adj _ _ hadj
    have hcard_image : ((arc p q x).image f).card = q := by
      have hcard' : ((arc p q x).image f).card = (arc p q x).card :=
        Finset.card_image_of_injective _ hf_inj
      simpa [harc_card x] using hcard'
    exact clique_eq_arc p q hq h2q hcoprime ((arc p q x).image f) hclique_image hcard_image
  classical
  choose g hg_spec using harc_image
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have himg :
        (arc p q x).image f = (arc p q y).image f := by
      simpa [hg_spec x, hg_spec y, hxy] using rfl
    have hxy' : arc p q x = arc p q y :=
      (Finset.image_injective hf_inj) himg
    exact (arc_eq_iff p q hq h2q _ _).1 hxy'
  -- g preserves adjacency of consecutive arcs
  have hg_adj : ∀ x, g (x + 1) = g x + 1 ∨ g (x + 1) = g x - 1 := by
    intro x
    have hcard : (arc p q x ∩ arc p q (x + 1)).card = q - 1 := by
      have := arc_inter_card p q h2q x 1 (by omega)
      simpa using this
    have hcard' : (arc p q (g x) ∩ arc p q (g (x + 1))).card = q - 1 := by
      calc
        (arc p q (g x) ∩ arc p q (g (x + 1))).card
            = ((arc p q x).image f ∩ (arc p q (x + 1)).image f).card := by
                simpa [hg_spec x, hg_spec (x + 1)]
        _ = ((arc p q x ∩ arc p q (x + 1)).image f).card := by
                have h := (Finset.image_inter (arc p q x) (arc p q (x + 1)) hf_inj)
                simpa [h] using rfl
        _ = (arc p q x ∩ arc p q (x + 1)).card := by
                exact Finset.card_image_of_injective _ hf_inj
        _ = q - 1 := hcard
    exact (arc_inter_card_eq_q_sub_one_iff p q hq h2q (g x) (g (x + 1))).1 hcard'
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hp : 2 < p := by omega
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdiv
    exact (not_lt_of_ge hle) hp
  have hkneq : ∀ k : ℕ, (k : ZMod p) + 2 ≠ (k : ZMod p) := by
    intro k h_eq
    have : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = (k : ZMod p) + 2 - (k : ZMod p) := by abel
        _ = 0 := by simpa [h_eq]
    exact htwo_ne this
  set a := g 0
  have hcase : g 1 = a + 1 ∨ g 1 = a - 1 := by
    simpa [a] using (hg_adj 0)
  -- For any j < q, x is in arc (x - j)
  have hmem_arc : ∀ x (j : ℕ), j < q → x ∈ arc p q (x - (j : ZMod p)) := by
    intro x j hj
    refine (mem_arc_iff p q (x - (j : ZMod p)) x).2 ?_
    refine ⟨j, hj, ?_⟩
    abel
  rcases hcase with hplus | hminus
  · -- Translation case: g x = a + x
    have hg_pair :
        ∀ k : ℕ, g (k : ZMod p) = a + (k : ZMod p) ∧
          g ((k : ZMod p) + 1) = a + ((k : ZMod p) + 1) := by
      intro k
      induction k with
      | zero =>
          refine ⟨?h0, ?h1⟩
          · simp [a]
          · simpa [a] using hplus
      | succ k hk =>
          rcases hk with ⟨hk0, hk1⟩
          have hstep := hg_adj ((k : ZMod p) + 1)
          have hstep' :
              g ((k : ZMod p) + 2) = g ((k : ZMod p) + 1) + 1 ∨
                g ((k : ZMod p) + 2) = g ((k : ZMod p) + 1) - 1 := by
            simpa [add_assoc, one_add_one_eq_two] using hstep
          have hnext : g ((k : ZMod p) + 2) = g ((k : ZMod p) + 1) + 1 := by
            rcases hstep' with hstep | hstep
            · exact hstep
            · have h_eq : g ((k : ZMod p) + 2) = g (k : ZMod p) := by
                calc
                  g ((k : ZMod p) + 2)
                      = g ((k : ZMod p) + 1) - 1 := hstep
                  _ = a + (k : ZMod p) := by
                        calc
                          g ((k : ZMod p) + 1) - 1
                              = (a + ((k : ZMod p) + 1)) - 1 := by simpa [hk1]
                          _ = a + (k : ZMod p) := by abel
                  _ = g (k : ZMod p) := by simpa [hk0]
              exact (hkneq k (hg_inj h_eq)).elim
          refine ⟨?_, ?_⟩
          · simpa [Nat.cast_add] using hk1
          · have hcast : (↑(k + 1) : ZMod p) + 1 = (↑k : ZMod p) + 2 := by
              simp [Nat.cast_add, add_assoc, one_add_one_eq_two]
            have hcast1 : (↑k : ZMod p) + 1 + 1 = ↑k + 2 := by
              calc
                (↑k : ZMod p) + 1 + 1 = (↑k : ZMod p) + (1 + 1) := by simp [add_assoc]
                _ = ↑k + 2 := by simp [one_add_one_eq_two]
            calc
              g (↑(k + 1) + 1) = g (↑k + 1 + 1) := by
                simp [Nat.cast_add, add_assoc]
              _ = g (↑k + 2) := by simpa [hcast1]
              _ = g (↑k + 1) + 1 := hnext
              _ = a + (↑k + 1) + 1 := by simpa [hk1]
              _ = a + (↑k + 2) := by
                    calc
                      a + (↑k + 1) + 1 = a + (↑k + 1 + 1) := by simp [add_assoc]
                      _ = a + (↑k + 2) := by simpa [hcast1]
              _ = a + (↑(k + 1) + 1) := by
                    simpa using congrArg (fun t => a + t) hcast.symm
    have hg_translate : ∀ x, g x = a + x := by
      intro x
      have hk := (hg_pair x.val).1
      simpa [ZMod.natCast_zmod_val] using hk
    have hf_translate : ∀ x, f x = a + x := by
      intro x
      have hx0 : f x ∈ arc p q (a + x) := by
        have hx : x ∈ arc p q x := by
          exact (mem_arc_iff p q x x).2 ⟨0, by omega, by simp⟩
        have hx' : f x ∈ (arc p q x).image f :=
          Finset.mem_image.mpr ⟨x, hx, rfl⟩
        simpa [hg_spec x, hg_translate] using hx'
      have hxq : f x ∈ arc p q (a + x - ((q - 1 : ℕ) : ZMod p)) := by
        have hx : x ∈ arc p q (x - ((q - 1 : ℕ) : ZMod p)) :=
          hmem_arc x (q - 1) (by omega)
        have hx' : f x ∈ (arc p q (x - ((q - 1 : ℕ) : ZMod p))).image f :=
          Finset.mem_image.mpr ⟨x, hx, rfl⟩
        have hx'' := hx'
        have himg := hg_spec (x - ((q - 1 : ℕ) : ZMod p))
        rw [himg] at hx''
        simpa [hg_translate, sub_eq_add_neg, add_assoc] using hx''
      have hsingle :
          arc p q (a + x) ∩ arc p q (a + x - ((q - 1 : ℕ) : ZMod p)) = {a + x} := by
        have h :=
          arc_inter_eq p q h2q (a + x - ((q - 1 : ℕ) : ZMod p)) (q - 1) (by omega)
        have hq1 : q - (q - 1) = 1 := by omega
        have h' : arc p q (a + x) ∩ arc p q (a + x - ((q - 1 : ℕ) : ZMod p)) =
            arc p 1 (a + x) := by
          simpa [hq1, Finset.inter_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
        simpa [arc_one_eq_singleton p (a + x)] using h'
      have hxmem : f x ∈ arc p q (a + x) ∩ arc p q (a + x - ((q - 1 : ℕ) : ZMod p)) :=
        Finset.mem_inter.mpr ⟨hx0, hxq⟩
      have hxmem' : f x ∈ ({a + x} : Finset (ZMod p)) := by
        simpa [hsingle] using hxmem
      exact Finset.mem_singleton.mp hxmem'
    exact ⟨a, Or.inl hf_translate⟩
  · -- Reflection case: g x = a - x
    have hg_pair :
        ∀ k : ℕ, g (k : ZMod p) = a - (k : ZMod p) ∧
          g ((k : ZMod p) + 1) = a - ((k : ZMod p) + 1) := by
      intro k
      induction k with
      | zero =>
          constructor
          · simp [a]
          · simpa [a] using hminus
      | succ k hk =>
          rcases hk with ⟨hk0, hk1⟩
          have hstep := hg_adj ((k : ZMod p) + 1)
          have hstep' :
              g ((k : ZMod p) + 2) = g ((k : ZMod p) + 1) + 1 ∨
                g ((k : ZMod p) + 2) = g ((k : ZMod p) + 1) - 1 := by
            simpa [add_assoc, one_add_one_eq_two] using hstep
          have hnext : g ((k : ZMod p) + 2) = g ((k : ZMod p) + 1) - 1 := by
            rcases hstep' with hstep | hstep
            · have h_eq : g ((k : ZMod p) + 2) = g (k : ZMod p) := by
                calc
                  g ((k : ZMod p) + 2)
                      = g ((k : ZMod p) + 1) + 1 := hstep
                  _ = a - (k : ZMod p) := by
                        calc
                          g ((k : ZMod p) + 1) + 1
                              = (a - ((k : ZMod p) + 1)) + 1 := by simpa [hk1]
                          _ = a - (k : ZMod p) := by abel
                  _ = g (k : ZMod p) := by simpa [hk0]
              exact (hkneq k (hg_inj h_eq)).elim
            · exact hstep
          refine ⟨?_, ?_⟩
          · simpa [Nat.cast_add] using hk1
          · have hcast : (↑(k + 1) : ZMod p) + 1 = (↑k : ZMod p) + 2 := by
              simp [Nat.cast_add, add_assoc, one_add_one_eq_two]
            have hcast1 : (↑k : ZMod p) + 1 + 1 = ↑k + 2 := by
              calc
                (↑k : ZMod p) + 1 + 1 = (↑k : ZMod p) + (1 + 1) := by simp [add_assoc]
                _ = ↑k + 2 := by simp [one_add_one_eq_two]
            calc
              g (↑(k + 1) + 1) = g (↑k + 1 + 1) := by
                simp [Nat.cast_add, add_assoc]
              _ = g (↑k + 2) := by simpa [hcast1]
              _ = g (↑k + 1) - 1 := hnext
              _ = a - (↑k + 1) - 1 := by simpa [hk1]
              _ = a - (↑k + 2) := by
                    calc
                      a - (↑k + 1) - 1 = a - (↑k + (1 + 1)) := by
                        simp [sub_eq_add_neg, add_comm, add_left_comm]
                      _ = a - (↑k + 2) := by simp [one_add_one_eq_two]
              _ = a - (↑(k + 1) + 1) := by
                    simpa using congrArg (fun t => a - t) hcast.symm
    have hg_reflect : ∀ x, g x = a - x := by
      intro x
      have hk := (hg_pair x.val).1
      simpa [ZMod.natCast_zmod_val] using hk
    set a' : ZMod p := a + (q - 1 : ℕ) with ha'
    have hf_reflect : ∀ x, f x = a' - x := by
      intro x
      have hx0 : f x ∈ arc p q (a - x) := by
        have hx : x ∈ arc p q x := by
          exact (mem_arc_iff p q x x).2 ⟨0, by omega, by simp⟩
        have hx' : f x ∈ (arc p q x).image f :=
          Finset.mem_image.mpr ⟨x, hx, rfl⟩
        simpa [hg_spec x, hg_reflect, sub_eq_add_neg, add_assoc] using hx'
      have hxq : f x ∈ arc p q (a - x + ((q - 1 : ℕ) : ZMod p)) := by
        have hx : x ∈ arc p q (x - ((q - 1 : ℕ) : ZMod p)) :=
          hmem_arc x (q - 1) (by omega)
        have hx' : f x ∈ (arc p q (x - ((q - 1 : ℕ) : ZMod p))).image f :=
          Finset.mem_image.mpr ⟨x, hx, rfl⟩
        have hx'' := hx'
        have himg := hg_spec (x - ((q - 1 : ℕ) : ZMod p))
        rw [himg] at hx''
        simpa [hg_reflect, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx''
      have hsingle :
          arc p q (a - x) ∩ arc p q (a - x + ((q - 1 : ℕ) : ZMod p)) =
            {a - x + ((q - 1 : ℕ) : ZMod p)} := by
        have h := arc_inter_eq p q h2q (a - x) (q - 1) (by omega)
        have hq1 : q - (q - 1) = 1 := by omega
        have h' :
            arc p q (a - x) ∩ arc p q (a - x + ((q - 1 : ℕ) : ZMod p)) =
              arc p 1 (a - x + ((q - 1 : ℕ) : ZMod p)) := by
          simpa [hq1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
        simpa [arc_one_eq_singleton p (a - x + ((q - 1 : ℕ) : ZMod p))] using h'
      have hxmem :
          f x ∈ arc p q (a - x) ∩ arc p q (a - x + ((q - 1 : ℕ) : ZMod p)) :=
        Finset.mem_inter.mpr ⟨hx0, hxq⟩
      have hxmem' :
          f x ∈ ({a - x + ((q - 1 : ℕ) : ZMod p)} : Finset (ZMod p)) := by
        simpa [hsingle] using hxmem
      have hxmem'' := Finset.mem_singleton.mp hxmem'
      simpa [ha', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxmem''
    exact ⟨a', Or.inr hf_reflect⟩

/-- Combined: Self-cohomomorphisms of fraction graphs are rotations ± reflections. -/
theorem fractionGraph_selfCohom_form (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : IsCohom (fractionGraph p q) (fractionGraph p q) f) :
    ∃ a : ZMod p, (∀ x, f x = a + x) ∨ (∀ x, f x = a - x) := by
  have hbij := fractionGraph_selfCohom_isIso p q hq h2q hcoprime f hf
  exact fractionGraph_selfIso_form p q hq h2q hcoprime f hbij hf

/-- Theorem 5.6 (part 1) — generalised: Self-cohomomorphisms of fraction graphs
    `E_{p/q}` are isomorphisms, without the `q ≥ 2` restriction.

    For `q ≥ 2`, this delegates to `fractionGraph_selfCohom_isIso`. For `q ≤ 1`,
    `E_{p/q}` is edgeless (`q = 0` forces `p = 1`; `q = 1` is the edgeless case),
    so any cohomomorphism is automatically injective and hence bijective. -/
theorem fractionGraph_selfCohom_isIso_general (p q : ℕ) [NeZero p]
    (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : IsCohom (fractionGraph p q) (fractionGraph p q) f) :
    Function.Bijective f := by
  by_cases hq : 2 ≤ q
  · exact fractionGraph_selfCohom_isIso p q hq h2q hcoprime f hf
  · -- q ≤ 1. E_{p/q} is edgeless (no edges when q ≤ 1).
    push_neg at hq
    have : q = 0 ∨ q = 1 := by omega
    rcases this with rfl | rfl
    · -- q = 0: p = 1 (from coprimality), single vertex, trivially bijective
      have hp1 : p = 1 := by simpa [Nat.Coprime] using hcoprime
      subst hp1
      exact (Finite.injective_iff_bijective).mp fun a b _ =>
        Subsingleton.elim a b
    · -- q = 1: E_{p/1} is edgeless, injective hence bijective
      have hedgeless := FractionGraphBasic.fractionGraph_one_edgeless p
      exact (Finite.injective_iff_bijective).mp fun a b hab => by
        by_contra hne
        exact (hf a b hne (by rw [hedgeless]; exact not_false)).1 hab

/-! ### Cyclic Neighbors in ZMod

In ZMod p, the cyclic neighbors of a vertex v are v+1 and v-1. These are the
vertices at "distance 1" in the cyclic order. Rotations and reflections of
E_{p/q} preserve this cyclic neighbor relationship. -/

/-- The cyclic neighbors of v in ZMod p are v+1 and v-1. -/
def cyclicNeighbors (p : ℕ) [NeZero p] (v : ZMod p) : Finset (ZMod p) :=
  {v + 1, v - 1}

/-- Rotation preserves cyclic neighbors: if w is a cyclic neighbor of v,
    then (a + w) is a cyclic neighbor of (a + v). -/
lemma cyclicNeighbors_rotation (p : ℕ) [NeZero p] (a v : ZMod p) :
    (cyclicNeighbors p v).image (fun w => a + w) = cyclicNeighbors p (a + v) := by
  simp only [cyclicNeighbors, Finset.image_insert, Finset.image_singleton]
  congr 1 <;> ring_nf

/-- Reflection swaps cyclic neighbors: if w is a cyclic neighbor of v,
    then (a - w) is a cyclic neighbor of (a - v). -/
lemma cyclicNeighbors_reflection (p : ℕ) [NeZero p] (a v : ZMod p) :
    (cyclicNeighbors p v).image (fun w => a - w) = cyclicNeighbors p (a - v) := by
  simp only [cyclicNeighbors, Finset.image_insert, Finset.image_singleton]
  -- a - (v + 1) = a - v - 1 and a - (v - 1) = a - v + 1
  ext w
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · right; ring
    · left; ring
  · rintro (rfl | rfl)
    · right; ring
    · left; ring

/-- The cyclic neighbors of v are exactly v ± 1. -/
lemma mem_cyclicNeighbors_iff (p : ℕ) [NeZero p] (v w : ZMod p) :
    w ∈ cyclicNeighbors p v ↔ w = v + 1 ∨ w = v - 1 := by
  simp [cyclicNeighbors]

/-- The cyclic neighbors of 0 are 1 and p-1 (which equals -1 in ZMod p). -/
lemma cyclicNeighbors_zero (p : ℕ) [NeZero p] :
    cyclicNeighbors p (0 : ZMod p) = {1, -1} := by
  simp [cyclicNeighbors]

/-- Self-isomorphisms of E_{p/q} map cyclic neighbors to cyclic neighbors.
    If f is a rotation (f x = a + x) or reflection (f x = a - x), then
    f maps the cyclic neighbors of any vertex v to the cyclic neighbors of f v. -/
lemma fractionGraph_selfIso_preserves_cyclicNeighbors (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : Function.Bijective f)
    (hf_cohom : IsCohom (fractionGraph p q) (fractionGraph p q) f)
    (v : ZMod p) :
    (cyclicNeighbors p v).image f = cyclicNeighbors p (f v) := by
  rcases fractionGraph_selfIso_form p q hq h2q hcoprime f hf hf_cohom with ⟨a, hrot | hrefl⟩
  · -- Rotation case: f x = a + x
    have hf_eq : f = fun w => a + w := funext hrot
    simp only [hf_eq]
    exact cyclicNeighbors_rotation p a v
  · -- Reflection case: f x = a - x
    have hf_eq : f = fun w => a - w := funext hrefl
    simp only [hf_eq]
    exact cyclicNeighbors_reflection p a v

/-! ### Cyclic Neighbors on Circle via Graph Isomorphism

For S ⊆ Circle isomorphic to E_{p/q}, the cyclic neighbors of y ∈ S are determined by
the graph structure: if φ : S → ZMod p is the isomorphism with φ(y) = v, then the
cyclic neighbors are φ⁻¹(v+1) and φ⁻¹(v-1).

Following Lemma 5.3: when S_y and S_x share the same skeleton
(S_y \ {y} = S_x \ {x}), both y and x have the same cyclic neighbors s_prev, s_next
in their respective sets (because both fill the same "gap" in the skeleton). -/

/-- Given an isomorphism φ : S → ZMod p and y ∈ S with φ(y) = v, the cyclic neighbors
    of y are the preimages of v+1 and v-1 in ZMod p. -/
noncomputable def circleCyclicNeighborsViaIso {p : ℕ} [NeZero p] (S : Set Circle)
    (φ : S ≃ ZMod p) (y : S) : Finset Circle :=
  {(φ.symm (φ y + 1)).val, (φ.symm (φ y - 1)).val}

/-- Key lemma: If f maps S_y to f(S_y), and both are isomorphic to E_{p/q} via graph isomorphisms,
    then f maps cyclic neighbors to cyclic neighbors.

    More precisely: Let φ : S_y → ZMod p and ψ : f(S_y) → ZMod p be graph isomorphisms.
    If s is a cyclic neighbor of y in S_y (meaning φ(s) = φ(y) ± 1), then f(s) is a
    cyclic neighbor of f(y) in f(S_y) (meaning ψ(f(s)) = ψ(f(y)) ± 1).

    Proof: The composition ψ ∘ f|_{S_y} ∘ φ^{-1} : ZMod p → ZMod p is a self-isomorphism of E_{p/q}.
    By fractionGraph_selfIso_form, it's a rotation (x ↦ a+x) or reflection (x ↦ a-x).
    Both rotations and reflections map {v-1, v+1} to {(rotation/reflection)(v) ± 1}. -/
lemma cohom_preserves_cyclicNeighbors_via_iso
    (p q : ℕ) [NeZero p] (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (S_y : Set Circle) (f : Circle → Circle)
    -- S_y isomorphic to E_{p/q}
    (φ : ((circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2)).induce S_y) ≃g fractionGraph p q)
    -- f(S_y) isomorphic to E_{p/q}
    (ψ : ((circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2)).induce (S_y.image f))
      ≃g fractionGraph p q)
    (y : S_y)
    -- Assume f is injective on S_y (so f(S_y) has the same size)
    (hf_inj : Function.Injective (fun s : S_y => f s.val))
    -- f is a cohom on the circle graph (needed to show f|_{S_y} preserves non-adjacency)
    (hf_cohom : IsCohom (circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2))
                        (circleGraphOpen 2 (by norm_num : (2 : ℝ) ≤ 2)) f)
    -- s is a cyclic neighbor of y via φ
    (s : S_y) (hs_neighbor : φ s = φ y + 1 ∨ φ s = φ y - 1) :
    -- Then f(s) is a cyclic neighbor of f(y) via ψ
    let fy : (S_y.image f) := ⟨f y.val, Set.mem_image_of_mem f y.property⟩
    let fs : (S_y.image f) := ⟨f s.val, Set.mem_image_of_mem f s.property⟩
    ψ fs = ψ fy + 1 ∨ ψ fs = ψ fy - 1 := by
  intro fy fs
  -- Step 1: Define g : ZMod p → ZMod p as ψ ∘ f|_{S_y} ∘ φ⁻¹
  let g : ZMod p → ZMod p := fun v =>
    let s_v : S_y := φ.symm v
    let fs_v : (S_y.image f) := ⟨f s_v.val, Set.mem_image_of_mem f s_v.property⟩
    ψ fs_v
  -- Step 2: Show g(φ(y)) = ψ(fy) and g(φ(s)) = ψ(fs)
  have hg_y : g (φ y) = ψ fy := by
    simp only [g, RelIso.symm_apply_apply]; rfl
  have hg_s : g (φ s) = ψ fs := by
    simp only [g, RelIso.symm_apply_apply]; rfl
  -- Step 3: Show g is a bijection
  have hg_bij : Function.Bijective g := by
    constructor
    · -- Injective
      intro v w hvw
      simp only [g] at hvw
      have h1 := ψ.injective hvw
      have h2 : f (φ.symm v).val = f (φ.symm w).val := Subtype.ext_iff.mp h1
      have h3 := hf_inj h2
      have h4 := Subtype.ext_iff.mp h3
      exact φ.symm.injective (Subtype.ext h4)
    · -- Surjective
      intro w
      obtain ⟨z, hz⟩ := ψ.surjective w
      obtain ⟨c, hc_mem, hc_eq⟩ := z.property
      use φ ⟨c, hc_mem⟩
      simp only [g, RelIso.symm_apply_apply]
      rw [← hz]
      congr 1
      exact Subtype.ext hc_eq
  -- Step 4: Show g is a cohom
  -- For bijective cohoms between finite graphs with same #edges, cohom = iso
  -- Both (induce S_y) and (induce f(S_y)) are iso to E_{p/q}, hence same #edges
  have hg_cohom : IsCohom (fractionGraph p q) (fractionGraph p q) g := by
    intro u v huv hnadj
    constructor
    · intro heq; apply huv; exact hg_bij.1 heq
    · -- g = ψ ∘ f|_{S_y} ∘ φ⁻¹ preserves non-adjacency because:
      -- φ⁻¹ (graph iso) → f (cohom) → ψ (graph iso)
      -- Each step preserves non-adjacency.
      --
      -- Direct proof: Given hnadj : ¬E[p/q].Adj u v, show ¬E[p/q].Adj (g u) (g v)
      intro hadj_g
      -- hadj_g : E[p/q].Adj (g u) (g v), we derive contradiction with hnadj
      --
      -- Step 1: φ.symm preserves non-adjacency (graph iso)
      -- hnadj : ¬E[p/q].Adj u v
      -- So ¬(induce S_y).Adj (φ.symm u) (φ.symm v)
      have h_Sy_nadj : ¬((circleGraphOpen 2 (by norm_num)).induce S_y).Adj
          (φ.symm u) (φ.symm v) := by
        intro h_Sy_adj
        apply hnadj
        -- φ.symm.map_adj_iff : (induce S_y).Adj (φ.symm a) (φ.symm b) ↔ E[p/q].Adj a b
        rw [← φ.symm.map_adj_iff]
        exact h_Sy_adj
      -- Step 2: Induced non-adjacency → Circle non-adjacency
      -- induce_adj : (induce S G).Adj u v ↔ G.Adj ↑u ↑v
      have h_circle_nadj : ¬(circleGraphOpen 2 (by norm_num)).Adj
          (φ.symm u).val (φ.symm v).val := by
        intro h_circle_adj
        apply h_Sy_nadj
        rw [SimpleGraph.induce_adj]
        exact h_circle_adj
      -- Step 3: f is cohom, so preserves non-adjacency on Circle
      have h_ne : (φ.symm u).val ≠ (φ.symm v).val := by
        intro heq
        apply huv
        exact φ.symm.injective (Subtype.ext heq)
      have hf_result := hf_cohom (φ.symm u).val (φ.symm v).val h_ne h_circle_nadj
      obtain ⟨hf_ne, hf_nadj⟩ := hf_result
      -- hf_nadj : ¬Circle.Adj (f (φ.symm u).val) (f (φ.symm v).val)
      -- Step 4: Circle non-adjacency → (induce f(S_y)) non-adjacency
      have h_fSy_nadj : ¬((circleGraphOpen 2 (by norm_num)).induce (S_y.image f)).Adj
          ⟨f (φ.symm u).val, Set.mem_image_of_mem f (φ.symm u).property⟩
          ⟨f (φ.symm v).val, Set.mem_image_of_mem f (φ.symm v).property⟩ := by
        intro h_fSy_adj
        rw [SimpleGraph.induce_adj] at h_fSy_adj
        exact hf_nadj h_fSy_adj
      -- Step 5: ψ preserves non-adjacency (graph iso)
      have h_Epq_nadj : ¬(fractionGraph p q).Adj
          (ψ ⟨f (φ.symm u).val, Set.mem_image_of_mem f (φ.symm u).property⟩)
          (ψ ⟨f (φ.symm v).val, Set.mem_image_of_mem f (φ.symm v).property⟩) := by
        intro h_Epq_adj
        apply h_fSy_nadj
        have h := ψ.map_adj_iff.mp h_Epq_adj
        exact h
      -- Step 6: This is ¬Adj (g u) (g v), contradicting hadj_g
      simp only [g] at hadj_g
      exact h_Epq_nadj hadj_g
  -- Step 5: Apply fractionGraph_selfCohom_form to conclude g is rotation or reflection
  have hg_form := fractionGraph_selfCohom_form p q hq h2q hcoprime g hg_cohom
  obtain ⟨a, hrot | hrefl⟩ := hg_form
  · -- Rotation case: g(x) = a + x
    cases hs_neighbor with
    | inl h_plus =>
      left
      calc ψ fs = g (φ s) := hg_s.symm
        _ = a + φ s := hrot (φ s)
        _ = a + (φ y + 1) := by rw [h_plus]
        _ = (a + φ y) + 1 := by ring
        _ = g (φ y) + 1 := by rw [← hrot (φ y)]
        _ = ψ fy + 1 := by rw [hg_y]
    | inr h_minus =>
      right
      calc ψ fs = g (φ s) := hg_s.symm
        _ = a + φ s := hrot (φ s)
        _ = a + (φ y - 1) := by rw [h_minus]
        _ = (a + φ y) - 1 := by ring
        _ = g (φ y) - 1 := by rw [← hrot (φ y)]
        _ = ψ fy - 1 := by rw [hg_y]
  · -- Reflection case: g(x) = a - x
    cases hs_neighbor with
    | inl h_plus =>
      right
      calc ψ fs = g (φ s) := hg_s.symm
        _ = a - φ s := hrefl (φ s)
        _ = a - (φ y + 1) := by rw [h_plus]
        _ = (a - φ y) - 1 := by ring
        _ = g (φ y) - 1 := by rw [← hrefl (φ y)]
        _ = ψ fy - 1 := by rw [hg_y]
    | inr h_minus =>
      left
      calc ψ fs = g (φ s) := hg_s.symm
        _ = a - φ s := hrefl (φ s)
        _ = a - (φ y - 1) := by rw [h_minus]
        _ = (a - φ y) + 1 := by ring
        _ = g (φ y) + 1 := by rw [← hrefl (φ y)]
        _ = ψ fy + 1 := by rw [hg_y]

/-! ### Self-Cohomomorphisms of Circle Graphs -/

/-
Lemma 5.5 (continuity) uses continued fraction convergents:
1. The convergents p_n/q_n of r give fraction graphs E_{p_n/q_n}
2. Equidistant points on circle induce these fraction graphs
3. Self-cohomomorphism maps these finite induced subgraphs isomorphically
4. The isomorphisms must be consistent (rotations/reflections)
5. This forces the map on the circle to be continuous
-/

lemma continuous_add_left_circle (a : Circle) : Continuous (fun x : Circle => a + x) := by
  simpa using (continuous_const.add continuous_id)

lemma continuous_sub_left_circle (a : Circle) : Continuous (fun x : Circle => a - x) := by
  simpa [sub_eq_add_neg] using (continuous_const.add continuous_neg)

lemma two_lt_of_irrational_ge_two (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) : 2 < r := by
  have hne : r ≠ (2 : ℝ) := by
    simpa using (hirr.ne_rat (2 : ℚ))
  exact lt_of_le_of_ne hr hne.symm

lemma frac_lt_of_det_one (a b a1 b1 : ℕ) (hb : 0 < b) (hb1 : 0 < b1)
    (hdet : a1 * b - b1 * a = 1) : (a : ℚ) / b < (a1 : ℚ) / b1 := by
  have hmul : (a : ℚ) * b1 < (a1 : ℚ) * b := by
    have hdet' : (a1 : ℤ) * b - (b1 : ℤ) * a = 1 := by
      have hle : b1 * a ≤ a1 * b := by omega
      simpa [Int.ofNat_sub hle] using congrArg (fun t : ℕ => (t : ℤ)) hdet
    have hmul' : (a1 : ℤ) * b = (b1 : ℤ) * a + 1 := by linarith
    have hmul'' : (a : ℤ) * b1 < (a1 : ℤ) * b := by linarith [hmul']
    exact_mod_cast hmul''
  have hb1' : (0 : ℚ) < b1 := Nat.cast_pos.mpr hb1
  have hb' : (0 : ℚ) < b := Nat.cast_pos.mpr hb
  rw [div_lt_div_iff₀ hb' hb1']
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

lemma frac_lt_of_det_neg_one (a b a1 b1 : ℕ) (hb : 0 < b) (hb1 : 0 < b1)
    (hdet : b1 * a - a1 * b = 1) : (a1 : ℚ) / b1 < (a : ℚ) / b := by
  have hdet' : a * b1 - b * a1 = 1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdet
  have h := frac_lt_of_det_one a1 b1 a b hb1 hb hdet'
  simpa using h

lemma fractionGraph_no_cohom_to_predecessor (p q p' q' : ℕ) [NeZero p] [NeZero p']
    (hq : 0 < q) (hq' : 0 < q') (h2q : 2 * q ≤ p) (h2q' : 2 * q' ≤ p')
    (hp'_lt : p' < p) (hq'_lt : q' < q) (heq : p * q' - q * p' = 1) :
    ¬Cohom (fractionGraph p q) (fractionGraph p' q') := by
  intro hcohom
  have hle :=
    fractionGraph_ordering_reverse p q p' q' hq hq' h2q h2q' hcohom
  have hlt := sternBrocot_predecessor_lt p q p' q' hp'_lt hq'_lt hq' heq
  exact (not_le_of_gt hlt) hle

lemma circleGraphClosed_adj_add_left (r : ℝ) (hr : 2 ≤ r) (a u v : Circle) :
    (circleGraphClosed r hr).Adj (a + u) (a + v) ↔ (circleGraphClosed r hr).Adj u v := by
  constructor
  · rintro ⟨hne, hdist⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (by simpa [h])
    · simpa [circleDistance, dist_add_left] using hdist
  · rintro ⟨hne, hdist⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (add_left_cancel h)
    · simpa [circleDistance, dist_add_left] using hdist

lemma circleGraphOpen_adj_add_left (r : ℝ) (hr : 2 ≤ r) (a u v : Circle) :
    (circleGraphOpen r hr).Adj (a + u) (a + v) ↔ (circleGraphOpen r hr).Adj u v := by
  constructor
  · rintro ⟨hne, hdist⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (by simpa [h])
    · simpa [circleDistance, dist_add_left] using hdist
  · rintro ⟨hne, hdist⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (add_left_cancel h)
    · simpa [circleDistance, dist_add_left] using hdist

lemma isCohom_add_left_open (r : ℝ) (hr : 2 ≤ r) (a : Circle) :
    IsCohom (circleGraphOpen r hr) (circleGraphOpen r hr) (fun x => a + x) := by
  intro u v huv hnadj
  have hne : a + u ≠ a + v := by
    intro h
    exact huv (add_left_cancel h)
  have hnadj' : ¬(circleGraphOpen r hr).Adj (a + u) (a + v) := by
    have h := (circleGraphOpen_adj_add_left r hr a u v)
    exact (by simpa [h] using hnadj)
  exact ⟨hne, hnadj'⟩

lemma isCohom_add_left_closed (r : ℝ) (hr : 2 ≤ r) (a : Circle) :
    IsCohom (circleGraphClosed r hr) (circleGraphClosed r hr) (fun x => a + x) := by
  intro u v huv hnadj
  have hne : a + u ≠ a + v := by
    intro h
    exact huv (add_left_cancel h)
  have hnadj' : ¬(circleGraphClosed r hr).Adj (a + u) (a + v) := by
    have h := (circleGraphClosed_adj_add_left r hr a u v)
    exact (by simpa [h] using hnadj)
  exact ⟨hne, hnadj'⟩

def equidistantPointsShift (N : ℕ) [NeZero N] (y : Circle) : Set Circle :=
  Set.image (fun x => y + x) (equidistantPoints N)

lemma mem_equidistantPointsShift (N : ℕ) [NeZero N] (y : Circle) :
    y ∈ equidistantPointsShift N y := by
  refine ⟨embedZMod N 0, ?_, by simpa [embedZMod_zero]⟩
  exact ⟨0, rfl⟩

lemma equidistantPointsShift_finite (N : ℕ) [NeZero N] (y : Circle) :
    (equidistantPointsShift N y).Finite := by
  classical
  exact (equidistantPoints_finite N).image (fun x => y + x)

lemma circleDistance_equidistant_shift_rat (N : ℕ) [NeZero N] (y : Circle) (k : ZMod N) :
    circleDistance y (y + embedZMod N k) =
      (distMod N (0 : ZMod N) k : ℝ) / (N : ℝ) := by
  have hdist :
      circleDistance y (y + embedZMod N k) =
        circleDistance (embedZMod N (0 : ZMod N)) (embedZMod N k) := by
    simpa [circleDistance, embedZMod_zero, add_comm, add_left_comm, add_assoc] using
      (dist_add_left y (embedZMod N (0 : ZMod N)) (embedZMod N k))
  have hdist' :
      circleDistance (embedZMod N (0 : ZMod N)) (embedZMod N k) =
        (distMod N (0 : ZMod N) k : ℝ) / (N : ℝ) := by
    simpa [circleDistance] using (embedZMod_dist_eq N (0 : ZMod N) k)
  simpa [hdist] using hdist'

lemma circleDistance_equidistant_shift_rat' (N : ℕ) [NeZero N] (y : Circle)
    (k l : ZMod N) :
    circleDistance (y + embedZMod N k) (y + embedZMod N l) =
      (distMod N k l : ℝ) / (N : ℝ) := by
  have hdist :
      circleDistance (y + embedZMod N k) (y + embedZMod N l) =
        circleDistance (embedZMod N k) (embedZMod N l) := by
    simpa [circleDistance, add_comm, add_left_comm, add_assoc] using
      (dist_add_left y (embedZMod N k) (embedZMod N l))
  have hdist' :
      circleDistance (embedZMod N k) (embedZMod N l) =
        (distMod N k l : ℝ) / (N : ℝ) := by
    simpa [circleDistance] using (embedZMod_dist_eq N k l)
  simpa [hdist] using hdist'

lemma circleDistance_equidistant_shift_ne_one_div (r : ℝ) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (y : Circle) (k : ZMod N) :
    circleDistance y (y + embedZMod N k) ≠ 1 / r := by
  have hirr_inv : Irrational (1 / r) := by
    simpa using (Irrational.inv hirr)
  obtain ⟨q, hq⟩ :
      ∃ q : ℚ, (circleDistance y (y + embedZMod N k) : ℝ) = (q : ℝ) := by
    refine ⟨(distMod N (0 : ZMod N) k : ℚ) / (N : ℚ), ?_⟩
    have hrat' :=
      circleDistance_equidistant_shift_rat (N := N) (y := y) (k := k)
    have hcast :
        ((distMod N (0 : ZMod N) k : ℚ) / (N : ℚ) : ℝ) =
          (distMod N (0 : ZMod N) k : ℝ) / (N : ℝ) := by
      simpa using
        (Rat.cast_div (p := (distMod N (0 : ZMod N) k : ℚ)) (q := (N : ℚ)) (α := ℝ))
    simpa [hcast] using hrat'
  intro h
  have h' : (q : ℝ) = (1 / r : ℝ) := by
    simpa [hq] using h
  exact (hirr_inv.ne_rat q) h'.symm

lemma circleDistance_equidistant_shift_ne_one_div' (r : ℝ) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (y : Circle) (k l : ZMod N) :
    circleDistance (y + embedZMod N k) (y + embedZMod N l) ≠ 1 / r := by
  have hirr_inv : Irrational (1 / r) := by
    simpa using (Irrational.inv hirr)
  obtain ⟨q, hq⟩ :
      ∃ q : ℚ,
        (circleDistance (y + embedZMod N k) (y + embedZMod N l) : ℝ) = (q : ℝ) := by
    refine ⟨(distMod N k l : ℚ) / (N : ℚ), ?_⟩
    have hrat' :=
      circleDistance_equidistant_shift_rat' (N := N) (y := y) (k := k) (l := l)
    have hcast :
        ((distMod N k l : ℚ) / (N : ℚ) : ℝ) =
          (distMod N k l : ℝ) / (N : ℝ) := by
      simpa using (Rat.cast_div (p := (distMod N k l : ℚ)) (q := (N : ℚ)) (α := ℝ))
    simpa [hcast] using hrat'
  intro h
  have h' : (q : ℝ) = (1 / r : ℝ) := by
    simpa [hq] using h
  exact (hirr_inv.ne_rat q) h'.symm

lemma circleDistance_lipschitz (x y z : Circle) :
    |circleDistance x z - circleDistance y z| ≤ circleDistance x y := by
  simpa [circleDistance, Real.dist_eq, abs_sub_comm] using
    (dist_dist_dist_le_left x y z)

noncomputable def repFrom (u x : Circle) : ℝ :=
  (AddCircle.equivIco 1 0 (x - u)).val

lemma repFrom_nonneg (u x : Circle) : 0 ≤ repFrom u x :=
  by
    simpa [repFrom] using (AddCircle.equivIco 1 0 (x - u)).prop.1

lemma repFrom_lt_one (u x : Circle) : repFrom u x < 1 :=
  by
    simpa [repFrom] using (AddCircle.equivIco 1 0 (x - u)).prop.2

lemma repFrom_self (u : Circle) : repFrom u u = 0 := by
  have hx : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by simp
  have h0 :
      (AddCircle.equivIco 1 0 (0 : Circle)) = ⟨0, hx⟩ := by
    simpa using (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := 0) hx)
  have h := congrArg Subtype.val h0
  simpa [repFrom, sub_eq_add_neg] using h

lemma repFrom_eq_zero_iff (u x : Circle) :
    repFrom u x = 0 ↔ x = u := by
  constructor
  · intro h
    have hx : (AddCircle.equivIco 1 0 (x - u)).val = 0 := h
    have hx' :
        (AddCircle.equivIco 1 0 (x - u)) =
          ⟨0, by simp⟩ := by
      apply Subtype.ext
      simpa using hx
    have h0 :
        (AddCircle.equivIco 1 0 (0 : Circle)) =
          ⟨0, by simp⟩ := by
      simpa using (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := 0) (by simp))
    have hxu : (x - u : Circle) = 0 := by
      apply (AddCircle.equivIco 1 0).injective
      simpa [h0] using hx'
    have := sub_eq_zero.mp hxu
    simpa [sub_eq_add_neg] using this
  · intro h
    subst h
    simp [repFrom_self]

lemma repFrom_pos_of_ne (u x : Circle) (hxu : x ≠ u) : 0 < repFrom u x := by
  have hne : repFrom u x ≠ 0 := by
    intro hzero
    exact hxu ((repFrom_eq_zero_iff u x).1 hzero)
  exact lt_of_le_of_ne (repFrom_nonneg u x) (Ne.symm hne)

/-- Helper: (a - b).val when a.val < b.val equals n - (b.val - a.val). -/
lemma zmod_val_sub_of_lt' (n : ℕ) [NeZero n] (a b : ZMod n) (h : a.val < b.val) :
    (a - b).val = n - (b.val - a.val) := by
  have hbn := ZMod.val_lt b
  have han := ZMod.val_lt a
  rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val]
  split_ifs with hb
  · simp only [hb, ZMod.val_zero] at h; omega
  · have hbval_pos : 0 < b.val := by
      by_contra h'; push_neg at h'
      simp only [Nat.le_zero] at h'
      exact hb ((ZMod.val_eq_zero b).mp h')
    have hsum : a.val + (n - b.val) < n := by omega
    rw [Nat.mod_eq_of_lt hsum]
    omega

/-- embedZMod is injective: if embedZMod N u = embedZMod N v then u = v.
    Proof: distance between u and v in ZMod N equals 0 iff u = v. -/
lemma embedZMod_eq_iff_eq (N : ℕ) [NeZero N] (u v : ZMod N) :
    embedZMod N u = embedZMod N v ↔ u = v := by
  constructor
  · intro h
    have hdist0 : dist (embedZMod N u) (embedZMod N v) = 0 := by simp [h]
    rw [embedZMod_dist_eq] at hdist0
    have hdm0 : (distMod N u v : ℝ) = 0 := by
      have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
      exact (div_eq_zero_iff.mp hdist0).resolve_right (ne_of_gt hN_pos)
    have hdm_nat : distMod N u v = 0 := by exact_mod_cast hdm0
    simp only [distMod] at hdm_nat
    have hval0 : (u - v).val = 0 := by
      rcases Nat.min_eq_zero_iff.mp hdm_nat with h1 | h2
      · exact h1
      · have := ZMod.val_lt (u - v); omega
    have huv_eq : u - v = 0 := (ZMod.val_eq_zero (u - v)).mp hval0
    exact sub_eq_zero.mp huv_eq
  · intro h; rw [h]

/-- embedZMod N k = 0 iff k = 0. -/
lemma embedZMod_eq_zero_iff (N : ℕ) [NeZero N] (k : ZMod N) :
    embedZMod N k = 0 ↔ k = 0 := by
  rw [← embedZMod_zero N]
  exact embedZMod_eq_iff_eq N k 0

/-- repFrom between equidistant points equals (l - k).val / N.
    This is key for computing cyclic successors/predecessors. -/
lemma repFrom_equidistant (N : ℕ) [NeZero N] (y : Circle) (k l : ZMod N) :
    repFrom (y + embedZMod N k) (y + embedZMod N l) = (l - k).val / N := by
  simp only [repFrom]
  -- The difference (y + embedZMod N l) - (y + embedZMod N k) = embedZMod N l - embedZMod N k
  have hdiff : (y + embedZMod N l) - (y + embedZMod N k) = embedZMod N l - embedZMod N k := by
    simp only [add_sub_add_left_eq_sub]
  rw [hdiff]
  -- embedZMod N l - embedZMod N k = QuotientAddGroup.mk (((l - k).val : ℝ) / N)
  -- Expand embedZMod definition
  simp only [embedZMod]
  have hembed : (QuotientAddGroup.mk (l.val / N : ℝ) : Circle) -
      (QuotientAddGroup.mk (k.val / N : ℝ) : Circle) =
      (QuotientAddGroup.mk (((l - k).val : ℝ) / N) : Circle) := by
    rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq]
    simp only [AddSubgroup.mem_zmultiples_iff, neg_sub]
    by_cases h : k.val ≤ l.val
    · use 0
      rw [ZMod.val_sub h]
      simp only [Nat.cast_sub h, zero_smul]
      ring
    · push_neg at h
      use 1
      have hN_pos : 0 < N := NeZero.pos N
      have hval := zmod_val_sub_of_lt' N l k h
      have hkn := ZMod.val_lt k
      have hbminus : k.val - l.val ≤ N := by omega
      rw [hval]
      simp only [Nat.cast_sub hbminus, Nat.cast_sub (le_of_lt h)]
      have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN_pos)
      field_simp
      ring
  rw [hembed]
  -- The [0,1) representative of (l - k).val / N is itself (since (l-k).val ∈ [0, N-1])
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hval_lt : (l - k).val < N := ZMod.val_lt (l - k)
  have hval_nonneg : 0 ≤ ((l - k).val : ℝ) / N := by positivity
  have hval_lt_one : ((l - k).val : ℝ) / N < 1 := by
    rw [div_lt_one hN_pos]
    exact_mod_cast hval_lt
  have hmem : ((l - k).val : ℝ) / N ∈ Set.Ico (0 : ℝ) 1 := ⟨hval_nonneg, hval_lt_one⟩
  have hequiv := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ))
    (x := ((l - k).val : ℝ) / N) (by simpa using hmem)
  exact congrArg Subtype.val hequiv

/-- repFrom to the cyclic successor in equidistant points equals 1/N (when N ≥ 2). -/
lemma repFrom_equidistant_successor (N : ℕ) [NeZero N] (hN : 2 ≤ N)
    (y : Circle) (k : ZMod N) :
    repFrom (y + embedZMod N k) (y + embedZMod N (k + 1)) = 1 / N := by
  rw [repFrom_equidistant]
  simp only [add_sub_cancel_left]
  -- (1 : ZMod N).val = 1 when N ≥ 2
  haveI : Fact (1 < N) := ⟨hN⟩
  have hval : (1 : ZMod N).val = 1 := ZMod.val_one N
  rw [hval, Nat.cast_one]

/-- repFrom to the cyclic predecessor in equidistant points equals (N-1)/N. -/
lemma repFrom_equidistant_predecessor (N : ℕ) [NeZero N] (y : Circle) (k : ZMod N) :
    repFrom (y + embedZMod N k) (y + embedZMod N (k - 1)) = (N - 1) / N := by
  rw [repFrom_equidistant]
  -- (k - 1) - k = -1 in ZMod N
  have hsub : (k - 1) - k = -1 := by ring
  rw [hsub]
  -- (-1 : ZMod N).val = N - 1
  have hN_pos : 0 < N := NeZero.pos N
  have hval : (-1 : ZMod N).val = N - 1 := by
    rw [ZMod.neg_val]
    split_ifs with h
    · -- (1 : ZMod N) = 0 means N = 1 by ZMod.one_eq_zero_iff
      have hN1 : N = 1 := ZMod.one_eq_zero_iff.mp h
      simp [hN1]
    · -- N ≥ 2: (1 : ZMod N).val = 1
      have hN_gt : 1 < N := by
        by_contra hle; push_neg at hle
        have hN1 : N = 1 := le_antisymm hle (NeZero.pos N)
        subst hN1
        exact h rfl
      have hvaleq : (1 : ZMod N).val = 1 := by
        have : ((1 : ℕ) : ZMod N).val = 1 := ZMod.val_natCast_of_lt hN_gt
        simp only [Nat.cast_one] at this
        exact this
      rw [hvaleq]
  rw [hval]
  -- Now: ↑(N - 1) / ↑N = (↑N - 1) / ↑N
  have h1le : 1 ≤ N := hN_pos
  simp only [Nat.cast_sub h1le, Nat.cast_one]

/-- The minimum positive repFrom in equidistant points is 1/N. -/
lemma repFrom_equidistant_min (N : ℕ) [NeZero N] (y : Circle) (k l : ZMod N)
    (hne : l ≠ k) :
    (1 : ℝ) / N ≤ repFrom (y + embedZMod N k) (y + embedZMod N l) := by
  rw [repFrom_equidistant]
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hval_pos : 0 < (l - k).val := by
    by_contra h; push_neg at h
    simp only [Nat.le_zero, ZMod.val_eq_zero] at h
    have : l - k = 0 := h
    have : l = k := sub_eq_zero.mp this
    exact hne this
  have h1 : (1 : ℝ) ≤ (l - k).val := by exact_mod_cast hval_pos
  exact div_le_div_of_nonneg_right h1 (le_of_lt hN_pos)

/-- The maximum repFrom in equidistant points is (N-1)/N. -/
lemma repFrom_equidistant_max (N : ℕ) [NeZero N] (y : Circle) (k l : ZMod N) :
    repFrom (y + embedZMod N k) (y + embedZMod N l) ≤ (N - 1) / N := by
  rw [repFrom_equidistant]
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hN_pos' : 0 < N := NeZero.pos N
  have hval_lt : (l - k).val < N := ZMod.val_lt (l - k)
  have hval_le : (l - k).val ≤ N - 1 := by omega
  have h1 : ((l - k).val : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast hval_le
  have h2 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have : 1 ≤ N := hN_pos'
    simp only [Nat.cast_sub this, Nat.cast_one]
  calc ((l - k).val : ℝ) / N ≤ ((N - 1 : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right h1 (le_of_lt hN_pos)
    _ = (N - 1 : ℝ) / N := by rw [h2]

/-- For distinct points u ≠ x, the clockwise and counterclockwise arcs sum to 1. -/
lemma repFrom_add_repFrom_eq_one (u x : Circle) (hxu : x ≠ u) :
    repFrom u x + repFrom x u = 1 := by
  -- The key: (x - u) + (u - x) = 0 in Circle, and for a nonzero element y,
  -- the representatives of y and -y in [0, 1) sum to 1.
  have hr := repFrom_pos_of_ne u x hxu
  simp only [repFrom]
  set r := (AddCircle.equivIco 1 0 (x - u)).val
  have hr_pos : 0 < r := hr
  have hr_lt : r < 1 := by simpa using (AddCircle.equivIco 1 0 (x - u)).prop.2
  have h_neg : (u - x : Circle) = -(x - u) := by abel
  rw [h_neg]
  -- (x - u) has representative r in (0, 1)
  have h_coe : (x - u : Circle) = (r : Circle) := by
    have := (AddCircle.equivIco 1 0).symm_apply_apply (x - u)
    simp only [AddCircle.equivIco] at this
    exact this.symm
  -- -(x - u) = (1 - r : Circle) since adding 1 doesn't change Circle element
  have h_neg_coe : (-(x - u) : Circle) = ((1 - r : ℝ) : Circle) := by
    rw [h_coe]
    -- In AddCircle 1, (1 : ℝ) maps to 0, so -(r : Circle) = (-r + 1 : Circle) = (1 - r : Circle)
    have hperiod : ((1 : ℝ) : Circle) = 0 := AddCircle.coe_period 1
    have h1 : ((-r : ℝ) : Circle) + ((1 : ℝ) : Circle) = (((-r + 1 : ℝ)) : Circle) := by
      rw [← AddCircle.coe_add]
    rw [hperiod, add_zero] at h1
    have h2 : ((-r + 1 : ℝ) : Circle) = ((1 - r : ℝ) : Circle) := by ring_nf
    calc (-((r : ℝ) : Circle)) = ((-r : ℝ) : Circle) := by rfl
      _ = (((-r + 1 : ℝ)) : Circle) := h1
      _ = ((1 - r : ℝ) : Circle) := h2
  rw [h_neg_coe]
  have h_mem : 1 - r ∈ Set.Ico (0 : ℝ) (0 + 1) := by simp; constructor <;> linarith
  have h_eq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := 1 - r) h_mem
  have h_val : (AddCircle.equivIco 1 0 ((1 - r : ℝ) : Circle)).val = 1 - r := by
    exact congrArg Subtype.val h_eq
  linarith

/-- Arc addition: if b is "between" a and c (clockwise), then
    repFrom a c = repFrom a b + repFrom b c.
    The condition is that repFrom a b + repFrom b c < 1 (no wrap-around). -/
lemma repFrom_add (a b c : Circle) (hab : a ≠ b) (hbc : b ≠ c)
    (h_no_wrap : repFrom a b + repFrom b c < 1) :
    repFrom a c = repFrom a b + repFrom b c := by
  -- Key: (c - a) = (c - b) + (b - a) as Circle elements
  -- Since repFrom a b + repFrom b c < 1, the sum of representatives doesn't wrap
  set r1 := repFrom a b with hr1_def
  set r2 := repFrom b c with hr2_def
  have hr1_pos : 0 < r1 := repFrom_pos_of_ne a b hab.symm
  have hr2_pos : 0 < r2 := repFrom_pos_of_ne b c hbc.symm
  have hr1_lt : r1 < 1 := repFrom_lt_one a b
  have hr2_lt : r2 < 1 := repFrom_lt_one b c
  have hsum_pos : 0 < r1 + r2 := by linarith
  have hsum_lt : r1 + r2 < 1 := h_no_wrap
  -- The representative of (c - a) is r1 + r2
  simp only [repFrom]
  -- (c - a) = (c - b) + (b - a) in Circle
  have h_split : c - a = (c - b) + (b - a) := by abel
  rw [h_split]
  -- (b - a) has representative r1, (c - b) has representative r2
  have h_ba : (b - a : Circle) = (r1 : Circle) := by
    have := (AddCircle.equivIco 1 0).symm_apply_apply (b - a)
    simp only [AddCircle.equivIco, hr1_def, repFrom] at this ⊢
    exact this.symm
  have h_cb : (c - b : Circle) = (r2 : Circle) := by
    have := (AddCircle.equivIco 1 0).symm_apply_apply (c - b)
    simp only [AddCircle.equivIco, hr2_def, repFrom] at this ⊢
    exact this.symm
  rw [h_ba, h_cb]
  -- (r2 : Circle) + (r1 : Circle) = ((r1 + r2) : Circle)
  have h_sum_cast : (r2 : Circle) + (r1 : Circle) = ((r1 + r2 : ℝ) : Circle) := by
    have h1 : (r1 : Circle) + (r2 : Circle) = ((r1 + r2 : ℝ) : Circle) := by
      simp only [← AddCircle.coe_add]
    rw [add_comm (r2 : Circle) (r1 : Circle), h1]
  rw [h_sum_cast]
  -- Since r1 + r2 ∈ [0, 1), its representative is itself
  have h_mem : r1 + r2 ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨le_of_lt hsum_pos, by simpa⟩
  have h_eq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := r1 + r2) h_mem
  exact congrArg Subtype.val h_eq

/-- Corollary: arc subtraction. If c is between a and b, then
    repFrom c b = repFrom a b - repFrom a c. -/
lemma repFrom_sub (a b c : Circle) (hac : a ≠ c) (hcb : c ≠ b)
    (h_between : repFrom a c + repFrom c b < 1) :
    repFrom c b = repFrom a b - repFrom a c := by
  have hadd := repFrom_add a c b hac hcb h_between
  linarith

/-- Key arc property: If b is "between" a and c on the short arc (repFrom a b ≤ repFrom a c < 1/2),
    then repFrom b c = repFrom a c - repFrom a b.
    This follows because on a half-circle, arc arithmetic is well-behaved. -/
lemma repFrom_between (a b c : Circle) (_hab : a ≠ b) (_hbc : b ≠ c)
    (h_ab_le_ac : repFrom a b ≤ repFrom a c) (h_ac_lt_half : repFrom a c < 1 / 2) :
    repFrom b c = repFrom a c - repFrom a b := by
  -- Key: Since repFrom a c < 1/2, both b and c are in the "forward half" from a
  -- This means the clockwise arc from b to c has length repFrom a c - repFrom a b
  -- and this doesn't wrap around since the total is < 1/2 < 1
  --
  -- Proof outline:
  -- 1. repFrom a b ≤ repFrom a c < 1/2 means 0 ≤ repFrom a b < 1/2
  -- 2. The arc a -> b has representative repFrom a b in [0, 1/2)
  -- 3. The arc a -> c has representative repFrom a c in [0, 1/2)
  -- 4. In AddCircle: c - a = (repFrom a c : Circle), b - a = (repFrom a b : Circle)
  -- 5. So c - b = (c - a) - (b - a) = (repFrom a c - repFrom a b : Circle)
  -- 6. Since repFrom a c - repFrom a b ∈ [0, 1/2), its representative is itself
  set r_ab := repFrom a b with hr_ab_def
  set r_ac := repFrom a c with hr_ac_def
  have hr_ab_nonneg : 0 ≤ r_ab := repFrom_nonneg a b
  have hr_ac_nonneg : 0 ≤ r_ac := repFrom_nonneg a c
  have hr_diff_nonneg : 0 ≤ r_ac - r_ab := by linarith
  have hr_diff_lt_one : r_ac - r_ab < 1 := by linarith [h_ac_lt_half]
  -- (b - a) has representative r_ab
  have h_ba : (b - a : Circle) = (r_ab : Circle) := by
    have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (b - a)
    rw [← h1]
    simp only [repFrom, hr_ab_def]
    rfl
  -- (c - a) has representative r_ac
  have h_ca : (c - a : Circle) = (r_ac : Circle) := by
    have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (c - a)
    rw [← h1]
    simp only [repFrom, hr_ac_def]
    rfl
  -- (c - b) = (c - a) - (b - a) = r_ac - r_ab in Circle
  have h_cb : (c - b : Circle) = ((r_ac - r_ab : ℝ) : Circle) := by
    calc (c - b : Circle) = (c - a) - (b - a) := by abel
      _ = (r_ac : Circle) - (r_ab : Circle) := by rw [h_ca, h_ba]
      _ = ((r_ac - r_ab : ℝ) : Circle) := by rw [← QuotientAddGroup.mk_sub]
  -- Since r_ac - r_ab ∈ [0, 1), its representative is itself
  have h_mem : r_ac - r_ab ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simp only [Set.mem_Ico, zero_add]
    exact ⟨hr_diff_nonneg, hr_diff_lt_one⟩
  have h_eq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := r_ac - r_ab) h_mem
  simp only [repFrom, h_cb]
  exact congrArg Subtype.val h_eq

/-- Arc subtraction with ordering: when b is between a and c (repFrom a b ≤ repFrom a c),
    then repFrom b c = repFrom a c - repFrom a b.
    Weaker precondition than repFrom_between: no < 1/2 constraint needed.

    Key insight: Since repFrom values are in [0, 1), and repFrom a b ≤ repFrom a c,
    the difference repFrom a c - repFrom a b is in [0, 1), so no wrap-around occurs. -/
lemma repFrom_ordered (a b c : Circle) (h_ab_le_ac : repFrom a b ≤ repFrom a c) :
    repFrom b c = repFrom a c - repFrom a b := by
  set r_ab := repFrom a b with hr_ab_def
  set r_ac := repFrom a c with hr_ac_def
  have hr_ab_nonneg : 0 ≤ r_ab := repFrom_nonneg a b
  have hr_ac_lt_one : r_ac < 1 := repFrom_lt_one a c
  -- r_ac - r_ab ∈ [0, 1)
  have hr_diff_nonneg : 0 ≤ r_ac - r_ab := by linarith
  have hr_diff_lt_one : r_ac - r_ab < 1 := by linarith
  -- (b - a) has representative r_ab
  have h_ba : (b - a : Circle) = (r_ab : Circle) := by
    have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (b - a)
    rw [← h1]
    simp only [repFrom, hr_ab_def]
    rfl
  -- (c - a) has representative r_ac
  have h_ca : (c - a : Circle) = (r_ac : Circle) := by
    have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (c - a)
    rw [← h1]
    simp only [repFrom, hr_ac_def]
    rfl
  -- (c - b) = (c - a) - (b - a) = r_ac - r_ab in Circle
  have h_cb : (c - b : Circle) = ((r_ac - r_ab : ℝ) : Circle) := by
    calc (c - b : Circle) = (c - a) - (b - a) := by abel
      _ = (r_ac : Circle) - (r_ab : Circle) := by rw [h_ca, h_ba]
      _ = ((r_ac - r_ab : ℝ) : Circle) := by rw [← QuotientAddGroup.mk_sub]
  -- Since r_ac - r_ab ∈ [0, 1), its representative is itself
  have h_mem : r_ac - r_ab ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simp only [Set.mem_Ico, zero_add]
    exact ⟨hr_diff_nonneg, hr_diff_lt_one⟩
  have h_eq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := r_ac - r_ab) h_mem
  simp only [repFrom, h_cb]
  exact congrArg Subtype.val h_eq

/-- When shifting the base point by δ (where 0 < δ < 1), repFrom changes predictably.
    If repFrom u x ≥ δ, then repFrom (u + δ) x = repFrom u x - δ (no wrap-around).

    Proof idea: repFrom u x = r means (x - u) has representative r in [0, 1).
    Then x - (u + δ) = (x - u) - δ has representative r - δ (since r ≥ δ, no wrap).
    So repFrom (u + δ) x = r - δ = repFrom u x - δ. -/
lemma repFrom_shift_no_wrap (u x : Circle) (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_one : δ < 1)
    (h_ge : δ ≤ repFrom u x) :
    repFrom (u + (δ : Circle)) x = repFrom u x - δ := by
  -- Key: x - (u + δ) = (x - u) - δ, and if repFrom u x ≥ δ, subtracting δ doesn't wrap
  set r := repFrom u x with hr_def
  -- r is in [0, 1)
  have hr_ge : 0 ≤ r := repFrom_nonneg u x
  have hr_lt : r < 1 := repFrom_lt_one u x
  -- r - δ ∈ [0, 1) since r ≥ δ and r < 1
  have h_sub_nonneg : 0 ≤ r - δ := by linarith
  have h_sub_lt : r - δ < 1 := by linarith
  have h_sub_mem : r - δ ∈ Set.Ico (0 : ℝ) 1 := ⟨h_sub_nonneg, h_sub_lt⟩
  -- Rewrite repFrom as equivIco
  simp only [repFrom]
  -- x - (u + δ) = (x - u) - δ in Circle
  have h1 : x - (u + (δ : Circle)) = (x - u) - (δ : Circle) := by
    simp only [sub_add_eq_sub_sub]
  rw [h1]
  -- The representative of (x - u) is r
  have hr_eq : (AddCircle.equivIco 1 0 (x - u)).val = r := by
    simp only [repFrom] at hr_def
    exact hr_def
  -- In Circle: (x - u) - δ = (r : Circle) - (δ : Circle) = ((r - δ) : Circle)
  -- We need: equivIco ((x - u) - δ) = equivIco (r - δ) when r ≥ δ
  -- First, show (x - u) = (r : Circle) using that r is its representative
  have h_xu_coe : (x - u : Circle) = (r : Circle) := by
    -- equivIco.symm gives back the coercion of the value
    have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (x - u)
    rw [← h1]
    -- symm of equivIco applied to ⟨v, hv⟩ gives (v : Circle)
    -- The key: equivIco.symm ⟨v, hv⟩ = (v : Circle) by definition
    have h2 : (AddCircle.equivIco 1 0).symm (AddCircle.equivIco 1 0 (x - u)) =
              ((AddCircle.equivIco 1 0 (x - u)).val : Circle) := rfl
    rw [h2, hr_eq]
  -- Now (x - u) - δ = r - δ in Circle
  rw [h_xu_coe]
  -- equivIco (↑(r - δ)) = ⟨r - δ, _⟩ since r - δ ∈ [0, 1)
  have h_mem : r - δ ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using h_sub_mem
  have h_eq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := r - δ) h_mem
  -- Need to convert ↑r - ↑δ to ↑(r - δ)
  simp only [← QuotientAddGroup.mk_sub] at h_eq ⊢
  rw [h_eq]

/-- When shifting the base point by δ and repFrom u x < δ, there's wrap-around.
    repFrom (u + δ) x = repFrom u x - δ + 1 ≥ 1 - δ.

    Proof idea: repFrom u x = r < δ means (x - u) has representative r in [0, δ).
    Then x - (u + δ) = (x - u) - δ, and r - δ ∈ (-δ, 0), so mod 1 gives r - δ + 1 ∈ (1-δ, 1).
    So repFrom (u + δ) x ≥ 1 - δ. -/
lemma repFrom_shift_wrap_lower (u x : Circle) (δ : ℝ) (_hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h_lt : repFrom u x < δ) :
    1 - δ ≤ repFrom (u + (δ : Circle)) x := by
  -- Similar structure to repFrom_shift_no_wrap, but for the wrap-around case
  set r := repFrom u x with hr_def
  have hr_ge : 0 ≤ r := repFrom_nonneg u x
  have hr_lt : r < 1 := repFrom_lt_one u x
  -- Since r < δ, we have r - δ ∈ (-δ, 0), so r - δ + 1 ∈ (1-δ, 1) ⊆ [0, 1)
  have h_wrap_nonneg : 0 ≤ r - δ + 1 := by linarith
  have h_wrap_lt : r - δ + 1 < 1 := by linarith
  have h_wrap_mem : r - δ + 1 ∈ Set.Ico (0 : ℝ) 1 := ⟨h_wrap_nonneg, h_wrap_lt⟩
  -- x - u = (r : Circle)
  have hr_eq : (AddCircle.equivIco 1 0 (x - u)).val = r := by
    simp only [repFrom] at hr_def
    exact hr_def
  have h_xu_coe : (x - u : Circle) = (r : Circle) := by
    have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (x - u)
    rw [← h1]
    have h2 : (AddCircle.equivIco 1 0).symm (AddCircle.equivIco 1 0 (x - u)) =
              ((AddCircle.equivIco 1 0 (x - u)).val : Circle) := rfl
    rw [h2, hr_eq]
  -- x - (u + δ) = (x - u) - δ = (r : Circle) - (δ : Circle) = ((r - δ) : Circle)
  simp only [repFrom]
  have h1 : x - (u + (δ : Circle)) = (x - u) - (δ : Circle) := by simp only [sub_add_eq_sub_sub]
  rw [h1, h_xu_coe]
  -- (r - δ : Circle) = ((r - δ + 1) : Circle) since they differ by 1
  -- Show (r : Circle) - (δ : Circle) = ((r - δ + 1) : Circle)
  have h_mod1 : (r : Circle) - (δ : Circle) = (((r - δ + 1) : ℝ) : Circle) := by
    -- ↑r - ↑δ = ↑(r - δ) = ↑(r - δ + 1) (mod 1)
    rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq]
    simp only [AddSubgroup.mem_zmultiples_iff]
    use 1
    ring
  rw [h_mod1]
  -- equivIco (↑(r - δ + 1)) = ⟨r - δ + 1, _⟩ since r - δ + 1 ∈ [0, 1)
  have h_mem : r - δ + 1 ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using h_wrap_mem
  have h_eq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := r - δ + 1) h_mem
  rw [h_eq]
  -- r - δ + 1 ≥ 1 - δ iff r ≥ 0, which is true
  linarith

lemma exists_min_repFrom (S : Finset Circle) (u : Circle) (hu : u ∈ S)
    (hcard : 1 < S.card) :
    ∃ v ∈ S, v ≠ u ∧ ∀ w ∈ S, w ≠ u → repFrom u v ≤ repFrom u w := by
  classical
  have hnontriv : S.Nontrivial := (Finset.one_lt_card_iff_nontrivial).1 hcard
  have hnonempty : (S.erase u).Nonempty :=
    (Finset.erase_nonempty (s := S) (a := u) hu).2 hnontriv
  let T : Finset ℝ := (S.erase u).image (fun x => repFrom u x)
  have hT_nonempty : T.Nonempty := by
    rcases hnonempty with ⟨v, hv⟩
    refine ⟨repFrom u v, ?_⟩
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  let r := T.min' hT_nonempty
  have hr_mem : r ∈ T := Finset.min'_mem T hT_nonempty
  rcases Finset.mem_image.mp hr_mem with ⟨v, hv, hv_eq⟩
  have hv_ne : v ≠ u := (Finset.mem_erase.mp hv).1
  have hvS : v ∈ S := (Finset.mem_erase.mp hv).2
  refine ⟨v, hvS, hv_ne, ?_⟩
  intro w hwS hwu
  have hw : w ∈ S.erase u := by
    simp [Finset.mem_erase, hwS, hwu]
  have hwT : repFrom u w ∈ T := Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hminall : ∀ b ∈ T, r ≤ b := by
    have hmin :=
      (Finset.min'_eq_iff (s := T) (H := hT_nonempty) (a := r)).1 rfl
    exact hmin.2
  have hmin : r ≤ repFrom u w := hminall _ hwT
  simpa [hv_eq] using hmin

/-! ### Cyclic Order Infrastructure for Slot Argument -/

/-- Cyclic successor of u in S: the element of S \ {u} with smallest positive repFrom u.
    This is the "next" element clockwise from u in the cyclic order on Circle. -/
noncomputable def cyclicSucc (S : Finset Circle) (u : Circle) (hu : u ∈ S) (hS : 2 ≤ S.card) :
    Circle :=
  -- S \ {u} is nonempty since |S| ≥ 2
  have hne : (S.erase u).Nonempty := by
    have hcard : 1 ≤ (S.erase u).card := by
      rw [Finset.card_erase_of_mem hu]
      omega
    exact Finset.card_pos.mp hcard
  let T := (S.erase u).image (fun x => repFrom u x)
  have hTne : T.Nonempty := Finset.Nonempty.image hne _
  let minR := T.min' hTne
  (Finset.mem_image.mp (Finset.min'_mem T hTne)).choose

/-- Cyclic predecessor of u in S: the element of S \ {u} with largest repFrom u.
    This is the "previous" element clockwise from u in the cyclic order on Circle.
    Note: repFrom u (cyclicPred) is closest to 1 (from below). -/
noncomputable def cyclicPred (S : Finset Circle) (u : Circle) (hu : u ∈ S) (hS : 2 ≤ S.card) :
    Circle :=
  have hne : (S.erase u).Nonempty := by
    have hcard : 1 ≤ (S.erase u).card := by
      rw [Finset.card_erase_of_mem hu]
      omega
    exact Finset.card_pos.mp hcard
  let T := (S.erase u).image (fun x => repFrom u x)
  have hTne : T.Nonempty := Finset.Nonempty.image hne _
  let maxR := T.max' hTne
  (Finset.mem_image.mp (Finset.max'_mem T hTne)).choose

/-- Distance on Circle is at most the clockwise arc length (repFrom).
    This follows because dist is the minimum of clockwise and counterclockwise arc lengths. -/
lemma dist_le_repFrom (u x : Circle) : dist u x ≤ repFrom u x := by
  -- dist u x = ‖u - x‖ = ‖x - u‖ on AddCircle (norm is symmetric)
  -- repFrom u x = representative of (x - u) in [0, 1)
  -- ‖y‖ = min(rep, 1 - rep) where rep is the [0,1) representative
  rw [dist_eq_norm, ← norm_neg (u - x)]
  simp only [neg_sub]
  set r := repFrom u x with hr_def
  have hr_ge : 0 ≤ r := repFrom_nonneg u x
  have hr_lt : r < 1 := repFrom_lt_one u x
  -- (x - u : Circle) = (r : Circle) since r is the representative
  have h_coe : (x - u : Circle) = (r : Circle) := by
    have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (x - u)
    simp only [AddCircle.equivIco] at h1
    rw [← h1]
    simp only [repFrom] at hr_def
    rfl
  rw [h_coe, UnitAddCircle.norm_eq]
  -- Need: |r - round r| ≤ r
  -- Since r ∈ [0, 1):
  --   if r ∈ [0, 0.5), round r = 0, so |r - 0| = r ≤ r ✓
  --   if r ∈ [0.5, 1), round r = 1, so |r - 1| = 1 - r ≤ r since r ≥ 0.5 ✓
  by_cases hr_half : r < 1/2
  · -- r < 0.5, so round r = 0
    have h_round : round r = 0 := by
      rw [round_eq_zero_iff]
      constructor <;> linarith
    simp only [h_round, Int.cast_zero, sub_zero, abs_of_nonneg hr_ge, le_refl]
  · -- r ≥ 0.5, so round r = 1 and |r - 1| = 1 - r ≤ r
    push_neg at hr_half
    have h_round : round r = 1 := by
      -- r ∈ [1/2, 1) means floor(r + 1/2) = 1
      rw [round_eq]
      have h : ⌊r + 1/2⌋ = 1 := by
        rw [Int.floor_eq_iff]
        simp only [Int.cast_one]
        constructor <;> linarith
      exact h
    simp only [h_round, Int.cast_one]
    rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 1 - r)]
    linarith

/-- When repFrom u x ≤ 1/2, the metric distance equals the clockwise arc length. -/
lemma dist_eq_repFrom_of_le_half (u x : Circle) (h : repFrom u x ≤ 1 / 2) :
    dist u x = repFrom u x := by
  rw [dist_eq_norm, ← norm_neg (u - x)]
  simp only [neg_sub]
  set r := repFrom u x with hr_def
  have hr_ge : 0 ≤ r := repFrom_nonneg u x
  have hr_lt : r < 1 := repFrom_lt_one u x
  have h_coe : (x - u : Circle) = (r : Circle) := by
    have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (x - u)
    simp only [AddCircle.equivIco] at h1
    rw [← h1]
    simp only [repFrom] at hr_def
    rfl
  rw [h_coe, UnitAddCircle.norm_eq]
  by_cases hr_half : r < 1/2
  · have h_round : round r = 0 := by
      rw [round_eq_zero_iff]
      constructor <;> linarith
    simp only [h_round, Int.cast_zero, sub_zero, abs_of_nonneg hr_ge]
  · -- r = 1/2 (since r ≤ 1/2 and ¬(r < 1/2))
    have hr_eq : r = 1/2 := le_antisymm h (not_lt.mp hr_half)
    have h_round : round r = 1 := by
      rw [round_eq]
      have hfl : ⌊r + 1/2⌋ = 1 := by
        rw [Int.floor_eq_iff]
        simp only [Int.cast_one]
        constructor <;> linarith
      exact hfl
    simp only [h_round, Int.cast_one]
    rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 1 - r)]
    linarith

/-- The slot width of u in S is the arc length from cyclicPred to cyclicSucc passing through u.
    This equals: repFrom (cyclicPred) (cyclicSucc) - repFrom (cyclicPred) u
                = repFrom (cyclicPred) (cyclicSucc) - (1 - repFrom u (cyclicPred))
    Simplified: 1 - repFrom u (cyclicPred) + repFrom u (cyclicSucc)
              = gap_left + gap_right where gap_left = 1 - repFrom u (cyclicPred)
                                        and gap_right = repFrom u (cyclicSucc) -/
noncomputable def slotWidth (S : Finset Circle) (u : Circle) (hu : u ∈ S) (hS : 2 ≤ S.card) : ℝ :=
  let succ := cyclicSucc S u hu hS
  let pred := cyclicPred S u hu hS
  -- gap from pred to u (going clockwise, i.e., 1 - repFrom u pred)
  -- gap from u to succ (going clockwise, i.e., repFrom u succ)
  -- Total slot width = (1 - repFrom u pred) + repFrom u succ
  (1 - repFrom u pred) + repFrom u succ

/-- Key lemma: If x is in the slot of u (between cyclicPred and cyclicSucc),
    then dist(u, x) ≤ slotWidth. -/
lemma dist_le_slotWidth_of_in_slot (S : Finset Circle) (u : Circle)
    (hu : u ∈ S) (hS : 2 ≤ S.card) (x : Circle)
    (hx_in_slot : repFrom (cyclicPred S u hu hS) x <
      repFrom (cyclicPred S u hu hS) (cyclicSucc S u hu hS)) :
    dist u x ≤ slotWidth S u hu hS := by
  -- The slot is the arc from pred to succ containing u.
  -- Uses the universal bound dist ≤ 1/2 combined with dist_le_repFrom.
  set pred := cyclicPred S u hu hS with hpred_def
  set succ := cyclicSucc S u hu hS with hsucc_def
  simp only [slotWidth]
  -- dist(u, x) ≤ 1/2 always on AddCircle 1
  have hdist_le_half : dist u x ≤ 1/2 := circleDistance_le_half u x
  -- slotWidth ≥ 0 and we need a lower bound
  -- Case split: is slotWidth ≥ 1/2? If so, use hdist_le_half directly
  by_cases hslot_large : 1/2 ≤ (1 - repFrom u pred) + repFrom u succ
  · linarith
  · -- slotWidth < 1/2, need tighter analysis
    -- In this case, the slot is "small", meaning pred and succ are close to u
    push_neg at hslot_large
    -- Case split on direction of x from u
    by_cases hcase : repFrom u x ≤ repFrom u succ
    · -- x is "clockwise" from u, in arc [u, succ]
      calc dist u x ≤ repFrom u x := dist_le_repFrom u x
        _ ≤ repFrom u succ := hcase
        _ ≤ (1 - repFrom u pred) + repFrom u succ := by
            linarith [repFrom_nonneg u pred, repFrom_lt_one u pred]
    · -- x is "counterclockwise" from u (repFrom u x > repFrom u succ)
      push_neg at hcase
      -- Key insight: x is in [pred, succ) but NOT in [u, succ]
      -- (since repFrom u x > repFrom u succ).
      -- Therefore x must be in [pred, u].
      -- For such x, dist u x ≤ repFrom x u ≤ repFrom pred u = 1 - repFrom u pred ≤ slotWidth.
      by_cases hxu : x = u
      · -- x = u: trivial
        rw [hxu, _root_.dist_self]
        linarith [repFrom_nonneg u pred, repFrom_nonneg u succ, repFrom_lt_one u pred]
      · -- x ≠ u
        have hdist_comm : dist u x = dist x u := dist_comm u x
        have hdist_le_xu : dist x u ≤ repFrom x u := dist_le_repFrom x u
        have hsum : repFrom u x + repFrom x u = 1 := repFrom_add_repFrom_eq_one u x hxu
        have hpred_ne_u : pred ≠ u := by
          simp only [cyclicPred, hpred_def] at *
          have hne : (S.erase u).Nonempty := by
            have hcard : 1 ≤ (S.erase u).card := by
              rw [Finset.card_erase_of_mem hu]; omega
            exact Finset.card_pos.mp hcard
          have hmax_mem := Finset.max'_mem ((S.erase u).image (fun x => repFrom u x))
            (Finset.Nonempty.image hne _)
          have hchoose_mem := (Finset.mem_image.mp hmax_mem).choose_spec.1
          exact (Finset.mem_erase.mp hchoose_mem).1
        have hsum_pred : repFrom u pred + repFrom pred u = 1 :=
          repFrom_add_repFrom_eq_one u pred hpred_ne_u
        have h_pred_u : repFrom pred u = 1 - repFrom u pred := by linarith
        -- Key fact: x is in [pred, u], so repFrom x u ≤ repFrom pred u
        -- This requires detailed arc geometry on the circle
        -- The key insight: slot < 1/2 means all points are in a half-circle,
        -- where repFrom behaves monotonically
        have h_xu_bound : repFrom x u ≤ repFrom pred u := by
          -- x is in [pred, succ) (from hx_in_slot) but NOT in [u, succ) (from hcase)
          -- Therefore x is in [pred, u]
          -- repFrom x u ≤ repFrom pred u follows from arc monotonicity in a half-circle
          --
          -- Key facts:
          -- 1. slotWidth = repFrom pred u + repFrom u succ < 1/2 (from hslot_large)
          -- 2. repFrom pred x < repFrom pred succ (from hx_in_slot)
          -- 3. repFrom u x > repFrom u succ (from hcase)
          --
          -- Proof by contradiction: Assume x is in (u, succ] instead of [pred, u]
          -- Then repFrom pred x = repFrom pred u + repFrom u x (arc addition)
          -- Since repFrom u x > repFrom u succ:
          --   repFrom pred x > repFrom pred u + repFrom u succ = repFrom pred succ
          -- This contradicts repFrom pred x < repFrom pred succ.
          -- So x must be in [pred, u], and repFrom x u ≤ repFrom pred u follows.

          -- First establish that pred, u, succ are in clockwise order with no wrap
          have hpred_ne_succ : pred ≠ succ := by
            intro heq
            -- If pred = succ, then the slot has width (1 - repFrom u pred) + repFrom u succ
            -- = (1 - repFrom u pred) + repFrom u pred = 1 (using heq)
            -- But slotWidth < 1/2, contradiction
            have heq_slot : (1 - repFrom u pred) + repFrom u succ = 1 := by
              rw [← heq]; ring
            linarith
          -- slot < 1/2 means repFrom pred succ < 1 (so arc addition applies)
          have hslot_sum : repFrom pred u + repFrom u succ < 1 := by
            -- slotWidth = (1 - repFrom u pred) + repFrom u succ
            -- 1 - repFrom u pred = repFrom pred u (since pred ≠ u)
            have hsum : repFrom u pred + repFrom pred u = 1 :=
              repFrom_add_repFrom_eq_one u pred hpred_ne_u
            have h_pred_u : 1 - repFrom u pred = repFrom pred u := by linarith
            rw [← h_pred_u]
            linarith
          -- By arc addition: repFrom pred succ = repFrom pred u + repFrom u succ
          have hsucc_ne_u : succ ≠ u := by
            simp only [cyclicSucc] at hsucc_def
            have hne : (S.erase u).Nonempty := by
              have hcard : 1 ≤ (S.erase u).card := by
                rw [Finset.card_erase_of_mem hu]; omega
              exact Finset.card_pos.mp hcard
            let T := (S.erase u).image (fun x => repFrom u x)
            have hTne : T.Nonempty := Finset.Nonempty.image hne _
            have hmin_mem := Finset.min'_mem T hTne
            have hmin_spec := (Finset.mem_image.mp hmin_mem).choose_spec
            exact (Finset.mem_erase.mp hmin_spec.1).1
          have hpred_succ_add : repFrom pred succ = repFrom pred u + repFrom u succ := by
            exact repFrom_add pred u succ hpred_ne_u hsucc_ne_u.symm hslot_sum
          -- Now prove x is in [pred, u] by contradiction
          -- Assume x is past u (in the arc (u, succ])
          by_cases hx_past_u : repFrom pred u < repFrom pred x
          · -- x is past u, so x is in (u, succ]
            -- Then repFrom pred x = repFrom pred u + repFrom u x (if no wrap)
            have hx_ne_u : x ≠ u := by
              intro heq; rw [heq] at hx_past_u
              exact (lt_irrefl _ hx_past_u)
            have hx_ne_pred : x ≠ pred := by
              intro heq; rw [heq, repFrom_self] at hx_past_u
              have := repFrom_nonneg pred u
              linarith
            -- Arc from pred to x doesn't wrap since repFrom pred x < repFrom pred succ < 1
            have hpred_x_lt : repFrom pred x < 1 := by
              calc repFrom pred x < repFrom pred succ := hx_in_slot
                _ = repFrom pred u + repFrom u succ := hpred_succ_add
                _ < 1 := hslot_sum
            -- Arc addition: repFrom u x = repFrom pred x - repFrom pred u (since pred -> u -> x)
            -- Key: repFrom pred u < repFrom pred x means u is "before" x from pred's view
            have h_arc_no_wrap : repFrom pred u + repFrom u x < 1 := by
              -- Use repFrom_between: u is between pred and x
              -- repFrom pred u < repFrom pred x < repFrom pred succ < 1/2
              -- So repFrom u x = repFrom pred x - repFrom pred u
              -- And repFrom pred u + repFrom u x = repFrom pred x < 1
              have h_pred_x_lt_half : repFrom pred x < 1/2 := by
                calc repFrom pred x < repFrom pred succ := hx_in_slot
                  _ = repFrom pred u + repFrom u succ := hpred_succ_add
                  _ < 1/2 := by
                    have hslot_bound : (1 - repFrom u pred) + repFrom u succ < 1/2 := hslot_large
                    have hsum : repFrom u pred + repFrom pred u = 1 :=
                      repFrom_add_repFrom_eq_one u pred hpred_ne_u
                    have h_swap : 1 - repFrom u pred = repFrom pred u := by linarith
                    linarith
              have h_u_le_x : repFrom pred u ≤ repFrom pred x := le_of_lt hx_past_u
              have h_between := repFrom_between pred u x hpred_ne_u hx_ne_u.symm
                h_u_le_x h_pred_x_lt_half
              -- h_between : repFrom u x = repFrom pred x - repFrom pred u
              linarith
            have h_pred_x_add : repFrom pred x = repFrom pred u + repFrom u x :=
              repFrom_add pred u x hpred_ne_u hx_ne_u.symm h_arc_no_wrap
            -- Now: repFrom u x > repFrom u succ (from hcase)
            -- So: repFrom pred x = repFrom pred u + repFrom u x
            --                    > repFrom pred u + repFrom u succ
            --                    = repFrom pred succ
            have hcontra : repFrom pred x > repFrom pred succ := by
              calc repFrom pred x = repFrom pred u + repFrom u x := h_pred_x_add
                _ > repFrom pred u + repFrom u succ := by linarith [hcase]
                _ = repFrom pred succ := hpred_succ_add.symm
            -- But hx_in_slot says repFrom pred x < repFrom pred succ
            linarith
          · -- x is not past u, so x is in [pred, u]
            push_neg at hx_past_u
            -- repFrom pred x ≤ repFrom pred u
            -- Now show repFrom x u ≤ repFrom pred u
            by_cases hx_eq_pred : x = pred
            · -- x = pred: repFrom pred u = repFrom x u ≤ repFrom pred u ✓
              rw [hx_eq_pred]
            · -- x ≠ pred: use arc addition
              -- repFrom pred u = repFrom pred x + repFrom x u (if no wrap)
              -- So repFrom x u = repFrom pred u - repFrom pred x ≤ repFrom pred u
              have hx_ne_pred : x ≠ pred := hx_eq_pred
              have hx_ne_u' : x ≠ u := by
                intro heq
                -- If x = u, then repFrom u x = 0, but hcase says repFrom u x > repFrom u succ > 0
                rw [heq, repFrom_self] at hcase
                have h_succ_pos : 0 < repFrom u succ := repFrom_pos_of_ne u succ hsucc_ne_u
                linarith
              have h_no_wrap : repFrom pred x + repFrom x u < 1 := by
                -- Use repFrom_between: since repFrom pred x ≤ repFrom pred u < 1/2,
                -- we have repFrom x u = repFrom pred u - repFrom pred x
                -- So repFrom pred x + repFrom x u = repFrom pred u < 1/2 < 1
                have h_pred_u_lt_half : repFrom pred u < 1/2 := by
                  have hslot_bound : (1 - repFrom u pred) + repFrom u succ < 1/2 := hslot_large
                  have hsum : repFrom u pred + repFrom pred u = 1 :=
                    repFrom_add_repFrom_eq_one u pred hpred_ne_u
                  have h_swap : 1 - repFrom u pred = repFrom pred u := by linarith
                  linarith [repFrom_nonneg u succ]
                have h_between := repFrom_between pred x u hx_ne_pred.symm hx_ne_u'
                  hx_past_u h_pred_u_lt_half
                -- h_between : repFrom x u = repFrom pred u - repFrom pred x
                linarith
              have h_arc_eq : repFrom pred u = repFrom pred x + repFrom x u :=
                repFrom_add pred x u hx_ne_pred.symm hx_ne_u' h_no_wrap
              have h_nonneg : 0 ≤ repFrom pred x := repFrom_nonneg pred x
              linarith
        calc dist u x = dist x u := hdist_comm
          _ ≤ repFrom x u := hdist_le_xu
          _ ≤ repFrom pred u := h_xu_bound
          _ = 1 - repFrom u pred := h_pred_u
          _ ≤ (1 - repFrom u pred) + repFrom u succ := by linarith [repFrom_nonneg u succ]

/-! ### Slot Argument: Same Slot Property for Shared Skeleton

The key geometric lemma for gap_exists_of_dist_gt:
When S_y = insert y skeleton and S_x = insert x skeleton (same skeleton),
both y and x occupy the same "gap" in the skeleton's cyclic order.

After applying f, both f(y) and f(x) are in the same slot of f(skeleton).
This is because:
1. The iso S_y ≃ E_{a1/q} maps y to some vertex (say 0)
2. The iso f(S_y) ≃ E_{a1/q} maps f(y) to some vertex (say 0)
3. The composition is a self-iso of E_{a1/q}, which is rotation or reflection
4. Rotation/reflection fixing 0 preserves cyclic neighbors
5. So the cyclic neighbors of f(y) in f(S_y) are f(s_1) and f(s_{a1-1})
   where s_1 and s_{a1-1} are the cyclic neighbors of y in S_y
6. The same argument for S_x shows f(x) has the same cyclic neighbors
7. Therefore f(y) and f(x) are both in the slot between f(s_{a1-1}) and f(s_1)
-/

/-
Key algebraic insight for insertion_same_gap_of_both_iso_to_fraction:

The ZMod-cyclic neighbors are preserved under the automorphism.
If T ∪ {p} ≃ E_{a1/q} via φ and T ∪ {p'} ≃ E_{a1/q} via ψ, then
φ⁻¹({φ(p)-1, φ(p)+1}) = ψ⁻¹({ψ(p')-1, ψ(p')+1}) as subsets of T.

Proof: The composition σ = ψ|T ∘ (φ|T)⁻¹ extended to E_{a1/q} is an automorphism.
By fractionGraph_selfIso_form, σ is rotation or reflection.
Both preserve {v-1, v+1} → {σ(v)-1, σ(v)+1} = {w-1, w+1}.

This is the algebraic core of insertion_same_gap_of_both_iso_to_fraction.
The remaining step shows that "ZMod-cyclic neighbors" correspond to
"Circle-cyclic neighbors" via the graph adjacency constraint; this is
discharged by `same_slot_of_shared_skeleton` below.
-/

/-!
### Equidistant Skeleton Structure

Structural facts used by the slot argument (`same_slot_of_shared_skeleton`):

**For skeleton = equidistantPointsShift N x \ {x} with N ≥ 3:**
1. The skeleton has N-1 points at x + k/N for k = 1, ..., N-1
2. The "large gap" (where x was removed) has width 2/N
3. Gap boundary points are x + 1/N (successor) and x + (N-1)/N (predecessor)
4. x is at the center of this large gap (distance 1/N from each boundary)
5. All other gaps have width 1/N

**Key insight for same_slot_of_shared_skeleton:**
For both S_y = skeleton ∪ {y} and S_x = skeleton ∪ {x} to induce E_{N/q}:
- The isomorphism constraint forces y to be in the large gap (same as x)
- This is because skeleton ≃ E_{predecessor(N/q)}, and filling the "hole"
  requires the new point to have the correct neighbor count and pattern
- Therefore y and x have the same cyclic neighbors in skeleton
- Hence f(y) and f(x) are in the same slot of f(skeleton)

This geometric argument underlies the slot argument used in gap_exists_of_dist_gt.
Formalizing it requires:
1. Proving that the graph isomorphism constraint determines geometric position
2. Showing that the "hole filling" operation has a unique position
3. Connecting ZMod-cyclic neighbors to Circle-cyclic neighbors
-/

/-- For equidistant skeleton, x is in the slot between its cyclic neighbors.

    When skeleton = equidistantPointsShift a1 x \ {x}, the cyclic neighbors of x are:
    - s_prev = x + embedZMod a1 (-1) (predecessor in cyclic order)
    - s_next = x + embedZMod a1 1 (successor in cyclic order)

    And x is exactly in the middle of the arc from s_prev to s_next:
    - repFrom s_prev x = 1/a1
    - repFrom x s_next = 1/a1
    - repFrom s_prev s_next = 2/a1
    - repFrom s_prev x + repFrom x s_next = repFrom s_prev s_next

    This follows directly from repFrom_equidistant and is key to the Lemma 5.3 approach. -/
lemma equidistant_slot_structure (a1 : ℕ) [NeZero a1] (ha1_ge : 3 ≤ a1) (x : Circle) :
    let s_prev := x + embedZMod a1 (-1 : ZMod a1)
    let s_next := x + embedZMod a1 (1 : ZMod a1)
    -- s_prev and s_next are in skeleton
    s_prev ∈ equidistantPointsShift a1 x \ {x} ∧
    s_next ∈ equidistantPointsShift a1 x \ {x} ∧
    s_prev ≠ s_next ∧
    -- x is in the slot between s_prev and s_next
    repFrom s_prev x + repFrom x s_next = repFrom s_prev s_next ∧
    -- The slot has width 2/a1
    repFrom s_prev s_next = 2 / a1 := by
  intro s_prev s_next
  have ha1_pos : 0 < a1 := NeZero.pos a1
  have ha1_ne_1 : a1 ≠ 1 := by omega
  have ha1_pos' : (0 : ℝ) < a1 := Nat.cast_pos.mpr ha1_pos
  -- Use repFrom_equidistant directly for the key equalities
  have h_rep_prev_x : repFrom s_prev x = 1 / a1 := by
    simp only [s_prev]
    have h := repFrom_equidistant a1 x (-1 : ZMod a1) (0 : ZMod a1)
    simp only [embedZMod_zero, add_zero, sub_neg_eq_add, zero_add] at h
    rw [h]
    congr 1
    have hval : (1 : ZMod a1).val = 1 := ZMod.val_one'' ha1_ne_1
    simp only [hval, Nat.cast_one]
  have h_rep_x_next : repFrom x s_next = 1 / a1 := by
    simp only [s_next]
    have h := repFrom_equidistant a1 x (0 : ZMod a1) (1 : ZMod a1)
    simp only [embedZMod_zero, add_zero, sub_zero] at h
    rw [h]
    congr 1
    have hval : (1 : ZMod a1).val = 1 := ZMod.val_one'' ha1_ne_1
    simp only [hval, Nat.cast_one]
  have h_rep_prev_next : repFrom s_prev s_next = 2 / a1 := by
    simp only [s_prev, s_next]
    have h := repFrom_equidistant a1 x (-1 : ZMod a1) (1 : ZMod a1)
    rw [h]
    congr 1
    have hval : (1 - (-1) : ZMod a1).val = 2 := by
      have h2 : (1 - (-1) : ZMod a1) = 2 := by ring
      rw [h2]
      exact ZMod.val_cast_of_lt (by omega : 2 < a1)
    simp only [hval, Nat.cast_ofNat]
  -- Membership and distinctness from embedZMod properties
  -- (embedZMod a1 k = 0 iff k = 0, and embedZMod is injective)
  refine ⟨?_, ?_, ?_, ?_, h_rep_prev_next⟩
  · -- s_prev ∈ equidistantPointsShift a1 x \ {x}
    constructor
    · -- Membership in equidistantPointsShift
      unfold equidistantPointsShift
      rw [Set.mem_image]
      exact ⟨embedZMod a1 (-1), ⟨-1, rfl⟩, rfl⟩
    · -- Not equal to x
      simp only [Set.mem_singleton_iff, s_prev]
      intro h
      have h1 : embedZMod a1 (-1 : ZMod a1) = 0 := add_left_cancel (a := x) (by rwa [add_zero])
      rw [embedZMod_eq_zero_iff] at h1
      have : (-1 : ZMod a1) ≠ 0 := by
        simp only [ne_eq, neg_eq_zero]
        have : Fact (1 < a1) := ⟨by omega⟩
        exact one_ne_zero
      exact this h1
  · -- s_next ∈ equidistantPointsShift a1 x \ {x}
    constructor
    · -- Membership in equidistantPointsShift
      unfold equidistantPointsShift
      rw [Set.mem_image]
      exact ⟨embedZMod a1 1, ⟨1, rfl⟩, rfl⟩
    · -- Not equal to x
      simp only [Set.mem_singleton_iff, s_next]
      intro h
      have h1 : embedZMod a1 (1 : ZMod a1) = 0 := add_left_cancel (a := x) (by rwa [add_zero])
      rw [embedZMod_eq_zero_iff] at h1
      have : (1 : ZMod a1) ≠ 0 := by
        have : Fact (1 < a1) := ⟨by omega⟩
        exact one_ne_zero
      exact this h1
  · -- s_prev ≠ s_next
    simp only [s_prev, s_next, ne_eq]
    intro h
    have h1 : embedZMod a1 (-1 : ZMod a1) = embedZMod a1 (1 : ZMod a1) :=
      add_left_cancel (a := x) h
    rw [embedZMod_eq_iff_eq] at h1
    -- -1 = 1 in ZMod a1 means 2 = 0 in ZMod a1, contradiction with a1 ≥ 3
    have h2 : (2 : ZMod a1) = 0 := by
      have eq1 : (-1 : ZMod a1) + (1 : ZMod a1) = (1 : ZMod a1) + (1 : ZMod a1) := by rw [h1]
      simp at eq1
      have eq2 : (1 : ZMod a1) + (1 : ZMod a1) = 0 := eq1.symm
      convert eq2 using 1
      norm_num
    have h3 : (2 : ZMod a1).val = 0 := by rw [h2]; exact ZMod.val_zero
    have hval : (2 : ZMod a1).val = 2 % a1 := ZMod.val_natCast a1 2
    rw [hval] at h3
    have h4 : a1 ∣ 2 := Nat.dvd_of_mod_eq_zero h3
    have h5 : a1 ≤ 2 := Nat.le_of_dvd (by norm_num) h4
    omega
  · -- repFrom s_prev x + repFrom x s_next = repFrom s_prev s_next
    rw [h_rep_prev_x, h_rep_x_next, h_rep_prev_next]
    field_simp
    ring

/-- Core cyclic order preservation for distance-monotone graph isomorphisms on Circle.

    If G is distance-monotone on S ⊆ Circle, φ : G.induce S ≃g fractionGraph a1 q,
    and φ maps u to w and v to w+1 (consecutive in ZMod a1), then either:
    (a) v is the counterclockwise-immediate successor of u in S (no S-point between them), or
    (b) v is the counterclockwise-farthest from u (all other S-points are closer counterclockwise).

    **Mathematical proof outline:**
    1. Sort S counterclockwise from u: s_0 = u, s_1, ..., s_{a1-1}
    2. The counterclockwise neighbors of each s_i form a clique of size ≤ q (by clique bound)
    3. By degree counting (each vertex has 2(q-1) neighbors) and monotonicity,
       each s_i has exactly q-1 ccw neighbors and q-1 cw neighbors
    4. So σ : i ↦ φ(s_i) is a self-isomorphism of fractionGraph a1 q
    5. By fractionGraph_selfIso_form (needs coprimality), σ is rotation or reflection
    6. σ(0) = w, so either σ(j) = w + j (rotation) or σ(j) = w - j (reflection)
    7. φ(v) = w+1 = σ(k) for some k. Rotation gives k=1, reflection gives k=a1-1
    8. k=1: v = s_1 (immediate successor). k=a1-1: v = s_{a1-1} (farthest counterclockwise) -/
lemma fractionGraph_iso_consecutive_or_reversed
    (G : SimpleGraph Circle)
    (a1 q : ℕ) [NeZero a1] (ha1_ge : 3 ≤ a1) (hq_ge : 2 ≤ q) (h2q : 2 * q ≤ a1)
    (hcoprime : Nat.Coprime a1 q)
    (S : Set Circle) (hS_finite : S.Finite) (hS_card : hS_finite.toFinset.card = a1)
    (φ : G.induce S ≃g fractionGraph a1 q)
    (hG_mono : ∀ u v w : Circle, u ≠ v → u ≠ w →
      G.Adj u w → dist u v < dist u w → G.Adj u v)
    -- Clique transitivity: if u adj v, u adj w, and v is ccw-between u and w (in
    -- near half), then v adj w. This holds for circle graphs since
    -- circleDistance(v,w) < circleDistance(u,w) < 1/r.
    (hG_ccw_trans : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
      G.Adj u w → G.Adj u v → repFrom u v < repFrom u w → repFrom u w ≤ 1/2 → G.Adj v w)
    (u v : Circle) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hφ_consec : φ ⟨v, hv⟩ = φ ⟨u, hu⟩ + 1) :
    -- Either no S-point is strictly counterclockwise-between u and v:
    (∀ t ∈ S, t ≠ u → t ≠ v → ¬(repFrom u t < repFrom u v)) ∨
    -- Or v is the counterclockwise-farthest from u (all other S-points are closer):
    (∀ t ∈ S, t ≠ u → t ≠ v → repFrom u t < repFrom u v) := by
  classical
  haveI : Fintype ↥S := hS_finite.fintype
  have ha1_pos : 0 < a1 := NeZero.pos a1
  have ha1_ne_one : a1 ≠ 1 := by omega
  have hq_pos : 0 < q := by omega
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 0: Finset setup and basic facts
  -- ═══════════════════════════════════════════════════════════════════
  set F := hS_finite.toFinset with hF_def
  have hF_mem : ∀ s, s ∈ F ↔ s ∈ S := fun s => Set.Finite.mem_toFinset hS_finite
  have hu_F : u ∈ F := (hF_mem u).mpr hu
  have hv_F : v ∈ F := (hF_mem v).mpr hv
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 1: Define ccw-rank: rank(s) = |{t ∈ F | repFrom u t < repFrom u s}|
  -- ═══════════════════════════════════════════════════════════════════
  let rank : Circle → ℕ := fun s => (F.filter (fun t => repFrom u t < repFrom u s)).card
  -- rank u = 0 (no S-point has repFrom u · < 0)
  have hrank_u : rank u = 0 := by
    change (F.filter (fun t => repFrom u t < repFrom u u)).card = 0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _; rw [repFrom_self]; exact not_lt.mpr (repFrom_nonneg u t)
  -- rank s < a1 for s ∈ F (s ∉ filter, so filter ⊊ F)
  have hrank_lt : ∀ s ∈ F, rank s < a1 := by
    intro s hs
    have hsub : F.filter (fun t => repFrom u t < repFrom u s) ⊂ F :=
      ⟨Finset.filter_subset _ F, fun h => not_lt.mpr le_rfl ((Finset.mem_filter.mp (h hs)).2)⟩
    rw [← hS_card]; exact Finset.card_lt_card hsub
  -- rank is injective on F
  have hrank_inj : ∀ s₁ ∈ F, ∀ s₂ ∈ F, rank s₁ = rank s₂ → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ heq
    by_contra hne
    -- Distinct points have distinct repFrom u values
    have hne_rep : repFrom u s₁ ≠ repFrom u s₂ := by
      intro h
      have h1 : (s₁ - u : Circle) = (s₂ - u : Circle) := by
        have : (AddCircle.equivIco 1 0 (s₁ - u)).val = (AddCircle.equivIco 1 0 (s₂ - u)).val := h
        exact (AddCircle.equivIco 1 0).injective (Subtype.ext this)
      exact hne (sub_left_injective h1)
    rcases lt_or_gt_of_ne hne_rep with h | h
    · have hsub : F.filter (fun t => repFrom u t < repFrom u s₁) ⊂
          F.filter (fun t => repFrom u t < repFrom u s₂) :=
        ⟨fun x hx => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
          lt_trans (Finset.mem_filter.mp hx).2 h⟩,
         fun hsub' => not_lt.mpr le_rfl ((Finset.mem_filter.mp (hsub'
          (Finset.mem_filter.mpr ⟨hs₁, h⟩))).2)⟩
      exact absurd heq (Nat.ne_of_lt (Finset.card_lt_card hsub))
    · have hsub : F.filter (fun t => repFrom u t < repFrom u s₂) ⊂
          F.filter (fun t => repFrom u t < repFrom u s₁) :=
        ⟨fun x hx => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
          lt_trans (Finset.mem_filter.mp hx).2 h⟩,
         fun hsub' => not_lt.mpr le_rfl ((Finset.mem_filter.mp (hsub'
          (Finset.mem_filter.mpr ⟨hs₂, h⟩))).2)⟩
      exact absurd heq (Nat.ne_of_gt (Finset.card_lt_card hsub))
  -- rank is surjective onto {0, ..., a1-1}
  have hrank_surj : ∀ i : ℕ, i < a1 → ∃ s ∈ F, rank s = i := by
    -- rank injects F (size a1) into Finset.range a1 (size a1), so it's surjective
    have h_image_card : (F.image rank).card = F.card :=
      Finset.card_image_of_injOn (fun a ha b hb => hrank_inj a ha b hb)
    have h_sub : F.image rank ⊆ Finset.range a1 := by
      intro x hx; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hrank_lt s hs)
    have h_eq : F.image rank = Finset.range a1 :=
      Finset.eq_of_subset_of_card_le h_sub (by rw [Finset.card_range, ← hS_card, ← h_image_card])
    intro i hi
    have := h_eq ▸ Finset.mem_range.mpr hi
    exact Finset.mem_image.mp this
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 2: Define the ccw-sorted indexing si : ZMod a1 → Circle
  -- ═══════════════════════════════════════════════════════════════════
  let si : ZMod a1 → Circle := fun i =>
    (hrank_surj i.val (ZMod.val_lt i)).choose
  have hsi_mem : ∀ i, si i ∈ F := fun i =>
    (hrank_surj i.val (ZMod.val_lt i)).choose_spec.1
  have hsi_rank : ∀ i, rank (si i) = i.val := fun i =>
    (hrank_surj i.val (ZMod.val_lt i)).choose_spec.2
  have hsi_mem_S : ∀ i, si i ∈ S := fun i => (hF_mem (si i)).mp (hsi_mem i)
  have hsi_inj : Function.Injective si := by
    intro i j h; exact ZMod.val_injective a1
      (by rw [← hsi_rank i, ← hsi_rank j]; exact congrArg rank h)
  -- si 0 = u
  have hsi_zero : si 0 = u := by
    apply hrank_inj (si 0) (hsi_mem 0) u hu_F
    rw [hsi_rank 0, ZMod.val_zero, hrank_u]
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 3: Define σ : ZMod a1 → ZMod a1 (ccw-rank → φ-rank)
  -- ═══════════════════════════════════════════════════════════════════
  let w := φ ⟨u, hu⟩
  let σ : ZMod a1 → ZMod a1 := fun i => φ ⟨si i, hsi_mem_S i⟩ - w
  -- σ(0) = 0
  have hσ_zero : σ 0 = 0 := by
    change φ ⟨si 0, hsi_mem_S 0⟩ - w = 0
    have : (⟨si 0, hsi_mem_S 0⟩ : ↥S) = ⟨u, hu⟩ := Subtype.ext hsi_zero
    rw [this]; exact sub_self w
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 4: Clique bound — adjacent S-points are close in ccw-rank
  -- ═══════════════════════════════════════════════════════════════════
  have clique_bound : ∀ i j : ZMod a1, i ≠ j →
      (G.induce S).Adj ⟨si i, hsi_mem_S i⟩ ⟨si j, hsi_mem_S j⟩ →
      FractionGraphBasic.distMod a1 i j < q := by
    intro i j hij hadj
    -- Clique bound argument: the S-points on the short arc from si i to si j
    -- (inclusive) form a clique in G (by hG_mono + hG_ccw_trans), hence have
    -- size ≤ cliqueNum(E[a1/q]) = q. So distMod(i,j) ≤ q-1.
    --
    -- Step A: Establish monotonicity: k.val < l.val → repFrom u (si k) < repFrom u (si l)
    have hsi_repFrom_strict_mono : ∀ k l : ZMod a1, k.val < l.val →
        repFrom u (si k) < repFrom u (si l) := by
      intro k l hkl
      by_contra h
      push_neg at h
      rcases eq_or_lt_of_le h with heq | hlt
      · have hsame : si k = si l := by
          apply hrank_inj (si k) (hsi_mem k) (si l) (hsi_mem l)
          have hcard_eq : (F.filter (fun t => repFrom u t < repFrom u (si k))).card =
              (F.filter (fun t => repFrom u t < repFrom u (si l))).card := by
            congr 1; ext t; simp only [Finset.mem_filter]; constructor
            · exact fun ⟨h1, h2⟩ => ⟨h1, heq ▸ h2⟩
            · exact fun ⟨h1, h2⟩ => ⟨h1, heq.symm ▸ h2⟩
          exact hcard_eq
        exact absurd (congrArg ZMod.val (hsi_inj hsame)) (Nat.ne_of_lt hkl)
      · have : (F.filter (fun t => repFrom u t < repFrom u (si l))).card <
            (F.filter (fun t => repFrom u t < repFrom u (si k))).card := by
          apply Finset.card_lt_card
          exact ⟨fun t ht => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,
              lt_trans (Finset.mem_filter.mp ht).2 hlt⟩,
            fun hsub => not_lt.mpr le_rfl
              ((Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hsi_mem l, hlt⟩))).2)⟩
        have h1 : l.val < k.val := by rw [← hsi_rank l, ← hsi_rank k]; exact this
        omega
    -- Step B: si i ≠ si j and G.Adj (si i) (si j) from hadj
    have hsi_ne : si i ≠ si j := fun heq => hij (hsi_inj heq)
    have hG_adj : G.Adj (si i) (si j) := hadj
    -- Step C: General arc bound for ZMod arcs (no val-ordering assumption).
    -- For any a ≠ b with G.Adj (si a) (si b) and repFrom (si a) (si b) ≤ 1/2,
    -- the arc si(a), si(a+1), ..., si(b) forms a clique of size (b-a).val + 1 ≤ q.
    --
    -- The key insight: repFrom (si a) (si (a+k)) is strictly increasing in k
    -- for 0 ≤ k ≤ (b-a).val, and all values ≤ 1/2.
    -- This holds for BOTH wrapping and non-wrapping arcs because:
    -- - When (a+k).val ≥ a.val: repFrom (si a) (si(a+k)) = repFrom u (si(a+k)) -
    --   repFrom u (si a)
    -- - When (a+k).val < a.val: repFrom (si a) (si(a+k)) = 1 - repFrom u (si a) +
    --   repFrom u (si(a+k))
    -- In both cases the expression is increasing in repFrom u (si(a+k)), which
    -- increases with (a+k).val.
    -- The transition between formulas (at the wrap point) is also increasing.
    suffices arc_bound : ∀ a b : ZMod a1, a ≠ b →
        G.Adj (si a) (si b) → repFrom (si a) (si b) ≤ 1/2 →
        (b - a).val < q by
      -- Use arc_bound to close the goal. Case split on which arc has repFrom ≤ 1/2.
      have hsum_one : repFrom (si i) (si j) + repFrom (si j) (si i) = 1 :=
        repFrom_add_repFrom_eq_one (si i) (si j) hsi_ne.symm
      rcases le_or_gt (repFrom (si i) (si j)) (1/2) with h_ij_le | h_ij_gt
      · -- repFrom (si i) (si j) ≤ 1/2: arc i → j gives (j-i).val < q
        have hd := arc_bound i j hij hG_adj h_ij_le
        -- distMod a1 i j = min((i-j).val, (j-i).val) ≤ (j-i).val < q
        -- Since distMod = min((i-j).val, a1 - (i-j).val) and (j-i).val = a1 - (i-j).val
        -- (when i ≠ j), we have distMod ≤ (j-i).val.
        rw [FractionGraphBasic.distMod_comm]
        simp only [FractionGraphBasic.distMod]
        exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hd
      · -- repFrom (si i) (si j) > 1/2, so repFrom (si j) (si i) < 1/2
        have h_ji_le : repFrom (si j) (si i) ≤ 1/2 := by linarith
        have hd := arc_bound j i hij.symm hG_adj.symm h_ji_le
        -- distMod a1 i j = min((i-j).val, a1 - (i-j).val) ≤ (i-j).val < q
        simp only [FractionGraphBasic.distMod]
        exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hd
    -- Proof of arc_bound: for any a ≠ b with G.Adj (si a) (si b) and repFrom ≤ 1/2,
    -- show (b - a).val < q.
    intro a b hab hG_adj_ab hrep_le
    set d := (b - a).val with hd_def
    have hd_pos : 0 < d := by
      rw [hd_def]
      exact Nat.pos_of_ne_zero (fun h => hab.symm (sub_eq_zero.mp (ZMod.val_eq_zero _ |>.mp h)))
    have hd_lt_a1 : d < a1 := ZMod.val_lt (b - a)
    -- Key: (d : ZMod a1) = b - a, and a + (d : ZMod a1) = b
    have hd_cast : (d : ZMod a1) = b - a := by
      rw [hd_def]
      have h1 : ((b - a).val : ZMod a1) = ZMod.cast (b - a) := ZMod.natCast_val (b - a)
      have h2 : (ZMod.cast (b - a) : ZMod a1) = b - a := ZMod.cast_id a1 (b - a)
      exact h1.trans h2
    have hab_eq' : a + (d : ZMod a1) = b := by rw [hd_cast, add_sub_cancel]
    -- For k < a1, (k : ZMod a1).val = k
    have hk_val : ∀ k : ℕ, k < a1 → (k : ZMod a1).val = k :=
      fun k hk => ZMod.val_natCast_of_lt hk
    -- The arc points: si(a + 0), si(a + 1), ..., si(a + d) = si(b)
    -- Key: the (a + k) values for 0 ≤ k ≤ d are all distinct elements of ZMod a1.
    -- si(a + k) ≠ si(a + l) for k ≠ l (with 0 ≤ k, l ≤ d) since si is injective
    -- and (k : ZMod a1) ≠ (l : ZMod a1) when 0 ≤ k < l < a1.
    --
    -- repFrom (si a) (si (a + (k : ZMod a1))) for the arc:
    -- We prove this is monotone increasing in k by using the formula with
    -- repFrom_ordered.
    --
    -- Case 1: (a + (k : ZMod a1)).val ≥ a.val
    --   Then repFrom u (si a) ≤ repFrom u (si (a + k)) (by
    --   hsi_repFrom_strict_mono, unless equal)
    --   And repFrom (si a) (si (a + k)) = repFrom u (si (a + k)) - repFrom u
    --   (si a) (by repFrom_ordered)
    --
    -- Case 2: (a + (k : ZMod a1)).val < a.val (wrapping case)
    --   repFrom u (si (a + k)) < repFrom u (si a) (by strict mono on val)
    --   repFrom (si (a + k)) (si a)
    --     = repFrom u (si a) - repFrom u (si (a + k)) (repFrom_ordered)
    --   repFrom (si a) (si (a + k)) = 1 - repFrom (si (a + k)) (si a)
    --     = 1 - repFrom u (si a) + repFrom u (si (a + k))
    --
    -- In both cases, repFrom (si a) (si (a + k)) is increasing in repFrom u (si (a + k)).
    -- And repFrom u (si (a + k)) depends only on (a + k).val, which increases along the arc.
    --
    -- The arc visits val values: a.val, a.val+1, ..., a1-1, 0, 1, ..., (a+d).val = b'.
    -- repFrom u (si ·) is strictly increasing with val. So along the arc, repFrom u first
    -- increases then wraps from max to 0 and increases again.
    -- But repFrom (si a) (si ·) keeps increasing because the formula compensates for the wrap.
    --
    -- Instead of formalizing this case analysis, we use a cleaner approach:
    -- We prove repFrom (si a) (si (a + (k : ZMod a1))) is increasing using repFrom_ordered
    -- and the relation between consecutive repFrom values.
    --
    -- Cleanest approach: prove the bound using repFrom (si a) ordering directly.
    -- For each k ≤ d, show repFrom (si a) (si (a + (k : ZMod a1))) ≤ repFrom (si a) (si b) ≤ 1/2.
    --
    -- Proof of this ordering: by structural argument on the ccw arc.
    -- si(a+k) is on the ccw arc from si(a) to si(b). The arc length is repFrom(si a)(si b) ≤ 1/2.
    -- Any point on this arc has repFrom(si a)(·) ≤ repFrom(si a)(si b).
    --
    -- To formalize: repFrom(si a)(si(a+k)) ≤ repFrom(si a)(si b) follows from
    -- repFrom(si(a+k))(si b) ≥ 0 and the arc decomposition
    -- repFrom(si a)(si b) = repFrom(si a)(si(a+k)) + repFrom(si(a+k))(si b)
    -- (when repFrom(si a)(si(a+k)) + repFrom(si(a+k))(si b) < 1).
    --
    -- We prove the repFrom ordering directly by computing repFrom(si a)(si(a+k))
    -- in terms of repFrom u values.
    -- Define the repFrom (si a) formula for arc points:
    have hrepFrom_a_formula : ∀ k : ℕ, k ≤ d →
        repFrom (si a) (si (a + (k : ZMod a1))) =
        (if a.val ≤ (a + (k : ZMod a1)).val
         then repFrom u (si (a + (k : ZMod a1))) - repFrom u (si a)
         else 1 - repFrom u (si a) + repFrom u (si (a + (k : ZMod a1)))) := by
      intro k hk
      by_cases hle : a.val ≤ (a + (k : ZMod a1)).val
      · -- Non-wrapping: (a+k).val ≥ a.val
        simp only [if_pos hle]
        rcases eq_or_lt_of_le hle with heq | hlt
        · -- (a+k).val = a.val means a + k = a, so k = 0
          have : a + (k : ZMod a1) = a := ZMod.val_injective a1 heq.symm
          rw [this, repFrom_self, sub_self]
        · -- (a+k).val > a.val: repFrom u (si a) < repFrom u (si (a+k))
          have hle' : repFrom u (si a) ≤ repFrom u (si (a + (k : ZMod a1))) :=
            le_of_lt (hsi_repFrom_strict_mono a (a + (k : ZMod a1)) hlt)
          exact repFrom_ordered u (si a) (si (a + (k : ZMod a1))) hle'
      · -- Wrapping: (a+k).val < a.val
        push_neg at hle
        simp only [if_neg (by omega : ¬(a.val ≤ (a + (k : ZMod a1)).val))]
        -- repFrom u (si (a+k)) < repFrom u (si a) (since (a+k).val < a.val)
        have hlt : repFrom u (si (a + (k : ZMod a1))) < repFrom u (si a) :=
          hsi_repFrom_strict_mono (a + (k : ZMod a1)) a hle
        have hle' : repFrom u (si (a + (k : ZMod a1))) ≤ repFrom u (si a) := le_of_lt hlt
        -- repFrom (si (a+k)) (si a) = repFrom u (si a) - repFrom u (si (a+k))
        have h1 : repFrom (si (a + (k : ZMod a1))) (si a) =
            repFrom u (si a) - repFrom u (si (a + (k : ZMod a1))) :=
          repFrom_ordered u (si (a + (k : ZMod a1))) (si a) hle'
        -- si a ≠ si (a+k) (since vals differ)
        have hne : si a ≠ si (a + (k : ZMod a1)) := by
          intro heq; have := congrArg ZMod.val (hsi_inj heq); omega
        -- repFrom (si a) (si (a+k)) + repFrom (si (a+k)) (si a) = 1
        have hsum := repFrom_add_repFrom_eq_one (si a) (si (a + (k : ZMod a1))) hne.symm
        linarith
    -- Now prove monotonicity
    have hrepFrom_a_strict_mono : ∀ k1 k2 : ℕ, k1 < k2 → k2 ≤ d →
        repFrom (si a) (si (a + (k1 : ZMod a1))) <
        repFrom (si a) (si (a + (k2 : ZMod a1))) := by
      intro k1 k2 hk12 hk2d
      rw [hrepFrom_a_formula k1 (by omega), hrepFrom_a_formula k2 hk2d]
      -- The key: in both formulas, repFrom (si a) (si (a+k)) depends on
      -- repFrom u (si (a+k)), which depends on (a+k).val.
      -- The arc visits (a+k).val = a.val, a.val+1, ..., a1-1, 0, 1, ..., (a+d).val.
      -- These values are ALL DISTINCT (since k ranges over {0, ..., d} and d < a1).
      -- So (a+k1).val ≠ (a+k2).val, hence the monotonicity follows from:
      -- 1. In the non-wrapping region: bigger val means bigger repFrom u, means
      --    bigger formula
      -- 2. Across the wrap: the wrapping formula value is strictly larger than
      --    any non-wrapping value
      -- 3. In the post-wrap region: bigger val means bigger repFrom u, means
      --    bigger formula
      --
      -- Case analysis on whether k1 and k2 are in pre-wrap or post-wrap:
      -- Pre-wrap: (a+k).val = (a.val + k) mod a1 ≥ a.val (when a.val + k < a1)
      -- Post-wrap: (a+k).val = (a.val + k) mod a1 < a.val (when a.val + k ≥ a1)
      --
      -- Key fact: (a + (k : ZMod a1)).val = (a.val + k) % a1
      -- When a.val + k < a1: (a+k).val = a.val + k ≥ a.val (pre-wrap)
      -- When a.val + k ≥ a1: (a+k).val = a.val + k - a1 < a.val (post-wrap, since k < a1)
      have hval_k1 : (a + (k1 : ZMod a1)).val = (a.val + k1) % a1 := by
        rw [ZMod.val_add, ZMod.val_natCast_of_lt (by omega : k1 < a1)]
      have hval_k2 : (a + (k2 : ZMod a1)).val = (a.val + k2) % a1 := by
        rw [ZMod.val_add, ZMod.val_natCast_of_lt (by omega : k2 < a1)]
      -- The expression we're comparing is:
      -- f(x) = if a.val ≤ x.val then (repFrom u (si x) - repFrom u (si a))
      --                           else (1 - repFrom u (si a) + repFrom u (si x))
      -- = if a.val ≤ x.val then repFrom u (si x) - repFrom u (si a)
      --                     else repFrom u (si x) + (1 - repFrom u (si a))
      -- Note: 1 - repFrom u (si a) > repFrom u (si (a1-1)) - repFrom u (si a)
      --   (since repFrom u (si (a1-1)) < 1)
      -- So f(x) is increasing as x.val goes: a.val, a.val+1, ..., a1-1, 0, 1, ..., a.val-1
      -- (the cyclic order starting from a.val).
      --
      -- To formalize, we need to show the following:
      -- For the ccw-arc order, (a+k1).val comes before (a+k2).val.
      -- Since k1 < k2 ≤ d < a1, and (a+k).val = (a.val + k) % a1,
      -- the ccw-arc order is determined by k, not by val.
      -- So we need f((a+k1).val) < f((a+k2).val), which follows from the
      -- monotonicity of f along the ccw arc.
      --
      -- Split into 3 cases based on whether (a+ki).val wraps around:
      -- Case A: Both pre-wrap (a.val ≤ (a+k1).val and a.val ≤ (a+k2).val)
      -- Case B: k1 pre-wrap, k2 post-wrap
      -- Case C: Both post-wrap
      by_cases h1 : a.val ≤ (a + (k1 : ZMod a1)).val <;>
        by_cases h2 : a.val ≤ (a + (k2 : ZMod a1)).val
      · -- Case A: both pre-wrap
        simp only [if_pos h1, if_pos h2]
        have hlt1 : a.val + k1 < a1 := by
          by_contra hge; push_neg at hge
          -- If a.val + k1 ≥ a1, then (a+k1).val = (a.val+k1)%a1 = a.val+k1-a1 < a.val
          have hv1_eq : (a + (k1 : ZMod a1)).val = (a.val + k1) % a1 := hval_k1
          have h_2a1 : a.val + k1 < 2 * a1 := by have := ZMod.val_lt a; omega
          have hsub_lt : a.val + k1 - a1 < a1 := by omega
          have : (a.val + k1) % a1 = a.val + k1 - a1 := by
            conv_lhs => rw [show a.val + k1 = (a.val + k1 - a1) + a1 from by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]
          rw [hv1_eq, this] at h1; omega
        have hlt2 : a.val + k2 < a1 := by
          by_contra hge; push_neg at hge
          have hv2_eq : (a + (k2 : ZMod a1)).val = (a.val + k2) % a1 := hval_k2
          have h_2a1 : a.val + k2 < 2 * a1 := by have := ZMod.val_lt a; omega
          have hsub_lt : a.val + k2 - a1 < a1 := by omega
          have : (a.val + k2) % a1 = a.val + k2 - a1 := by
            conv_lhs => rw [show a.val + k2 = (a.val + k2 - a1) + a1 from by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]
          rw [hv2_eq, this] at h2; omega
        have : (a + (k1 : ZMod a1)).val < (a + (k2 : ZMod a1)).val := by
          rw [hval_k1, hval_k2, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]; omega
        linarith [hsi_repFrom_strict_mono (a + (k1 : ZMod a1)) (a + (k2 : ZMod a1)) this]
      · -- Case B: k1 pre-wrap, k2 post-wrap
        simp only [if_pos h1, if_neg h2]
        -- repFrom u (si (a+k1)) - repFrom u (si a) < 1 - repFrom u (si a) + repFrom u (si (a+k2))
        -- ⟺ repFrom u (si (a+k1)) < 1 + repFrom u (si (a+k2))
        -- This is true since repFrom u < 1 and repFrom u ≥ 0.
        have h_k1_lt_one : repFrom u (si (a + (k1 : ZMod a1))) < 1 :=
          repFrom_lt_one u (si (a + (k1 : ZMod a1)))
        have h_k2_ge_zero : 0 ≤ repFrom u (si (a + (k2 : ZMod a1))) :=
          repFrom_nonneg u (si (a + (k2 : ZMod a1)))
        linarith
      · -- Case impossible: k1 post-wrap but k2 pre-wrap
        -- If k1 post-wraps (a.val + k1 ≥ a1), then k2 > k1 also post-wraps (a.val + k2 ≥ a1).
        -- So (a+k2).val = a.val + k2 - a1 < a.val, contradicting h2.
        push_neg at h1
        exfalso
        have hge1 : a.val + k1 ≥ a1 := by
          -- If a.val + k1 < a1, then (a+k1).val = a.val + k1 ≥ a.val, contradicting h1
          by_contra hlt; push_neg at hlt
          have : (a + (k1 : ZMod a1)).val = a.val + k1 := by
            rw [hval_k1]; exact Nat.mod_eq_of_lt hlt
          omega
        have hge2 : a.val + k2 ≥ a1 := by omega
        -- (a+k2).val = (a.val + k2) % a1 = a.val + k2 - a1
        have hv2 : (a + (k2 : ZMod a1)).val = a.val + k2 - a1 := by
          rw [hval_k2]
          have h2_lt : a.val + k2 < 2 * a1 := by have := ZMod.val_lt a; omega
          have hsub_lt : a.val + k2 - a1 < a1 := by omega
          conv_lhs => rw [show a.val + k2 = (a.val + k2 - a1) + a1 from by omega]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]
        -- a.val + k2 - a1 < a.val since k2 ≤ d < a1
        omega
      · -- Case C: both post-wrap
        push_neg at h1 h2
        simp only [if_neg (by omega : ¬(a.val ≤ (a + (k1 : ZMod a1)).val)),
                    if_neg (by omega : ¬(a.val ≤ (a + (k2 : ZMod a1)).val))]
        have hv1 : (a + (k1 : ZMod a1)).val < (a + (k2 : ZMod a1)).val := by
          rw [hval_k1, hval_k2]
          have hge1 : a.val + k1 ≥ a1 := by
            by_contra hlt; push_neg at hlt
            rw [hval_k1, Nat.mod_eq_of_lt hlt] at h1; omega
          have hge2 : a.val + k2 ≥ a1 := by omega
          -- a.val + k < 2 * a1 (since k < a1 and a.val < a1), so mod = a.val + k - a1
          have h1_lt : a.val + k1 < 2 * a1 := by
            have := ZMod.val_lt a; omega
          have h2_lt : a.val + k2 < 2 * a1 := by
            have := ZMod.val_lt a; omega
          have hsub1_lt : a.val + k1 - a1 < a1 := by omega
          have hsub2_lt : a.val + k2 - a1 < a1 := by omega
          have hv1_eq : (a.val + k1) % a1 = a.val + k1 - a1 := by
            conv_lhs => rw [show a.val + k1 = (a.val + k1 - a1) + a1 from by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub1_lt]
          have hv2_eq : (a.val + k2) % a1 = a.val + k2 - a1 := by
            conv_lhs => rw [show a.val + k2 = (a.val + k2 - a1) + a1 from by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub2_lt]
          rw [hv1_eq, hv2_eq]; omega
        linarith [hsi_repFrom_strict_mono (a + (k1 : ZMod a1)) (a + (k2 : ZMod a1)) hv1]
    -- repFrom (si a) (si (a+k)) ≤ repFrom (si a) (si b) for k ≤ d
    have hrepFrom_a_le_b : ∀ k : ℕ, k ≤ d →
        repFrom (si a) (si (a + (k : ZMod a1))) ≤ repFrom (si a) (si b) := by
      intro k hk
      rcases eq_or_lt_of_le hk with rfl | hlt
      · simp only [hab_eq']; exact le_rfl
      · exact le_of_lt (by simp only [← hab_eq']; exact hrepFrom_a_strict_mono k d hlt le_rfl)
    have hrepFrom_a_le_half : ∀ k : ℕ, k ≤ d →
        repFrom (si a) (si (a + (k : ZMod a1))) ≤ 1/2 := by
      intro k hk; exact le_trans (hrepFrom_a_le_b k hk) hrep_le
    have hdist_eq_rep : ∀ k : ℕ, k ≤ d →
        dist (si a) (si (a + (k : ZMod a1))) = repFrom (si a) (si (a + (k : ZMod a1))) := by
      intro k hk; exact dist_eq_repFrom_of_le_half _ _ (hrepFrom_a_le_half k hk)
    -- All arc points pairwise adjacent: step 1, si a adj to all si(a+k)
    have hadj_from_a : ∀ k : ℕ, 0 < k → k ≤ d →
        G.Adj (si a) (si (a + (k : ZMod a1))) := by
      intro k hk_pos hk_le
      rcases eq_or_lt_of_le hk_le with rfl | hk_lt
      · rw [hab_eq']; exact hG_adj_ab
      · have hne_ak : si a ≠ si (a + (k : ZMod a1)) := by
          intro heq; have h := hsi_inj heq
          -- h : a = a + (k : ZMod a1)
          have hk0 : (k : ZMod a1) = 0 := by
            have h' : a + 0 = a + (k : ZMod a1) := by rw [add_zero]; exact h
            exact (add_left_cancel h').symm
          have := congrArg ZMod.val hk0
          rw [ZMod.val_natCast_of_lt (by omega : k < a1), ZMod.val_zero] at this; omega
        have hdist_lt : dist (si a) (si (a + (k : ZMod a1))) < dist (si a) (si b) := by
          rw [hdist_eq_rep k (by omega), ← hab_eq', hdist_eq_rep d le_rfl]
          exact hrepFrom_a_strict_mono k d hk_lt le_rfl
        exact hG_mono (si a) (si (a + (k : ZMod a1))) (si b)
          hne_ak (fun h => hab (hsi_inj h)) hG_adj_ab hdist_lt
    -- Step 2: all pairs adjacent via hG_ccw_trans
    have hadj_pairwise : ∀ k1 k2 : ℕ, k1 < k2 → k2 ≤ d →
        G.Adj (si (a + (k1 : ZMod a1))) (si (a + (k2 : ZMod a1))) := by
      intro k1 k2 hk12 hk2d
      rcases Nat.eq_or_lt_of_le (Nat.zero_le k1) with rfl | hk1_pos
      · simp only [Nat.cast_zero, add_zero]
        exact hadj_from_a k2 (by omega) hk2d
      · have hzmod_ne : ∀ k : ℕ, 0 < k → k < a1 → (k : ZMod a1) ≠ (0 : ZMod a1) := by
          intro k hk_pos hk_lt h
          have := congrArg ZMod.val h
          rw [ZMod.val_natCast_of_lt hk_lt, ZMod.val_zero] at this; omega
        have hne1 : si a ≠ si (a + (k1 : ZMod a1)) := by
          intro heq; have h := hsi_inj heq
          have : (k1 : ZMod a1) = 0 :=
            (add_left_cancel (show a + 0 = a + (k1 : ZMod a1) by rw [add_zero]; exact h)).symm
          exact hzmod_ne k1 hk1_pos (by omega) this
        have hne2 : si a ≠ si (a + (k2 : ZMod a1)) := by
          intro heq; have h := hsi_inj heq
          have : (k2 : ZMod a1) = 0 :=
            (add_left_cancel (show a + 0 = a + (k2 : ZMod a1) by rw [add_zero]; exact h)).symm
          exact hzmod_ne k2 (by omega) (by omega) this
        have hne12 : si (a + (k1 : ZMod a1)) ≠ si (a + (k2 : ZMod a1)) := by
          intro heq
          have h := hsi_inj heq
          have : (k1 : ZMod a1) = (k2 : ZMod a1) :=
            add_left_cancel h
          have := congrArg ZMod.val this
          rw [ZMod.val_natCast_of_lt (by omega : k1 < a1),
              ZMod.val_natCast_of_lt (by omega : k2 < a1)] at this; omega
        exact hG_ccw_trans (si a) (si (a + (k1 : ZMod a1))) (si (a + (k2 : ZMod a1)))
          hne1 hne2 hne12
          (hadj_from_a k2 (by omega) hk2d) (hadj_from_a k1 hk1_pos (by omega))
          (hrepFrom_a_strict_mono k1 k2 hk12 hk2d) (hrepFrom_a_le_half k2 hk2d)
    -- Step 3: Build Finset of arc images and show d + 1 ≤ q
    have hinj' : Set.InjOn (fun (k : ℕ) => φ ⟨si (a + (k : ZMod a1)), hsi_mem_S _⟩)
        (Finset.range (d + 1) : Set ℕ) := by
      intro k1 hk1 k2 hk2 hφ_eq
      rw [Finset.mem_coe, Finset.mem_range] at hk1 hk2
      have h_eq := φ.injective hφ_eq
      have h_si : si (a + (k1 : ZMod a1)) = si (a + (k2 : ZMod a1)) :=
        Subtype.mk.inj h_eq
      have hv_eq := congrArg ZMod.val (add_left_cancel (hsi_inj h_si))
      rw [ZMod.val_natCast_of_lt (by omega : k1 < a1),
          ZMod.val_natCast_of_lt (by omega : k2 < a1)] at hv_eq
      exact hv_eq
    have hpw : ∀ x ∈ (Finset.range (d + 1)).image
        (fun (k : ℕ) => φ ⟨si (a + (k : ZMod a1)), hsi_mem_S _⟩),
        ∀ y ∈ (Finset.range (d + 1)).image
        (fun (k : ℕ) => φ ⟨si (a + (k : ZMod a1)), hsi_mem_S _⟩),
        x ≠ y → FractionGraphBasic.distMod a1 x y < q := by
      intro x hx y hy hxy
      obtain ⟨k1, hk1_mem, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k2, hk2_mem, rfl⟩ := Finset.mem_image.mp hy
      have hk1_lt : k1 < d + 1 := Finset.mem_range.mp hk1_mem
      have hk2_lt : k2 < d + 1 := Finset.mem_range.mp hk2_mem
      have hk_ne : k1 ≠ k2 := fun heq => by subst heq; exact hxy rfl
      rcases lt_or_gt_of_ne hk_ne with hlt | hgt
      · have hinduce_adj : (G.induce S).Adj ⟨si (a + (k1 : ZMod a1)), hsi_mem_S _⟩
            ⟨si (a + (k2 : ZMod a1)), hsi_mem_S _⟩ :=
          hadj_pairwise k1 k2 hlt (by omega)
        exact (φ.map_rel_iff.mpr hinduce_adj).2
      · have hinduce_adj : (G.induce S).Adj ⟨si (a + (k2 : ZMod a1)), hsi_mem_S _⟩
            ⟨si (a + (k1 : ZMod a1)), hsi_mem_S _⟩ :=
          hadj_pairwise k2 k1 hgt (by omega)
        rw [FractionGraphBasic.distMod_comm]
        exact (φ.map_rel_iff.mpr hinduce_adj).2
    have hcard_le :=
      FractionGraphBasic.finset_card_le_of_pairwise_dist_lt a1 q hq_pos h2q _ hpw
    rw [Finset.card_image_of_injOn hinj', Finset.card_range] at hcard_le; omega
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 5: σ is a cohomomorphism of E[a1/q]
  -- ═══════════════════════════════════════════════════════════════════
  have hσ_cohom : IsCohom (fractionGraph a1 q) (fractionGraph a1 q) σ := by
    intro i j hij hnadj
    -- Not adj in fractionGraph means distMod ≥ q
    have hdist_ge : ¬FractionGraphBasic.distMod a1 i j < q :=
      fun hlt => hnadj ⟨hij, hlt⟩
    -- By contrapositive of clique_bound: not adj in G.induce S
    have hnadj_induce : ¬(G.induce S).Adj ⟨si i, hsi_mem_S i⟩ ⟨si j, hsi_mem_S j⟩ :=
      fun hadj => hdist_ge (clique_bound i j hij hadj)
    -- σ(i) ≠ σ(j)
    have hσ_ne : σ i ≠ σ j := by
      intro heq
      have hφ_eq : φ ⟨si i, hsi_mem_S i⟩ = φ ⟨si j, hsi_mem_S j⟩ := by
        have h : (φ ⟨si i, hsi_mem_S i⟩ - w : ZMod a1) = φ ⟨si j, hsi_mem_S j⟩ - w := heq
        calc φ ⟨si i, _⟩ = (φ ⟨si i, _⟩ - w) + w := (sub_add_cancel _ _).symm
          _ = (φ ⟨si j, _⟩ - w) + w := by rw [h]
          _ = φ ⟨si j, _⟩ := sub_add_cancel _ _
      have hne : si i ≠ si j := fun heq => hij (hsi_inj heq)
      exact hne (congrArg Subtype.val (φ.injective hφ_eq))
    -- ¬E[a1/q].Adj (σ i) (σ j)
    have hσ_nadj : ¬(fractionGraph a1 q).Adj (σ i) (σ j) := by
      intro ⟨_, hdist_σ⟩
      have hdiff : σ i - σ j = φ ⟨si i, hsi_mem_S i⟩ - φ ⟨si j, hsi_mem_S j⟩ := by
        change (φ ⟨si i, hsi_mem_S i⟩ - w) - (φ ⟨si j, hsi_mem_S j⟩ - w) = _; ring
      have hdiff' : σ j - σ i = φ ⟨si j, hsi_mem_S j⟩ - φ ⟨si i, hsi_mem_S i⟩ := by
        change (φ ⟨si j, hsi_mem_S j⟩ - w) - (φ ⟨si i, hsi_mem_S i⟩ - w) = _; ring
      have hdistMod : FractionGraphBasic.distMod a1 (σ i) (σ j) =
          FractionGraphBasic.distMod a1 (φ ⟨si i, hsi_mem_S i⟩) (φ ⟨si j, hsi_mem_S j⟩) := by
        simp only [FractionGraphBasic.distMod, hdiff]
      have hne_φ : φ ⟨si i, hsi_mem_S i⟩ ≠ φ ⟨si j, hsi_mem_S j⟩ := by
        intro h; exact hij (hsi_inj (congrArg Subtype.val (φ.injective h)))
      have hadj_φ : (fractionGraph a1 q).Adj
          (φ ⟨si i, hsi_mem_S i⟩) (φ ⟨si j, hsi_mem_S j⟩) :=
        ⟨hne_φ, by rw [← hdistMod]; exact hdist_σ⟩
      exact hnadj_induce (φ.map_rel_iff.mp hadj_φ)
    exact ⟨hσ_ne, hσ_nadj⟩
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 6: Apply fractionGraph_selfCohom_form
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨a, ha⟩ := fractionGraph_selfCohom_form a1 q hq_ge h2q hcoprime σ hσ_cohom
  -- Since σ(0) = 0, determine a
  have ha_zero : a = 0 := by
    rcases ha with hrot | hrefl
    · have := hrot 0; rw [hσ_zero, add_zero] at this; exact this.symm
    · have := hrefl 0; rw [hσ_zero, sub_zero] at this; exact this.symm
  subst ha_zero
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 7: Find the index of v and case-split
  -- ═══════════════════════════════════════════════════════════════════
  have hv_exists : ∃ iv : ZMod a1, si iv = v := by
    refine ⟨(rank v : ZMod a1), ?_⟩
    apply hrank_inj _ (hsi_mem _) v hv_F
    rw [hsi_rank]; exact ZMod.val_natCast_of_lt (hrank_lt v hv_F)
  obtain ⟨iv, hiv⟩ := hv_exists
  -- σ(iv) = φ(v) - φ(u) = (φ(u) + 1) - φ(u) = 1
  have hσ_iv : σ iv = 1 := by
    change φ ⟨si iv, hsi_mem_S iv⟩ - w = 1
    have : (⟨si iv, hsi_mem_S iv⟩ : ↥S) = ⟨v, hv⟩ := Subtype.ext hiv
    rw [this, hφ_consec]; ring
  -- Case split on rotation vs reflection
  rcases ha with hrot | hrefl
  · -- Rotation: σ(x) = 0 + x = x. So iv = 1.
    have hiv_eq : iv = 1 := by
      have := hrot iv; simp only [zero_add] at this; rw [← this]; exact hσ_iv
    -- rank(v) = 1
    have hrv_eq_1 : rank v = 1 := by
      calc rank v = rank (si iv) := by rw [hiv]
        _ = iv.val := hsi_rank iv
        _ = (1 : ZMod a1).val := by rw [hiv_eq]
        _ = 1 := ZMod.val_one'' ha1_ne_one
    left
    intro t ht htu htv hlt
    have ht_F : t ∈ F := (hF_mem t).mpr ht
    -- Both u and t are in the filter for v, but card = 1
    have hu_in : u ∈ F.filter (fun s => repFrom u s < repFrom u v) :=
      Finset.mem_filter.mpr ⟨hu_F, by rw [repFrom_self]; exact repFrom_pos_of_ne u v huv.symm⟩
    have ht_in : t ∈ F.filter (fun s => repFrom u s < repFrom u v) :=
      Finset.mem_filter.mpr ⟨ht_F, hlt⟩
    have : 2 ≤ (F.filter (fun s => repFrom u s < repFrom u v)).card := by
      calc 2 = ({u, t} : Finset Circle).card := (Finset.card_pair htu.symm).symm
        _ ≤ _ := Finset.card_le_card (Finset.insert_subset_iff.mpr
            ⟨hu_in, Finset.singleton_subset_iff.mpr ht_in⟩)
    have : (F.filter (fun s => repFrom u s < repFrom u v)).card = rank v := rfl
    linarith [hrv_eq_1]
  · -- Reflection: σ(x) = -x. So iv = -1, rank(v) = a1 - 1.
    have hiv_eq : iv = -1 := by
      have h1 := hrefl iv; simp only [zero_sub] at h1
      exact neg_eq_iff_eq_neg.mp (h1.symm.trans hσ_iv)
    have hrv : rank v = a1 - 1 := by
      calc rank v = rank (si iv) := by rw [hiv]
        _ = iv.val := hsi_rank iv
        _ = (-1 : ZMod a1).val := by rw [hiv_eq]
        _ = a1 - 1 := by cases a1 with | zero => omega | succ n => exact ZMod.val_neg_one n
    right
    intro t ht htu htv
    have ht_F : t ∈ F := (hF_mem t).mpr ht
    have hrt_lt : rank t < rank v := by
      have := hrank_lt t ht_F; rw [hrv]
      exact Nat.lt_of_le_of_ne (by omega) (fun h => htv (hrank_inj t ht_F v hv_F (by omega)))
    by_contra hge; push_neg at hge
    have : rank v ≤ rank t := Finset.card_le_card (fun x hx =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
        lt_of_lt_of_le (Finset.mem_filter.mp hx).2 hge⟩)
    omega

/-- Graph isomorphisms from distance-monotone graphs to fractionGraph preserve arc containment.

    If φ : G.induce S ≃g fractionGraph a1 q is an isomorphism for a distance-monotone G,
    and t1, t2, p ∈ S with φ(t1), φ(p), φ(t2) consecutive in ZMod a1
    (i.e., φ(t1) = v-1, φ(p) = v, φ(t2) = v+1 for some v), then for any t ∈ S \ {t1, t2},
    t is not strictly between t1 and p in the arc from t1 to t2.

    **Proof:** Apply fractionGraph_iso_consecutive_or_reversed with u = t1, v = p.
    Case (a): no point between t1 and p → conclusion immediate.
    Case (b): p is farthest from t1 → repFrom t1 t2 < repFrom t1 p, making the
    second conjunct false, so the conclusion holds vacuously. -/
lemma fractionGraph_iso_preserves_arc_containment
    (G : SimpleGraph Circle)
    (a1 q : ℕ) [NeZero a1] (ha1_ge : 3 ≤ a1) (hq_ge : 2 ≤ q) (_hq_pos : 0 < q)
    (h2q : 2 * q ≤ a1) (hcoprime : Nat.Coprime a1 q)
    (S : Set Circle) (hS_finite : S.Finite) (hS_card : hS_finite.toFinset.card = a1)
    (φ : G.induce S ≃g fractionGraph a1 q)
    (hG_mono : ∀ u v w : Circle, u ≠ v → u ≠ w →
      G.Adj u w → dist u v < dist u w → G.Adj u v)
    (hG_ccw_trans : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
      G.Adj u w → G.Adj u v → repFrom u v < repFrom u w → repFrom u w ≤ 1/2 → G.Adj v w)
    (t1 p t2 : Circle) (ht1 : t1 ∈ S) (hp : p ∈ S) (ht2 : t2 ∈ S)
    (ht1_ne_p : t1 ≠ p) (hp_ne_t2 : p ≠ t2) (ht1_ne_t2 : t1 ≠ t2)
    -- φ maps t1, p, t2 to consecutive elements v-1, v, v+1 in ZMod a1
    (v : ZMod a1)
    (hφt1 : φ ⟨t1, ht1⟩ = v - 1)
    (hφp : φ ⟨p, hp⟩ = v)
    (_hφt2 : φ ⟨t2, ht2⟩ = v + 1) :
    ∀ t ∈ S, t ≠ t1 → t ≠ t2 → ¬(repFrom t1 t < repFrom t1 p ∧ repFrom t1 p < repFrom t1 t2) := by
  -- Apply the cyclic order preservation lemma
  have hφ_consec : φ ⟨p, hp⟩ = φ ⟨t1, ht1⟩ + 1 := by rw [hφp, hφt1]; ring
  rcases fractionGraph_iso_consecutive_or_reversed G a1 q ha1_ge hq_ge h2q hcoprime
    S hS_finite hS_card φ hG_mono hG_ccw_trans t1 p ht1 hp ht1_ne_p hφ_consec with hcase_a | hcase_b
  · -- Case (a): no S-point is strictly counterclockwise-between t1 and p
    intro t ht ht_ne_t1 _ht_ne_t2 ⟨h_lt_p, _⟩
    by_cases htp : t = p
    · rw [htp] at h_lt_p; exact lt_irrefl _ h_lt_p
    · exact hcase_a t ht ht_ne_t1 htp h_lt_p
  · -- Case (b): p is the counterclockwise-farthest from t1
    -- Then repFrom t1 t2 < repFrom t1 p (since t2 ∈ S, t2 ≠ t1, t2 ≠ p)
    have hp_ne_t2' : p ≠ t2 := hp_ne_t2
    have ht2_lt_p : repFrom t1 t2 < repFrom t1 p := by
      -- φ(t2) = v+1 ≠ v = φ(p), so t2 ≠ p
      exact hcase_b t2 ht2 ht1_ne_t2.symm hp_ne_t2'.symm
    -- The second conjunct repFrom t1 p < repFrom t1 t2 is false
    intro t _ht _ht_ne_t1 _ht_ne_t2 ⟨_, h_p_lt_t2⟩
    linarith

/-- The automorphism argument for the p' case.

    If T ∪ {p} and T ∪ {p'} both induce E_{a1/q} via isomorphisms φ and ψ respectively,
    and t1, t2 are the cyclic neighbors of p under φ (i.e., φ(t1) = v-1, φ(t2) = v+1
    where v = φ(p)), then t1, t2 are also the cyclic neighbors of p' under ψ
    (possibly swapped, i.e., {ψ(t1), ψ(t2)} = {w-1, w+1} where w = ψ(p')).

    **Mathematical justification:**
    The composition σ := ψ|_T ∘ (φ|_T)⁻¹ extends to an automorphism of E_{a1/q}.
    By fractionGraph_selfIso_form (proved), σ is either a rotation or reflection,
    both of which map {v-1, v+1} to {w-1, w+1}. The arc containment then follows
    from fractionGraph_iso_preserves_arc_containment applied to ψ.

    Depends on: fractionGraph_iso_preserves_arc_containment (BJH02 Lemma 2.4). -/
lemma fractionGraph_iso_preserves_arc_containment_automorphism
    (G : SimpleGraph Circle)
    (a1 q : ℕ) [NeZero a1] (ha1_ge : 3 ≤ a1) (hq_ge : 2 ≤ q) (hq_pos : 0 < q)
    (h2q : 2 * q ≤ a1) (hcoprime : Nat.Coprime a1 q)
    (T : Finset Circle) (hT_card : T.card = a1 - 1)
    (p p' : Circle) (_hp : p ∉ T) (hp' : p' ∉ T) (_hpp' : p ≠ p')
    (φ : G.induce (insert p (T : Set Circle)) ≃g
         fractionGraph a1 q)
    (ψ : G.induce (insert p' (T : Set Circle)) ≃g
         fractionGraph a1 q)
    (hG_mono : ∀ u v w : Circle, u ≠ v → u ≠ w →
      G.Adj u w → dist u v < dist u w → G.Adj u v)
    (hG_ccw_trans : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
      G.Adj u w → G.Adj u v → repFrom u v < repFrom u w → repFrom u w ≤ 1/2 → G.Adj v w)
    -- t1, t2 are the cyclic neighbors of p under φ
    (t1 t2 : Circle) (ht1 : t1 ∈ T) (ht2 : t2 ∈ T) (ht1_ne_t2 : t1 ≠ t2)
    (v : ZMod a1)
    (hφt1 : φ ⟨t1, Or.inr ht1⟩ = v - 1)
    (hφp : φ ⟨p, Set.mem_insert p T⟩ = v)
    (hφt2 : φ ⟨t2, Or.inr ht2⟩ = v + 1) :
    -- p' has the same arc containment property
    ∀ t ∈ T, t ≠ t1 → t ≠ t2 →
      ¬(repFrom t1 t < repFrom t1 p' ∧
        repFrom t1 p' < repFrom t1 t2) := by
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 1: Set up w = ψ(p') and the transfer function σ
  -- ═══════════════════════════════════════════════════════════════════
  set w := ψ ⟨p', Set.mem_insert p' T⟩ with hw_def
  -- For x ≠ v, φ.symm x is in T (not p), so it's also in T ∪ {p'}
  have hφ_symm_in_T : ∀ x : ZMod a1, x ≠ v → (φ.symm x).val ∈ (T : Set Circle) := by
    intro x hx
    have hpt := (φ.symm x).property
    cases hpt with
    | inl h =>
      exfalso; apply hx; rw [← hφp]
      exact (φ.apply_symm_apply x).symm ▸
        congrArg φ (Subtype.ext h)
    | inr h => exact h
  -- Define σ : ZMod a1 → ZMod a1
  let σ : ZMod a1 → ZMod a1 := fun x =>
    if hx : x = v then w
    else ψ ⟨(φ.symm x).val, Or.inr (hφ_symm_in_T x hx)⟩
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 2: σ is IsCohom (preserves non-adjacency)
  -- ═══════════════════════════════════════════════════════════════════
  -- For x, y both ≠ v: follows from φ, ψ being graph isos on common T
  -- For x = v: uses degree regularity of fractionGraph
  have hσ_cohom : IsCohom (fractionGraph a1 q) (fractionGraph a1 q) σ := by
    intro x y hxy hnadj
    constructor
    · -- σ x ≠ σ y
      intro heq
      simp only [σ] at heq
      split_ifs at heq with hx hy hy
      · exact hxy (hx.trans hy.symm)
      · -- w = ψ(φ⁻¹(y).val, ...) → p' = φ⁻¹(y).val → p' ∈ T, contradiction
        have hinj := ψ.injective heq
        simp only [Subtype.mk.injEq] at hinj
        exact hp' (hinj ▸ hφ_symm_in_T y hy)
      · -- symmetric
        have hinj := ψ.injective heq.symm
        simp only [Subtype.mk.injEq] at hinj
        exact hp' (hinj ▸ hφ_symm_in_T x hx)
      · -- Both ≠ v: ψ injective → φ.symm x = φ.symm y → x = y
        have hinj := ψ.injective heq
        simp only [Subtype.mk.injEq] at hinj
        exact hxy (φ.symm.injective (Subtype.ext hinj))
    · -- ¬(fractionGraph a1 q).Adj (σ x) (σ y)
      -- First establish σ is injective (reusing the logic from above)
      have hσ_inj : Function.Injective σ := by
        intro a b heq
        simp only [σ] at heq
        split_ifs at heq with ha hb hb
        · exact ha.trans hb.symm
        · exfalso
          have hinj := ψ.injective heq
          simp only [Subtype.mk.injEq] at hinj
          exact hp' (hinj ▸ hφ_symm_in_T b hb)
        · exfalso
          have hinj := ψ.injective heq.symm
          simp only [Subtype.mk.injEq] at hinj
          exact hp' (hinj ▸ hφ_symm_in_T a ha)
        · have hinj := ψ.injective heq
          simp only [Subtype.mk.injEq] at hinj
          exact φ.symm.injective (Subtype.ext hinj)
      -- σ v = w
      have hσv : σ v = w := dif_pos rfl
      -- Key: for a ≠ v, b ≠ v, Adj a b ↔ Adj (σ a) (σ b)
      have hσ_adj_iff : ∀ a b : ZMod a1, a ≠ v → b ≠ v →
          ((fractionGraph a1 q).Adj a b ↔
           (fractionGraph a1 q).Adj (σ a) (σ b)) := by
        intro a b ha hb
        have hσa : σ a = ψ ⟨(φ.symm a).val,
            Or.inr (hφ_symm_in_T a ha)⟩ := dif_neg ha
        have hσb : σ b = ψ ⟨(φ.symm b).val,
            Or.inr (hφ_symm_in_T b hb)⟩ := dif_neg hb
        rw [hσa, hσb, ψ.map_rel_iff]
        -- Goal: Adj a b ↔ (G.induce (insert p' T)).Adj ⟨_, _⟩ ⟨_, _⟩
        -- Both sides are definitionally G.Adj (φ.symm a).val (φ.symm b).val
        constructor
        · intro hadj
          -- Adj a b → (G.induce (insert p T)).Adj (φ.symm a) (φ.symm b)
          exact φ.symm.map_rel_iff.mpr hadj
        · intro hadj
          -- (G.induce (insert p' T)).Adj ⟨_,_⟩ ⟨_,_⟩ is G.Adj on .val
          -- which equals (G.induce (insert p T)).Adj (φ.symm a) (φ.symm b)
          exact φ.symm.map_rel_iff.mp hadj
      -- Degree regularity via nonAdjFinset_translate
      classical
      let N : ZMod a1 → Finset (ZMod a1) := fun u =>
        Finset.univ.filter fun z => (fractionGraph a1 q).Adj u z
      -- Partition: Finset.univ = N u ∪ nonAdjFinset ∪ {u}
      have hN_partition : ∀ u : ZMod a1,
          (N u).card + (nonAdjFinset a1 q u).card + 1 =
            (Finset.univ : Finset (ZMod a1)).card := by
        intro u
        have hpart : Finset.univ =
            N u ∪ nonAdjFinset a1 q u ∪ {u} := by
          ext z
          simp only [N, nonAdjFinset, Finset.mem_univ,
            Finset.mem_union, Finset.mem_filter,
            Finset.mem_singleton, true_and]
          constructor
          · intro _
            by_cases hzu : z = u
            · right; exact hzu
            · left
              by_cases hadj : (fractionGraph a1 q).Adj u z
              · left; exact hadj
              · right; exact ⟨hzu, hadj⟩
          · intro _; trivial
        have hdisj1 : Disjoint (N u) (nonAdjFinset a1 q u) :=
          Finset.disjoint_left.mpr fun z hz1 hz2 =>
            (Finset.mem_filter.mp hz2).2.2 (Finset.mem_filter.mp hz1).2
        have hdisj2 :
            Disjoint (N u ∪ nonAdjFinset a1 q u) {u} := by
          rw [Finset.disjoint_singleton_right]
          intro hmem
          rcases Finset.mem_union.mp hmem with h | h
          · exact absurd (Finset.mem_filter.mp h).2
              ((fractionGraph a1 q).loopless.irrefl u)
          · exact (Finset.mem_filter.mp h).2.1 rfl
        rw [hpart, Finset.card_union_of_disjoint hdisj2,
          Finset.card_union_of_disjoint hdisj1,
          Finset.card_singleton]
      have hN_card_eq : ∀ u₁ u₂ : ZMod a1,
          (N u₁).card = (N u₂).card := by
        intro u₁ u₂
        have hna : (nonAdjFinset a1 q u₁).card =
            (nonAdjFinset a1 q u₂).card := by
          have h0 := nonAdjFinset_translate a1 q u₁ 0
          rw [zero_add] at h0
          have h0' := nonAdjFinset_translate a1 q u₂ 0
          rw [zero_add] at h0'
          calc (nonAdjFinset a1 q u₁).card
              = (nonAdjFinset a1 q 0).card := by
                rw [← h0]
                exact Finset.card_image_of_injective
                  _ (fun (a b : ZMod a1) (h : a + u₁ = b + u₁) =>
                    add_right_cancel h)
            _ = (nonAdjFinset a1 q u₂).card := by
                rw [← h0']
                exact (Finset.card_image_of_injective
                  _ (fun (a b : ZMod a1) (h : a + u₂ = b + u₂) =>
                    add_right_cancel h)).symm
        have := hN_partition u₁
        have := hN_partition u₂
        omega
      -- Helper: σ z ≠ w when z ≠ v
      have hσ_ne_w : ∀ z : ZMod a1, z ≠ v → σ z ≠ w := by
        intro z hzv heq
        exact hzv (hσ_inj (heq.trans hσv.symm))
      -- Counting argument for one-vertex-is-v cases
      -- Given: u ≠ v, ¬Adj v u, prove ¬Adj w (σ u)
      -- σ maps (N u).erase v into (N (σ u)).erase w
      -- v ∉ N u (since ¬Adj u v), so |(N u).erase v| = |N u|
      -- If w ∈ N (σ u): |(N (σ u)).erase w| = |N (σ u)| - 1
      -- But |N u| = |N (σ u)| by regularity, contradiction.
      have hcounting : ∀ u : ZMod a1, u ≠ v →
          ¬(fractionGraph a1 q).Adj v u →
          ¬(fractionGraph a1 q).Adj w (σ u) := by
        intro u hu hnadj_vu
        -- σ maps (N u).erase v into (N (σ u)).erase w
        have hmap : ∀ z ∈ (N u).erase v,
            σ z ∈ (N (σ u)).erase w := by
          intro z hz
          have hzv : z ≠ v := (Finset.mem_erase.mp hz).1
          have hz_adj : (fractionGraph a1 q).Adj u z :=
            (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).2
          have hσ_adj : (fractionGraph a1 q).Adj (σ u) (σ z) :=
            ((hσ_adj_iff z u hzv hu).mp hz_adj.symm).symm
          exact Finset.mem_erase.mpr ⟨hσ_ne_w z hzv,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ_adj⟩⟩
        have hinj_on :
            Set.InjOn σ ((N u).erase v : Set (ZMod a1)) :=
          fun a _ b _ hab => hσ_inj hab
        have hle : ((N u).erase v).card ≤
            ((N (σ u)).erase w).card :=
          Finset.card_le_card_of_injOn σ hmap hinj_on
        -- v ∉ N u since ¬Adj u v
        have hnadj_uv : ¬(fractionGraph a1 q).Adj u v :=
          fun h => hnadj_vu h.symm
        have hv_notin : v ∉ N u :=
          fun h => hnadj_uv (Finset.mem_filter.mp h).2
        rw [Finset.erase_eq_of_notMem hv_notin] at hle
        -- By contradiction: assume Adj w (σ u)
        intro hadj_w
        have hw_in : w ∈ N (σ u) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj_w.symm⟩
        rw [Finset.card_erase_of_mem hw_in] at hle
        have := hN_card_eq u (σ u)
        have : 0 < (N (σ u)).card := Finset.card_pos.mpr ⟨w, hw_in⟩
        omega
      -- Case split on x = v, y = v
      by_cases hxv : x = v
      · -- Case x = v: need ¬Adj (σ v) (σ y) = ¬Adj w (σ y)
        have hyv : y ≠ v := fun h => hxy (hxv.trans h.symm)
        rw [hxv, hσv]
        exact hcounting y hyv (hxv ▸ hnadj)
      · by_cases hyv : y = v
        · -- Case y = v: need ¬Adj (σ x) w
          rw [hyv, hσv]
          have hnadj_vx : ¬(fractionGraph a1 q).Adj v x :=
            hyv ▸ fun h => hnadj h.symm
          exact fun h => hcounting x hxv hnadj_vx h.symm
        · -- Both ≠ v: direct from hσ_adj_iff
          exact fun hadj => hnadj ((hσ_adj_iff x y hxv hyv).mpr hadj)
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 3: σ is rotation or reflection
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨a, hform⟩ := fractionGraph_selfCohom_form a1 q hq_ge h2q hcoprime σ hσ_cohom
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 4: Compute σ(v-1) and σ(v+1)
  -- ═══════════════════════════════════════════════════════════════════
  -- σ(v-1) = ψ(φ⁻¹(v-1)) = ψ(t1) since φ(t1) = v-1
  have hσ_vm1 : σ (v - 1) = ψ ⟨t1, Or.inr ht1⟩ := by
    have hne : v - 1 ≠ v := by
      intro h; haveI : Fact (1 < a1) := ⟨by omega⟩
      exact absurd (show (1 : ZMod a1) = 0 from by
        have : v - (v - 1) = v - v := congr_arg (v - ·) h
        simp [sub_sub_cancel] at this) one_ne_zero
    simp only [σ, dif_neg hne]
    congr 1; apply Subtype.ext; simp only
    have : φ.symm (v - 1) = ⟨t1, Or.inr ht1⟩ := by
      apply φ.injective; rw [φ.apply_symm_apply]; exact hφt1.symm ▸ rfl
    exact congrArg Subtype.val this
  -- σ(v+1) = ψ(t2) similarly
  have hσ_vp1 : σ (v + 1) = ψ ⟨t2, Or.inr ht2⟩ := by
    have hne : v + 1 ≠ v := by
      intro h; haveI : Fact (1 < a1) := ⟨by omega⟩
      exact absurd (show (1 : ZMod a1) = 0 from by
        have : v + 1 - v = v - v := congr_arg (· - v) h
        simp at this) one_ne_zero
    simp only [σ, dif_neg hne]
    congr 1; apply Subtype.ext; simp only
    have : φ.symm (v + 1) = ⟨t2, Or.inr ht2⟩ := by
      apply φ.injective; rw [φ.apply_symm_apply]; exact hφt2.symm ▸ rfl
    exact congrArg Subtype.val this
  -- σ(v) = w
  have hσ_v : σ v = w := by simp only [σ, dif_pos rfl]
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 5: Rotation/reflection maps {v-1,v+1} to {w-1,w+1}
  -- ═══════════════════════════════════════════════════════════════════
  have hψt1t2 : ({ψ ⟨t1, Or.inr ht1⟩, ψ ⟨t2, Or.inr ht2⟩} : Set (ZMod a1)) =
      {w - 1, w + 1} := by
    rcases hform with hrot | hrefl
    · -- Rotation: σ(x) = a + x
      have h1 := hrot v; rw [hσ_v] at h1 -- w = a + v
      have h2 := hrot (v - 1); rw [hσ_vm1] at h2 -- ψ(t1) = a + (v-1) = w - 1
      have h3 := hrot (v + 1); rw [hσ_vp1] at h3 -- ψ(t2) = a + (v+1) = w + 1
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl)
        · left; rw [h2, h1]; ring
        · right; rw [h3, h1]; ring
      · rintro (rfl | rfl)
        · left; rw [h2, h1]; ring
        · right; rw [h3, h1]; ring
    · -- Reflection: σ(x) = a - x
      have h1 := hrefl v; rw [hσ_v] at h1 -- w = a - v
      have h2 := hrefl (v - 1); rw [hσ_vm1] at h2 -- ψ(t1) = a - (v-1) = w + 1
      have h3 := hrefl (v + 1); rw [hσ_vp1] at h3 -- ψ(t2) = a - (v+1) = w - 1
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl)
        · right; rw [h2, h1]; ring
        · left; rw [h3, h1]; ring
      · rintro (rfl | rfl)
        · right; rw [h3, h1]; ring
        · left; rw [h2, h1]; ring
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 6: Apply fractionGraph_iso_preserves_arc_containment to ψ
  -- ═══════════════════════════════════════════════════════════════════
  -- From hψt1t2, either ψ(t1)=w-1,ψ(t2)=w+1 or ψ(t1)=w+1,ψ(t2)=w-1
  -- In both cases, (t1, p', t2) or (t2, p', t1) are consecutive under ψ
  -- Apply fractionGraph_iso_preserves_arc_containment to get the arc containment
  have hS_p' : (insert p' (T : Set Circle)).Finite :=
    Set.Finite.insert p' (Finset.finite_toSet T)
  have hcard_p' : hS_p'.toFinset.card = a1 := by
    rw [Set.Finite.toFinset_insert, Finset.card_insert_of_notMem (by
      rwa [Set.Finite.mem_toFinset, Finset.mem_coe]), Finset.finite_toSet_toFinset]
    omega
  -- The arc containment for ψ gives the result via case split on rotation vs reflection
  rcases hform with hrot | hrefl
  · -- ══ Rotation case: σ(x) = a + x, so ψ(t1) = w-1, ψ(t2) = w+1 ══
    have h_av : w = a + v := by have := hrot v; rwa [hσ_v] at this
    have hψt1_eq : ψ ⟨t1, Or.inr ht1⟩ = w - 1 := by
      have h := hrot (v - 1); rw [hσ_vm1] at h; rw [h, h_av]; ring
    have hψt2_eq : ψ ⟨t2, Or.inr ht2⟩ = w + 1 := by
      have h := hrot (v + 1); rw [hσ_vp1] at h; rw [h, h_av]; ring
    have ht1_ne_p' : t1 ≠ p' := fun h => hp' (h ▸ ht1)
    have hp'_ne_t2 : p' ≠ t2 := fun h => hp' (h ▸ ht2)
    exact fun t htT ht_ne_t1 ht_ne_t2 =>
      fractionGraph_iso_preserves_arc_containment G a1 q ha1_ge hq_ge hq_pos h2q hcoprime
        (insert p' ↑T) hS_p' hcard_p' ψ hG_mono hG_ccw_trans
        t1 p' t2 (Or.inr ht1) (Set.mem_insert p' ↑T) (Or.inr ht2)
        ht1_ne_p' hp'_ne_t2 ht1_ne_t2 w hψt1_eq hw_def.symm hψt2_eq
        t (Or.inr htT) ht_ne_t1 ht_ne_t2
  · -- ══ Reflection case: σ(x) = a - x, so ψ(t1) = w+1, ψ(t2) = w-1 ══
    have h_av : w = a - v := by have := hrefl v; rwa [hσ_v] at this
    have hψt1_eq : ψ ⟨t1, Or.inr ht1⟩ = w + 1 := by
      have h := hrefl (v - 1); rw [hσ_vm1] at h; rw [h, h_av]; ring
    have hψt2_eq : ψ ⟨t2, Or.inr ht2⟩ = w - 1 := by
      have h := hrefl (v + 1); rw [hσ_vp1] at h; rw [h, h_av]; ring
    -- Proof by contradiction
    intro t htT ht_ne_t1 ht_ne_t2 ⟨h_lt_p', h_p'_lt_t2⟩
    have ht_ne_p' : t ≠ p' := fun h => hp' (h ▸ htT)
    have ht2_ne_p' : t2 ≠ p' := fun h => hp' (h ▸ ht2)
    have ht1_ne_p' : t1 ≠ p' := fun h => hp' (h ▸ ht1)
    -- ψ(p') = ψ(t2) + 1 (consecutive pair (t2, p'))
    have hψ_consec1 : ψ ⟨p', Set.mem_insert p' ↑T⟩ = ψ ⟨t2, Or.inr ht2⟩ + 1 := by
      rw [hw_def.symm, hψt2_eq]; ring
    -- Apply fractionGraph_iso_consecutive_or_reversed with (u=t2, v=p')
    rcases fractionGraph_iso_consecutive_or_reversed G a1 q ha1_ge hq_ge h2q hcoprime
      (insert p' ↑T) hS_p' hcard_p' ψ hG_mono hG_ccw_trans
      t2 p' (Or.inr ht2) (Set.mem_insert p' ↑T) ht2_ne_p' hψ_consec1 with h_left1 | h_right1
    · -- Left(t2,p'): no S'-point ccw-closer to t2 than p'
      -- ∀ s ∈ S', s ≠ t2 → s ≠ p' → ¬(repFrom t2 s < repFrom t2 p')
      -- But repFrom t2 t < repFrom t2 p' (from arc arithmetic), contradiction
      exact h_left1 t (Or.inr htT) ht_ne_t2 ht_ne_p' (by
        have := repFrom_ordered t1 t t2 (le_of_lt (lt_trans h_lt_p' h_p'_lt_t2))
        have := repFrom_ordered t1 p' t2 (le_of_lt h_p'_lt_t2)
        have := repFrom_add_repFrom_eq_one t2 t ht_ne_t2
        have := repFrom_add_repFrom_eq_one t2 p' ht2_ne_p'.symm
        linarith)
    · -- Right(t2,p'): p' is ccw-farthest from t2
      -- Apply fractionGraph_iso_consecutive_or_reversed with (u=p', v=t1)
      have hψ_consec2 : ψ ⟨t1, Or.inr ht1⟩ = ψ ⟨p', Set.mem_insert p' ↑T⟩ + 1 := by
        rw [hψt1_eq, hw_def.symm]
      rcases fractionGraph_iso_consecutive_or_reversed G a1 q ha1_ge hq_ge h2q hcoprime
        (insert p' ↑T) hS_p' hcard_p' ψ hG_mono hG_ccw_trans
        p' t1 (Set.mem_insert p' ↑T) (Or.inr ht1) ht1_ne_p'.symm hψ_consec2 with h_left2 | h_right2
      · -- Left(p',t1): impossible — t2 violates it
        -- ∀ s ∈ S', s ≠ p' → s ≠ t1 → ¬(repFrom p' s < repFrom p' t1)
        -- But repFrom p' t2 < repFrom p' t1 (since repFrom t1 t2 < 1)
        exact h_left2 t2 (Or.inr ht2) ht2_ne_p' ht1_ne_t2.symm (by
          have := repFrom_ordered t1 p' t2 (le_of_lt h_p'_lt_t2)
          have := repFrom_add_repFrom_eq_one p' t1 ht1_ne_p'
          linarith [repFrom_lt_one t1 t2])
      · -- Right(p',t1): t1 is ccw-farthest from p'
        -- repFrom p' t < repFrom p' t1 (from h_right2), but arithmetic gives the opposite
        have h := h_right2 t (Or.inr htT) ht_ne_p' ht_ne_t1
        have := repFrom_ordered t1 t p' (le_of_lt h_lt_p')
        have := repFrom_add_repFrom_eq_one p' t ht_ne_p'
        have := repFrom_add_repFrom_eq_one p' t1 ht1_ne_p'
        linarith [repFrom_pos_of_ne t1 t ht_ne_t1]

/-- Key helper: When T has a1-1 points and both T ∪ {p} and T ∪ {p'} induce E_{a1/q},
    then p and p' are in the same "cyclic gap" of T.

    Proof idea:
    1. T ≃ E_{a1/q} \ {v} ≃ E_{predecessor(a1,q)} (by vertex removal theorem)
    2. This "missing vertex" structure has a unique gap of width 2/a1
    3. For T ∪ {p} to reconstruct E_{a1/q}, p must fill this unique gap
    4. Same for p'
    5. Therefore p and p' have the same cyclic neighbors in T

    This is the core geometric insight behind same_slot_of_shared_skeleton. -/
lemma insertion_same_gap_of_both_iso_to_fraction
    (G : SimpleGraph Circle)
    (a1 q : ℕ) [NeZero a1] (ha1_ge : 3 ≤ a1) (hq_ge : 2 ≤ q) (hq_pos : 0 < q)
    (h2q : 2 * q ≤ a1) (hcoprime : Nat.Coprime a1 q)
    (T : Finset Circle) (hT_card : T.card = a1 - 1)
    (p p' : Circle) (hp : p ∉ T) (hp' : p' ∉ T) (hpp' : p ≠ p')
    (hiso_p : Nonempty (G.induce
        (insert p (T : Set Circle)) ≃g fractionGraph a1 q))
    (hiso_p' : Nonempty (G.induce
        (insert p' (T : Set Circle)) ≃g fractionGraph a1 q))
    (hG_mono : ∀ u v w : Circle, u ≠ v → u ≠ w →
      G.Adj u w → dist u v < dist u w → G.Adj u v)
    (hG_ccw_trans : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
      G.Adj u w → G.Adj u v → repFrom u v < repFrom u w → repFrom u w ≤ 1/2 → G.Adj v w) :
    -- p and p' have the same cyclic neighbors in T
    ∃ t1 t2 : Circle, t1 ∈ T ∧ t2 ∈ T ∧ t1 ≠ t2 ∧
      -- p is in the arc from t1 to t2 (not containing other T points)
      (∀ t ∈ T, t ≠ t1 → t ≠ t2 →
        ¬(repFrom t1 t < repFrom t1 p ∧
          repFrom t1 p < repFrom t1 t2)) ∧
      -- p' is in the same arc
      (∀ t ∈ T, t ≠ t1 → t ≠ t2 →
        ¬(repFrom t1 t < repFrom t1 p' ∧
          repFrom t1 p' < repFrom t1 t2)) := by
  -- ════════════════════════════════════════════════════════════════════════════
  -- PROOF OUTLINE (Gap Uniqueness Argument)
  -- ════════════════════════════════════════════════════════════════════════════
  --
  -- Key insight: Both T ∪ {p} and T ∪ {p'} induce E_{a1/q}, where T is common.
  -- The isomorphism structure constrains p and p' to be in the same "gap" of T.
  --
  -- Detailed structure:
  -- 1. From hiso_p, get φ: T ∪ {p} ≃g E_{a1/q}. Let v = φ(p).
  -- 2. The restriction φ|T: T → E_{a1/q} \ {v} is a graph isomorphism.
  -- 3. From hiso_p', get ψ: T ∪ {p'} ≃g E_{a1/q}. Let w = ψ(p').
  -- 4. The restriction ψ|T: T → E_{a1/q} \ {w} is also a graph isomorphism.
  -- 5. The composition σ := ψ|T ∘ (φ|T)⁻¹: E_{a1/q}\{v} → E_{a1/q}\{w}
  --    extends to an automorphism of E_{a1/q} (mapping v to w).
  -- 6. By fractionGraph_selfIso_form, σ is a rotation (x ↦ a+x) or reflection (x ↦ a-x).
  -- 7. Both rotations and reflections map {v-1, v+1} to {w-1, w+1} as sets.
  -- 8. Define t1 = φ⁻¹(v+1), t2 = φ⁻¹(v-1). Then {t1, t2} = ψ⁻¹({w-1, w+1}).
  -- 9. The cyclic neighbors of v in E_{a1/q} are v±1. By isomorphism, t1, t2 are
  --    the "gap boundary" points for both p and p' in T.
  -- 10. Therefore p and p' are both in the arc from t2 to t1 (the same gap).
  --
  -- FORMALIZATION STATUS:
  -- This proof requires formalizing cyclic order on finite Circle subsets and
  -- showing the graph isomorphism preserves the "gap boundary" structure.
  -- Key helper needed: The cyclic neighbors in E_{a1/q} (vertices v±1) correspond
  -- to the Circle-cyclic neighbors of the inserted point.
  --
  -- ════════════════════════════════════════════════════════════════════════════
  -- Extract the isomorphisms
  classical
  obtain ⟨φ⟩ := hiso_p
  obtain ⟨ψ⟩ := hiso_p'
  -- Get v = φ(p) and w = ψ(p')
  have hp_mem : p ∈ insert p (T : Set Circle) := Set.mem_insert p T
  have hp'_mem : p' ∈ insert p' (T : Set Circle) := Set.mem_insert p' T
  let p_sub : ↑(insert p (T : Set Circle)) := ⟨p, hp_mem⟩
  let p'_sub : ↑(insert p' (T : Set Circle)) := ⟨p', hp'_mem⟩
  let v : ZMod a1 := φ p_sub
  let w : ZMod a1 := ψ p'_sub
  -- Define t1, t2 as preimages of v-1 and v+1 (note: swapped order for correct cyclic direction)
  -- t1 = φ⁻¹(v-1) = predecessor, t2 = φ⁻¹(v+1) = successor
  -- This ensures repFrom t1 p < repFrom t1 t2 (p is between t1 and t2 in positive direction)
  -- First, show v+1 ≠ v and v-1 ≠ v (need a1 ≥ 2)
  have ha1_pos : 0 < a1 := NeZero.pos a1
  have ha1_ge_2 : 2 ≤ a1 := le_trans (by norm_num : (2 : ℕ) ≤ 3) ha1_ge
  -- 1 ≠ 0 in ZMod a1 when a1 ≥ 2
  have h1_ne_0 : (1 : ZMod a1) ≠ 0 := by
    intro h1eq
    have ha1_ne_1 : a1 ≠ 1 := by omega
    have hval : (1 : ZMod a1).val = 1 := ZMod.val_one'' ha1_ne_1
    rw [h1eq, ZMod.val_zero] at hval
    omega
  have hv_ne_v_plus : v + 1 ≠ v := by
    intro h
    have : (1 : ZMod a1) = 0 := by
      calc (1 : ZMod a1) = (v + 1) - v := by ring
        _ = v - v := by rw [h]
        _ = 0 := sub_self v
    exact h1_ne_0 this
  have hv_ne_v_minus : v - 1 ≠ v := by
    intro h
    have : (1 : ZMod a1) = 0 := by
      calc (1 : ZMod a1) = v - (v - 1) := by ring
        _ = v - v := by rw [h]
        _ = 0 := sub_self v
    exact h1_ne_0 this
  -- φ.symm (v - 1) is in insert p T, and since v-1 ≠ v, it's in T (this will be t1)
  have hv_minus_mem : (φ.symm (v - 1)).val ∈ insert p (T : Set Circle) :=
    (φ.symm (v - 1)).property
  have hv_minus_ne_p : (φ.symm (v - 1)).val ≠ p := by
    intro h
    have h1 : φ.symm (v - 1) = p_sub := Subtype.ext h
    have h2 : v - 1 = v := by
      calc v - 1 = φ (φ.symm (v - 1)) := (φ.apply_symm_apply (v - 1)).symm
        _ = φ p_sub := by rw [h1]
        _ = v := rfl
    exact hv_ne_v_minus h2
  have ht1_mem : (φ.symm (v - 1)).val ∈ (T : Set Circle) := by
    cases hv_minus_mem with
    | inl h => exact (hv_minus_ne_p h).elim
    | inr h => exact h
  -- φ.symm (v + 1) is in insert p T, and since v+1 ≠ v, it's in T (this will be t2)
  have hv_plus_mem : (φ.symm (v + 1)).val ∈ insert p (T : Set Circle) :=
    (φ.symm (v + 1)).property
  have hv_plus_ne_p : (φ.symm (v + 1)).val ≠ p := by
    intro h
    have h1 : φ.symm (v + 1) = p_sub := Subtype.ext h
    have h2 : v + 1 = v := by
      calc v + 1 = φ (φ.symm (v + 1)) := (φ.apply_symm_apply (v + 1)).symm
        _ = φ p_sub := by rw [h1]
        _ = v := rfl
    exact hv_ne_v_plus h2
  have ht2_mem : (φ.symm (v + 1)).val ∈ (T : Set Circle) := by
    cases hv_plus_mem with
    | inl h => exact (hv_plus_ne_p h).elim
    | inr h => exact h
  -- Define t1 = φ⁻¹(v-1) and t2 = φ⁻¹(v+1) (swapped for correct cyclic order)
  let t1 : Circle := (φ.symm (v - 1)).val
  let t2 : Circle := (φ.symm (v + 1)).val
  -- Show t1 ≠ t2 (since v-1 ≠ v+1 when a1 ≥ 3, or a1 = 2 requires special handling)
  have ht1_ne_t2 : t1 ≠ t2 := by
    intro h
    have h1 : φ.symm (v - 1) = φ.symm (v + 1) := Subtype.ext h
    have h2 : v - 1 = v + 1 := φ.symm.injective h1
    -- v - 1 = v + 1 implies 2 = 0 in ZMod a1
    have h2_eq_0 : (2 : ZMod a1) = 0 := by
      calc (2 : ZMod a1) = (v + 1) - (v - 1) := by ring
        _ = (v - 1) - (v - 1) := by rw [h2]
        _ = 0 := sub_self _
    -- 2 ≠ 0 in ZMod a1 when a1 > 2
    by_cases ha1_eq_2 : a1 = 2
    · -- a1 = 2 contradicts ha1_ge : 3 ≤ a1
      omega
    · have h2_ne_0 : (2 : ZMod a1) ≠ 0 := by
        intro h2eq
        have hval : (2 : ZMod a1).val = 2 := ZMod.val_cast_of_lt (by omega : 2 < a1)
        rw [h2eq, ZMod.val_zero] at hval
        omega
      exact h2_ne_0 h2_eq_0
  -- Now use t1, t2 as the witnesses
  use t1, t2
  refine ⟨ht1_mem, ht2_mem, ht1_ne_t2, ?_, ?_⟩
  · -- gap_p: p is in the arc from t1 to t2
    intro t htT ht_ne_t1 ht_ne_t2
    -- Apply the arc containment lemma
    let S : Set Circle := insert p (T : Set Circle)
    have hS_finite : S.Finite := Set.Finite.insert p (Finset.finite_toSet T)
    have hS_card : hS_finite.toFinset.card = a1 := by
      have h1 : hS_finite.toFinset = insert p T := by
        ext x
        simp only [Set.Finite.mem_toFinset, Finset.mem_insert]
        constructor
        · intro hx
          cases hx with
          | inl h => left; exact h
          | inr h => right; exact h
        · intro hx
          cases hx with
          | inl h => left; exact h
          | inr h => right; exact h
      rw [h1, Finset.card_insert_of_notMem hp, hT_card]
      omega
    have ht1_in_S : t1 ∈ S := Or.inr ht1_mem
    have hp_in_S : p ∈ S := Set.mem_insert p T
    have ht2_in_S : t2 ∈ S := Or.inr ht2_mem
    have ht_in_S : t ∈ S := Or.inr htT
    -- Show the φ conditions
    have hφt1 : φ ⟨t1, ht1_in_S⟩ = v - 1 := by
      have h : (⟨t1, ht1_in_S⟩ : ↑S) = φ.symm (v - 1) := Subtype.ext rfl
      rw [h]
      exact φ.apply_symm_apply (v - 1)
    have hφp : φ ⟨p, hp_in_S⟩ = v := by
      have h : (⟨p, hp_in_S⟩ : ↑S) = p_sub := Subtype.ext rfl
      simp only [h, v]
    have hφt2 : φ ⟨t2, ht2_in_S⟩ = v + 1 := by
      have h : (⟨t2, ht2_in_S⟩ : ↑S) = φ.symm (v + 1) := Subtype.ext rfl
      rw [h]
      exact φ.apply_symm_apply (v + 1)
    have ht1_ne_p : t1 ≠ p := hv_minus_ne_p
    have hp_ne_t2 : p ≠ t2 := fun h => hv_plus_ne_p h.symm
    exact fractionGraph_iso_preserves_arc_containment G a1 q ha1_ge hq_ge hq_pos h2q hcoprime
      S hS_finite hS_card φ hG_mono hG_ccw_trans
      t1 p t2 ht1_in_S hp_in_S ht2_in_S ht1_ne_p hp_ne_t2 ht1_ne_t2 v hφt1 hφp hφt2 t ht_in_S
      ht_ne_t1 ht_ne_t2
  --
  -- FOR p': We use the automorphism argument to show the same t1, t2 work.
  --
  -- ALGEBRAIC ARGUMENT:
  -- Let w = ψ(p'). The composition σ := ψ|_T ∘ (φ|_T)⁻¹ : ZMod a1 \ {v} → ZMod a1 \ {w}
  -- extends to an automorphism of E_{a1/q} (since both φ and ψ are graph isomorphisms).
  -- By fractionGraph_selfIso_form, σ is either:
  --   - Rotation: σ(x) = a + x for some a ∈ ZMod a1
  --   - Reflection: σ(x) = a - x for some a ∈ ZMod a1
  --
  -- Both rotations and reflections map cyclic neighbors to cyclic neighbors:
  --   - Rotation: σ({v-1, v+1}) = {a+v-1, a+v+1} = {σ(v)-1, σ(v)+1}
  --   - Reflection: σ({v-1, v+1}) = {a-v+1, a-v-1} = {σ(v)+1, σ(v)-1}
  --
  -- If σ(v) = w (which follows from the graph structure), then:
  --   σ({v-1, v+1}) = {w-1, w+1}
  --
  -- Since t1 = φ⁻¹(v-1) and t2 = φ⁻¹(v+1), we have:
  --   {ψ(t1), ψ(t2)} = {σ(v-1), σ(v+1)} = {w-1, w+1}
  --
  -- This means t1 and t2 are also the preimages of w±1 under ψ (possibly swapped).
  -- Therefore, t1 and t2 serve as the cyclic neighbors of p' just as they do for p.
  --
  · -- gap_p': p' is in the same arc
    intro t htT ht_ne_t1 ht_ne_t2
    -- Apply the automorphism lemma
    -- First, establish the φ conditions from the earlier proof
    have hp_in_pT : p ∈ insert p (T : Set Circle) := Set.mem_insert p T
    have ht1_in_pT : t1 ∈ (T : Set Circle) := ht1_mem
    have ht2_in_pT : t2 ∈ (T : Set Circle) := ht2_mem
    have hφt1' : φ ⟨t1, Or.inr ht1_in_pT⟩ = v - 1 := by
      have h : (⟨t1, Or.inr ht1_in_pT⟩ : ↑(insert p (T : Set Circle))) =
          φ.symm (v - 1) :=
        Subtype.ext rfl
      rw [h]
      exact φ.apply_symm_apply (v - 1)
    have hφp' : φ ⟨p, hp_in_pT⟩ = v := rfl
    have hφt2' : φ ⟨t2, Or.inr ht2_in_pT⟩ = v + 1 := by
      have h : (⟨t2, Or.inr ht2_in_pT⟩ : ↑(insert p (T : Set Circle))) = φ.symm (v + 1) :=
        Subtype.ext rfl
      rw [h]
      exact φ.apply_symm_apply (v + 1)
    exact fractionGraph_iso_preserves_arc_containment_automorphism G a1 q ha1_ge hq_ge hq_pos
      h2q hcoprime T hT_card
      p p' hp hp' hpp' φ ψ hG_mono hG_ccw_trans
      t1 t2 ht1_in_pT ht2_in_pT ht1_ne_t2 v hφt1' hφp' hφt2'
      t htT ht_ne_t1 ht_ne_t2

/-- Core disjunction: p' is "near" t1 or "near" t2 in the skeleton.

When both T ∪ {p} and T ∪ {p'} induce E_{a1/q}, the automorphism σ = ψ∘φ⁻¹
is a rotation or reflection. By composing φ with the fractionGraph reflection
x ↦ 2v-x (which swaps v-1 and v+1), we can apply the automorphism lemma from
both perspectives and then case-split.

Reference: Lemma 5.3. -/
lemma fractionGraph_iso_arc_containment_disjunction
    (G : SimpleGraph Circle)
    (a1 q : ℕ) [NeZero a1] (ha1_ge : 3 ≤ a1) (hq_ge : 2 ≤ q) (hq_pos : 0 < q)
    (h2q : 2 * q ≤ a1) (hcoprime : Nat.Coprime a1 q)
    (T : Finset Circle) (hT_card : T.card = a1 - 1)
    (p p' : Circle) (hp : p ∉ T) (hp' : p' ∉ T) (hpp' : p ≠ p')
    (φ : G.induce (insert p (T : Set Circle)) ≃g fractionGraph a1 q)
    (ψ : G.induce (insert p' (T : Set Circle)) ≃g fractionGraph a1 q)
    (hG_mono : ∀ u v w : Circle, u ≠ v → u ≠ w →
      G.Adj u w → dist u v < dist u w → G.Adj u v)
    (hG_ccw_trans : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
      G.Adj u w → G.Adj u v → repFrom u v < repFrom u w →
      repFrom u w ≤ 1/2 → G.Adj v w)
    (t1 t2 : Circle) (ht1 : t1 ∈ T) (ht2 : t2 ∈ T)
    (ht1_ne_t2 : t1 ≠ t2)
    (v : ZMod a1)
    (hφt1 : φ ⟨t1, Or.inr ht1⟩ = v - 1)
    (hφp : φ ⟨p, Set.mem_insert p T⟩ = v)
    (hφt2 : φ ⟨t2, Or.inr ht2⟩ = v + 1) :
    (∀ t ∈ (T : Set Circle), t ≠ t1 →
      ¬(0 < repFrom t1 t ∧ repFrom t1 t < repFrom t1 p')) ∨
    (∀ t ∈ (T : Set Circle), t ≠ t2 →
      ¬(0 < repFrom t2 t ∧ repFrom t2 t < repFrom t2 p')) := by
  have weak_t1 := fractionGraph_iso_preserves_arc_containment_automorphism
    G a1 q ha1_ge hq_ge hq_pos h2q hcoprime T hT_card
    p p' hp hp' hpp' φ ψ hG_mono hG_ccw_trans
    t1 t2 ht1 ht2 ht1_ne_t2 v hφt1 hφp hφt2
  let r := ConvexRound.fractionGraph_reflection a1 q (2 * v)
  let φ' := φ.trans r
  have hφ't2 : φ' ⟨t2, Or.inr ht2⟩ = v - 1 := by
    change r (φ ⟨t2, Or.inr ht2⟩) = v - 1
    rw [hφt2]
    change (2 * v - (v + 1) : ZMod a1) = v - 1
    ring
  have hφ'p : φ' ⟨p, Set.mem_insert p T⟩ = v := by
    change r (φ ⟨p, Set.mem_insert p T⟩) = v
    rw [hφp]
    change (2 * v - v : ZMod a1) = v
    ring
  have hφ't1 : φ' ⟨t1, Or.inr ht1⟩ = v + 1 := by
    change r (φ ⟨t1, Or.inr ht1⟩) = v + 1
    rw [hφt1]
    change (2 * v - (v - 1) : ZMod a1) = v + 1
    ring
  have weak_t2 := fractionGraph_iso_preserves_arc_containment_automorphism
    G a1 q ha1_ge hq_ge hq_pos h2q hcoprime T hT_card
    p p' hp hp' hpp' φ' ψ hG_mono hG_ccw_trans
    t2 t1 ht2 ht1 ht1_ne_t2.symm v hφ't2 hφ'p hφ't1
  by_cases h_case : repFrom t1 p' < repFrom t1 t2
  · left
    intro t htT ht_ne_t1 ⟨_, h_lt_p'⟩
    by_cases ht_eq_t2 : t = t2
    · rw [ht_eq_t2] at h_lt_p'; linarith
    · exact weak_t1 t htT ht_ne_t1 ht_eq_t2 ⟨h_lt_p', h_case⟩
  · push_neg at h_case
    right
    have hp'_ne_t2 : p' ≠ t2 := fun h => hp' (h ▸ ht2)
    have h_t2_p'_eq : repFrom t2 p' = repFrom t1 p' - repFrom t1 t2 :=
      repFrom_ordered t1 t2 p' h_case
    have h_t2_t1_eq : repFrom t2 t1 = 1 - repFrom t1 t2 := by
      linarith [repFrom_add_repFrom_eq_one t1 t2 ht1_ne_t2.symm]
    have h_t2_p'_lt_t2_t1 : repFrom t2 p' < repFrom t2 t1 := by
      rw [h_t2_p'_eq, h_t2_t1_eq]
      linarith [repFrom_lt_one t1 p']
    intro t htT ht_ne_t2 ⟨_, h_lt_p'⟩
    by_cases ht_eq_t1 : t = t1
    · rw [ht_eq_t1] at h_lt_p'; linarith
    · exact weak_t2 t htT ht_ne_t2 ht_eq_t1 ⟨h_lt_p', h_t2_p'_lt_t2_t1⟩

/-- Full slot analysis: When T ∪ {p} and T ∪ {p'} both induce E_{a1/q}, there exist
    t1, t2 ∈ T such that p is in the arc from t1 to t2 with no T-points between
    t1 and p, no T-points between p and t2, and p' is near either t1 or t2.

    This strengthens `insertion_same_gap_of_both_iso_to_fraction` by additionally
    providing arc containment and two-sided emptiness. -/
private lemma insertion_full_slot_analysis
    (G : SimpleGraph Circle)
    (a1 q : ℕ) [NeZero a1] (ha1_ge : 3 ≤ a1) (hq_ge : 2 ≤ q) (hq_pos : 0 < q)
    (h2q : 2 * q ≤ a1) (hcoprime : Nat.Coprime a1 q)
    (T : Finset Circle) (hT_card : T.card = a1 - 1)
    (p p' : Circle) (hp : p ∉ T) (hp' : p' ∉ T) (hpp' : p ≠ p')
    (hiso_p : Nonempty (G.induce (insert p (T : Set Circle)) ≃g fractionGraph a1 q))
    (hiso_p' : Nonempty (G.induce (insert p' (T : Set Circle)) ≃g fractionGraph a1 q))
    (hG_mono : ∀ u v w : Circle, u ≠ v → u ≠ w →
      G.Adj u w → dist u v < dist u w → G.Adj u v)
    (hG_ccw_trans : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
      G.Adj u w → G.Adj u v → repFrom u v < repFrom u w → repFrom u w ≤ 1/2 → G.Adj v w) :
    ∃ t1 t2 : Circle, t1 ∈ T ∧ t2 ∈ T ∧ t1 ≠ t2 ∧
      repFrom t1 p + repFrom p t2 ≤ repFrom t1 t2 ∧
      ((∀ t ∈ (T : Set Circle), t ≠ t1 →
        ¬(0 < repFrom t1 t ∧ repFrom t1 t < repFrom t1 p')) ∨
       (∀ t ∈ (T : Set Circle), t ≠ t2 →
        ¬(0 < repFrom t2 t ∧ repFrom t2 t < repFrom t2 p'))) ∧
      (∀ t ∈ (T : Set Circle), t ≠ t1 →
        ¬(0 < repFrom t1 t ∧ repFrom t1 t < repFrom t1 p)) ∧
      (∀ t ∈ (T : Set Circle), t ≠ t2 →
        ¬(0 < repFrom p t ∧ repFrom p t < repFrom p t2)) := by
  -- ════════════════════════════════════════════════════════════════════════════
  -- SETUP: Extract isomorphism and define cyclic neighbors
  -- ════════════════════════════════════════════════════════════════════════════
  classical
  obtain ⟨φ⟩ := hiso_p
  obtain ⟨ψ⟩ := hiso_p'
  have hp_mem : p ∈ insert p (T : Set Circle) := Set.mem_insert p T
  let p_sub : ↑(insert p (T : Set Circle)) := ⟨p, hp_mem⟩
  let v : ZMod a1 := φ p_sub
  -- S = insert p T
  let S : Set Circle := insert p (T : Set Circle)
  have hS_finite : S.Finite := Set.Finite.insert p (Finset.finite_toSet T)
  have hS_card : hS_finite.toFinset.card = a1 := by
    have h1 : hS_finite.toFinset = insert p T := by
      ext x
      simp only [Set.Finite.mem_toFinset, Finset.mem_insert]
      constructor
      · intro hx; cases hx with | inl h => left; exact h | inr h => right; exact h
      · intro hx; cases hx with | inl h => left; exact h | inr h => right; exact h
    rw [h1, Finset.card_insert_of_notMem hp, hT_card]; omega
  -- ZMod a1 facts
  have h1_ne_0 : (1 : ZMod a1) ≠ 0 := by
    intro h1eq
    have hval : (1 : ZMod a1).val = 1 := ZMod.val_one'' (by omega : a1 ≠ 1)
    rw [h1eq, ZMod.val_zero] at hval; omega
  have hv_ne_v_plus : v + 1 ≠ v := by
    intro h; exact h1_ne_0 (by calc (1 : ZMod a1) = (v + 1) - v := by ring
      _ = v - v := by rw [h]
      _ = 0 := sub_self v)
  have hv_ne_v_minus : v - 1 ≠ v := by
    intro h; exact h1_ne_0 (by calc (1 : ZMod a1) = v - (v - 1) := by ring
      _ = v - v := by rw [h]
      _ = 0 := sub_self v)
  -- φ.symm(v-1) ∈ T (this is t1)
  have hv_minus_ne_p : (φ.symm (v - 1)).val ≠ p := by
    intro h
    have h1 : φ.symm (v - 1) = p_sub := Subtype.ext h
    exact hv_ne_v_minus (by calc v - 1 = φ (φ.symm (v - 1)) := (φ.apply_symm_apply _).symm
      _ = φ p_sub := by rw [h1]
      _ = v := rfl)
  have ht1_mem : (φ.symm (v - 1)).val ∈ (T : Set Circle) := by
    cases (φ.symm (v - 1)).property with
    | inl h => exact (hv_minus_ne_p h).elim | inr h => exact h
  -- φ.symm(v+1) ∈ T (this is t2)
  have hv_plus_ne_p : (φ.symm (v + 1)).val ≠ p := by
    intro h
    have h1 : φ.symm (v + 1) = p_sub := Subtype.ext h
    exact hv_ne_v_plus (by calc v + 1 = φ (φ.symm (v + 1)) := (φ.apply_symm_apply _).symm
      _ = φ p_sub := by rw [h1]
      _ = v := rfl)
  have ht2_mem : (φ.symm (v + 1)).val ∈ (T : Set Circle) := by
    cases (φ.symm (v + 1)).property with
    | inl h => exact (hv_plus_ne_p h).elim | inr h => exact h
  let t1 : Circle := (φ.symm (v - 1)).val
  let t2 : Circle := (φ.symm (v + 1)).val
  have ht1_ne_t2 : t1 ≠ t2 := by
    intro h
    have h1 : φ.symm (v - 1) = φ.symm (v + 1) := Subtype.ext h
    have h2 : v - 1 = v + 1 := φ.symm.injective h1
    have h2_eq_0 : (2 : ZMod a1) = 0 := by
      calc (2 : ZMod a1) = (v + 1) - (v - 1) := by ring
        _ = (v - 1) - (v - 1) := by rw [h2]
        _ = 0 := sub_self _
    have h2_ne_0 : (2 : ZMod a1) ≠ 0 := by
      intro h2eq
      have hval : (2 : ZMod a1).val = 2 := ZMod.val_cast_of_lt (by omega : 2 < a1)
      rw [h2eq, ZMod.val_zero] at hval; omega
    exact h2_ne_0 h2_eq_0
  -- φ conditions
  have hφt1 : φ ⟨t1, Or.inr ht1_mem⟩ = v - 1 := by
    have h : (⟨t1, Or.inr ht1_mem⟩ : ↑S) = φ.symm (v - 1) := Subtype.ext rfl
    rw [h]; exact φ.apply_symm_apply (v - 1)
  have hφt2 : φ ⟨t2, Or.inr ht2_mem⟩ = v + 1 := by
    have h : (⟨t2, Or.inr ht2_mem⟩ : ↑S) = φ.symm (v + 1) := Subtype.ext rfl
    rw [h]; exact φ.apply_symm_apply (v + 1)
  -- Consecutive condition for (t1, p)
  have hconsec : φ ⟨p, hp_mem⟩ = φ ⟨t1, Or.inr ht1_mem⟩ + 1 := by
    rw [hφt1]; change v = (v - 1) + 1; ring
  -- ════════════════════════════════════════════════════════════════════════════
  -- ORIENTATION CASE SPLIT
  -- ════════════════════════════════════════════════════════════════════════════
  rcases fractionGraph_iso_consecutive_or_reversed G a1 q ha1_ge hq_ge h2q hcoprime
    S hS_finite hS_card φ hG_mono hG_ccw_trans
    t1 p (Or.inr ht1_mem) hp_mem (show t1 ≠ p from hv_minus_ne_p) hconsec
    with hcase_a | hcase_b
  · -- ════════════════════════════════════════════════════════════════════════
    -- CASE A: Order-preserving (p nearest to t1 counterclockwise)
    -- ════════════════════════════════════════════════════════════════════════
    use t1, t2
    have ht2_ne_p : t2 ≠ p := hv_plus_ne_p
    have hp_le_t2 : repFrom t1 p ≤ repFrom t1 t2 := by
      by_contra hgt; push_neg at hgt
      exact hcase_a t2 (Or.inr ht2_mem) (Ne.symm ht1_ne_t2) ht2_ne_p (lt_of_lt_of_le hgt le_rfl)
    refine ⟨ht1_mem, ht2_mem, ht1_ne_t2, ?_, ?_, ?_, ?_⟩
    -- A.1: Arc containment
    · linarith [repFrom_ordered t1 p t2 hp_le_t2]
    -- A.2: p'-disjunction
    · exact fractionGraph_iso_arc_containment_disjunction G a1 q ha1_ge hq_ge hq_pos
        h2q hcoprime T hT_card p p' hp hp' hpp' φ ψ hG_mono hG_ccw_trans
        t1 t2 ht1_mem ht2_mem ht1_ne_t2 v hφt1 rfl hφt2
    -- A.3: Left emptiness (no T-point between t1 and p)
    · intro t htT ht_ne_t1 ⟨_, hlt⟩
      have ht_ne_p : t ≠ p := fun h => hp (h ▸ Finset.mem_coe.mp htT)
      exact hcase_a t (Or.inr htT) ht_ne_t1 ht_ne_p hlt
    -- A.4: Right emptiness (no T-point between p and t2)
    · -- Apply consecutive_or_reversed to (p, t2)
      have hconsec2 : φ ⟨t2, Or.inr ht2_mem⟩ = φ ⟨p, hp_mem⟩ + 1 := by
        rw [hφt2]
      rcases fractionGraph_iso_consecutive_or_reversed G a1 q ha1_ge hq_ge h2q hcoprime
        S hS_finite hS_card φ hG_mono hG_ccw_trans
        p t2 hp_mem (Or.inr ht2_mem) (Ne.symm ht2_ne_p) hconsec2
        with hcase_a2 | hcase_b2
      · -- A2: t2 nearest to p → emptiness holds
        intro t htT ht_ne_t2 ⟨_, hlt⟩
        have ht_ne_p : t ≠ p := fun h => hp (h ▸ Finset.mem_coe.mp htT)
        exact hcase_a2 t (Or.inr htT) ht_ne_p ht_ne_t2 hlt
      · -- B2: IMPOSSIBLE (1 < repFrom t1 t2)
        exfalso
        have h1 := hcase_b2 t1 (Or.inr ht1_mem) hv_minus_ne_p ht1_ne_t2
        -- repFrom p t1 < repFrom p t2
        -- repFrom p t1 = 1 - repFrom t1 p, repFrom p t2 = repFrom t1 t2 - repFrom t1 p
        have h_pt1 := repFrom_add_repFrom_eq_one t1 p (Ne.symm hv_minus_ne_p)
        have h_pt2 := repFrom_ordered t1 p t2 hp_le_t2
        linarith [repFrom_lt_one t1 t2]
  · -- ════════════════════════════════════════════════════════════════════════
    -- CASE B: Order-reversing (p farthest from t1) → SWAP witnesses
    -- ════════════════════════════════════════════════════════════════════════
    use t2, t1
    have ht2_ne_p : t2 ≠ p := hv_plus_ne_p
    have hp_ne_t1 : p ≠ t1 := hv_minus_ne_p.symm
    have ht1_lt_p : repFrom t1 t2 < repFrom t1 p :=
      hcase_b t2 (Or.inr ht2_mem) (Ne.symm ht1_ne_t2) ht2_ne_p
    have ht2_le_p : repFrom t1 t2 ≤ repFrom t1 p := le_of_lt ht1_lt_p
    refine ⟨ht2_mem, ht1_mem, ht1_ne_t2.symm, ?_, ?_, ?_, ?_⟩
    -- B.1: Arc containment (repFrom t2 p + repFrom p t1 ≤ repFrom t2 t1)
    · have h_t2p := repFrom_ordered t1 t2 p ht2_le_p
      have h_pt1 := repFrom_add_repFrom_eq_one t1 p (Ne.symm hv_minus_ne_p)
      have h_t2t1 := repFrom_add_repFrom_eq_one t1 t2 (Ne.symm ht1_ne_t2)
      linarith
    -- B.2: p'-disjunction (use reflected isomorphism)
    · let r := ConvexRound.fractionGraph_reflection a1 q (2 * v)
      let φ' := φ.trans r
      have hφ't2 : φ' ⟨t2, Or.inr ht2_mem⟩ = v - 1 := by
        change r (φ ⟨t2, Or.inr ht2_mem⟩) = v - 1
        rw [hφt2]; change (2 * v - (v + 1) : ZMod a1) = v - 1; ring
      have hφ'p : φ' ⟨p, hp_mem⟩ = v := by
        change r (φ ⟨p, hp_mem⟩) = v; change (2 * v - v : ZMod a1) = v; ring
      have hφ't1 : φ' ⟨t1, Or.inr ht1_mem⟩ = v + 1 := by
        change r (φ ⟨t1, Or.inr ht1_mem⟩) = v + 1
        rw [hφt1]; change (2 * v - (v - 1) : ZMod a1) = v + 1; ring
      exact fractionGraph_iso_arc_containment_disjunction G a1 q ha1_ge hq_ge hq_pos
        h2q hcoprime T hT_card p p' hp hp' hpp' φ' ψ hG_mono hG_ccw_trans
        t2 t1 ht2_mem ht1_mem ht1_ne_t2.symm v hφ't2 hφ'p hφ't1
    -- B.3: Left emptiness (no T-point between t2 and p)
    · let r := ConvexRound.fractionGraph_reflection a1 q (2 * v)
      let φ' := φ.trans r
      have hconsec_B : φ' ⟨p, hp_mem⟩ = φ' ⟨t2, Or.inr ht2_mem⟩ + 1 := by
        change r (φ ⟨p, hp_mem⟩) = r (φ ⟨t2, Or.inr ht2_mem⟩) + 1
        rw [hφt2]; change (2 * v - v : ZMod a1) = (2 * v - (v + 1)) + 1; ring
      rcases fractionGraph_iso_consecutive_or_reversed G a1 q ha1_ge hq_ge h2q hcoprime
        S hS_finite hS_card φ' hG_mono hG_ccw_trans
        t2 p (Or.inr ht2_mem) hp_mem (show t2 ≠ p from ht2_ne_p) hconsec_B
        with hcase_a' | hcase_b'
      · intro t htT ht_ne_t2 ⟨_, hlt⟩
        have ht_ne_p : t ≠ p := fun h => hp (h ▸ Finset.mem_coe.mp htT)
        exact hcase_a' t (Or.inr htT) ht_ne_t2 ht_ne_p hlt
      · exfalso
        have h1 := hcase_b' t1 (Or.inr ht1_mem) ht1_ne_t2 hv_minus_ne_p
        have h_t2t1 := repFrom_add_repFrom_eq_one t1 t2 (Ne.symm ht1_ne_t2)
        have h_t2p := repFrom_ordered t1 t2 p ht2_le_p
        linarith [repFrom_lt_one t1 p]
    -- B.4: Right emptiness (no T-point between p and t1)
    · intro t htT ht_ne_t1 ⟨hpos, hlt⟩
      have ht_ne_p : t ≠ p := fun h => hp (h ▸ Finset.mem_coe.mp htT)
      have h_order := hcase_b t (Or.inr htT) ht_ne_t1 ht_ne_p
      -- repFrom t1 t < repFrom t1 p, need: ¬(repFrom p t < repFrom p t1)
      have h_tp := repFrom_ordered t1 t p (le_of_lt h_order)
      have h_pt := repFrom_add_repFrom_eq_one t p (Ne.symm ht_ne_p)
      have h_pt1 := repFrom_add_repFrom_eq_one t1 p (Ne.symm hv_minus_ne_p)
      -- repFrom p t = 1 - repFrom t p = 1 - (repFrom t1 p - repFrom t1 t)
      -- repFrom p t1 = 1 - repFrom t1 p
      -- So repFrom p t - repFrom p t1 = repFrom t1 t > 0
      linarith [repFrom_pos_of_ne t1 t ht_ne_t1]

/-! ### Finite Induced Subgraph Preservation

The key insight (Lemma 5.3) is that any finite
induced subgraph of a circle graph is equivalent to a fraction graph. Moreover, when
S ≃ E_{p/q} for a convergent p/q, and f is a self-cohomomorphism, then f(S) ≃ E_{p/q}.

This follows from:
1. f(S) is equivalent to some E_{a/b} (by finite_induce)
2. Cohom E_{p/q} E_{a/b} (composition through f)
3. p/q ≤ a/b (cohom ordering via fractionGraph_ordering_reverse)
4. a/b ≤ r (f(S) is in circle graph with parameter r)
5. a ≤ |f(S)| ≤ |S| = p (core property + cohom doesn't increase size)
6. By CFA best approximation: if p/q ≤ a/b ≤ r with a ≤ p, then a/b = p/q
7. Therefore f(S) ≃ E_{p/q}

This is proved below from finite_induce_closed/finite_induce_open
and convergent_best_approx_from_below.
-/

/-! #### Folding Lemma for Nested Neighborhoods

If `N(i) ⊆ N(j)` and `G.Adj i j`, then the retraction mapping `j ↦ i` (identity
elsewhere) is a cohomomorphism from `G` to itself. The key observation: since
`N(i) ⊆ N(j)`, any vertex non-adjacent to `j` is also non-adjacent to `i`.
Combined with corestriction to `V \ {j}` and inclusion, this gives cohom-equivalence
between `G` and `G.induce (V \ {j})`. -/

/-- If N(i) ⊆ N(j) in G, the retraction mapping j ↦ i (identity elsewhere)
    is a cohomomorphism from G to G, provided G.Adj i j. Since N(i) ⊆ N(j),
    non-adjacent pairs involving j become non-adjacent pairs involving i. -/
theorem retraction_isCohom_of_nested {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (i j : V) (_hij : i ≠ j)
    (hadj : G.Adj i j)
    (hnested : G.neighborSet i ⊆ G.neighborSet j) :
    IsCohom G G (fun v => if v = j then i else v) := by
  set f : V → V := fun v => if v = j then i else v with hf_def
  have hfj : f j = i := if_pos rfl
  have hfne : ∀ v, v ≠ j → f v = v := fun v hv => if_neg hv
  intro u v huv hnadj
  constructor
  · -- f(u) ≠ f(v)
    intro heq
    by_cases huj : u = j
    · -- u = j, f(u) = i
      have hfu : f u = i := by rw [huj, hfj]
      rw [hfu] at heq
      by_cases hvj : v = j
      · exact huv (huj.trans hvj.symm)
      · rw [hfne v hvj] at heq
        -- heq: i = v, huj: u = j, hnadj: ¬G.Adj u v
        -- Need: G.Adj u v = G.Adj j i. hadj.symm: G.Adj j i.
        rw [huj, ← heq] at hnadj; exact hnadj hadj.symm
    · -- u ≠ j, f(u) = u
      rw [hfne u huj] at heq
      by_cases hvj : v = j
      · have hfv : f v = i := by rw [hvj, hfj]
        rw [hfv] at heq
        -- u = i, v = j, ¬G.Adj i j contradicts hadj
        rw [heq, hvj] at hnadj; exact hnadj hadj
      · rw [hfne v hvj] at heq
        exact huv heq
  · -- ¬G.Adj (f u) (f v)
    intro hadj'
    by_cases huj : u = j
    · have hfu : f u = i := by rw [huj, hfj]
      rw [hfu] at hadj'
      by_cases hvj : v = j
      · exact huv (huj.trans hvj.symm)
      · rw [hfne v hvj] at hadj'
        -- G.Adj i v, N(i) ⊆ N(j), so G.Adj j v
        rw [huj] at hnadj; exact hnadj (hnested hadj')
    · rw [hfne u huj] at hadj'
      by_cases hvj : v = j
      · have hfv : f v = i := by rw [hvj, hfj]
        rw [hfv] at hadj'
        -- G.Adj u i, N(i) ⊆ N(j), so G.Adj j u, so G.Adj u j
        rw [hvj] at hnadj
        exact hnadj ((hnested hadj'.symm).symm)
      · rw [hfne v hvj] at hadj'
        exact hnadj hadj'

/-- Inclusion of an induced subgraph is a cohomomorphism. -/
theorem inclusion_isCohom {V : Type*} (G : SimpleGraph V) (S : Set V) :
    IsCohom (G.induce S) G (fun s => s.val) := by
  intro ⟨u, hu⟩ ⟨v, hv⟩ huv hnadj
  exact ⟨fun h => huv (Subtype.ext h), hnadj⟩

/-- If N(i) ⊆ N(j) and G.Adj i j, then G and G.induce (V \ {j}) are
    cohom-equivalent. Forward: retraction j ↦ i. Reverse: inclusion. -/
theorem nested_folding_cohom {V : Type*}
    (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hadj : G.Adj i j)
    (hnested : G.neighborSet i ⊆ G.neighborSet j) :
    Cohom G (G.induce (Set.univ \ {j})) ∧
    Cohom (G.induce (Set.univ \ {j})) G := by
  classical
  constructor
  · -- Forward: retraction j ↦ i, corestricted to V \ {j}
    have hf_cohom :=
      retraction_isCohom_of_nested G i j hij hadj hnested
    have hf_mem : ∀ v, (if v = j then i else v) ∈
        Set.univ \ ({j} : Set V) := by
      intro v
      simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
        true_and]
      split_ifs with h
      · intro h2; exact hij h2
      · exact h
    exact ⟨fun v => ⟨if v = j then i else v, hf_mem v⟩,
      isCohom_corestrict _ hf_cohom _ hf_mem⟩
  · -- Reverse: inclusion
    exact ⟨fun s => s.val, inclusion_isCohom G _⟩

/-- If N(i) ⊆ N(j), then ¬G.Adj i j.
    Proof: If G.Adj i j, then j ∈ N(i) ⊆ N(j), contradicting irreflexivity. -/
theorem not_adj_of_neighborSet_subset {V : Type*}
    (G : SimpleGraph V) (i j : V)
    (hnested : G.neighborSet i ⊆ G.neighborSet j) :
    ¬G.Adj i j := by
  intro hadj
  exact G.loopless.irrefl j (hnested hadj)

/-- Complement-direction nested folding: if N(i) ⊆ N(j), then Gᶜ and
    (G.induce (V \ {i}))ᶜ are cohom-equivalent.
    Unlike nested_folding_cohom (which works on G, needs G.Adj i j),
    this works on complements and USES ¬G.Adj i j.
    Forward: retraction i ↦ j. Reverse: inclusion. -/
theorem nested_folding_complement_cohom {V : Type*}
    (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hnested : G.neighborSet i ⊆ G.neighborSet j) :
    Cohom Gᶜ (G.induce (Set.univ \ {i}))ᶜ ∧
    Cohom (G.induce (Set.univ \ {i}))ᶜ Gᶜ := by
  classical
  have hnadj : ¬G.Adj i j := not_adj_of_neighborSet_subset G i j hnested
  constructor
  · -- Forward: retraction i ↦ j, corestricted to V \ {i}
    refine ⟨fun v => if h : v = i then
        ⟨j, Set.mem_diff_singleton.mpr ⟨Set.mem_univ _, hij.symm⟩⟩
      else ⟨v, Set.mem_diff_singleton.mpr ⟨Set.mem_univ _, h⟩⟩,
      fun u v huv hnadj_compl => ?_⟩
    simp only [SimpleGraph.compl_adj] at hnadj_compl
    push_neg at hnadj_compl
    have hadj : G.Adj u v := hnadj_compl huv
    by_cases hu : u = i
    · -- u = i
      have hvi : v ≠ i := fun h => huv (hu.trans h.symm)
      have hadj_jv : G.Adj j v := hnested (by subst hu; exact hadj)
      simp only [dif_pos hu, dif_neg hvi]
      refine ⟨fun heq => ?_, fun ⟨_, h⟩ => h hadj_jv⟩
      simp only [Subtype.mk.injEq] at heq
      exact absurd (heq ▸ hadj_jv) (G.loopless.irrefl v)
    · by_cases hv : v = i
      · -- v = i
        have hadj_uj : G.Adj u j :=
          G.symm (hnested (G.symm (by subst hv; exact hadj)))
        simp only [dif_neg hu, dif_pos hv]
        refine ⟨fun heq => ?_, fun ⟨_, h⟩ => h hadj_uj⟩
        simp only [Subtype.mk.injEq] at heq
        exact absurd (heq ▸ hadj_uj) (G.loopless.irrefl j)
      · -- u ≠ i, v ≠ i
        simp only [dif_neg hu, dif_neg hv]
        exact ⟨fun heq => huv (congr_arg Subtype.val heq),
          fun ⟨_, h⟩ => h hadj⟩
  · -- Reverse: inclusion (subtype coercion)
    -- Edges of G.induce(V\{i}) are edges of G, trivially preserved.
    refine ⟨fun s => s.val, fun u v huv hnadj_compl => ?_⟩
    simp only [SimpleGraph.compl_adj] at hnadj_compl ⊢
    push_neg at hnadj_compl ⊢
    have hadj_ind := hnadj_compl huv
    exact ⟨fun h => huv (Subtype.ext h), fun _ => hadj_ind⟩

/-- distMod is positive for distinct elements. -/
private lemma distMod_pos_of_ne' (N : ℕ) [NeZero N] {k l : ZMod N} (hkl : k ≠ l) :
    0 < distMod N k l := by
  by_contra h
  push_neg at h
  have h0 : distMod N k l = 0 := by omega
  simp only [distMod] at h0
  rcases Nat.min_eq_zero_iff.mp h0 with hval | hval
  · exact hkl (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp hval))
  · exact absurd (Nat.sub_eq_zero_iff_le.mp hval) (not_le.mpr (k - l).val_lt)

/-! #### Convex-Round Graphs are Cohom-Equivalent to Fraction Graphs

The main theorem: every convex-round graph on n vertices is cohom-equivalent
to some fraction graph E_{a/b}. This is proved by strong induction on n using
the BJH02 trichotomy:
- Bipartite case: cohom-equivalent to E_{n/1} (edgeless) or fold + recurse
- Fraction graph case: coprime reduction via fractionGraph_cohomomorphism
- Circular clique case: complement analysis + circular chromatic number
- Nested neighborhood case: complement folding via nested_folding_complement_cohom

The strong induction is needed for the nested neighborhood case (Case 4),
where we remove a vertex by folding and apply the induction hypothesis
to the smaller graph on n-1 vertices. -/

-- Helper lemmas for CyclicInterval membership through the skip-d embedding.
-- These are extracted as standalone lemmas to keep omega's context clean.

private lemma cyclicInterval_skipEmbed_neq {n : ℕ} (hn : 3 ≤ n)
    (d l h_hi : Fin n) (j : Fin (n - 1))
    (hld : l.val ≠ d.val) (hhd : h_hi.val ≠ d.val) :
    haveI : NeZero n := ⟨by omega⟩
    haveI : NeZero (n - 1) := ⟨by omega⟩
    (if j.val < d.val then (⟨j.val, by omega⟩ : Fin n) else ⟨j.val + 1, by omega⟩) ∈
      ConvexRound.CyclicInterval n l h_hi ↔
    j ∈ ConvexRound.CyclicInterval (n - 1)
      (⟨if l.val < d.val then l.val else l.val - 1, by split_ifs <;> omega⟩)
      (⟨if h_hi.val < d.val then h_hi.val else h_hi.val - 1, by split_ifs <;> omega⟩) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (n - 1) := ⟨by omega⟩
  simp only [ConvexRound.CyclicInterval]
  constructor <;> intro hmem
  all_goals split_ifs at hmem ⊢
  all_goals simp only [Set.mem_setOf_eq] at hmem ⊢
  all_goals omega

private lemma cyclicInterval_skipEmbed_dEqL {n : ℕ} (hn : 3 ≤ n)
    (d h_hi : Fin n) (j : Fin (n - 1))
    (hhd : h_hi.val ≠ d.val) :
    haveI : NeZero n := ⟨by omega⟩
    haveI : NeZero (n - 1) := ⟨by omega⟩
    (if j.val < d.val then (⟨j.val, by omega⟩ : Fin n) else ⟨j.val + 1, by omega⟩) ∈
      ConvexRound.CyclicInterval n d h_hi ↔
    j ∈ ConvexRound.CyclicInterval (n - 1)
      (⟨if d.val + 1 < n then d.val else 0, by split_ifs <;> omega⟩)
      (⟨if h_hi.val < d.val then h_hi.val else h_hi.val - 1, by split_ifs <;> omega⟩) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (n - 1) := ⟨by omega⟩
  simp only [ConvexRound.CyclicInterval]
  constructor <;> intro hmem
  all_goals split_ifs at hmem ⊢
  all_goals simp only [Set.mem_setOf_eq] at hmem ⊢
  all_goals omega

private lemma cyclicInterval_skipEmbed_dEqH {n : ℕ} (hn : 3 ≤ n)
    (d l : Fin n) (j : Fin (n - 1))
    (hld : l.val ≠ d.val) :
    haveI : NeZero n := ⟨by omega⟩
    haveI : NeZero (n - 1) := ⟨by omega⟩
    (if j.val < d.val then (⟨j.val, by omega⟩ : Fin n) else ⟨j.val + 1, by omega⟩) ∈
      ConvexRound.CyclicInterval n l d ↔
    j ∈ ConvexRound.CyclicInterval (n - 1)
      (⟨if l.val < d.val then l.val else l.val - 1, by split_ifs <;> omega⟩)
      (⟨if 0 < d.val then d.val - 1 else n - 2, by split_ifs <;> omega⟩) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (n - 1) := ⟨by omega⟩
  simp only [ConvexRound.CyclicInterval]
  constructor <;> intro hmem
  all_goals split_ifs at hmem ⊢
  all_goals simp only [Set.mem_setOf_eq] at hmem ⊢
  all_goals omega

set_option maxHeartbeats 400000 in
-- strong induction with complex trichotomy case split
/-- Auxiliary lemma: strong induction version of convexRound_cohom_equiv_fractionGraph.
    The NeZero instance is passed explicitly to enable clean induction on n.
    Note: The conclusion uses Gᶜ (complement) because IsConvexRoundEnum represents
    far-side graphs, while cohom-equivalence to fraction graphs holds for the
    complement (close-side). Per BJH02 Theorem 3.1 (BJH02.tex §3): convex-round
    graphs are homomorphically equivalent to circular cliques, so their complements
    are cohomomorphically equivalent to fraction graphs. -/
private theorem convexRound_cohom_equiv_fractionGraph_aux (n : ℕ) :
    ∀ (inst : NeZero n), 2 ≤ n →
    ∀ (G : SimpleGraph (Fin n)),
    @ConvexRound.IsConvexRoundEnum n inst G →
    (∃ u v : Fin n, u ≠ v ∧ ¬G.Adj u v) →
    ∃ (a b : ℕ) (ha_pos : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      Nat.Coprime a b ∧
      Cohom Gᶜ (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) ∧
      Cohom (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) Gᶜ := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro inst hn G hG hne
    haveI : NeZero n := inst
    -- Apply BJH02 trichotomy
    have htri := ConvexRound.convexRound_trichotomy n hn G hG
    rcases htri with hbip | ⟨q, hq, h2q, heq⟩ |
      ⟨d, hd, hdn, heq⟩ | ⟨i, hnested⟩
    · -- Case 1: Bipartite
      -- Bipartite = Colorable 2, so Gᶜ is cohom-equivalent to fractionGraph 2 1
      -- (which is the edgeless graph on ZMod 2, since distMod 2 0 1 = 1 ≥ 1).
      classical
      refine ⟨2, 1, by omega, by omega, by omega, Nat.coprime_one_right 2, ?_, ?_⟩
      · -- Cohom Gᶜ (fractionGraph 2 1)
        -- A 2-coloring of G gives a cohomomorphism from Gᶜ to fractionGraph 2 1
        obtain ⟨c⟩ := hbip  -- c : G.Coloring (Fin 2) = G.Coloring (ZMod 2)
        refine ⟨c, fun u v huv hnadj => ?_⟩
        simp only [SimpleGraph.compl_adj, not_and, not_not] at hnadj
        have hadj := hnadj huv
        exact ⟨c.valid hadj, fun ⟨_, hlt⟩ =>
          absurd hlt (not_lt.mpr (distMod_pos_of_ne' 2 (c.valid hadj)))⟩
      · -- Cohom (fractionGraph 2 1) Gᶜ
        -- Need an edge in G (from convex-roundness: vertex 0 has non-empty N)
        obtain ⟨l, _, hN, hnotmem⟩ := hG.neighborhood_isInterval (0 : Fin n)
        have hl_adj : G.Adj 0 l := by
          rw [show G.Adj 0 l ↔ l ∈ G.neighborSet 0 from Iff.rfl, hN]
          exact ⟨ConvexRound.left_mem_cyclicInterval l _,
            fun h => hnotmem (h ▸ ConvexRound.left_mem_cyclicInterval l _)⟩
        refine ⟨fun z => if z = 0 then (0 : Fin n) else l, fun u v huv hnadj => ?_⟩
        constructor
        · -- Distinctness of images
          have hne : (0 : Fin n) ≠ l := G.ne_of_adj hl_adj
          have hne' : l ≠ (0 : Fin n) := hne.symm
          fin_cases u <;> fin_cases v <;> simp_all <;> tauto
        · -- ¬Gᶜ.Adj (g u) (g v), i.e., g u = g v ∨ G.Adj (g u) (g v)
          simp only [SimpleGraph.compl_adj, not_and, not_not]
          intro _
          fin_cases u <;> fin_cases v <;> simp_all [G.adj_symm hl_adj] <;>
            first | exact hl_adj | exact G.adj_symm hl_adj | tauto
    · -- Case 2: G = fractionGraph n q (mapped to Fin n)
      -- Under IsConvexRoundEnum, the close-side (fractionGraph) case only produces
      -- complete graphs (2q > n), since close-side arcs centered at a vertex
      -- always contain the vertex, violating i ∉ CyclicInterval for non-complete graphs.
      -- Therefore this case is always handled by exfalso from hne.
      subst heq
      obtain ⟨u, v, huv, hnadj⟩ := hne
      -- Show the mapped fractionGraph must be complete under IsConvexRoundEnum.
      by_cases h2qn : n < 2 * q
      · -- Sub-case 2q > n: all pairs adjacent (distMod ≤ n/2 < q)
        exact absurd ((ConvexRound.mapped_fractionGraph_adj n q u v).mpr ⟨huv, by
          simp only [distMod]
          set d := (ConvexRound.finZModEquiv n u - ConvexRound.finZModEquiv n v).val
          have hd_lt : d < n := (ConvexRound.finZModEquiv n u - ConvexRound.finZModEquiv n v).val_lt
          by_cases hd : d ≤ n / 2
          · exact lt_of_le_of_lt (Nat.min_le_left d (n - d)) (by omega)
          · push_neg at hd
            exact lt_of_le_of_lt (Nat.min_le_right d (n - d)) (by omega)⟩) hnadj
      · -- Sub-case 2q ≤ n: contradiction from CyclicInterval analysis
        push_neg at h2qn
        exfalso
        obtain ⟨l, h_hi, hN0, hnotmem0⟩ := hG.neighborhood_isInterval (0 : Fin n)
        -- CyclicInterval for vertex 0 is non-wrapping
        have hl_le : l.val ≤ h_hi.val := by
          by_contra hgt; push_neg at hgt
          exact hnotmem0 ((ConvexRound.mem_cyclicInterval_of_gt hgt).mpr
            (Or.inr (Nat.zero_le _)))
        -- N(0) = CyclicInterval n l h_hi (since 0 ∉ CyclicInterval)
        have hN0_eq : ((fractionGraph n q).map (ConvexRound.zmodFinEquiv n).toEmbedding).neighborSet
            (0 : Fin n) = ConvexRound.CyclicInterval n l h_hi := by
          rw [hN0]; ext x; simp only [Set.mem_diff, Set.mem_singleton_iff]
          constructor
          · exact fun ⟨hx, _⟩ => hx
          · exact fun hx => ⟨hx, fun h => hnotmem0 (h ▸ hx)⟩
        by_cases hq1 : q = 1
        · -- q = 1: graph is edgeless, but CyclicInterval is non-empty
          have hl_mem := ConvexRound.left_mem_cyclicInterval l h_hi
          rw [← hN0_eq] at hl_mem
          simp only [SimpleGraph.mem_neighborSet,
            ConvexRound.mapped_fractionGraph_adj] at hl_mem
          have hpos := distMod_pos_of_ne' n
            ((ConvexRound.finZModEquiv n).injective.ne hl_mem.1)
          subst hq1; omega
        · -- q ≥ 2 with 2q ≤ n: use q-1, n-q+1, q to derive contradiction
          push_neg at hq1; have hq2 : 2 ≤ q := by omega
          have hn4 : 4 ≤ n := by omega
          -- Define key vertices
          set a : Fin n := ⟨q - 1, by omega⟩ -- at distMod q-1 from 0
          set b : Fin n := ⟨n - q + 1, by omega⟩ -- at distMod q-1 from 0 (other side)
          set c : Fin n := ⟨q, by omega⟩ -- at distMod q from 0
          -- a ∈ CyclicInterval (right endpoint of centered interval)
          have ha_mem : a ∈ ConvexRound.CyclicInterval n l h_hi := by
            rw [← hN0_eq, SimpleGraph.mem_neighborSet,
              ConvexRound.mapped_fractionGraph_adj]
            refine ⟨by simp [a, Fin.ext_iff]; omega, ?_⟩
            rw [ConvexRound.distMod_lt_iff_in_cyclic_interval n q hq h2qn]
            convert ConvexRound.right_mem_cyclicInterval _ _ using 1
            exact Fin.ext (by simp [a, Nat.zero_mod,
              Nat.mod_eq_of_lt (show q - 1 < n by omega)])
          -- b ∈ CyclicInterval (left endpoint of centered
          -- interval)
          have hb_mem :
              b ∈ ConvexRound.CyclicInterval n l h_hi := by
            rw [← hN0_eq, SimpleGraph.mem_neighborSet,
              ConvexRound.mapped_fractionGraph_adj]
            constructor
            · simp [b, Fin.ext_iff]
            · rw [ConvexRound.distMod_lt_iff_in_cyclic_interval
                n q hq h2qn]
              convert
                ConvexRound.left_mem_cyclicInterval _ _
                using 1
              exact Fin.ext (by
                simp only [b, Fin.val_zero]
                rw [Nat.mod_eq_of_lt (by omega :
                  0 + n - (q - 1) < n)]
                omega)
          -- c ∉ CyclicInterval (at distMod = q, not < q)
          have hc_nmem :
              c ∉ ConvexRound.CyclicInterval n l h_hi := by
            rw [← hN0_eq, SimpleGraph.mem_neighborSet,
              ConvexRound.mapped_fractionGraph_adj]
            intro ⟨_, hdist⟩
            have hge := distMod_ge_q_of_val_diff_in_range
              n q h2qn
              (ConvexRound.finZModEquiv n 0)
              (ConvexRound.finZModEquiv n c)
              (by simp [ConvexRound.finZModEquiv,
                ZMod.val_zero, ZMod.val_natCast])
              (by simp [ConvexRound.finZModEquiv, c,
                ZMod.val_cast_of_lt (show q < n by omega),
                ZMod.val_zero])
              (by simp [ConvexRound.finZModEquiv, c,
                ZMod.val_cast_of_lt (show q < n by omega),
                ZMod.val_zero]; omega)
            omega
          -- Non-wrapping: from a ∈ [l, h_hi], l ≤ q-1
          have ha_le : l.val ≤ q - 1 := by
            rw [ConvexRound.mem_cyclicInterval_of_le hl_le] at ha_mem
            exact ha_mem.1
          -- From c ∉ [l, h_hi] with l ≤ q: h_hi < q
          have hh_lt : h_hi.val < q := by
            rw [ConvexRound.mem_cyclicInterval_of_le hl_le] at hc_nmem
            simp only [c] at hc_nmem
            by_contra h; push_neg at h
            exact hc_nmem ⟨by omega, h⟩
          -- From b ∈ [l, h_hi]: n-q+1 ≤ h_hi
          have hb_le : n - q + 1 ≤ h_hi.val := by
            rw [ConvexRound.mem_cyclicInterval_of_le hl_le] at hb_mem
            exact hb_mem.2
          -- Contradiction: h_hi < q but h_hi ≥ n-q+1, and 2q ≤ n
          omega
    · -- Case 3: G = circularCliqueGraph n d (MAIN CASE)
      -- circularCliqueGraph n d has Adj ↔ distMod ≥ d (far-side).
      -- Its complement Gᶜ has Adj ↔ u ≠ v ∧ distMod < d (close-side).
      -- This complement is isomorphic to fractionGraph n d on ZMod n.
      -- We use fractionGraph_cohomomorphism for coprime reduction.
      subst heq
      set g := Nat.gcd n d with hg_def
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d (by omega)
      have hg_dvd_n : g ∣ n := Nat.gcd_dvd_left n d
      have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right n d
      set a := n / g with ha_def
      set b := d / g with hb_def
      have ha_pos : 0 < a := Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_n) hg_pos
      have hb_pos : 0 < b := Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_d) hg_pos
      have h2b_le_a : 2 * b ≤ a := by
        change 2 * (d / g) ≤ n / g
        rw [← Nat.mul_div_assoc 2 hg_dvd_d]
        exact Nat.div_le_div_right hdn
      have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hg_pos
      have h_nb_eq_ad : n * b = a * d := by
        have := Nat.div_mul_cancel hg_dvd_n
        have := Nat.div_mul_cancel hg_dvd_d
        nlinarith
      have h_ratio : (n : ℚ) / d = (a : ℚ) / b := by
        have hd_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hb_ne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [div_eq_div_iff hd_ne hb_ne]
        exact_mod_cast h_nb_eq_ad
      haveI : NeZero a := ⟨by omega⟩
      refine ⟨a, b, ha_pos, hb_pos, h2b_le_a, hcop, ?_, ?_⟩
      · -- Cohom Gᶜ (fractionGraph a b)
        -- Non-edges of Gᶜ are edges of circularCliqueGraph (distMod ≥ d),
        -- which are non-edges of fractionGraph n d. Use scaling.
        have hscale := fractionGraph_cohomomorphism n d a b hd (le_of_eq h_ratio)
        obtain ⟨f, hf⟩ := hscale
        exact ⟨f ∘ ConvexRound.finZModEquiv n, fun u v huv hnadj => by
          simp only [SimpleGraph.compl_adj] at hnadj
          push_neg at hnadj
          have hadj_G := hnadj huv
          have hne' : ConvexRound.finZModEquiv n u ≠ ConvexRound.finZModEquiv n v :=
            (ConvexRound.finZModEquiv n).injective.ne huv
          apply hf _ _ hne'
          intro ⟨_, hlt⟩
          exact Nat.not_lt.mpr hadj_G.2 hlt⟩
      · -- Cohom (fractionGraph a b) Gᶜ
        -- Non-edges of fractionGraph (distMod ≥ b) scale to non-edges of
        -- fractionGraph n d (distMod ≥ d), which are edges of circularCliqueGraph,
        -- i.e., non-edges of Gᶜ.
        have hscale := fractionGraph_cohomomorphism a b n d hb_pos (le_of_eq h_ratio.symm)
        obtain ⟨f, hf⟩ := hscale
        exact ⟨ConvexRound.zmodFinEquiv n ∘ f, fun u v huv hnadj => by
          obtain ⟨hne', hnadj'⟩ := hf u v huv hnadj
          constructor
          · exact (ConvexRound.zmodFinEquiv n).injective.ne hne'
          · -- ¬(circularCliqueGraph n d)ᶜ.Adj ...
            intro ⟨_, hnotadj⟩
            apply hnotadj
            -- (circularCliqueGraph n d).Adj (zmodFinEquiv n (f u)) (zmodFinEquiv n (f v))
            refine ⟨(ConvexRound.zmodFinEquiv n).injective.ne hne', ?_⟩
            -- d ≤ distMod n (finZModEquiv n (zmodFinEquiv n (f u))) ...
            simp only [ConvexRound.zmodFinEquiv, Function.comp_apply, Equiv.apply_symm_apply]
            -- d ≤ distMod n (f u) (f v)
            by_contra hlt
            push_neg at hlt
            exact hnadj' ⟨hne', hlt⟩⟩
    · -- Case 4: Nested neighborhoods
      -- Extract dominated/target vertices from the disjunction
      obtain ⟨d, t, hdt, hnested_dt⟩ :
          ∃ (d t : Fin n), d ≠ t ∧ G.neighborSet d ⊆ G.neighborSet t := by
        rcases hnested with h | h
        · exact ⟨i, i + 1, by
            intro h; have : i - i = i + 1 - i := congr_arg (· - i) h
            simp at this; omega, h⟩
        · exact ⟨i + 1, i, by
            intro h; have : i + 1 - (i + 1) = i - (i + 1) := congr_arg (· - (i + 1)) h
            simp at this; omega, h⟩
      -- Step 1: Apply complement-direction folding
      obtain ⟨hcohom_fwd, hcohom_rev⟩ :=
        nested_folding_complement_cohom G d t hdt hnested_dt
      -- Step 2: Transfer the induced subgraph to Fin (n-1), show convex-round
      -- This is the key technical step: removing a dominated vertex from a
      -- convex-round graph preserves convex-roundness up to relabeling.
      -- Define the embedding Fin (n-1) → Fin n that skips d
      let embed : Fin (n - 1) → Fin n := fun k =>
        if h : k.val < d.val then ⟨k.val, by omega⟩ else ⟨k.val + 1, by omega⟩
      have hembed_ne_d : ∀ k, embed k ≠ d := by
        intro k; simp only [embed]
        split_ifs with h
        · exact ne_of_apply_ne Fin.val (ne_of_lt h)
        · exact ne_of_apply_ne Fin.val
            (ne_of_gt (Nat.lt_succ_of_le (Nat.le_of_not_lt h)))
      have hembed_inj : Function.Injective embed := by
        intro a b hab; simp only [embed] at hab
        ext; split_ifs at hab with ha hb hb <;> simp [Fin.ext_iff] at hab <;> omega
      -- Define G' on Fin (n-1) via pullback along embed
      let G' : SimpleGraph (Fin (n - 1)) :=
        { Adj := fun i j => G.Adj (embed i) (embed j)
          symm := fun i j h => G.symm h
          loopless := ⟨fun i h => G.loopless.irrefl (embed i) h⟩ }
      -- Define the inverse map {x : Fin n | x ≠ d} → Fin (n-1)
      let proj : {x : Fin n // x ∈ Set.univ \ {d}} → Fin (n - 1) := fun x =>
        if h : x.val.val < d.val then ⟨x.val.val, by omega⟩
        else ⟨x.val.val - 1, by
          have := x.val.isLt
          have hne := (Set.mem_diff_singleton.mp x.2).2
          simp [Fin.ext_iff] at hne
          omega⟩
      have hproj_embed : ∀ k, proj ⟨embed k,
          Set.mem_diff_singleton.mpr ⟨Set.mem_univ _, hembed_ne_d k⟩⟩ = k := by
        intro k; simp only [proj, embed]
        split_ifs with h1 h2
        · ext; simp
        · exact absurd (lt_of_lt_of_le h2 (Nat.le_of_not_lt h1))
            (Nat.not_lt_of_le (Nat.le_succ _))
        · ext; simp
      have hembed_proj : ∀ x : {x : Fin n // x ∈ Set.univ \ {d}},
          embed (proj x) = x.val := by
        intro ⟨x, hx⟩; simp only [embed, proj]
        have hne_d := (Set.mem_diff_singleton.mp hx).2
        split_ifs with h1 h2
        · ext; simp
        · exfalso
          exact absurd (Fin.ext (le_antisymm (Nat.le_of_pred_lt h2)
            (Nat.le_of_not_lt h1))) hne_d
        · ext; simp only []
          have : d.val < x.val :=
            lt_of_le_of_ne (Nat.le_of_not_lt h1) (Fin.val_ne_of_ne hne_d.symm)
          exact Nat.sub_one_add_one (by omega)
      -- n ≥ 3: for n = 2, IsConvexRoundEnum forces completeness,
      -- contradicting hne.
      have h3 : 3 ≤ n := by
        by_contra hlt; push_neg at hlt
        have hn2 : n = 2 := by omega
        subst hn2
        -- Each vertex has ≥ 1 neighbor from CyclicInterval
        have h_nonempty : ∀ i : Fin 2,
            (G.neighborSet i).Nonempty := by
          intro i
          obtain ⟨l, _, hN, hnotmem⟩ :=
            hG.neighborhood_isInterval i
          rw [hN]
          exact ⟨l, Set.mem_diff_singleton.mpr
            ⟨ConvexRound.left_mem_cyclicInterval l _,
             fun h => hnotmem (h ▸
               ConvexRound.left_mem_cyclicInterval l _)⟩⟩
        -- G is complete on Fin 2
        have h_complete : ∀ u v : Fin 2,
            u ≠ v → G.Adj u v := by
          intro u v huv
          obtain ⟨w, hw⟩ := h_nonempty u
          have huw : w ≠ u :=
            fun h => G.loopless.irrefl u (h ▸ hw)
          -- Fin 2: w ≠ u implies w = v
          have : w = v := by
            fin_cases u <;> fin_cases v <;>
              fin_cases w <;>
              first | rfl | (exfalso; omega)
          exact this ▸ hw
        obtain ⟨u, v, huv, hnadj⟩ := hne
        exact hnadj (h_complete u v huv)
      haveI : NeZero (n - 1) := ⟨by omega⟩
      have ⟨G', hG'_cr, hG'_fwd, hG'_rev⟩ :
          ∃ (G' : SimpleGraph (Fin (n - 1))),
            ConvexRound.IsConvexRoundEnum (n - 1) G' ∧
            Cohom (G.induce (Set.univ \ {d}))ᶜ G'ᶜ ∧
            Cohom G'ᶜ (G.induce (Set.univ \ {d}))ᶜ := by
        refine ⟨G', ?_, ?_, ?_⟩
        · -- IsConvexRoundEnum (n-1) G'
          -- Removing a dominated vertex from a convex-round graph preserves
          -- the convex-round enumeration. For each k in Fin (n-1), the
          -- neighborhood of embed k in G is a CyclicInterval; the preimage
          -- of this interval under embed (which skips d) is a CyclicInterval
          -- on Fin (n-1).
          haveI : NeZero (n - 1) := ⟨by omega⟩
          refine ⟨fun k => ?_⟩
          obtain ⟨l, h_hi, hN, hnotmem⟩ := hG.neighborhood_isInterval (embed k)
          -- Characterize G'.neighborSet k via CyclicInterval
          have hG'N : ∀ j : Fin (n - 1),
              j ∈ G'.neighborSet k ↔
              embed j ∈ ConvexRound.CyclicInterval n l h_hi := by
            intro j; constructor
            · intro hadj
              have : embed j ∈ G.neighborSet (embed k) := hadj
              rw [hN] at this
              exact (Set.mem_diff_singleton.mp this).1
            · intro hmem
              change G.Adj (embed k) (embed j)
              rw [← SimpleGraph.mem_neighborSet, hN]
              exact Set.mem_diff_singleton.mpr
                ⟨hmem, fun heq => hnotmem (heq ▸ hmem)⟩
          -- CyclicInterval n l h_hi ≠ {d}: if it were {d}, then embed k's
          -- only neighbor is d; by N(d) ⊆ N(t), embed k ∈ N(t), so
          -- t ∈ N(embed k) = {d}, giving t = d, contradiction.
          have hCI_ne_d : ¬(l = d ∧ h_hi = d) := by
            rintro ⟨hl_eq, hh_eq⟩
            rw [hl_eq, hh_eq] at hN hnotmem
            have hNk : G.neighborSet (embed k) = {d} := by
              rw [hN]; ext x
              simp only [ConvexRound.CyclicInterval, if_pos (le_refl d.val)]
                at hnotmem ⊢
              simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
              exact ⟨fun ⟨⟨h1, h2⟩, hne⟩ => Fin.ext (Nat.le_antisymm h2 h1),
                fun h => ⟨h ▸ ⟨le_refl _, le_refl _⟩,
                  fun heq => hnotmem (heq ▸ h ▸ ⟨le_refl _, le_refl _⟩)⟩⟩
            have had : G.Adj (embed k) d := by
              rw [← SimpleGraph.mem_neighborSet, hNk]; exact rfl
            have hkt : embed k ∈ G.neighborSet t :=
              hnested_dt (G.symm had)
            have ht_in : t ∈ G.neighborSet (embed k) := G.symm hkt
            rw [hNk] at ht_in
            exact hdt (Set.mem_singleton_iff.mp ht_in).symm
          -- Case split: is d an endpoint of the CyclicInterval?
          by_cases hd_l : d = l <;> by_cases hd_h : d = h_hi
          · -- d = l = h_hi: impossible
            exact absurd ⟨hd_l.symm, hd_h.symm⟩ hCI_ne_d
          · -- d = l, d ≠ h_hi
            subst hd_l
            have hh_ne : h_hi ≠ d := Ne.symm hd_h
            have hh_val_ne : h_hi.val ≠ d.val :=
              fun h => hh_ne (Fin.ext h)
            refine ⟨⟨if d.val + 1 < n then d.val else 0, by split_ifs <;> omega⟩,
                    ⟨if h_hi.val < d.val then h_hi.val else h_hi.val - 1,
                     by split_ifs <;> omega⟩, ?_, ?_⟩
            · ext j; simp only [SimpleGraph.mem_neighborSet, Set.mem_diff,
                Set.mem_singleton_iff]
              constructor
              · intro hadj
                have hmem_j := (hG'N j).mp hadj
                exact ⟨(cyclicInterval_skipEmbed_dEqL h3 d h_hi j
                  hh_val_ne).mp hmem_j,
                  fun heq => absurd (heq ▸ hadj) (G'.loopless.irrefl k)⟩
              · intro ⟨hmem, _⟩; apply (hG'N j).mpr
                exact (cyclicInterval_skipEmbed_dEqL h3 d h_hi j
                  hh_val_ne).mpr hmem
            · intro hmem; apply hnotmem
              exact (cyclicInterval_skipEmbed_dEqL h3 d h_hi k
                hh_val_ne).mpr hmem
          · -- d ≠ l, d = h_hi
            subst hd_h
            have hl_ne : l ≠ d := Ne.symm hd_l
            have hl_val_ne : l.val ≠ d.val :=
              fun h => hl_ne (Fin.ext h)
            refine ⟨⟨if l.val < d.val then l.val else l.val - 1,
                     by split_ifs <;> omega⟩,
                    ⟨if 0 < d.val then d.val - 1 else n - 2,
                     by split_ifs <;> omega⟩, ?_, ?_⟩
            · ext j; simp only [SimpleGraph.mem_neighborSet, Set.mem_diff,
                Set.mem_singleton_iff]
              constructor
              · intro hadj
                have hmem_j := (hG'N j).mp hadj
                exact ⟨(cyclicInterval_skipEmbed_dEqH h3 d l j
                  hl_val_ne).mp hmem_j,
                  fun heq => absurd (heq ▸ hadj) (G'.loopless.irrefl k)⟩
              · intro ⟨hmem, _⟩; apply (hG'N j).mpr
                exact (cyclicInterval_skipEmbed_dEqH h3 d l j
                  hl_val_ne).mpr hmem
            · intro hmem; apply hnotmem
              exact (cyclicInterval_skipEmbed_dEqH h3 d l k
                hl_val_ne).mpr hmem
          · -- d ≠ l, d ≠ h_hi: use proj(l), proj(h_hi)
            have hl_ne : l ≠ d := Ne.symm hd_l
            have hh_ne : h_hi ≠ d := Ne.symm hd_h
            have hl_val_ne : l.val ≠ d.val :=
              fun h => hl_ne (Fin.ext h)
            have hh_val_ne : h_hi.val ≠ d.val :=
              fun h => hh_ne (Fin.ext h)
            refine ⟨⟨if l.val < d.val then l.val else l.val - 1,
                     by split_ifs <;> omega⟩,
                    ⟨if h_hi.val < d.val then h_hi.val else h_hi.val - 1,
                     by split_ifs <;> omega⟩, ?_, ?_⟩
            · ext j; simp only [SimpleGraph.mem_neighborSet, Set.mem_diff,
                Set.mem_singleton_iff]
              constructor
              · intro hadj
                have hmem_j := (hG'N j).mp hadj
                exact ⟨(cyclicInterval_skipEmbed_neq h3 d l h_hi j
                  hl_val_ne hh_val_ne).mp hmem_j,
                  fun heq => absurd (heq ▸ hadj) (G'.loopless.irrefl k)⟩
              · intro ⟨hmem, _⟩; apply (hG'N j).mpr
                exact (cyclicInterval_skipEmbed_neq h3 d l h_hi j
                  hl_val_ne hh_val_ne).mpr hmem
            · intro hmem; apply hnotmem
              exact (cyclicInterval_skipEmbed_neq h3 d l h_hi k
                hl_val_ne hh_val_ne).mpr hmem
        · -- Cohom (G.induce ...)ᶜ G'ᶜ
          refine ⟨proj, fun u v huv hnadj => ?_⟩
          simp only [SimpleGraph.compl_adj] at hnadj ⊢
          push_neg at hnadj
          have hadj : G.Adj u.val v.val := hnadj huv
          constructor
          · intro heq
            have := congr_arg embed heq
            rw [hembed_proj, hembed_proj] at this
            exact huv (Subtype.ext this)
          · intro ⟨_, hnadj'⟩
            apply hnadj'
            change G.Adj (embed (proj u)) (embed (proj v))
            rwa [hembed_proj, hembed_proj]
        · -- Cohom G'ᶜ (G.induce ...)ᶜ
          refine ⟨fun k => ⟨embed k,
            Set.mem_diff_singleton.mpr ⟨Set.mem_univ _, hembed_ne_d k⟩⟩,
            fun u v huv hnadj => ?_⟩
          simp only [SimpleGraph.compl_adj] at hnadj ⊢
          push_neg at hnadj
          have hadj : G.Adj (embed u) (embed v) := hnadj huv
          exact ⟨fun h => huv (hembed_inj (Subtype.ext_iff.mp h)),
            fun ⟨_, h⟩ => h hadj⟩
      -- Step 3: Check if folded graph is complete or non-complete
      by_cases hne' : ∃ u v : Fin (n - 1), u ≠ v ∧ ¬G'.Adj u v
      · -- Non-complete case: apply IH on n-1 < n
        have h_lt : n - 1 < n := by omega
        have h2 : 2 ≤ n - 1 := by omega
        obtain ⟨a, b, ha, hb, h2b, hcop, hf, hr⟩ :=
          ih (n - 1) h_lt ⟨by omega⟩ h2 G' hG'_cr hne'
        exact ⟨a, b, ha, hb, h2b, hcop,
          Cohom.trans (Cohom.trans hcohom_fwd hG'_fwd) hf,
          Cohom.trans (Cohom.trans hr hG'_rev) hcohom_rev⟩
      · -- Complete case: G' is complete, so G'ᶜ is edgeless.
        -- Use fractionGraph (n-1) 1 (edgeless on ZMod (n-1)).
        push_neg at hne'
        haveI : NeZero (n - 1) := ⟨by omega⟩
        refine ⟨n - 1, 1, by omega, by omega, by omega,
          Nat.coprime_one_right _, ?_, ?_⟩
        · -- Cohom Gᶜ (fractionGraph (n-1) 1)
          -- Compose: Gᶜ → (G.induce S)ᶜ → G'ᶜ → fractionGraph (n-1) 1
          apply Cohom.trans (Cohom.trans hcohom_fwd hG'_fwd)
          -- Cohom G'ᶜ (fractionGraph (n-1) 1): both are edgeless
          refine ⟨ConvexRound.finZModEquiv (n - 1), fun u v huv _ =>
            ⟨(ConvexRound.finZModEquiv (n - 1)).injective.ne huv, fun hadj => ?_⟩⟩
          exact absurd hadj.2 (not_lt.mpr (Nat.succ_le_iff.mpr
            (distMod_pos_of_ne' (n - 1) ((ConvexRound.finZModEquiv (n - 1)).injective.ne huv))))
        · -- Cohom (fractionGraph (n-1) 1) Gᶜ
          -- Compose: fractionGraph (n-1) 1 → G'ᶜ → (G.induce S)ᶜ → Gᶜ
          apply Cohom.trans _ (Cohom.trans hG'_rev hcohom_rev)
          -- Cohom (fractionGraph (n-1) 1) G'ᶜ: both are edgeless
          refine ⟨ConvexRound.zmodFinEquiv (n - 1), fun u v huv _ =>
            ⟨(ConvexRound.zmodFinEquiv (n - 1)).injective.ne huv, fun hadj => ?_⟩⟩
          exact absurd (hne' _ _ ((ConvexRound.zmodFinEquiv (n - 1)).injective.ne huv))
            hadj.2

/-- BJH02 Theorem 3.1 (BJH02.tex §3): Every non-complete convex-round graph on
    Fin n has its complement cohom-equivalent to some fraction graph. Returns the
    parameters (a, b) with the cohom witnesses.
    The IsConvexRoundEnum structure represents far-side graphs (neighborhoods are intervals
    not containing the vertex). Their complements are close-side graphs, and by BJH02
    Theorem 3.1, these complements are cohomomorphically equivalent to fraction graphs.
    The non-completeness hypothesis (hne) ensures the complement is non-edgeless. -/
theorem convexRound_cohom_equiv_fractionGraph (n : ℕ) [NeZero n]
    (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hG : ConvexRound.IsConvexRoundEnum n G)
    (hne : ∃ u v : Fin n, u ≠ v ∧ ¬G.Adj u v) :
    ∃ (a b : ℕ) (ha_pos : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      Nat.Coprime a b ∧
      Cohom Gᶜ
        (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) ∧
      Cohom
        (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) Gᶜ :=
  convexRound_cohom_equiv_fractionGraph_aux n ‹_› hn G hG hne

/-- Far-side graph of a finite circle subset is convex-round.
    If S is a finite subset of Circle and G has close-side adjacency (hG_le, hG_ge),
    then there exists a cyclic ordering σ of S such that the far-side graph
    (complement of G.induce S pulled back to Fin n through σ) is convex-round.
    The key fact: far-side neighborhoods (vertices at distance ≥ 1/r) form contiguous
    arcs on the circle, which become cyclic intervals under cyclic ordering.
    The proof constructs σ by sorting S according to the cyclic order on Circle
    (using repFrom to measure clockwise arc lengths from a reference point).
    Used for the has-edge case in finite_induce_core. -/
private lemma circle_far_side_convexRound (G : SimpleGraph Circle)
    (r : ℝ) (hr : 2 ≤ r)
    (hG_le : ∀ u v, G.Adj u v → circleDistance u v ≤ 1 / r)
    (hG_ge : ∀ u v, u ≠ v → circleDistance u v < 1 / r → G.Adj u v)
    (S : Set Circle) (hS : S.Finite) [Fintype ↥S]
    (n : ℕ) (hn : n = Fintype.card ↥S) (hn2 : 2 ≤ n) [NeZero n]
    (h_nouniv : ∀ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬G.Adj x y) :
    ∃ (σ : ↥S ≃ Fin n),
      ConvexRound.IsConvexRoundEnum n
        ((G.induce S).comap σ.symm)ᶜ := by
  classical
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 0: Setup — Finset, reference point, basic bounds
  -- ═══════════════════════════════════════════════════════════════════
  set F := hS.toFinset with hF_def
  have hF_mem : ∀ s, s ∈ F ↔ s ∈ S := fun s => Set.Finite.mem_toFinset hS
  have hF_card : F.card = n := by rw [hn, hS.card_toFinset]
  have hn_pos : 0 < n := NeZero.pos n
  -- Pick a reference point u₀ ∈ S
  have hF_ne : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    simp [h] at hF_card; omega
  obtain ⟨u₀, hu₀_F⟩ := hF_ne
  have hu₀_S : u₀ ∈ S := (hF_mem u₀).mp hu₀_F
  -- 1/r ≤ 1/2 since r ≥ 2
  have hr_inv_le : 1 / r ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) hr
  have hr_pos : 0 < r := by linarith
  have hr_inv_pos : 0 < 1 / r := by positivity
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 1: Define rank and sorting — same pattern as line 3150
  -- rank(s) = |{t ∈ F | repFrom u₀ t < repFrom u₀ s}|
  -- ═══════════════════════════════════════════════════════════════════
  let rank : Circle → ℕ := fun s =>
    (F.filter (fun t => repFrom u₀ t < repFrom u₀ s)).card
  have hrank_u₀ : rank u₀ = 0 := by
    change (F.filter (fun t => repFrom u₀ t < repFrom u₀ u₀)).card = 0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _; rw [repFrom_self]; exact not_lt.mpr (repFrom_nonneg u₀ t)
  have hrank_lt : ∀ s ∈ F, rank s < n := by
    intro s hs
    have hsub : F.filter (fun t => repFrom u₀ t < repFrom u₀ s) ⊂ F :=
      ⟨Finset.filter_subset _ F,
       fun h => not_lt.mpr le_rfl ((Finset.mem_filter.mp (h hs)).2)⟩
    rw [← hF_card]; exact Finset.card_lt_card hsub
  have hrank_inj : ∀ s₁ ∈ F, ∀ s₂ ∈ F,
      rank s₁ = rank s₂ → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ heq
    by_contra hne
    have hne_rep : repFrom u₀ s₁ ≠ repFrom u₀ s₂ := by
      intro h
      have h1 : (s₁ - u₀ : Circle) = (s₂ - u₀ : Circle) := by
        have : (AddCircle.equivIco 1 0 (s₁ - u₀)).val =
            (AddCircle.equivIco 1 0 (s₂ - u₀)).val := h
        exact (AddCircle.equivIco 1 0).injective (Subtype.ext this)
      exact hne (sub_left_injective h1)
    rcases lt_or_gt_of_ne hne_rep with h | h
    · have hsub : F.filter (fun t => repFrom u₀ t < repFrom u₀ s₁) ⊂
          F.filter (fun t => repFrom u₀ t < repFrom u₀ s₂) :=
        ⟨fun x hx => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).1,
           lt_trans (Finset.mem_filter.mp hx).2 h⟩,
         fun hsub' => not_lt.mpr le_rfl
          ((Finset.mem_filter.mp (hsub'
            (Finset.mem_filter.mpr ⟨hs₁, h⟩))).2)⟩
      exact absurd heq (Nat.ne_of_lt (Finset.card_lt_card hsub))
    · have hsub : F.filter (fun t => repFrom u₀ t < repFrom u₀ s₂) ⊂
          F.filter (fun t => repFrom u₀ t < repFrom u₀ s₁) :=
        ⟨fun x hx => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).1,
           lt_trans (Finset.mem_filter.mp hx).2 h⟩,
         fun hsub' => not_lt.mpr le_rfl
          ((Finset.mem_filter.mp (hsub'
            (Finset.mem_filter.mpr ⟨hs₂, h⟩))).2)⟩
      exact absurd heq (Nat.ne_of_gt (Finset.card_lt_card hsub))
  have hrank_surj : ∀ i : ℕ, i < n → ∃ s ∈ F, rank s = i := by
    have h_image_card : (F.image rank).card = F.card :=
      Finset.card_image_of_injOn (fun a ha b hb => hrank_inj a ha b hb)
    have h_sub : F.image rank ⊆ Finset.range n := by
      intro x hx; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hrank_lt s hs)
    have h_eq : F.image rank = Finset.range n :=
      Finset.eq_of_subset_of_card_le h_sub
        (by rw [Finset.card_range, ← hF_card, ← h_image_card])
    intro i hi
    exact Finset.mem_image.mp (h_eq ▸ Finset.mem_range.mpr hi)
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 2: Define sorted indexing si : Fin n → Circle
  -- ═══════════════════════════════════════════════════════════════════
  let si : Fin n → Circle := fun i =>
    (hrank_surj i.val i.isLt).choose
  have hsi_mem : ∀ i, si i ∈ F := fun i =>
    (hrank_surj i.val i.isLt).choose_spec.1
  have hsi_rank : ∀ i, rank (si i) = i.val := fun i =>
    (hrank_surj i.val i.isLt).choose_spec.2
  have hsi_mem_S : ∀ i, si i ∈ S := fun i =>
    (hF_mem (si i)).mp (hsi_mem i)
  have hsi_inj : Function.Injective si := by
    intro i j h; exact Fin.ext
      (by rw [← hsi_rank i, ← hsi_rank j]; exact congrArg rank h)
  -- si is surjective onto F (every element of F has some rank)
  have hsi_surj_F : ∀ s ∈ F, ∃ i : Fin n, si i = s := by
    intro s hs
    refine ⟨⟨rank s, hrank_lt s hs⟩, ?_⟩
    change (hrank_surj (rank s) (hrank_lt s hs)).choose = s
    exact hrank_inj _ (hrank_surj (rank s) (hrank_lt s hs)).choose_spec.1 s hs
      (hrank_surj (rank s) (hrank_lt s hs)).choose_spec.2
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 3: Build σ : ↥S ≃ Fin n from si
  -- ═══════════════════════════════════════════════════════════════════
  -- σ maps ⟨s, hs⟩ to the unique i with si i = s
  let σ_fun : ↥S → Fin n := fun ⟨s, hs⟩ =>
    ⟨rank s, hrank_lt s ((hF_mem s).mpr hs)⟩
  have hσ_fun_inj : Function.Injective σ_fun := by
    intro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ h
    simp only [σ_fun, Fin.mk.injEq] at h
    exact Subtype.ext (hrank_inj s₁ ((hF_mem s₁).mpr hs₁)
      s₂ ((hF_mem s₂).mpr hs₂) h)
  have hσ_fun_surj : Function.Surjective σ_fun := by
    intro ⟨i, hi⟩
    obtain ⟨s, hs, hrank_eq⟩ := hrank_surj i hi
    exact ⟨⟨s, (hF_mem s).mp hs⟩, Fin.ext (by simp [σ_fun, hrank_eq])⟩
  let σ : ↥S ≃ Fin n := Equiv.ofBijective σ_fun ⟨hσ_fun_inj, hσ_fun_surj⟩
  -- Key: σ.symm i = ⟨si i, hsi_mem_S i⟩
  have hσ_symm : ∀ i : Fin n, (σ.symm i).val = si i := by
    intro i
    -- σ.symm i is the unique element of S with rank = i.val
    -- si i also has rank = i.val
    -- Both are in S, so they must be equal
    have h_rank_symm : rank (σ.symm i).val = i.val := by
      have := σ.apply_symm_apply i
      change σ_fun (σ.symm i) = i at this
      simp only [σ_fun] at this
      exact Fin.val_eq_of_eq this
    exact hrank_inj (σ.symm i).val
      ((hF_mem _).mpr (σ.symm i).prop)
      (si i) (hsi_mem i)
      (by rw [h_rank_symm, hsi_rank])
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 4: Strict monotonicity of repFrom u₀ ∘ si
  -- ═══════════════════════════════════════════════════════════════════
  have hsi_strict_mono : ∀ i j : Fin n, i.val < j.val →
      repFrom u₀ (si i) < repFrom u₀ (si j) := by
    intro i j hij
    by_contra h; push_neg at h
    rcases eq_or_lt_of_le h with heq | hlt
    · have hsame : si i = si j := by
        apply hrank_inj (si i) (hsi_mem i) (si j) (hsi_mem j)
        change (F.filter _).card = (F.filter _).card
        congr 1; apply Finset.filter_congr
        intro t _; constructor
        · exact fun h2 => heq ▸ h2
        · exact fun h2 => heq.symm ▸ h2
      exact absurd (congrArg Fin.val (hsi_inj hsame)) (Nat.ne_of_lt hij)
    · have : (F.filter (fun t => repFrom u₀ t < repFrom u₀ (si j))).card <
          (F.filter (fun t => repFrom u₀ t < repFrom u₀ (si i))).card := by
        apply Finset.card_lt_card
        exact ⟨fun t ht => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp ht).1,
           lt_trans (Finset.mem_filter.mp ht).2 hlt⟩,
         fun hsub => not_lt.mpr le_rfl
          ((Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr
            ⟨hsi_mem j, hlt⟩))).2)⟩
      have h1 : j.val < i.val := by
        rw [← hsi_rank j, ← hsi_rank i]; exact this
      omega
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 5: Prove IsConvexRoundEnum for the far-side graph
  -- ═══════════════════════════════════════════════════════════════════
  -- Key property: si i ≠ si j for i ≠ j
  have hsi_ne : ∀ i j : Fin n, i ≠ j → si i ≠ si j :=
    fun i j h => hsi_inj.ne h
  -- Far-side characterization: Gfar.Adj i j ↔ i ≠ j ∧ ¬G.Adj (si i) (si j)
  have hfar_adj : ∀ i j : Fin n, ((G.induce S).comap σ.symm)ᶜ.Adj i j ↔
      i ≠ j ∧ ¬G.Adj (si i) (si j) := by
    intro i j
    constructor
    · intro hadj
      have hne : i ≠ j := hadj.ne
      refine ⟨hne, fun hG_adj => hadj.2 ?_⟩
      change (G.induce S).Adj (σ.symm i) (σ.symm j)
      rw [SimpleGraph.induce_adj, hσ_symm, hσ_symm]
      exact hG_adj
    · intro ⟨hne, hnadj⟩
      constructor
      · exact hne
      · intro hadj
        apply hnadj
        have hadj' : (G.induce S).Adj (σ.symm i) (σ.symm j) := hadj
        rw [SimpleGraph.induce_adj, hσ_symm, hσ_symm] at hadj'
        exact hadj'
  -- Far-side implies far distance
  have hfar_dist : ∀ i j : Fin n, i ≠ j → ¬G.Adj (si i) (si j) →
      1 / r ≤ circleDistance (si i) (si j) := by
    intro i j hij hnadj
    by_contra h; push_neg at h
    exact hnadj (hG_ge _ _ (hsi_ne i j hij) h)
  -- Close-side implies close distance
  have hclose_dist : ∀ i j : Fin n, G.Adj (si i) (si j) →
      circleDistance (si i) (si j) ≤ 1 / r := fun _ _ => hG_le _ _
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 6: Prove far-side neighborhoods are CyclicIntervals
  -- Key idea: {y | circleDistance x y ≥ 1/r} is a contiguous arc on
  -- Circle not containing x. Under the sorted bijection si, contiguous
  -- arcs become CyclicIntervals in Fin n.
  -- ═══════════════════════════════════════════════════════════════════
  -- Far-side convexity: if j₁ and j₃ are far-side neighbors of i,
  -- and j₂ is cyclically between them (not going through i), then j₂
  -- is also far-side. This follows because the close-side ball
  -- {y | dist(x,y) < 1/r} is a connected arc containing x, so its
  -- complement is also a connected arc not containing x.
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 6: repFrom (si i) (si j) formula and monotonicity
  -- For i.val ≤ j.val: repFrom (si i) (si j) = repFrom u₀ (si j) - repFrom u₀ (si i)
  -- For j.val < i.val: repFrom (si i) (si j) = 1 - repFrom u₀ (si i) + repFrom u₀ (si j)
  -- In both cases, strictly increasing in j (cyclically from i).
  -- ═══════════════════════════════════════════════════════════════════
  have hrepFrom_formula : ∀ i j : Fin n, i.val < j.val →
      repFrom (si i) (si j) = repFrom u₀ (si j) - repFrom u₀ (si i) := by
    intro i j hij
    exact repFrom_ordered u₀ (si i) (si j)
      (le_of_lt (hsi_strict_mono i j hij))
  have hrepFrom_formula_wrap : ∀ i j : Fin n, j.val < i.val →
      repFrom (si i) (si j) = 1 - repFrom u₀ (si i) + repFrom u₀ (si j) := by
    intro i j hji
    have hlt : repFrom u₀ (si j) < repFrom u₀ (si i) :=
      hsi_strict_mono j i hji
    have hle : repFrom u₀ (si j) ≤ repFrom u₀ (si i) := le_of_lt hlt
    have h_rev := repFrom_ordered u₀ (si j) (si i) hle
    have hne : si i ≠ si j := hsi_ne i j (by intro h; omega)
    have hsum := repFrom_add_repFrom_eq_one (si j) (si i) hne
    linarith
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 7: Far-side convexity — if j₁ and j₂ are far-side neighbors
  -- of i, and k is cyclically between them (not through i), then k is
  -- also far-side. Uses: dist = min(repFrom, 1 - repFrom) and repFrom
  -- monotonicity ensures repFrom (si i) (si k) is between the repFrom
  -- values of j₁ and j₂, keeping it in [1/r, 1-1/r].
  -- ═══════════════════════════════════════════════════════════════════
  -- Key: circleDistance = min(repFrom, 1 - repFrom)
  -- So circleDistance (si i) (si j) ≥ 1/r ↔ repFrom (si i) (si j) ∈ [1/r, 1-1/r]
  -- (for j ≠ i, since 1/r ≤ 1/2)
  have hdist_repFrom : ∀ i j : Fin n, i ≠ j →
      (circleDistance (si i) (si j) ≥ 1 / r ↔
       1 / r ≤ repFrom (si i) (si j) ∧ repFrom (si i) (si j) ≤ 1 - 1 / r) := by
    intro i j hij
    constructor
    · intro hge
      constructor
      · exact le_trans hge (dist_le_repFrom (si i) (si j))
      · have hne : si i ≠ si j := hsi_ne i j hij
        have hsum := repFrom_add_repFrom_eq_one (si i) (si j) hne.symm
        have h_le := dist_le_repFrom (si j) (si i)
        unfold circleDistance at hge
        rw [_root_.dist_comm] at hge
        linarith
    · intro ⟨h1, h2⟩
      rcases le_or_gt (repFrom (si i) (si j)) (1/2) with hle | hgt
      · rw [circleDistance, dist_eq_repFrom_of_le_half _ _ hle]; exact h1
      · have hne : si i ≠ si j := hsi_ne i j hij
        have hsum := repFrom_add_repFrom_eq_one (si i) (si j) hne.symm
        have h_rep_ji : repFrom (si j) (si i) = 1 - repFrom (si i) (si j) := by linarith
        have h_le_half : repFrom (si j) (si i) ≤ 1 / 2 := by linarith
        rw [circleDistance, _root_.dist_comm, dist_eq_repFrom_of_le_half _ _ h_le_half, h_rep_ji]
        linarith
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 8: repFrom (si idx) (si ·) is strictly monotone in cyclicDist
  -- ═══════════════════════════════════════════════════════════════════
  have hrepFrom_cyclicDist_strict_mono : ∀ idx j₁ j₂ : Fin n,
      j₁ ≠ idx → j₂ ≠ idx →
      ConvexRound.cyclicDist n idx j₁ < ConvexRound.cyclicDist n idx j₂ →
      repFrom (si idx) (si j₁) < repFrom (si idx) (si j₂) := by
    intro idx j₁ j₂ hj₁ hj₂ hlt
    -- Split into cases based on position relative to idx
    simp only [ConvexRound.cyclicDist] at hlt
    -- Express repFrom using formulas based on val ordering
    have hne₁ : si idx ≠ si j₁ := hsi_ne idx j₁ hj₁.symm
    have hne₂ : si idx ≠ si j₂ := hsi_ne idx j₂ hj₂.symm
    -- All four cases based on whether idx.val ≤ j₁.val and idx.val ≤ j₂.val
    by_cases h1 : idx.val ≤ j₁.val <;> by_cases h2 : idx.val ≤ j₂.val
    · -- Both ≥ idx: j₁.val < j₂.val, both use forward formula
      have hv : j₁.val < j₂.val := by (split_ifs at hlt; omega)
      rcases eq_or_lt_of_le h1 with heq | hlt₁
      · -- idx.val = j₁.val → j₁ = idx, contradiction
        exact absurd (Fin.ext heq.symm) hj₁
      · rw [hrepFrom_formula idx j₁ hlt₁, hrepFrom_formula idx j₂ (by omega)]
        linarith [hsi_strict_mono j₁ j₂ hv]
    · -- j₁ ≥ idx, j₂ < idx: j₂ wraps, j₁ doesn't
      push_neg at h2
      rcases eq_or_lt_of_le h1 with heq | hlt₁
      · exact absurd (Fin.ext heq.symm) hj₁
      · rw [hrepFrom_formula idx j₁ hlt₁,
            hrepFrom_formula_wrap idx j₂ h2]
        linarith [repFrom_lt_one u₀ (si j₁), repFrom_nonneg u₀ (si j₂)]
    · -- j₁ < idx, j₂ ≥ idx
      push_neg at h1
      split_ifs at hlt <;> omega
    · -- Both < idx: wrapping formula for both
      push_neg at h1 h2
      -- cyclicDist = n - idx.val + j.val for both
      have hv : j₁.val < j₂.val := by split_ifs at hlt <;> omega
      rw [hrepFrom_formula_wrap idx j₁ h1, hrepFrom_formula_wrap idx j₂ h2]
      linarith [hsi_strict_mono j₁ j₂ hv]
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 9: Far-side adjacency ↔ repFrom in [1/r, 1-1/r]
  -- ═══════════════════════════════════════════════════════════════════
  have hfar_iff_repFrom : ∀ idx j : Fin n, idx ≠ j →
      (((G.induce S).comap σ.symm)ᶜ.Adj idx j →
       1 / r ≤ repFrom (si idx) (si j) ∧ repFrom (si idx) (si j) ≤ 1 - 1 / r) := by
    intro idx j hij
    rw [hfar_adj idx j]
    intro ⟨_, hnadj⟩
    exact (hdist_repFrom idx j hij).mp (not_lt.mp (mt (hG_ge _ _ (hsi_ne idx j hij)) hnadj))
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 10: Construct the convex-round enumeration
  -- ═══════════════════════════════════════════════════════════════════
  refine ⟨σ, ⟨fun idx => ?_⟩⟩
  -- For this idx, define the set of far-side neighbors
  set farN := Finset.univ.filter (fun j : Fin n => j ≠ idx ∧
      ¬G.Adj (si idx) (si j)) with hfarN_def
  -- Far-side set is nonempty (from h_nouniv)
  have hfarN_nonempty : farN.Nonempty := by
    obtain ⟨y, hy_S, hne, hnadj⟩ := h_nouniv (si idx) (hsi_mem_S idx)
    obtain ⟨j, hj_eq⟩ := hsi_surj_F y ((hF_mem y).mpr hy_S)
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · intro heq; exact hne (by rw [← hj_eq]; exact congrArg si heq.symm)
    · rw [hj_eq]; exact hnadj
  -- Define cyclicDist from idx for each far-side neighbor
  set distFromIdx := farN.image (fun j => ConvexRound.cyclicDist n idx j)
    with hdistFromIdx_def
  have hdistFromIdx_nonempty : distFromIdx.Nonempty :=
    Finset.Nonempty.image hfarN_nonempty _
  -- Find l (min cyclicDist) and h (max cyclicDist) among far-side neighbors
  set dmin := distFromIdx.min' hdistFromIdx_nonempty with hdmin_def
  set dmax := distFromIdx.max' hdistFromIdx_nonempty with hdmax_def
  -- Get witnesses
  have hdmin_mem := Finset.min'_mem distFromIdx hdistFromIdx_nonempty
  have hdmax_mem := Finset.max'_mem distFromIdx hdistFromIdx_nonempty
  obtain ⟨l, hl_far, hl_dist⟩ := Finset.mem_image.mp hdmin_mem
  have hl_dist_eq : ConvexRound.cyclicDist n idx l = dmin := by rw [hdmin_def]; exact hl_dist
  obtain ⟨h_hi, hh_far, hh_dist⟩ := Finset.mem_image.mp hdmax_mem
  have hh_dist_eq : ConvexRound.cyclicDist n idx h_hi = dmax := by rw [hdmax_def]; exact hh_dist
  have hl_ne : l ≠ idx := (Finset.mem_filter.mp hl_far).2.1
  have hh_ne : h_hi ≠ idx := (Finset.mem_filter.mp hh_far).2.1
  have hl_nadj : ¬G.Adj (si idx) (si l) := (Finset.mem_filter.mp hl_far).2.2
  have hh_nadj : ¬G.Adj (si idx) (si h_hi) := (Finset.mem_filter.mp hh_far).2.2
  -- All far-side neighbors have cyclicDist in [dmin, dmax]
  have hfar_in_range : ∀ j, j ∈ farN →
      dmin ≤ ConvexRound.cyclicDist n idx j ∧
      ConvexRound.cyclicDist n idx j ≤ dmax := by
    intro j hj
    exact ⟨hdmin_def ▸ Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩),
           hdmax_def ▸ Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩
  -- Key: every k with dmin ≤ cyclicDist(idx, k) ≤ dmax and k ≠ idx is far-side
  have hconvex : ∀ k : Fin n, k ≠ idx →
      dmin ≤ ConvexRound.cyclicDist n idx k →
      ConvexRound.cyclicDist n idx k ≤ dmax →
      k ∈ farN := by
    intro k hk_ne hk_min hk_max
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_ne, ?_⟩
    -- Split into: k = l, k = h_hi, or strict interior
    rcases eq_or_lt_of_le hk_min with heq_min | hlt_min
    · -- cyclicDist = dmin → k = l → ¬G.Adj directly
      have hcd_eq : ConvexRound.cyclicDist n idx k = ConvexRound.cyclicDist n idx l := by omega
      have hk_eq_l : k = l := by
        simp only [ConvexRound.cyclicDist] at hcd_eq
        by_cases h1 : idx.val ≤ l.val <;> by_cases h2 : idx.val ≤ k.val <;>
        simp [h1, h2] at hcd_eq <;> apply Fin.ext <;> omega
      rw [hk_eq_l]; exact hl_nadj
    rcases eq_or_lt_of_le hk_max with heq_max | hlt_max
    · -- cyclicDist = dmax → k = h_hi → ¬G.Adj directly
      have hcd_eq : ConvexRound.cyclicDist n idx k =
          ConvexRound.cyclicDist n idx h_hi := by omega
      have hk_eq_h : k = h_hi := by
        simp only [ConvexRound.cyclicDist] at hcd_eq
        by_cases h1 : idx.val ≤ h_hi.val <;> by_cases h2 : idx.val ≤ k.val <;>
        simp [h1, h2] at hcd_eq <;> apply Fin.ext <;> omega
      rw [hk_eq_h]; exact hh_nadj
    · -- Strict interior: dmin < cyclicDist(idx,k) < dmax
      -- Strict monotonicity gives 1/r < repFrom(k) < 1-1/r
      have hl_rep := (hdist_repFrom idx l hl_ne.symm).mp
        (not_lt.mp (mt (hG_ge _ _ (hsi_ne idx l hl_ne.symm)) hl_nadj))
      have hh_rep := (hdist_repFrom idx h_hi hh_ne.symm).mp
        (not_lt.mp (mt (hG_ge _ _ (hsi_ne idx h_hi hh_ne.symm)) hh_nadj))
      have hk_rep_lb : 1 / r < repFrom (si idx) (si k) :=
        lt_of_le_of_lt hl_rep.1 (hrepFrom_cyclicDist_strict_mono idx l k
          hl_ne hk_ne (hl_dist_eq ▸ hlt_min))
      have hk_rep_ub : repFrom (si idx) (si k) < 1 - 1 / r :=
        lt_of_lt_of_le (hrepFrom_cyclicDist_strict_mono idx k h_hi
          hk_ne hh_ne (hh_dist_eq ▸ hlt_max)) hh_rep.2
      -- circleDistance > 1/r (strict), contradicting hG_le
      intro hadj
      have hle := hG_le _ _ hadj
      rcases le_or_gt (repFrom (si idx) (si k)) (1 / 2) with hle_half | hgt_half
      · -- repFrom ≤ 1/2: circleDistance = repFrom > 1/r
        rw [circleDistance, dist_eq_repFrom_of_le_half _ _ hle_half] at hle
        linarith
      · -- repFrom > 1/2: circleDistance = 1-repFrom > 1/r
        have hne := hsi_ne idx k hk_ne.symm
        have hsum := repFrom_add_repFrom_eq_one (si idx) (si k) hne.symm
        have h_le_half : repFrom (si k) (si idx) ≤ 1 / 2 := by linarith
        rw [circleDistance, _root_.dist_comm,
          dist_eq_repFrom_of_le_half _ _ h_le_half] at hle
        linarith
  -- ═══════════════════════════════════════════════════════════════════
  -- STEP 11: Prove CyclicInterval n l h_hi = far-side set ∪ {idx} or similar
  -- We need: neighborSet idx = CyclicInterval n l h_hi \ {idx}
  --          and idx ∉ CyclicInterval n l h_hi
  -- ═══════════════════════════════════════════════════════════════════
  -- l ∈ CyclicInterval(idx, h_hi) and h_hi ∈ CyclicInterval(idx, h_hi)
  -- Key fact: CyclicInterval(l, h_hi) = {k | cyclicDist(l,k) ≤ cyclicDist(l,h_hi)}
  -- We need to translate between cyclicDist from idx and cyclicDist from l
  -- Fact: l ∈ CyclicInterval(idx, h_hi) since cyclicDist(idx, l) ≤ cyclicDist(idx, h_hi)
  have hl_in : l ∈ ConvexRound.CyclicInterval n idx h_hi := by
    rw [ConvexRound.mem_cyclicInterval_iff_cyclicDist]
    rw [hl_dist_eq, hh_dist_eq]
    calc dmin = distFromIdx.min' hdistFromIdx_nonempty := (hdmin_def.symm)
      _ ≤ distFromIdx.max' hdistFromIdx_nonempty :=
          Finset.min'_le _ _ (Finset.max'_mem _ _)
      _ = dmax := hdmax_def
  -- The CyclicInterval from l to h_hi is exactly {k | dmin ≤ cyclicDist(idx,k) ≤ dmax}
  -- because l comes dmin steps after idx, and h_hi comes dmax steps after idx
  -- Use: k ∈ CyclicInterval(l, h_hi) ↔ cyclicDist(l, k) ≤ cyclicDist(l, h_hi)
  -- And: cyclicDist(l, h_hi) = dmax - dmin (by triangle equality)
  have hdmax_ge_dmin : dmin ≤ dmax := by
    calc dmin = distFromIdx.min' hdistFromIdx_nonempty := (hdmin_def.symm)
      _ ≤ distFromIdx.max' hdistFromIdx_nonempty :=
          Finset.min'_le _ _ (Finset.max'_mem _ _)
      _ = dmax := hdmax_def
  have hcyclicDist_l_h : ConvexRound.cyclicDist n l h_hi = dmax - dmin := by
    have htri := ConvexRound.cyclicDist_triangle hl_in
    rw [hl_dist_eq, hh_dist_eq] at htri; omega
  -- idx ∉ CyclicInterval n l h_hi
  have hidx_not_in : idx ∉ ConvexRound.CyclicInterval n l h_hi := by
    rw [ConvexRound.mem_cyclicInterval_iff_cyclicDist, hcyclicDist_l_h]
    -- cyclicDist(l, idx) = n - dmin (since cyclicDist(idx, l) = dmin)
    -- Need: n - dmin > dmax - dmin, i.e., n > dmax
    -- dmax = cyclicDist(idx, h_hi) < n (since h_hi ≠ idx)
    have hdmax_lt_n : dmax < n := by
      rw [← hh_dist_eq]; simp only [ConvexRound.cyclicDist]
      have := h_hi.isLt; have := idx.isLt
      have : h_hi.val ≠ idx.val := fun h => hh_ne (Fin.ext h)
      split_ifs <;> omega
    have hcyclicDist_l_idx : ConvexRound.cyclicDist n l idx = n - dmin := by
      have hrev := ConvexRound.cyclicDist_add_reverse hl_ne
      rw [hl_dist_eq] at hrev; omega
    rw [hcyclicDist_l_idx]; omega
  -- Now prove: the far-side neighbor set = CyclicInterval n l h_hi \ {idx}
  -- Equivalently: ∀ k, k ∈ neighborSet ↔ k ∈ CyclicInterval n l h_hi ∧ k ≠ idx
  refine ⟨l, h_hi, ?_, hidx_not_in⟩
  ext k
  simp only [SimpleGraph.mem_neighborSet, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · -- k is a far-side neighbor → k ∈ CyclicInterval(l, h_hi) \ {idx}
    intro hadj
    have hk_ne : k ≠ idx := hadj.ne.symm
    have hk_far : k ∈ farN := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_ne, ?_⟩
      intro hG_adj
      exact hadj.2 (by
        change (G.induce S).Adj (σ.symm idx) (σ.symm k)
        rw [SimpleGraph.induce_adj, hσ_symm, hσ_symm]
        exact hG_adj)
    have ⟨hmin, hmax⟩ := hfar_in_range k hk_far
    constructor
    · rw [ConvexRound.mem_cyclicInterval_iff_cyclicDist, hcyclicDist_l_h]
      -- cyclicDist(l, k) = cyclicDist(idx, k) - dmin (by triangle from hl_in)
      -- Need: cyclicDist(l, k) ≤ dmax - dmin
      have hk_in_idx_h : k ∈ ConvexRound.CyclicInterval n idx h_hi := by
        rw [ConvexRound.mem_cyclicInterval_iff_cyclicDist, hh_dist_eq]; exact hmax
      have hl_in_idx_k : l ∈ ConvexRound.CyclicInterval n idx k := by
        rw [ConvexRound.mem_cyclicInterval_iff_cyclicDist, hl_dist_eq]; exact hmin
      have htri := ConvexRound.cyclicDist_triangle hl_in_idx_k
      -- cyclicDist(idx, k) = cyclicDist(idx, l) + cyclicDist(l, k)
      -- = dmin + cyclicDist(l, k)
      -- Also cyclicDist(idx, k) ≤ dmax
      rw [hl_dist_eq] at htri
      omega
    · exact hk_ne
  · -- k ∈ CyclicInterval(l, h_hi) \ {idx} → k is a far-side neighbor
    intro ⟨hk_mem, hk_ne⟩
    -- k ∈ CyclicInterval(l, h_hi) → cyclicDist(l, k) ≤ cyclicDist(l, h_hi) = dmax - dmin
    have hk_mem_ci := hk_mem
    rw [ConvexRound.mem_cyclicInterval_iff_cyclicDist, hcyclicDist_l_h] at hk_mem
    -- cyclicDist(idx, k) = cyclicDist(idx, l) + cyclicDist(l, k) = dmin + cyclicDist(l,k)
    -- since l ∈ CyclicInterval(idx, k) (because cyclicDist(idx,l) = dmin ≤ dmin + cyclicDist(l,k))
    have hk_dist_ub : ConvexRound.cyclicDist n idx k ≤ dmax := by
      -- l ∈ CyclicInterval(idx, h_hi) already proved
      -- k ∈ CyclicInterval(l, h_hi) → k ∈ CyclicInterval(idx, h_hi)
      -- → cyclicDist(idx, k) ≤ cyclicDist(idx, h_hi) = dmax
      have : k ∈ ConvexRound.CyclicInterval n idx h_hi :=
        ConvexRound.cyclicInterval_subset hl_in (by
          rw [hl_dist_eq, hcyclicDist_l_h]; omega) hk_mem_ci
      rw [ConvexRound.mem_cyclicInterval_iff_cyclicDist, hh_dist_eq] at this; exact this
    have hk_dist_lb : dmin ≤ ConvexRound.cyclicDist n idx k := by
      -- By contradiction: if cyclicDist(idx, k) < dmin = cyclicDist(idx, l),
      -- then k ∈ CyclicInterval(idx, l), but k ∈ CyclicInterval(l, h_hi) and
      -- idx ∉ CyclicInterval(l, h_hi), giving a contradiction.
      by_contra hlt_min; push_neg at hlt_min
      -- k ∈ CyclicInterval(idx, l) since cyclicDist(idx, k) < cyclicDist(idx, l)
      have hk_in_idx_l : k ∈ ConvexRound.CyclicInterval n idx l :=
        (ConvexRound.mem_cyclicInterval_iff_cyclicDist k idx l).mpr (by rw [hl_dist_eq]; omega)
      -- k ∈ CyclicInterval(l, h_hi) ∩ CyclicInterval(idx, l) means k = l (endpoints)
      -- But actually this creates a contradiction:
      -- cyclicDist(l, k) ≤ dmax - dmin (from hk_mem)
      -- cyclicDist(idx, k) < dmin
      -- cyclicDist(idx, l) = dmin
      -- cyclicDist(l, k): if k ∈ [idx, l] and k ∈ [l, h_hi], then k = l
      -- Triangle: cyclicDist(idx, l) = cyclicDist(idx, k) + cyclicDist(k, l)
      -- So cyclicDist(k, l) = dmin - cyclicDist(idx, k) > 0
      -- Also cyclicDist(l, k) + cyclicDist(k, l) = n (since l ≠ k, because cyclicDist > 0)
      -- So cyclicDist(l, k) = n - cyclicDist(k, l) = n - dmin + cyclicDist(idx, k)
      -- And cyclicDist(l, k) ≤ dmax - dmin
      -- So n - dmin + cyclicDist(idx, k) ≤ dmax - dmin → n ≤ dmax - cyclicDist(idx, k) < n
      -- Contradiction since dmax < n
      have htri := ConvexRound.cyclicDist_triangle hk_in_idx_l
      rw [hl_dist_eq] at htri
      have hk_ne_l : k ≠ l := by
        intro heq; subst heq; rw [hl_dist_eq] at hlt_min
        exact Nat.lt_irrefl _ hlt_min
      have hrev := ConvexRound.cyclicDist_add_reverse hk_ne_l
      have hdmax_lt_n : dmax < n := by
        rw [← hh_dist_eq]; simp only [ConvexRound.cyclicDist]
        have := h_hi.isLt; have := idx.isLt
        have : h_hi.val ≠ idx.val := fun h => hh_ne (Fin.ext h)
        split_ifs <;> omega
      omega
    have hk_far := hconvex k hk_ne hk_dist_lb hk_dist_ub
    have hk_nadj : ¬G.Adj (si idx) (si k) := (Finset.mem_filter.mp hk_far).2.2
    exact (hfar_adj idx k).mpr ⟨Ne.symm hk_ne, hk_nadj⟩

/-- Cohomomorphism bound: if fractionGraph a b → G.induce S (as cohomomorphism)
    where G is sandwiched between open and closed circle graphs with parameter r,
    then a/b ≤ r. This follows from the circular chromatic number theory:
    Cohom (fractionGraph a b) (G.induce S) gives a homomorphism
    K_{a/b} → (G.induce S)ᶜ, implying χ_c(K_{a/b}) = a/b ≤ χ_c((G.induce S)ᶜ) ≤ r.
    Used for the has-edge case in finite_induce_core. -/
private lemma cohom_fractionGraph_circle_bound (G : SimpleGraph Circle)
    (r : ℝ) (hr : 2 ≤ r)
    (_hG_le : ∀ u v, G.Adj u v → circleDistance u v ≤ 1 / r)
    (hG_ge : ∀ u v, u ≠ v → circleDistance u v < 1 / r → G.Adj u v)
    (S : Set Circle) (_hS : S.Finite)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * b ≤ a)
    (_hcop : Nat.Coprime a b)
    (hrev : Cohom (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)
              (G.induce S)) :
    (a : ℝ) / b ≤ r := by
  -- Step 1: inclusion map gives Cohom (G.induce S) (circleGraphOpen r hr)
  have h_incl : Cohom (G.induce S) (circleGraphOpen r hr) :=
    ⟨Subtype.val, fun u v huv hnadj =>
      ⟨Subtype.val_injective.ne huv, fun hadj =>
        hnadj (hG_ge u.val v.val (Subtype.val_injective.ne huv) hadj.2)⟩⟩
  -- Step 2: compose to get fractionGraph a b → circleGraphOpen r
  have h_chain := Cohom.trans hrev h_incl
  -- Step 3: by contradiction, assume r < a/b
  by_contra h_lt
  push_neg at h_lt
  -- Find intermediate rational q_rat with r < q_rat < a/b
  obtain ⟨q_rat, hrq, hqa⟩ := exists_rat_btwn h_lt
  -- Properties of q_rat
  have hq_gt2 : (2 : ℝ) < (q_rat : ℝ) := lt_of_le_of_lt hr hrq
  have hq_pos : 0 < q_rat := by
    have : (0 : ℝ) < (q_rat : ℝ) := lt_trans (by positivity) hq_gt2
    exact_mod_cast this
  have hq_num_pos : 0 < q_rat.num := Rat.num_pos.mpr hq_pos
  -- Extract p', q' from q_rat
  set p' := q_rat.num.toNat with hp'_def
  set q' := q_rat.den with hq'_def
  have hq'_pos : 0 < q' := q_rat.den_pos
  have hp'_pos : 0 < p' := by
    have : (p' : ℤ) = q_rat.num := Int.toNat_of_nonneg (le_of_lt hq_num_pos)
    omega
  haveI : NeZero p' := ⟨Nat.pos_iff_ne_zero.mp hp'_pos⟩
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  -- 2 * q' ≤ p'
  have h2q' : 2 * q' ≤ p' := by
    have hnum_eq : (q_rat.num.toNat : ℤ) = q_rat.num :=
      Int.toNat_of_nonneg (le_of_lt hq_num_pos)
    have hq_gt2_rat : (2 : ℚ) < q_rat := by exact_mod_cast hq_gt2
    have h_int : 2 * (q_rat.den : ℤ) < q_rat.num := by
      have h : 2 * (q_rat.den : ℚ) < q_rat.num := by
        calc 2 * (q_rat.den : ℚ) < q_rat * q_rat.den := by
              exact mul_lt_mul_of_pos_right hq_gt2_rat (by exact_mod_cast q_rat.den_pos)
            _ = q_rat.num := by rw [Rat.mul_den_eq_num]
      exact_mod_cast h
    omega
  -- Identity: (q_rat : ℝ) = (p' : ℝ) / q'
  have hq_eq : (q_rat : ℝ) = (p' : ℝ) / (q' : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hq_num_pos)).symm
  -- 2 ≤ (p' : ℝ) / q'
  have hs_ge2 : 2 ≤ (p' : ℝ) / q' := by linarith
  -- Chain: circleGraphOpen r → circleGraphClosed (p'/q') → circleGraphOpen (p'/q')
  -- → fractionGraph p' q'
  have h1 : Cohom (circleGraphOpen r hr)
      (circleGraphClosed ((p' : ℝ) / q') hs_ge2) :=
    circleGraph_mono_middle r ((p' : ℝ) / q') hr hs_ge2 (by linarith)
  have h2 : Cohom (circleGraphClosed ((p' : ℝ) / q') hs_ge2)
      (circleGraphOpen ((p' : ℝ) / q') hs_ge2) :=
    circleGraphClosed_le_open ((p' : ℝ) / q') hs_ge2
  have h3 : Cohom (circleGraphOpen ((p' : ℝ) / q') hs_ge2)
      (@fractionGraph p' q' ⟨(NeZero.pos p').ne'⟩) :=
    (circleGraphOpen_equiv_fractionGraph p' q' hq'_pos h2q').1
  -- Compose: fractionGraph a b → fractionGraph p' q'
  have h_final : Cohom (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha⟩)
      (@fractionGraph p' q' ⟨(NeZero.pos p').ne'⟩) :=
    Cohom.trans (Cohom.trans (Cohom.trans h_chain h1) h2) h3
  -- Apply fraction graph ordering: (a : ℚ)/b ≤ (p' : ℚ)/q'
  have h_ord : (a : ℚ) / b ≤ (p' : ℚ) / q' :=
    fractionGraph_ordering_reverse a b p' q' hb hq'_pos hab h2q' h_final
  -- But (p' : ℚ)/q' = q_rat and q_rat < a/b, contradiction
  have hq_rat_eq : (p' : ℚ) / (q' : ℚ) = q_rat := by
    rw [show (p' : ℚ) = (q_rat.num : ℚ) from by
      have := Int.toNat_of_nonneg (le_of_lt hq_num_pos)
      exact_mod_cast this]
    exact Rat.num_div_den q_rat
  rw [hq_rat_eq] at h_ord
  -- h_ord : (a : ℚ) / b ≤ q_rat, but hqa : (q_rat : ℝ) < (a : ℝ) / b
  -- Cast h_ord to ℝ and derive contradiction
  have h_ord_real : ((a : ℚ) / (b : ℚ) : ℝ) ≤ (q_rat : ℝ) := by exact_mod_cast h_ord
  have h_eq : ((a : ℚ) / (b : ℚ) : ℝ) = (a : ℝ) / (b : ℝ) := by push_cast; ring
  linarith

/-- Lemma 5.3: Finite non-complete induced
    subgraphs of circle graphs (open or closed) are cohom-equivalent to some
    fraction graph E_{a/b} with a/b ≤ r.
    This is the core lemma underlying both finite_induce_closed and
    finite_induce_open. It works for any graph G on Circle such that:
    1. G.Adj implies close distance (hG_le)
    2. Close distance implies G.Adj (hG_ge), ensuring the complement
       has convex-round structure (far-side neighborhoods are intervals)
    3. The induced subgraph has at least one non-edge (hne)

    The proof combines:
    - Cyclic ordering of S on the circle → convex-round enumeration
    - convexRound_cohom_equiv_fractionGraph (BJH02 Theorem 3.1) → fraction graph
    - Circle geometry → bound a/b ≤ r -/
private theorem finite_induce_core (G : SimpleGraph Circle)
    (r : ℝ) (hr : 2 ≤ r)
    -- G.Adj implies close distance
    (hG_le : ∀ u v, G.Adj u v → circleDistance u v ≤ 1 / r)
    -- Close distance implies G.Adj (ensures complement is convex-round)
    (hG_ge : ∀ u v, u ≠ v → circleDistance u v < 1 / r → G.Adj u v)
    (S : Set Circle) (hS : S.Finite)
    -- The induced subgraph has at least one non-edge (non-complete)
    (hne : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬G.Adj u v) :
    ∃ (a b : ℕ) (ha_pos : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      Nat.Coprime a b ∧ (a : ℝ) / b ≤ r ∧
      Cohom (G.induce S)
        (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) ∧
      Cohom
        (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩)
        (G.induce S) := by
  -- Setup: get Fintype instance and cardinality
  haveI := hS.fintype
  set n := Fintype.card ↥S with hn_def
  -- n ≥ 2 from existence of two distinct elements
  have hn2 : 2 ≤ n := by
    obtain ⟨u, huS, v, hvS, huv, _⟩ := hne
    have : 1 < Fintype.card ↥S :=
      Fintype.one_lt_card_iff.mpr ⟨⟨u, huS⟩, ⟨v, hvS⟩,
        fun h => huv (congrArg Subtype.val h)⟩
    omega
  haveI : NeZero n := ⟨by omega⟩
  -- Split on whether G.induce S has edges
  by_cases hedge_S : ∃ u v : ↥S, (G.induce S).Adj u v
  · -- Case 1: G.induce S has at least one edge → use convex-round machinery
    -- Define S' = non-universal vertices (those with at least one non-neighbor)
    -- Universal vertices (adjacent to all others) can't be part of a convex-round
    -- enumeration since their far-side neighborhood would be empty.
    let S' : Set Circle := {x ∈ S | ∃ y ∈ S, x ≠ y ∧ ¬G.Adj x y}
    have hS'_sub : S' ⊆ S := fun x hx => hx.1
    have hS'_fin : S'.Finite := hS.subset hS'_sub
    haveI : Fintype ↥S' := hS'_fin.fintype
    -- S' ≥ 2 elements: the non-adjacent pair from hne are both in S'
    obtain ⟨u₀, hu₀S, v₀, hv₀S, huv₀, hnadj₀⟩ := hne
    have hu₀S' : u₀ ∈ S' := ⟨hu₀S, v₀, hv₀S, huv₀, hnadj₀⟩
    have hv₀S' : v₀ ∈ S' :=
      ⟨hv₀S, u₀, hu₀S, huv₀.symm, fun h => hnadj₀ (G.symm h)⟩
    set n' := Fintype.card ↥S' with hn'_def
    have hn'2 : 2 ≤ n' :=
      Fintype.one_lt_card_iff.mpr ⟨⟨u₀, hu₀S'⟩, ⟨v₀, hv₀S'⟩,
        fun h => huv₀ (congrArg Subtype.val h)⟩
    haveI : NeZero n' := ⟨by omega⟩
    -- h_nouniv for S': if x ∈ S' has non-neighbor y ∈ S, then y ∈ S' too
    have h_nouniv_S' : ∀ x ∈ S', ∃ y ∈ S', x ≠ y ∧ ¬G.Adj x y := by
      intro x ⟨hxS, y, hyS, hxy, hnadj⟩
      exact ⟨y, ⟨hyS, x, hxS, hxy.symm, fun h => hnadj (G.symm h)⟩,
        hxy, hnadj⟩
    -- Cohom: G.induce S' → G.induce S (inclusion)
    have hcohom_incl : Cohom (G.induce S') (G.induce S) :=
      induced_subset_cohom G S' S hS'_sub
    -- Cohom: G.induce S → G.induce S' (projection: universal vertices → fixed)
    have hcohom_proj : Cohom (G.induce S) (G.induce S') := by
      classical
      refine ⟨fun x => if h : x.val ∈ S' then ⟨x.val, h⟩
        else ⟨u₀, hu₀S'⟩, fun u v huv hnadj => ?_⟩
      -- Non-adjacent vertices must both be in S'
      have huS' : u.val ∈ S' :=
        ⟨u.property, v.val, v.property,
          Subtype.val_injective.ne huv, hnadj⟩
      have hvS' : v.val ∈ S' :=
        ⟨v.property, u.val, u.property,
          (Subtype.val_injective.ne huv).symm,
          fun h => hnadj (G.symm h)⟩
      simp only [dif_pos huS', dif_pos hvS']
      refine ⟨fun h => ?_, hnadj⟩
      apply huv; ext
      exact congrArg (fun (x : ↥S') => (x : Circle)) h
    -- Get convex-round enumeration for S'
    obtain ⟨σ, hcr⟩ := circle_far_side_convexRound G r hr hG_le hG_ge
      S' hS'_fin n' hn'_def hn'2 h_nouniv_S'
    let G_close := (G.induce S').comap σ.symm
    -- Sub-split: does G.induce S' have edges?
    by_cases hedge_S' : ∃ u v : ↥S', (G.induce S').Adj u v
    · -- Case 1a: S' has edges → use convex-round + fraction graph
      have hne_far : ∃ u v : Fin n', u ≠ v ∧ ¬G_closeᶜ.Adj u v := by
        obtain ⟨u, v, hadj⟩ := hedge_S'
        have hne' : σ u ≠ σ v :=
          σ.injective.ne (fun h => (G.induce S').loopless.irrefl u (h ▸ hadj))
        refine ⟨σ u, σ v, hne', fun h => h.2 ?_⟩
        change (G.induce S').Adj (σ.symm (σ u)) (σ.symm (σ v))
        rwa [σ.symm_apply_apply, σ.symm_apply_apply]
      obtain ⟨a, b, ha_pos, hb_pos, hab, hcop, hfwd, hrev⟩ :=
        convexRound_cohom_equiv_fractionGraph n' hn'2 G_closeᶜ hcr hne_far
      rw [compl_compl] at hfwd hrev
      -- Transfer Cohom from G_close to G.induce S' via σ
      have hfwd_S' : Cohom (G.induce S')
          (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) := by
        obtain ⟨f, hf⟩ := hfwd
        refine ⟨f ∘ σ, fun u v huv hnadj => ?_⟩
        apply hf (σ u) (σ v) (σ.injective.ne huv)
        intro hadj; apply hnadj
        change (G.induce S').Adj (σ.symm (σ u)) (σ.symm (σ v)) at hadj
        rwa [σ.symm_apply_apply, σ.symm_apply_apply] at hadj
      have hrev_S' : Cohom
          (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩)
          (G.induce S') := by
        obtain ⟨g, hg⟩ := hrev
        refine ⟨fun x => σ.symm (g x), fun u v huv hnadj => ?_⟩
        obtain ⟨hne_g, hnadj_g⟩ := hg u v huv hnadj
        exact ⟨σ.symm.injective.ne hne_g, fun hadj => hnadj_g hadj⟩
      -- Compose with S↔S' cohoms for final result
      refine ⟨a, b, ha_pos, hb_pos, hab, hcop, ?_,
        Cohom.trans hcohom_proj hfwd_S',
        Cohom.trans hrev_S' hcohom_incl⟩
      exact cohom_fractionGraph_circle_bound G r hr hG_le hG_ge S hS a b
        ha_pos hb_pos hab hcop (Cohom.trans hrev_S' hcohom_incl)
    · -- Case 1b: S' is edgeless → use fractionGraph n' 1
      push_neg at hedge_S'
      have h_frac_edgeless :
          ∀ u v : ZMod n', ¬(fractionGraph n' 1).Adj u v := by
        intro u v hadj
        simp only [fractionGraph] at hadj
        exact absurd hadj.2 (not_lt.mpr (Nat.succ_le_iff.mpr
          (distMod_pos_of_ne' n' hadj.1)))
      have hfwd_S' : Cohom (G.induce S')
          (@fractionGraph n' 1
            ⟨Nat.pos_iff_ne_zero.mp (by omega : 0 < n')⟩) :=
        ⟨ConvexRound.finZModEquiv n' ∘ Fintype.equivFin ↥S',
          fun u v huv hnadj =>
          ⟨((ConvexRound.finZModEquiv n').injective.comp
              (Fintype.equivFin ↥S').injective).ne huv,
            h_frac_edgeless _ _⟩⟩
      have hrev_S' : Cohom
          (@fractionGraph n' 1
            ⟨Nat.pos_iff_ne_zero.mp (by omega : 0 < n')⟩)
          (G.induce S') :=
        ⟨fun x => (Fintype.equivFin ↥S').symm
            (ConvexRound.zmodFinEquiv n' x),
          fun u v huv hnadj =>
          ⟨((Fintype.equivFin ↥S').symm.injective.comp
              (ConvexRound.zmodFinEquiv n').injective).ne huv,
            hedge_S' _ _⟩⟩
      refine ⟨n', 1, by omega, by omega, by omega,
        Nat.coprime_one_right n', ?_,
        Cohom.trans hcohom_proj hfwd_S',
        Cohom.trans hrev_S' hcohom_incl⟩
      exact cohom_fractionGraph_circle_bound G r hr hG_le hG_ge S hS
        n' 1 (by omega) (by omega) (by omega) (Nat.coprime_one_right n')
        (Cohom.trans hrev_S' hcohom_incl)
  · -- Case 2: G.induce S is edgeless → use a = n, b = 1
    push_neg at hedge_S
    -- Any equivalence works for the edgeless case
    let σ := Fintype.equivFin ↥S
    -- fractionGraph n 1 is also edgeless (distMod ≥ 1 for distinct elements)
    have h_frac_edgeless : ∀ u v : ZMod n, ¬(fractionGraph n 1).Adj u v := by
      intro u v hadj
      simp only [fractionGraph] at hadj
      exact absurd hadj.2 (not_lt.mpr (Nat.succ_le_iff.mpr
        (distMod_pos_of_ne' n hadj.1)))
    -- Construct Cohom's (both graphs are edgeless, use bijections)
    have hfwd_edgeless : Cohom (G.induce S)
        (@fractionGraph n 1 ⟨Nat.pos_iff_ne_zero.mp (by omega : 0 < n)⟩) :=
      ⟨ConvexRound.finZModEquiv n ∘ σ, fun u v huv hnadj =>
        ⟨((ConvexRound.finZModEquiv n).injective.comp σ.injective).ne huv,
         h_frac_edgeless _ _⟩⟩
    have hrev_edgeless : Cohom
        (@fractionGraph n 1 ⟨Nat.pos_iff_ne_zero.mp (by omega : 0 < n)⟩)
        (G.induce S) :=
      ⟨fun x => σ.symm (ConvexRound.zmodFinEquiv n x), fun u v huv hnadj =>
        ⟨(σ.symm.injective.comp (ConvexRound.zmodFinEquiv n).injective).ne huv,
         hedge_S _ _⟩⟩
    refine ⟨n, 1, by omega, by omega, by omega, Nat.coprime_one_right n, ?_,
      hfwd_edgeless, hrev_edgeless⟩
    -- Bound: (n : ℝ) / 1 ≤ r
    exact cohom_fractionGraph_circle_bound G r hr hG_le hG_ge S hS n 1
      (by omega) (by omega) (by omega) (Nat.coprime_one_right n) hrev_edgeless

/-- Lemma 5.3 for closed circle graphs:
    Every finite non-complete induced subgraph of a closed circle graph is
    cohom-equivalent to a fraction graph E_{a/b} with a/b ≤ r.
    The non-completeness hypothesis (hne) says there exist two points in S
    at distance ≥ 1/r (so they are not adjacent). -/
theorem finite_induce_closed (r : ℝ) (hr : 2 ≤ r)
    (S : Set Circle) (hS : S.Finite)
    (hne : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬(circleGraphClosed r hr).Adj u v) :
    ∃ (a b : ℕ) (ha_pos : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      Nat.Coprime a b ∧ (a : ℝ) / b ≤ r ∧
      Cohom ((circleGraphClosed r hr).induce S)
        (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) ∧
      Cohom (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩)
        ((circleGraphClosed r hr).induce S) := by
  apply finite_induce_core (circleGraphClosed r hr) r hr
  · intro u v ⟨_, hdist⟩; exact hdist
  · intro u v huv hdist; exact ⟨huv, le_of_lt hdist⟩
  · exact hS
  · exact hne

/-- Lemma 5.3 for the open circle graph. -/
theorem finite_induce_open (r : ℝ) (hr : 2 ≤ r)
    (S : Set Circle) (hS : S.Finite)
    (hne : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬(circleGraphOpen r hr).Adj u v) :
    ∃ (a b : ℕ) (ha_pos : 0 < a), 0 < b ∧ 2 * b ≤ a ∧
      Nat.Coprime a b ∧ (a : ℝ) / b ≤ r ∧
      Cohom ((circleGraphOpen r hr).induce S)
        (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) ∧
      Cohom (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩)
        ((circleGraphOpen r hr).induce S) := by
  apply finite_induce_core (circleGraphOpen r hr) r hr
  · intro u v ⟨_, hdist⟩; exact le_of_lt hdist
  · intro u v huv hdist; exact ⟨huv, hdist⟩
  · exact hS
  · exact hne

/-- CFA(4): Best rational approximation from below with bounded numerator.
    If p/q ≤ r with error bound r - p/q < 1/q², and a/b ≤ r with a ≤ p,
    then a/b ≤ p/q.
    Proof: Assume a/b > p/q for contradiction. From a ≤ p we get b < q.
    Then a/b - p/q ≥ 1/(bq) (distinct fractions), so r - p/q ≥ 1/(bq).
    But 1/(bq) < 1/q² requires b > q, contradicting b < q. -/
theorem convergent_best_approx_from_below (r : ℝ) (_hirr : Irrational r)
    (p q a b : ℕ) (_hp : 0 < p) (hq : 0 < q) (_ha : 0 < a) (hb : 0 < b)
    (_h2q : 2 * q ≤ p) (_hcoprime_pq : Nat.Coprime p q) (_hcoprime_ab : Nat.Coprime a b)
    (_hpq_le : (p : ℝ) / q ≤ r)
    (hab_le : (a : ℝ) / b ≤ r)
    (ha_le : a ≤ p)
    (herr : r - (p : ℝ) / q < 1 / (q : ℝ) ^ 2) :
    (a : ℚ) / b ≤ (p : ℚ) / q := by
  by_contra h_not
  push_neg at h_not
  -- h_not : (p : ℚ) / q < (a : ℚ) / b
  -- Step 1: Cross multiply to get p*b < a*q as naturals
  have hq_pos_q : (0 : ℚ) < q := Nat.cast_pos.mpr hq
  have hb_pos_q : (0 : ℚ) < b := Nat.cast_pos.mpr hb
  have h_cross_q : (p : ℚ) * b < (a : ℚ) * q :=
    (div_lt_div_iff₀ hq_pos_q hb_pos_q).mp h_not
  have h_cross : p * b < a * q := by exact_mod_cast h_cross_q
  -- Step 2: From a ≤ p, derive b < q
  have hb_lt_q : b < q := by
    have h1 : a * q ≤ p * q := Nat.mul_le_mul_right q ha_le
    have : p * b < p * q := lt_of_lt_of_le h_cross h1
    exact Nat.lt_of_mul_lt_mul_left this
  -- Step 3: (a/b - p/q) ≥ 1/(b*q), hence r - p/q ≥ 1/(b*q)
  have hb_pos_r : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hq_pos_r : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hbq_pos : (0 : ℝ) < (b : ℝ) * q := mul_pos hb_pos_r hq_pos_r
  have h_num_ge : (1 : ℝ) ≤ (a : ℝ) * q - (b : ℝ) * p := by
    have h1 : b * p + 1 ≤ a * q := by nlinarith [h_cross, mul_comm p b]
    have h2 : ((b * p + 1 : ℕ) : ℝ) ≤ ((a * q : ℕ) : ℝ) := Nat.cast_le.mpr h1
    push_cast at h2; linarith
  have h_diff_ge : 1 / ((b : ℝ) * q) ≤ (a : ℝ) / b - (p : ℝ) / q := by
    rw [div_sub_div _ _ (ne_of_gt hb_pos_r) (ne_of_gt hq_pos_r)]
    exact div_le_div_of_nonneg_right h_num_ge (le_of_lt hbq_pos)
  have h_r_lb : 1 / ((b : ℝ) * q) ≤ r - (p : ℝ) / q := by linarith
  -- Step 4: Combined with herr: 1/(bq) < 1/q², so q² < bq, so q < b
  have h_lt : 1 / ((b : ℝ) * q) < 1 / (q : ℝ) ^ 2 := by linarith
  have hq_lt_b : q < b := by
    have hqsq_pos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    have h' : (q : ℝ) ^ 2 < (b : ℝ) * q := by
      rwa [div_lt_div_iff₀ hbq_pos hqsq_pos, one_mul, one_mul] at h_lt
    rw [sq] at h'
    have : (q : ℝ) < (b : ℝ) := by nlinarith
    exact_mod_cast this
  -- Contradiction: b < q and q < b
  omega

/-- Self-cohomomorphisms of fraction graphs are bijective (for all b ≥ 1).
    For b ≥ 2, this follows from fractionGraph_selfCohom_isIso.
    For b = 1, E_{a/1} is edgeless so cohomomorphisms are injective by definition. -/
private lemma fractionGraph_selfCohom_bijective (a b : ℕ) [NeZero a]
    (hb_pos : 0 < b) (h2b : 2 * b ≤ a) (hcop : Nat.Coprime a b)
    (f : ZMod a → ZMod a) (hf : IsCohom (fractionGraph a b) (fractionGraph a b) f) :
    Function.Bijective f := by
  rcases le_or_gt 2 b with hb_ge_2 | hb_lt_2
  · exact fractionGraph_selfCohom_isIso a b hb_ge_2 h2b hcop f hf
  · -- b = 1: E_{a/1} is edgeless, cohom = injective
    have hb1 : b = 1 := by omega
    have hinj : Function.Injective f := by
      intro x y hfxy
      by_contra hxy
      have hnadj : ¬(fractionGraph a b).Adj x y := by
        intro ⟨_, hdist⟩
        subst hb1; simp only [distMod] at hdist
        have h1 : 0 < (x - y : ZMod a).val := by
          rw [Nat.pos_iff_ne_zero]; intro hval
          exact hxy (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp hval))
        have h2 : (x - y : ZMod a).val < a := ZMod.val_lt _
        omega
      exact (hf x y hxy hnadj).1 hfxy
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-- A bijective cohomomorphism from E_{p/q} preserves adjacency in the forward direction,
    provided there is a reverse cohom making the composition a bijective self-cohom.
    Key step: the composition is an iso (rotation/reflection for q ≥ 2), so if the
    forward map dropped an edge, the composition would too, contradicting iso. -/
private lemma cohom_bijective_adj_preserved (p q : ℕ) [NeZero p]
    (hq_pos : 0 < q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    {W : Type*} (H : SimpleGraph W)
    (g : ZMod p → W) (hg : IsCohom (fractionGraph p q) H g) (hg_inj : Function.Injective g)
    (h_rev : W → ZMod p) (hh : IsCohom H (fractionGraph p q) h_rev)
    (u v : ZMod p) (hadj : (fractionGraph p q).Adj u v) :
    H.Adj (g u) (g v) := by
  by_contra hnadj
  have hne_g : g u ≠ g v := fun h => (SimpleGraph.ne_of_adj _ hadj) (hg_inj h)
  -- h_rev maps non-adjacent (g u, g v) to non-adjacent in E_{p/q}
  have hcomp_nadj : ¬(fractionGraph p q).Adj (h_rev (g u)) (h_rev (g v)) :=
    (hh (g u) (g v) hne_g hnadj).2
  -- But h_rev ∘ g is a bijective self-cohom of E_{p/q}, so it preserves adjacency
  have hcomp_cohom : IsCohom (fractionGraph p q) (fractionGraph p q) (h_rev ∘ g) :=
    hg.comp hh
  have hcomp_bij := fractionGraph_selfCohom_bijective p q hq_pos h2q hcoprime
    (h_rev ∘ g) hcomp_cohom
  -- Bijective self-cohom of a finite graph maps edges to edges (by counting:
  -- it maps non-edges to non-edges bijectively, so edges map to edges)
  -- Use the contrapositive: if it mapped an edge to a non-edge, there would be
  -- more non-edges in the image than in the domain, contradicting bijectivity.
  -- For finite types, bijective cohom preserves edge count.
  have hcomp_adj : (fractionGraph p q).Adj ((h_rev ∘ g) u) ((h_rev ∘ g) v) := by
    -- The bijection σ = h_rev ∘ g maps non-adj pairs injectively to non-adj pairs.
    -- Since σ is bijective on vertices, it's bijective on unordered pairs.
    -- If σ mapped an adj pair to a non-adj pair, there would be strictly more
    -- non-adj pairs in the image (all original non-adj pairs plus this one),
    -- contradicting bijectivity on pairs.
    -- We formalize via Finset counting on the complement graph's edge set.
    by_contra h
    -- σ maps edge (u,v) to non-edge, and maps all non-edges to non-edges.
    -- So σ maps all n(n-1)/2 pairs to pairs, with at least (non-edges + 1) mapped
    -- to non-edges. But σ is a bijection on vertices, hence on pairs.
    -- The number of non-edge pairs is preserved, contradiction.
    -- Alternative: use fractionGraph_selfCohom_form for q ≥ 2, trivial for q = 1.
    rcases le_or_gt 2 q with hq2 | hq1
    · -- q ≥ 2: σ is a rotation or reflection, which preserves distMod hence adjacency
      obtain ⟨c, hrot | hrefl⟩ := fractionGraph_selfCohom_form p q hq2 h2q hcoprime
        (h_rev ∘ g) hcomp_cohom
      · -- Rotation: σ(x) = c + x
        simp only [Function.comp_apply] at hrot h
        rw [hrot u, hrot v] at h
        have : (fractionGraph p q).Adj (c + u) (c + v) := by
          constructor
          · intro heq; exact (SimpleGraph.ne_of_adj _ hadj) (add_left_cancel heq)
          · obtain ⟨_, hdist⟩ := hadj
            show distMod p (c + u) (c + v) < q
            have : c + u - (c + v) = u - v := by ring
            simp only [distMod, this]; exact hdist
        exact h this
      · -- Reflection: σ(x) = c - x
        simp only [Function.comp_apply] at hrefl h
        rw [hrefl u, hrefl v] at h
        have : (fractionGraph p q).Adj (c - u) (c - v) := by
          constructor
          · intro heq
            have := sub_right_injective heq
            exact (SimpleGraph.ne_of_adj _ hadj) this
          · obtain ⟨_, hdist⟩ := hadj
            show distMod p (c - u) (c - v) < q
            have : c - u - (c - v) = v - u := by ring
            simp only [distMod, this]
            rwa [distMod_comm] at hdist
        exact h this
    · -- q = 1: E_{p/1} is edgeless, no edges to preserve (vacuous)
      have : ¬(fractionGraph p q).Adj u v := by
        intro ⟨_, hdist⟩
        have hq1' : q = 1 := by omega
        subst hq1'; simp only [distMod] at hdist
        have h1 : 0 < (u - v : ZMod p).val := by
          rw [Nat.pos_iff_ne_zero]; intro hval
          exact (SimpleGraph.ne_of_adj _ hadj) (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp hval))
        have h2 : (u - v : ZMod p).val < p := ZMod.val_lt _
        omega
      exact this hadj
  exact hcomp_nadj hcomp_adj

/-- (Lemma finite_induce + CFA):
    If S induces E_{p/q} in a circle graph with irrational parameter r,
    and f is a self-cohomomorphism of the circle graph,
    then f(S) also induces E_{p/q}.

    The proof uses finite_induce (for the specific graph G) and
    convergent_best_approx_from_below. -/
lemma cohom_image_preserves_fractionGraph_iso
    (G : SimpleGraph Circle)
    (r : ℝ) (_hr : 2 ≤ r) (hirr : Irrational r)
    -- G satisfies the finite_induce property for parameter r (on non-complete subgraphs)
    (hG_fi : ∀ (T : Set Circle), T.Finite →
      (∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ ¬G.Adj u v) →
      ∃ (a b : ℕ) (ha_pos : 0 < a), 0 < b ∧ 2 * b ≤ a ∧ Nat.Coprime a b ∧
        (a : ℝ) / b ≤ r ∧
        Cohom (G.induce T) (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) ∧
        Cohom (@fractionGraph a b ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩) (G.induce T))
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    (hcoprime : Nat.Coprime p q)
    (herr : r - (p : ℝ) / q < 1 / (q : ℝ) ^ 2)
    (S : Set Circle) (hS_finite : S.Finite)
    -- S induces E_{p/q} in the circle graph G (open or closed)
    (hiso : Nonempty (G.induce S ≃g fractionGraph p q))
    -- f is a self-cohomomorphism of G
    (f : Circle → Circle)
    (hf : IsCohom G G f) :
    -- f(S) also induces E_{p/q}
    Nonempty (G.induce (S.image f) ≃g fractionGraph p q) := by
  -- Step 1: S.image f is finite and has a non-edge
  have hfS_finite : (S.image f).Finite := hS_finite.image f
  -- Construct non-edge in S.image f: fractionGraph p q has non-edge (0, q),
  -- the iso transfers it to G.induce S, and f (as a cohom) preserves non-edges.
  have hfS_hne : ∃ u ∈ S.image f, ∃ v ∈ S.image f, u ≠ v ∧ ¬G.Adj u v := by
    obtain ⟨iso⟩ := hiso
    -- fractionGraph p q has a non-edge: (0, q) with distMod ≥ q
    have hq_lt_p : q < p := by omega
    have hne_0q : (0 : ZMod p) ≠ (q : ZMod p) := by
      intro h
      have h1 : (0 : ZMod p).val = (q : ZMod p).val := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_natCast_of_lt hq_lt_p] at h1; omega
    have hne_frac : ¬(fractionGraph p q).Adj (0 : ZMod p) (q : ZMod p) := by
      intro ⟨_, hdist⟩
      have hdm : distMod p 0 (q : ZMod p) ≥ q :=
        distMod_ge_q_of_val_diff_in_range p q h2q 0 (q : ZMod p)
          (by simp [ZMod.val_zero])
          (by rw [ZMod.val_natCast_of_lt hq_lt_p, ZMod.val_zero]; omega)
          (by rw [ZMod.val_natCast_of_lt hq_lt_p, ZMod.val_zero]; omega)
      omega
    -- Transfer to G.induce S
    let u0 : ↥S := iso.symm 0
    let uq : ↥S := iso.symm q
    have hne_S : u0 ≠ uq := fun h => hne_0q (iso.symm.injective h)
    have hnadj_S : ¬G.Adj u0.val uq.val := by
      intro hadj
      exact hne_frac (iso.symm.map_adj_iff.mp hadj)
    -- Apply f (cohom preserves non-edges)
    have hf_ne : f u0.val ≠ f uq.val ∧ ¬G.Adj (f u0.val) (f uq.val) := by
      exact hf u0.val uq.val (Subtype.val_injective.ne hne_S) hnadj_S
    exact ⟨f u0.val, Set.mem_image_of_mem f u0.prop,
           f uq.val, Set.mem_image_of_mem f uq.prop,
           hf_ne.1, hf_ne.2⟩
  -- Step 2: Apply finite_induce to get E_{a/b} equivalent to G.induce(S.image f)
  rcases hG_fi (S.image f) hfS_finite hfS_hne with
    ⟨a, b, ha_pos, hb_pos, h2b, hcop_ab, hab_le_r, hcohom_fwd, hcohom_rev⟩
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
  -- Step 3: Build cohom E_{p/q} → G.induce(S.image f)
  obtain ⟨iso⟩ := hiso
  have iso_cohom : IsCohom (fractionGraph p q) (G.induce S)
      (fun v => iso.symm v) := by
    intro x y hxy hnadj
    exact ⟨fun h => hxy (iso.symm.injective h), fun h => hnadj (iso.symm.map_adj_iff.mp h)⟩
  have incl_cohom : IsCohom (G.induce S) G (fun s => s.val) := by
    intro x y hxy hnadj
    exact ⟨fun h => hxy (Subtype.ext h), hnadj⟩
  have comp_cohom := (iso_cohom.comp incl_cohom).comp hf
  have himg : ∀ v : ZMod p, (f ∘ (fun s : ↥S => s.val) ∘ fun v => iso.symm v) v ∈ S.image f :=
    fun v => Set.mem_image_of_mem f (iso.symm v).prop
  have g_cohom := isCohom_corestrict _ comp_cohom (S.image f) himg
  -- g_cohom : IsCohom E_{p/q} (G.induce(S.image f)) g
  -- Step 4: Cohom E_{p/q} E_{a/b} → p/q ≤ a/b (rational ordering)
  have hcohom_pq_ab : Cohom (fractionGraph p q) (fractionGraph a b) :=
    Cohom.trans ⟨_, g_cohom⟩ hcohom_fwd
  have hpq_le_ab := fractionGraph_ordering_reverse p q a b hq hb_pos h2q h2b hcohom_pq_ab
  -- Step 5: Core property → a ≤ |S.image f| ≤ |S| = p
  obtain ⟨h_fwd_fn, hh_fwd⟩ := hcohom_fwd
  obtain ⟨h_rev_fn, hh_rev⟩ := hcohom_rev
  have hself_cohom := hh_rev.comp hh_fwd
  have hself_bij := fractionGraph_selfCohom_bijective a b hb_pos h2b hcop_ab
    (h_fwd_fn ∘ h_rev_fn) hself_cohom
  -- h_rev_fn is injective (composition with h_fwd_fn is bijective)
  have h_rev_inj : Function.Injective h_rev_fn := hself_bij.1.of_comp
  -- a ≤ |S.image f|: injective map from ZMod a (a elements) to S.image f
  haveI : Fintype ↥(S.image f) := hfS_finite.fintype
  have h_a_le_fS : a ≤ Fintype.card ↥(S.image f) := by
    have : a = Fintype.card (ZMod a) := (ZMod.card a).symm
    rw [this]
    exact Fintype.card_le_of_injective h_rev_fn h_rev_inj
  -- |S.image f| ≤ |S| = p
  haveI : Fintype ↥S := hS_finite.fintype
  have h_card_S : Fintype.card ↥S = p := by
    have h := iso.card_eq
    rw [ZMod.card] at h; exact h
  have h_fS_le_S : Fintype.card ↥(S.image f) ≤ Fintype.card ↥S := by
    apply Fintype.card_le_of_surjective (fun s : ↥S => ⟨f s.val, Set.mem_image_of_mem f s.prop⟩)
    intro ⟨y, hy⟩
    obtain ⟨x, hx_mem, hfx⟩ := hy
    exact ⟨⟨x, hx_mem⟩, Subtype.ext hfx⟩
  have ha_le_p : a ≤ p := by omega
  -- Step 6: Apply CFA best approximation → a/b ≤ p/q
  -- First derive p/q ≤ r from p/q ≤ a/b ≤ r
  have hpq_le_r : (p : ℝ) / q ≤ r := by
    have hab_r : (a : ℝ) / b ≤ r := hab_le_r
    have hpq_ab : (p : ℚ) / q ≤ (a : ℚ) / b := hpq_le_ab
    have hpq_ab_real : (p : ℝ) / q ≤ (a : ℝ) / b := by
      have h1 : ((↑p / ↑q : ℚ) : ℝ) ≤ ((↑a / ↑b : ℚ) : ℝ) := Rat.cast_le.mpr hpq_ab
      simp only [Rat.cast_div, Rat.cast_natCast] at h1; exact h1
    linarith
  have hab_le_pq := convergent_best_approx_from_below r hirr p q a b
    (NeZero.pos p) hq ha_pos hb_pos h2q hcoprime hcop_ab hpq_le_r hab_le_r ha_le_p herr
  -- Step 7: p/q ≤ a/b and a/b ≤ p/q → a/b = p/q → a = p and b = q
  have hab_eq_pq : (a : ℚ) / b = (p : ℚ) / q := le_antisymm hab_le_pq hpq_le_ab
  have ha_eq_p : a = p := by
    have hq_pos' : (0 : ℚ) < q := Nat.cast_pos.mpr hq
    have hb_pos' : (0 : ℚ) < b := Nat.cast_pos.mpr hb_pos
    have h := hab_eq_pq
    rw [div_eq_div_iff hb_pos'.ne' hq_pos'.ne'] at h
    -- a * q = p * b with Coprime a b and Coprime p q
    have h_nat : a * q = p * b := by exact_mod_cast h
    -- From Coprime a b and a ∣ p*b: a ∣ p
    have ha_dvd_p : a ∣ p :=
      hcop_ab.dvd_of_dvd_mul_right ⟨q, h_nat.symm⟩
    -- From Coprime p q and p ∣ a*q: p ∣ a
    have hp_dvd_a : p ∣ a :=
      hcoprime.dvd_of_dvd_mul_right ⟨b, h_nat⟩
    exact dvd_antisymm ha_dvd_p hp_dvd_a
  have hb_eq_q : b = q := by
    have hq_pos' : (0 : ℚ) < q := Nat.cast_pos.mpr hq
    have hb_pos' : (0 : ℚ) < b := Nat.cast_pos.mpr hb_pos
    have h := hab_eq_pq
    rw [div_eq_div_iff hb_pos'.ne' hq_pos'.ne'] at h
    have h_nat : a * q = p * b := by exact_mod_cast h
    rw [ha_eq_p] at h_nat
    exact mul_left_cancel₀ (Nat.pos_iff_ne_zero.mp (NeZero.pos p)) h_nat.symm
  -- Step 8: Substitute a = p, b = q. Now we have bidirectional cohoms with E_{a/b}.
  -- (subst eliminates p→a and q→b since NeZero a prevents eliminating a)
  subst ha_eq_p; subst hb_eq_q
  -- After subst: p is replaced by a, q by b throughout the context and goal
  have h_card_fS_eq : Fintype.card ↥(S.image f) = a := by omega
  have h_rev_bij : Function.Bijective h_rev_fn := by
    have hcard : Fintype.card (ZMod a) = Fintype.card ↥(S.image f) := by
      rw [ZMod.card, h_card_fS_eq]
    exact (Fintype.bijective_iff_injective_and_card h_rev_fn).mpr ⟨h_rev_inj, hcard⟩
  -- Step 9: Construct the isomorphism
  -- h_rev_fn preserves non-edges (cohom) and edges (by cohom_bijective_adj_preserved)
  have h_rev_adj : ∀ u v, (fractionGraph a b).Adj u v →
      (G.induce (S.image f)).Adj (h_rev_fn u) (h_rev_fn v) :=
    cohom_bijective_adj_preserved a b hq h2q hcoprime
      (G.induce (S.image f)) h_rev_fn hh_rev h_rev_inj h_fwd_fn hh_fwd
  -- Build the iso: h_rev_fn⁻¹ : G.induce(S.image f) ≃g E_{p/q}
  let g_equiv := Equiv.ofBijective h_rev_fn h_rev_bij
  exact ⟨{
    toEquiv := g_equiv.symm
    map_rel_iff' := by
      intro x y
      constructor
      · -- (frac).Adj (g_equiv.symm x) (g_equiv.symm y) → (G.induce ...).Adj x y
        intro hadj
        have := h_rev_adj (g_equiv.symm x) (g_equiv.symm y) hadj
        convert this using 1 <;> exact (g_equiv.apply_symm_apply _).symm
      · -- (G.induce ...).Adj x y → (frac).Adj (g_equiv.symm x) (g_equiv.symm y)
        intro hadj
        by_contra hnadj
        have hne : g_equiv.symm x ≠ g_equiv.symm y :=
          fun h => (SimpleGraph.ne_of_adj _ hadj) (g_equiv.symm.injective h)
        have ⟨_, hnadj'⟩ := hh_rev (g_equiv.symm x) (g_equiv.symm y) hne hnadj
        apply hnadj'
        convert hadj using 1 <;> exact g_equiv.apply_symm_apply _
  }⟩

/-- If S induces E_{p/q}, then S has exactly p elements.
    This follows from SimpleGraph.Iso.card_eq: an isomorphism preserves vertex count.
    Since fractionGraph p q has vertex set ZMod p with p elements, S must have p elements. -/
lemma fractionGraph_iso_card
    (r : ℝ) (hr : 2 ≤ r)
    (p q : ℕ) [NeZero p]
    (S : Set Circle) (hS_finite : S.Finite)
    (hiso : Nonempty ((circleGraphOpen r hr).induce S ≃g fractionGraph p q)) :
    hS_finite.toFinset.card = p := by
  obtain ⟨iso⟩ := hiso
  -- Use Fintype instance from the finite set
  haveI : Fintype ↥S := hS_finite.fintype
  -- hS_finite.toFinset.card = Fintype.card ↥S
  have h1 : hS_finite.toFinset.card = Fintype.card ↥S := hS_finite.card_toFinset
  -- Fintype.card ↥S = Fintype.card (ZMod p) from the isomorphism
  have h2 : Fintype.card ↥S = Fintype.card (ZMod p) := iso.card_eq
  -- Fintype.card (ZMod p) = p
  have h3 : Fintype.card (ZMod p) = p := ZMod.card p
  omega

/-- S_x = equidistantPointsShift p x can be expressed as insert x (S_y \ {y})
    where S_y = insert y (equidistantPointsShift p x \ {x}).
    This is a set identity: removing y from S_y gives skeleton, inserting x back
    gives S_x. Requires y ∉ equidistantPointsShift p x for the identity to hold. -/
lemma equidistantPointsShift_insert_diff_eq
    (p : ℕ) [NeZero p] (x y : Circle) (hxy : x ≠ y)
    (hy_not_mem : y ∉ equidistantPointsShift p x) :
    equidistantPointsShift p x = insert x (insert y (equidistantPointsShift p x \ {x}) \ {y}) := by
  -- Key fact: x ∈ equidistantPointsShift p x
  have hx_mem : x ∈ equidistantPointsShift p x := mem_equidistantPointsShift p x
  -- y ∉ skeleton since y ∉ equidistantPointsShift p x and skeleton ⊆ equidistantPointsShift p x
  have hy_not_skel : y ∉ equidistantPointsShift p x \ {x} := by
    intro hmem
    exact hy_not_mem (Set.diff_subset hmem)
  -- insert y skeleton \ {y} = skeleton when y ∉ skeleton
  have h1 : insert y (equidistantPointsShift p x \ {x}) \ {y} =
      equidistantPointsShift p x \ {x} := by
    ext z
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz_mem, hz_ne_y⟩
      rcases hz_mem with rfl | hz_skel
      · exact absurd rfl hz_ne_y
      · exact hz_skel
    · intro hz_skel
      constructor
      · right; exact hz_skel
      · intro hz_eq_y
        rw [hz_eq_y] at hz_skel
        exact hy_not_skel hz_skel
  -- insert x skeleton = equidistantPointsShift p x
  have h2 : insert x (equidistantPointsShift p x \ {x}) = equidistantPointsShift p x := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hz_mem, _⟩)
      · exact hx_mem
      · exact hz_mem
    · intro hz_mem
      by_cases hzx : z = x
      · left; exact hzx
      · right; exact ⟨hz_mem, hzx⟩
  rw [h1, h2]

/-- equidistantPointsShift p x induces E_{p/q} where q = ⌈p/r⌉.

    The proof constructs a translation isomorphism (shift by -x) from
    equidistantPointsShift p x to equidistantPoints p, then composes with the
    base isomorphism from circleGraph_equidistant_induced_open.
    The parameter q must equal ⌈p/r⌉, which is established via clique number
    preservation: both the swapped set and equidistant set are isomorphic to
    fractionGraphs whose clique numbers determine the q parameter. -/
lemma equidistantPointsShift_iso_from_swap_iso
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) (x y : Circle) (hxy : x ≠ y)
    (hiso_swap : Nonempty ((circleGraphOpen r hr).induce
        (insert y (equidistantPointsShift p x \ ({x} : Set Circle))) ≃g fractionGraph p q)) :
    Nonempty ((circleGraphOpen r hr).induce (equidistantPointsShift p x) ≃g fractionGraph p q) := by
  have hp_ge_2 : 2 ≤ p := by omega
  -- Get iso: induce(equidistantPoints p) ≃g fractionGraph p q' where q' = Nat.ceil(p/r)
  rcases circleGraph_equidistant_induced_open r hr p hp_ge_2 with ⟨iso_base, _⟩
  -- Shift iso: induce(equidistantPointsShift p x) ≃g induce(equidistantPoints p)
  have shift_iso : (circleGraphOpen r hr).induce (equidistantPointsShift p x) ≃g
      (circleGraphOpen r hr).induce (equidistantPoints p) := by
    classical
    exact
      { toEquiv :=
          { toFun := fun z => ⟨-x + z, by
              rcases z.property with ⟨t, ht, htz⟩
              have hz : (-x + (z : Circle)) = t := by
                calc -x + (z : Circle) = -x + (x + t) := by simpa [htz]
                  _ = t := by simpa using (neg_add_cancel_left x t)
              simpa [hz] using ht⟩
            invFun := fun z => ⟨x + z, ⟨z, z.property, rfl⟩⟩
            left_inv := fun z => by ext; simp
            right_inv := fun z => by ext; simp }
        map_rel_iff' := fun {a b} => by
          simpa [SimpleGraph.induce_adj] using
            (circleGraphOpen_adj_add_left r hr (-x) (a : Circle) (b : Circle)) }
  -- Compose: induce(equidistantPointsShift p x) ≃g fractionGraph p q'
  set q' := Nat.ceil ((p : ℝ) / r) with hq'_def
  have shift_composed : (circleGraphOpen r hr).induce (equidistantPointsShift p x) ≃g
      fractionGraph p q' := shift_iso.trans iso_base
  -- It suffices to show q = q'
  suffices hqq' : q = q' by rw [hqq']; exact ⟨shift_composed⟩
  -- PROOF OF q = q':
  -- Strategy: show q ≤ q' and q' ≤ q using clique transfer through the shared skeleton.
  classical
  -- Abbreviations
  set S := equidistantPointsShift p x with hS_def
  set S' := insert y (S \ ({x} : Set Circle)) with hS'_def
  set skeleton := S \ ({x} : Set Circle) with hskel_def
  -- Extract the swap isomorphism
  obtain ⟨iso_sw⟩ := hiso_swap
  -- Basic properties
  have hr_pos : (0 : ℝ) < r := by linarith
  have hp_pos_real : (0 : ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
  -- r > 2 since r ≥ 2 and r is irrational (hence r ≠ 2)
  have hr_gt_2 : (2 : ℝ) < r := by
    rcases lt_or_eq_of_le hr with h | h
    · exact h
    · exfalso; rw [← h] at hirr; exact Nat.not_irrational 2 hirr
  -- 0 < q'
  have hq'_pos : 0 < q' := by rw [hq'_def, Nat.ceil_pos]; positivity
  -- Finiteness
  have hS_finite : S.Finite := equidistantPointsShift_finite p x
  have hS'_finite : S'.Finite := by
    apply Set.Finite.insert; exact hS_finite.subset Set.diff_subset
  -- Cardinalities from isomorphisms
  have hS_card : hS_finite.toFinset.card = p := by
    haveI : Fintype ↥S := hS_finite.fintype
    have h1 : hS_finite.toFinset.card = Fintype.card ↥S := hS_finite.card_toFinset
    have h2 : Fintype.card ↥S = Fintype.card (ZMod p) := shift_composed.card_eq
    have h3 : Fintype.card (ZMod p) = p := ZMod.card p
    omega
  have hS'_card : hS'_finite.toFinset.card = p := by
    haveI : Fintype ↥S' := hS'_finite.fintype
    have h1 : hS'_finite.toFinset.card = Fintype.card ↥S' := hS'_finite.card_toFinset
    have h2 : Fintype.card ↥S' = Fintype.card (ZMod p) := iso_sw.card_eq
    have h3 : Fintype.card (ZMod p) = p := ZMod.card p
    omega
  -- Key structural fact: y ∉ S
  have hy_not_in_S : y ∉ S := by
    intro hy_in
    -- y ∈ S and y ≠ x means y ∈ skeleton
    have hy_skel : y ∈ skeleton := ⟨hy_in, fun h => hxy (Set.mem_singleton_iff.mp h).symm⟩
    -- So insert y skeleton = skeleton, hence S' = skeleton
    have hS'_eq_skel : S' = skeleton := Set.insert_eq_self.mpr hy_skel
    -- |skeleton| = |S| - 1 = p - 1
    have hx_in_S : x ∈ S := mem_equidistantPointsShift p x
    have hskel_finite := hS_finite.subset (Set.diff_subset : skeleton ⊆ S)
    have hskel_card : hskel_finite.toFinset.card = p - 1 := by
      have h_eq : hskel_finite.toFinset = hS_finite.toFinset \ {x} := by
        ext z; simp [Set.Finite.mem_toFinset]
      rw [h_eq, Finset.sdiff_singleton_eq_erase]
      have hmem : x ∈ hS_finite.toFinset := (Set.Finite.mem_toFinset _).mpr hx_in_S
      rw [Finset.card_erase_of_mem hmem, hS_card]
    -- But |S'| = p and S' = skeleton, contradiction
    have h_finset_eq : hS'_finite.toFinset = hskel_finite.toFinset := by
      ext z; rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, hS'_eq_skel]
    rw [h_finset_eq] at hS'_card
    omega
  -- Skeleton = S' \ {y}
  have hskel_eq : skeleton = S' \ {y} := by
    ext z
    simp only [hskel_def, hS'_def, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hz_S, hz_ne_x⟩
      exact ⟨Or.inr ⟨hz_S, hz_ne_x⟩, fun heq => hy_not_in_S (heq ▸ hz_S)⟩
    · intro ⟨hz_S', hz_ne_y⟩
      rcases hz_S' with rfl | ⟨hz_S, hz_ne_x⟩
      · exact absurd rfl hz_ne_y
      · exact ⟨hz_S, hz_ne_x⟩
  -- Skeleton ⊆ S and skeleton ⊆ S'
  have hskel_sub_S : skeleton ⊆ S := Set.diff_subset
  have hskel_sub_S' : skeleton ⊆ S' := hskel_eq ▸ Set.diff_subset
  -- 2 * q' ≤ p: proved by contradiction (if 2q' > p, the fractionGraph is complete,
  -- forcing p - 1 ≤ q from a skeleton clique, contradicting 2q ≤ p for p ≥ 3)
  have h2q' : 2 * q' ≤ p := by
    by_contra hcon
    push_neg at hcon
    haveI : Fintype ↥S := hS_finite.fintype
    haveI : Fintype ↥S' := hS'_finite.fintype
    -- All distinct pairs in S are adjacent (fractionGraph p q' is complete when 2q' > p)
    have hS_adj : ∀ (a b : ↥S), a ≠ b →
        ((circleGraphOpen r hr).induce S).Adj a b := by
      intro a b hab
      rw [← shift_composed.map_rel_iff]
      refine ⟨fun h => hab (shift_composed.injective h), ?_⟩
      calc distMod p (shift_composed a) (shift_composed b)
          ≤ p / 2 := by
            unfold distMod
            have := ZMod.val_lt (shift_composed a - shift_composed b)
            simp only [Nat.min_def]; split <;> omega
        _ < q' := by omega
    -- Build (p-1)-clique in S' from skeleton (all of S' except y)
    let y_sub : ↥S' := ⟨y, Set.mem_insert y _⟩
    let skel_fs : Finset ↥S' := Finset.univ.erase y_sub
    have hskel_clique : ((circleGraphOpen r hr).induce S').IsClique skel_fs := by
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_erase] at hu hv
      have hu_ne_y : (u : Circle) ≠ y := fun h => hu.1 (Subtype.ext h)
      have hv_ne_y : (v : Circle) ≠ y := fun h => hv.1 (Subtype.ext h)
      have hu_S : (u : Circle) ∈ S := by
        rcases Set.mem_insert_iff.mp u.property with heq | h
        · exact absurd heq hu_ne_y
        · exact h.1
      have hv_S : (v : Circle) ∈ S := by
        rcases Set.mem_insert_iff.mp v.property with heq | h
        · exact absurd heq hv_ne_y
        · exact h.1
      exact hS_adj ⟨_, hu_S⟩ ⟨_, hv_S⟩ (by
        intro h; apply huv; ext
        exact congrArg (fun (x : ↥S) => (x : Circle)) h)
    have hskel_card : skel_fs.card = p - 1 := by
      simp only [skel_fs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      have : Fintype.card ↥S' = p := by rw [iso_sw.card_eq, ZMod.card]
      omega
    -- p - 1 ≤ cliqueNum(induce S')
    have h_skel_le := hskel_clique.card_le_cliqueNum
    rw [hskel_card] at h_skel_le
    -- cliqueNum(induce S') ≤ q (via iso_sw)
    have h_cn_le : ((circleGraphOpen r hr).induce S').cliqueNum ≤ q := by
      rw [← FractionGraphBasic.cliqueNum_fractionGraph_eq p q hq h2q]
      obtain ⟨s, hs⟩ := ((circleGraphOpen r hr).induce S').exists_isNClique_cliqueNum
      let s' := s.image iso_sw
      have hs'_card : s'.card = s.card := by
        apply Finset.card_image_of_injOn
        intro a _ b _ h; exact iso_sw.toEquiv.injective h
      have hs'_clique : (fractionGraph p q).IsClique s' := by
        intro u hu v hv huv
        rw [Finset.mem_coe, Finset.mem_image] at hu hv
        obtain ⟨a, ha, rfl⟩ := hu
        obtain ⟨b, hb, rfl⟩ := hv
        exact iso_sw.map_rel_iff.mpr
          (hs.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
            (fun h => huv (congrArg iso_sw h)))
      calc ((circleGraphOpen r hr).induce S').cliqueNum = s.card := hs.card_eq.symm
        _ = s'.card := hs'_card.symm
        _ ≤ (fractionGraph p q).cliqueNum := hs'_clique.card_le_cliqueNum
    -- p - 1 ≤ q, 2q ≤ p → p ≤ 2 → p = 2, q = 1
    have hp2 : p = 2 := by omega
    -- q' = ⌈2/r⌉ = 1 since r > 2
    have hq'_le_1 : q' ≤ 1 := by
      have h1 : (↑p : ℝ) / r ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < r), hp2]; exact_mod_cast hr
      rw [hq'_def]; exact Nat.ceil_le.mpr (by exact_mod_cast h1)
    -- q' = 1, 2q' = 2 ≤ 2 = p, contradicting hcon
    omega
  -- Direction 1: q ≤ q'
  -- Strategy: build a q-clique in induce S, then use cliqueNum(induce S) = q'
  have hq_le_q' : q ≤ q' := by
    -- Finite type instances
    haveI : Fintype ↥S := hS_finite.fintype
    haveI : Fintype ↥S' := hS'_finite.fintype
    -- Step 1: Build q-element clique in fractionGraph p q avoiding iso_sw(y)
    have hy_mem_S' : y ∈ S' := Set.mem_insert y _
    let y_sub : ↥S' := ⟨y, hy_mem_S'⟩
    let w₀ := iso_sw y_sub
    let arc_start := w₀ + (q : ZMod p)
    -- Step 2: Define the composed map: j ↦ iso_sw.symm(arc_start + j).val ∈ S
    -- Each element avoids y, hence lies in skeleton ⊆ S
    let φ : ℕ → Circle := fun j =>
      (iso_sw.symm (arc_start + (j : ZMod p)) : Circle)
    -- Each φ j for j < q avoids y (since arc_start + j ≠ w₀)
    have hφ_ne_y : ∀ j < q, φ j ≠ y := by
      intro j hj heq
      have : iso_sw.symm (arc_start + (j : ZMod p)) = y_sub := Subtype.ext heq
      have h1 : arc_start + (j : ZMod p) = w₀ := by
        have := congrArg iso_sw this; simp only [RelIso.apply_symm_apply] at this; exact this
      -- arc_start + j = w₀ + q + j = w₀ means q + j ≡ 0 mod p
      have h2 : (q : ZMod p) + (j : ZMod p) = 0 := by
        have : w₀ + ((q : ZMod p) + (j : ZMod p)) = w₀ := by rwa [← add_assoc]
        simpa using this
      have h3 : ((q + j : ℕ) : ZMod p) = 0 := by push_cast at h2 ⊢; exact h2
      have hqj_lt : q + j < p := by omega
      have h4 := ZMod.val_natCast_of_lt hqj_lt
      rw [h3, ZMod.val_zero] at h4; omega
    -- Each φ j for j < q lies in skeleton
    have hφ_in_skel : ∀ j < q, φ j ∈ skeleton := by
      intro j hj
      have hval := (iso_sw.symm (arc_start + (j : ZMod p))).property
      simp only [hS'_def, Set.mem_insert_iff] at hval
      rcases hval with heq | hvskel
      · exact absurd heq (hφ_ne_y j hj)
      · exact hvskel
    -- Each φ j for j < q lies in S
    have hφ_in_S : ∀ j < q, φ j ∈ S := fun j hj => hskel_sub_S (hφ_in_skel j hj)
    -- Step 3: Build Finset ↥S
    let ψ : ℕ → ↥S := fun j =>
      if hj : j < q then ⟨φ j, hφ_in_S j hj⟩
      else ⟨x, mem_equidistantPointsShift p x⟩
    set clique_S := (Finset.range q).image ψ with hclique_S_def
    -- Step 4: clique_S is a clique in induce S
    have hclique_S_isClique : ((circleGraphOpen r hr).induce S).IsClique clique_S := by
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_image] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      rw [Finset.mem_range] at ha hb
      simp only [ψ, dif_pos ha, dif_pos hb] at huv ⊢
      rw [SimpleGraph.induce_adj]
      -- The corresponding elements in fractionGraph are adjacent
      have hne_zmod : arc_start + (a : ZMod p) ≠ arc_start + (b : ZMod p) := by
        intro heq
        apply huv
        ext
        change φ a = φ b
        simp [φ, heq]
      have hadj_f : (fractionGraph p q).Adj (arc_start + (a : ZMod p))
          (arc_start + (b : ZMod p)) := by
        exact FractionGraphBasic.isClique_arc p q hq h2q arc_start
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, rfl⟩))
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr hb, rfl⟩))
          hne_zmod
      -- Transfer through iso_sw.symm
      exact iso_sw.symm.map_rel_iff.mpr hadj_f
    -- Step 5: |clique_S| = q
    have hclique_S_card : clique_S.card = q := by
      rw [hclique_S_def, Finset.card_image_of_injOn]
      · exact Finset.card_range q
      · intro a ha b hb heq
        rw [Finset.mem_coe, Finset.mem_range] at ha hb
        have hval_eq : φ a = φ b := by
          have h := congrArg Subtype.val heq
          simp only [ψ, dif_pos ha, dif_pos hb] at h
          exact h
        have h_eq_zmod : arc_start + (a : ZMod p) = arc_start + (b : ZMod p) := by
          have h1 : iso_sw.symm (arc_start + (a : ZMod p)) =
              iso_sw.symm (arc_start + (b : ZMod p)) := by
            ext; exact hval_eq
          exact iso_sw.symm.injective h1
        have := add_left_cancel h_eq_zmod
        have ha' : a < p := by omega
        have hb' : b < p := by omega
        have := congrArg ZMod.val this
        rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this
    -- Step 6: q ≤ cliqueNum(induce S) = q'
    have h_card_le := hclique_S_isClique.card_le_cliqueNum
    rw [hclique_S_card] at h_card_le
    have h_cn_eq : ((circleGraphOpen r hr).induce S).cliqueNum = q' := by
      rw [← FractionGraphBasic.cliqueNum_fractionGraph_eq p q' hq'_pos h2q']
      -- cliqueNum is preserved by iso shift_composed
      -- Need: cliqueNum(induce S) = cliqueNum(fractionGraph p q')
      -- This follows from shift_composed being an iso
      have h_le_1 : ((circleGraphOpen r hr).induce S).cliqueNum ≤
          (fractionGraph p q').cliqueNum := by
        obtain ⟨s, hs⟩ := ((circleGraphOpen r hr).induce S).exists_isNClique_cliqueNum
        -- Map s through shift_composed to get a clique in fractionGraph
        let s' := s.image shift_composed
        have hs'_clique : (fractionGraph p q').IsClique s' := by
          intro u hu v hv huv
          rw [Finset.mem_coe, Finset.mem_image] at hu hv
          obtain ⟨a, ha, rfl⟩ := hu
          obtain ⟨b, hb, rfl⟩ := hv
          have hne : a ≠ b := fun h => huv (congrArg shift_composed h)
          exact shift_composed.map_rel_iff.mpr
            (hs.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne)
        have hs'_card : s'.card = s.card := by
          rw [Finset.card_image_of_injOn]
          intro a ha b hb heq
          exact shift_composed.toEquiv.injective heq
        calc ((circleGraphOpen r hr).induce S).cliqueNum = s.card := hs.card_eq.symm
          _ = s'.card := hs'_card.symm
          _ ≤ (fractionGraph p q').cliqueNum := hs'_clique.card_le_cliqueNum
      have h_le_2 : (fractionGraph p q').cliqueNum ≤
          ((circleGraphOpen r hr).induce S).cliqueNum := by
        obtain ⟨s, hs⟩ := (fractionGraph p q').exists_isNClique_cliqueNum
        let s' := s.image shift_composed.symm
        have hs'_clique : ((circleGraphOpen r hr).induce S).IsClique s' := by
          intro u hu v hv huv
          rw [Finset.mem_coe, Finset.mem_image] at hu hv
          obtain ⟨a, ha, rfl⟩ := hu
          obtain ⟨b, hb, rfl⟩ := hv
          have hne : a ≠ b := fun h => huv (congrArg shift_composed.symm h)
          exact shift_composed.symm.map_rel_iff.mpr
            (hs.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne)
        have hs'_card : s'.card = s.card := by
          rw [Finset.card_image_of_injOn]
          intro a ha b hb heq
          exact shift_composed.symm.toEquiv.injective heq
        calc (fractionGraph p q').cliqueNum = s.card := hs.card_eq.symm
          _ = s'.card := hs'_card.symm
          _ ≤ ((circleGraphOpen r hr).induce S).cliqueNum := hs'_clique.card_le_cliqueNum
      exact le_antisymm h_le_1 h_le_2
    linarith
  -- Direction 2: q' ≤ q (symmetric argument)
  have hq'_le_q : q' ≤ q := by
    haveI : Fintype ↥S := hS_finite.fintype
    haveI : Fintype ↥S' := hS'_finite.fintype
    -- Get a q'-clique in fractionGraph p q' avoiding shift_composed(x_sub)
    have hx_in_S : x ∈ S := mem_equidistantPointsShift p x
    let x_sub : ↥S := ⟨x, hx_in_S⟩
    let v₀ := shift_composed x_sub
    let arc_start' := v₀ + (q' : ZMod p)
    -- φ' : j ↦ shift_composed.symm(arc_start' + j).val
    let φ' : ℕ → Circle := fun j =>
      (shift_composed.symm (arc_start' + (j : ZMod p)) : Circle)
    -- Each φ' j for j < q' avoids x
    have hφ'_ne_x : ∀ j < q', φ' j ≠ x := by
      intro j hj heq
      have : shift_composed.symm (arc_start' + (j : ZMod p)) = x_sub := Subtype.ext heq
      have h1 : arc_start' + (j : ZMod p) = v₀ := by
        have := congrArg shift_composed this
        simp only [RelIso.apply_symm_apply] at this; exact this
      have h2 : (q' : ZMod p) + (j : ZMod p) = 0 := by
        have : v₀ + ((q' : ZMod p) + (j : ZMod p)) = v₀ := by rwa [← add_assoc]
        simpa using this
      have h3 : ((q' + j : ℕ) : ZMod p) = 0 := by push_cast at h2 ⊢; exact h2
      have hqj_lt : q' + j < p := by omega
      have h4 := ZMod.val_natCast_of_lt hqj_lt
      rw [h3, ZMod.val_zero] at h4; omega
    -- Each φ' j for j < q' lies in skeleton
    have hφ'_in_skel : ∀ j < q', φ' j ∈ skeleton := by
      intro j hj
      have hval := (shift_composed.symm (arc_start' + (j : ZMod p))).property
      constructor
      · exact hval
      · intro hx_eq
        exact hφ'_ne_x j hj (Set.mem_singleton_iff.mp hx_eq)
    -- Each φ' j for j < q' lies in S'
    have hφ'_in_S' : ∀ j < q', φ' j ∈ S' := fun j hj => hskel_sub_S' (hφ'_in_skel j hj)
    -- Build Finset ↥S'
    let ψ' : ℕ → ↥S' := fun j =>
      if hj : j < q' then ⟨φ' j, hφ'_in_S' j hj⟩
      else ⟨y, Set.mem_insert y _⟩
    set clique_S' := (Finset.range q').image ψ' with hclique_S'_def
    -- clique_S' is a clique in induce S'
    have hclique_S'_isClique : ((circleGraphOpen r hr).induce S').IsClique clique_S' := by
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_image] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      rw [Finset.mem_range] at ha hb
      simp only [ψ', dif_pos ha, dif_pos hb] at huv ⊢
      rw [SimpleGraph.induce_adj]
      have hne_zmod : arc_start' + (a : ZMod p) ≠ arc_start' + (b : ZMod p) := by
        intro heq; apply huv; ext; change φ' a = φ' b; simp [φ', heq]
      have hadj_f : (fractionGraph p q').Adj (arc_start' + (a : ZMod p))
          (arc_start' + (b : ZMod p)) :=
        FractionGraphBasic.isClique_arc p q' hq'_pos h2q' arc_start'
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, rfl⟩))
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr hb, rfl⟩))
          hne_zmod
      exact shift_composed.symm.map_rel_iff.mpr hadj_f
    -- |clique_S'| = q'
    have hclique_S'_card : clique_S'.card = q' := by
      rw [hclique_S'_def, Finset.card_image_of_injOn]
      · exact Finset.card_range q'
      · intro a ha b hb heq
        rw [Finset.mem_coe, Finset.mem_range] at ha hb
        have hval_eq : φ' a = φ' b := by
          have h := congrArg Subtype.val heq
          simp only [ψ', dif_pos ha, dif_pos hb] at h
          exact h
        have h_eq_zmod : arc_start' + (a : ZMod p) = arc_start' + (b : ZMod p) := by
          have h1 : shift_composed.symm (arc_start' + (a : ZMod p)) =
              shift_composed.symm (arc_start' + (b : ZMod p)) := by ext; exact hval_eq
          exact shift_composed.symm.injective h1
        have := add_left_cancel h_eq_zmod
        have ha' : a < p := by omega
        have hb' : b < p := by omega
        have := congrArg ZMod.val this
        rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this
    -- q' ≤ cliqueNum(induce S') = q
    have h_card_le := hclique_S'_isClique.card_le_cliqueNum
    rw [hclique_S'_card] at h_card_le
    have h_cn_eq : ((circleGraphOpen r hr).induce S').cliqueNum = q := by
      rw [← FractionGraphBasic.cliqueNum_fractionGraph_eq p q hq h2q]
      have h_le_1 : ((circleGraphOpen r hr).induce S').cliqueNum ≤
          (fractionGraph p q).cliqueNum := by
        obtain ⟨s, hs⟩ := ((circleGraphOpen r hr).induce S').exists_isNClique_cliqueNum
        let s' := s.image iso_sw
        have hs'_clique : (fractionGraph p q).IsClique s' := by
          intro u hu v hv huv
          rw [Finset.mem_coe, Finset.mem_image] at hu hv
          obtain ⟨a, ha, rfl⟩ := hu
          obtain ⟨b, hb, rfl⟩ := hv
          have hne : a ≠ b := fun h => huv (congrArg iso_sw h)
          exact iso_sw.map_rel_iff.mpr
            (hs.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne)
        have hs'_card : s'.card = s.card := by
          rw [Finset.card_image_of_injOn]
          intro a ha b hb heq; exact iso_sw.toEquiv.injective heq
        calc ((circleGraphOpen r hr).induce S').cliqueNum = s.card := hs.card_eq.symm
          _ = s'.card := hs'_card.symm
          _ ≤ (fractionGraph p q).cliqueNum := hs'_clique.card_le_cliqueNum
      have h_le_2 : (fractionGraph p q).cliqueNum ≤
          ((circleGraphOpen r hr).induce S').cliqueNum := by
        obtain ⟨s, hs⟩ := (fractionGraph p q).exists_isNClique_cliqueNum
        let s' := s.image iso_sw.symm
        have hs'_clique : ((circleGraphOpen r hr).induce S').IsClique s' := by
          intro u hu v hv huv
          rw [Finset.mem_coe, Finset.mem_image] at hu hv
          obtain ⟨a, ha, rfl⟩ := hu
          obtain ⟨b, hb, rfl⟩ := hv
          have hne : a ≠ b := fun h => huv (congrArg iso_sw.symm h)
          exact iso_sw.symm.map_rel_iff.mpr
            (hs.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne)
        have hs'_card : s'.card = s.card := by
          rw [Finset.card_image_of_injOn]
          intro a ha b hb heq; exact iso_sw.symm.toEquiv.injective heq
        calc (fractionGraph p q).cliqueNum = s.card := hs.card_eq.symm
          _ = s'.card := hs'_card.symm
          _ ≤ ((circleGraphOpen r hr).induce S').cliqueNum := hs'_clique.card_le_cliqueNum
      exact le_antisymm h_le_1 h_le_2
    linarith
  -- Combine
  exact le_antisymm hq_le_q' hq'_le_q

/-- For consecutive Stern-Brocot neighbors (a, b) and (a0, b0) where a * b0 - b * a0 = 1,
    with a/b > r > a0/b0, we have floor(a/r) = b.

    Proof:
    1. Lower bound: From r < a/b, we get b*r < a, so a/r > b, thus floor(a/r) ≥ b.
    2. Upper bound: From determinant a*b0 - b*a0 = 1, we get a/b - a0/b0 = 1/(b*b0).
       Since r > a0/b0, we have a/b - r < a/b - a0/b0 = 1/(b*b0).
       So a - b*r < b/(b*b0) = 1/b0 ≤ 1 < r ≤ (since r ≥ 2 and b0 ≥ 1).
       Thus a < b*r + r = (b+1)*r, giving a/r < b+1, so floor(a/r) ≤ b.
    3. Combined: floor(a/r) = b. -/
lemma floor_convergent_from_pred
    (r : ℝ) (hr : 2 ≤ r) (_hirr : Irrational r)
    (a b a0 b0 : ℕ) (ha : 0 < a) (hb : 0 < b) (_h2b : 2 * b ≤ a)
    (ha0 : 0 < a0) (_ha0_lt : a0 < a) (hb0 : 0 < b0) (_hb0_lt : b0 < b)
    (hpred : a * b0 - b * a0 = 1)
    -- Additional hypotheses: r is between the two Stern-Brocot neighbors
    (ha0b0_lt_r : (a0 : ℝ) / b0 < r) -- even convergent below r
    (hr_lt_ab : r < (a : ℝ) / b) : -- odd convergent above r
    Nat.floor ((a : ℝ) / r) = b := by
  have hr_pos : 0 < r := by linarith
  have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hb0_pos : (0 : ℝ) < b0 := Nat.cast_pos.mpr hb0
  have ha0_pos : (0 : ℝ) < a0 := Nat.cast_pos.mpr ha0
  -- Lower bound: a/r > b
  have h_lower : (b : ℝ) < (a : ℝ) / r := by
    rw [lt_div_iff₀ hr_pos]
    have h1 : r * b < a := by
      rw [mul_comm]
      calc (b : ℝ) * r < (a : ℝ) / b * b := by nlinarith
        _ = (a : ℝ) := div_mul_cancel₀ (a : ℝ) (ne_of_gt hb_pos)
    linarith
  -- Upper bound: a/r < b + 1
  -- From determinant: a/b - a0/b0 = 1/(b*b0)
  have h_det_real : (a : ℝ) * b0 - b * a0 = 1 := by
    have h := hpred
    have ha_b0 : (a : ℝ) * (b0 : ℝ) = ((a * b0 : ℕ) : ℝ) := by simp [Nat.cast_mul]
    have hb_a0 : (b : ℝ) * (a0 : ℝ) = ((b * a0 : ℕ) : ℝ) := by simp [Nat.cast_mul]
    simp only [ha_b0, hb_a0]
    -- Need: (a * b0 : ℕ) - (b * a0 : ℕ) = 1
    -- From hpred : a * b0 - b * a0 = 1, need to convert Nat subtraction to real
    -- Since hpred says a * b0 - b * a0 = 1, this means a * b0 ≥ b * a0 + 1 > b * a0
    have h_gt : a * b0 > b * a0 := by omega
    rw [← Nat.cast_sub (Nat.le_of_lt h_gt)]
    simp only [hpred, Nat.cast_one]
  -- a/b - a0/b0 = 1/(b*b0)
  have h_diff : (a : ℝ) / b - a0 / b0 = 1 / (b * b0) := by
    have hbb0_ne : (b : ℝ) * b0 ≠ 0 := mul_ne_zero (ne_of_gt hb_pos) (ne_of_gt hb0_pos)
    field_simp
    linarith [h_det_real]
  -- Since a0/b0 < r < a/b and a/b - a0/b0 = 1/(b*b0), we get a/b - r < 1/(b*b0).
  have h_ab_minus_r : (a : ℝ) / b - r < 1 / (b * b0) := by
    -- From a0/b0 < r < a/b and a/b - a0/b0 = 1/(b*b0):
    -- a/b - r < a/b - a0/b0 = 1/(b*b0)
    calc (a : ℝ) / b - r < (a : ℝ) / b - a0 / b0 := by linarith
      _ = 1 / (b * b0) := h_diff
  -- From a/b - r < 1/(b*b0):
  -- a - b*r < b/(b*b0) = 1/b0 ≤ 1 (since b0 ≥ 1)
  have h_a_minus_br : (a : ℝ) - b * r < 1 / b0 := by
    have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
    have hb0_ne : (b0 : ℝ) ≠ 0 := ne_of_gt hb0_pos
    have hbb0_ne : (b : ℝ) * b0 ≠ 0 := mul_ne_zero hb_ne hb0_ne
    have h1 : (a : ℝ) - b * r = ((a : ℝ) / b - r) * b := by
      rw [sub_mul, div_mul_cancel₀ (a : ℝ) hb_ne, mul_comm]
    have h2 : ((a : ℝ) / b - r) * b < 1 / (b * b0) * b := by
      apply mul_lt_mul_of_pos_right h_ab_minus_r hb_pos
    have h3 : (1 : ℝ) / (b * b0) * b = 1 / b0 := by field_simp
    linarith
  -- 1/b0 ≤ 1 since b0 ≥ 1
  have h_inv_b0_le_one : 1 / b0 ≤ (1 : ℝ) := by
    rw [div_le_one hb0_pos]
    exact Nat.one_le_cast.mpr hb0
  -- 1 ≤ r
  have h_one_le_r : (1 : ℝ) ≤ r := by linarith
  -- a - b*r < 1/b0 ≤ 1 ≤ r
  have h_a_lt_bplusone_r : (a : ℝ) < (b + 1) * r := by
    calc (a : ℝ) = b * r + (a - b * r) := by ring
      _ < b * r + 1 / b0 := by linarith
      _ ≤ b * r + 1 := by linarith
      _ ≤ b * r + r := by linarith
      _ = (b + 1) * r := by ring
  -- Upper bound: a/r < b + 1
  have h_upper : (a : ℝ) / r < b + 1 := by
    rw [div_lt_iff₀ hr_pos]
    exact h_a_lt_bplusone_r
  -- Combine: b < a/r < b + 1, so floor(a/r) = b
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · exact le_of_lt h_lower
  · exact h_upper

/-- For convergent pairs with floor(a/r) = b, we have r ≤ a.
    Proof: floor(a/r) = b implies b ≤ a/r, so b*r ≤ a.
    Since b ≥ 1, we get r ≤ b*r ≤ a. -/
lemma r_le_convergent
    (r : ℝ) (hr : 2 ≤ r)
    (a b : ℕ) (hb : 0 < b)
    (hfloor : Nat.floor ((a : ℝ) / r) = b) :
    r ≤ (a : ℝ) := by
  -- From floor(a/r) = b, we have b ≤ a/r
  have h_floor_le : (b : ℝ) ≤ (a : ℝ) / r := by
    rw [← hfloor]
    exact Nat.floor_le (by positivity)
  -- Multiply by r > 0 to get b * r ≤ a
  have hr_pos : 0 < r := by linarith
  have h_br_le : (b : ℝ) * r ≤ (a : ℝ) := by
    calc (b : ℝ) * r = (b : ℝ) * r := rfl
      _ ≤ ((a : ℝ) / r) * r := by nlinarith [h_floor_le]
      _ = (a : ℝ) := by field_simp
  -- Since b ≥ 1, we have r ≤ b * r ≤ a
  have hb_ge_one : (1 : ℝ) ≤ (b : ℝ) := by
    simp only [Nat.one_le_cast]
    omega
  calc r = 1 * r := by ring
    _ ≤ (b : ℝ) * r := by nlinarith
    _ ≤ (a : ℝ) := h_br_le

/-- If S induces E_{p/q} in the closed graph, then S has exactly p elements.
    This is the closed variant of fractionGraph_iso_card. -/
lemma fractionGraph_iso_card_closed
    (r : ℝ) (hr : 2 ≤ r)
    (p q : ℕ) [NeZero p]
    (S : Set Circle) (hS_finite : S.Finite)
    (hiso : Nonempty ((circleGraphClosed r hr).induce S ≃g fractionGraph p q)) :
    hS_finite.toFinset.card = p := by
  obtain ⟨iso⟩ := hiso
  haveI : Fintype ↥S := hS_finite.fintype
  have h1 : hS_finite.toFinset.card = Fintype.card ↥S := hS_finite.card_toFinset
  have h2 : Fintype.card ↥S = Fintype.card (ZMod p) := iso.card_eq
  have h3 : Fintype.card (ZMod p) = p := ZMod.card p
  omega

/-- Key slot argument: If S_y and S_x share skeleton (S_y \ {y} = S_x \ {x}),
    and both f(S_y) and f(S_x) are isomorphic to E_{a1/q} as induced subgraphs,
    then f(y) and f(x) are in the same "slot" of f(skeleton).

    More precisely: Let skeleton = S_y \ {y} = S_x \ {x}.
    Then f(y) and f(x) are both in the same arc of f(skeleton),
    i.e., the arc from f(s_prev) to f(s_next) where s_prev and s_next are
    the common cyclic neighbors of y and x in skeleton.

    This follows from insertion_same_gap_of_both_iso_to_fraction applied to
    f(skeleton), f(y), and f(x). -/
lemma same_slot_of_shared_skeleton
    (G : SimpleGraph Circle)
    (a1 q : ℕ) [NeZero a1] (ha1_ge : 3 ≤ a1) (hq_ge : 2 ≤ q) (hq_pos : 0 < q)
    (h2q : 2 * q ≤ a1) (hcoprime : Nat.Coprime a1 q)
    (S_y : Set Circle) (hS_y_finite : S_y.Finite) (hcard_y : hS_y_finite.toFinset.card = a1)
    (y : Circle) (hy : y ∈ S_y)
    -- S_x = skeleton ∪ {x} where skeleton = S_y \ {y}
    (x : Circle) (hxy : x ≠ y)
    (S_x : Set Circle) (hS_x : S_x = insert x (S_y \ {y}))
    (hx : x ∈ S_x)
    (f : Circle → Circle)
    (hfxy : f y ≠ f x)
    -- f(S_y) is isomorphic to E_{a1/q} (in graph G, either open or closed)
    (_hiso_y : Nonempty (G.induce (S_y.image f) ≃g
                fractionGraph a1 q))
    -- f(S_x) is isomorphic to E_{a1/q}
    (_hiso_x : Nonempty (G.induce (S_x.image f) ≃g
                fractionGraph a1 q))
    -- Distance monotonicity: G respects circle distance (holds for circleGraphOpen/Closed)
    (hG_mono : ∀ u v w : Circle, u ≠ v → u ≠ w →
      G.Adj u w → dist u v < dist u w → G.Adj u v)
    (hG_ccw_trans : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
      G.Adj u w → G.Adj u v → repFrom u v < repFrom u w → repFrom u w ≤ 1/2 → G.Adj v w) :
    -- f(y) and f(x) are in the same slot: there exist skeleton points s1, s2
    -- such that f(y) is in the arc from f(s1) to f(s2), and f(x) is nearby
    ∃ s1 s2 : Circle, s1 ∈ S_y \ {y} ∧ s2 ∈ S_y \ {y} ∧ s1 ≠ s2 ∧
      -- f(y) is between f(s1) and f(s2) (in the arc not containing other skeleton points)
      repFrom (f s1) (f y) + repFrom (f y) (f s2) ≤ repFrom (f s1) (f s2) ∧
      -- f(x) is near f(s1) or near f(s2) (disjunction from automorphism structure)
      ((∀ t ∈ S_y \ {y}, t ≠ s1 →
        ¬(0 < repFrom (f s1) (f t) ∧ repFrom (f s1) (f t) < repFrom (f s1) (f x)))
       ∨
       (∀ t ∈ S_y \ {y}, t ≠ s2 →
        ¬(0 < repFrom (f s2) (f t) ∧ repFrom (f s2) (f t) < repFrom (f s2) (f x)))) ∧
      -- No skeleton point in interior of arc (f(s1), f(y))
      (∀ t ∈ S_y \ {y}, t ≠ s1 →
        ¬(0 < repFrom (f s1) (f t) ∧ repFrom (f s1) (f t) < repFrom (f s1) (f y))) ∧
      -- No skeleton point in interior of arc (f(y), f(s2))
      (∀ t ∈ S_y \ {y}, t ≠ s2 →
        ¬(0 < repFrom (f y) (f t) ∧ repFrom (f y) (f t) < repFrom (f y) (f s2))) := by
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 0: Setup and classical reasoning
  -- ════════════════════════════════════════════════════════════════════════════
  classical
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 1: Derive x ∉ S_y (from cardinality of the isomorphism)
  -- ════════════════════════════════════════════════════════════════════════════
  -- If x ∈ S_y, then since x ≠ y, x ∈ S_y \ {y}, so S_x = insert x (S_y \ {y}) = S_y \ {y}.
  -- Then |S_x| = a1 - 1, so |S_x.image f| ≤ a1 - 1.
  -- But the iso _hiso_x gives Fintype.card ↥(S_x.image f) = a1, contradiction.
  have hx_notin_Sy : x ∉ S_y := by
    intro hx_in
    have hx_skel : x ∈ S_y \ {y} := Set.mem_diff_singleton.mpr ⟨hx_in, hxy⟩
    have hSx_eq : S_x = S_y \ {y} := by
      rw [hS_x, Set.insert_eq_of_mem hx_skel]
    -- S_y \ {y} has a1 - 1 elements
    have hskel_finite : (S_y \ {y}).Finite := hS_y_finite.subset (Set.diff_subset (t := {y}))
    have hcard_skel : hskel_finite.toFinset.card = a1 - 1 := by
      have hy_mem : y ∈ hS_y_finite.toFinset := hS_y_finite.mem_toFinset.mpr hy
      have h1 : hskel_finite.toFinset = hS_y_finite.toFinset.erase y := by
        ext z
        simp only [Set.Finite.mem_toFinset, Set.mem_diff, Set.mem_singleton_iff,
                    Finset.mem_erase]
        tauto
      rw [h1, Finset.card_erase_of_mem hy_mem, hcard_y]
    -- |S_x.image f| ≤ |S_x| = a1 - 1 < a1
    obtain ⟨iso_x⟩ := _hiso_x
    have hSx_finite : S_x.Finite := hSx_eq ▸ hskel_finite
    -- |S_x.image f| = a1 via the isomorphism
    haveI : Fintype ↥(S_x.image f) := (hSx_finite.image f).fintype
    have hcard_img : (S_x.image f).ncard = a1 := by
      rw [Set.ncard_eq_toFinset_card' _, Set.toFinset_card]
      rw [iso_x.card_eq, ZMod.card a1]
    -- |S_x| = a1 - 1 (since S_x = S_y \ {y})
    have hcard_Sx : S_x.ncard ≤ a1 - 1 := by
      rw [hSx_eq, Set.ncard_eq_toFinset_card _ hskel_finite, hcard_skel]
    -- |image| ≤ |source|
    have : (S_x.image f).ncard ≤ S_x.ncard := Set.ncard_image_le hSx_finite
    omega
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 2: Derive f is injective on S_y (from |f(S_y)| = a1 = |S_y|)
  -- ════════════════════════════════════════════════════════════════════════════
  have hf_injOn_Sy : Set.InjOn f S_y := by
    obtain ⟨iso_y⟩ := _hiso_y
    apply Set.injOn_of_ncard_image_eq (s := S_y) (f := f) _ hS_y_finite
    rw [Set.ncard_eq_toFinset_card _ hS_y_finite,
        Set.ncard_eq_toFinset_card _ (hS_y_finite.image f)]
    haveI : Fintype ↥(S_y.image f) := (hS_y_finite.image f).fintype
    haveI : Fintype ↥S_y := hS_y_finite.fintype
    rw [hS_y_finite.card_toFinset, (hS_y_finite.image f).card_toFinset]
    have hcard_img_y : Fintype.card ↥(S_y.image f) = a1 := by
      rw [iso_y.card_eq, ZMod.card a1]
    have hcard_Sy : Fintype.card ↥S_y = a1 := by
      rw [hS_y_finite.card_toFinset] at hcard_y; exact hcard_y
    omega
  -- f is also injective on S_x
  have hSx_finite : S_x.Finite := by
    rw [hS_x]
    exact (hS_y_finite.subset Set.diff_subset).insert x
  have hf_injOn_Sx : Set.InjOn f S_x := by
    obtain ⟨iso_x⟩ := _hiso_x
    apply Set.injOn_of_ncard_image_eq (s := S_x) (f := f) _ hSx_finite
    rw [Set.ncard_eq_toFinset_card _ hSx_finite,
        Set.ncard_eq_toFinset_card _ (hSx_finite.image f)]
    haveI : Fintype ↥(S_x.image f) := (hSx_finite.image f).fintype
    haveI : Fintype ↥S_x := hSx_finite.fintype
    rw [hSx_finite.card_toFinset, (hSx_finite.image f).card_toFinset]
    have hcard_img_x : Fintype.card ↥(S_x.image f) = a1 := by
      rw [iso_x.card_eq, ZMod.card a1]
    -- |S_x| = a1: S_x = insert x (S_y \ {y}), x ∉ S_y, |S_y| = a1
    have hx_notin_skel : x ∉ S_y \ {y} := by
      intro h; exact hx_notin_Sy (Set.diff_subset h)
    have hcard_Sx : S_x.ncard = a1 := by
      rw [hS_x, Set.ncard_insert_of_notMem hx_notin_skel (hS_y_finite.subset Set.diff_subset)]
      have : (S_y \ {y}).ncard = a1 - 1 := by
        have h1 := Set.ncard_diff_singleton_add_one hy hS_y_finite
        rw [Set.ncard_eq_toFinset_card _ hS_y_finite] at h1
        omega
      omega
    rw [Set.ncard_eq_toFinset_card _ hSx_finite, hSx_finite.card_toFinset] at hcard_Sx
    omega
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 3: Construct T : Finset Circle as the image of the skeleton under f
  -- ════════════════════════════════════════════════════════════════════════════
  -- skeleton = S_y \ {y} as a Set
  -- T = f(skeleton) as a Finset
  let skel_finite : (S_y \ {y}).Finite := hS_y_finite.subset Set.diff_subset
  let T : Finset Circle := skel_finite.toFinset.image f
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 4: Show T.card = a1 - 1
  -- ════════════════════════════════════════════════════════════════════════════
  have hT_card : T.card = a1 - 1 := by
    -- f is injective on S_y \ {y} (subset of S_y where f is injective)
    have hf_injOn_skel : Set.InjOn f (S_y \ {y}) :=
      hf_injOn_Sy.mono Set.diff_subset
    rw [Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact hf_injOn_skel (skel_finite.mem_toFinset.mp ha) (skel_finite.mem_toFinset.mp hb) hab)]
    -- skel_finite.toFinset.card = a1 - 1
    have hy_mem : y ∈ hS_y_finite.toFinset := hS_y_finite.mem_toFinset.mpr hy
    have h1 : skel_finite.toFinset = hS_y_finite.toFinset.erase y := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_erase]
      tauto
    rw [h1, Finset.card_erase_of_mem hy_mem, hcard_y]
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 5: Show f(y) ∉ T and f(x) ∉ T
  -- ════════════════════════════════════════════════════════════════════════════
  have hfy_notin_T : f y ∉ T := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨t, ht_mem, ht_eq⟩ := hmem
    have ht_in_skel : t ∈ S_y \ {y} := skel_finite.mem_toFinset.mp ht_mem
    have ht_in_Sy : t ∈ S_y := Set.diff_subset ht_in_skel
    have ht_ne_y : t ≠ y := (Set.mem_diff_singleton.mp ht_in_skel).2
    exact ht_ne_y (hf_injOn_Sy ht_in_Sy hy ht_eq)
  have hfx_notin_T : f x ∉ T := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨t, ht_mem, ht_eq⟩ := hmem
    have ht_in_skel : t ∈ S_y \ {y} := skel_finite.mem_toFinset.mp ht_mem
    -- t ∈ S_y and t ∈ S_x (since S_y \ {y} ⊆ S_x via hS_x)
    have ht_in_Sx : t ∈ S_x := by
      rw [hS_x]; exact Set.mem_insert_of_mem x ht_in_skel
    have hx_in_Sx : x ∈ S_x := hx
    -- f(t) = f(x), so t = x (by injectivity of f on S_x)
    have htx : t = x := hf_injOn_Sx ht_in_Sx hx_in_Sx ht_eq
    -- But t ∈ S_y \ {y} ⊆ S_y, so x ∈ S_y, contradicting hx_notin_Sy
    exact hx_notin_Sy (htx ▸ Set.diff_subset ht_in_skel)
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 6: f(y) ≠ f(x) from hypothesis
  -- ════════════════════════════════════════════════════════════════════════════
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 7: Show S_y.image f = insert (f y) ↑T (as sets)
  -- ════════════════════════════════════════════════════════════════════════════
  have hSy_img_eq : S_y.image f = insert (f y) ↑T := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hwy : w = y
      · left; rw [hwy]
      · right
        show f w ∈ (T : Set Circle)
        rw [Finset.mem_coe]
        exact Finset.mem_image.mpr ⟨w, skel_finite.mem_toFinset.mpr
          (Set.mem_diff_singleton.mpr ⟨hw, hwy⟩), rfl⟩
    · rintro (rfl | hz)
      · exact ⟨y, hy, rfl⟩
      · rw [Finset.mem_coe] at hz
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        exact ⟨w, Set.diff_subset (skel_finite.mem_toFinset.mp hw), rfl⟩
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 8: Show S_x.image f = insert (f x) ↑T (as sets)
  -- ════════════════════════════════════════════════════════════════════════════
  have hSx_img_eq : S_x.image f = insert (f x) ↑T := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hS_x] at hw
      cases hw with
      | inl h => left; rw [h]
      | inr h =>
        -- w ∈ S_y \ {y}, so f(w) ∈ T
        right
        show f w ∈ (T : Set Circle)
        rw [Finset.mem_coe]
        exact Finset.mem_image.mpr ⟨w, skel_finite.mem_toFinset.mpr h, rfl⟩
    · rintro (rfl | hz)
      · exact ⟨x, hx, rfl⟩
      · rw [Finset.mem_coe] at hz
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        have hw_skel : w ∈ S_y \ {y} := skel_finite.mem_toFinset.mp hw
        exact ⟨w, by rw [hS_x]; exact Set.mem_insert_of_mem x hw_skel, rfl⟩
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 9: Rewrite _hiso_y and _hiso_x to use insert form
  -- ════════════════════════════════════════════════════════════════════════════
  have hiso_y' : Nonempty (G.induce (insert (f y) ↑T) ≃g fractionGraph a1 q) := by
    rwa [← hSy_img_eq]
  have hiso_x' : Nonempty (G.induce (insert (f x) ↑T) ≃g fractionGraph a1 q) := by
    rwa [← hSx_img_eq]
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 10: Apply insertion_full_slot_analysis
  -- ════════════════════════════════════════════════════════════════════════════
  obtain ⟨t1, t2, ht1_mem, ht2_mem, ht1_ne_t2, harc, hx_disj, hfy_left, hfy_right⟩ :=
    insertion_full_slot_analysis G a1 q ha1_ge hq_ge hq_pos h2q hcoprime
      T hT_card (f y) (f x) hfy_notin_T hfx_notin_T hfxy hiso_y' hiso_x' hG_mono hG_ccw_trans
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 11: Find preimages s1, s2 ∈ S_y \ {y}
  -- ════════════════════════════════════════════════════════════════════════════
  obtain ⟨s1, hs1_finset, hfs1⟩ := Finset.mem_image.mp ht1_mem
  obtain ⟨s2, hs2_finset, hfs2⟩ := Finset.mem_image.mp ht2_mem
  have hs1_skel : s1 ∈ S_y \ {y} := skel_finite.mem_toFinset.mp hs1_finset
  have hs2_skel : s2 ∈ S_y \ {y} := skel_finite.mem_toFinset.mp hs2_finset
  have hs1_ne_s2 : s1 ≠ s2 := by
    intro h; exact ht1_ne_t2 (hfs1.symm.trans ((congr_arg f h).trans hfs2))
  -- ════════════════════════════════════════════════════════════════════════════
  -- STEP 12: Produce the conclusion
  -- ════════════════════════════════════════════════════════════════════════════
  -- Helper: for t ∈ S_y \ {y}, f(t) ∈ T
  have hft_mem_T : ∀ t, t ∈ S_y \ {y} → f t ∈ (T : Set Circle) :=
    fun t ht => Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨t, skel_finite.mem_toFinset.mpr ht, rfl⟩)
  -- Helper: for t ∈ S_y \ {y} with t ≠ s1, f(t) ≠ t1
  have hft_ne_t1 : ∀ t, t ∈ S_y \ {y} → t ≠ s1 → f t ≠ t1 :=
    fun t ht hne heq => hne (hf_injOn_Sy (Set.diff_subset ht)
      (Set.diff_subset hs1_skel) (heq.trans hfs1.symm))
  -- Helper: for t ∈ S_y \ {y} with t ≠ s2, f(t) ≠ t2
  have hft_ne_t2 : ∀ t, t ∈ S_y \ {y} → t ≠ s2 → f t ≠ t2 :=
    fun t ht hne heq => hne (hf_injOn_Sy (Set.diff_subset ht)
      (Set.diff_subset hs2_skel) (heq.trans hfs2.symm))
  refine ⟨s1, s2, hs1_skel, hs2_skel, hs1_ne_s2, ?_, ?_, ?_, ?_⟩
  -- Condition 1: Arc containment
  · rw [hfs1, hfs2]; exact harc
  -- Condition 2: x-disjunction
  · cases hx_disj with
    | inl h =>
      left; intro t ht hne ⟨hpos, hlt⟩
      exact h (f t) (hft_mem_T t ht) (hft_ne_t1 t ht hne)
        ⟨hfs1 ▸ hpos, hfs1 ▸ hlt⟩
    | inr h =>
      right; intro t ht hne ⟨hpos, hlt⟩
      exact h (f t) (hft_mem_T t ht) (hft_ne_t2 t ht hne)
        ⟨hfs2 ▸ hpos, hfs2 ▸ hlt⟩
  -- Condition 3: y-emptiness left (no skeleton image between f(s1) and f(y))
  · intro t ht hne ⟨hpos, hlt⟩
    exact hfy_left (f t) (hft_mem_T t ht) (hft_ne_t1 t ht hne)
      ⟨hfs1 ▸ hpos, hfs1 ▸ hlt⟩
  -- Condition 4: y-emptiness right (no skeleton image between f(y) and f(s2))
  · intro t ht hne ⟨hpos, hlt⟩
    exact hfy_right (f t) (hft_mem_T t ht) (hft_ne_t2 t ht hne)
      ⟨hpos, hfs2 ▸ hlt⟩

/-- Corollary: If f(y) and f(x) are in the same slot, and all gaps ≤ 1/a,
    then dist(f(y), f(x)) ≤ 2/a. -/
lemma dist_le_two_over_a_of_same_slot
    (a : ℕ) [NeZero a] (_ha_ge : 2 ≤ a)
    (S : Finset Circle) (_hcard : 2 ≤ S.card)
    (u v : Circle) (_hu : u ∈ S) (_hv : v ∈ S)
    (s1 s2 : Circle) (_hs1 : s1 ∈ S) (_hs2 : s2 ∈ S) (_hs1s2 : s1 ≠ s2)
    -- u and v are both in the arc from s1 to s2
    (hu_slot : repFrom s1 u + repFrom u s2 ≤ repFrom s1 s2)
    (hv_slot : repFrom s1 v + repFrom v s2 ≤ repFrom s1 s2)
    -- The arc from s1 to s2 has width ≤ 2/a (composed of at most 2 gaps)
    (harc_width : repFrom s1 s2 ≤ 2 / a) :
    dist u v ≤ 2 / a := by
  -- The distance from u to v is at most the arc width
  -- Since u and v are both in the arc [s1, s2], their distance ≤ arc width
  have hu_bound : repFrom s1 u ≤ repFrom s1 s2 := by linarith [hu_slot, repFrom_nonneg u s2]
  have hv_bound : repFrom s1 v ≤ repFrom s1 s2 := by linarith [hv_slot, repFrom_nonneg v s2]
  -- Case split on the relative positions of u and v within the arc
  by_cases h_order : repFrom s1 u ≤ repFrom s1 v
  · -- u is "before" v in the arc from s1
    -- So going from u to v within the arc, repFrom u v ≤ repFrom s1 s2
    have h_uv : repFrom u v ≤ repFrom s1 s2 := by
      -- In the arc, repFrom u v = repFrom s1 v - repFrom s1 u (monotonicity)
      -- Use that dist is bounded by arc length (arc-geometry argument)
      -- Key: repFrom s1 u + repFrom u v + repFrom v s2 = repFrom s1 s2 when no wrap
      -- From hv_slot: repFrom s1 v + repFrom v s2 ≤ repFrom s1 s2
      -- So repFrom s1 v ≤ repFrom s1 s2 - repFrom v s2
      -- And repFrom u v ≤ repFrom s1 v (since u is before v)
      -- So repFrom u v ≤ repFrom s1 s2
      calc repFrom u v ≤ repFrom s1 v := by
            -- u is between s1 and v in the arc (repFrom s1 u ≤ repFrom s1 v)
            -- So repFrom u v = repFrom s1 v - repFrom s1 u ≤ repFrom s1 v
            by_cases hu_eq_s1 : u = s1
            · -- u = s1: repFrom u v = repFrom s1 v ✓
              rw [hu_eq_s1]
            · by_cases hu_eq_v : u = v
              · -- u = v: repFrom u v = 0 ≤ repFrom s1 v ✓
                rw [hu_eq_v, repFrom_self]
                exact repFrom_nonneg s1 v
              · -- u ≠ s1, u ≠ v: use arc subtraction
                -- repFrom u v = repFrom s1 v - repFrom s1 u (since u is between s1 and v)
                -- Key: (v - u) = (v - s1) - (u - s1) in Circle
                -- Since repFrom s1 u ≤ repFrom s1 v < 1, subtraction doesn't wrap
                have hv_lt_one : repFrom s1 v < 1 := repFrom_lt_one s1 v
                have hu_nonneg' : 0 ≤ repFrom s1 u := repFrom_nonneg s1 u
                have h_diff_nonneg : 0 ≤ repFrom s1 v - repFrom s1 u := by linarith
                have h_diff_lt_one : repFrom s1 v - repFrom s1 u < 1 := by linarith
                -- (u - s1) has representative repFrom s1 u
                have h_us1 : (u - s1 : Circle) = (repFrom s1 u : Circle) := by
                  have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (u - s1)
                  rw [← h1]; rfl
                -- (v - s1) has representative repFrom s1 v
                have h_vs1 : (v - s1 : Circle) = (repFrom s1 v : Circle) := by
                  have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (v - s1)
                  rw [← h1]; rfl
                -- (v - u) = (v - s1) - (u - s1) = repFrom s1 v - repFrom s1 u in Circle
                have h_vu : (v - u : Circle) = ((repFrom s1 v - repFrom s1 u : ℝ) : Circle) := by
                  calc (v - u : Circle) = (v - s1) - (u - s1) := by abel
                    _ = (repFrom s1 v : Circle) - (repFrom s1 u : Circle) := by rw [h_vs1, h_us1]
                    _ = ((repFrom s1 v - repFrom s1 u : ℝ) : Circle) := by
                        rw [← QuotientAddGroup.mk_sub]
                -- Since repFrom s1 v - repFrom s1 u ∈ [0, 1), its representative is itself
                have h_mem : repFrom s1 v - repFrom s1 u ∈ Set.Ico (0 : ℝ) (0 + 1) := by
                  simp only [Set.mem_Ico, zero_add]
                  exact ⟨h_diff_nonneg, h_diff_lt_one⟩
                have h_eq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ))
                    (x := repFrom s1 v - repFrom s1 u) h_mem
                have h_rep : repFrom u v = repFrom s1 v - repFrom s1 u := by
                  simp only [repFrom, h_vu]
                  exact congrArg Subtype.val h_eq
                have hu_nonneg : 0 ≤ repFrom s1 u := repFrom_nonneg s1 u
                linarith
        _ ≤ repFrom s1 s2 := hv_bound
    calc dist u v ≤ repFrom u v := dist_le_repFrom u v
      _ ≤ repFrom s1 s2 := h_uv
      _ ≤ 2 / a := harc_width
  · -- v is "before" u in the arc
    push_neg at h_order
    have h_vu : repFrom v u ≤ repFrom s1 s2 := by
      calc repFrom v u ≤ repFrom s1 u := by
            -- v is between s1 and u in the arc (repFrom s1 v < repFrom s1 u)
            -- So repFrom v u = repFrom s1 u - repFrom s1 v ≤ repFrom s1 u
            by_cases hv_eq_s1 : v = s1
            · -- v = s1: repFrom v u = repFrom s1 u ✓
              rw [hv_eq_s1]
            · by_cases hv_eq_u : v = u
              · -- v = u: repFrom v u = 0 ≤ repFrom s1 u ✓
                rw [hv_eq_u, repFrom_self]
                exact repFrom_nonneg s1 u
              · -- v ≠ s1, v ≠ u: use arc subtraction
                have hu_lt_one : repFrom s1 u < 1 := repFrom_lt_one s1 u
                have hv_nonneg : 0 ≤ repFrom s1 v := repFrom_nonneg s1 v
                have h_diff_nonneg : 0 ≤ repFrom s1 u - repFrom s1 v := by linarith
                have h_diff_lt_one : repFrom s1 u - repFrom s1 v < 1 := by linarith
                have h_vs1 : (v - s1 : Circle) = (repFrom s1 v : Circle) := by
                  have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (v - s1)
                  rw [← h1]; rfl
                have h_us1 : (u - s1 : Circle) = (repFrom s1 u : Circle) := by
                  have h1 := (AddCircle.equivIco 1 0).symm_apply_apply (u - s1)
                  rw [← h1]; rfl
                have h_uv : (u - v : Circle) = ((repFrom s1 u - repFrom s1 v : ℝ) : Circle) := by
                  calc (u - v : Circle) = (u - s1) - (v - s1) := by abel
                    _ = (repFrom s1 u : Circle) - (repFrom s1 v : Circle) := by rw [h_us1, h_vs1]
                    _ = ((repFrom s1 u - repFrom s1 v : ℝ) : Circle) := by
                        rw [← QuotientAddGroup.mk_sub]
                have h_mem : repFrom s1 u - repFrom s1 v ∈ Set.Ico (0 : ℝ) (0 + 1) := by
                  simp only [Set.mem_Ico, zero_add]
                  exact ⟨h_diff_nonneg, h_diff_lt_one⟩
                have h_eq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ))
                    (x := repFrom s1 u - repFrom s1 v) h_mem
                have h_rep : repFrom v u = repFrom s1 u - repFrom s1 v := by
                  simp only [repFrom, h_uv]
                  exact congrArg Subtype.val h_eq
                have h_v_nonneg : 0 ≤ repFrom s1 v := repFrom_nonneg s1 v
                linarith
        _ ≤ repFrom s1 s2 := hu_bound
    calc dist u v = dist v u := dist_comm u v
      _ ≤ repFrom v u := dist_le_repFrom v u
      _ ≤ repFrom s1 s2 := h_vu
      _ ≤ 2 / a := harc_width

noncomputable def roundToZModShift (N : ℕ) [NeZero N] (y : Circle) : Circle → ZMod N :=
  fun x => roundToZMod N (x - y)


lemma circleGraphOpen_adj_stable_point
    (r : ℝ) (hr : 2 ≤ r) {x s : Circle}
    (hxs : x ≠ s) (hneq : circleDistance x s ≠ 1 / r) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ →
      ((circleGraphOpen r hr).Adj y s ↔ (circleGraphOpen r hr).Adj x s) := by
  classical
  have hdist_pos : 0 < circleDistance x s := by
    have hne : circleDistance x s ≠ 0 := by
      simpa [circleDistance_eq_zero_iff] using hxs
    exact lt_of_le_of_ne (circleDistance_nonneg _ _) (Ne.symm hne)
  by_cases hlt : circleDistance x s < 1 / r
  · -- Adjacent case: preserve strict inequality
    let ε : ℝ := (1 / r - circleDistance x s) / 2
    have hε_pos : 0 < ε := by
      have hpos : 0 < 1 / r - circleDistance x s := sub_pos.mpr hlt
      simpa [ε] using (half_pos hpos)
    let δ : ℝ := min (circleDistance x s / 2) ε
    have hδ_pos : 0 < δ := by
      have hpos1 : 0 < circleDistance x s / 2 := by nlinarith
      exact lt_min_iff.mpr ⟨hpos1, hε_pos⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro y hyx
    have hclose :
        |circleDistance y s - circleDistance x s| < ε := by
      have hle := circleDistance_lipschitz y x s
      have hlt' : circleDistance y x < ε := (lt_min_iff.mp hyx).2
      exact lt_of_le_of_lt (by simpa [abs_sub_comm] using hle) hlt'
    have hdist_lt : circleDistance y s < 1 / r := by
      have hclose' := (abs_lt.mp hclose).2
      have hbound : circleDistance x s + ε < 1 / r := by
        dsimp [ε]
        nlinarith [hlt]
      have hdist' : circleDistance y s < circleDistance x s + ε := by
        linarith
      exact lt_trans hdist' hbound
    have hy_ne : y ≠ s := by
      intro hys
      have hdist : circleDistance x s < circleDistance x s / 2 := by
        have hxy : circleDistance y x < circleDistance x s / 2 :=
          (lt_min_iff.mp hyx).1
        simpa [hys, circleDistance_comm] using hxy
      exact (by nlinarith [hdist])
    constructor
    · intro _
      exact ⟨hxs, hlt⟩
    · intro _
      exact ⟨hy_ne, hdist_lt⟩
  · -- Non-adjacent case: preserve strict inequality
    have hgt : 1 / r < circleDistance x s := lt_of_le_of_ne (le_of_not_gt hlt) hneq.symm
    let ε : ℝ := (circleDistance x s - 1 / r) / 2
    have hε_pos : 0 < ε := by
      have hpos : 0 < circleDistance x s - 1 / r := sub_pos.mpr hgt
      simpa [ε] using (half_pos hpos)
    let δ : ℝ := min (circleDistance x s / 2) ε
    have hδ_pos : 0 < δ := by
      have hpos1 : 0 < circleDistance x s / 2 := by nlinarith
      exact lt_min_iff.mpr ⟨hpos1, hε_pos⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro y hyx
    have hclose :
        |circleDistance y s - circleDistance x s| < ε := by
      have hle := circleDistance_lipschitz y x s
      have hlt' : circleDistance y x < ε := (lt_min_iff.mp hyx).2
      exact lt_of_le_of_lt (by simpa [abs_sub_comm] using hle) hlt'
    have hdist_gt : 1 / r < circleDistance y s := by
      have hclose' := (abs_lt.mp hclose).1
      have hbound : 1 / r < circleDistance x s - ε := by
        dsimp [ε]
        nlinarith [hgt]
      have hdist' : circleDistance x s - ε < circleDistance y s := by
        linarith
      exact lt_trans hbound hdist'
    have hy_ne : y ≠ s := by
      intro hys
      have hdist : circleDistance x s < circleDistance x s / 2 := by
        have hxy : circleDistance y x < circleDistance x s / 2 :=
          (lt_min_iff.mp hyx).1
        simpa [hys, circleDistance_comm] using hxy
      exact (by nlinarith [hdist])
    constructor
    · intro hadj
      obtain ⟨_, hdist⟩ := hadj
      exact (False.elim (lt_asymm hdist hdist_gt))
    · intro hadj
      obtain ⟨_, hdist⟩ := hadj
      exact (False.elim (lt_asymm hdist hgt))

lemma circleGraphClosed_adj_stable_point
    (r : ℝ) (hr : 2 ≤ r) {x s : Circle}
    (hxs : x ≠ s) (hneq : circleDistance x s ≠ 1 / r) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ →
      ((circleGraphClosed r hr).Adj y s ↔ (circleGraphClosed r hr).Adj x s) := by
  classical
  have hdist_pos : 0 < circleDistance x s := by
    have hne : circleDistance x s ≠ 0 := by
      simpa [circleDistance_eq_zero_iff] using hxs
    exact lt_of_le_of_ne (circleDistance_nonneg _ _) (Ne.symm hne)
  by_cases hlt : circleDistance x s < 1 / r
  · -- Adjacent case: preserve strict inequality
    let ε : ℝ := (1 / r - circleDistance x s) / 2
    have hε_pos : 0 < ε := by
      have hpos : 0 < 1 / r - circleDistance x s := sub_pos.mpr hlt
      simpa [ε] using (half_pos hpos)
    let δ : ℝ := min (circleDistance x s / 2) ε
    have hδ_pos : 0 < δ := by
      have hpos1 : 0 < circleDistance x s / 2 := by nlinarith
      exact lt_min_iff.mpr ⟨hpos1, hε_pos⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro y hyx
    have hclose :
        |circleDistance y s - circleDistance x s| < ε := by
      have hle := circleDistance_lipschitz y x s
      have hlt' : circleDistance y x < ε := (lt_min_iff.mp hyx).2
      exact lt_of_le_of_lt (by simpa [abs_sub_comm] using hle) hlt'
    have hdist_lt : circleDistance y s < 1 / r := by
      have hclose' := (abs_lt.mp hclose).2
      have hbound : circleDistance x s + ε < 1 / r := by
        dsimp [ε]
        nlinarith [hlt]
      have hdist' : circleDistance y s < circleDistance x s + ε := by
        linarith
      exact lt_trans hdist' hbound
    have hy_ne : y ≠ s := by
      intro hys
      have hdist : circleDistance x s < circleDistance x s / 2 := by
        have hxy : circleDistance y x < circleDistance x s / 2 :=
          (lt_min_iff.mp hyx).1
        simpa [hys, circleDistance_comm] using hxy
      exact (by nlinarith [hdist])
    constructor
    · intro _
      exact ⟨hxs, le_of_lt hlt⟩
    · intro _
      exact ⟨hy_ne, le_of_lt hdist_lt⟩
  · -- Non-adjacent case: preserve strict inequality
    have hgt : 1 / r < circleDistance x s := lt_of_le_of_ne (le_of_not_gt hlt) hneq.symm
    let ε : ℝ := (circleDistance x s - 1 / r) / 2
    have hε_pos : 0 < ε := by
      have hpos : 0 < circleDistance x s - 1 / r := sub_pos.mpr hgt
      simpa [ε] using (half_pos hpos)
    let δ : ℝ := min (circleDistance x s / 2) ε
    have hδ_pos : 0 < δ := by
      have hpos1 : 0 < circleDistance x s / 2 := by nlinarith
      exact lt_min_iff.mpr ⟨hpos1, hε_pos⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro y hyx
    have hclose :
        |circleDistance y s - circleDistance x s| < ε := by
      have hle := circleDistance_lipschitz y x s
      have hlt' : circleDistance y x < ε := (lt_min_iff.mp hyx).2
      exact lt_of_le_of_lt (by simpa [abs_sub_comm] using hle) hlt'
    have hdist_gt : 1 / r < circleDistance y s := by
      have hclose' := (abs_lt.mp hclose).1
      have hbound : 1 / r < circleDistance x s - ε := by
        dsimp [ε]
        nlinarith [hgt]
      have hdist' : circleDistance x s - ε < circleDistance y s := by
        linarith
      exact lt_trans hbound hdist'
    have hy_ne : y ≠ s := by
      intro hys
      have hdist : circleDistance x s < circleDistance x s / 2 := by
        have hxy : circleDistance y x < circleDistance x s / 2 :=
          (lt_min_iff.mp hyx).1
        simpa [hys, circleDistance_comm] using hxy
      exact (by nlinarith [hdist])
    constructor
    · intro hadj
      obtain ⟨_, hdist⟩ := hadj
      have : (1 / r) < (1 / r) := lt_of_lt_of_le hdist_gt hdist
      exact (False.elim (lt_irrefl _ this))
    · intro hadj
      obtain ⟨_, hdist⟩ := hadj
      have : (1 / r) < (1 / r) := lt_of_lt_of_le hgt hdist
      exact (False.elim (lt_irrefl _ this))

lemma circleGraphOpen_adj_stable_finset
    (r : ℝ) (hr : 2 ≤ r) (x : Circle) (S : Finset Circle)
    (hS : ∀ s ∈ S, s ≠ x ∧ circleDistance x s ≠ 1 / r) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ →
      ∀ s ∈ S, ((circleGraphOpen r hr).Adj y s ↔ (circleGraphOpen r hr).Adj x s) := by
  classical
  revert hS
  refine Finset.induction_on S ?base ?step
  · intro _hS
    refine ⟨1, by norm_num, ?_⟩
    intro y hy
    simp
  · intro s S hsS ih hS'
    have hs : s ≠ x ∧ circleDistance x s ≠ 1 / r := by
      have hs' : s ∈ (insert s S) := by simp
      exact hS' s hs'
    rcases circleGraphOpen_adj_stable_point r hr (x := x) (s := s) hs.1.symm hs.2 with
      ⟨δ1, hδ1_pos, hδ1⟩
    have hS'' : ∀ t ∈ S, t ≠ x ∧ circleDistance x t ≠ 1 / r := by
      intro t ht
      have ht' : t ∈ insert s S := by simpa [ht, hsS] using ht
      exact hS' t ht'
    rcases ih hS'' with ⟨δ2, hδ2_pos, hδ2⟩
    refine ⟨min δ1 δ2, lt_min_iff.mpr ⟨hδ1_pos, hδ2_pos⟩, ?_⟩
    intro y hy
    have hy1 : circleDistance y x < δ1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : circleDistance y x < δ2 := lt_of_lt_of_le hy (min_le_right _ _)
    intro t ht
    by_cases hts : t = s
    · subst hts
      simpa using hδ1 y hy1
    · have htS : t ∈ S := by
        simpa [Finset.mem_insert, hts] using ht
      exact hδ2 y hy2 t htS

lemma circleGraphClosed_adj_stable_finset
    (r : ℝ) (hr : 2 ≤ r) (x : Circle) (S : Finset Circle)
    (hS : ∀ s ∈ S, s ≠ x ∧ circleDistance x s ≠ 1 / r) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ →
      ∀ s ∈ S, ((circleGraphClosed r hr).Adj y s ↔ (circleGraphClosed r hr).Adj x s) := by
  classical
  revert hS
  refine Finset.induction_on S ?base ?step
  · intro _hS
    refine ⟨1, by norm_num, ?_⟩
    intro y hy
    simp
  · intro s S hsS ih hS'
    have hs : s ≠ x ∧ circleDistance x s ≠ 1 / r := by
      have hs' : s ∈ (insert s S) := by simp
      exact hS' s hs'
    rcases circleGraphClosed_adj_stable_point r hr (x := x) (s := s) hs.1.symm hs.2 with
      ⟨δ1, hδ1_pos, hδ1⟩
    have hS'' : ∀ t ∈ S, t ≠ x ∧ circleDistance x t ≠ 1 / r := by
      intro t ht
      have ht' : t ∈ insert s S := by simpa [ht, hsS] using ht
      exact hS' t ht'
    rcases ih hS'' with ⟨δ2, hδ2_pos, hδ2⟩
    refine ⟨min δ1 δ2, lt_min_iff.mpr ⟨hδ1_pos, hδ2_pos⟩, ?_⟩
    intro y hy
    have hy1 : circleDistance y x < δ1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : circleDistance y x < δ2 := lt_of_lt_of_le hy (min_le_right _ _)
    intro t ht
    by_cases hts : t = s
    · subst hts
      simpa using hδ1 y hy1
    · have htS : t ∈ S := by
        simpa [Finset.mem_insert, hts] using ht
      exact hδ2 y hy2 t htS

lemma circleGraphOpen_adj_stable_finite
    (r : ℝ) (hr : 2 ≤ r) (x : Circle) (S : Set Circle) (hSfin : S.Finite)
    (hS : ∀ s ∈ S, s ≠ x ∧ circleDistance x s ≠ 1 / r) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ →
      ∀ s ∈ S, ((circleGraphOpen r hr).Adj y s ↔ (circleGraphOpen r hr).Adj x s) := by
  classical
  let Sf : Finset Circle := hSfin.toFinset
  have hS' : ∀ s ∈ Sf, s ≠ x ∧ circleDistance x s ≠ 1 / r := by
    intro s hs
    exact hS s (by simpa [Sf] using hs)
  rcases circleGraphOpen_adj_stable_finset r hr x Sf hS' with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy s hs
  exact hδ y hy s (by simpa [Sf] using (hSfin.mem_toFinset.mpr hs))

lemma circleGraphClosed_adj_stable_finite
    (r : ℝ) (hr : 2 ≤ r) (x : Circle) (S : Set Circle) (hSfin : S.Finite)
    (hS : ∀ s ∈ S, s ≠ x ∧ circleDistance x s ≠ 1 / r) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ →
      ∀ s ∈ S, ((circleGraphClosed r hr).Adj y s ↔ (circleGraphClosed r hr).Adj x s) := by
  classical
  let Sf : Finset Circle := hSfin.toFinset
  have hS' : ∀ s ∈ Sf, s ≠ x ∧ circleDistance x s ≠ 1 / r := by
    intro s hs
    exact hS s (by simpa [Sf] using hs)
  rcases circleGraphClosed_adj_stable_finset r hr x Sf hS' with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy s hs
  exact hδ y hy s (by simpa [Sf] using (hSfin.mem_toFinset.mpr hs))

noncomputable def circleGraphOpen_induce_swap_iso
    (r : ℝ) (hr : 2 ≤ r) (x y : Circle) (S : Set Circle)
    (hx : x ∈ S) (hy : y ∉ S)
    (hstable : ∀ s ∈ S, s ≠ x →
      ((circleGraphOpen r hr).Adj y s ↔ (circleGraphOpen r hr).Adj x s)) :
    (circleGraphOpen r hr).induce S ≃g
      (circleGraphOpen r hr).induce (insert y (S \ {x})) := by
  classical
  let e : Circle ≃ Circle := Equiv.swap x y
  have hmem : ∀ u, u ∈ S ↔ e u ∈ insert y (S \ {x}) := by
    intro u
    by_cases hux : u = x
    · constructor
      · intro _huS
        simpa [e, hux] using (Or.inl rfl : (y : Circle) = y ∨ y ∈ S \ {x})
      · intro _huS
        simpa [hux] using hx
    by_cases huy : u = y
    · have huS : u ∉ S := by simpa [huy] using hy
      constructor
      · intro huS'
        exact (huS huS').elim
      · intro huS'
        have : x ∈ insert y (S \ {x}) := by simpa [e, huy] using huS'
        rcases this with h | h
        · exact (huS (by simpa [huy, h] using hx)).elim
        · exact (h.2 rfl).elim
    · have hux' : u ≠ x := hux
      have huy' : u ≠ y := huy
      constructor
      · intro huS
        have eu : e u = u := Equiv.swap_apply_of_ne_of_ne hux' huy'
        have : u ∈ insert y (S \ {x}) := Or.inr ⟨huS, hux'⟩
        simpa [eu] using this
      · intro huS'
        have eu : e u = u := Equiv.swap_apply_of_ne_of_ne hux' huy'
        have : u ∈ insert y (S \ {x}) := by simpa [eu] using huS'
        rcases this with h | h
        · exact (huy' h).elim
        · exact h.1
  refine
    { toEquiv := e.subtypeEquiv hmem
      map_rel_iff' := ?_ }
  intro u v
  change (circleGraphOpen r hr).Adj ((e u) : Circle) (e v : Circle) ↔
    (circleGraphOpen r hr).Adj (u : Circle) (v : Circle)
  by_cases hux : (u : Circle) = x
  · by_cases hvx : (v : Circle) = x
    · simp [hux, hvx, circleGraphOpen, e]
    · have hvy : (v : Circle) ≠ y := by
        intro hvy
        have : (v : Circle) ∈ S := v.property
        exact hy (by simpa [hvy] using this)
      have hstable' := hstable v v.property hvx
      have ev : e (v : Circle) = v := Equiv.swap_apply_of_ne_of_ne hvx hvy
      simpa [e, hux, ev] using hstable'
  · have hux' : (u : Circle) ≠ x := hux
    have huy : (u : Circle) ≠ y := by
      intro huy
      have : (u : Circle) ∈ S := u.property
      exact hy (by simpa [huy] using this)
    by_cases hvx : (v : Circle) = x
    · have huv : (u : Circle) ≠ x := hux'
      have hstable' := hstable u u.property huv
      have eu : e (u : Circle) = u := Equiv.swap_apply_of_ne_of_ne hux' huy
      have hstable'' :
          (circleGraphOpen r hr).Adj u y ↔ (circleGraphOpen r hr).Adj u x := by
        simpa [circleGraphOpen, circleDistance_comm, eq_comm] using hstable'
      simpa [e, eu, hvx] using hstable''
    · have hvy : (v : Circle) ≠ y := by
        intro hvy
        have : (v : Circle) ∈ S := v.property
        exact hy (by simpa [hvy] using this)
      have eu : e (u : Circle) = u := Equiv.swap_apply_of_ne_of_ne hux' huy
      have ev : e (v : Circle) = v := Equiv.swap_apply_of_ne_of_ne hvx hvy
      simp [e, eu, ev, circleGraphOpen]

noncomputable def circleGraphClosed_induce_swap_iso
    (r : ℝ) (hr : 2 ≤ r) (x y : Circle) (S : Set Circle)
    (hx : x ∈ S) (hy : y ∉ S)
    (hstable : ∀ s ∈ S, s ≠ x →
      ((circleGraphClosed r hr).Adj y s ↔ (circleGraphClosed r hr).Adj x s)) :
    (circleGraphClosed r hr).induce S ≃g
      (circleGraphClosed r hr).induce (insert y (S \ {x})) := by
  classical
  let e : Circle ≃ Circle := Equiv.swap x y
  have hmem : ∀ u, u ∈ S ↔ e u ∈ insert y (S \ {x}) := by
    intro u
    by_cases hux : u = x
    · constructor
      · intro _huS
        simpa [e, hux] using (Or.inl rfl : (y : Circle) = y ∨ y ∈ S \ {x})
      · intro _huS
        simpa [hux] using hx
    by_cases huy : u = y
    · have huS : u ∉ S := by simpa [huy] using hy
      constructor
      · intro huS'
        exact (huS huS').elim
      · intro huS'
        have : x ∈ insert y (S \ {x}) := by simpa [e, huy] using huS'
        rcases this with h | h
        · exact (huS (by simpa [huy, h] using hx)).elim
        · exact (h.2 rfl).elim
    · have hux' : u ≠ x := hux
      have huy' : u ≠ y := huy
      constructor
      · intro huS
        have eu : e u = u := Equiv.swap_apply_of_ne_of_ne hux' huy'
        have : u ∈ insert y (S \ {x}) := Or.inr ⟨huS, hux'⟩
        simpa [eu] using this
      · intro huS'
        have eu : e u = u := Equiv.swap_apply_of_ne_of_ne hux' huy'
        have : u ∈ insert y (S \ {x}) := by simpa [eu] using huS'
        rcases this with h | h
        · exact (huy' h).elim
        · exact h.1
  refine
    { toEquiv := e.subtypeEquiv hmem
      map_rel_iff' := ?_ }
  intro u v
  change (circleGraphClosed r hr).Adj ((e u) : Circle) (e v : Circle) ↔
    (circleGraphClosed r hr).Adj (u : Circle) (v : Circle)
  by_cases hux : (u : Circle) = x
  · by_cases hvx : (v : Circle) = x
    · simp [hux, hvx, circleGraphClosed, e]
    · have hvy : (v : Circle) ≠ y := by
        intro hvy
        have : (v : Circle) ∈ S := v.property
        exact hy (by simpa [hvy] using this)
      have hstable' := hstable v v.property hvx
      have ev : e (v : Circle) = v := Equiv.swap_apply_of_ne_of_ne hvx hvy
      simpa [e, hux, ev] using hstable'
  · have hux' : (u : Circle) ≠ x := hux
    have huy : (u : Circle) ≠ y := by
      intro huy
      have : (u : Circle) ∈ S := u.property
      exact hy (by simpa [huy] using this)
    by_cases hvx : (v : Circle) = x
    · have huv : (u : Circle) ≠ x := hux'
      have hstable' := hstable u u.property huv
      have eu : e (u : Circle) = u := Equiv.swap_apply_of_ne_of_ne hux' huy
      have hstable'' :
          (circleGraphClosed r hr).Adj u y ↔ (circleGraphClosed r hr).Adj u x := by
        simpa [circleGraphClosed, circleDistance_comm, eq_comm] using hstable'
      simpa [e, eu, hvx] using hstable''
    · have hvy : (v : Circle) ≠ y := by
        intro hvy
        have : (v : Circle) ∈ S := v.property
        exact hy (by simpa [hvy] using this)
      have eu : e (u : Circle) = u := Equiv.swap_apply_of_ne_of_ne hux' huy
      have ev : e (v : Circle) = v := Equiv.swap_apply_of_ne_of_ne hvx hvy
      simp [e, eu, ev, circleGraphClosed]

lemma equidistantPointsShift_dist_ne_one_div
    (r : ℝ) (hirr : Irrational r) (N : ℕ) [NeZero N] (x : Circle)
    {s : Circle} (hs : s ∈ equidistantPointsShift N x) :
    circleDistance x s ≠ 1 / r := by
  rcases hs with ⟨t, ht, rfl⟩
  rcases ht with ⟨k, rfl⟩
  simpa using (circleDistance_equidistant_shift_ne_one_div r hirr N x k)

lemma circleGraphOpen_adj_stable_equidistant_shift
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (x : Circle) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ →
      ∀ s ∈ equidistantPointsShift N x, s ≠ x →
        ((circleGraphOpen r hr).Adj y s ↔ (circleGraphOpen r hr).Adj x s) := by
  classical
  let S : Set Circle := equidistantPointsShift N x \ ({x} : Set Circle)
  have hSfin : S.Finite :=
    (equidistantPointsShift_finite N x).subset (by
      intro s hs
      have : s ∈ equidistantPointsShift N x ∧ s ∉ Set.singleton x := by
        simpa [S, Set.mem_diff] using hs
      exact this.1)
  have hS :
      ∀ s ∈ S, s ≠ x ∧ circleDistance x s ≠ 1 / r := by
    intro s hs
    have hs' : s ∈ equidistantPointsShift N x := by
      have : s ∈ equidistantPointsShift N x ∧ s ∉ Set.singleton x := by
        simpa [S, Set.mem_diff] using hs
      exact this.1
    have hsne : s ≠ x := by
      have hsnot : s ∉ Set.singleton x := by
        have : s ∈ equidistantPointsShift N x ∧ s ∉ Set.singleton x := by
          simpa [S, Set.mem_diff] using hs
        exact this.2
      simpa [Set.mem_singleton_iff] using hsnot
    exact ⟨hsne, equidistantPointsShift_dist_ne_one_div r hirr N x hs'⟩
  rcases circleGraphOpen_adj_stable_finite r hr x S hSfin hS with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy s hs hsne
  have hs' : s ∈ S := by
    have : s ∈ equidistantPointsShift N x ∧ s ∉ Set.singleton x := by
      refine ⟨hs, ?_⟩
      simpa [Set.mem_singleton_iff] using hsne
    simpa [S, Set.mem_diff] using this
  exact hδ y hy s hs'

lemma circleGraphClosed_adj_stable_equidistant_shift
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (x : Circle) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ →
      ∀ s ∈ equidistantPointsShift N x, s ≠ x →
        ((circleGraphClosed r hr).Adj y s ↔ (circleGraphClosed r hr).Adj x s) := by
  classical
  let S : Set Circle := equidistantPointsShift N x \ ({x} : Set Circle)
  have hSfin : S.Finite :=
    (equidistantPointsShift_finite N x).subset (by
      intro s hs
      have : s ∈ equidistantPointsShift N x ∧ s ∉ Set.singleton x := by
        simpa [S, Set.mem_diff] using hs
      exact this.1)
  have hS :
      ∀ s ∈ S, s ≠ x ∧ circleDistance x s ≠ 1 / r := by
    intro s hs
    have hs' : s ∈ equidistantPointsShift N x := by
      have : s ∈ equidistantPointsShift N x ∧ s ∉ Set.singleton x := by
        simpa [S, Set.mem_diff] using hs
      exact this.1
    have hsne : s ≠ x := by
      have hsnot : s ∉ Set.singleton x := by
        have : s ∈ equidistantPointsShift N x ∧ s ∉ Set.singleton x := by
          simpa [S, Set.mem_diff] using hs
        exact this.2
      simpa [Set.mem_singleton_iff] using hsnot
    exact ⟨hsne, equidistantPointsShift_dist_ne_one_div r hirr N x hs'⟩
  rcases circleGraphClosed_adj_stable_finite r hr x S hSfin hS with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy s hs hsne
  have hs' : s ∈ S := by
    have : s ∈ equidistantPointsShift N x ∧ s ∉ Set.singleton x := by
      refine ⟨hs, ?_⟩
      simpa [Set.mem_singleton_iff] using hsne
    simpa [S, Set.mem_diff] using this
  exact hδ y hy s hs'

lemma distMod_pos_of_ne (N : ℕ) [NeZero N] {k l : ZMod N} (hkl : k ≠ l) :
    0 < distMod N k l := by
  classical
  by_contra h
  have h0 : distMod N k l = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
  simp only [distMod] at h0
  rcases Nat.min_eq_zero_iff.mp h0 with hval | hval
  · have hval0 : (k - l).val = 0 := hval
    have hkl' : k - l = 0 := (ZMod.val_eq_zero _).mp hval0
    exact hkl (sub_eq_zero.mp hkl')
  · have hval0 : N - (k - l).val = 0 := hval
    have hle : N ≤ (k - l).val := (Nat.sub_eq_zero_iff_le.mp hval0)
    have hlt := (k - l).val_lt
    exact (lt_irrefl _ (lt_of_lt_of_le hlt hle))

lemma circleDistance_equidistant_shift_ge_one_div (N : ℕ) [NeZero N]
    (y : Circle) (k l : ZMod N) (hkl : k ≠ l) :
    (1 : ℝ) / N ≤ circleDistance (y + embedZMod N k) (y + embedZMod N l) := by
  have hpos : 0 < distMod N k l := distMod_pos_of_ne N hkl
  have hge : (1 : ℝ) ≤ distMod N k l := by
    exact_mod_cast (Nat.succ_le_iff.mp hpos)
  have hdist :
      circleDistance (y + embedZMod N k) (y + embedZMod N l) =
        (distMod N k l : ℝ) / (N : ℝ) := by
    simpa [circleDistance, dist_add_left] using
      (circleDistance_equidistant_shift_rat' (N := N) (y := y) (k := k) (l := l))
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hdiv : (1 : ℝ) / N ≤ (distMod N k l : ℝ) / N := by
    exact (div_le_div_of_nonneg_right hge (le_of_lt hN_pos))
  simpa [hdist] using hdiv

lemma circleGraphOpen_induce_swap_iso_equidistant_shift
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (x : Circle) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ → y ≠ x →
      Nonempty
        ((circleGraphOpen r hr).induce (equidistantPointsShift N x) ≃g
          (circleGraphOpen r hr).induce
            (insert y (equidistantPointsShift N x \ ({x} : Set Circle)))) := by
  classical
  let S : Set Circle := equidistantPointsShift N x
  rcases circleGraphOpen_adj_stable_equidistant_shift r hr hirr N x with ⟨δ0, hδ0_pos, hδ0⟩
  have hN_pos : 0 < (1 : ℝ) / N := by
    have hN_pos' : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    exact one_div_pos.mpr hN_pos'
  refine ⟨min δ0 ((1 : ℝ) / N), lt_min_iff.mpr ⟨hδ0_pos, hN_pos⟩, ?_⟩
  intro y hy hyne
  have hy0 : circleDistance y x < δ0 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy1 : circleDistance y x < (1 : ℝ) / N := lt_of_lt_of_le hy (min_le_right _ _)
  have hyS : y ∉ S := by
    intro hyS
    rcases hyS with ⟨t, ht, rfl⟩
    rcases ht with ⟨k, rfl⟩
    have hkne : (k : ZMod N) ≠ 0 := by
      intro hk
      apply hyne
      simpa [hk, embedZMod_zero]
    have hdist_ge :
        (1 : ℝ) / N ≤ circleDistance x (x + embedZMod N k) := by
      have hdist :=
        circleDistance_equidistant_shift_ge_one_div (N := N) (y := x) (k := 0) (l := k) (by
          simpa [eq_comm] using hkne)
      simpa [embedZMod_zero] using hdist
    have hdist_ge' : (1 : ℝ) / N ≤ circleDistance (x + embedZMod N k) x := by
      simpa [circleDistance_comm] using hdist_ge
    exact (not_lt_of_ge hdist_ge') hy1
  have hxS : x ∈ S := mem_equidistantPointsShift N x
  have hstable :
      ∀ s ∈ S, s ≠ x →
        ((circleGraphOpen r hr).Adj y s ↔ (circleGraphOpen r hr).Adj x s) := by
    intro s hs hsne
    exact hδ0 y hy0 s hs hsne
  exact ⟨by
    simpa [S] using
      (circleGraphOpen_induce_swap_iso r hr x y S hxS hyS hstable)⟩

lemma circleGraphClosed_induce_swap_iso_equidistant_shift
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (x : Circle) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ → y ≠ x →
      Nonempty
        ((circleGraphClosed r hr).induce (equidistantPointsShift N x) ≃g
          (circleGraphClosed r hr).induce
            (insert y (equidistantPointsShift N x \ ({x} : Set Circle)))) := by
  classical
  let S : Set Circle := equidistantPointsShift N x
  rcases circleGraphClosed_adj_stable_equidistant_shift r hr hirr N x with ⟨δ0, hδ0_pos, hδ0⟩
  have hN_pos : 0 < (1 : ℝ) / N := by
    have hN_pos' : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    exact one_div_pos.mpr hN_pos'
  refine ⟨min δ0 ((1 : ℝ) / N), lt_min_iff.mpr ⟨hδ0_pos, hN_pos⟩, ?_⟩
  intro y hy hyne
  have hy0 : circleDistance y x < δ0 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy1 : circleDistance y x < (1 : ℝ) / N := lt_of_lt_of_le hy (min_le_right _ _)
  have hyS : y ∉ S := by
    intro hyS
    rcases hyS with ⟨t, ht, rfl⟩
    rcases ht with ⟨k, rfl⟩
    have hkne : (k : ZMod N) ≠ 0 := by
      intro hk
      apply hyne
      simpa [hk, embedZMod_zero]
    have hdist_ge :
        (1 : ℝ) / N ≤ circleDistance x (x + embedZMod N k) := by
      have hdist :=
        circleDistance_equidistant_shift_ge_one_div (N := N) (y := x) (k := 0) (l := k) (by
          simpa [eq_comm] using hkne)
      simpa [embedZMod_zero] using hdist
    have hdist_ge' : (1 : ℝ) / N ≤ circleDistance (x + embedZMod N k) x := by
      simpa [circleDistance_comm] using hdist_ge
    exact (not_lt_of_ge hdist_ge') hy1
  have hxS : x ∈ S := mem_equidistantPointsShift N x
  have hstable :
      ∀ s ∈ S, s ≠ x →
        ((circleGraphClosed r hr).Adj y s ↔ (circleGraphClosed r hr).Adj x s) := by
    intro s hs hsne
    exact hδ0 y hy0 s hs hsne
  exact ⟨by
    simpa [S] using
      (circleGraphClosed_induce_swap_iso r hr x y S hxS hyS hstable)⟩

lemma circleGraphOpen_adj_iff_closed_equidistant
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (y : Circle)
    {u v : Circle}
    (hu : u ∈ equidistantPointsShift N y)
    (hv : v ∈ equidistantPointsShift N y) :
    (circleGraphOpen r hr).Adj u v ↔ (circleGraphClosed r hr).Adj u v := by
  rcases hu with ⟨xu, hxu, rfl⟩
  rcases hv with ⟨xv, hxv, rfl⟩
  rcases hxu with ⟨k, rfl⟩
  rcases hxv with ⟨l, rfl⟩
  have hneq : circleDistance (y + embedZMod N k) (y + embedZMod N l) ≠ 1 / r :=
    circleDistance_equidistant_shift_ne_one_div' r hirr N y k l
  constructor
  · rintro ⟨hne, hdist⟩
    exact ⟨hne, le_of_lt hdist⟩
  · rintro ⟨hne, hdist⟩
    have hlt : circleDistance (y + embedZMod N k) (y + embedZMod N l) < 1 / r := by
      exact lt_of_le_of_ne hdist (by simpa [eq_comm] using hneq)
    exact ⟨hne, hlt⟩

lemma circleGraphOpen_induce_eq_closed_equidistant
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (y : Circle) :
    (circleGraphOpen r hr).induce (equidistantPointsShift N y) =
      (circleGraphClosed r hr).induce (equidistantPointsShift N y) := by
  ext u v
  change (circleGraphOpen r hr).Adj (u : Circle) (v : Circle) ↔
    (circleGraphClosed r hr).Adj (u : Circle) (v : Circle)
  exact circleGraphOpen_adj_iff_closed_equidistant r hr hirr N y u.property v.property

noncomputable def circleGraphClosed_induce_shift_iso
    (r : ℝ) (hr : 2 ≤ r) (N : ℕ) [NeZero N] (y : Circle) :
    (circleGraphClosed r hr).induce (equidistantPointsShift N y) ≃g
      (circleGraphClosed r hr).induce (equidistantPoints N) := by
  classical
  refine
    { toEquiv :=
        { toFun := fun x => ⟨-y + x, ?_⟩
          invFun := fun x => ⟨y + x, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      map_rel_iff' := ?_ }
  · rcases x.property with ⟨t, ht, htx⟩
    have hx : (-y + (x : Circle)) = t := by
      calc
        -y + (x : Circle) = -y + (y + t) := by simpa [htx]
        _ = t := by simpa using (neg_add_cancel_left y t)
    simpa [hx] using ht
  · change y + (x : Circle) ∈ equidistantPointsShift N y
    exact ⟨x, x.property, rfl⟩
  · intro x
    ext
    simp
  · intro x
    ext
    simp
  · intro a b
    simpa [SimpleGraph.induce_adj] using
      (circleGraphClosed_adj_add_left r hr (-y) (a : Circle) (b : Circle))

noncomputable def circleGraphOpen_induce_shift_iso
    (r : ℝ) (hr : 2 ≤ r) (N : ℕ) [NeZero N] (y : Circle) :
    (circleGraphOpen r hr).induce (equidistantPointsShift N y) ≃g
      (circleGraphOpen r hr).induce (equidistantPoints N) := by
  classical
  refine
    { toEquiv :=
        { toFun := fun x => ⟨-y + x, ?_⟩
          invFun := fun x => ⟨y + x, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      map_rel_iff' := ?_ }
  · rcases x.property with ⟨t, ht, htx⟩
    have hx : (-y + (x : Circle)) = t := by
      calc
        -y + (x : Circle) = -y + (y + t) := by simpa [htx]
        _ = t := by simpa using (neg_add_cancel_left y t)
    simpa [hx] using ht
  · change y + (x : Circle) ∈ equidistantPointsShift N y
    exact ⟨x, x.property, rfl⟩
  · intro x
    ext
    simp
  · intro x
    ext
    simp
  · intro a b
    simpa [SimpleGraph.induce_adj] using
      (circleGraphOpen_adj_add_left r hr (-y) (a : Circle) (b : Circle))

noncomputable def circleGraph_equidistant_shift_induced_closed
    (r : ℝ) (hr : 2 ≤ r) (N : ℕ) [NeZero N] (hN : 2 ≤ N) (y : Circle) :
    ∃ (q : ℕ), 0 < q ∧
      ∃ (_iso : (circleGraphClosed r hr).induce (equidistantPointsShift N y) ≃g
        fractionGraph N q), True := by
  let q := Nat.floor ((N : ℝ) / r) + 1
  have hq_pos : 0 < q := Nat.succ_pos _
  rcases circleGraph_equidistant_induced_closed r hr N hN with ⟨iso, htriv⟩
  refine ⟨q, hq_pos, ?_⟩
  refine ⟨?_, htriv⟩
  have iso_shift := (circleGraphClosed_induce_shift_iso r hr N y).trans iso
  simpa [q] using iso_shift

noncomputable def circleGraph_equidistant_shift_induced_open
    (r : ℝ) (hr : 2 ≤ r) (N : ℕ) [NeZero N] (hN : 2 ≤ N) (y : Circle) :
    ∃ (q : ℕ), 0 < q ∧
      ∃ (_iso : (circleGraphOpen r hr).induce (equidistantPointsShift N y) ≃g
        fractionGraph N q), True := by
  let q := Nat.ceil ((N : ℝ) / r)
  have hq_pos : 0 < q := by
    rw [Nat.ceil_pos]
    positivity
  rcases circleGraph_equidistant_induced_open r hr N hN with ⟨iso, htriv⟩
  refine ⟨q, hq_pos, ?_⟩
  refine ⟨?_, htriv⟩
  have iso_shift := (circleGraphOpen_induce_shift_iso r hr N y).trans iso
  simpa [q] using iso_shift

lemma circleGraphOpen_induce_swap_iso_equidistant_shift_fractionGraph
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (x : Circle) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ → y ≠ x →
      ∃ q : ℕ, 0 < q ∧
        Nonempty
          ((circleGraphOpen r hr).induce
              (insert y (equidistantPointsShift N x \ ({x} : Set Circle))) ≃g
            fractionGraph N q) := by
  classical
  rcases circleGraph_equidistant_shift_induced_open r hr N hN x with ⟨q, hq_pos, hIso, _⟩
  rcases circleGraphOpen_induce_swap_iso_equidistant_shift r hr hirr N x with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy hyne
  rcases hδ y hy hyne with ⟨iso_swap⟩
  refine ⟨q, hq_pos, ?_⟩
  exact ⟨iso_swap.symm.trans hIso⟩

/-- Variant that exposes q = Nat.ceil(N/r) explicitly. -/
lemma circleGraphOpen_induce_swap_iso_q_eq_ceil
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (x : Circle) :
    let q := Nat.ceil ((N : ℝ) / r)
    ∃ δ > 0, ∀ y, circleDistance y x < δ → y ≠ x →
      0 < q ∧
      Nonempty
        ((circleGraphOpen r hr).induce
            (insert y (equidistantPointsShift N x \ ({x} : Set Circle))) ≃g
          fractionGraph N q) := by
  classical
  set q := Nat.ceil ((N : ℝ) / r)
  have hq_pos : 0 < q := by rw [Nat.ceil_pos]; positivity
  rcases circleGraph_equidistant_induced_open r hr N hN with ⟨iso, _⟩
  rcases circleGraphOpen_induce_swap_iso_equidistant_shift r hr hirr N x with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy hyne
  rcases hδ y hy hyne with ⟨iso_swap⟩
  refine ⟨hq_pos, ?_⟩
  have iso_shift := (circleGraphOpen_induce_shift_iso r hr N x).trans iso
  exact ⟨iso_swap.symm.trans iso_shift⟩

/-- Variant that exposes q = Nat.floor(N/r) + 1 explicitly for closed case. -/
lemma circleGraphClosed_induce_swap_iso_q_eq_floor_succ
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (x : Circle) :
    let q := Nat.floor ((N : ℝ) / r) + 1
    ∃ δ > 0, ∀ y, circleDistance y x < δ → y ≠ x →
      0 < q ∧
      Nonempty
        ((circleGraphClosed r hr).induce
            (insert y (equidistantPointsShift N x \ ({x} : Set Circle))) ≃g
          fractionGraph N q) := by
  classical
  set q := Nat.floor ((N : ℝ) / r) + 1
  have hq_pos : 0 < q := Nat.succ_pos _
  rcases circleGraph_equidistant_induced_closed r hr N hN with ⟨iso, _⟩
  rcases circleGraphClosed_induce_swap_iso_equidistant_shift r hr hirr N x with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy hyne
  rcases hδ y hy hyne with ⟨iso_swap⟩
  refine ⟨hq_pos, ?_⟩
  have iso_shift := (circleGraphClosed_induce_shift_iso r hr N x).trans iso
  exact ⟨iso_swap.symm.trans iso_shift⟩

lemma circleGraphClosed_induce_swap_iso_equidistant_shift_fractionGraph
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (x : Circle) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ → y ≠ x →
      ∃ q : ℕ, 0 < q ∧
        Nonempty
          ((circleGraphClosed r hr).induce
              (insert y (equidistantPointsShift N x \ ({x} : Set Circle))) ≃g
            fractionGraph N q) := by
  classical
  rcases circleGraph_equidistant_shift_induced_closed r hr N hN x with ⟨q, hq_pos, hIso, _⟩
  rcases circleGraphClosed_induce_swap_iso_equidistant_shift r hr hirr N x with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy hyne
  rcases hδ y hy hyne with ⟨iso_swap⟩
  refine ⟨q, hq_pos, ?_⟩
  exact ⟨iso_swap.symm.trans hIso⟩

lemma ceil_convergent_even_eq_den (r : ℝ) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent (2 * n) : ℝ)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (r.convergent (2 * n) : ℝ) = (a : ℝ) / b ∧
      Nat.ceil ((a : ℝ) / r) = b := by
  -- Use integer numerators/denominators of the convergents.
  rcases nums_int_of_irrational r hirr (2 * n) with ⟨A, hA⟩
  rcases dens_int_pos_of_irrational r hirr (2 * n) with ⟨B, hB, hBpos⟩
  have hratio : (r.convergent (2 * n) : ℝ) = (A : ℝ) / B := by
    have hconv := convergent_cast_eq_nums_div_dens r (2 * n)
    simpa [hA, hB] using hconv
  have hBposR : 0 < (B : ℝ) := by exact_mod_cast hBpos
  have hAposR : 0 < (A : ℝ) := by
    have hgt' : (2 : ℝ) < (A : ℝ) / B := by
      calc
        (2 : ℝ) < (r.convergent (2 * n) : ℝ) := hgt
        _ = (A : ℝ) / B := hratio
    have hmul : (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
      have hmul' := (mul_lt_mul_of_pos_right hgt' hBposR)
      have hB_ne : (B : ℝ) ≠ 0 := ne_of_gt hBposR
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hB_ne] using hmul'
    exact lt_trans (mul_pos (by norm_num) hBposR) hmul
  have hApos : 0 < A := by exact_mod_cast hAposR
  -- Natural numerators/denominators.
  let a : ℕ := Int.toNat A
  let b : ℕ := Int.toNat B
  have hA_nat : (a : ℤ) = A := by
    simp [a, Int.toNat_of_nonneg (le_of_lt hApos)]
  have hB_nat : (b : ℤ) = B := by
    simp [b, Int.toNat_of_nonneg (le_of_lt hBpos)]
  have ha_pos : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha_zero
    have : (a : ℤ) = 0 := by simp [ha_zero]
    have : A = 0 := by simpa [hA_nat] using this
    exact (ne_of_gt hApos) this
  have hb_pos : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro hb_zero
    have : (b : ℤ) = 0 := by simp [hb_zero]
    have : B = 0 := by simpa [hB_nat] using this
    exact (ne_of_gt hBpos) this
  have hA_real : (a : ℝ) = (A : ℝ) := by exact_mod_cast hA_nat
  have hB_real : (b : ℝ) = (B : ℝ) := by exact_mod_cast hB_nat
  have hratio' : (r.convergent (2 * n) : ℝ) = (a : ℝ) / b := by
    simpa [hA_real, hB_real] using hratio
  -- Show the numerator is at least 2b.
  have htwoB_ltA : (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
    have hgt' : (2 : ℝ) < (A : ℝ) / B := by simpa [hratio] using hgt
    have hmul' := (mul_lt_mul_of_pos_right hgt' hBposR)
    have hB_ne : (B : ℝ) ≠ 0 := ne_of_gt hBposR
    simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hB_ne] using hmul'
  have htwoB_le_a : 2 * b ≤ a := by
    have htwoB_le_a_real : (2 : ℝ) * (b : ℝ) ≤ (a : ℝ) := by
      have htwoB_ltA' : (2 : ℝ) * (B : ℝ) < (A : ℝ) := htwoB_ltA
      have htwoB_ltA'' : (2 : ℝ) * (b : ℝ) < (a : ℝ) := by
        simpa [hA_real, hB_real] using htwoB_ltA'
      exact le_of_lt htwoB_ltA''
    exact_mod_cast htwoB_le_a_real
  -- Error bound: |r - a/b| ≤ 1 / b^2.
  have hbound : |r - (r.convergent (2 * n) : ℝ)| ≤
      1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n)) := by
    have hbound' :=
      GenContFract.abs_sub_convs_le (v := r) (n := 2 * n)
        (not_terminatedAt_of_irrational r hirr (2 * n))
    have hconv :
        (GenContFract.of r).convs (2 * n) = (r.convergent (2 * n) : ℝ) := by
      simpa using (Real.convs_eq_convergent r (2 * n))
    have hmono := GenContFract.of_den_mono (v := r) (n := 2 * n)
    have hden_pos := dens_pos_of_irrational r hirr (2 * n)
    have hden_pos' : 0 < (GenContFract.of r).dens (2 * n) := hden_pos
    have hmul_le :
        (GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n) ≤
          (GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n + 1) := by
      have := mul_le_mul_of_nonneg_left hmono (le_of_lt hden_pos')
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hbound'' : |r - (r.convergent (2 * n) : ℝ)| ≤
        1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n)) := by
      have hbound0 : |r - (r.convergent (2 * n) : ℝ)| ≤
          1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n + 1)) := by
        simpa [hconv] using hbound'
      have hpos0 : 0 < (GenContFract.of r).dens (2 * n) *
          (GenContFract.of r).dens (2 * n) := by
        exact mul_pos hden_pos' hden_pos'
      have hdiv_le :
          1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n + 1)) ≤
            1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n)) := by
        have := one_div_le_one_div_of_le hpos0 hmul_le
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      exact hbound0.trans hdiv_le
    exact hbound''
  have hbound' : |r - (r.convergent (2 * n) : ℝ)| ≤ 1 / ((b : ℝ) * (b : ℝ)) := by
    simpa [hB_real, hB] using hbound
  have hlt_even : (r.convergent (2 * n) : ℝ) < r :=
    convergent_even_lt_irrational r hirr n
  have hlt_even' : r - (r.convergent (2 * n) : ℝ) ≤ 1 / ((b : ℝ) * (b : ℝ)) := by
    have hnonneg : 0 ≤ r - (r.convergent (2 * n) : ℝ) := by linarith
    have habs : |r - (r.convergent (2 * n) : ℝ)| = r - (r.convergent (2 * n) : ℝ) := by
      simpa [abs_of_nonneg hnonneg]
    simpa [habs] using hbound'
  have hupper : (a : ℝ) / r < b := by
    have hratio_lt : (a : ℝ) / b < r := by simpa [hratio'] using hlt_even
    have hr_pos : 0 < r := by
      have h2r : (2 : ℝ) < r := lt_trans hgt hlt_even
      linarith
    have hb_posR : 0 < (b : ℝ) := by exact_mod_cast hb_pos
    have hmul : (a : ℝ) < r * b := by
      have hmul' := (mul_lt_mul_of_pos_right hratio_lt hb_posR)
      have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hb_ne] using hmul'
    have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
    -- Clear the denominator r.
    field_simp [hr_ne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hlower : (b - 1 : ℝ) < (a : ℝ) / r := by
    have hr_pos : 0 < r := by
      have h2r : (2 : ℝ) < r := lt_trans hgt hlt_even
      linarith
    have hb_posR : 0 < (b : ℝ) := by exact_mod_cast hb_pos
    have hratio_le : r ≤ (a : ℝ) / b + 1 / ((b : ℝ) * (b : ℝ)) := by
      have hratio_eq : (a : ℝ) / b = (r.convergent (2 * n) : ℝ) := by
        simpa [hratio'] using rfl
      linarith [hlt_even', hratio_eq]
    have hmul : r * (b - 1 : ℝ) ≤
        ((a : ℝ) / b + 1 / ((b : ℝ) * (b : ℝ))) * (b - 1 : ℝ) := by
      have hnonneg : 0 ≤ (b - 1 : ℝ) := by
        have hb1 : (1 : ℝ) ≤ b := by
          exact_mod_cast (Nat.succ_le_iff.mp hb_pos)
        linarith
      have := mul_le_mul_of_nonneg_right hratio_le hnonneg
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hineq : r * (b - 1 : ℝ) < a := by
      have hfrac_lt : (b - 1 : ℝ) / (b * b) < (a : ℝ) / b := by
        have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
        field_simp [hb_ne]
        have htwoB_le_a_real : (2 : ℝ) * (b : ℝ) ≤ (a : ℝ) := by
          exact_mod_cast htwoB_le_a
        nlinarith [hb_posR, htwoB_le_a_real]
      have hlt :
          ((a : ℝ) / b + 1 / ((b : ℝ) * (b : ℝ))) * (b - 1 : ℝ) < a := by
        have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
        have hcalc : (a : ℝ) / b * (b - 1 : ℝ) = a - (a : ℝ) / b := by
          calc
            (a : ℝ) / b * (b - 1 : ℝ) = (a : ℝ) / b * b - (a : ℝ) / b := by ring
            _ = a - (a : ℝ) / b := by
              field_simp [hb_ne]
        calc
          ((a : ℝ) / b + 1 / ((b : ℝ) * (b : ℝ))) * (b - 1 : ℝ)
              = (a : ℝ) / b * (b - 1 : ℝ) + (b - 1 : ℝ) / (b * b) := by
                  ring
          _ = a - (a : ℝ) / b + (b - 1 : ℝ) / (b * b) := by
                  simpa [hcalc]
          _ < a := by
                  linarith [hfrac_lt]
      exact lt_of_le_of_lt hmul hlt
    have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
    field_simp [hr_ne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
  have hceil :
      Nat.ceil ((a : ℝ) / r) = b := by
    have hb_ne : b ≠ 0 := by exact Nat.ne_of_gt hb_pos
    have hceil' := (Nat.ceil_eq_iff (a := (a : ℝ) / r) (n := b) hb_ne).2
    refine hceil' ?_
    refine ⟨?_, le_of_lt hupper⟩
    have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      simpa using (Nat.cast_pred (R := ℝ) (n := b) hb_pos)
    have hlower' : ((b - 1 : ℕ) : ℝ) < (a : ℝ) / r := by
      simpa [hb1] using hlower
    exact hlower'
  exact ⟨a, b, ha_pos, hb_pos, hratio', hceil⟩

/-- Extended version of ceil_convergent_even_eq_den that also returns nums/dens equalities. -/
lemma ceil_convergent_even_eq_den_ext (r : ℝ) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent (2 * n) : ℝ)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (r.convergent (2 * n) : ℝ) = (a : ℝ) / b ∧
      Nat.ceil ((a : ℝ) / r) = b ∧
      (GenContFract.of r).nums (2 * n) = (a : ℝ) ∧
      (GenContFract.of r).dens (2 * n) = (b : ℝ) := by
  -- Copy the proof from ceil_convergent_even_eq_den and add the extra conclusions
  rcases nums_int_of_irrational r hirr (2 * n) with ⟨A, hA⟩
  rcases dens_int_pos_of_irrational r hirr (2 * n) with ⟨B, hB, hBpos⟩
  have hratio : (r.convergent (2 * n) : ℝ) = (A : ℝ) / B := by
    have hconv := convergent_cast_eq_nums_div_dens r (2 * n)
    simpa [hA, hB] using hconv
  have hBposR : 0 < (B : ℝ) := by exact_mod_cast hBpos
  have hAposR : 0 < (A : ℝ) := by
    have hgt' : (2 : ℝ) < (A : ℝ) / B := by simpa [hratio] using hgt
    have hmul : (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
      have hmul' := mul_lt_mul_of_pos_right hgt' hBposR
      have hB_ne : (B : ℝ) ≠ 0 := ne_of_gt hBposR
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hB_ne] using hmul'
    exact lt_trans (mul_pos (by norm_num) hBposR) hmul
  have hApos : 0 < A := by exact_mod_cast hAposR
  let a : ℕ := Int.toNat A
  let b : ℕ := Int.toNat B
  have hA_nat : (a : ℤ) = A := by simp [a, Int.toNat_of_nonneg (le_of_lt hApos)]
  have hB_nat : (b : ℤ) = B := by simp [b, Int.toNat_of_nonneg (le_of_lt hBpos)]
  have ha_pos : 0 < a := by
    apply Nat.pos_of_ne_zero; intro ha_zero
    have : (a : ℤ) = 0 := by simp [ha_zero]
    have : A = 0 := by simpa [hA_nat] using this
    exact (ne_of_gt hApos) this
  have hb_pos : 0 < b := by
    apply Nat.pos_of_ne_zero; intro hb_zero
    have : (b : ℤ) = 0 := by simp [hb_zero]
    have : B = 0 := by simpa [hB_nat] using this
    exact (ne_of_gt hBpos) this
  have hA_real : (a : ℝ) = (A : ℝ) := by exact_mod_cast hA_nat
  have hB_real : (b : ℝ) = (B : ℝ) := by exact_mod_cast hB_nat
  have hratio' : (r.convergent (2 * n) : ℝ) = (a : ℝ) / b := by
    simpa [hA_real, hB_real] using hratio
  -- The nums/dens equalities
  have hnums_eq : (GenContFract.of r).nums (2 * n) = (a : ℝ) := by rw [hA, hA_real]
  have hdens_eq : (GenContFract.of r).dens (2 * n) = (b : ℝ) := by rw [hB, hB_real]
  -- Inline the ceiling proof directly (same as ceil_convergent_even_eq_den)
  have htwoB_ltA : (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
    have hgt' : (2 : ℝ) < (A : ℝ) / B := by simpa [hratio] using hgt
    have hmul' := mul_lt_mul_of_pos_right hgt' hBposR
    have hB_ne : (B : ℝ) ≠ 0 := ne_of_gt hBposR
    simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hB_ne] using hmul'
  have htwoB_le_a : 2 * b ≤ a := by
    have htwoB_le_a_real : (2 : ℝ) * (b : ℝ) ≤ (a : ℝ) := by
      have htwoB_ltA'' : (2 : ℝ) * (b : ℝ) < (a : ℝ) := by
        simpa [hA_real, hB_real] using htwoB_ltA
      exact le_of_lt htwoB_ltA''
    exact_mod_cast htwoB_le_a_real
  have hbound : |r - (r.convergent (2 * n) : ℝ)| ≤
      1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n)) := by
    have hbound' :=
      GenContFract.abs_sub_convs_le (v := r) (n := 2 * n)
        (not_terminatedAt_of_irrational r hirr (2 * n))
    have hconv :
        (GenContFract.of r).convs (2 * n) = (r.convergent (2 * n) : ℝ) := by
      simpa using (Real.convs_eq_convergent r (2 * n))
    have hmono := GenContFract.of_den_mono (v := r) (n := 2 * n)
    have hden_pos := dens_pos_of_irrational r hirr (2 * n)
    have hmul_le :
        (GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n) ≤
          (GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n + 1) := by
      have := mul_le_mul_of_nonneg_left hmono (le_of_lt hden_pos)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hbound0 : |r - (r.convergent (2 * n) : ℝ)| ≤
        1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n + 1)) := by
      simpa [hconv] using hbound'
    have hpos0 : 0 < (GenContFract.of r).dens (2 * n) *
        (GenContFract.of r).dens (2 * n) := mul_pos hden_pos hden_pos
    have hdiv_le :
        1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n + 1)) ≤
          1 / ((GenContFract.of r).dens (2 * n) * (GenContFract.of r).dens (2 * n)) := by
      have := one_div_le_one_div_of_le hpos0 hmul_le
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    exact hbound0.trans hdiv_le
  have hbound' : |r - (r.convergent (2 * n) : ℝ)| ≤ 1 / ((b : ℝ) * (b : ℝ)) := by
    simpa [hB_real, hB] using hbound
  have hlt_even : (r.convergent (2 * n) : ℝ) < r := convergent_even_lt_irrational r hirr n
  have hlt_even' : r - (r.convergent (2 * n) : ℝ) ≤ 1 / ((b : ℝ) * (b : ℝ)) := by
    have hnonneg : 0 ≤ r - (r.convergent (2 * n) : ℝ) := by linarith
    have habs : |r - (r.convergent (2 * n) : ℝ)| = r - (r.convergent (2 * n) : ℝ) := by
      simpa [abs_of_nonneg hnonneg]
    simpa [habs] using hbound'
  have hupper : (a : ℝ) / r < b := by
    have hratio_lt : (a : ℝ) / b < r := by simpa [hratio'] using hlt_even
    have hr_pos : 0 < r := by linarith [lt_trans hgt hlt_even]
    have hb_posR : 0 < (b : ℝ) := by exact_mod_cast hb_pos
    have hmul : (a : ℝ) < r * b := by
      have hmul' := mul_lt_mul_of_pos_right hratio_lt hb_posR
      have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hb_ne] using hmul'
    have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
    field_simp [hr_ne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hlower : (b - 1 : ℝ) < (a : ℝ) / r := by
    have hr_pos : 0 < r := by linarith [lt_trans hgt hlt_even]
    have hb_posR : 0 < (b : ℝ) := by exact_mod_cast hb_pos
    have hratio_le : r ≤ (a : ℝ) / b + 1 / ((b : ℝ) * (b : ℝ)) := by
      have hratio_eq : (a : ℝ) / b = (r.convergent (2 * n) : ℝ) := hratio'.symm
      linarith [hlt_even', hratio_eq]
    have hmul : r * (b - 1 : ℝ) ≤
        ((a : ℝ) / b + 1 / ((b : ℝ) * (b : ℝ))) * (b - 1 : ℝ) := by
      have hnonneg : 0 ≤ (b - 1 : ℝ) := by
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (Nat.succ_le_iff.mp hb_pos)
        linarith
      have := mul_le_mul_of_nonneg_right hratio_le hnonneg
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hineq : r * (b - 1 : ℝ) < a := by
      have hfrac_lt : (b - 1 : ℝ) / (b * b) < (a : ℝ) / b := by
        have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
        field_simp [hb_ne]
        have htwoB_le_a_real : (2 : ℝ) * (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast htwoB_le_a
        nlinarith [hb_posR, htwoB_le_a_real]
      have hlt :
          ((a : ℝ) / b + 1 / ((b : ℝ) * (b : ℝ))) * (b - 1 : ℝ) < a := by
        have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
        have hcalc : (a : ℝ) / b * (b - 1 : ℝ) = a - (a : ℝ) / b := by
          calc
            (a : ℝ) / b * (b - 1 : ℝ) = (a : ℝ) / b * b - (a : ℝ) / b := by ring
            _ = a - (a : ℝ) / b := by field_simp [hb_ne]
        calc
          ((a : ℝ) / b + 1 / ((b : ℝ) * (b : ℝ))) * (b - 1 : ℝ)
              = (a : ℝ) / b * (b - 1 : ℝ) + (b - 1 : ℝ) / (b * b) := by ring
          _ = a - (a : ℝ) / b + (b - 1 : ℝ) / (b * b) := by simpa [hcalc]
          _ < a := by linarith [hfrac_lt]
      exact lt_of_le_of_lt hmul hlt
    have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
    field_simp [hr_ne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
  have hceil : Nat.ceil ((a : ℝ) / r) = b := by
    have hb_ne : b ≠ 0 := Nat.ne_of_gt hb_pos
    have hceil' := (Nat.ceil_eq_iff (a := (a : ℝ) / r) (n := b) hb_ne).2
    refine hceil' ⟨?_, le_of_lt hupper⟩
    have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      simpa using (Nat.cast_pred (R := ℝ) (n := b) hb_pos)
    simpa [hb1] using hlower
  exact ⟨a, b, ha_pos, hb_pos, hratio', hceil, hnums_eq, hdens_eq⟩

lemma floor_convergent_odd_eq_den (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent (2 * n + 1) : ℝ)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (r.convergent (2 * n + 1) : ℝ) = (a : ℝ) / b ∧
      Nat.floor ((a : ℝ) / r) = b := by
  rcases nums_int_of_irrational r hirr (2 * n + 1) with ⟨A, hA⟩
  rcases dens_int_pos_of_irrational r hirr (2 * n + 1) with ⟨B, hB, hBpos⟩
  have hratio : (r.convergent (2 * n + 1) : ℝ) = (A : ℝ) / B := by
    have hconv := convergent_cast_eq_nums_div_dens r (2 * n + 1)
    simpa [hA, hB] using hconv
  have hBposR : 0 < (B : ℝ) := by exact_mod_cast hBpos
  have hAposR : 0 < (A : ℝ) := by
    have hgt' : (2 : ℝ) < (A : ℝ) / B := by
      calc
        (2 : ℝ) < (r.convergent (2 * n + 1) : ℝ) := hgt
        _ = (A : ℝ) / B := hratio
    have hmul : (2 : ℝ) * (B : ℝ) < (A : ℝ) := by
      have hmul' := (mul_lt_mul_of_pos_right hgt' hBposR)
      have hB_ne : (B : ℝ) ≠ 0 := ne_of_gt hBposR
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hB_ne] using hmul'
    exact lt_trans (mul_pos (by norm_num) hBposR) hmul
  have hApos : 0 < A := by exact_mod_cast hAposR
  let a : ℕ := Int.toNat A
  let b : ℕ := Int.toNat B
  have hA_nat : (a : ℤ) = A := by
    simp [a, Int.toNat_of_nonneg (le_of_lt hApos)]
  have hB_nat : (b : ℤ) = B := by
    simp [b, Int.toNat_of_nonneg (le_of_lt hBpos)]
  have ha_pos : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha_zero
    have : (a : ℤ) = 0 := by simp [ha_zero]
    have : A = 0 := by simpa [hA_nat] using this
    exact (ne_of_gt hApos) this
  have hb_pos : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro hb_zero
    have : (b : ℤ) = 0 := by simp [hb_zero]
    have : B = 0 := by simpa [hB_nat] using this
    exact (ne_of_gt hBpos) this
  have hA_real : (a : ℝ) = (A : ℝ) := by exact_mod_cast hA_nat
  have hB_real : (b : ℝ) = (B : ℝ) := by exact_mod_cast hB_nat
  have hratio' : (r.convergent (2 * n + 1) : ℝ) = (a : ℝ) / b := by
    simpa [hA_real, hB_real] using hratio
  have hbound : |r - (r.convergent (2 * n + 1) : ℝ)| ≤
      1 / ((GenContFract.of r).dens (2 * n + 1) * (GenContFract.of r).dens (2 * n + 1)) := by
    have hbound' :=
      GenContFract.abs_sub_convs_le (v := r) (n := 2 * n + 1)
        (not_terminatedAt_of_irrational r hirr (2 * n + 1))
    have hconv :
        (GenContFract.of r).convs (2 * n + 1) = (r.convergent (2 * n + 1) : ℝ) := by
      simpa using (Real.convs_eq_convergent r (2 * n + 1))
    have hmono := GenContFract.of_den_mono (v := r) (n := 2 * n + 1)
    have hden_pos := dens_pos_of_irrational r hirr (2 * n + 1)
    have hden_pos' : 0 < (GenContFract.of r).dens (2 * n + 1) := hden_pos
    have hmul_le :
        (GenContFract.of r).dens (2 * n + 1) * (GenContFract.of r).dens (2 * n + 1) ≤
          (GenContFract.of r).dens (2 * n + 1) * (GenContFract.of r).dens (2 * n + 2) := by
      have := mul_le_mul_of_nonneg_left hmono (le_of_lt hden_pos')
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hbound'' : |r - (r.convergent (2 * n + 1) : ℝ)| ≤
        1 / ((GenContFract.of r).dens (2 * n + 1) * (GenContFract.of r).dens (2 * n + 1)) := by
      have hbound0 : |r - (r.convergent (2 * n + 1) : ℝ)| ≤
          1 / ((GenContFract.of r).dens (2 * n + 1) * (GenContFract.of r).dens (2 * n + 2)) := by
        simpa [hconv] using hbound'
      have hpos0 : 0 < (GenContFract.of r).dens (2 * n + 1) *
          (GenContFract.of r).dens (2 * n + 1) := by
        exact mul_pos hden_pos' hden_pos'
      have hdiv_le :
          1 / ((GenContFract.of r).dens (2 * n + 1) * (GenContFract.of r).dens (2 * n + 2)) ≤
            1 / ((GenContFract.of r).dens (2 * n + 1) * (GenContFract.of r).dens (2 * n + 1)) := by
        have := one_div_le_one_div_of_le hpos0 hmul_le
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      exact hbound0.trans hdiv_le
    exact hbound''
  have hbound' : |r - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * (b : ℝ)) := by
    have hden_eq : (GenContFract.of r).dens (2 * n + 1) = (b : ℝ) := by
      simpa [hB_real] using hB
    have hbound0 := hbound
    rw [hratio'] at hbound0
    simpa [hden_eq] using hbound0
  have hlt_odd : r < (r.convergent (2 * n + 1) : ℝ) :=
    convergent_odd_gt_irrational r hirr n
  have hratio_lt : r < (a : ℝ) / b := by
    calc
      r < (r.convergent (2 * n + 1) : ℝ) := hlt_odd
      _ = (a : ℝ) / b := hratio'
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
  have hb_posR : 0 < (b : ℝ) := by exact_mod_cast hb_pos
  have hmul : r * (b : ℝ) < (a : ℝ) := by
    have hmul' := (mul_lt_mul_of_pos_right hratio_lt hb_posR)
    have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
    simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hb_ne] using hmul'
  have hlower : (b : ℝ) < (a : ℝ) / r := by
    have hmul' : (b : ℝ) * r < a := by simpa [mul_comm] using hmul
    exact (lt_div_iff₀ hr_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul')
  have hnonneg : 0 ≤ (a : ℝ) / b - r := by linarith
  have habs : |r - (a : ℝ) / b| = (a : ℝ) / b - r := by
    have habs' : |(a : ℝ) / b - r| = (a : ℝ) / b - r := abs_of_nonneg hnonneg
    simpa [abs_sub_comm] using habs'
  have hle' : (a : ℝ) / b ≤ r + 1 / ((b : ℝ) * (b : ℝ)) := by
    have hle'' : (a : ℝ) / b - r ≤ 1 / ((b : ℝ) * (b : ℝ)) := by
      simpa [habs] using hbound'
    linarith
  have hmul_le : (a : ℝ) ≤ r * b + 1 / b := by
    have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
    have hmul' := (mul_le_mul_of_nonneg_left hle' (le_of_lt hb_posR))
    have hmul'' : (a : ℝ) ≤ b * (r + 1 / (b * b)) := by
      calc
        (a : ℝ) = b * ((a : ℝ) / b) := by
          field_simp [hb_ne]
        _ ≤ b * (r + 1 / (b * b)) := hmul'
    have hmul''' : b * (r + 1 / (b * b)) = r * b + 1 / b := by
      field_simp [hb_ne]
    calc
      (a : ℝ) ≤ b * (r + 1 / (b * b)) := hmul''
      _ = r * b + 1 / b := hmul'''
  have hb_ge1 : (1 : ℝ) ≤ b := by
    exact_mod_cast (Nat.succ_le_iff.mp hb_pos)
  have h1b_le_one : (1 : ℝ) / b ≤ 1 := by
    have h1_pos : (0 : ℝ) < 1 := by norm_num
    have := (one_div_le_one_div_of_le h1_pos hb_ge1)
    simpa using this
  have h1b_le_r : (1 : ℝ) / b ≤ r := by
    have h1_le_r : (1 : ℝ) ≤ r := by linarith
    exact le_trans h1b_le_one h1_le_r
  have hmul_le' : (a : ℝ) ≤ r * (b + 1) := by
    have : r * b + 1 / b ≤ r * b + r := by nlinarith
    have hmul_le'' : (a : ℝ) ≤ r * b + r := le_trans hmul_le this
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using hmul_le''
  have hupper_le : (a : ℝ) / r ≤ b + 1 := by
    exact (div_le_iff₀ hr_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_le')
  have hirr_div : Irrational ((a : ℝ) / r) := by
    have : Irrational (a / r) := by
      simpa using (irrational_natCast_div_iff (n := a) (x := r)).2 ⟨Nat.ne_of_gt ha_pos, hirr⟩
    simpa using this
  have hne : (a : ℝ) / r ≠ (b + 1 : ℝ) := by
    have hne' := hirr_div.ne_rat (b + 1 : ℚ)
    simpa using hne'
  have hupper : (a : ℝ) / r < b + 1 := lt_of_le_of_ne hupper_le hne
  have hfloor : Nat.floor ((a : ℝ) / r) = b := by
    have ha0 : 0 ≤ (a : ℝ) / r := le_of_lt (div_pos (Nat.cast_pos.mpr ha_pos) hr_pos)
    refine (Nat.floor_eq_iff ha0).2 ?_
    refine ⟨le_of_lt hlower, hupper⟩
  exact ⟨a, b, ha_pos, hb_pos, hratio', hfloor⟩

lemma floor_div_eq_pred_of_ceil_eq (r : ℝ) (hirr : Irrational r)
    {a b : ℕ} (ha : 0 < a) (hr : 0 < r) (hceil : Nat.ceil ((a : ℝ) / r) = b) :
    Nat.floor ((a : ℝ) / r) = b - 1 := by
  have hb_pos : 0 < b := by
    by_contra hb
    have hb0 : b = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt hb)
    have hce : Nat.ceil ((a : ℝ) / r) = 0 := by simpa [hb0] using hceil
    have hle : (a : ℝ) / r ≤ 0 := (Nat.ceil_eq_zero).1 hce
    have ha_posR : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
    have hpos : 0 < (a : ℝ) / r := by exact div_pos ha_posR hr
    linarith
  have hb_ne : b ≠ 0 := by exact Nat.ne_of_gt hb_pos
  have hceil' := (Nat.ceil_eq_iff (a := (a : ℝ) / r) (n := b) hb_ne).1 hceil
  have hlt : ((b - 1 : ℕ) : ℝ) < (a : ℝ) / r := hceil'.1
  have hle : (a : ℝ) / r ≤ b := hceil'.2
  have hirr_div : Irrational ((a : ℝ) / r) := by
    have ha_ne : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    have hirr' : Irrational (a / r) := by
      simpa using (irrational_natCast_div_iff (n := a) (x := r)).2 ⟨Nat.ne_of_gt ha, hirr⟩
    simpa using hirr'
  have hne : (a : ℝ) / r ≠ (b : ℝ) := by
    have hne' := hirr_div.ne_rat (b : ℚ)
    simpa using hne'
  have hlt' : (a : ℝ) / r < b := lt_of_le_of_ne hle hne
  have hcast : ((b - 1 : ℕ) : ℝ) + 1 = (b : ℝ) := by
    have hnat : b - 1 + 1 = b := Nat.sub_add_cancel (Nat.succ_le_iff.mp hb_pos)
    exact_mod_cast hnat
  have hfloor' :
      Nat.floor ((a : ℝ) / r) = b - 1 := by
    have ha0 : 0 ≤ (a : ℝ) / r := le_of_lt (div_pos (Nat.cast_pos.mpr ha) hr)
    refine (Nat.floor_eq_iff ha0).2 ?_
    refine ⟨le_of_lt hlt, ?_⟩
    simpa [hcast] using hlt'
  exact hfloor'

lemma circleGraph_rounding_cohom_convergent_odd
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent (2 * n + 1) : ℝ)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (r.convergent (2 * n + 1) : ℝ) = (a : ℝ) / b ∧
      (∃ _ : NeZero a,
        Cohom (circleGraphOpen r hr) (fractionGraph a b) ∧
        Cohom (circleGraphClosed r hr) (fractionGraph a b)) := by
  rcases floor_convergent_odd_eq_den r hr hirr n hgt with ⟨a, b, ha, hb, hratio, hfloor⟩
  have hb_posR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hlt : r < (a : ℝ) / b := by
    calc
      r < (r.convergent (2 * n + 1) : ℝ) := convergent_odd_gt_irrational r hirr n
      _ = (a : ℝ) / b := hratio
  have hmul : r * (b : ℝ) < (a : ℝ) := by
    have hmul' := mul_lt_mul_of_pos_right hlt hb_posR
    have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
    simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hb_ne] using hmul'
  have hb_ge1 : 1 ≤ b := Nat.succ_le_iff.mp hb
  have h2_le_2b : 2 ≤ 2 * b := Nat.mul_le_mul_left 2 hb_ge1
  have h2b_le_a : 2 * b ≤ a := by
    have h2b_le_rb : (2 : ℝ) * (b : ℝ) ≤ r * b := by
      have hb_nonneg : 0 ≤ (b : ℝ) := by exact_mod_cast (Nat.zero_le b)
      exact mul_le_mul_of_nonneg_right hr hb_nonneg
    have h2b_le_a_real : (2 : ℝ) * (b : ℝ) ≤ (a : ℝ) :=
      le_of_lt (lt_of_le_of_lt h2b_le_rb hmul)
    exact_mod_cast h2b_le_a_real
  have h2_le_a : 2 ≤ a := le_trans h2_le_2b h2b_le_a
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
  have hNr : r ≤ (a : ℝ) := by
    have hb_ge1R : (1 : ℝ) ≤ b := by exact_mod_cast hb_ge1
    have hr_le : r ≤ r * b := by
      have := mul_le_mul_of_nonneg_left hb_ge1R (le_of_lt hr_pos)
      simpa using this
    exact le_of_lt (lt_of_le_of_lt hr_le hmul)
  haveI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  have hcohom :=
    circleGraph_rounding_cohom_floor r hr a h2_le_a hNr
  rcases hcohom with ⟨_, hcohom_open, hcohom_closed⟩
  refine ⟨a, b, ha, hb, hratio, ?_⟩
  refine ⟨inferInstance, ?_, ?_⟩
  · simpa [hfloor] using hcohom_open
  · simpa [hfloor] using hcohom_closed

lemma cohom_fractionGraph_to_convergent_odd_open
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent (2 * n + 1) : ℝ))
    {N q : ℕ} [NeZero N]
    (hcohom : Cohom (fractionGraph N q) (circleGraphOpen r hr)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (r.convergent (2 * n + 1) : ℝ) = (a : ℝ) / b ∧
      (∃ _ : NeZero a, Cohom (fractionGraph N q) (fractionGraph a b)) := by
  rcases circleGraph_rounding_cohom_convergent_odd r hr hirr n hgt with
    ⟨a, b, ha, hb, hratio, ⟨ha0, hcohom_open, _⟩⟩
  classical
  let _ : NeZero a := ha0
  refine ⟨a, b, ha, hb, hratio, ?_⟩
  exact ⟨inferInstance, Cohom.trans hcohom hcohom_open⟩

lemma cohom_fractionGraph_to_convergent_odd_closed
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent (2 * n + 1) : ℝ))
    {N q : ℕ} [NeZero N]
    (hcohom : Cohom (fractionGraph N q) (circleGraphClosed r hr)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (r.convergent (2 * n + 1) : ℝ) = (a : ℝ) / b ∧
      (∃ _ : NeZero a, Cohom (fractionGraph N q) (fractionGraph a b)) := by
  rcases circleGraph_rounding_cohom_convergent_odd r hr hirr n hgt with
    ⟨a, b, ha, hb, hratio, ⟨ha0, _, hcohom_closed⟩⟩
  classical
  let _ : NeZero a := ha0
  refine ⟨a, b, ha, hb, hratio, ?_⟩
  exact ⟨inferInstance, Cohom.trans hcohom hcohom_closed⟩

lemma circleGraph_equidistant_shift_induced_closed_convergent
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent (2 * n) : ℝ)) (y : Circle) :
    ∃ (a b : ℕ) (ha : 0 < a) (hb : 0 < b),
      (r.convergent (2 * n) : ℝ) = (a : ℝ) / b ∧
      Nonempty (by
        classical
        let _ : NeZero a := ⟨Nat.ne_of_gt ha⟩
        let _ : NeZero b := ⟨Nat.ne_of_gt hb⟩
        exact (circleGraphClosed r hr).induce (equidistantPointsShift a y) ≃g
          fractionGraph a b) := by
  rcases ceil_convergent_even_eq_den r hirr n hgt with ⟨a, b, ha, hb, hratio, hceil⟩
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
  have hb_posR : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  have hgt' : (2 : ℝ) < (a : ℝ) / b := by simpa [hratio] using hgt
  have hmul : (2 : ℝ) * (b : ℝ) < (a : ℝ) := by
    have hmul' := mul_lt_mul_of_pos_right hgt' hb_posR
    have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
    simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hb_ne] using hmul'
  have h2b_le_a : 2 * b ≤ a := by exact_mod_cast (le_of_lt hmul)
  have hb_ge1 : 1 ≤ b := Nat.succ_le_iff.mp hb
  have h2_le_2b : 2 ≤ 2 * b := Nat.mul_le_mul_left 2 hb_ge1
  have ha_ge2 : 2 ≤ a := le_trans h2_le_2b h2b_le_a
  haveI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  rcases circleGraph_equidistant_induced_closed r hr a ha_ge2 with ⟨iso, _⟩
  have hfloor : Nat.floor ((a : ℝ) / r) = b - 1 :=
    floor_div_eq_pred_of_ceil_eq r hirr ha hr_pos hceil
  have hq_eq : Nat.floor ((a : ℝ) / r) + 1 = b := by
    have hnat : b - 1 + 1 = b := Nat.sub_add_cancel (Nat.succ_le_iff.mp hb)
    simpa [hfloor, hnat]
  have iso' :
      (circleGraphClosed r hr).induce (equidistantPointsShift a y) ≃g
        fractionGraph a b := by
    have iso_shift := (circleGraphClosed_induce_shift_iso r hr a y).trans iso
    simpa [hq_eq] using iso_shift
  refine ⟨a, b, ha, hb, hratio, ?_⟩
  classical
  let _ : NeZero a := ⟨Nat.ne_of_gt ha⟩
  let _ : NeZero b := ⟨Nat.ne_of_gt hb⟩
  exact ⟨iso'⟩

lemma circleGraph_equidistant_shift_induced_open_convergent
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) (n : ℕ)
    (hgt : (2 : ℝ) < (r.convergent (2 * n) : ℝ)) (y : Circle) :
    ∃ (a b : ℕ) (ha : 0 < a) (hb : 0 < b),
      (r.convergent (2 * n) : ℝ) = (a : ℝ) / b ∧
      Nonempty (by
        classical
        let _ : NeZero a := ⟨Nat.ne_of_gt ha⟩
        let _ : NeZero b := ⟨Nat.ne_of_gt hb⟩
        exact (circleGraphOpen r hr).induce (equidistantPointsShift a y) ≃g
          fractionGraph a b) := by
  rcases ceil_convergent_even_eq_den r hirr n hgt with ⟨a, b, ha, hb, hratio, hceil⟩
  have hb_ge1 : 1 ≤ b := Nat.succ_le_iff.mp hb
  have hb_posR : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  have hgt' : (2 : ℝ) < (a : ℝ) / b := by simpa [hratio] using hgt
  have hmul : (2 : ℝ) * (b : ℝ) < (a : ℝ) := by
    have hmul' := mul_lt_mul_of_pos_right hgt' hb_posR
    have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_posR
    simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel_right₀ hb_ne] using hmul'
  have h2b_le_a : 2 * b ≤ a := by exact_mod_cast (le_of_lt hmul)
  have h2_le_2b : 2 ≤ 2 * b := Nat.mul_le_mul_left 2 hb_ge1
  have ha_ge2 : 2 ≤ a := le_trans h2_le_2b h2b_le_a
  haveI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  rcases circleGraph_equidistant_induced_open r hr a ha_ge2 with ⟨iso, _⟩
  have hq_eq : Nat.ceil ((a : ℝ) / r) = b := hceil
  have iso' :
      (circleGraphOpen r hr).induce (equidistantPointsShift a y) ≃g
        fractionGraph a b := by
    have iso_shift := (circleGraphOpen_induce_shift_iso r hr a y).trans iso
    simpa [hq_eq] using iso_shift
  refine ⟨a, b, ha, hb, hratio, ?_⟩
  classical
  let _ : NeZero a := ⟨Nat.ne_of_gt ha⟩
  let _ : NeZero b := ⟨Nat.ne_of_gt hb⟩
  exact ⟨iso'⟩

lemma isCohom_induce_to_closed (r : ℝ) (hr : 2 ≤ r) (S : Set Circle)
    (f : Circle → Circle)
    (hf : IsCohom (circleGraphClosed r hr) (circleGraphClosed r hr) f) :
    IsCohom ((circleGraphClosed r hr).induce S) (circleGraphClosed r hr) (fun x => f x) := by
  intro u v huv hnadj
  have huv' : (u : Circle) ≠ v := by
    intro h
    exact huv (Subtype.ext h)
  have hnadj' : ¬(circleGraphClosed r hr).Adj (u : Circle) (v : Circle) := by
    simpa [SimpleGraph.induce_adj] using hnadj
  simpa using (hf u v huv' hnadj')

lemma isCohom_induce_to_open (r : ℝ) (hr : 2 ≤ r) (S : Set Circle)
    (f : Circle → Circle)
    (hf : IsCohom (circleGraphOpen r hr) (circleGraphOpen r hr) f) :
    IsCohom ((circleGraphOpen r hr).induce S) (circleGraphOpen r hr) (fun x => f x) := by
  intro u v huv hnadj
  have huv' : (u : Circle) ≠ v := by
    intro h
    exact huv (Subtype.ext h)
  have hnadj' : ¬(circleGraphOpen r hr).Adj (u : Circle) (v : Circle) := by
    simpa [SimpleGraph.induce_adj] using hnadj
  simpa using (hf u v huv' hnadj')

lemma cohom_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : Cohom G H := by
  refine ⟨e, ?_⟩
  intro u v huv hnadj
  constructor
  · intro h
    exact huv (e.injective h)
  · intro hadj
    have hmap : H.Adj (e u) (e v) ↔ G.Adj u v := by
      simpa using (e.map_rel_iff (a := u) (b := v))
    exact hnadj (hmap.1 hadj)

lemma circleGraphOpen_cohom_equidistant_shift_fractionGraph
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (x : Circle) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ → y ≠ x →
      ∃ q : ℕ, 0 < q ∧ Cohom (fractionGraph N q) (circleGraphOpen r hr) := by
  classical
  rcases circleGraphOpen_induce_swap_iso_equidistant_shift_fractionGraph r hr hirr N hN x with
    ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy hyne
  rcases hδ y hy hyne with ⟨q, hq_pos, hIso⟩
  have hcohom_induced :
      Cohom ((circleGraphOpen r hr).induce
        (insert y (equidistantPointsShift N x \ ({x} : Set Circle))))
        (circleGraphOpen r hr) :=
    induced_cohom (circleGraphOpen r hr)
      (insert y (equidistantPointsShift N x \ ({x} : Set Circle)))
  have hcohom_iso :
      Cohom (fractionGraph N q)
        ((circleGraphOpen r hr).induce
          (insert y (equidistantPointsShift N x \ ({x} : Set Circle)))) := by
    rcases hIso with ⟨iso⟩
    simpa using (cohom_of_iso iso.symm)
  refine ⟨q, hq_pos, Cohom.trans hcohom_iso hcohom_induced⟩

lemma circleGraphClosed_cohom_equidistant_shift_fractionGraph
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (x : Circle) :
    ∃ δ > 0, ∀ y, circleDistance y x < δ → y ≠ x →
      ∃ q : ℕ, 0 < q ∧ Cohom (fractionGraph N q) (circleGraphClosed r hr) := by
  classical
  rcases circleGraphClosed_induce_swap_iso_equidistant_shift_fractionGraph r hr hirr N hN x with
    ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy hyne
  rcases hδ y hy hyne with ⟨q, hq_pos, hIso⟩
  have hcohom_induced :
      Cohom ((circleGraphClosed r hr).induce
        (insert y (equidistantPointsShift N x \ ({x} : Set Circle))))
        (circleGraphClosed r hr) :=
    induced_cohom (circleGraphClosed r hr)
      (insert y (equidistantPointsShift N x \ ({x} : Set Circle)))
  have hcohom_iso :
      Cohom (fractionGraph N q)
        ((circleGraphClosed r hr).induce
          (insert y (equidistantPointsShift N x \ ({x} : Set Circle)))) := by
    rcases hIso with ⟨iso⟩
    simpa using (cohom_of_iso iso.symm)
  refine ⟨q, hq_pos, Cohom.trans hcohom_iso hcohom_induced⟩

/-! ### `ℕ+` wrappers for `main_selfCohom_isIso` and `main_selfCohom_form` -/

/-- Proof of `main_selfCohom_isIso`: `ℕ+` wrapper for
    `fractionGraph_selfCohom_isIso_general`. The `NeZero p` requirement is
    automatic since `p : ℕ+`. -/
theorem fractionGraph_selfCohom_isIso_pnat (p q : ℕ+) (h2q : 2 * q ≤ p)
    (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : IsCohom (fractionGraph p q) (fractionGraph p q) f) :
    Function.Bijective f :=
  fractionGraph_selfCohom_isIso_general (p : ℕ) (q : ℕ)
    (by exact_mod_cast h2q) hcoprime f hf

/-- Proof of `main_selfCohom_form`: `ℕ+` wrapper for
    `fractionGraph_selfCohom_form`. -/
theorem fractionGraph_selfCohom_form_pnat (p q : ℕ+) (hq : 2 ≤ q) (h2q : 2 * q ≤ p)
    (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : IsCohom (fractionGraph p q) (fractionGraph p q) f) :
    ∃ a : ZMod p, (∀ x, f x = a + x) ∨ (∀ x, f x = a - x) :=
  fractionGraph_selfCohom_form (p : ℕ) (q : ℕ)
    (by exact_mod_cast hq) (by exact_mod_cast h2q) hcoprime f hf

end AsymptoticSpectrumDistance
