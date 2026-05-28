/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.FractionGraph
import AsymptoticSpectrumDistance.Section4.CircleGraphs
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Convex-Round Graphs

This file formalizes convex-round graph theory following Bang-Jensen & Huang
"Convex-Round Graphs are Circular-Perfect" (J. Graph Theory 40:182-194, 2002).

## Main definitions

* `CyclicInterval`: An interval in cyclic order on Fin n
* `IsConvexRoundEnum`: A graph with vertices Fin n is convex-round if each neighborhood
  forms a cyclic interval
* `ConvexRoundGraph`: A graph that admits a convex-round enumeration

## Main results

* `convexRound_iso_cyclic_order`: Isomorphisms between non-bipartite convex-round cores
  preserve cyclic order (up to rotation/reflection)

## References

* [BJH02] Bang-Jensen, Huang, "Convex-Round Graphs are Circular-Perfect", 2002
-/

namespace ConvexRound

open FractionGraphBasic SimpleGraph

/-! ### Section 1: Cyclic Intervals on Fin n -/

/-- A cyclic interval [a, b] in Fin n, going from a to b in the positive direction.
    For a ≤ b: {a, a+1, ..., b}
    For a > b: {a, a+1, ..., n-1, 0, 1, ..., b} (wraps around) -/
def CyclicInterval (n : ℕ) [NeZero n] (a b : Fin n) : Set (Fin n) :=
  if a.val ≤ b.val then
    {x | a.val ≤ x.val ∧ x.val ≤ b.val}
  else
    {x | a.val ≤ x.val ∨ x.val ≤ b.val}

notation "[" a ", " b "]_c" => CyclicInterval _ a b

/-- The cyclic distance from a to b (going in the positive direction) -/
def cyclicDist (n : ℕ) [NeZero n] (a b : Fin n) : ℕ :=
  if a.val ≤ b.val then b.val - a.val else n - a.val + b.val

/-- Membership in cyclic interval when a ≤ b -/
lemma mem_cyclicInterval_of_le {n : ℕ} [NeZero n] {a b x : Fin n} (hab : a.val ≤ b.val) :
    x ∈ CyclicInterval n a b ↔ a.val ≤ x.val ∧ x.val ≤ b.val := by
  simp only [CyclicInterval, if_pos hab, Set.mem_setOf_eq]

/-- Membership in cyclic interval when a > b (wraps around) -/
lemma mem_cyclicInterval_of_gt {n : ℕ} [NeZero n] {a b x : Fin n} (hab : b.val < a.val) :
    x ∈ CyclicInterval n a b ↔ a.val ≤ x.val ∨ x.val ≤ b.val := by
  simp only [CyclicInterval, if_neg (not_le.mpr hab), Set.mem_setOf_eq]

/-- A cyclic interval always contains its endpoints -/
lemma left_mem_cyclicInterval {n : ℕ} [NeZero n] (a b : Fin n) :
    a ∈ CyclicInterval n a b := by
  simp only [CyclicInterval]
  split_ifs with h
  · exact ⟨le_refl _, h⟩
  · left; exact le_refl _

lemma right_mem_cyclicInterval {n : ℕ} [NeZero n] (a b : Fin n) :
    b ∈ CyclicInterval n a b := by
  simp only [CyclicInterval]
  split_ifs with h
  · exact ⟨h, le_refl _⟩
  · right; exact le_refl _

/-- The size of a cyclic interval -/
lemma cyclicInterval_card {n : ℕ} [NeZero n] (a b : Fin n) :
    (CyclicInterval n a b).ncard = cyclicDist n a b + 1 := by
  simp only [CyclicInterval, cyclicDist]
  split_ifs with hab
  · -- Case: a.val ≤ b.val
    rw [Set.ncard_eq_toFinset_card']
    have heq : {x : Fin n | a.val ≤ x.val ∧ x.val ≤ b.val}.toFinset =
               Finset.univ.filter (fun x : Fin n => a.val ≤ x.val ∧ x.val ≤ b.val) := by
      ext x; simp
    rw [heq]
    have hcard : (Finset.univ.filter (fun x : Fin n => a.val ≤ x.val ∧ x.val ≤ b.val)).card =
                 b.val - a.val + 1 := by
      have hbij : (Finset.univ.filter (fun x : Fin n => a.val ≤ x.val ∧ x.val ≤ b.val)).card =
                  (Finset.Icc a.val b.val).card := by
        apply Finset.card_bij (fun x _ => x.val)
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp only [Finset.mem_Icc]
          exact hx
        · intro x1 _ x2 _ hval
          exact Fin.ext hval
        · intro i hi
          simp only [Finset.mem_Icc] at hi
          have hi_lt : i < n := Nat.lt_of_le_of_lt hi.2 b.isLt
          refine ⟨⟨i, hi_lt⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hi
      rw [hbij, Nat.card_Icc]
      omega
    exact hcard
  · -- Case: a.val > b.val (wrapping)
    push_neg at hab
    rw [Set.ncard_eq_toFinset_card']
    have heq : {x : Fin n | a.val ≤ x.val ∨ x.val ≤ b.val}.toFinset =
               Finset.univ.filter (fun x : Fin n => a.val ≤ x.val ∨ x.val ≤ b.val) := by
      ext x; simp
    rw [heq]
    -- Split into disjoint union
    have hcard : (Finset.univ.filter (fun x : Fin n => a.val ≤ x.val ∨ x.val ≤ b.val)).card =
                 n - a.val + b.val + 1 := by
      have hsplit : Finset.univ.filter (fun x : Fin n => a.val ≤ x.val ∨ x.val ≤ b.val) =
                    (Finset.univ.filter (fun x : Fin n => a.val ≤ x.val)) ∪
                    (Finset.univ.filter (fun x : Fin n => x.val ≤ b.val)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      have hdisj : Disjoint (Finset.univ.filter (fun x : Fin n => a.val ≤ x.val))
                           (Finset.univ.filter (fun x : Fin n => x.val ≤ b.val)) := by
        rw [Finset.disjoint_filter]
        intro x _ hax hxb
        omega
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
      -- Count part 1: {x | a.val ≤ x.val} has n - a.val elements
      have hcard1 : (Finset.univ.filter (fun x : Fin n => a.val ≤ x.val)).card = n - a.val := by
        have hbij1 : (Finset.univ.filter (fun x : Fin n => a.val ≤ x.val)).card =
                     (Finset.Ico a.val n).card := by
          apply Finset.card_bij (fun x _ => x.val)
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            simp only [Finset.mem_Ico]
            exact ⟨hx, x.isLt⟩
          · intro x1 _ x2 _ hval
            exact Fin.ext hval
          · intro i hi
            simp only [Finset.mem_Ico] at hi
            refine ⟨⟨i, hi.2⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hi.1
        rw [hbij1, Nat.card_Ico]
      -- Count part 2: {x | x.val ≤ b.val} has b.val + 1 elements
      have hcard2 : (Finset.univ.filter (fun x : Fin n => x.val ≤ b.val)).card = b.val + 1 := by
        have hbij2 : (Finset.univ.filter (fun x : Fin n => x.val ≤ b.val)).card =
                     (Finset.Iic b.val).card := by
          apply Finset.card_bij (fun x _ => x.val)
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            simp only [Finset.mem_Iic]
            exact hx
          · intro x1 _ x2 _ hval
            exact Fin.ext hval
          · intro i hi
            simp only [Finset.mem_Iic] at hi
            have hi_lt : i < n := Nat.lt_of_le_of_lt hi b.isLt
            refine ⟨⟨i, hi_lt⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hi
        rw [hbij2, Nat.card_Iic]
      omega
    exact hcard

/-- The symmetric cyclic distance (minimum of forward and backward distance) -/
def symCyclicDist (n : ℕ) [NeZero n] (a b : Fin n) : ℕ :=
  min (cyclicDist n a b) (cyclicDist n b a)

/-! ### Section 2: Convex-Round Enumeration -/

/-- A graph G on Fin n has a convex-round enumeration if each vertex's neighborhood
    forms a cyclic interval (contiguous arc) not containing the vertex itself.
    More precisely, for each vertex i, there exist l(i) and h(i) such that
    N(i) = [l(i), h(i)]_c \ {i} and i ∉ [l(i), h(i)]_c.
    This matches the paper's (BJH02) definition where the interval arc does not pass
    through the vertex. The condition i ∉ [l, h] ensures the neighborhood is a
    contiguous arc (no gap at the vertex). -/
structure IsConvexRoundEnum (n : ℕ) [NeZero n] (G : SimpleGraph (Fin n)) : Prop where
  /-- For each vertex, the neighborhood is a cyclic interval minus the vertex itself,
      and the vertex is outside the interval -/
  neighborhood_isInterval : ∀ i : Fin n, ∃ l h : Fin n,
    G.neighborSet i = CyclicInterval n l h \ {i} ∧ i ∉ CyclicInterval n l h

/-- A graph is convex-round if it admits some convex-round enumeration -/
def IsConvexRound {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (e : V ≃ Fin n), IsConvexRoundEnum n (G.map e.toEmbedding)

/-! ### Section 3: Fraction Graphs are Convex-Round -/

/-- The neighborhood of v in fractionGraph p q is {u | u ≠ v ∧ distMod p v u < q}. -/
lemma fractionGraph_neighborSet (p q : ℕ) [NeZero p] (v : ZMod p) :
    (fractionGraph p q).neighborSet v =
      {u | u ≠ v ∧ distMod p v u < q} := by
  ext u
  simp only [mem_neighborSet, Set.mem_setOf_eq]
  constructor
  · intro hadj
    simp only [fractionGraph] at hadj
    exact ⟨hadj.1.symm, hadj.2⟩
  · intro ⟨hne, hdist⟩
    simp only [fractionGraph]
    exact ⟨hne.symm, hdist⟩

/-- Helper: the Fin → ZMod equivalence -/
noncomputable def finZModEquiv (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun i := i.val
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv i := by simp only [ZMod.val_natCast_of_lt i.isLt, Fin.eta]
  right_inv z := ZMod.natCast_zmod_val z

/-- The inverse: ZMod → Fin equivalence -/
noncomputable def zmodFinEquiv (p : ℕ) [NeZero p] : ZMod p ≃ Fin p :=
  (finZModEquiv p).symm

/-- Adjacency in the mapped fractionGraph -/
lemma mapped_fractionGraph_adj (p q : ℕ) [NeZero p] (i j : Fin p) :
    ((fractionGraph p q).map (zmodFinEquiv p).toEmbedding).Adj i j ↔
    i ≠ j ∧ distMod p (finZModEquiv p i) (finZModEquiv p j) < q := by
  simp only [SimpleGraph.map_adj]
  constructor
  · intro ⟨a, b, hadj, hai, hbj⟩
    constructor
    · intro heq
      rw [heq] at hai
      have hinj := (zmodFinEquiv p).injective (hai.trans hbj.symm)
      simp only [fractionGraph] at hadj
      exact hadj.1 hinj
    · simp only [fractionGraph] at hadj
      have ha : a = finZModEquiv p i := by
        have h1 : zmodFinEquiv p a = i := hai
        calc a = finZModEquiv p (zmodFinEquiv p a) := by simp [zmodFinEquiv]
          _ = finZModEquiv p i := by rw [h1]
      have hb : b = finZModEquiv p j := by
        have h1 : zmodFinEquiv p b = j := hbj
        calc b = finZModEquiv p (zmodFinEquiv p b) := by simp [zmodFinEquiv]
          _ = finZModEquiv p j := by rw [h1]
      rw [ha, hb] at hadj
      exact hadj.2
  · intro ⟨hne, hdist⟩
    refine ⟨finZModEquiv p i, finZModEquiv p j, ?_, ?_, ?_⟩
    · simp only [fractionGraph]
      constructor
      · intro heq
        apply hne
        have : zmodFinEquiv p (finZModEquiv p i) = zmodFinEquiv p (finZModEquiv p j) := by rw [heq]
        simp only [zmodFinEquiv, Equiv.symm_apply_apply] at this
        exact this
      · exact hdist
    · simp only [zmodFinEquiv, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    · simp only [zmodFinEquiv, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

/-- The neighborSet in the mapped fractionGraph -/
lemma mapped_fractionGraph_neighborSet (p q : ℕ) [NeZero p] (i : Fin p) :
    ((fractionGraph p q).map (zmodFinEquiv p).toEmbedding).neighborSet i =
    {j : Fin p | j ≠ i ∧ distMod p (finZModEquiv p i) (finZModEquiv p j) < q} := by
  ext j
  simp only [SimpleGraph.mem_neighborSet, Set.mem_setOf_eq]
  constructor
  · intro hadj
    have h := (mapped_fractionGraph_adj p q i j).mp hadj
    exact ⟨h.1.symm, h.2⟩
  · intro ⟨hne, hdist⟩
    exact (mapped_fractionGraph_adj p q i j).mpr ⟨hne.symm, hdist⟩

/-- distMod < q iff within the cyclic interval of radius q-1.
    Key insight: distMod p x y = min(|x.val - y.val|, p - |x.val - y.val|) < q
    means the "closer" direction has distance at most q-1, which is exactly
    what membership in CyclicInterval [i-(q-1), i+(q-1)] captures. -/
lemma distMod_lt_iff_in_cyclic_interval (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    (i j : Fin p) :
    distMod p (finZModEquiv p i) (finZModEquiv p j) < q ↔
    j ∈ CyclicInterval p
        ⟨(i.val + p - (q - 1)) % p, Nat.mod_lt _ (NeZero.pos p)⟩
        ⟨(i.val + (q - 1)) % p, Nat.mod_lt _ (NeZero.pos p)⟩ := by
  -- The key is that distMod measures the minimum cyclic distance,
  -- and the cyclic interval [l, h] contains exactly those j with cyclic
  -- distance ≤ q-1 from i.
  let l : Fin p := ⟨(i.val + p - (q - 1)) % p, Nat.mod_lt _ (NeZero.pos p)⟩
  let h : Fin p := ⟨(i.val + (q - 1)) % p, Nat.mod_lt _ (NeZero.pos p)⟩
  -- distMod p (finZModEquiv p i) (finZModEquiv p j) = min(d, p - d)
  -- where d = ((i.val : ℕ) - j.val) mod p or similar
  -- This is < q iff the minimum is ≤ q-1
  -- The cyclic interval [l, h] around i contains j iff the "positive direction"
  -- distance from i to j is ≤ q-1, OR the "negative direction" distance is ≤ q-1.
  have hp_pos : 0 < p := NeZero.pos p
  have hi_lt : i.val < p := i.isLt
  have hj_lt : j.val < p := j.isLt
  have hj_le_ip : j.val ≤ i.val + p := by omega
  have hfze_i : finZModEquiv p i = (i.val : ZMod p) := rfl
  have hfze_j : finZModEquiv p j = (j.val : ZMod p) := rfl
  have hcast_eq : (↑i.val - ↑j.val : ZMod p) = ↑(i.val + p - j.val) := by
    rw [Nat.cast_sub hj_le_ip, Nat.cast_add]
    rw [show (p : ZMod p) = 0 from ZMod.natCast_self p, add_zero]
  have hd_eq : (finZModEquiv p i - finZModEquiv p j).val =
      (i.val + p - j.val) % p := by
    rw [hfze_i, hfze_j, hcast_eq, ZMod.val_natCast]
  rw [show distMod p (finZModEquiv p i) (finZModEquiv p j) =
      min ((i.val + p - j.val) % p) (p - (i.val + p - j.val) % p) from by
    simp only [distMod, hd_eq]]
  set d := (i.val + p - j.val) % p with hd_def
  have hd_lt_p : d < p := Nat.mod_lt _ hp_pos
  rw [show min d (p - d) < q ↔ (d ≤ q - 1 ∨ d ≥ p - (q - 1)) from by
    constructor
    · intro hmlt
      by_contra habs; push_neg at habs
      have hd_ge_q : d ≥ q := by omega
      have hpd_ge_q : p - d ≥ q := by omega
      exact not_lt.mpr (Nat.le_min.mpr ⟨hd_ge_q, hpd_ge_q⟩) hmlt
    · rintro (hlt | hgt)
      · exact lt_of_le_of_lt (min_le_left d (p - d)) (by omega)
      · exact lt_of_le_of_lt (min_le_right d (p - d)) (by omega)]
  have hd_cases : (j.val ≤ i.val ∧ d = i.val - j.val) ∨
      (i.val < j.val ∧ d = i.val + p - j.val) := by
    by_cases hjle : j.val ≤ i.val
    · left; exact ⟨hjle, by
        rw [hd_def,
          show i.val + p - j.val = (i.val - j.val) + p from by omega,
          Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)⟩
    · right; exact ⟨by omega, by
        rw [hd_def]; exact Nat.mod_eq_of_lt (by omega)⟩
  have hl_cases : (q - 1 ≤ i.val ∧ l.val = i.val - (q - 1)) ∨
      (i.val < q - 1 ∧ l.val = i.val + p - (q - 1)) := by
    by_cases hle : q - 1 ≤ i.val
    · left; refine ⟨hle, ?_⟩
      change (i.val + p - (q - 1)) % p = i.val - (q - 1)
      rw [show i.val + p - (q - 1) = (i.val - (q - 1)) + p from by omega,
        Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    · right; exact ⟨by omega, by
        change (i.val + p - (q - 1)) % p = i.val + p - (q - 1)
        exact Nat.mod_eq_of_lt (by omega)⟩
  have hh_cases : (i.val + (q - 1) < p ∧ h.val = i.val + (q - 1)) ∨
      (p ≤ i.val + (q - 1) ∧ h.val = i.val + (q - 1) - p) := by
    by_cases hlt : i.val + (q - 1) < p
    · left; exact ⟨hlt, by
        change (i.val + (q - 1)) % p = i.val + (q - 1)
        exact Nat.mod_eq_of_lt hlt⟩
    · right; exact ⟨by omega, by
        change (i.val + (q - 1)) % p = i.val + (q - 1) - p
        rw [Nat.mod_eq_sub_mod (by omega)]
        exact Nat.mod_eq_of_lt (by omega)⟩
  rcases hl_cases with ⟨hl_ge, hl_eq⟩ | ⟨hl_lt, hl_eq⟩
  · rcases hh_cases with ⟨hh_lt, hh_eq⟩ | ⟨hh_ge, hh_eq⟩
    · rcases hd_cases with ⟨hd_jle, hd_eq'⟩ | ⟨hd_jgt, hd_eq'⟩
      · rw [mem_cyclicInterval_of_le
          (show l.val ≤ h.val by rw [hl_eq, hh_eq]; omega)]
        simp only [hl_eq, hh_eq, hd_eq']
        exact ⟨fun h1 => h1.elim
          (fun h1 => ⟨by omega, by omega⟩)
          (fun h1 => absurd h1 (by omega)),
          fun ⟨h1, h2⟩ => Or.inl (by omega)⟩
      · rw [mem_cyclicInterval_of_le
          (show l.val ≤ h.val by rw [hl_eq, hh_eq]; omega)]
        simp only [hl_eq, hh_eq, hd_eq']
        exact ⟨fun h1 => h1.elim
          (fun h1 => absurd h1 (by omega))
          (fun h1 => ⟨by omega, by omega⟩),
          fun ⟨h1, h2⟩ => Or.inr (by omega)⟩
    · rcases hd_cases with ⟨hd_jle, hd_eq'⟩ | ⟨hd_jgt, hd_eq'⟩
      · rw [mem_cyclicInterval_of_gt
          (show h.val < l.val by rw [hl_eq, hh_eq]; omega)]
        simp only [hl_eq, hh_eq, hd_eq']
        exact ⟨fun h1 => h1.elim
          (fun h1 => Or.inl (by omega))
          (fun h1 => Or.inr (by omega)),
          fun h1 => h1.elim
          (fun h1 => Or.inl (by omega))
          (fun h1 => Or.inr (by omega))⟩
      · rw [mem_cyclicInterval_of_gt
          (show h.val < l.val by rw [hl_eq, hh_eq]; omega)]
        simp only [hl_eq, hh_eq, hd_eq']
        exact ⟨fun h1 => h1.elim
          (fun h1 => Or.inl (by omega))
          (fun h1 => Or.inl (by omega)),
          fun h1 => h1.elim
          (fun h1 => Or.inr (by omega))
          (fun h1 => absurd h1 (by omega))⟩
  · rcases hh_cases with ⟨hh_lt, hh_eq⟩ | ⟨hh_ge, hh_eq⟩
    · rcases hd_cases with ⟨hd_jle, hd_eq'⟩ | ⟨hd_jgt, hd_eq'⟩
      · rw [mem_cyclicInterval_of_gt
          (show h.val < l.val by rw [hl_eq, hh_eq]; omega)]
        simp only [hl_eq, hh_eq, hd_eq']
        exact ⟨fun h1 => h1.elim
          (fun h1 => Or.inr (by omega))
          (fun h1 => absurd h1 (by omega)),
          fun h1 => h1.elim
          (fun h1 => absurd h1 (by omega))
          (fun h1 => Or.inl (by omega))⟩
      · rw [mem_cyclicInterval_of_gt
          (show h.val < l.val by rw [hl_eq, hh_eq]; omega)]
        simp only [hl_eq, hh_eq, hd_eq']
        exact ⟨fun h1 => h1.elim
          (fun h1 => Or.inl (by omega))
          (fun h1 => Or.inr (by omega)),
          fun h1 => h1.elim
          (fun h1 => Or.inl (by omega))
          (fun h1 => Or.inr (by omega))⟩
    · rcases hd_cases with ⟨hd_jle, hd_eq'⟩ | ⟨hd_jgt, hd_eq'⟩
      · exfalso; omega
      · exfalso; omega

/-- Membership in a cyclic interval is translation-invariant: shifting all three
    arguments (x, a, b) by the same amount preserves membership. -/
private lemma cyclicDist_add_right {n : ℕ} [NeZero n] (a b c : Fin n) :
    cyclicDist n (a + c) (b + c) = cyclicDist n a b := by
  simp only [cyclicDist]
  -- cyclicDist uses val comparisons. We need:
  -- if a.val ≤ b.val then b.val - a.val else n - a.val + b.val
  -- equals
  -- if (a+c).val ≤ (b+c).val then (b+c).val - (a+c).val else n - (a+c).val + (b+c).val
  -- Key: (a+c).val = (a.val + c.val) % n, similarly for b+c
  have hn_pos : 0 < n := NeZero.pos n
  set av := a.val; set bv := b.val; set cv := c.val
  have ha : av < n := a.isLt
  have hb : bv < n := b.isLt
  have hc : cv < n := c.isLt
  have hac : (a + c).val = (av + cv) % n := Fin.val_add a c
  have hbc : (b + c).val = (bv + cv) % n := Fin.val_add b c
  -- Case split on whether av + cv < n and bv + cv < n
  by_cases hac_wrap : av + cv < n <;> by_cases hbc_wrap : bv + cv < n
  · -- Neither wraps
    rw [hac, hbc, Nat.mod_eq_of_lt (by omega : av + cv < n),
        Nat.mod_eq_of_lt (by omega : bv + cv < n)]
    split_ifs <;> omega
  · -- a+c doesn't wrap, b+c wraps
    rw [hac, hbc, Nat.mod_eq_of_lt (by omega : av + cv < n)]
    have : (bv + cv) % n = bv + cv - n := by
      rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    rw [this]
    split_ifs <;> omega
  · -- a+c wraps, b+c doesn't
    rw [hac, hbc, Nat.mod_eq_of_lt (by omega : bv + cv < n)]
    have : (av + cv) % n = av + cv - n := by
      rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    rw [this]
    split_ifs <;> omega
  · -- Both wrap
    rw [hac, hbc]
    have ha' : (av + cv) % n = av + cv - n := by
      rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    have hb' : (bv + cv) % n = bv + cv - n := by
      rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    rw [ha', hb']
    split_ifs <;> omega

lemma mem_cyclicInterval_iff_cyclicDist {n : ℕ} [NeZero n] (x a b : Fin n) :
    x ∈ CyclicInterval n a b ↔ cyclicDist n a x ≤ cyclicDist n a b := by
  have hn_pos : 0 < n := NeZero.pos n
  have ha : a.val < n := a.isLt
  have hb : b.val < n := b.isLt
  have hx : x.val < n := x.isLt
  -- Compute cyclicDist explicitly in each case
  by_cases hab : a.val ≤ b.val <;> by_cases hax : a.val ≤ x.val
  · -- a ≤ b, a ≤ x
    rw [mem_cyclicInterval_of_le hab]
    have hdab : cyclicDist n a b = b.val - a.val := by
      simp only [cyclicDist, if_pos hab]
    have hdax : cyclicDist n a x = x.val - a.val := by
      simp only [cyclicDist, if_pos hax]
    rw [hdab, hdax]; omega
  · -- a ≤ b, x < a
    rw [mem_cyclicInterval_of_le hab]
    have hdab : cyclicDist n a b = b.val - a.val := by
      simp only [cyclicDist, if_pos hab]
    have hdax : cyclicDist n a x = n - a.val + x.val := by
      simp only [cyclicDist, if_neg hax]
    rw [hdab, hdax]
    push_neg at hax; omega
  · -- b < a, a ≤ x
    push_neg at hab
    rw [mem_cyclicInterval_of_gt hab]
    have hdab : cyclicDist n a b = n - a.val + b.val := by
      simp only [cyclicDist, if_neg (by omega : ¬(a.val ≤ b.val))]
    have hdax : cyclicDist n a x = x.val - a.val := by
      simp only [cyclicDist, if_pos hax]
    rw [hdab, hdax]
    constructor
    · intro _; omega
    · intro _; left; exact hax
  · -- b < a, x < a
    push_neg at hab hax
    rw [mem_cyclicInterval_of_gt (by omega : b.val < a.val)]
    have hdab : cyclicDist n a b = n - a.val + b.val := by
      simp only [cyclicDist, if_neg (by omega : ¬(a.val ≤ b.val))]
    have hdax : cyclicDist n a x = n - a.val + x.val := by
      simp only [cyclicDist, if_neg (by omega : ¬(a.val ≤ x.val))]
    rw [hdab, hdax]
    constructor
    · rintro (h1 | h2)
      · omega
      · omega
    · intro h; right; omega

private lemma mem_cyclicInterval_add_iff {n : ℕ} [NeZero n] (x a b : Fin n) (c : Fin n) :
    x ∈ CyclicInterval n a b ↔ (x + c) ∈ CyclicInterval n (a + c) (b + c) := by
  rw [mem_cyclicInterval_iff_cyclicDist, mem_cyclicInterval_iff_cyclicDist,
      cyclicDist_add_right, cyclicDist_add_right]

/-- Special case: shifting by 1. -/
private lemma mem_cyclicInterval_add_one_iff {n : ℕ} [NeZero n] (x a b : Fin n) :
    x ∈ CyclicInterval n a b ↔ (x + 1) ∈ CyclicInterval n (a + 1) (b + 1) :=
  mem_cyclicInterval_add_iff x a b 1

/-- Triangle equality for cyclicDist: if b ∈ [a, c], then
    cyclicDist a c = cyclicDist a b + cyclicDist b c. -/
lemma cyclicDist_triangle {n : ℕ} [NeZero n] {a b c : Fin n}
    (h : b ∈ CyclicInterval n a c) :
    cyclicDist n a c = cyclicDist n a b + cyclicDist n b c := by
  rw [mem_cyclicInterval_iff_cyclicDist] at h
  simp only [cyclicDist] at *
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  have hn_pos : 0 < n := NeZero.pos n
  split_ifs at h ⊢ <;> omega

/-- The total cyclicDist around a pair sums to n:
    cyclicDist a b + cyclicDist b a = n for a ≠ b. -/
lemma cyclicDist_add_reverse {n : ℕ} [NeZero n] {a b : Fin n} (hab : a ≠ b) :
    cyclicDist n a b + cyclicDist n b a = n := by
  simp only [cyclicDist]
  have _ha := a.isLt; have _hb := b.isLt
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  split_ifs <;> omega

/-- Fin n: i + 1 ≠ i when n ≥ 2. -/
private lemma fin_succ_ne {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) : i + 1 ≠ i := by
  intro h
  have hv := congr_arg Fin.val h
  simp only [Fin.val_add] at hv
  have h1v : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  rw [h1v] at hv
  have hi := i.isLt
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hv; omega

/-- Cyclic interval subset: if a ∈ [c, d] and the distance from c through a to b
    fits within [c, d], then [a, b] ⊆ [c, d]. -/
lemma cyclicInterval_subset {n : ℕ} [NeZero n] {a b c d : Fin n}
    (_ha : a ∈ CyclicInterval n c d)
    (hbd : cyclicDist n c a + cyclicDist n a b ≤ cyclicDist n c d) :
    CyclicInterval n a b ⊆ CyclicInterval n c d := by
  intro x hx
  rw [mem_cyclicInterval_iff_cyclicDist] at hx ⊢
  by_cases hcax : cyclicDist n c a ≤ cyclicDist n c x
  · -- a ∈ [c, x]: use triangle equality
    have ha_cx : a ∈ CyclicInterval n c x := by
      rw [mem_cyclicInterval_iff_cyclicDist]; exact hcax
    rw [cyclicDist_triangle ha_cx]
    calc cyclicDist n c a + cyclicDist n a x
        ≤ cyclicDist n c a + cyclicDist n a b := by omega
      _ ≤ cyclicDist n c d := hbd
  · -- x ∈ [c, a): cyclicDist c x < cyclicDist c a ≤ cyclicDist c d
    push_neg at hcax; omega

/-- If c ∈ [a, b] ∩ [b, a] with a ≠ b and n ≥ 3, then c = a ∨ c = b. -/
private lemma mem_both_arcs_eq {n : ℕ} [NeZero n] (_hn : 3 ≤ n)
    {a b c : Fin n} (hab : a ≠ b)
    (h1 : c ∈ CyclicInterval n a b) (h2 : c ∈ CyclicInterval n b a) :
    c = a ∨ c = b := by
  rw [mem_cyclicInterval_iff_cyclicDist] at h1 h2
  by_contra h_neg; push_neg at h_neg; obtain ⟨hca, hcb⟩ := h_neg
  have htri := cyclicDist_triangle ((mem_cyclicInterval_iff_cyclicDist c a b).mpr h1)
  have hrev_bc := cyclicDist_add_reverse hcb.symm
  have hrev := cyclicDist_add_reverse hab
  have hac_zero : cyclicDist n a c = 0 := by omega
  simp only [cyclicDist] at hac_zero
  have := a.isLt; have := c.isLt
  split_ifs at hac_zero with h <;> exact hca (Fin.ext (by omega))

/-- Every element of Fin n is in [a, b] or [b, a]. -/
private lemma mem_arc_or {n : ℕ} [NeZero n] {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    c ∈ CyclicInterval n a b ∨ c ∈ CyclicInterval n b a := by
  simp only [CyclicInterval]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  split_ifs with h1 h2 h2 <;> simp only [Set.mem_setOf_eq] <;> omega

/-- A cyclic interval [lc, hc] that avoids two distinct points a and b cannot
    simultaneously contain a point from [a,b] and a point from [b,a]
    (other than a and b themselves). -/
private lemma no_straddle_arcs {n : ℕ} [NeZero n] (hn3 : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {lc hc : Fin n} (ha_out : a ∉ CyclicInterval n lc hc) (hb_out : b ∉ CyclicInterval n lc hc)
    {x y : Fin n} (hx_lh : x ∈ CyclicInterval n lc hc) (hy_lh : y ∈ CyclicInterval n lc hc)
    (hx_ab : x ∈ CyclicInterval n a b) (hy_ba : y ∈ CyclicInterval n b a)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) : False := by
  have htri_axb := cyclicDist_triangle hx_ab
  have htri_bya := cyclicDist_triangle hy_ba
  have hab_rev := cyclicDist_add_reverse hab
  have hxy_ne : x ≠ y := by
    intro heq; subst heq
    rcases mem_both_arcs_eq hn3 hab hx_ab hy_ba with heq | heq
    · exact hxa heq
    · exact hxb heq
  have hya_pos : 0 < cyclicDist n y a := by
    simp only [cyclicDist]; have := y.isLt; have := a.isLt
    have : y.val ≠ a.val := fun h => hya (Fin.ext h); split_ifs <;> omega
  have hax_pos : 0 < cyclicDist n a x := by
    simp only [cyclicDist]; have := a.isLt; have := x.isLt
    have : a.val ≠ x.val := fun h => hxa (Fin.ext h).symm; split_ifs <;> omega
  have four_sum : cyclicDist n a x + cyclicDist n x b +
      cyclicDist n b y + cyclicDist n y a = n := by omega
  have hb_in_xy : b ∈ CyclicInterval n x y := by
    rcases mem_arc_or hxy_ne b with hb_xy | hb_yx
    · exact hb_xy
    · exfalso
      have htri_ybx := cyclicDist_triangle hb_yx
      have hxy_rev := cyclicDist_add_reverse hxy_ne
      have hxb_rev := cyclicDist_add_reverse hxb
      have hyb_rev := cyclicDist_add_reverse hyb
      omega
  have ha_in_yx : a ∈ CyclicInterval n y x := by
    rcases mem_arc_or hxy_ne.symm a with ha_yx | ha_xy
    · exact ha_yx
    · exfalso
      have htri_xay := cyclicDist_triangle ha_xy
      have hxy_rev := cyclicDist_add_reverse hxy_ne
      have hxa_rev := cyclicDist_add_reverse hxa.symm
      have hya_rev := cyclicDist_add_reverse hya
      have hxb_zero : cyclicDist n x b = 0 := by omega
      simp only [cyclicDist] at hxb_zero
      have := x.isLt; have := b.isLt
      have : x.val ≠ b.val := fun h => hxb (Fin.ext h)
      split_ifs at hxb_zero <;> omega
  rw [mem_cyclicInterval_iff_cyclicDist] at hx_lh hy_lh
  by_cases h_order : cyclicDist n lc x ≤ cyclicDist n lc y
  · have hx_in_lcy : x ∈ CyclicInterval n lc y :=
      (mem_cyclicInterval_iff_cyclicDist x lc y).mpr h_order
    have htri_lxy := cyclicDist_triangle hx_in_lcy
    exact hb_out (cyclicInterval_subset
      ((mem_cyclicInterval_iff_cyclicDist x lc hc).mpr hx_lh)
      (show cyclicDist n lc x + cyclicDist n x y ≤ cyclicDist n lc hc by omega)
      hb_in_xy)
  · push_neg at h_order
    have hy_in_lcx : y ∈ CyclicInterval n lc x :=
      (mem_cyclicInterval_iff_cyclicDist y lc x).mpr (by omega)
    have htri_lyx := cyclicDist_triangle hy_in_lcx
    exact ha_out (cyclicInterval_subset
      ((mem_cyclicInterval_iff_cyclicDist y lc hc).mpr hy_lh)
      (show cyclicDist n lc y + cyclicDist n y x ≤ cyclicDist n lc hc by omega)
      ha_in_yx)

-- BHY00 Lemma 3.7 cases 3&4: Forward declaration (proved after connectivity lemma).
-- When neighborhoods of non-adjacent c, d are on opposite sides, G is bipartite.
-- Proof follows after convexRound_preconnected_of_not_bipartite.

-- BHY00 Corollary 3.10: A non-bipartite convex-round graph is connected.
set_option maxHeartbeats 1600000 in -- needed for convex-round connectivity argument
private lemma convexRound_preconnected_of_not_bipartite {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n)) (hCR : IsConvexRoundEnum n G) (hnotBip : ¬G.IsBipartite) :
    G.Preconnected := by
  by_contra hnotConn
  apply hnotBip
  rw [SimpleGraph.Preconnected] at hnotConn
  push_neg at hnotConn
  obtain ⟨u₀, v₀, hnotReach⟩ := hnotConn
  choose l hi hlhi using hCR.neighborhood_isInterval
  have hlh : ∀ j, G.neighborSet j = CyclicInterval n (l j) (hi j) \ {j} := fun j => (hlhi j).1
  have hcanon : ∀ j, j ∉ CyclicInterval n (l j) (hi j) := fun j => (hlhi j).2
  have hadj_iff : ∀ a b : Fin n, G.Adj a b ↔ b ∈ CyclicInterval n (l a) (hi a) ∧ b ≠ a := by
    intro a b; rw [show G.Adj a b ↔ b ∈ G.neighborSet a from Iff.rfl, hlh a]
    simp [Set.mem_diff, Set.mem_singleton_iff]
  have hReach_outside : ∀ w t₀ : Fin n, G.Reachable u₀ w → ¬G.Reachable u₀ t₀ →
      w ∉ CyclicInterval n (l t₀) (hi t₀) := by
    intro w t₀ hw ht₀ hmem
    by_cases hwt₀ : w = t₀
    · exact ht₀ (hwt₀ ▸ hw)
    · exact ht₀ (hw.trans (((hadj_iff t₀ w).mpr ⟨hmem, hwt₀⟩).symm).reachable)
  have hNotReach_outside : ∀ w s₀ : Fin n, ¬G.Reachable u₀ w → G.Reachable u₀ s₀ →
      w ∉ CyclicInterval n (l s₀) (hi s₀) := by
    intro w s₀ hw hs₀ hmem
    by_cases hws₀ : w = s₀
    · exact hw (hws₀ ▸ hs₀)
    · exact hw (hs₀.trans ((hadj_iff s₀ w).mpr ⟨hmem, hws₀⟩).reachable)
  -- Use two_colorable_iff_forall_loop_even
  rw [show G.IsBipartite = G.Colorable 2 from rfl, two_colorable_iff_forall_loop_even]
  intro u
  -- Pick reference vertex outside u's component
  have hRef : ∃ t₀ : Fin n, ¬G.Reachable u t₀ := by
    rcases Classical.em (G.Reachable u₀ u) with hreach | hunreach
    · exact ⟨v₀, fun h => hnotReach (hreach.trans h)⟩
    · exact ⟨u₀, fun h => hunreach h.symm⟩
  obtain ⟨t₀, ht₀⟩ := hRef
  -- Define facing function as Bool for cleaner reasoning
  let g : Fin n → Bool := fun i =>
    decide (cyclicDist n (hi t₀ + 1) (l i) < cyclicDist n (hi t₀ + 1) i)
  -- Key: g flips at each edge where both endpoints are not reachable from t₀
  -- This uses the geometric argument: within the complement arc of [l(t₀), h(t₀)],
  -- adjacent vertices have opposite "facing" (l on different sides)
  -- Unreachable vertices lie outside t₀'s interval
  have hunreach_outside : ∀ a : Fin n, ¬G.Reachable a t₀ →
      a ∉ CyclicInterval n (l t₀) (hi t₀) := by
    intro a ha hmem
    by_cases hat₀ : a = t₀
    · exact ha (hat₀ ▸ ⟨.nil⟩)
    · exact ha (((hadj_iff t₀ a).mpr ⟨hmem, hat₀⟩).symm.reachable)
  -- t₀ is outside the interval of any unreachable vertex
  have ht₀_outside : ∀ a : Fin n, ¬G.Reachable a t₀ →
      t₀ ∉ CyclicInterval n (l a) (hi a) := by
    intro a ha hmem
    by_cases hat₀ : t₀ = a
    · exact ha (hat₀ ▸ ⟨.nil⟩)
    · exact ha ((hadj_iff a t₀).mpr ⟨hmem, hat₀⟩).reachable
  -- Interval of unreachable vertex is disjoint from t₀'s interval
  have hunreach_disjoint : ∀ a : Fin n, ¬G.Reachable a t₀ →
      ∀ w, w ∈ CyclicInterval n (l a) (hi a) → w ∉ CyclicInterval n (l t₀) (hi t₀) := by
    intro a ha w hw hmemw
    by_cases hwa : w = a
    · exact hunreach_outside a ha (hwa ▸ hmemw)
    by_cases hwt₀ : w = t₀
    · exact ht₀_outside a ha (hwt₀ ▸ hw)
    · exact ha (((hadj_iff a w).mpr ⟨hw, hwa⟩).reachable.trans
        ((hadj_iff t₀ w).mpr ⟨hmemw, hwt₀⟩).symm.reachable)
  set r := hi t₀ + 1 with hr_def
  have hn_pos : 0 < n := NeZero.pos n
  -- Establish r.val concretely for omega: either (hi t₀).val + 1 or 0
  have hr_cases : (r.val = (hi t₀).val + 1 ∧ (hi t₀).val + 1 < n) ∨
                  (r.val = 0 ∧ (hi t₀).val = n - 1) := by
    have hhi := (hi t₀).isLt
    by_cases h : (hi t₀).val + 1 < n
    · left; exact ⟨show r.val = _ from Fin.val_add_one_of_lt' h, h⟩
    · right
      have heq : (hi t₀).val = n - 1 := by omega
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hlast : hi t₀ = Fin.last m := by ext; simp [Fin.last]; omega
      exact ⟨show r.val = _ by rw [show r = hi t₀ + 1 from rfl, hlast,
        Fin.val_add_one, if_pos rfl], heq⟩
  -- t₀ ∉ [l t₀, hi t₀] gives a size bound on the interval
  have ht₀c := hcanon t₀
  rw [mem_cyclicInterval_iff_cyclicDist] at ht₀c; push_neg at ht₀c
  -- Points outside [l t₀, hi t₀] have cyclicDist from r < cyclicDist r (l t₀)
  have hgap_dist : ∀ x : Fin n, x ∉ CyclicInterval n (l t₀) (hi t₀) →
      cyclicDist n r x < cyclicDist n r (l t₀) := by
    intro x hx
    rw [mem_cyclicInterval_iff_cyclicDist] at hx; push_neg at hx
    simp only [cyclicDist] at hx ht₀c ⊢
    rcases hr_cases with ⟨hrv, _⟩ | ⟨hrv, hhi_eq⟩ <;>
      (split_ifs at hx ht₀c ⊢ <;> omega)
  -- For x ∈ [l a, hi a] with a unreachable:
  -- cyclicDist r (l a) ≤ cyclicDist r x ≤ cyclicDist r (hi a)
  have hgap_bounds : ∀ (a x : Fin n), ¬G.Reachable a t₀ →
      x ∈ CyclicInterval n (l a) (hi a) →
      cyclicDist n r (l a) ≤ cyclicDist n r x ∧
      cyclicDist n r x ≤ cyclicDist n r (hi a) := by
    intro a x ha hx
    rw [mem_cyclicInterval_iff_cyclicDist] at hx
    have hla_gap := hgap_dist (l a) (hunreach_disjoint a ha (l a) (left_mem_cyclicInterval _ _))
    have hha_gap := hgap_dist (hi a) (hunreach_disjoint a ha (hi a) (right_mem_cyclicInterval _ _))
    have hx_gap := hgap_dist x (hunreach_disjoint a ha x
      ((mem_cyclicInterval_iff_cyclicDist x (l a) (hi a)).mpr hx))
    have hlt₀_out : l t₀ ∉ CyclicInterval n (l a) (hi a) := by
      intro hmem; exact hunreach_disjoint a ha (l t₀) hmem (left_mem_cyclicInterval _ _)
    rw [mem_cyclicInterval_iff_cyclicDist] at hlt₀_out; push_neg at hlt₀_out
    -- Unfold cyclicDist only in local facts (not ht₀c, to reduce case explosion)
    simp only [cyclicDist] at hx hla_gap hha_gap hx_gap hlt₀_out ⊢
    rcases hr_cases with ⟨hrv, _⟩ | ⟨hrv, hhi_eq⟩ <;>
      (constructor <;> (split_ifs at hx hla_gap hha_gap hx_gap hlt₀_out ⊢ <;> omega))
  -- a ∉ [l a, hi a] means cyclicDist r a is outside [cyclicDist r (l a), cyclicDist r (hi a)]
  have hunreach_a_pos : ∀ a : Fin n, ¬G.Reachable a t₀ →
      cyclicDist n r a < cyclicDist n r (l a) ∨
      cyclicDist n r (hi a) < cyclicDist n r a := by
    intro a ha
    have ha_out := hcanon a
    rw [mem_cyclicInterval_iff_cyclicDist] at ha_out; push_neg at ha_out
    have hla_gap := hgap_dist (l a) (hunreach_disjoint a ha (l a) (left_mem_cyclicInterval _ _))
    have hha_gap := hgap_dist (hi a) (hunreach_disjoint a ha (hi a) (right_mem_cyclicInterval _ _))
    have ha_gap := hgap_dist a (hunreach_outside a ha)
    have hlt₀_out : l t₀ ∉ CyclicInterval n (l a) (hi a) := by
      intro hmem; exact hunreach_disjoint a ha (l t₀) hmem (left_mem_cyclicInterval _ _)
    rw [mem_cyclicInterval_iff_cyclicDist] at hlt₀_out; push_neg at hlt₀_out
    simp only [cyclicDist] at ha_out hla_gap hha_gap ha_gap hlt₀_out ⊢
    rcases hr_cases with ⟨hrv, _⟩ | ⟨hrv, hhi_eq⟩ <;>
      (split_ifs at ha_out hla_gap hha_gap ha_gap hlt₀_out ⊢ <;> omega)
  -- Main: g flips at each edge between unreachable vertices
  have hflip_g : ∀ a b, G.Adj a b → ¬G.Reachable a t₀ → ¬G.Reachable b t₀ →
      g a ≠ g b := by
    intro a b hadj ha hb
    have hb_in_a : b ∈ CyclicInterval n (l a) (hi a) := ((hadj_iff a b).mp hadj).1
    have ha_in_b : a ∈ CyclicInterval n (l b) (hi b) := ((hadj_iff b a).mp hadj.symm).1
    obtain ⟨hla_le_b, hb_le_ha⟩ := hgap_bounds a b ha hb_in_a
    obtain ⟨hlb_le_a, ha_le_hb⟩ := hgap_bounds b a hb ha_in_b
    -- cyclicDist r a ≠ cyclicDist r b (injective on the gap)
    have hdr_ne : cyclicDist n r a ≠ cyclicDist n r b := by
      intro heq; simp only [cyclicDist] at heq
      split_ifs at heq <;> exact hadj.ne (Fin.ext (by omega))
    by_cases hab_lt : cyclicDist n r a < cyclicDist n r b
    · -- g b = true: cyclicDist r (l b) ≤ cyclicDist r a < cyclicDist r b
      have hgb : g b = true := by
        simp only [g, decide_eq_true_eq]; exact lt_of_le_of_lt hlb_le_a hab_lt
      -- g a = false: must have cyclicDist r a < cyclicDist r (l a)
      have hga : g a = false := by
        simp only [g, decide_eq_false_iff_not, not_lt]
        rcases hunreach_a_pos a ha with h | h
        · exact le_of_lt h
        · exact absurd (lt_of_le_of_lt hb_le_ha h) (not_lt.mpr (le_of_lt hab_lt))
      rw [hga, hgb]; decide
    · -- cyclicDist r b < cyclicDist r a
      have hlt : cyclicDist n r b < cyclicDist n r a :=
        lt_of_le_of_ne (Nat.le_of_not_lt hab_lt) (Ne.symm hdr_ne)
      -- g a = true
      have hga : g a = true := by
        simp only [g, decide_eq_true_eq]; exact lt_of_le_of_lt hla_le_b hlt
      -- g b = false
      have hgb : g b = false := by
        simp only [g, decide_eq_false_iff_not, not_lt]
        rcases hunreach_a_pos b hb with h | h
        · exact le_of_lt h
        · exact absurd (lt_of_le_of_lt ha_le_hb h) (not_lt.mpr (le_of_lt hlt))
      rw [hga, hgb]; decide
  -- Helper: vertices on a walk from a are reachable from a
  have walk_support_reachable : ∀ {a b : Fin n} (p : G.Walk a b) (x : Fin n),
      x ∈ p.support → G.Reachable a x := by
    intro a b p x hx
    induction p with
    | nil =>
      simp only [SimpleGraph.Walk.support, List.mem_singleton] at hx
      subst hx
      exact ⟨.nil⟩
    | @cons u' v' w' hadj' rest ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨.nil⟩
      · exact hadj'.reachable.trans (ih hx)
  -- Generalized walk parity: along any walk where all vertices are not reachable
  -- from t₀, the length parity equals whether g-values at endpoints agree
  have h_gen : ∀ {a b : Fin n} (p : G.Walk a b),
      (∀ x ∈ p.support, ¬G.Reachable x t₀) →
      (Even p.length ↔ (g a = g b)) := by
    intro a b p hsup
    induction p with
    | nil => simp
    | @cons a' v' b' hadj' rest ih =>
      have ha' : ¬G.Reachable a' t₀ :=
        hsup a' (by simp [SimpleGraph.Walk.support_cons])
      have hv' : ¬G.Reachable v' t₀ :=
        hsup v' (List.mem_cons_of_mem a' (SimpleGraph.Walk.start_mem_support rest))
      have hrest_sup : ∀ x ∈ rest.support, ¬G.Reachable x t₀ :=
        fun x hx => hsup x (List.mem_cons_of_mem a' hx)
      rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih hrest_sup]
      have hne_ab := hflip_g a' v' hadj' ha' hv'
      cases ha : g a' <;> cases hv : g v' <;> cases hb : g b' <;> simp_all
  -- Apply to closed walk: all support vertices are reachable from u, hence
  -- not reachable from t₀
  intro w
  refine (h_gen w (fun x hx => ?_)).mpr rfl
  exact fun hreach => ht₀ ((walk_support_reachable w x hx).trans hreach)

-- BHY00 Lemma 3.7 cases 3&4: When neighborhoods of non-adjacent c, d are on
-- opposite sides, G is bipartite.
-- Handles both orientations: neighborhoods facing towards or away from each other.
-- Key insight: [l(x), h(x)] cannot contain both c and d (since c adj d is false),
-- so we can use c or d as a reference for the g-function coloring.
set_option maxHeartbeats 1600000 in -- needed for bipartite characterization proof
private lemma opposite_sides_bipartite {n : ℕ} [NeZero n] (hn3 : 3 ≤ n)
    (G : SimpleGraph (Fin n))
    (hCR : IsConvexRoundEnum n G)
    {c d : Fin n} (hne : c ≠ d) (hnadj : ¬G.Adj c d)
    (h : (G.neighborSet c ⊆ ↑(CyclicInterval n c d) ∧
          G.neighborSet d ⊆ ↑(CyclicInterval n d c)) ∨
         (G.neighborSet c ⊆ ↑(CyclicInterval n d c) ∧
          G.neighborSet d ⊆ ↑(CyclicInterval n c d))) :
    G.IsBipartite := by
  -- Proof by contradiction: assume not bipartite, get connectivity, then derive bipartite.
  by_contra hnotBip
  apply hnotBip
  have hconn := convexRound_preconnected_of_not_bipartite G hCR hnotBip
  -- Extract the convex-round structure
  choose l hi hlhi using hCR.neighborhood_isInterval
  have hlh : ∀ j, G.neighborSet j = CyclicInterval n (l j) (hi j) \ {j} :=
    fun j => (hlhi j).1
  have hcanon : ∀ j, j ∉ CyclicInterval n (l j) (hi j) := fun j => (hlhi j).2
  have hadj_iff : ∀ a b : Fin n, G.Adj a b ↔
      b ∈ CyclicInterval n (l a) (hi a) ∧ b ≠ a := by
    intro a b; rw [show G.Adj a b ↔ b ∈ G.neighborSet a from Iff.rfl, hlh a]
    simp [Set.mem_diff, Set.mem_singleton_iff]
  -- Key: [l(x), h(x)] cannot contain both c and d for any x.
  -- If both c,d ∈ [l(x),h(x)], then x adj c and x adj d.
  -- From the disjunction: in Case 1, x ∈ N(c) ⊆ [c,d] and x ∈ N(d) ⊆ [d,c],
  -- so x ∈ [c,d] ∩ [d,c] = {c,d}. But c,d ∉ [l(c),h(c)] and c,d ∉ [l(d),h(d)].
  -- Contradiction. Case 2 is analogous.
  have hinterval_avoids : ∀ x : Fin n, c ∉ CyclicInterval n (l x) (hi x) ∨
      d ∉ CyclicInterval n (l x) (hi x) := by
    intro x
    by_contra hall; push_neg at hall; obtain ⟨hc_in, hd_in⟩ := hall
    have hxc : G.Adj x c := (hadj_iff x c).mpr ⟨hc_in, fun h => hcanon c (h ▸ hc_in)⟩
    have hxd : G.Adj x d := (hadj_iff x d).mpr ⟨hd_in, fun h => hcanon d (h ▸ hd_in)⟩
    rcases h with ⟨hNc, hNd⟩ | ⟨hNc, hNd⟩
    · -- Case 1: x ∈ N(c) ⊆ [c,d] and x ∈ N(d) ⊆ [d,c]
      have hx_cd := hNc (G.mem_neighborSet c x |>.mpr hxc.symm)
      have hx_dc := hNd (G.mem_neighborSet d x |>.mpr hxd.symm)
      rcases mem_both_arcs_eq hn3 hne hx_cd hx_dc with heq | heq
      · exact absurd (heq ▸ hc_in) (hcanon _)
      · exact absurd (heq ▸ hd_in) (hcanon _)
    · -- Case 2: x ∈ N(c) ⊆ [d,c] and x ∈ N(d) ⊆ [c,d]
      have hx_dc := hNc (G.mem_neighborSet c x |>.mpr hxc.symm)
      have hx_cd := hNd (G.mem_neighborSet d x |>.mpr hxd.symm)
      rcases mem_both_arcs_eq hn3 hne hx_cd hx_dc with heq | heq
      · exact absurd (heq ▸ hc_in) (hcanon _)
      · exact absurd (heq ▸ hd_in) (hcanon _)
  -- Use arc_independent_of_nbhd_side (defined later but in scope via mutual recursion
  -- pattern: we have by_contra hnotBip). We inline the key argument here.
  -- Reduce to showing [d,c] and [c,d] are both independent, then construct 2-coloring.
  -- Handle both cases of h symmetrically.
  -- For both cases, we prove bipartiteness via a direction-based 2-coloring.
  -- Key helper: interval containment. If l(x) is between x and ref (clockwise),
  -- and ref ∉ [l(x), h(x)], then the whole interval [l(x), h(x)] ⊆ [x, ref].
  have hcontain : ∀ (x ref : Fin n),
      x ∉ CyclicInterval n (l x) (hi x) →
      ref ∉ CyclicInterval n (l x) (hi x) →
      cyclicDist n x (l x) ≤ cyclicDist n x ref →
      ∀ y ∈ CyclicInterval n (l x) (hi x),
        y ∈ CyclicInterval n x ref := by
    intro x ref hx_out href_out hdir y hy
    have hlx_in : l x ∈ CyclicInterval n x ref :=
      (mem_cyclicInterval_iff_cyclicDist (l x) x ref).mpr hdir
    rw [mem_cyclicInterval_iff_cyclicDist] at href_out; push_neg at href_out
    have htri := cyclicDist_triangle hlx_in
    exact cyclicInterval_subset hlx_in (by omega) hy
  -- Key helper: direction flip. If two adjacent vertices a, b both have ref ∉ interval,
  -- and both have l on the same side of ref, we get a contradiction.
  have hflip : ∀ (a b ref : Fin n), G.Adj a b →
      ref ∉ CyclicInterval n (l a) (hi a) →
      ref ∉ CyclicInterval n (l b) (hi b) →
      cyclicDist n a (l a) ≤ cyclicDist n a ref →
      cyclicDist n b (l b) ≤ cyclicDist n b ref →
      False := by
    intro a b ref hadj_ab href_a href_b hdir_a hdir_b
    have hab_ne := hadj_ab.ne
    have hb_in_a := ((hadj_iff a b).mp hadj_ab).1
    have ha_in_b := ((hadj_iff b a).mp hadj_ab.symm).1
    have hb_in_ref := hcontain a ref (hcanon a) href_a hdir_a b hb_in_a
    have ha_in_ref := hcontain b ref (hcanon b) href_b hdir_b a ha_in_b
    have htri1 := cyclicDist_triangle hb_in_ref
    have htri2 := cyclicDist_triangle ha_in_ref
    have := cyclicDist_add_reverse hab_ne
    omega
  -- Backward pair contradiction: two adjacent backward vertices give a = b
  have hflip_back : ∀ (a b ref : Fin n), G.Adj a b →
      a ≠ ref → b ≠ ref →
      ref ∉ CyclicInterval n (l a) (hi a) →
      ref ∉ CyclicInterval n (l b) (hi b) →
      ¬(cyclicDist n a (l a) ≤ cyclicDist n a ref) →
      ¬(cyclicDist n b (l b) ≤ cyclicDist n b ref) →
      False := by
    intro a b ref hadj_ab ha_ne hb_ne href_a href_b hback_a hback_b
    push_neg at hback_a hback_b
    have hab_ne := hadj_ab.ne
    have hb_in_a := ((hadj_iff a b).mp hadj_ab).1
    have ha_in_b := ((hadj_iff b a).mp hadj_ab.symm).1
    have hla_self : l a ∈ CyclicInterval n (l a) (hi a) :=
      (mem_cyclicInterval_iff_cyclicDist (l a) (l a) (hi a)).mpr (by simp [cyclicDist])
    have hlb_self : l b ∈ CyclicInterval n (l b) (hi b) :=
      (mem_cyclicInterval_iff_cyclicDist (l b) (l b) (hi b)).mpr (by simp [cyclicDist])
    have hla_ne_a : l a ≠ a := by
      intro h; have h1 := hcanon a; have h2 := hla_self; rw [h] at h1 h2; exact h1 h2
    have hla_ne_ref : l a ≠ ref := by
      intro h; have h1 := href_a; have h2 := hla_self; rw [h] at h1 h2; exact h1 h2
    have hlb_ne_b : l b ≠ b := by
      intro h; have h1 := hcanon b; have h2 := hlb_self; rw [h] at h1 h2; exact h1 h2
    have hlb_ne_ref : l b ≠ ref := by
      intro h; have h1 := href_b; have h2 := hlb_self; rw [h] at h1 h2; exact h1 h2
    have hla_refa : l a ∈ CyclicInterval n ref a := by
      rcases mem_arc_or ha_ne (l a) with h | h
      · rw [mem_cyclicInterval_iff_cyclicDist] at h; omega
      · exact h
    have hlb_refb : l b ∈ CyclicInterval n ref b := by
      rcases mem_arc_or hb_ne (l b) with h | h
      · rw [mem_cyclicInterval_iff_cyclicDist] at h; omega
      · exact h
    have hb_refa : b ∈ CyclicInterval n ref a := by
      rcases mem_arc_or ha_ne b with h | h
      · exfalso; exact no_straddle_arcs hn3 ha_ne (hcanon a) href_a
          hb_in_a hla_self h hla_refa hab_ne.symm hb_ne hla_ne_a hla_ne_ref
      · exact h
    have ha_refb : a ∈ CyclicInterval n ref b := by
      rcases mem_arc_or hb_ne a with h | h
      · exfalso; exact no_straddle_arcs hn3 hb_ne (hcanon b) href_b
          ha_in_b hlb_self h hlb_refb hab_ne ha_ne hlb_ne_b hlb_ne_ref
      · exact h
    have htri := cyclicDist_triangle ha_refb
    rw [mem_cyclicInterval_iff_cyclicDist] at hb_refa
    have hab_zero : cyclicDist n a b = 0 := by omega
    simp only [cyclicDist] at hab_zero
    have := a.isLt; have := b.isLt
    split_ifs at hab_zero with h <;> exact hab_ne (Fin.ext (by omega))
  rcases h with ⟨hNc, hNd⟩ | ⟨hNc, hNd⟩
  · -- Case 1: N(c) ⊆ [c, d], N(d) ⊆ [d, c]. "Outward" neighborhoods.
    -- Reference: d for arc [c,d), c for arc [d,c).
    have href1 : ∀ x, cyclicDist n c x < cyclicDist n c d →
        d ∉ CyclicInterval n (l x) (hi x) := by
      intro x hx hd_in
      by_cases hxc : x = c
      · rw [hxc] at hd_in; exact hnadj ((hadj_iff c d).mpr ⟨hd_in, fun h => hcanon d (h ▸ hd_in)⟩)
      · have hxd_adj : G.Adj x d := (hadj_iff x d).mpr ⟨hd_in, fun h => hcanon d (h ▸ hd_in)⟩
        have hx_in_cd := (mem_cyclicInterval_iff_cyclicDist x c d).mpr (le_of_lt hx)
        have hx_in_dc : x ∈ ↑(CyclicInterval n d c) :=
          hNd (G.mem_neighborSet d x |>.mpr hxd_adj.symm)
        rcases mem_both_arcs_eq hn3 hne hx_in_cd hx_in_dc with rfl | rfl
        · exact hxc rfl
        · simp [cyclicDist] at hx
    have href2 : ∀ x, cyclicDist n d x < cyclicDist n d c →
        c ∉ CyclicInterval n (l x) (hi x) := by
      intro x hx hc_in
      by_cases hxd : x = d
      · rw [hxd] at hc_in
        exact hnadj ((hadj_iff d c).mpr
          ⟨hc_in, fun h => hcanon c (h ▸ hc_in)⟩).symm
      · have hxc_adj : G.Adj x c := (hadj_iff x c).mpr ⟨hc_in, fun h => hcanon c (h ▸ hc_in)⟩
        have hx_in_dc := (mem_cyclicInterval_iff_cyclicDist x d c).mpr (le_of_lt hx)
        have hx_in_cd : x ∈ ↑(CyclicInterval n c d) :=
          hNc (G.mem_neighborSet c x |>.mpr hxc_adj.symm)
        rcases mem_both_arcs_eq hn3 hne hx_in_cd hx_in_dc with rfl | rfl
        · simp [cyclicDist] at hx
        · exact hxd rfl
    -- Vertices partition into [c,d) and [d,c)
    have hpartition : ∀ x : Fin n, cyclicDist n c x < cyclicDist n c d ∨
        cyclicDist n d x < cyclicDist n d c := by
      intro x
      by_contra hall; push_neg at hall
      rcases mem_arc_or hne x with hx_cd | hx_dc
      · rw [mem_cyclicInterval_iff_cyclicDist] at hx_cd
        have htri := cyclicDist_triangle ((mem_cyclicInterval_iff_cyclicDist x c d).mpr hx_cd)
        -- cyclicDist(x, d) = 0 → x = d
        have hxd_zero : cyclicDist n x d = 0 := by omega
        have hxd : x = d := by
          simp only [cyclicDist] at hxd_zero; have := x.isLt; have := d.isLt
          split_ifs at hxd_zero with h <;> exact Fin.ext (by omega)
        rw [hxd] at hall
        have hdd : cyclicDist n d d = 0 := by simp [cyclicDist]
        have hdc_le := hall.2; rw [hdd] at hdc_le
        have hdc_zero : cyclicDist n d c = 0 := by omega
        simp only [cyclicDist] at hdc_zero; have := d.isLt; have := c.isLt
        split_ifs at hdc_zero with h <;> exact hne (Fin.ext (by omega))
      · rw [mem_cyclicInterval_iff_cyclicDist] at hx_dc
        have htri := cyclicDist_triangle ((mem_cyclicInterval_iff_cyclicDist x d c).mpr hx_dc)
        have hxc_zero : cyclicDist n x c = 0 := by omega
        have hxc : x = c := by
          simp only [cyclicDist] at hxc_zero; have := x.isLt; have := c.isLt
          split_ifs at hxc_zero with h <;> exact Fin.ext (by omega)
        rw [hxc] at hall
        have hcc : cyclicDist n c c = 0 := by simp [cyclicDist]
        have hcd_le := hall.1; rw [hcc] at hcd_le
        have hcd_zero : cyclicDist n c d = 0 := by omega
        simp only [cyclicDist] at hcd_zero; have := c.isLt; have := d.isLt
        split_ifs at hcd_zero with h <;> exact hne (Fin.ext (by omega))
    -- Direction: for x in [c,d) (ref d), is l(x) between x and d?
    -- True = "forward" (towards d), False = "backward" (away from d)
    let fwd1 (x : Fin n) : Prop := cyclicDist n x (l x) ≤ cyclicDist n x d
    let fwd2 (x : Fin n) : Prop := cyclicDist n x (l x) ≤ cyclicDist n x c
    -- Forward vertices in [c,d) have all neighbors in [c,d]
    have hfwd1_same_arc : ∀ x, cyclicDist n c x < cyclicDist n c d → fwd1 x →
        ∀ y ∈ CyclicInterval n (l x) (hi x), cyclicDist n c y ≤ cyclicDist n c d := by
      intro x hx hfwd y hy
      have hd_out := href1 x hx
      have hy_xd := hcontain x d (hcanon x) hd_out hfwd y hy
      have hx_cd := (mem_cyclicInterval_iff_cyclicDist x c d).mpr (le_of_lt hx)
      have htri := cyclicDist_triangle hx_cd
      exact (mem_cyclicInterval_iff_cyclicDist y c d).mp
        (cyclicInterval_subset hx_cd (by omega) hy_xd)
    -- Forward vertices in [d,c) have all neighbors in [d,c]
    have hfwd2_same_arc : ∀ x, cyclicDist n d x < cyclicDist n d c → fwd2 x →
        ∀ y ∈ CyclicInterval n (l x) (hi x), cyclicDist n d y ≤ cyclicDist n d c := by
      intro x hx hfwd y hy
      have hc_out := href2 x hx
      have hy_xc := hcontain x c (hcanon x) hc_out hfwd y hy
      have hx_dc := (mem_cyclicInterval_iff_cyclicDist x d c).mpr (le_of_lt hx)
      have htri := cyclicDist_triangle hx_dc
      exact (mem_cyclicInterval_iff_cyclicDist y d c).mp
        (cyclicInterval_subset hx_dc (by omega) hy_xc)
    -- Partition exclusivity: [c,d) and [d,c) are disjoint
    have hpart_excl : ∀ x, cyclicDist n d x < cyclicDist n d c →
        ¬(cyclicDist n c x < cyclicDist n c d) := by
      intro x hx hlt
      have hx_ne_d : x ≠ d := fun h => by rw [h] at hlt; simp [cyclicDist] at hlt
      have hx_cd := (mem_cyclicInterval_iff_cyclicDist x c d).mpr (le_of_lt hlt)
      have := cyclicDist_triangle hx_cd
      have := cyclicDist_add_reverse hx_ne_d
      have := cyclicDist_add_reverse hne
      omega
    -- Define the coloring
    rw [show G.IsBipartite = G.Colorable 2 from rfl]
    refine ⟨⟨fun x =>
      if cyclicDist n c x < cyclicDist n c d then
        if cyclicDist n x (l x) ≤ cyclicDist n x d then (0 : Fin 2) else 1
      else
        if cyclicDist n x (l x) ≤ cyclicDist n x c then 1 else 0,
      fun {a b} hadj_ab => ?_⟩⟩
    have hab_ne := hadj_ab.ne
    have hb_in_a := ((hadj_iff a b).mp hadj_ab).1
    have ha_in_b := ((hadj_iff b a).mp hadj_ab.symm).1
    rcases hpartition a with ha1 | ha2 <;> rcases hpartition b with hb1 | hb2
    · -- Both in [c,d): direction must differ
      simp only [if_pos ha1, if_pos hb1]
      have hda := href1 a ha1; have hdb := href1 b hb1
      have ha_ne_d : a ≠ d := fun h => by rw [h] at ha1; simp [cyclicDist] at ha1
      have hb_ne_d : b ≠ d := fun h => by rw [h] at hb1; simp [cyclicDist] at hb1
      by_cases h1 : cyclicDist n a (l a) ≤ cyclicDist n a d <;>
        by_cases h2 : cyclicDist n b (l b) ≤ cyclicDist n b d <;>
        simp only [h1, h2, ite_true, ite_false]
      · exact (hflip a b d hadj_ab hda hdb h1 h2).elim
      · exact Fin.zero_ne_one
      · exact Fin.zero_ne_one.symm
      · exact (hflip_back a b d hadj_ab ha_ne_d hb_ne_d hda hdb h1 h2).elim
    · -- a in [c,d), b in [d,c): cross-arc
      have hb_not_cd := hpart_excl b hb2
      simp only [if_pos ha1, if_neg hb_not_cd]
      have ha_back : ¬(cyclicDist n a (l a) ≤ cyclicDist n a d) := by
        intro hfwd
        have hb_cd := hfwd1_same_arc a ha1 hfwd b hb_in_a
        have hb_cd' := (mem_cyclicInterval_iff_cyclicDist b c d).mpr hb_cd
        have hb_dc := (mem_cyclicInterval_iff_cyclicDist b d c).mpr (le_of_lt hb2)
        rcases mem_both_arcs_eq hn3 hne hb_cd' hb_dc with rfl | rfl
        · simp [cyclicDist] at hb2
        · exact (href1 a ha1) hb_in_a
      have hb_back : ¬(cyclicDist n b (l b) ≤ cyclicDist n b c) := by
        intro hfwd
        have ha_dc := hfwd2_same_arc b hb2 hfwd a ha_in_b
        have ha_dc' := (mem_cyclicInterval_iff_cyclicDist a d c).mpr ha_dc
        have ha_cd := (mem_cyclicInterval_iff_cyclicDist a c d).mpr (le_of_lt ha1)
        obtain (heq | heq) := mem_both_arcs_eq hn3 hne ha_cd ha_dc'
        · -- a = c: c adj b and N(c) ⊆ [c,d], so b ∈ [c,d] ∩ [d,c) → b ∈ {c,d} → contradiction
          have hadj_cb : G.Adj c b := heq ▸ hadj_ab
          have hb_cd := hNc (G.mem_neighborSet c b |>.mpr hadj_cb)
          have hb_dc := (mem_cyclicInterval_iff_cyclicDist b d c).mpr (le_of_lt hb2)
          obtain (hbc | hbd) := mem_both_arcs_eq hn3 hne hb_cd hb_dc
          · rw [← hbc] at hb2; exact absurd hb2 (lt_irrefl _)
          · exact hnadj (hbd ▸ hadj_cb)
        · rw [heq] at ha1; exact absurd ha1 (lt_irrefl _)
      simp only [if_neg ha_back, if_neg hb_back]
      exact Fin.zero_ne_one.symm
    · -- a in [d,c), b in [c,d): cross-arc (symmetric)
      have ha_not_cd := hpart_excl a ha2
      simp only [if_neg ha_not_cd, if_pos hb1]
      have hb_back : ¬(cyclicDist n b (l b) ≤ cyclicDist n b d) := by
        intro hfwd
        have ha_cd := hfwd1_same_arc b hb1 hfwd a ha_in_b
        have ha_cd' := (mem_cyclicInterval_iff_cyclicDist a c d).mpr ha_cd
        have ha_dc := (mem_cyclicInterval_iff_cyclicDist a d c).mpr (le_of_lt ha2)
        rcases mem_both_arcs_eq hn3 hne ha_cd' ha_dc with rfl | rfl
        · simp [cyclicDist] at ha2
        · exact (href1 b hb1) ha_in_b
      have ha_back : ¬(cyclicDist n a (l a) ≤ cyclicDist n a c) := by
        intro hfwd
        have hb_dc := hfwd2_same_arc a ha2 hfwd b hb_in_a
        have hb_dc' := (mem_cyclicInterval_iff_cyclicDist b d c).mpr hb_dc
        have hb_cd := (mem_cyclicInterval_iff_cyclicDist b c d).mpr (le_of_lt hb1)
        rcases mem_both_arcs_eq hn3 hne hb_cd hb_dc' with rfl | rfl
        · exact (href2 a ha2) hb_in_a
        · simp [cyclicDist] at hb1
      simp only [if_neg ha_back, if_neg hb_back]
      exact Fin.zero_ne_one
    · -- Both in [d,c): direction must differ (ref c)
      have ha_not_cd := hpart_excl a ha2
      have hb_not_cd := hpart_excl b hb2
      simp only [if_neg ha_not_cd, if_neg hb_not_cd]
      have hca := href2 a ha2; have hcb := href2 b hb2
      have ha_ne_c : a ≠ c := fun h => by rw [h] at ha2; simp [cyclicDist] at ha2
      have hb_ne_c : b ≠ c := fun h => by rw [h] at hb2; simp [cyclicDist] at hb2
      by_cases h1 : cyclicDist n a (l a) ≤ cyclicDist n a c <;>
        by_cases h2 : cyclicDist n b (l b) ≤ cyclicDist n b c <;>
        simp only [h1, h2, ite_true, ite_false]
      · exact (hflip a b c hadj_ab hca hcb h1 h2).elim
      · exact Fin.zero_ne_one.symm
      · exact Fin.zero_ne_one
      · exact (hflip_back a b c hadj_ab ha_ne_c hb_ne_c hca hcb h1 h2).elim
  · -- Case 2: N(c) ⊆ [d, c], N(d) ⊆ [c, d]. "Inward" neighborhoods.
    -- Reference: c for arc [c,d), d for arc [d,c).
    have href1 : ∀ x, cyclicDist n c x < cyclicDist n c d →
        c ∉ CyclicInterval n (l x) (hi x) := by
      intro x hx hc_in
      by_cases hxc : x = c
      · rw [hxc] at hc_in; exact hcanon c hc_in
      · have hxc_adj : G.Adj x c := (hadj_iff x c).mpr ⟨hc_in, fun h => hcanon c (h ▸ hc_in)⟩
        have hx_in_cd := (mem_cyclicInterval_iff_cyclicDist x c d).mpr (le_of_lt hx)
        have hx_in_dc : x ∈ ↑(CyclicInterval n d c) :=
          hNc (G.mem_neighborSet c x |>.mpr hxc_adj.symm)
        rcases mem_both_arcs_eq hn3 hne hx_in_cd hx_in_dc with rfl | rfl
        · exact hxc rfl
        · simp [cyclicDist] at hx
    have href2 : ∀ x, cyclicDist n d x < cyclicDist n d c →
        d ∉ CyclicInterval n (l x) (hi x) := by
      intro x hx hd_in
      by_cases hxd : x = d
      · rw [hxd] at hd_in; exact hcanon d hd_in
      · have hxd_adj : G.Adj x d := (hadj_iff x d).mpr ⟨hd_in, fun h => hcanon d (h ▸ hd_in)⟩
        have hx_in_dc := (mem_cyclicInterval_iff_cyclicDist x d c).mpr (le_of_lt hx)
        have hx_in_cd : x ∈ ↑(CyclicInterval n c d) :=
          hNd (G.mem_neighborSet d x |>.mpr hxd_adj.symm)
        rcases mem_both_arcs_eq hn3 hne hx_in_cd hx_in_dc with rfl | rfl
        · simp [cyclicDist] at hx
        · exact hxd rfl
    have hpartition : ∀ x : Fin n, cyclicDist n c x < cyclicDist n c d ∨
        cyclicDist n d x < cyclicDist n d c := by
      intro x
      by_contra hall; push_neg at hall
      rcases mem_arc_or hne x with hx_cd | hx_dc
      · rw [mem_cyclicInterval_iff_cyclicDist] at hx_cd
        have htri := cyclicDist_triangle ((mem_cyclicInterval_iff_cyclicDist x c d).mpr hx_cd)
        have hxd_zero : cyclicDist n x d = 0 := by omega
        have hxd : x = d := by
          simp only [cyclicDist] at hxd_zero; have := x.isLt; have := d.isLt
          split_ifs at hxd_zero with h <;> exact Fin.ext (by omega)
        rw [hxd] at hall
        have hdd : cyclicDist n d d = 0 := by simp [cyclicDist]
        have hdc_le := hall.2; rw [hdd] at hdc_le
        have hdc_zero : cyclicDist n d c = 0 := by omega
        simp only [cyclicDist] at hdc_zero; have := d.isLt; have := c.isLt
        split_ifs at hdc_zero with h <;> exact hne (Fin.ext (by omega))
      · rw [mem_cyclicInterval_iff_cyclicDist] at hx_dc
        have htri := cyclicDist_triangle ((mem_cyclicInterval_iff_cyclicDist x d c).mpr hx_dc)
        have hxc_zero : cyclicDist n x c = 0 := by omega
        have hxc : x = c := by
          simp only [cyclicDist] at hxc_zero; have := x.isLt; have := c.isLt
          split_ifs at hxc_zero with h <;> exact Fin.ext (by omega)
        rw [hxc] at hall
        have hcc : cyclicDist n c c = 0 := by simp [cyclicDist]
        have hcd_le := hall.1; rw [hcc] at hcd_le
        have hcd_zero : cyclicDist n c d = 0 := by omega
        simp only [cyclicDist] at hcd_zero; have := c.isLt; have := d.isLt
        split_ifs at hcd_zero with h <;> exact hne (Fin.ext (by omega))
    -- Backward x (≠ c) in [c,d): neighbors confined to [c,x]
    have hback1 : ∀ x, x ≠ c → cyclicDist n c x < cyclicDist n c d →
        ¬(cyclicDist n x (l x) ≤ cyclicDist n x c) →
        ∀ y ∈ CyclicInterval n (l x) (hi x), cyclicDist n c y ≤ cyclicDist n c x := by
      intro x hxc hx hback y hy; push_neg at hback
      have hlx : l x ∈ CyclicInterval n c x := by
        rcases mem_arc_or hxc.symm (l x) with h | h
        · exact h
        · rw [mem_cyclicInterval_iff_cyclicDist] at h; omega
      have : cyclicDist n (l x) (hi x) < cyclicDist n (l x) x := by
        by_contra h; push_neg at h
        exact hcanon x ((mem_cyclicInterval_iff_cyclicDist x (l x) (hi x)).mpr h)
      have htri := cyclicDist_triangle hlx
      exact (mem_cyclicInterval_iff_cyclicDist y c x).mp
        (cyclicInterval_subset hlx (by omega) hy)
    -- Backward x (≠ d) in [d,c): neighbors confined to [d,x]
    have hback2 : ∀ x, x ≠ d → cyclicDist n d x < cyclicDist n d c →
        ¬(cyclicDist n x (l x) ≤ cyclicDist n x d) →
        ∀ y ∈ CyclicInterval n (l x) (hi x), cyclicDist n d y ≤ cyclicDist n d x := by
      intro x hxd hx hback y hy; push_neg at hback
      have hlx : l x ∈ CyclicInterval n d x := by
        rcases mem_arc_or hxd.symm (l x) with h | h
        · exact h
        · rw [mem_cyclicInterval_iff_cyclicDist] at h; omega
      have : cyclicDist n (l x) (hi x) < cyclicDist n (l x) x := by
        by_contra h; push_neg at h
        exact hcanon x ((mem_cyclicInterval_iff_cyclicDist x (l x) (hi x)).mpr h)
      have htri := cyclicDist_triangle hlx
      exact (mem_cyclicInterval_iff_cyclicDist y d x).mp
        (cyclicInterval_subset hlx (by omega) hy)
    -- Partition exclusivity
    have hpart_excl : ∀ x, cyclicDist n d x < cyclicDist n d c →
        ¬(cyclicDist n c x < cyclicDist n c d) := by
      intro x hx hlt
      have hxd : x ≠ d := fun h => by subst h; simp [cyclicDist] at hlt
      have := cyclicDist_triangle ((mem_cyclicInterval_iff_cyclicDist x c d).mpr (le_of_lt hlt))
      have := cyclicDist_add_reverse hxd; have := cyclicDist_add_reverse hne; omega
    -- Strict membership: x ∈ [y,z], x ≠ z → cyclicDist(y,x) < cyclicDist(y,z)
    have strict_mem : ∀ {x y z : Fin n}, x ∈ CyclicInterval n y z → x ≠ z →
        cyclicDist n y x < cyclicDist n y z := by
      intro x y z hm hxz
      have htri := cyclicDist_triangle hm
      rw [mem_cyclicInterval_iff_cyclicDist] at hm
      by_contra hge; push_neg at hge
      have hcd0 : cyclicDist n x z = 0 := by omega
      unfold cyclicDist at hcd0; have := x.isLt; have := z.isLt
      split_ifs at hcd0 with hh <;> exact hxz (Fin.ext (by omega))
    -- Coloring: c → 0, d → 1, [c,d)\{c,d}: fwd→0/bwd→1, [d,c)\{c,d}: fwd→1/bwd→0
    rw [show G.IsBipartite = G.Colorable 2 from rfl]
    refine ⟨⟨fun x =>
      if x = c then (0 : Fin 2) else if x = d then 1
      else if cyclicDist n c x < cyclicDist n c d then
        if cyclicDist n x (l x) ≤ cyclicDist n x c then 0 else 1
      else if cyclicDist n x (l x) ≤ cyclicDist n x d then 1 else 0,
      fun {a b} hadj_ab => ?_⟩⟩
    have hab_ne := hadj_ab.ne
    have hb_in_a := ((hadj_iff a b).mp hadj_ab).1
    have ha_in_b := ((hadj_iff b a).mp hadj_ab.symm).1
    -- Case split on endpoint identities
    by_cases hac : a = c
    · -- a = c: color 0
      have hbc : b ≠ c := fun h => hab_ne (hac.trans h.symm)
      by_cases hbd : b = d
      · exact absurd (hac ▸ hbd ▸ hadj_ab) hnadj
      · have hb_dc := hNc (G.mem_neighborSet c b |>.mpr (hac ▸ hadj_ab))
        have hb2 := strict_mem hb_dc hbc
        have hb_fwd : cyclicDist n b (l b) ≤ cyclicDist n b d := by
          by_contra hbk
          have := hback2 b hbd hb2 hbk c (hac ▸ ha_in_b); omega
        simp only [if_pos hac, if_neg hbc, if_neg hbd,
          if_neg (hpart_excl b hb2 : ¬_), if_pos hb_fwd]
        exact Fin.zero_ne_one
    · by_cases hbc : b = c
      · -- b = c: color 0
        by_cases had : a = d
        · exact absurd (had ▸ hbc ▸ hadj_ab).symm hnadj
        · have ha_dc := hNc (G.mem_neighborSet c a |>.mpr (hbc ▸ hadj_ab).symm)
          have ha2 := strict_mem ha_dc hac
          have ha_fwd : cyclicDist n a (l a) ≤ cyclicDist n a d := by
            by_contra hbk
            have := hback2 a had ha2 hbk c (hbc ▸ hb_in_a); omega
          simp only [if_neg hac, if_neg had,
            if_neg (hpart_excl a ha2 : ¬_), if_pos ha_fwd, if_pos hbc]
          exact Fin.zero_ne_one.symm
      · by_cases had : a = d
        · -- a = d: color 1
          have hbd : b ≠ d := fun h => hab_ne (had.trans h.symm)
          have hb_cd := hNd (G.mem_neighborSet d b |>.mpr (had ▸ hadj_ab))
          have hb1 := strict_mem hb_cd hbd
          have hb_fwd : cyclicDist n b (l b) ≤ cyclicDist n b c := by
            by_contra hbk
            have := hback1 b hbc hb1 hbk d (had ▸ ha_in_b); omega
          simp only [if_neg hac, if_pos had, if_neg hbc, if_neg hbd,
            if_pos hb1, if_pos hb_fwd]
          exact Fin.zero_ne_one.symm
        · by_cases hbd : b = d
          · -- b = d: color 1
            have ha_cd := hNd (G.mem_neighborSet d a |>.mpr (hbd ▸ hadj_ab).symm)
            have ha1 := strict_mem ha_cd had
            have ha_fwd : cyclicDist n a (l a) ≤ cyclicDist n a c := by
              by_contra hbk
              have := hback1 a hac ha1 hbk d (hbd ▸ hb_in_a); omega
            simp only [if_neg hac, if_neg had, if_pos ha1, if_pos ha_fwd,
              if_neg hbc, if_pos hbd]
            exact Fin.zero_ne_one
          · -- Generic: a ≠ c, a ≠ d, b ≠ c, b ≠ d
            simp only [if_neg hac, if_neg had, if_neg hbc, if_neg hbd]
            rcases hpartition a with ha1 | ha2 <;> rcases hpartition b with hb1 | hb2
            · -- Both in [c,d): ref c
              simp only [if_pos ha1, if_pos hb1]
              by_cases h1 : cyclicDist n a (l a) ≤ cyclicDist n a c <;>
                by_cases h2 : cyclicDist n b (l b) ≤ cyclicDist n b c <;>
                simp only [h1, h2, ite_true, ite_false]
              · exact (hflip a b c hadj_ab (href1 a ha1) (href1 b hb1) h1 h2).elim
              · exact Fin.zero_ne_one
              · exact Fin.zero_ne_one.symm
              · exact (hflip_back a b c hadj_ab hac hbc
                  (href1 a ha1) (href1 b hb1) h1 h2).elim
            · -- a in [c,d), b in [d,c): cross-arc
              have hb_not := hpart_excl b hb2
              simp only [if_pos ha1, if_neg hb_not]
              have ha_fwd : cyclicDist n a (l a) ≤ cyclicDist n a c := by
                by_contra hbk
                exact hpart_excl b hb2
                  (lt_of_le_of_lt (hback1 a hac ha1 hbk b hb_in_a) ha1)
              have hb_fwd : cyclicDist n b (l b) ≤ cyclicDist n b d := by
                by_contra hbk
                exact hpart_excl a
                  (lt_of_le_of_lt (hback2 b hbd hb2 hbk a ha_in_b) hb2) ha1
              simp only [if_pos ha_fwd, if_pos hb_fwd]
              exact Fin.zero_ne_one
            · -- a in [d,c), b in [c,d): cross-arc (symmetric)
              have ha_not := hpart_excl a ha2
              simp only [if_neg ha_not, if_pos hb1]
              have hb_fwd : cyclicDist n b (l b) ≤ cyclicDist n b c := by
                by_contra hbk
                exact hpart_excl a ha2
                  (lt_of_le_of_lt (hback1 b hbc hb1 hbk a ha_in_b) hb1)
              have ha_fwd : cyclicDist n a (l a) ≤ cyclicDist n a d := by
                by_contra hbk
                exact hpart_excl b
                  (lt_of_le_of_lt (hback2 a had ha2 hbk b hb_in_a) ha2) hb1
              simp only [if_pos ha_fwd, if_pos hb_fwd]
              exact Fin.zero_ne_one.symm
            · -- Both in [d,c): ref d
              have ha_not := hpart_excl a ha2
              have hb_not := hpart_excl b hb2
              simp only [if_neg ha_not, if_neg hb_not]
              by_cases h1 : cyclicDist n a (l a) ≤ cyclicDist n a d <;>
                by_cases h2 : cyclicDist n b (l b) ≤ cyclicDist n b d <;>
                simp only [h1, h2, ite_true, ite_false]
              · exact (hflip a b d hadj_ab (href2 a ha2) (href2 b hb2) h1 h2).elim
              · exact Fin.zero_ne_one.symm
              · exact Fin.zero_ne_one
              · exact (hflip_back a b d hadj_ab had hbd
                  (href2 a ha2) (href2 b hb2) h1 h2).elim

-- BHY00 Lemma 3.7 + Corollary 3.10: In a non-bipartite convex-round graph,
-- if vertex a (an endpoint of a non-edge {c,d}) has its neighborhood contained
-- in the arc [c,d], then the opposite arc [d,c] is independent.
private lemma arc_independent_of_nbhd_side {n : ℕ} [NeZero n] (hn3 : 3 ≤ n)
    (G : SimpleGraph (Fin n))
    (hCR : IsConvexRoundEnum n G)
    (hnotBip : ¬G.IsBipartite)
    {a c d : Fin n} (hne : c ≠ d) (hnadj : ¬G.Adj c d)
    (h_side : G.neighborSet a ⊆ (CyclicInterval n c d : Set (Fin n)))
    (ha_cd : a = c ∨ a = d) :
    ∀ x y : Fin n, x ∈ CyclicInterval n d c → y ∈ CyclicInterval n d c →
      ¬G.Adj x y := by
  -- Setup
  choose l hi hlhi using hCR.neighborhood_isInterval
  have hlh : ∀ j, G.neighborSet j = CyclicInterval n (l j) (hi j) \ {j} := fun j => (hlhi j).1
  have hcanon : ∀ j, j ∉ CyclicInterval n (l j) (hi j) := fun j => (hlhi j).2
  have hconn := convexRound_preconnected_of_not_bipartite G hCR hnotBip
  -- z ∈ [d,c], z ≠ c, z ≠ d  ⟹  z ∉ [c,d]
  have h_excl : ∀ z, z ∈ CyclicInterval n d c → z ≠ c → z ≠ d →
      z ∉ CyclicInterval n c d :=
    fun z hz hzc hzd hzcd => (mem_both_arcs_eq hn3 hne hzcd hz).elim hzc hzd
  -- c ∉ [l(d), h(d)] and d ∉ [l(c), h(c)] (non-adjacency)
  have hc_out_ld : c ∉ CyclicInterval n (l d) (hi d) := by
    intro h
    have : c ∈ G.neighborSet d := by rw [hlh d]; exact ⟨h, hne⟩
    exact hnadj ((G.mem_neighborSet d c).mp this).symm
  have hd_out_lc : d ∉ CyclicInterval n (l c) (hi c) := by
    intro h
    have : d ∈ G.neighborSet c := by rw [hlh c]; exact ⟨h, Ne.symm hne⟩
    exact hnadj ((G.mem_neighborSet c d).mp this)
  -- Determine the other endpoint's neighborhood side
  -- Helper: [l(v), h(v)] avoids c and d ⟹ [l(v), h(v)] ⊆ [c,d] or [l(v), h(v)] ⊆ [d,c]
  have h_nbhd_one_side : ∀ (v : Fin n),
      c ∉ CyclicInterval n (l v) (hi v) → d ∉ CyclicInterval n (l v) (hi v) →
      (∀ w, w ∈ CyclicInterval n (l v) (hi v) → w ∈ CyclicInterval n c d) ∨
      (∀ w, w ∈ CyclicInterval n (l v) (hi v) → w ∈ CyclicInterval n d c) := by
    intro v hc_out hd_out
    by_contra h_neg; push_neg at h_neg
    obtain ⟨⟨u, hu_lv, hu_ncd⟩, ⟨w, hw_lv, hw_ndc⟩⟩ := h_neg
    have hu_dc := (mem_arc_or hne u).resolve_left hu_ncd
    have hw_cd := (mem_arc_or hne w).resolve_right hw_ndc
    exact no_straddle_arcs hn3 hne hc_out hd_out hw_lv hu_lv hw_cd hu_dc
      (fun h => hc_out (h ▸ hw_lv)) (fun h => hd_out (h ▸ hw_lv))
      (fun h => hc_out (h ▸ hu_lv)) (fun h => hd_out (h ▸ hu_lv))
  -- Step 1: Both N(c) and N(d) ⊆ [c,d]
  suffices h_both : G.neighborSet c ⊆ ↑(CyclicInterval n c d) ∧
                     G.neighborSet d ⊆ ↑(CyclicInterval n c d) by
    obtain ⟨hNc, hNd⟩ := h_both
    -- Step 2: For z ∈ (d,c)_open, z is not adjacent to c or d
    have h_not_adj : ∀ z, z ∈ CyclicInterval n d c → z ≠ c → z ≠ d →
        ¬G.Adj c z ∧ ¬G.Adj d z :=
      fun z hz hzc hzd =>
        ⟨fun h => h_excl z hz hzc hzd (hNc ((G.mem_neighborSet c z).mpr h)),
         fun h => h_excl z hz hzc hzd (hNd ((G.mem_neighborSet d z).mpr h))⟩
    -- Step 3: "good" property preserved by adjacency
    -- good(z) = z ∈ (d,c)_open → N(z) ⊆ [c,d]
    have h_good_step : ∀ u v : Fin n,
        (u ∈ CyclicInterval n d c → u ≠ c → u ≠ d →
          G.neighborSet u ⊆ ↑(CyclicInterval n c d)) →
        G.Adj u v →
        (v ∈ CyclicInterval n d c → v ≠ c → v ≠ d →
          G.neighborSet v ⊆ ↑(CyclicInterval n c d)) := by
      intro u v hu_good huv hv_dc hvc hvd
      -- v ∈ (d,c)_open. N(v) is on one side (no_straddle). Show it's the [c,d] side.
      have ⟨hncv, hndv⟩ := h_not_adj v hv_dc hvc hvd
      have hc_out_lv : c ∉ CyclicInterval n (l v) (hi v) := by
        intro h; exact hncv ((G.mem_neighborSet v c).mp
          (by rw [hlh v]; exact ⟨h, Ne.symm hvc⟩)).symm
      have hd_out_lv : d ∉ CyclicInterval n (l v) (hi v) := by
        intro h; exact hndv ((G.mem_neighborSet v d).mp
          (by rw [hlh v]; exact ⟨h, Ne.symm hvd⟩)).symm
      rcases h_nbhd_one_side v hc_out_lv hd_out_lv with h_cd | h_dc
      · -- N(v) ⊆ [c,d] ✓
        intro w hw; rw [hlh v] at hw; exact h_cd w hw.1
      · -- N(v) ⊆ [d,c]: contradiction via u
        exfalso
        -- u ∈ N(v) ⊆ [d,c]
        have hu_nv : u ∈ G.neighborSet v := (G.mem_neighborSet v u).mpr huv.symm
        have hu_lv : u ∈ CyclicInterval n (l v) (hi v) := by rw [hlh v] at hu_nv; exact hu_nv.1
        have hu_dc : u ∈ CyclicInterval n d c := h_dc u hu_lv
        by_cases huc : u = c
        · exact h_excl v hv_dc hvc hvd (hNc ((G.mem_neighborSet c v).mpr (huc ▸ huv)))
        · by_cases hud : u = d
          · exact h_excl v hv_dc hvc hvd (hNd ((G.mem_neighborSet d v).mpr (hud ▸ huv)))
          · -- u ∈ (d,c)_open, good(u), so N(u) ⊆ [c,d]
            -- v ∈ N(u) ⊆ [c,d], but v ∈ (d,c)_open ⟹ v ∉ [c,d]
            have hv_nu : v ∈ G.neighborSet u := (G.mem_neighborSet u v).mpr huv
            exact h_excl v hv_dc hvc hvd (hu_good hu_dc huc hud hv_nu)
    -- Step 4: Walk induction—every vertex reachable from c is "good"
    have h_walk_good : ∀ u v (w : G.Walk u v),
        (u ∈ CyclicInterval n d c → u ≠ c → u ≠ d →
          G.neighborSet u ⊆ ↑(CyclicInterval n c d)) →
        (v ∈ CyclicInterval n d c → v ≠ c → v ≠ d →
          G.neighborSet v ⊆ ↑(CyclicInterval n c d)) := by
      intro u v w
      induction w with
      | nil => exact id
      | cons hadj _ ih => exact fun hu => ih (h_good_step _ _ hu hadj)
    -- Step 5: Conclude [d,c] is independent
    intro x y hx_dc hy_dc hxy
    -- First show x, y ≠ c, d
    have hxc : x ≠ c := by
      intro hxc; rw [hxc] at hxy
      by_cases hyc : y = c
      · rw [hyc] at hxy; exact G.loopless.irrefl c hxy
      · by_cases hyd : y = d
        · rw [hyd] at hxy; exact hnadj hxy
        · exact (h_not_adj y hy_dc hyc hyd).1 hxy
    have hxd : x ≠ d := by
      intro hxd; rw [hxd] at hxy
      by_cases hyc : y = c
      · rw [hyc] at hxy; exact hnadj hxy.symm
      · by_cases hyd : y = d
        · rw [hyd] at hxy; exact G.loopless.irrefl d hxy
        · exact (h_not_adj y hy_dc hyc hyd).2 hxy
    have hyc : y ≠ c := by
      intro hyc; rw [hyc] at hxy
      exact (h_not_adj x hx_dc hxc hxd).1 hxy.symm
    have hyd : y ≠ d := by
      intro hyd; rw [hyd] at hxy
      exact (h_not_adj x hx_dc hxc hxd).2 hxy.symm
    -- x ∈ (d,c)_open: by connectivity + walk induction, x is good
    obtain ⟨w⟩ := hconn c x
    have hx_good := h_walk_good c x w
      (fun _ hcc _ => absurd rfl hcc) hx_dc hxc hxd
    -- y ∈ N(x) ⊆ [c,d], but y ∈ (d,c)_open ⟹ y ∉ [c,d]
    exact h_excl y hy_dc hyc hyd (hx_good ((G.mem_neighborSet x y).mpr hxy))
  -- Prove h_both: both N(c) and N(d) ⊆ [c,d]
  rcases ha_cd with rfl | rfl
  · -- a = c: N(c) ⊆ [c,d] given. Determine N(d).
    refine ⟨h_side, ?_⟩
    rcases h_nbhd_one_side d hc_out_ld (hcanon d) with h_cd | h_dc
    · intro z hz; rw [hlh d] at hz; exact h_cd z hz.1
    · -- N(d) ⊆ [d,c]: opposite side ⟹ bipartite
      exfalso; apply hnotBip
      have hNd_sub : G.neighborSet d ⊆ ↑(CyclicInterval n d a) := by
        intro z hz; rw [hlh d] at hz; exact h_dc z hz.1
      exact opposite_sides_bipartite hn3 G hCR hne hnadj (Or.inl ⟨h_side, hNd_sub⟩)
  · -- a = d: N(d) ⊆ [c,d] given. Determine N(c).
    refine ⟨?_, h_side⟩
    rcases h_nbhd_one_side c (hcanon c) hd_out_lc with h_cd | h_dc
    · intro z hz; rw [hlh c] at hz; exact h_cd z hz.1
    · -- N(c) ⊆ [d,c]: opposite side ⟹ bipartite
      exfalso; apply hnotBip
      have hNc_sub : G.neighborSet c ⊆ ↑(CyclicInterval n a c) := by
        intro z hz; rw [hlh c] at hz; exact h_dc z hz.1
      exact opposite_sides_bipartite hn3 G hCR hne hnadj (Or.inr ⟨hNc_sub, h_side⟩)

set_option maxHeartbeats 800000 in -- needed for independent arc characterization
private lemma independent_arc_of_not_bipartite {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n))
    (hCR : IsConvexRoundEnum n G)
    (hnotBip : ¬G.IsBipartite)
    {a b : Fin n} (hnadj : ¬G.Adj a b) (hne : a ≠ b) :
    (∀ x y : Fin n, x ∈ CyclicInterval n a b → y ∈ CyclicInterval n a b →
      ¬G.Adj x y) ∨
    (∀ x y : Fin n, x ∈ CyclicInterval n b a → y ∈ CyclicInterval n b a →
      ¬G.Adj x y) := by
  -- Handle n < 3
  by_cases hn3 : n < 3
  · exfalso; apply hnotBip
    have : n ≤ 2 := by omega
    exact ⟨SimpleGraph.Coloring.mk (fun i => ⟨i.val, by omega⟩) (fun {v w} hadj h => by
      have hveq : v.val = w.val := by
        have := congrArg (fun (x : Fin 2) => x.val) h; simpa using this
      exact G.ne_of_adj hadj (Fin.ext hveq))⟩
  push_neg at hn3
  -- Extract interval data
  choose l hi hlhi using hCR.neighborhood_isInterval
  have hlh : ∀ j, G.neighborSet j = CyclicInterval n (l j) (hi j) \ {j} := fun j => (hlhi j).1
  have hcanon : ∀ j, j ∉ CyclicInterval n (l j) (hi j) := fun j => (hlhi j).2
  -- b ∉ [l(a), h(a)] and a ∉ [l(b), h(b)] from non-adjacency
  have hb_out_la : b ∉ CyclicInterval n (l a) (hi a) := by
    intro hb; exact hnadj (show b ∈ G.neighborSet a by rw [hlh a]; exact ⟨hb, fun h => hne h.symm⟩)
  have ha_out_lb : a ∉ CyclicInterval n (l b) (hi b) := by
    intro ha'
    exact hnadj (show a ∈ G.neighborSet b by
      rw [hlh b]; exact ⟨ha', fun h => hne h⟩).symm
  -- For any vertex c not adjacent to both a and b, [l(c), h(c)] avoids both a and b.
  -- Key: connected arc avoiding both a and b is in one open arc.
  -- no_straddle: [lc, hc] avoiding a and b can't have elements in both (a,b)_open and (b,a)_open
  have no_straddle : ∀ (lc hc : Fin n),
      a ∉ CyclicInterval n lc hc → b ∉ CyclicInterval n lc hc →
      ∀ x y, x ∈ CyclicInterval n lc hc → y ∈ CyclicInterval n lc hc →
      x ∈ CyclicInterval n a b → y ∈ CyclicInterval n b a →
      x ≠ a → x ≠ b → y ≠ a → y ≠ b → False :=
    fun _ _ ha_out hb_out _ _ => no_straddle_arcs hn3 hne ha_out hb_out
  -- Determine which arc [l(a), h(a)] is in
  have la_side : (∀ x, x ∈ CyclicInterval n (l a) (hi a) → x ∈ CyclicInterval n a b) ∨
                 (∀ x, x ∈ CyclicInterval n (l a) (hi a) → x ∈ CyclicInterval n b a) := by
    by_contra h_neg; push_neg at h_neg
    obtain ⟨⟨x, hx_la, hx_nab⟩, ⟨y, hy_la, hy_nba⟩⟩ := h_neg
    have hx_ba := (mem_arc_or hne x).resolve_left hx_nab
    have hy_ab := (mem_arc_or hne y).resolve_right hy_nba
    exact no_straddle (l a) (hi a) (hcanon a) hb_out_la y x hy_la hx_la hy_ab hx_ba
      (fun h => hcanon a (h ▸ hy_la)) (fun h => hb_out_la (h ▸ hy_la))
      (fun h => hcanon a (h ▸ hx_la)) (fun h => hb_out_la (h ▸ hx_la))
  -- Prove independence of the appropriate arc using BHY00 Lemma 3.7
  rcases la_side with h_ab | h_ba
  · -- N(a) ⊆ [a, b] → [b, a] is independent
    right; exact arc_independent_of_nbhd_side hn3 G hCR hnotBip hne hnadj
      (fun z hz => h_ab z (by rw [hlh a] at hz; exact hz.1)) (Or.inl rfl)
  · -- N(a) ⊆ [b, a] → [a, b] is independent
    left; exact arc_independent_of_nbhd_side hn3 G hCR hnotBip (Ne.symm hne)
      (fun h => hnadj h.symm)
      (fun z hz => h_ba z (by rw [hlh a] at hz; exact hz.1)) (Or.inr rfl)


/-- If `a ∉ [b, d+1]`, `b ≠ a`, and `b ≠ d+1`, then `b ∈ [a+1, d]`.
    This is a cyclic complement argument: b ∉ [d+1, a] (since b ∈ [d+2, a] would imply
    a ∈ [b, d+1], contradiction), and b ≠ d+1, so b ∈ complement [d+1, a] = [a+1, d]. -/
private lemma mem_cyclicInterval_succ_of_not_mem {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a b d : Fin n)
    (ha : a ∉ CyclicInterval n b (d + 1))
    (hba : b ≠ a)
    (hbd : b ≠ d + 1) :
    b ∈ CyclicInterval n (a + 1) d := by
  -- Use API: b ∉ [d+1, a] (complement of [a+1, d]), so b ∈ [a+1, d].
  -- Step 1: Show b ∉ [d+2, a] (if b were there, going from b to d+1 passes through a)
  -- Step 2: b ≠ d+1 (hypothesis). So b ∉ [d+1, a].
  -- Step 3: complement of [d+1, a] is [a+1, d].
  rw [mem_cyclicInterval_iff_cyclicDist]
  -- We need: cyclicDist(a+1, b) ≤ cyclicDist(a+1, d)
  -- From ha: a ∉ [b, d+1], so dist(b, a) > dist(b, d+1)
  rw [mem_cyclicInterval_iff_cyclicDist] at ha; push_neg at ha
  -- ha: cyclicDist n b (d+1) < cyclicDist n b a
  -- Use reverse distances:
  -- dist(b, a) + dist(a, b) = n (since b ≠ a)
  -- dist(b, d+1) + dist(d+1, b) = n (since b ≠ d+1)
  have hrev_ba := cyclicDist_add_reverse hba
  have hrev_bd := cyclicDist_add_reverse hbd
  -- From ha and reverses: dist(a, b) < dist(d+1, b)
  have hab_lt : cyclicDist n a b < cyclicDist n (d + 1) b := by omega
  -- Triangle: dist(a, b) = dist(a, a+1) + dist(a+1, b) since a+1 ∈ [a, b]
  -- Translation invariance: dist(a+1, d+1) = dist(a, d)
  have htrans : cyclicDist n (a + 1) (d + 1) = cyclicDist n a d := cyclicDist_add_right a d 1
  -- dist(a, b) = 1 + dist(a+1, b) (triangle via a+1 ∈ [a, b])
  have hsucc : cyclicDist n a (a + 1) = 1 := by
    simp only [cyclicDist]; have := a.isLt
    have hav : (a + 1 : Fin n).val = (a.val + 1) % n := by simp [Fin.val_add]
    by_cases hlt : a.val + 1 < n
    · rw [Nat.mod_eq_of_lt hlt] at hav; rw [hav]; split_ifs <;> omega
    · rw [show a.val + 1 = n from by omega, Nat.mod_self] at hav; rw [hav]; split_ifs <;> omega
  have ha1_in_ab : a + 1 ∈ CyclicInterval n a b := by
    rw [mem_cyclicInterval_iff_cyclicDist]; rw [hsucc]
    have : 0 < cyclicDist n a b := by
      simp only [cyclicDist]; have := a.isLt; have := b.isLt
      have : a.val ≠ b.val := fun h => hba (Fin.ext h.symm)
      split_ifs <;> omega
    omega
  have htri_ab := cyclicDist_triangle ha1_in_ab
  -- dist(a, b) = 1 + dist(a+1, b), so dist(a+1, b) = dist(a, b) - 1
  rw [hsucc] at htri_ab
  -- Similarly for d+1: dist(d+1, b) = 1 + dist(d+1+1, b)... not quite what we need.
  -- Need: dist(a+1, d) vs dist(a+1, b)
  -- We have dist(a+1, b) = dist(a, b) - 1
  -- We need dist(a+1, d) ≥ dist(a+1, b). Case split on a = d vs a ≠ d.
  -- If a ≠ d: dist(a+1, d) = dist(a, d) - 1 (by translation), and this suffices.
  -- If a = d: dist(a+1, d) = n - 1 which is maximal, so trivially ≥ dist(a+1, b).
  by_cases had : a = d
  · -- a = d: dist(a+1, b) = dist(a, b) - 1, dist(a+1, d) = dist(a+1, a) = n - 1
    subst had
    -- Goal: dist(a+1, b) ≤ dist(a+1, a)
    -- dist(a+1, b) = dist(a, b) - 1
    -- dist(a+1, a) = n - 1 (since a+1 ≠ a for n ≥ 2)
    have ha1_ne_a := fin_succ_ne hn a
    have hrev_a1a := cyclicDist_add_reverse ha1_ne_a
    rw [hsucc] at hrev_a1a
    -- dist(a+1, a) = n - 1
    have : cyclicDist n (a + 1) a = n - 1 := by omega
    rw [this]; omega
  · -- a ≠ d: use triangle on d ∈ [a+1, d+1]
    have hd_succ : cyclicDist n d (d + 1) = 1 := by
      simp only [cyclicDist]; have := d.isLt
      have hdv : (d + 1 : Fin n).val = (d.val + 1) % n := by simp [Fin.val_add]
      by_cases hlt : d.val + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at hdv; rw [hdv]; split_ifs <;> omega
      · rw [show d.val + 1 = n from by omega, Nat.mod_self] at hdv; rw [hdv]; split_ifs <;> omega
    have hd_in : d ∈ CyclicInterval n (a + 1) (d + 1) := by
      rw [mem_cyclicInterval_iff_cyclicDist, htrans]
      have ha1_in_ad : a + 1 ∈ CyclicInterval n a d := by
        rw [mem_cyclicInterval_iff_cyclicDist]; rw [hsucc]
        have : 0 < cyclicDist n a d := by
          simp only [cyclicDist]; have := a.isLt; have := d.isLt
          have : a.val ≠ d.val := fun h => had (Fin.ext h)
          split_ifs <;> omega
        omega
      have := cyclicDist_triangle ha1_in_ad
      rw [hsucc] at this; omega
    have htri_d := cyclicDist_triangle hd_in
    rw [hd_succ] at htri_d
    -- dist(a+1, d+1) = dist(a+1, d) + 1, so dist(a+1, d) = dist(a, d) - 1
    -- dist(a+1, b) = dist(a, b) - 1
    -- Need: dist(a, b) - 1 ≤ dist(a, d) - 1, i.e., dist(a, b) ≤ dist(a, d)
    -- Reverse: dist(a, b) = n - dist(b, a), dist(a, d) = n - dist(d, a)
    -- Need: dist(b, a) ≥ dist(d, a)
    -- From hab_lt: dist(a, b) < dist(d+1, b)
    -- dist(d+1, b) = n - dist(b, d+1) (since b ≠ d+1)
    -- dist(a, b) = n - dist(b, a) (since b ≠ a)
    -- So n - dist(b, a) < n - dist(b, d+1), i.e., dist(b, d+1) < dist(b, a)
    -- This is just ha. Now d+1 ∈ [b, a] (from dist(b, d+1) < dist(b, a)):
    have hd1_in_ba : d + 1 ∈ CyclicInterval n b a := by
      rw [mem_cyclicInterval_iff_cyclicDist]; omega
    -- Triangle: dist(b, a) = dist(b, d+1) + dist(d+1, a)
    have htri_ba := cyclicDist_triangle hd1_in_ba
    -- d ∈ [b, d+1] since d is always on the arc from b to d+1 (d is right before d+1).
    have hd_in_bd1 : d ∈ CyclicInterval n b (d + 1) := by
      rw [mem_cyclicInterval_iff_cyclicDist]
      have hbd1 : cyclicDist n d (d + 1) = 1 := hd_succ
      -- dist(b, d) ≤ dist(b, d+1) since d is before d+1 in cyclic order.
      simp only [cyclicDist]; have := b.isLt; have := d.isLt; have := (d + 1 : Fin n).isLt
      have hdv : (d + 1 : Fin n).val = (d.val + 1) % n := by simp [Fin.val_add]
      by_cases hlt : d.val + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at hdv; rw [hdv]; split_ifs <;> omega
      · rw [show d.val + 1 = n from by omega, Nat.mod_self] at hdv; rw [hdv]
        split_ifs <;> omega
    have htri_bd := cyclicDist_triangle hd_in_bd1
    rw [hd_succ] at htri_bd
    -- dist(b, d+1) = dist(b, d) + 1
    -- Also d ∈ [b, a] since d ∈ [b, d+1] ⊆ [b, a]
    have hd_in_ba : d ∈ CyclicInterval n b a := by
      rw [mem_cyclicInterval_iff_cyclicDist]
      have : cyclicDist n b d ≤ cyclicDist n b (d + 1) := by omega
      omega
    have htri_bda := cyclicDist_triangle hd_in_ba
    -- dist(b, a) = dist(b, d) + dist(d, a)
    -- dist(d, a) ≤ dist(b, a)
    -- Reverse: dist(a, d) = n - dist(d, a), dist(a, b) = n - dist(b, a)
    -- dist(a, b) ≤ dist(a, d) iff n - dist(b, a) ≤ n - dist(d, a) iff dist(d, a) ≤ dist(b, a)
    have hda_le : cyclicDist n d a ≤ cyclicDist n b a := by omega
    have had_rev := cyclicDist_add_reverse (Ne.symm had)
    -- dist(a, d) = n - dist(d, a), dist(a, b) = n - dist(b, a)
    -- dist(a, b) ≤ dist(a, d)
    omega

set_option maxHeartbeats 800000 in -- needed for shift invariance of adjacency
/-- BJH02 Lemma 2.4 core: For a non-bipartite convex-round graph with no nesting,
    the adjacency relation is translation-invariant: G.Adj i v ↔ G.Adj (i+1) (v+1).
    This follows from the paper's proof that interval endpoints shift by +1. -/
private lemma adj_shift_of_noNesting {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hCR : IsConvexRoundEnum n G)
    (hnotBip : ¬G.IsBipartite)
    (hnoNested : ∀ i : Fin n, ¬(G.neighborSet i ⊆ G.neighborSet (i + 1)) ∧
                              ¬(G.neighborSet (i + 1) ⊆ G.neighborSet i))
    (i : Fin n) (v : Fin n) : G.Adj i v ↔ G.Adj (i + 1) (v + 1) := by
  -- =====================================================================
  -- BJH02 Lemma 2.4 core proof: adjacency translation invariance.
  --
  -- Strategy:
  -- 1. Choose canonical interval endpoints with j ∉ [l(j), hi(j)] for all j
  -- 2. Prove l(i+1) = l(i)+1 and hi(i+1) = hi(i)+1 (the paper's argument)
  -- 3. Derive adjacency translation from endpoint shift
  -- =====================================================================
  have hn_pos : 0 < n := NeZero.pos n
  have hi1_ne_i : i + 1 ≠ i := fin_succ_ne hn i
  -- Step 1: Get canonical interval endpoints (directly from strengthened IsConvexRoundEnum)
  -- Neighborhoods are non-empty (from no-nesting: N(j) = ∅ implies N(j) ⊆ N(j+1))
  have hnonempty : ∀ j : Fin n, (G.neighborSet j).Nonempty := by
    intro j
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact (hnoNested j).1 (by rw [h]; exact Set.empty_subset _)
  -- Canonical endpoints: j ∉ [l(j), hi(j)] for all j (from IsConvexRoundEnum definition)
  choose l hi hlh_canon using hCR.neighborhood_isInterval
  have hlh : ∀ j, G.neighborSet j = CyclicInterval n (l j) (hi j) \ {j} :=
    fun j => (hlh_canon j).1
  have hcanon : ∀ j, j ∉ CyclicInterval n (l j) (hi j) :=
    fun j => (hlh_canon j).2
  -- Step 2: Adjacency characterization and crossing lemma
  have hadj_iff : ∀ j x : Fin n, G.Adj j x ↔
      x ∈ CyclicInterval n (l j) (hi j) ∧ x ≠ j := by
    intro j x
    rw [show G.Adj j x ↔ x ∈ G.neighborSet j from Iff.rfl, hlh j]
    simp only [Set.mem_diff, Set.mem_singleton_iff]
  -- BJH02 Corollary 2.1: crossing arcs give bipartiteness.
  have crossing_bip : ∀ a b c d : Fin n,
      b ∈ CyclicInterval n a c → d ∈ CyclicInterval n c a →
      a ≠ c → G.Adj a b → G.Adj c d → ¬G.Adj a c → False := by
    intro a b c d hb_ac hd_ca hne hab hcd hnac
    rcases independent_arc_of_not_bipartite G hCR hnotBip hnac hne with
      h_indep_ac | h_indep_ca
    · exact h_indep_ac a b (left_mem_cyclicInterval a c) hb_ac hab
    · exact h_indep_ca c d (left_mem_cyclicInterval c a) hd_ca hcd
  -- Endpoints are adjacent (since j ∉ [l(j), hi(j)], both l(j), hi(j) ≠ j)
  have hhi_ne : ∀ j : Fin n, hi j ≠ j := by
    intro j hh
    have := hcanon j; rw [hh] at this
    exact this (right_mem_cyclicInterval (l j) j)
  have hl_ne : ∀ j : Fin n, l j ≠ j := by
    intro j hh
    have := hcanon j; rw [hh] at this
    exact this (left_mem_cyclicInterval j (hi j))
  have hadj_hi : ∀ j : Fin n, G.Adj j (hi j) := by
    intro j
    rw [show G.Adj j (hi j) ↔ hi j ∈ G.neighborSet j from Iff.rfl, hlh j]
    exact ⟨right_mem_cyclicInterval (l j) (hi j), hhi_ne j⟩
  have hadj_l : ∀ j : Fin n, G.Adj j (l j) := by
    intro j
    rw [show G.Adj j (l j) ↔ l j ∈ G.neighborSet j from Iff.rfl, hlh j]
    exact ⟨left_mem_cyclicInterval (l j) (hi j), hl_ne j⟩
  -- Step 3: The interval [l(j), hi(j)] doesn't cover all of Fin n (since j is not in it)
  have hnotFull : ∀ j : Fin n, hi j + 1 ≠ l j := by
    intro j hfull
    -- If hi(j) + 1 = l(j), then CyclicInterval n (l j) (hi j) = Fin n
    -- But j ∉ CyclicInterval n (l j) (hi j), contradiction
    have : j ∈ CyclicInterval n (l j) (hi j) := by
      rw [mem_cyclicInterval_iff_cyclicDist]
      -- cyclicDist n (l j) (hi j) = n - 1 since l j = hi j + 1; any cyclicDist ≤ n - 1
      have hval_l := (l j).isLt
      have hval_hi := (hi j).isLt
      have hval_j := j.isLt
      simp only [cyclicDist]
      have hlj_eq : (l j).val = ((hi j).val + 1) % n := by
        have := congr_arg Fin.val hfull
        simp [Fin.val_add] at this
        exact this.symm
      by_cases hlt : (hi j).val + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at hlj_eq
        split_ifs <;> omega
      · have : (hi j).val + 1 = n := by omega
        rw [this, Nat.mod_self] at hlj_eq
        split_ifs <;> omega
    exact hcanon j this
  -- Step 4: Prove endpoint shift: hi(i+1) = hi(i) + 1
  -- BJH02 Lemma 2.4: By contradiction, assuming hi(i+1) ≠ hi(i)+1 leads to nesting.
  have h_hi_shift : hi (i + 1) = hi i + 1 := by
    -- Step 4a: hi(i+1) ∈ CyclicInterval n (hi i) i (Lemma 2.2 argument)
    -- If hi(i+1) were in (i+1, hi(i)), crossing_bip gives bipartiteness.
    have h_range : hi (i + 1) ∈ CyclicInterval n (hi i) i := by
      -- By contrapositive: hi(i+1) ∉ [hi(i), i] → bipartite (contradiction)
      by_contra h_not_in
      -- Auxiliary: compute (i+1).val
      have hsucc_val : (i + 1 : Fin n).val = (i.val + 1) % n := by
        simp [Fin.val_add]
      -- Step 1: hi(i) ≠ i + 1 (otherwise [hi(i), i] = [i+1, i] = Fin n)
      have hhi_ne_succ : hi i ≠ i + 1 := by
        intro heq; apply h_not_in; rw [heq]
        rw [mem_cyclicInterval_iff_cyclicDist]; simp only [cyclicDist]
        have := (hi (i + 1)).isLt; have := i.isLt
        by_cases hlt : i.val + 1 < n
        · rw [Nat.mod_eq_of_lt hlt] at hsucc_val; rw [hsucc_val]; split_ifs <;> omega
        · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hsucc_val
          rw [hsucc_val]; split_ifs <;> omega
      -- Step 2: hi(i+1) ∈ [i+1, hi(i)] (complement of [hi(i), i] ⊂ [i+1, hi(i)])
      have h_in_complement : hi (i + 1) ∈ CyclicInterval n (i + 1) (hi i) := by
        rw [mem_cyclicInterval_iff_cyclicDist]
        rw [mem_cyclicInterval_iff_cyclicDist] at h_not_in; push_neg at h_not_in
        simp only [cyclicDist] at h_not_in ⊢
        have := (hi (i + 1)).isLt; have := (hi i).isLt; have := i.isLt
        have : (hi i).val ≠ i.val := fun h => hhi_ne i (Fin.ext h)
        have : (hi i).val ≠ (i + 1 : Fin n).val := fun h => hhi_ne_succ (Fin.ext h)
        by_cases hlt : i.val + 1 < n
        · rw [Nat.mod_eq_of_lt hlt] at hsucc_val; rw [hsucc_val]
          split_ifs at h_not_in ⊢ <;> omega
        · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hsucc_val
          rw [hsucc_val]; split_ifs at h_not_in ⊢ <;> omega
      -- Step 3: hi(i+1) ≠ hi(i) (since hi(i+1) ∉ [hi(i), i] but hi(i) ∈ [hi(i), i])
      have hhi1_ne_hi : hi (i + 1) ≠ hi i := by
        intro heq
        exact h_not_in (heq ▸ left_mem_cyclicInterval (hi i) i)
      -- Step 4: i ∈ [hi(i), i+1] (since [hi(i), i] ⊂ [hi(i), i+1])
      have hi_in : i ∈ CyclicInterval n (hi i) (i + 1) := by
        rw [mem_cyclicInterval_iff_cyclicDist]
        have h_i_in : i ∈ CyclicInterval n (hi i) i := right_mem_cyclicInterval (hi i) i
        rw [mem_cyclicInterval_iff_cyclicDist] at h_i_in
        -- cyclicDist(hi(i), i) ≤ cyclicDist(hi(i), i+1)
        -- Since i ∈ [hi(i), i] and i+1 goes one step further:
        -- cyclicDist(hi(i), i+1) = cyclicDist(hi(i), i) + cyclicDist(i, i+1)
        -- and cyclicDist(i, i+1) ≥ 1 (since n ≥ 2, i ≠ i+1)
        have h_i_in_to_i1 : i ∈ CyclicInterval n (hi i) (i + 1) := by
          rw [mem_cyclicInterval_iff_cyclicDist]
          -- Need: cyclicDist(hi(i), i) ≤ cyclicDist(hi(i), i+1)
          -- Use: cyclicDist(hi(i), i+1) = cyclicDist(hi(i), i) + cyclicDist(i, i+1)
          -- Resolve by computation on Fin values.
          simp only [cyclicDist]
          have hhi_v := (hi i).isLt
          have hi_v := i.isLt
          have hsucc_val : (i + 1 : Fin n).val = (i.val + 1) % n := by
            simp [Fin.val_add]
          by_cases hlt : i.val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hsucc_val
            rw [hsucc_val]; split_ifs <;> omega
          · have : i.val + 1 = n := by omega
            rw [this, Nat.mod_self] at hsucc_val
            rw [hsucc_val]; split_ifs <;> omega
        exact (mem_cyclicInterval_iff_cyclicDist i (hi i) (i + 1)).mp h_i_in_to_i1
      -- Step 5: ¬G.Adj (i+1) (hi i)
      -- hi(i) is beyond hi(i+1) from i+1's perspective, so outside N(i+1).
      have hnadj : ¬G.Adj (i + 1) (hi i) := by
        intro hadj_contra
        rw [hadj_iff] at hadj_contra
        obtain ⟨hmem_hi, _⟩ := hadj_contra
        -- hmem_hi : hi(i) ∈ [l(i+1), hi(i+1)]
        -- Step A: cyclicDist(i+1, hi(i)) > cyclicDist(i+1, hi(i+1)) via triangle
        have htri := cyclicDist_triangle h_in_complement
        have hpos : 0 < cyclicDist n (hi (i + 1)) (hi i) := by
          simp only [cyclicDist]
          have := (hi (i + 1)).isLt; have := (hi i).isLt
          have : (hi (i + 1)).val ≠ (hi i).val := fun h => hhi1_ne_hi (Fin.ext h)
          split_ifs <;> omega
        -- htri + hpos: cyclicDist(i+1, hi(i+1)) < cyclicDist(i+1, hi(i))
        -- Step B: [l(i+1), hi(i+1)] ⊆ [i+1, hi(i+1)] since i+1 ∉ [l(i+1), hi(i+1)]
        -- So hmem_hi gives cyclicDist(i+1, hi(i)) ≤ cyclicDist(i+1, hi(i+1)), contradiction.
        rw [mem_cyclicInterval_iff_cyclicDist] at hmem_hi
        have hcanon_i1 := hcanon (i + 1)
        rw [mem_cyclicInterval_iff_cyclicDist] at hcanon_i1; push_neg at hcanon_i1
        simp only [cyclicDist] at hmem_hi hcanon_i1 htri hpos ⊢
        have := (l (i + 1)).isLt; have := (hi (i + 1)).isLt
        have := (hi i).isLt; have := (i + 1 : Fin n).isLt
        split_ifs at hmem_hi hcanon_i1 htri hpos ⊢ <;> omega
      -- Step 6: Apply crossing_bip
      exact crossing_bip (i + 1) (hi (i + 1)) (hi i) i
        h_in_complement
        hi_in
        (Ne.symm hhi_ne_succ)
        (hadj_hi (i + 1))
        (G.adj_symm (hadj_hi i))
        hnadj
    -- Step 4b: By contradiction, assume hi(i+1) ≠ hi(i) + 1
    by_contra h_ne
    -- Step 4c: hi(i+1) ∈ [hi(i), i] and hi(i+1) ≠ hi(i) + 1
    -- Also hi(i+1) ≠ i (since (i+1) ∉ [l(i+1), hi(i+1)] by hcanon, but hi(i+1) ∈ [l(i+1), hi(i+1)])
    -- and hi(i+1) ≠ hi(i) (would need separate argument)
    -- Let k = hi(i+1) - 1. Then k+1 = hi(i+1).
    set k := hi (i + 1) - 1 with hk_def
    -- hi(i+1) ≠ hi(i): same right endpoint would give nesting
    have hhi1_ne_hi : hi (i + 1) ≠ hi i := by
      intro heq
      by_cases h : l i ∈ CyclicInterval n (l (i + 1)) (hi i)
      · -- [l(i), hi(i)] ⊆ [l(i+1), hi(i)] → N(i) ⊆ N(i+1)
        have hsub := cyclicInterval_subset h (le_of_eq (cyclicDist_triangle h).symm)
        apply (hnoNested i).1; intro x hx
        rw [hlh i] at hx; obtain ⟨hxmem, hxne⟩ := hx
        rw [SimpleGraph.mem_neighborSet, hadj_iff, heq]
        exact ⟨hsub hxmem, fun hxi1 => hcanon (i + 1) (heq ▸ hsub (hxi1 ▸ hxmem))⟩
      · -- l(i+1) ∈ [l(i), hi(i)] → N(i+1) ⊆ N(i)
        have h' : l (i + 1) ∈ CyclicInterval n (l i) (hi i) := by
          rw [mem_cyclicInterval_iff_cyclicDist] at h ⊢; push_neg at h
          simp only [cyclicDist] at h ⊢
          have := (l i).isLt; have := (l (i + 1)).isLt; have := (hi i).isLt
          split_ifs at h ⊢ <;> omega
        have hsub := cyclicInterval_subset h' (le_of_eq (cyclicDist_triangle h').symm)
        apply (hnoNested i).2; intro x hx
        rw [hlh (i + 1)] at hx; obtain ⟨hxmem, hxne⟩ := hx
        rw [SimpleGraph.mem_neighborSet, hadj_iff]; rw [heq] at hxmem
        exact ⟨hsub hxmem, fun hxi => hcanon i (hxi ▸ hsub hxmem)⟩
    -- k is in the "gap" of N(i): k ∉ N(i)
    have hk_not_adj_i : ¬G.Adj i k := by
      have hk1 : k + 1 = hi (i + 1) := by rw [hk_def]; exact sub_add_cancel _ _
      -- Case split: k = hi(i) or k ≠ hi(i)
      by_cases hk_eq : k = hi i
      · -- k = hi(i) → k+1 = hi(i)+1 = hi(i+1) → contradiction with h_ne
        exfalso; exact h_ne (by rw [← hk1, hk_eq])
      · -- k ≠ hi(i): if k ∈ [l(i), hi(i)] then k+1 ∈ [l(i), hi(i)], but k+1 = hi(i+1)
        -- would land in [l(i), hi(i)] ∩ [hi(i), i] = {hi(i)}, so hi(i+1) = hi(i), contradiction
        intro hadj; rw [hadj_iff] at hadj; obtain ⟨hmem, _⟩ := hadj
        -- hmem : k ∈ [l(i), hi(i)], k ≠ hi(i)
        -- Step 1: [k, hi(i)] ⊆ [l(i), hi(i)] since k ∈ [l(i), hi(i)]
        have hsub := cyclicInterval_subset hmem (le_of_eq (cyclicDist_triangle hmem).symm)
        -- Step 2: k+1 ∈ [k, hi(i)] since cyclicDist(k, k+1) ≤ cyclicDist(k, hi(i))
        have hk1_in : k + 1 ∈ CyclicInterval n k (hi i) := by
          rw [mem_cyclicInterval_iff_cyclicDist]
          simp only [cyclicDist]; have := k.isLt; have := (hi i).isLt
          have : k.val ≠ (hi i).val := fun h => hk_eq (Fin.ext h)
          have hk1v : (k + 1 : Fin n).val = (k.val + 1) % n := by simp [Fin.val_add]
          by_cases hlt : k.val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hk1v; rw [hk1v]; split_ifs <;> omega
          · rw [show k.val + 1 = n from by omega, Nat.mod_self] at hk1v
            rw [hk1v]; split_ifs <;> omega
        -- Step 3: hi(i+1) ∈ [l(i), hi(i)] (from k+1 ∈ [k, hi(i)] ⊆ [l(i), hi(i)])
        have hk1_mem : hi (i + 1) ∈ CyclicInterval n (l i) (hi i) := hk1 ▸ hsub hk1_in
        -- Step 4: Contradiction from hi(i+1) ∈ [l(i), hi(i)] ∩ [hi(i), i]
        -- cyclicDist level: the two memberships + reverse sums force cyclicDist(i, l(i)) ≤ 0
        have htri1 := cyclicDist_triangle hk1_mem
        have hrev1 := cyclicDist_add_reverse hhi1_ne_hi
        have h_range' : cyclicDist n (hi i) (hi (i + 1)) ≤ cyclicDist n (hi i) i :=
          (mem_cyclicInterval_iff_cyclicDist ..).mp h_range
        have hcanon_i : cyclicDist n (l i) (hi i) < cyclicDist n (l i) i := by
          have := hcanon i
          rw [mem_cyclicInterval_iff_cyclicDist] at this
          push_neg at this; exact this
        have hi_mem : hi i ∈ CyclicInterval n (l i) i := by
          rw [mem_cyclicInterval_iff_cyclicDist]; omega
        have htri2 := cyclicDist_triangle hi_mem
        have hli_ne_i : l i ≠ i := by
          intro heq; rw [heq] at hcanon_i
          simp only [cyclicDist] at hcanon_i; split_ifs at hcanon_i <;> omega
        have hrev2 := cyclicDist_add_reverse hli_ne_i
        have hg_pos : 0 < cyclicDist n i (l i) := by
          simp only [cyclicDist]; have := i.isLt; have := (l i).isLt
          have : i.val ≠ (l i).val := fun h => hli_ne_i (Fin.ext h.symm)
          split_ifs <;> omega
        omega
    -- k ≠ i (since hi(i+1) ≠ i+1, so k ≠ i)
    have hk_ne_i : k ≠ i := by
      intro heq
      -- k = i means hi(i+1) - 1 = i, so hi(i+1) = i + 1
      -- But hcanon says (i+1) ∉ [l(i+1), hi(i+1)], contradicting hi(i+1) = i+1
      have hhi1_eq : hi (i + 1) = i + 1 := by
        have : k + 1 = i + 1 := congr_arg (· + 1) heq
        rwa [hk_def, sub_add_cancel] at this
      have := hcanon (i + 1); rw [hhi1_eq] at this
      exact this (right_mem_cyclicInterval (l (i + 1)) (i + 1))
    -- [i, k] is NOT independent (contains edge i ~ hi(i), and hi(i) ∈ [i, k])
    have h_hi_in_ik : hi i ∈ CyclicInterval n i k := by
      rw [mem_cyclicInterval_iff_cyclicDist]
      -- cyclicDist(k, k+1) = 1
      have hk1 : k + 1 = hi (i + 1) := by rw [hk_def]; exact sub_add_cancel _ _
      have hcd1 : cyclicDist n k (k + 1) = 1 := by
        simp only [cyclicDist]; have := k.isLt
        have hk1v : (k + 1 : Fin n).val = (k.val + 1) % n := by simp [Fin.val_add]
        by_cases hlt : k.val + 1 < n
        · rw [Nat.mod_eq_of_lt hlt] at hk1v; rw [hk1v]; split_ifs <;> omega
        · rw [show k.val + 1 = n from by omega, Nat.mod_self] at hk1v
          rw [hk1v]; split_ifs <;> omega
      rw [hk1] at hcd1
      -- hi(i+1) ∈ [k, i]
      have hcd_ki_pos : 0 < cyclicDist n k i := by
        simp only [cyclicDist]; have := k.isLt; have := i.isLt
        have : k.val ≠ i.val := fun h => hk_ne_i (Fin.ext h)
        split_ifs <;> omega
      have hhi1_in_ki : hi (i + 1) ∈ CyclicInterval n k i := by
        rw [mem_cyclicInterval_iff_cyclicDist]; omega
      have htri_ki := cyclicDist_triangle hhi1_in_ki
      -- cyclicDist(hi(i), i) = cyclicDist(hi(i), hi(i+1)) + cyclicDist(hi(i+1), i)
      have htri_hii := cyclicDist_triangle h_range
      have hcd_pos : 0 < cyclicDist n (hi i) (hi (i + 1)) := by
        simp only [cyclicDist]; have := (hi i).isLt; have := (hi (i + 1)).isLt
        have : (hi i).val ≠ (hi (i + 1)).val := fun h => hhi1_ne_hi (Fin.ext h.symm)
        split_ifs <;> omega
      -- Reverse distances
      have hrev_hi := cyclicDist_add_reverse (Ne.symm (hhi_ne i))
      have hrev_k := cyclicDist_add_reverse hk_ne_i
      omega
    -- By Lemma 2.1 on pair (i, k): one arc is independent.
    -- [i, k] has edge i ~ hi(i), so it's NOT independent.
    -- Therefore [k, i] IS independent.
    have h_ki_indep : ∀ x y : Fin n, x ∈ CyclicInterval n k i →
        y ∈ CyclicInterval n k i → ¬G.Adj x y := by
      have hk_not_adj_i' : ¬G.Adj k i := fun h => hk_not_adj_i (G.adj_symm h)
      rcases independent_arc_of_not_bipartite G hCR hnotBip
        hk_not_adj_i' hk_ne_i with h_ki | h_ik
      · -- [k, i] independent: this is what we want
        exact h_ki
      · -- [i, k] independent: contradiction with i ~ hi(i) ∈ [i, k]
        exact absurd (hadj_hi i) (h_ik i (hi i) (left_mem_cyclicInterval i k) h_hi_in_ik)
    -- k ~ (i+1): By Lemma 2.1 on pair (k, i+1)
    have hk_adj_i1 : G.Adj k (i + 1) := by
      -- Inline helper: cyclicDist a (a+1) = 1
      have hcd_succ_k : cyclicDist n k (k + 1) = 1 := by
        simp only [cyclicDist]; have := k.isLt
        have hk1v : (k + 1 : Fin n).val = (k.val + 1) % n := by simp [Fin.val_add]
        by_cases hlt : k.val + 1 < n
        · rw [Nat.mod_eq_of_lt hlt] at hk1v; rw [hk1v]; split_ifs <;> omega
        · rw [show k.val + 1 = n from by omega, Nat.mod_self] at hk1v
          rw [hk1v]; split_ifs <;> omega
      have hk1 : k + 1 = hi (i + 1) := by rw [hk_def]; exact sub_add_cancel _ _
      -- k ≠ i+1 (otherwise [k,i]=[i+1,i]=Fin n is independent, contradicting hadj_hi)
      have hk_ne_i1 : k ≠ i + 1 := by
        intro heq
        have hmem_hi : hi i ∈ CyclicInterval n k i := by
          rw [heq, mem_cyclicInterval_iff_cyclicDist]
          simp only [cyclicDist]; have := (hi i).isLt; have := i.isLt
          have hsv : (i + 1 : Fin n).val = (i.val + 1) % n := by simp [Fin.val_add]
          by_cases hlt : i.val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hsv; rw [hsv]; split_ifs <;> omega
          · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hsv
            rw [hsv]; split_ifs <;> omega
        exact h_ki_indep i (hi i) (right_mem_cyclicInterval k i) hmem_hi (hadj_hi i)
      by_contra hnadj
      rcases independent_arc_of_not_bipartite G hCR hnotBip hnadj hk_ne_i1
        with hind_ki1 | hind_i1k
      · -- [k, i+1] independent: contradicts (i+1) ~ (k+1)=hi(i+1) ∈ [k, i+1]
        have hk1_in : k + 1 ∈ CyclicInterval n k (i + 1) := by
          rw [mem_cyclicInterval_iff_cyclicDist]
          have hcd_pos : 0 < cyclicDist n k (i + 1) := by
            by_contra hle; push_neg at hle
            have hzero : cyclicDist n k (i + 1) = 0 := by omega
            unfold cyclicDist at hzero
            have hk_lt := k.isLt; have hi1_lt := (i + 1 : Fin n).isLt
            generalize hkv : k.val = kv at hzero hk_lt
            generalize hi1v : (i + 1 : Fin n).val = i1v at hzero hi1_lt
            split_ifs at hzero with hab
            · exact hk_ne_i1 (Fin.ext (show k.val = (i + 1 : Fin n).val by
                rw [hkv, hi1v]; omega))
            · omega
          omega
        have hadj_i1_k1 : G.Adj (i + 1) (k + 1) := hk1 ▸ hadj_hi (i + 1)
        exact hind_ki1 (i + 1) (k + 1) (right_mem_cyclicInterval k (i + 1))
          hk1_in hadj_i1_k1
      · -- [i+1, k] independent: contradicts k ~ v for some v ∈ [i+1, k]
        obtain ⟨v, hv_mem⟩ := hnonempty k
        rw [SimpleGraph.mem_neighborSet] at hv_mem
        have hv_ne_k : v ≠ k := fun h => G.loopless.irrefl k (h ▸ hv_mem)
        -- v ∉ [k, i] (independence)
        have hv_not_ki : v ∉ CyclicInterval n k i :=
          fun hmem => h_ki_indep k v (left_mem_cyclicInterval k i) hmem hv_mem
        -- v ∈ [i, k] (coverage: complement of [k, i])
        have hv_in_ik : v ∈ CyclicInterval n i k := by
          rw [mem_cyclicInterval_iff_cyclicDist] at hv_not_ki ⊢; push_neg at hv_not_ki
          have hi_in_kv : i ∈ CyclicInterval n k v := by
            rw [mem_cyclicInterval_iff_cyclicDist]; omega
          have := cyclicDist_triangle hi_in_kv
          have := cyclicDist_add_reverse hk_ne_i
          have := cyclicDist_add_reverse hv_ne_k
          omega
        -- v ≠ i
        have hv_ne_i : v ≠ i :=
          fun h => hv_not_ki (h ▸ right_mem_cyclicInterval k i)
        -- v ∈ [i+1, k] (from v ∈ [i, k], v ≠ i)
        have hv_in_i1k : v ∈ CyclicInterval n (i + 1) k := by
          rw [mem_cyclicInterval_iff_cyclicDist] at hv_in_ik ⊢
          have hcd_iv_pos : 0 < cyclicDist n i v := by
            simp only [cyclicDist]; have := i.isLt; have := v.isLt
            have : i.val ≠ v.val := fun h => hv_ne_i (Fin.ext h.symm)
            split_ifs <;> omega
          have hcd_succ_i : cyclicDist n i (i + 1) = 1 := by
            simp only [cyclicDist]; have := i.isLt
            have hsv : (i + 1 : Fin n).val = (i.val + 1) % n := by simp [Fin.val_add]
            by_cases hlt : i.val + 1 < n
            · rw [Nat.mod_eq_of_lt hlt] at hsv; rw [hsv]; split_ifs <;> omega
            · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hsv
              rw [hsv]; split_ifs <;> omega
          have hi1_in_iv : (i + 1) ∈ CyclicInterval n i v := by
            rw [mem_cyclicInterval_iff_cyclicDist]; omega
          have hi1_in_ik : (i + 1) ∈ CyclicInterval n i k := by
            rw [mem_cyclicInterval_iff_cyclicDist]; omega
          have := cyclicDist_triangle hi1_in_iv
          have := cyclicDist_triangle hi1_in_ik
          omega
        exact hind_i1k v k hv_in_i1k (right_mem_cyclicInterval (i + 1) k)
          (G.adj_symm hv_mem)
    -- Derive nesting at k: l(k) = l(k+1), giving N(k) ⊆ N(k+1) or vice versa
    -- Both k and k+1 are adjacent to i+1 but not to i
    -- This forces l(k) = l(k+1) = i+1 (the boundary vertex)
    -- Then same left endpoint → one neighborhood contains the other
    have h_nesting_k : G.neighborSet k ⊆ G.neighborSet (k + 1) ∨
                        G.neighborSet (k + 1) ⊆ G.neighborSet k := by
      have hk1 : k + 1 = hi (i + 1) := by rw [hk_def]; exact sub_add_cancel _ _
      -- k+1 ∈ [k, i] (cyclicDist(k, k+1) = 1 ≤ cyclicDist(k, i))
      have hk1_in_ki : k + 1 ∈ CyclicInterval n k i := by
        rw [mem_cyclicInterval_iff_cyclicDist]
        have hcd1 : cyclicDist n k (k + 1) = 1 := by
          simp only [cyclicDist]; have := k.isLt
          have hk1v : (k + 1 : Fin n).val = (k.val + 1) % n := by simp [Fin.val_add]
          by_cases hlt : k.val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hk1v; rw [hk1v]; split_ifs <;> omega
          · rw [show k.val + 1 = n from by omega, Nat.mod_self] at hk1v
            rw [hk1v]; split_ifs <;> omega
        have : 0 < cyclicDist n k i := by
          simp only [cyclicDist]; have := k.isLt; have := i.isLt
          have : k.val ≠ i.val := fun h => hk_ne_i (Fin.ext h)
          split_ifs <;> omega
        omega
      -- ¬G.Adj (k+1) i (from [k,i] independence)
      have hk1_not_adj_i : ¬G.Adj (k + 1) i :=
        fun h => h_ki_indep (k + 1) i hk1_in_ki (right_mem_cyclicInterval k i) h
      -- i ∉ [l(k), hi(k)] (from ¬G.Adj k i)
      have hi_not_in_k : i ∉ CyclicInterval n (l k) (hi k) :=
        fun hmem => hk_not_adj_i (G.adj_symm ((hadj_iff k i).mpr ⟨hmem, Ne.symm hk_ne_i⟩))
      -- i+1 ∈ [l(k), hi(k)] (from G.Adj k (i+1))
      have hi1_in_k : i + 1 ∈ CyclicInterval n (l k) (hi k) :=
        ((hadj_iff k (i + 1)).mp hk_adj_i1).1
      -- i ∉ [l(k+1), hi(k+1)]
      have hi_not_in_k1 : i ∉ CyclicInterval n (l (k + 1)) (hi (k + 1)) := by
        by_cases hik1 : i = k + 1
        · rw [hik1]; exact hcanon (k + 1)
        · intro hmem
          exact hk1_not_adj_i ((hadj_iff (k + 1) i).mpr ⟨hmem, hik1⟩)
      -- i+1 ∈ [l(k+1), hi(k+1)] (from G.Adj (k+1) (i+1))
      have hk1_adj_i1 : G.Adj (k + 1) (i + 1) := by
        rw [hk1]; exact G.adj_symm (hadj_hi (i + 1))
      have hi1_in_k1 : i + 1 ∈ CyclicInterval n (l (k + 1)) (hi (k + 1)) :=
        ((hadj_iff (k + 1) (i + 1)).mp hk1_adj_i1).1
      -- Boundary lemma: i ∉ [c, d] and i+1 ∈ [c, d] → c = i+1
      have boundary : ∀ c d : Fin n,
          i ∉ CyclicInterval n c d → (i + 1) ∈ CyclicInterval n c d → c = i + 1 := by
        intro c d hni hyi
        by_contra h
        rw [mem_cyclicInterval_iff_cyclicDist] at hni hyi; push_neg at hni
        simp only [cyclicDist] at hni hyi
        have := c.isLt; have := d.isLt; have := i.isLt
        have hsv : (i + 1 : Fin n).val = (i.val + 1) % n := by simp [Fin.val_add]
        have h_ne : c.val ≠ (i + 1 : Fin n).val := fun heq => h (Fin.ext heq)
        by_cases hlt : i.val + 1 < n
        · rw [Nat.mod_eq_of_lt hlt] at hsv; rw [hsv] at hyi h_ne
          split_ifs at hni hyi <;> omega
        · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hsv
          rw [hsv] at hyi h_ne; split_ifs at hni hyi <;> omega
      have hlk : l k = i + 1 := boundary (l k) (hi k) hi_not_in_k hi1_in_k
      have hlk1 : l (k + 1) = i + 1 :=
        boundary (l (k + 1)) (hi (k + 1)) hi_not_in_k1 hi1_in_k1
      -- Nesting from same left endpoint: compare right endpoints
      rcases le_total (cyclicDist n (i + 1) (hi k))
        (cyclicDist n (i + 1) (hi (k + 1))) with hle | hle
      · -- [i+1, hi(k)] ⊆ [i+1, hi(k+1)] → N(k) ⊆ N(k+1)
        left; intro v hv
        rw [SimpleGraph.mem_neighborSet] at hv ⊢
        have ⟨hv_mem, hv_ne⟩ := (hadj_iff k v).mp hv
        rw [hlk] at hv_mem
        refine (hadj_iff (k + 1) v).mpr ⟨?_, ?_⟩
        · rw [hlk1]; rw [mem_cyclicInterval_iff_cyclicDist] at hv_mem ⊢
          exact le_trans hv_mem hle
        · intro heq; rw [heq] at hv
          exact h_ki_indep k (k + 1) (left_mem_cyclicInterval k i) hk1_in_ki hv
      · -- [i+1, hi(k+1)] ⊆ [i+1, hi(k)] → N(k+1) ⊆ N(k)
        right; intro v hv
        rw [SimpleGraph.mem_neighborSet] at hv ⊢
        have ⟨hv_mem, hv_ne⟩ := (hadj_iff (k + 1) v).mp hv
        rw [hlk1] at hv_mem
        refine (hadj_iff k v).mpr ⟨?_, ?_⟩
        · rw [hlk]; rw [mem_cyclicInterval_iff_cyclicDist] at hv_mem ⊢
          exact le_trans hv_mem hle
        · intro heq; rw [heq] at hv
          exact h_ki_indep (k + 1) k hk1_in_ki (left_mem_cyclicInterval k i) hv
    -- Contradiction with hnoNested at k
    rcases h_nesting_k with h1 | h2
    · exact (hnoNested k).1 h1
    · exact (hnoNested k).2 h2
  -- Step 5: Prove endpoint shift: l(i+1) = l(i) + 1 (symmetric argument)
  have h_l_shift : l (i + 1) = l i + 1 := by
    -- Step 5a: l(i) ∉ [l(i+1), hi(i+1)] (otherwise N(i) ⊆ N(i+1))
    have hl_not_in : l i ∉ CyclicInterval n (l (i + 1)) (hi (i + 1)) := by
      intro hmem
      -- l(i) ∈ [l(i+1), hi(i+1)] and dist(l(i), hi(i)) ≤ dist(l(i), hi(i+1))
      -- since hi(i+1) = hi(i)+1 and hi(i)+1 ≠ l(i) (from hnotFull)
      have hdist_le : cyclicDist n (l (i + 1)) (l i) + cyclicDist n (l i) (hi i) ≤
          cyclicDist n (l (i + 1)) (hi (i + 1)) := by
        have htri := cyclicDist_triangle hmem
        rw [h_hi_shift]
        -- Need: dist(l(i), hi(i)) ≤ dist(l(i), hi(i)+1)
        -- Since hi(i)+1 ≠ l(i), dist(l(i), hi(i)+1) = dist(l(i), hi(i)) + 1
        have hne_lhi : l i ≠ hi i + 1 := fun h => hnotFull i (by rw [← h])
        have hi_in_lh1 : hi i ∈ CyclicInterval n (l i) (hi i + 1) := by
          rw [mem_cyclicInterval_iff_cyclicDist]
          simp only [cyclicDist]; have := (l i).isLt; have := (hi i).isLt
          have hv : (hi i + 1 : Fin n).val = ((hi i).val + 1) % n := by
            simp only [Fin.val_add, Fin.coe_ofNat_eq_mod,
              Nat.mod_eq_of_lt (show 1 < n from by omega)]
          have : (l i).val ≠ ((hi i).val + 1) % n := fun h =>
            hne_lhi (Fin.ext (by
              simp only [Fin.val_add, Fin.coe_ofNat_eq_mod,
                Nat.mod_eq_of_lt (show 1 < n from by omega)]
              exact h))
          by_cases hlt : (hi i).val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hv this; rw [hv]; split_ifs <;> omega
          · rw [show (hi i).val + 1 = n from by omega, Nat.mod_self] at hv this
            rw [hv]; split_ifs <;> omega
        have htri_lh := cyclicDist_triangle hi_in_lh1
        -- Need: cyclicDist(l(i+1), l(i)) + cyclicDist(l(i), hi(i))
        --   ≤ cyclicDist(l(i+1), hi(i)+1)
        -- From htri (the outer triangle):
        --   cyclicDist(l(i+1), l(i)) + cyclicDist(l(i), hi(i+1))
        --   ≤ cyclicDist(l(i+1), hi(i+1))
        -- From htri_lh:
        --   cyclicDist(l(i), hi(i)) + cyclicDist(hi(i), hi(i)+1)
        --   ≤ cyclicDist(l(i), hi(i)+1)
        -- And cyclicDist(hi(i), hi(i)+1) = 1
        -- Also hi(i+1) = hi(i)+1 from h_hi_shift, so
        --   cyclicDist(l(i), hi(i+1)) = cyclicDist(l(i), hi(i)+1)
        rw [h_hi_shift] at htri
        omega
      have hsub := cyclicInterval_subset hmem hdist_le
      -- N(i) ⊆ N(i+1): for x ∈ N(i), x ∈ [l(i), hi(i)] ⊆ [l(i+1), hi(i+1)], x ≠ i+1
      apply (hnoNested i).1; intro x hx
      rw [hlh i] at hx; obtain ⟨hxmem, hxne⟩ := hx
      rw [SimpleGraph.mem_neighborSet, hadj_iff]
      constructor
      · exact hsub hxmem
      · intro hxi1
        exact hcanon (i + 1) (hsub (hxi1 ▸ hxmem))
    -- Step 5b: l(i+1) ≠ l(i) (otherwise N(i) ⊆ N(i+1) again)
    have hl1_ne_l : l (i + 1) ≠ l i := by
      intro heq
      -- If l(i+1) = l(i), then [l(i), hi(i)] ⊆ [l(i), hi(i)+1] = [l(i+1), hi(i+1)]
      have hsub : CyclicInterval n (l i) (hi i) ⊆
          CyclicInterval n (l (i + 1)) (hi (i + 1)) := by
        rw [heq, h_hi_shift]
        intro x hx; rw [mem_cyclicInterval_iff_cyclicDist] at hx ⊢
        have hi_in : hi i ∈ CyclicInterval n (l i) (hi i + 1) := by
          rw [mem_cyclicInterval_iff_cyclicDist]
          simp only [cyclicDist]; have := (l i).isLt; have := (hi i).isLt
          have hne_lhi : l i ≠ hi i + 1 := fun h => hnotFull i (by rw [← h])
          have hv : (hi i + 1 : Fin n).val = ((hi i).val + 1) % n := by
            simp only [Fin.val_add, Fin.coe_ofNat_eq_mod,
              Nat.mod_eq_of_lt (show 1 < n from by omega)]
          have : (l i).val ≠ ((hi i).val + 1) % n := fun h =>
            hne_lhi (Fin.ext (by
              simp only [Fin.val_add, Fin.coe_ofNat_eq_mod,
                Nat.mod_eq_of_lt (show 1 < n from by omega)]
              exact h))
          by_cases hlt : (hi i).val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hv this; rw [hv]; split_ifs <;> omega
          · rw [show (hi i).val + 1 = n from by omega, Nat.mod_self] at hv this
            rw [hv]; split_ifs <;> omega
        have := cyclicDist_triangle hi_in
        omega
      apply (hnoNested i).1; intro x hx
      rw [hlh i] at hx; obtain ⟨hxmem, hxne⟩ := hx
      rw [SimpleGraph.mem_neighborSet, hadj_iff]
      exact ⟨hsub hxmem, fun hxi1 => hcanon (i + 1) (hsub (hxi1 ▸ hxmem))⟩
    -- Step 5c: By contradiction, assume l(i+1) ≠ l(i)+1
    by_contra h_ne
    -- Step 5d: Set k = l(i+1) - 1
    set k := l (i + 1) - 1 with hk_def
    have hk1 : k + 1 = l (i + 1) := by rw [hk_def]; exact sub_add_cancel _ _
    -- l(i+1) ≠ l(i)+1, so k ≠ l(i)
    have hk_ne_l : k ≠ l i := by
      intro heq; exact h_ne (by rw [← hk1, heq])
    -- k ∈ [l(i), hi(i)]: case split on l(i+1) = hi(i) + 1
    have hk_in_li_hi : k ∈ CyclicInterval n (l i) (hi i) := by
      by_cases hl1_eq_hi1 : l (i + 1) = hi i + 1
      · -- l(i+1) = hi(i) + 1, so k = l(i+1) - 1 = hi(i) + 1 - 1 = hi(i)
        have : k = hi i := by rw [hk_def, hl1_eq_hi1]; simp
        rw [this]; exact right_mem_cyclicInterval (l i) (hi i)
      · -- l(i+1) ≠ hi(i) + 1: use complement argument
        have l_range : l (i + 1) ∈ CyclicInterval n (l i + 1) (hi i) :=
          mem_cyclicInterval_succ_of_not_mem hn (l i) (l (i + 1)) (hi i)
            (fun hmem => hl_not_in (h_hi_shift ▸ hmem))
            hl1_ne_l
            hl1_eq_hi1
        -- Use cyclic distance algebra instead of unfolding to ℕ
        -- Key identity: cyclicDist(a, a+1) = 1
        have hcd1 : cyclicDist n (l i) (l i + 1) = 1 := by
          simp only [cyclicDist]; have := (l i).isLt
          have hav : (l i + 1 : Fin n).val = ((l i).val + 1) % n := by simp [Fin.val_add]
          by_cases hlt : (l i).val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hav; rw [hav]; split_ifs <;> omega
          · rw [show (l i).val + 1 = n from by omega, Nat.mod_self] at hav
            rw [hav]; split_ifs <;> omega
        -- Translation: cyclicDist(l(i), k) = cyclicDist(l(i)+1, l(i+1))
        have hshift : cyclicDist n (l i) k = cyclicDist n (l i + 1) (l (i + 1)) := by
          have := cyclicDist_add_right (l i) k 1; rw [hk1] at this; exact this.symm
        -- From l_range: cyclicDist(l(i)+1, l(i+1)) ≤ cyclicDist(l(i)+1, hi(i))
        have hl_range_dist := (mem_cyclicInterval_iff_cyclicDist _ _ _).mp l_range
        -- Prove l(i) ≠ hi(i): if l(i) = hi(i), then l(i) ∈ [l(i+1), hi(i+1)]
        have hli_ne_hi : l i ≠ hi i := by
          intro heq; apply hl_not_in; rw [h_hi_shift, ← heq]
          -- l(i)+1 ∈ [l(i), l(i+1)] since 1 ≤ dist(l(i), l(i+1))
          have hpos : 0 < cyclicDist n (l i) (l (i + 1)) := by
            simp only [cyclicDist]; have := (l i).isLt; have := (l (i + 1)).isLt
            have : (l i).val ≠ (l (i + 1)).val := fun h => hl1_ne_l (Fin.ext h.symm)
            split_ifs <;> omega
          have hli1_in : l i + 1 ∈ CyclicInterval n (l i) (l (i + 1)) := by
            rw [mem_cyclicInterval_iff_cyclicDist, hcd1]; omega
          -- Triangle + reverse identities: dist(l(i+1), l(i)) ≤ dist(l(i+1), l(i)+1)
          rw [mem_cyclicInterval_iff_cyclicDist]
          have htri_ll1 := cyclicDist_triangle hli1_in
          have hrev := cyclicDist_add_reverse hl1_ne_l
          have hrev1 := cyclicDist_add_reverse h_ne
          omega
        -- l(i)+1 ∈ [l(i), hi(i)] since 1 ≤ dist(l(i), hi(i))
        have hli1_in_lhi : l i + 1 ∈ CyclicInterval n (l i) (hi i) := by
          rw [mem_cyclicInterval_iff_cyclicDist, hcd1]
          have : 0 < cyclicDist n (l i) (hi i) := by
            simp only [cyclicDist]; have := (l i).isLt; have := (hi i).isLt
            have : (l i).val ≠ (hi i).val := fun h => hli_ne_hi (Fin.ext h)
            split_ifs <;> omega
          omega
        -- Triangle: dist(l(i), hi(i)) = 1 + dist(l(i)+1, hi(i))
        have htri := cyclicDist_triangle hli1_in_lhi
        -- Combine: dist(l(i), k) ≤ dist(l(i), hi(i))
        rw [mem_cyclicInterval_iff_cyclicDist, hshift]
        linarith [hcd1, htri, hl_range_dist]
    -- k ≠ i (since k ∈ [l(i), hi(i)] and i ∉ [l(i), hi(i)])
    have hk_ne_i : k ≠ i := fun heq => hcanon i (heq ▸ hk_in_li_hi)
    -- G.Adj i k (since k ∈ [l(i), hi(i)] and k ≠ i)
    have hk_adj_i : G.Adj i k := (hadj_iff i k).mpr ⟨hk_in_li_hi, hk_ne_i⟩
    -- ¬G.Adj (i+1) k (k is just outside N(i+1) from the left)
    have hk_not_adj_i1 : ¬G.Adj (i + 1) k := by
      intro hadj_contra
      rw [hadj_iff] at hadj_contra
      obtain ⟨hmem_k, hk_ne_i1⟩ := hadj_contra
      -- k ∈ [l(i+1), hi(i+1)], so dist(l(i+1), k) ≤ dist(l(i+1), hi(i+1))
      -- But k = l(i+1)-1, so dist(l(i+1), k) = n-1 (going almost all the way around)
      -- And dist(l(i+1), hi(i+1)) < n (since (i+1) ∉ [l(i+1), hi(i+1)])
      -- Need dist(l(i+1), hi(i+1)) < n-1 to get contradiction
      rw [mem_cyclicInterval_iff_cyclicDist] at hmem_k
      have hcanon_i1 := hcanon (i + 1)
      rw [mem_cyclicInterval_iff_cyclicDist] at hcanon_i1; push_neg at hcanon_i1
      -- dist(l(i+1), k) = n-1 (since k = l(i+1)-1, one step back)
      have hk_dist : cyclicDist n (l (i + 1)) k = n - 1 := by
        -- k + 1 = l(i+1), so dist(k, l(i+1)) = dist(k, k+1) = 1
        -- By complement: dist(l(i+1), k) = n - 1
        have hk_ne_l1 : k ≠ l (i + 1) := by
          intro heq; rw [heq] at hk1
          -- hk1 : l(i+1) + 1 = l(i+1), contradiction
          have hv := congr_arg Fin.val hk1
          simp only [Fin.val_add, Fin.coe_ofNat_eq_mod,
            Nat.mod_eq_of_lt (show 1 < n from by omega)] at hv
          -- hv : ((l (i+1)).val + 1) % n = (l (i+1)).val
          have hl1_lt := (l (i + 1)).isLt
          by_cases hlt : (l (i + 1)).val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hv; omega
          · rw [show (l (i + 1)).val + 1 = n from by omega, Nat.mod_self] at hv; omega
        -- Inline cyclicDist_succ: dist(k, k+1) = 1
        have hcd_k_k1 : cyclicDist n k (k + 1) = 1 := by
          simp only [cyclicDist]; have := k.isLt
          have hkv : (k + 1 : Fin n).val = (k.val + 1) % n := by simp [Fin.val_add]
          by_cases hlt : k.val + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hkv; rw [hkv]; split_ifs <;> omega
          · rw [show k.val + 1 = n from by omega, Nat.mod_self] at hkv
            rw [hkv]; split_ifs <;> omega
        rw [hk1] at hcd_k_k1
        have hrev := cyclicDist_add_reverse (Ne.symm hk_ne_l1)
        omega
      -- Need: dist(l(i+1), hi(i+1)) < n-1
      -- Since hcanon: dist(l(i+1), i+1) > dist(l(i+1), hi(i+1))
      -- And hnotFull: hi(i+1) + 1 ≠ l(i+1), so dist(l(i+1), hi(i+1)) < n-1
      have hlt_n1 : cyclicDist n (l (i + 1)) (hi (i + 1)) < n - 1 := by
        by_contra hge
        push_neg at hge
        -- dist ≤ n-1 always, so dist = n-1
        have hle : cyclicDist n (l (i + 1)) (hi (i + 1)) ≤ n - 1 := by
          simp only [cyclicDist]; have := (l (i + 1)).isLt; have := (hi (i + 1)).isLt
          split_ifs <;> omega
        have heq : cyclicDist n (l (i + 1)) (hi (i + 1)) = n - 1 := by omega
        -- This means hi(i+1) = l(i+1) - 1, i.e., hi(i+1) + 1 = l(i+1)
        simp only [cyclicDist] at heq
        have := (l (i + 1)).isLt; have := (hi (i + 1)).isLt
        have hfull : hi (i + 1) + 1 = l (i + 1) := by
          have h1v : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt (show 1 < n by omega)
          split_ifs at heq with hab
          · have hvals : (hi (i + 1)).val = n - 1 ∧ (l (i + 1)).val = 0 := by omega
            ext; simp only [Fin.val_add, h1v]
            rw [show (hi (i + 1)).val + 1 = n from by omega, Nat.mod_self]
            exact hvals.2.symm
          · push_neg at hab
            ext; simp only [Fin.val_add, h1v]
            rw [Nat.mod_eq_of_lt (show (hi (i + 1)).val + 1 < n from by omega)]
            omega
        exact hnotFull (i + 1) hfull
      omega
    -- k ≠ i+1 (cyclic distance argument: if k = i+1, then l(i+1) = i+2 = l(i)+1, contradiction)
    have hk_ne_i1 : k ≠ i + 1 := by
      intro heq
      -- k = i+1 means l(i+1) = k+1 = i+2
      have hl1_eq : l (i + 1) = i + 1 + 1 := by rw [← hk1, heq]
      -- Also l(i+1) ∈ [l(i)+1, hi(i)] and l(i+1) ≠ l(i)+1
      -- k = i+1, so i+1 ∈ [l(i), hi(i)] (since k ∈ [l(i), hi(i)])
      have hi1_in : i + 1 ∈ CyclicInterval n (l i) (hi i) := heq ▸ hk_in_li_hi
      -- From hcanon: dist(l(i), i) > dist(l(i), hi(i))
      -- Since i ∉ [l(i), hi(i)] but i+1 ∈ [l(i), hi(i)]:
      --   dist(l(i), i+1) ≤ dist(l(i), hi(i)) < dist(l(i), i)
      -- Case split: if l(i) = i+1 then l(i+1) = i+2 = l(i)+1 contradicts h_ne.
      by_cases hli_eq : l i = i + 1
      · exact h_ne (by rw [hl1_eq, hli_eq])
      · -- l(i) ≠ i+1 and i+1 ∈ [l(i), hi(i)]
        -- i+1 ∈ [l(i), hi(i)] ⊆ [l(i), i], so dist(l(i), i+1) ≤ dist(l(i), hi(i)) < dist(l(i), i).
        -- Triangle: dist(l(i), i) = dist(l(i), i+1) + dist(i+1, i), giving contradiction since
        -- dist(i+1, i) = n-1 forces dist(l(i), i) ≥ n, but dist ≤ n-1.
        have hi1_in_li : i + 1 ∈ CyclicInterval n (l i) i := by
          rw [mem_cyclicInterval_iff_cyclicDist]
          rw [mem_cyclicInterval_iff_cyclicDist] at hi1_in
          have hcanon_i := hcanon i
          rw [mem_cyclicInterval_iff_cyclicDist] at hcanon_i; push_neg at hcanon_i
          omega
        have htri_li_i := cyclicDist_triangle hi1_in_li
        -- dist(i+1, i) = n-1 (since i ≠ i+1)
        have hcd_i1_i : cyclicDist n (i + 1) i = n - 1 := by
          have hrev := cyclicDist_add_reverse hi1_ne_i
          have : cyclicDist n i (i + 1) = 1 := by
            simp only [cyclicDist]; have := i.isLt
            have hsv : (i + 1 : Fin n).val = (i.val + 1) % n := by simp [Fin.val_add]
            by_cases hlt : i.val + 1 < n
            · rw [Nat.mod_eq_of_lt hlt] at hsv; rw [hsv]; split_ifs <;> omega
            · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hsv
              rw [hsv]; split_ifs <;> omega
          omega
        -- dist(l(i), i) = dist(l(i), i+1) + (n-1) ≥ n
        -- dist(l(i), i) ≤ n-1 but dist(l(i), i+1) ≥ 1, contradiction.
        have hcd_pos : 0 < cyclicDist n (l i) (i + 1) := by
          simp only [cyclicDist]; have := (l i).isLt; have := (i + 1 : Fin n).isLt
          have : (l i).val ≠ (i + 1 : Fin n).val := fun h => hli_eq (Fin.ext h)
          split_ifs <;> omega
        have hle : cyclicDist n (l i) i ≤ n - 1 := by
          simp only [cyclicDist]; have := (l i).isLt; have := i.isLt
          split_ifs <;> omega
        omega
    -- l(i) ∈ [i+1, k]: i is in the gap between hi(i) and l(i), so going clockwise
    -- from i+1 we reach l(i) before k (which is in [l(i), hi(i)]).
    have hl_in_i1k : l i ∈ CyclicInterval n (i + 1) k := by
      rw [mem_cyclicInterval_iff_cyclicDist]
      -- Cyclic order from i+1: ..., l(i), ..., k, ..., hi(i), so dist(i+1, l(i)) ≤ dist(i+1, k).
      have hcanon_i := hcanon i
      rw [mem_cyclicInterval_iff_cyclicDist] at hcanon_i; push_neg at hcanon_i
      rw [mem_cyclicInterval_iff_cyclicDist] at hk_in_li_hi
      -- Compute directly using Fin.val.
      simp only [cyclicDist] at hcanon_i hk_in_li_hi ⊢
      have := (l i).isLt; have := (hi i).isLt; have := i.isLt; have := k.isLt
      have hk_ne_i_val : k.val ≠ i.val := fun h => hk_ne_i (Fin.ext h)
      have hli_ne_i_val : (l i).val ≠ i.val := fun h => (hl_ne i) (Fin.ext h)
      have hsv : (i + 1 : Fin n).val = (i.val + 1) % n := by simp [Fin.val_add]
      rw [hsv] at ⊢
      by_cases hlt : i.val + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at ⊢
        split_ifs at hcanon_i hk_in_li_hi ⊢ <;> omega
      · rw [show i.val + 1 = n from by omega, Nat.mod_self] at ⊢
        split_ifs at hcanon_i hk_in_li_hi ⊢ <;> omega
    -- The arc [k, i+1] contains the edge (i+1) ~ (k+1), so it is not independent.
    -- By independent_arc, [i+1, k] is independent.
    have h_i1k_indep : ∀ x y : Fin n, x ∈ CyclicInterval n (i + 1) k →
        y ∈ CyclicInterval n (i + 1) k → ¬G.Adj x y := by
      have hk_not_adj_i1' : ¬G.Adj (i + 1) k := hk_not_adj_i1
      rcases independent_arc_of_not_bipartite G hCR hnotBip
        hk_not_adj_i1' (Ne.symm hk_ne_i1) with h_i1k | h_ki1
      · exact h_i1k
      · -- [k, i+1] independent: contradiction with G.Adj (i+1) (k+1) and both in [k, i+1]
        exfalso
        have hk1_in_ki1 : k + 1 ∈ CyclicInterval n k (i + 1) := by
          rw [mem_cyclicInterval_iff_cyclicDist]
          have hcd1 : cyclicDist n k (k + 1) = 1 := by
            simp only [cyclicDist]; have := k.isLt
            have hkv : (k + 1 : Fin n).val = (k.val + 1) % n := by simp [Fin.val_add]
            by_cases hlt : k.val + 1 < n
            · rw [Nat.mod_eq_of_lt hlt] at hkv; rw [hkv]; split_ifs <;> omega
            · rw [show k.val + 1 = n from by omega, Nat.mod_self] at hkv
              rw [hkv]; split_ifs <;> omega
          have : 0 < cyclicDist n k (i + 1) := by
            simp only [cyclicDist]; have hklt := k.isLt
            have hkne : k.val ≠ (i + 1 : Fin n).val := fun h => hk_ne_i1 (Fin.ext h)
            have hi1v : (i + 1 : Fin n).val = (i.val + 1) % n := by simp [Fin.val_add]
            by_cases hilt : i.val + 1 < n
            · rw [Nat.mod_eq_of_lt hilt] at hi1v; rw [hi1v]; split_ifs <;> omega
            · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hi1v
              rw [hi1v]; split_ifs <;> omega
          omega
        exact h_ki1 (i + 1) (k + 1)
          (right_mem_cyclicInterval k (i + 1))
          hk1_in_ki1
          (hk1 ▸ hadj_l (i + 1))
    -- Nesting at (k-1, k): both have hi = i
    -- Step A: k-1 ∈ [i+1, k]
    have hk_sub := k - 1
    -- k-1 ∈ [i+1, k]: dist(i+1, k-1) ≤ dist(i+1, k)
    have hk1_in_i1k : k - 1 ∈ CyclicInterval n (i + 1) k := by
      rw [mem_cyclicInterval_iff_cyclicDist]
      simp only [cyclicDist]
      have hi1lt := (i + 1 : Fin n).isLt; have hklt := k.isLt
      -- Resolve (i + 1 : Fin n).val to eliminate %
      have hi1v : (i + 1 : Fin n).val = (i.val + 1) % n := by simp [Fin.val_add]
      -- Resolve (k - 1 : Fin n).val
      have hkm1v : (k - 1 : Fin n).val = (k.val + n - 1) % n := by
        simp only [Fin.val_sub, show (1 : Fin n).val = 1 from Nat.mod_eq_of_lt (by linarith)]
        congr 1; clear_value k; clear h_hi_shift h_ne; omega
      by_cases hilt : i.val + 1 < n <;> by_cases hklt0 : k.val = 0
      · rw [Nat.mod_eq_of_lt hilt] at hi1v; rw [hklt0] at hkm1v
        simp only [zero_add, Nat.self_sub_mod] at hkm1v
        rw [hi1v, hkm1v]; split_ifs <;> omega
      · rw [Nat.mod_eq_of_lt hilt] at hi1v
        have hkm1s : (k.val + n - 1) % n = k.val - 1 := by
          rw [show k.val + n - 1 = k.val - 1 + n from by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hkm1s] at hkm1v; rw [hi1v, hkm1v]; split_ifs <;> omega
      · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hi1v
        rw [hklt0] at hkm1v; simp only [zero_add, Nat.self_sub_mod] at hkm1v
        rw [hi1v, hkm1v]; split_ifs <;> omega
      · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hi1v
        have hkm1s : (k.val + n - 1) % n = k.val - 1 := by
          rw [show k.val + n - 1 = k.val - 1 + n from by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hkm1s] at hkm1v; rw [hi1v, hkm1v]; split_ifs <;> omega
    -- k-1 ≠ i (if k-1 = i then k = i+1, contradicting hk_ne_i1)
    have hkm1_ne_i : k - 1 ≠ i := by
      intro heq
      have : k = i + 1 := by
        have := congr_arg (· + 1) heq
        simp only [sub_add_cancel] at this
        exact this
      exact hk_ne_i1 this
    -- G.Adj i (k-1): k-1 ∈ [l(i), hi(i)] and k-1 ≠ i
    have hkm1_in : k - 1 ∈ CyclicInterval n (l i) (hi i) := by
      rw [mem_cyclicInterval_iff_cyclicDist]
      rw [mem_cyclicInterval_iff_cyclicDist] at hk_in_li_hi
      -- k ∈ [l(i), hi(i)], k ≠ l(i) (hk_ne_l)
      -- k ∈ [l(i)+1, hi(i)] (since k ∈ [l(i), hi(i)] and k ≠ l(i))
      -- So dist(l(i), k) ≥ 1
      -- k-1 is one step before k: dist(l(i), k-1) = dist(l(i), k) - 1 ≤ dist(l(i), hi(i))
      simp only [cyclicDist] at hk_in_li_hi ⊢
      have := (l i).isLt; have := (hi i).isLt; have := k.isLt
      have hk_ne_l_val : k.val ≠ (l i).val := fun h => hk_ne_l (Fin.ext h)
      have hkm1v : (k - 1 : Fin n).val = (k.val + n - 1) % n := by
        simp only [Fin.val_sub, show (1 : Fin n).val = 1 from Nat.mod_eq_of_lt (by linarith)]
        congr 1; clear_value k; clear h_hi_shift h_ne; omega
      by_cases hlt : k.val = 0
      · rw [hlt] at hkm1v; simp only [zero_add, Nat.self_sub_mod] at hkm1v; rw [hkm1v]
        clear_value k; clear h_hi_shift h_ne hi1_ne_i hk_def hk1 hk_ne_i1
        split_ifs at hk_in_li_hi ⊢ <;> omega
      · have : (k.val + n - 1) % n = k.val - 1 := by
          rw [show k.val + n - 1 = k.val - 1 + n from by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [this] at hkm1v; rw [hkm1v]
        split_ifs at hk_in_li_hi ⊢ <;> omega
    have hkm1_adj_i : G.Adj i (k - 1) :=
      (hadj_iff i (k - 1)).mpr ⟨hkm1_in, hkm1_ne_i⟩
    -- ¬G.Adj (k-1) (i+1) (from [i+1, k] independence)
    have hkm1_not_adj_i1 : ¬G.Adj (k - 1) (i + 1) :=
      fun h => h_i1k_indep (i + 1) (k - 1) (left_mem_cyclicInterval (i + 1) k) hk1_in_i1k
        (G.adj_symm h)
    -- ¬G.Adj k (i+1) (from [i+1, k] independence)
    have hk_not_adj_i1' : ¬G.Adj k (i + 1) :=
      fun h => h_i1k_indep (i + 1) k (left_mem_cyclicInterval (i + 1) k)
        (right_mem_cyclicInterval (i + 1) k) (G.adj_symm h)
    -- Boundary lemma (right): i ∈ [c, d] and (i+1) ∉ [c, d] → d = i
    have boundary_right : ∀ c d : Fin n,
        (i + 1) ∉ CyclicInterval n c d → i ∈ CyclicInterval n c d → d = i := by
      intro c d hni hyi
      by_contra h
      rw [mem_cyclicInterval_iff_cyclicDist] at hni hyi; push_neg at hni
      simp only [cyclicDist] at hni hyi
      have := c.isLt; have := d.isLt; have := i.isLt
      have hsv : (i + 1 : Fin n).val = (i.val + 1) % n := by simp [Fin.val_add]
      have h_ne : d.val ≠ i.val := fun heq => h (Fin.ext heq)
      by_cases hlt : i.val + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at hsv; rw [hsv] at hni
        split_ifs at hni hyi <;> omega
      · rw [show i.val + 1 = n from by omega, Nat.mod_self] at hsv
        rw [hsv] at hni; split_ifs at hni hyi <;> omega
    -- hi(k-1) = i: from boundary_right
    have hhi_km1 : hi (k - 1) = i := by
      apply boundary_right (l (k - 1)) (hi (k - 1))
      · -- (i+1) ∉ [l(k-1), hi(k-1)]
        by_cases hik : i + 1 = k - 1
        · rw [hik]; exact hcanon (k - 1)
        · intro hmem
          exact hkm1_not_adj_i1
            ((hadj_iff (k - 1) (i + 1)).mpr ⟨hmem, hik⟩)
      · -- i ∈ [l(k-1), hi(k-1)]
        have : G.Adj (k - 1) i := G.adj_symm hkm1_adj_i
        exact ((hadj_iff (k - 1) i).mp this).1
    -- hi(k) = i: from boundary_right
    have hhi_k : hi k = i := by
      apply boundary_right (l k) (hi k)
      · -- (i+1) ∉ [l(k), hi(k)]
        by_cases hik : i + 1 = k
        · rw [hik]; exact hcanon k
        · intro hmem
          exact hk_not_adj_i1'
            ((hadj_iff k (i + 1)).mpr ⟨hmem, hik⟩)
      · -- i ∈ [l(k), hi(k)]
        have : G.Adj k i := G.adj_symm hk_adj_i
        exact ((hadj_iff k i).mp this).1
    -- Nesting at (k-1, k): same right endpoint hi = i, compare left endpoints
    have h_nesting_km1 : G.neighborSet (k - 1) ⊆ G.neighborSet k ∨
                          G.neighborSet k ⊆ G.neighborSet (k - 1) := by
      -- k ∈ [k-1, i] (k is one step from k-1)
      have hk_in_km1i : k ∈ CyclicInterval n (k - 1) i := by
        rw [mem_cyclicInterval_iff_cyclicDist]
        have hcd1 : cyclicDist n (k - 1) k = 1 := by
          simp only [cyclicDist]; have := k.isLt
          have hkm1v : (k - 1 : Fin n).val = (k.val + n - 1) % n := by
            simp only [Fin.val_sub, show (1 : Fin n).val = 1 from Nat.mod_eq_of_lt (by linarith)]
            congr 1; clear_value k; clear h_hi_shift h_ne; omega
          by_cases hlt : k.val = 0
          · rw [hlt] at hkm1v
            simp only [zero_add, Nat.self_sub_mod] at hkm1v; rw [hkm1v]
            clear_value k; clear h_hi_shift h_ne hi1_ne_i hk_def hk1 hk_ne_i1
            split_ifs <;> omega
          · have : (k.val + n - 1) % n = k.val - 1 := by
              rw [show k.val + n - 1 = k.val - 1 + n from by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [this] at hkm1v; rw [hkm1v]; split_ifs <;> omega
        have : 0 < cyclicDist n (k - 1) i := by
          simp only [cyclicDist]; have := (k - 1 : Fin n).isLt; have := i.isLt
          have : (k - 1 : Fin n).val ≠ i.val := fun h => hkm1_ne_i (Fin.ext h)
          split_ifs <;> omega
        omega
      -- ¬G.Adj (k-1) k (from [i+1, k] independence: k-1 ∈ [i+1, k] and k ∈ [i+1, k])
      have hkm1_not_adj_k : ¬G.Adj (k - 1) k :=
        fun h => h_i1k_indep (k - 1) k hk1_in_i1k (right_mem_cyclicInterval (i + 1) k) h
      -- N(k-1) = [l(k-1), i] \ {k-1} and N(k) = [l(k), i] \ {k}: same right endpoint,
      -- so nesting follows from comparing left endpoints.
      rcases le_total (cyclicDist n (l (k - 1)) i) (cyclicDist n (l k) i) with hle | hle
      · -- [l(k-1), i] ⊆ [l(k), i] → N(k-1) ⊆ N(k)
        left; intro v hv
        rw [SimpleGraph.mem_neighborSet] at hv ⊢
        have ⟨hv_mem, hv_ne⟩ := (hadj_iff (k - 1) v).mp hv
        rw [hhi_km1] at hv_mem
        refine (hadj_iff k v).mpr ⟨?_, ?_⟩
        · rw [hhi_k]
          -- l(k-1) ∈ [l(k), i] (since dist(l(k), l(k-1)) + dist(l(k-1), i) = dist(l(k), i))
          -- and [l(k-1), i] ⊆ [l(k), i]
          rw [mem_cyclicInterval_iff_cyclicDist] at hv_mem ⊢
          -- dist(l(k), v) ≤ dist(l(k), i)
          -- We know dist(l(k-1), v) ≤ dist(l(k-1), i) ≤ dist(l(k), i)
          -- But we need dist(l(k), v) ≤ dist(l(k), i), not dist(l(k-1), v)
          -- Use: if l(k-1) ∈ [l(k), i], then [l(k-1), i] ⊆ [l(k), i]
          have hl_km1_in : l (k - 1) ∈ CyclicInterval n (l k) i := by
            rw [mem_cyclicInterval_iff_cyclicDist]
            simp only [cyclicDist] at hle ⊢
            have := (l k).isLt; have := (l (k - 1)).isLt; have := i.isLt
            clear_value k
            clear h_hi_shift h_ne hi1_ne_i hk_def hk1 hk_ne_i1
              hl_not_in hl1_ne_l hk_ne_l hk_in_li_hi hk_ne_i hk_adj_i
              hk_not_adj_i1 hl_in_i1k h_i1k_indep hk1_in_i1k hkm1_ne_i
              hkm1_in hkm1_adj_i hkm1_not_adj_i1 hk_not_adj_i1' hhi_km1
              hhi_k hk_in_km1i hkm1_not_adj_k hk_sub hv hv_mem hv_ne
            split_ifs at hle ⊢ <;> omega
          have hsub := cyclicInterval_subset hl_km1_in
            (le_of_eq (cyclicDist_triangle hl_km1_in).symm)
          exact (mem_cyclicInterval_iff_cyclicDist v (l k) i).mp
            (hsub ((mem_cyclicInterval_iff_cyclicDist v
              (l (k - 1)) i).mpr hv_mem))
        · intro heq; rw [heq] at hv
          exact hkm1_not_adj_k hv
      · -- [l(k), i] ⊆ [l(k-1), i] → N(k) ⊆ N(k-1)
        right; intro v hv
        rw [SimpleGraph.mem_neighborSet] at hv ⊢
        have ⟨hv_mem, hv_ne⟩ := (hadj_iff k v).mp hv
        rw [hhi_k] at hv_mem
        refine (hadj_iff (k - 1) v).mpr ⟨?_, ?_⟩
        · rw [hhi_km1]
          rw [mem_cyclicInterval_iff_cyclicDist] at hv_mem ⊢
          have hl_k_in : l k ∈ CyclicInterval n (l (k - 1)) i := by
            rw [mem_cyclicInterval_iff_cyclicDist]
            simp only [cyclicDist] at hle ⊢
            have := (l k).isLt; have := (l (k - 1)).isLt; have := i.isLt
            clear_value k
            clear h_hi_shift h_ne hi1_ne_i hk_def hk1 hk_ne_i1
              hl_not_in hl1_ne_l hk_ne_l hk_in_li_hi hk_ne_i hk_adj_i
              hk_not_adj_i1 hl_in_i1k h_i1k_indep hk1_in_i1k hkm1_ne_i
              hkm1_in hkm1_adj_i hkm1_not_adj_i1 hk_not_adj_i1' hhi_km1
              hhi_k hk_in_km1i hkm1_not_adj_k hk_sub hv hv_mem hv_ne
            split_ifs at hle ⊢ <;> omega
          have hsub := cyclicInterval_subset hl_k_in
            (le_of_eq (cyclicDist_triangle hl_k_in).symm)
          exact (mem_cyclicInterval_iff_cyclicDist v
            (l (k - 1)) i).mp
            (hsub ((mem_cyclicInterval_iff_cyclicDist v
              (l k) i).mpr hv_mem))
        · intro heq; rw [heq] at hv
          exact hkm1_not_adj_k (G.adj_symm hv)
    -- Contradiction with hnoNested at k-1
    have hns := hnoNested (k - 1)
    rw [show (k - 1) + 1 = k from sub_add_cancel _ _] at hns
    rcases h_nesting_km1 with h1 | h2
    · exact hns.1 h1
    · exact hns.2 h2
  -- Step 5: Derive adjacency translation from endpoint shift
  rw [show G.Adj i v ↔ v ∈ G.neighborSet i from Iff.rfl]
  rw [show G.Adj (i + 1) (v + 1) ↔ (v + 1) ∈ G.neighborSet (i + 1) from Iff.rfl]
  rw [hlh i, hlh (i + 1), h_l_shift, h_hi_shift]
  simp only [Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hmem, hne⟩
    exact ⟨(mem_cyclicInterval_add_one_iff v (l i) (hi i)).mp hmem,
           fun h => hne (by have := congr_arg (· + (- 1 : Fin n)) h;
                            simp only [add_neg_cancel_right] at this; exact this)⟩
  · intro ⟨hmem, hne⟩
    exact ⟨(mem_cyclicInterval_add_one_iff v (l i) (hi i)).mpr hmem,
           fun h => hne (by rw [h])⟩

/-! ### Section 4: BJH02 Lemma 2.4 - Structural Trichotomy -/

/-- The circular clique graph G_n^d (BJH02 definition): vertices 0..n-1, adjacent when
    cyclic distance ≥ d. This is the paper's "far-side" graph, where non-adjacent vertices
    are the close ones. When the convex-round enumeration has N(0) not wrapping through 0,
    this is the correct graph type. -/
def circularCliqueGraph (n : ℕ) [NeZero n] (d : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ d ≤ distMod n (finZModEquiv n u) (finZModEquiv n v)
  symm u v := by
    intro ⟨hne, hd⟩
    refine ⟨hne.symm, ?_⟩
    rwa [distMod_comm]
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- BJH02 Lemma 2.4: For a convex-round graph G, exactly one of the following holds:
    (i) G is bipartite
    (ii) G = G_n^d for some d (the paper's circular clique), or equivalently
         G = fractionGraph n q (when the enumeration wraps through vertices)
    (iii) ∃ i such that N(vᵢ) ⊆ N(vᵢ₊₁) or N(vᵢ₊₁) ⊆ N(vᵢ) (nested neighborhoods)

    The code's IsConvexRoundEnum is broader than the paper's definition: it allows
    cyclic intervals that wrap through the vertex (close-side case, giving fractionGraph)
    in addition to intervals that don't wrap (far-side case, giving circularCliqueGraph). -/
inductive ConvexRoundStructure (n : ℕ) [NeZero n] (G : SimpleGraph (Fin n)) : Prop where
  | bipartite : G.IsBipartite → ConvexRoundStructure n G
  | isFractionGraph (q : ℕ) (hq : 0 < q) (h2q : 2 * q ≤ n + 2)
      (heq : G = (fractionGraph n q).map (zmodFinEquiv n).toEmbedding) :
      ConvexRoundStructure n G
  | isCircularCliqueGraph (d : ℕ) (hd : 0 < d) (hdn : 2 * d ≤ n)
      (heq : G = circularCliqueGraph n d) :
      ConvexRoundStructure n G
  | hasNestedNeighborhood (i : Fin n)
      (hnested : G.neighborSet i ⊆ G.neighborSet (i + 1) ∨
                 G.neighborSet (i + 1) ⊆ G.neighborSet i) :
      ConvexRoundStructure n G

/-- BJH02 Lemma 2.4 (core): Under no-nesting and not-bipartite conditions,
    G is either a fractionGraph (close-side: N(0) wraps around 0) or a
    circularCliqueGraph (far-side: N(0) is away from 0).
    The proof shows that the cyclic interval endpoints l(i), h(i) advance by
    exactly +1 at each step, making G a circulant graph. -/
private lemma convexRound_noNesting_is_circulant (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : IsConvexRoundEnum n G)
    (hnotBip : ¬G.IsBipartite)
    (hnoNested : ∀ i : Fin n, ¬(G.neighborSet i ⊆ G.neighborSet (i + 1)) ∧
                              ¬(G.neighborSet (i + 1) ⊆ G.neighborSet i)) :
    ConvexRoundStructure n G := by
  -- Step 1: Extract interval endpoints l, hi for each vertex (for close/far case analysis)
  have hinterval := hG.neighborhood_isInterval
  choose l hi hlh_and_canon using hinterval
  have hlh : ∀ j, G.neighborSet j = CyclicInterval n (l j) (hi j) \ {j} :=
    fun j => (hlh_and_canon j).1
  have hn_pos : 0 < n := NeZero.pos n
  -- Step 2: Translation invariance: G.Adj u v ↔ G.Adj (u+1) (v+1)
  -- Proved by adj_shift_of_noNesting (canonicalization + endpoint shift inside)
  have htranslation : ∀ u v : Fin n, G.Adj u v ↔ G.Adj (u + 1) (v + 1) :=
    fun u v => adj_shift_of_noNesting hn G hG hnotBip hnoNested u v
  -- Step 3: From translation invariance, adjacency only depends on difference
  have hshift : ∀ (u v : Fin n) (k : Fin n), G.Adj u v ↔ G.Adj (u + k) (v + k) := by
    intro u v ⟨kv, hkv⟩
    induction kv with
    | zero => simp [show (⟨0, hkv⟩ : Fin n) = 0 from rfl]
    | succ m ihm =>
      have hm_lt : m < n := by omega
      have hstep : (⟨m + 1, hkv⟩ : Fin n) = ⟨m, hm_lt⟩ + 1 := by
        apply Fin.ext
        change m + 1 = (⟨m, hm_lt⟩ + 1 : Fin n).val
        rw [Fin.val_add]
        change m + 1 = (m + (1 : Fin n).val) % n
        have : (1 : Fin n).val = 1 % n := rfl
        rw [this, Nat.mod_eq_of_lt (by omega : 1 < n)]
        exact (Nat.mod_eq_of_lt hkv).symm
      rw [show G.Adj u v ↔ G.Adj (u + ⟨m, hm_lt⟩) (v + ⟨m, hm_lt⟩) from ihm hm_lt]
      rw [htranslation, hstep]; simp only [add_assoc]
  have hadj_via_zero : ∀ u v : Fin n, G.Adj u v ↔ G.Adj 0 (v - u) := by
    intro u v
    calc G.Adj u v ↔ G.Adj (u + (-u)) (v + (-u)) := hshift u v (-u)
      _ ↔ G.Adj 0 (v - u) := by rw [add_neg_cancel, sub_eq_add_neg]
  -- Step 4: Symmetry of the connection set
  have hsymm_adj : ∀ v : Fin n, G.Adj 0 v ↔ G.Adj 0 (-v) := by
    intro v
    calc G.Adj 0 v ↔ G.Adj (0 + (-v)) (v + (-v)) := hshift 0 v (-v)
      _ ↔ G.Adj (-v) 0 := by rw [zero_add, add_neg_cancel]
      _ ↔ G.Adj 0 (-v) := ⟨fun hh => G.adj_symm hh, fun hh => G.adj_symm hh⟩
  -- Step 5: distMod translation invariance helpers (needed for both cases)
  have hdistMod_add_right : ∀ (c u v : ZMod n),
      distMod n (u + c) (v + c) = distMod n u v :=
    fun c u v => distMod_add_right n u v c
  have hfze_sub : ∀ a b : Fin n,
      finZModEquiv n a - finZModEquiv n b = finZModEquiv n (a - b) := by
    intro a b
    change (a.val : ZMod n) - (b.val : ZMod n) = ((a - b).val : ZMod n)
    rw [Fin.val_sub]
    have hmod : ((n - b.val + a.val) % n : ZMod n) = ((n - b.val + a.val : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff']; exact Nat.mod_modEq _ _
    rw [hmod, show (n - b.val + a.val : ℕ) = n + a.val - b.val from by omega]
    rw [Nat.cast_sub (by omega : b.val ≤ n + a.val), Nat.cast_add]
    rw [show ((n : ℕ) : ZMod n) = 0 from ZMod.natCast_self n]; ring
  have hfze_zero : finZModEquiv n 0 = (0 : ZMod n) := by
    change ((0 : Fin n).val : ZMod n) = 0; simp
  have hdistMod_translate : ∀ u v : Fin n,
      distMod n (finZModEquiv n u) (finZModEquiv n v) =
      distMod n (finZModEquiv n 0) (finZModEquiv n (v - u)) := by
    intro u v
    calc distMod n (finZModEquiv n u) (finZModEquiv n v)
        = distMod n (finZModEquiv n u + (-finZModEquiv n u))
                    (finZModEquiv n v + (-finZModEquiv n u)) :=
          (hdistMod_add_right (-finZModEquiv n u) _ _).symm
      _ = distMod n 0 (finZModEquiv n v + (-finZModEquiv n u)) := by
          rw [add_neg_cancel]
      _ = distMod n 0 (finZModEquiv n v - finZModEquiv n u) := by
          rw [sub_eq_add_neg]
      _ = distMod n 0 (finZModEquiv n (v - u)) := by rw [hfze_sub]
      _ = distMod n (finZModEquiv n 0) (finZModEquiv n (v - u)) := by
          rw [hfze_zero]
  -- Step 6: Case split on close-side vs far-side
  -- Close-side: 1 ∈ N(0) (connection set wraps around 0, giving fractionGraph)
  -- Far-side: 1 ∉ N(0) (connection set away from 0, giving circularCliqueGraph)
  by_cases h01 : G.Adj 0 1
  · -- Close-side case: G is a fractionGraph (distMod < q characterization)
    have hadj0_close : ∃ q : ℕ, 0 < q ∧ 2 * q ≤ n + 2 ∧
        ∀ v : Fin n, G.Adj 0 v ↔
          v ≠ 0 ∧ distMod n (finZModEquiv n 0) (finZModEquiv n v) < q := by
      -- N(0) is a cyclic interval minus {0}
      have hN0 := hlh 0
      -- 1 ∈ N(0)
      have h1_mem : (1 : Fin n) ∈ G.neighborSet 0 := h01
      -- n-1 ∈ N(0) by symmetry: G.Adj 0 (-1)
      have hneg1_mem : (-1 : Fin n) ∈ G.neighborSet 0 := by
        rw [SimpleGraph.mem_neighborSet]; exact (hsymm_adj 1).mp h01
      -- Rewrite adjacency via interval membership
      have hadj0_iff : ∀ v : Fin n, G.Adj 0 v ↔
          v ∈ CyclicInterval n (l 0) (hi 0) ∧ v ≠ 0 := by
        intro v
        rw [show G.Adj 0 v ↔ v ∈ G.neighborSet 0 from Iff.rfl, hN0]
        simp only [Set.mem_diff, Set.mem_singleton_iff]
      -- Symmetry of the interval: v ∈ interval ↔ -v ∈ interval (for v ≠ 0)
      have hinterval_symm : ∀ v : Fin n, v ≠ 0 →
          (v ∈ CyclicInterval n (l 0) (hi 0) ↔ (-v) ∈ CyclicInterval n (l 0) (hi 0)) := by
        intro v hv
        by_cases hnv : -v = 0
        · exfalso; apply hv; exact neg_eq_zero.mp hnv
        · constructor
          · intro hvm
            have : G.Adj 0 v := (hadj0_iff v).mpr ⟨hvm, hv⟩
            have : G.Adj 0 (-v) := (hsymm_adj v).mp this
            exact ((hadj0_iff (-v)).mp this).1
          · intro hnvm
            have : G.Adj 0 (-v) := (hadj0_iff (-v)).mpr ⟨hnvm, hnv⟩
            have : G.Adj 0 (- -v) := (hsymm_adj (-v)).mp this
            rw [neg_neg] at this
            exact ((hadj0_iff v).mp this).1
      -- Key: 1 and -1 = n-1 are both in the interval
      have h1_in_interval : (1 : Fin n) ∈ CyclicInterval n (l 0) (hi 0) := by
        exact ((hadj0_iff 1).mp h01).1
      have hneg1_in_interval : (-1 : Fin n) ∈ CyclicInterval n (l 0) (hi 0) := by
        exact ((hadj0_iff (-1)).mp ((hsymm_adj 1).mp h01)).1
      -- Compute -1 in Fin n
      have h1_val : (1 : Fin n).val = 1 := by
        have : (1 : Fin n).val = 1 % n := rfl
        rw [this, Nat.mod_eq_of_lt (by omega)]
      have hneg1_val : (-1 : Fin n).val = n - 1 := by
        have h1ne : (1 : Fin n) ≠ 0 := by
          intro h; have := congr_arg Fin.val h
          change 1 % n = 0 % n at this
          rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this
          omega
        rw [show (-1 : Fin n) = -(1 : Fin n) from by ring_nf, Fin.val_neg, if_neg h1ne, h1_val]
      -- Case split on whether the interval wraps around
      by_cases hwrap : (l 0).val ≤ (hi 0).val
      · -- Non-wrapping case: interval = {x | l.val ≤ x.val ≤ hi.val}
        -- Both 1 and n-1 must be in [l.val, hi.val]
        rw [mem_cyclicInterval_of_le hwrap] at h1_in_interval hneg1_in_interval
        -- So l.val ≤ 1 and hi.val ≥ n-1
        have hl_le_1 : (l 0).val ≤ 1 := by omega
        have hhi_ge_nm1 : n - 1 ≤ (hi 0).val := by rw [← hneg1_val]; omega
        -- Since hi.val < n, we get hi.val = n-1
        have hhi_eq : (hi 0).val = n - 1 := by omega
        -- The interval [l(0), n-1] covers all non-zero vertices (complete graph at vertex 0).
        -- Choose q = ⌊n/2⌋ + 1 so that distMod < q for all v ≠ 0.
        have hN0_complete : ∀ v : Fin n, v ≠ 0 → G.Adj 0 v := by
          intro v hv
          rw [hadj0_iff v]
          refine ⟨?_, hv⟩
          rw [mem_cyclicInterval_of_le hwrap]
          constructor
          · exact le_trans hl_le_1 (Fin.pos_iff_ne_zero.mpr hv)
          · rw [hhi_eq]; omega
        -- distMod n (fze 0) (fze v) for v with v.val = k is min(k, n-k)
        -- for the "complete" case, we need q > max(min(k, n-k)) = ⌊n/2⌋
        use n / 2 + 1
        refine ⟨by omega, ?_, ?_⟩
        · omega  -- 2 * (n/2 + 1) ≤ n + 2
        · intro v
          constructor
          · intro hadj
            refine ⟨fun heq => G.loopless.irrefl 0 (heq ▸ hadj), ?_⟩
            -- distMod n (fze 0) (fze v) = min(v.val, n - v.val)
            simp only [finZModEquiv, Equiv.coe_fn_mk, Fin.val_zero,
                        Nat.cast_zero, distMod,
                        show (0 : ZMod n) - (v.val : ZMod n) = -(v.val : ZMod n) from by ring]
            have hv_ne : v ≠ 0 := fun heq => G.loopless.irrefl 0 (heq ▸ hadj)
            have hv_pos : 0 < v.val := Fin.pos_iff_ne_zero.mpr hv_ne
            have hv_cast_ne : (v.val : ZMod n) ≠ 0 := by
              intro h; have := ZMod.val_natCast_of_lt v.isLt
              rw [h, ZMod.val_zero] at this; omega
            rw [ZMod.neg_val, if_neg hv_cast_ne, ZMod.val_natCast_of_lt v.isLt,
                Nat.sub_sub_self (Nat.le_of_lt v.isLt)]
            -- min(v.val, n - v.val) < n/2 + 1
            simp [Nat.min_def]; split <;> omega
          · intro ⟨hne, _hdist⟩
            exact hN0_complete v hne
      · -- Wrapping case: l.val > hi.val
        -- interval = {x | l.val ≤ x.val ∨ x.val ≤ hi.val}
        push_neg at hwrap
        -- 1 is in the interval
        rw [mem_cyclicInterval_of_gt hwrap] at h1_in_interval hneg1_in_interval
        -- Case split: complete wrapping (l = hi + 1, all vertices adjacent) vs proper gap
        by_cases hcomplete : (l 0).val = (hi 0).val + 1
        · -- Wrapping interval covers everything: N(0) = Fin n \ {0}
          have hN0_complete' : ∀ v : Fin n, v ≠ 0 → G.Adj 0 v := by
            intro v hv
            rw [hadj0_iff v]
            refine ⟨?_, hv⟩
            rw [mem_cyclicInterval_of_gt hwrap]
            rcases le_or_gt (l 0).val v.val with h | h
            · left; exact h
            · right; rw [hcomplete] at h; omega
          use n / 2 + 1
          refine ⟨by omega, ?_, ?_⟩
          · omega
          · intro v
            constructor
            · intro hadj
              refine ⟨fun heq => G.loopless.irrefl 0 (heq ▸ hadj), ?_⟩
              simp only [finZModEquiv, Equiv.coe_fn_mk, Fin.val_zero,
                          Nat.cast_zero, distMod,
                          show (0 : ZMod n) - (v.val : ZMod n) = -(v.val : ZMod n) from by ring]
              have hv_ne : v ≠ 0 := fun heq => G.loopless.irrefl 0 (heq ▸ hadj)
              have hv_pos : 0 < v.val := Fin.pos_iff_ne_zero.mpr hv_ne
              have hv_cast_ne : (v.val : ZMod n) ≠ 0 := by
                intro h; have := ZMod.val_natCast_of_lt v.isLt
                rw [h, ZMod.val_zero] at this; omega
              rw [ZMod.neg_val, if_neg hv_cast_ne, ZMod.val_natCast_of_lt v.isLt,
                  Nat.sub_sub_self (Nat.le_of_lt v.isLt)]
              simp [Nat.min_def]; split <;> omega
            · intro ⟨hne, _⟩
              exact hN0_complete' v hne
        · -- Proper wrapping: there's a gap in the interval
          -- We have l.val > hi.val + 1
          have hgap : (hi 0).val + 1 < (l 0).val := by omega
          -- In the gap case, 1 must be on the small side (hi.val ≥ 1)
          have hhi_ge_1 : 1 ≤ (hi 0).val := by
            rcases h1_in_interval with h | h
            · rw [h1_val] at h; omega -- l ≤ 1 contradicts hgap : hi+1 < l, since hi ≥ 0 gives l ≥ 2
            · rw [h1_val] at h; exact h
          -- Vertex (hi 0).val + 1 is NOT in the interval
          -- (and ≠ 0 since hi.val ≥ 1 so hi.val + 1 ≥ 2)
          have hhi1_lt_n : (hi 0).val + 1 < n := by omega
          have hhi1_ne_zero : (⟨(hi 0).val + 1, hhi1_lt_n⟩ : Fin n) ≠ 0 := by
            intro h; have := congr_arg Fin.val h
            change (hi 0).val + 1 = 0 % n at this; rw [Nat.zero_mod] at this; omega
          have hhi1_not_in : (⟨(hi 0).val + 1, hhi1_lt_n⟩ : Fin n) ∉
              CyclicInterval n (l 0) (hi 0) := by
            intro hmem
            rcases (mem_cyclicInterval_of_gt hwrap).mp hmem with h | h
            · change (l 0).val ≤ (hi 0).val + 1 at h; omega
            · change (hi 0).val + 1 ≤ (hi 0).val at h; omega
          have hhi1_not_adj : ¬G.Adj 0 ⟨(hi 0).val + 1, hhi1_lt_n⟩ := by
            intro hadj
            exact hhi1_not_in ((hadj0_iff _).mp hadj).1
          -- By symmetry, -(hi 0 + 1) is also not adjacent to 0
          have hneg_hi1_not_adj : ¬G.Adj 0 (-⟨(hi 0).val + 1, hhi1_lt_n⟩) := by
            intro hadj; exact hhi1_not_adj ((hsymm_adj _).mpr hadj)
          -- Compute val of -(hi 0 + 1)
          have hneg_hi1_val : (-⟨(hi 0).val + 1, hhi1_lt_n⟩ : Fin n).val =
              n - ((hi 0).val + 1) := by
            rw [Fin.val_neg, if_neg hhi1_ne_zero]
          -- -(hi 0 + 1) is not in the interval
          have hneg_hi1_not_in : (-⟨(hi 0).val + 1, hhi1_lt_n⟩ : Fin n) ∉
              CyclicInterval n (l 0) (hi 0) := by
            intro hmem
            have : G.Adj 0 (-⟨(hi 0).val + 1, hhi1_lt_n⟩) := by
              rw [hadj0_iff]
              refine ⟨hmem, ?_⟩
              intro heq
              have : (-⟨(hi 0).val + 1, hhi1_lt_n⟩ : Fin n).val = 0 := by
                rw [heq]; rfl
              rw [hneg_hi1_val] at this; omega
            exact hneg_hi1_not_adj this
          -- From hneg_hi1_not_in: n - (hi.val + 1) is not in interval
          -- So: n - (hi.val + 1) > hi.val AND n - (hi.val + 1) < l.val
          have hneg_hi1_bound : n - ((hi 0).val + 1) < (l 0).val := by
            by_contra hge; push_neg at hge
            exact hneg_hi1_not_in (by
              rw [mem_cyclicInterval_of_gt hwrap]; left; rw [hneg_hi1_val]; exact hge)
          -- Similarly, vertex (hi 0) IS in interval, so -(hi 0) is also in interval
          -- (hi 0) is in the small side of the interval
          have hhi_in_interval : (hi 0) ∈ CyclicInterval n (l 0) (hi 0) :=
            right_mem_cyclicInterval _ _
          -- If hi 0 ≠ 0, then -(hi 0) is in interval by symmetry
          have hhi_ne_zero : (hi 0) ≠ (0 : Fin n) := by
            intro h; have hv := congr_arg Fin.val h
            change (hi 0).val = 0 % n at hv; rw [Nat.zero_mod] at hv; omega
          have hneg_hi_in : (-(hi 0) : Fin n) ∈ CyclicInterval n (l 0) (hi 0) := by
            exact (hinterval_symm (hi 0) hhi_ne_zero).mp hhi_in_interval
          -- val of -(hi 0)
          have hneg_hi_val : (-(hi 0) : Fin n).val = n - (hi 0).val := by
            rw [Fin.val_neg, if_neg hhi_ne_zero]
          -- -(hi 0) is in the big side (since n - hi.val > hi.val in the wrapping case)
          -- So l.val ≤ n - hi.val
          have hl_le : (l 0).val ≤ n - (hi 0).val := by
            rw [mem_cyclicInterval_of_gt hwrap] at hneg_hi_in
            rcases hneg_hi_in with h | h
            · rw [hneg_hi_val] at h; exact h
            · -- -(hi 0) on small side: n - hi.val ≤ hi.val. Then -(hi+1) also small: contradiction.
              exfalso; rw [hneg_hi_val] at h
              exact hneg_hi1_not_in (by
                rw [mem_cyclicInterval_of_gt hwrap]; right
                rw [hneg_hi1_val]; omega)
          -- Combining: n - hi.val - 1 < l.val ≤ n - hi.val
          -- So l.val = n - hi.val
          have hl_eq : (l 0).val = n - (hi 0).val := by omega
          -- Now we know the interval structure:
          -- CyclicInterval n (l 0) (hi 0) = {x | x.val ≥ n - r ∨ x.val ≤ r}
          -- where r = (hi 0).val
          -- This is exactly the set of vertices with distMod ≤ r from 0.
          -- Set q = r + 1 = (hi 0).val + 1
          set r := (hi 0).val with hr_def
          use r + 1
          refine ⟨by omega, ?_, ?_⟩
          · -- 2 * (r + 1) ≤ n + 2
            -- From wrapping: l.val > hi.val, i.e., n - r > r, i.e., n > 2r
            -- So 2r + 2 ≤ n + 1 ≤ n + 2
            omega
          · intro v
            constructor
            · -- G.Adj 0 v → v ≠ 0 ∧ distMod < r + 1
              intro hadj
              have hv_ne : v ≠ 0 := fun heq => G.loopless.irrefl 0 (heq ▸ hadj)
              refine ⟨hv_ne, ?_⟩
              have hv_in : v ∈ CyclicInterval n (l 0) (hi 0) := ((hadj0_iff v).mp hadj).1
              rw [mem_cyclicInterval_of_gt hwrap] at hv_in
              -- v.val ≥ n - r or v.val ≤ r
              simp only [finZModEquiv, Equiv.coe_fn_mk, Fin.val_zero,
                          Nat.cast_zero, distMod,
                          show (0 : ZMod n) - (v.val : ZMod n) = -(v.val : ZMod n) from by ring]
              have hv_pos : 0 < v.val := Fin.pos_iff_ne_zero.mpr hv_ne
              have hv_cast_ne : (v.val : ZMod n) ≠ 0 := by
                intro h; have := ZMod.val_natCast_of_lt v.isLt
                rw [h, ZMod.val_zero] at this; omega
              rw [ZMod.neg_val, if_neg hv_cast_ne, ZMod.val_natCast_of_lt v.isLt,
                  Nat.sub_sub_self (Nat.le_of_lt v.isLt)]
              -- Need: min(v.val, n - v.val) < r + 1, i.e., min(v.val, n - v.val) ≤ r
              rcases hv_in with hbig | hsmall
              · rw [hl_eq] at hbig; simp [Nat.min_def]; split <;> omega
              · simp [Nat.min_def]; split <;> omega
            · -- v ≠ 0 ∧ distMod < r + 1 → G.Adj 0 v
              intro ⟨hv_ne, hdist⟩
              rw [hadj0_iff v]
              refine ⟨?_, hv_ne⟩
              rw [mem_cyclicInterval_of_gt hwrap]
              -- From distMod < r + 1: min(v.val, n - v.val) ≤ r
              simp only [finZModEquiv, Equiv.coe_fn_mk, Fin.val_zero,
                          Nat.cast_zero, distMod,
                          show (0 : ZMod n) - (v.val : ZMod n) = -(v.val : ZMod n) from by ring]
                at hdist
              have hv_pos : 0 < v.val := Fin.pos_iff_ne_zero.mpr hv_ne
              have hv_cast_ne : (v.val : ZMod n) ≠ 0 := by
                intro h; have := ZMod.val_natCast_of_lt v.isLt
                rw [h, ZMod.val_zero] at this; omega
              rw [ZMod.neg_val, if_neg hv_cast_ne, ZMod.val_natCast_of_lt v.isLt,
                  Nat.sub_sub_self (Nat.le_of_lt v.isLt)] at hdist
              -- min(v.val, n - v.val) < r + 1
              -- So v.val ≤ r or n - v.val ≤ r
              rcases min_le_iff.mp (Nat.lt_succ_iff.mp hdist) with h | h
              · left; rw [hl_eq]; omega  -- h : n - v.val ≤ r, so v.val ≥ n - r
              · right; rw [← hr_def]; exact h  -- h : v.val ≤ r
    obtain ⟨q, hq_pos, h2q, hadj0_distMod⟩ := hadj0_close
    -- Prove graph equality with fractionGraph
    have heq : G = (fractionGraph n q).map (zmodFinEquiv n).toEmbedding := by
      ext u v
      simp only [mapped_fractionGraph_adj]
      constructor
      · intro hadj
        refine ⟨fun heq => G.loopless.irrefl u (heq ▸ hadj), ?_⟩
        rw [hadj_via_zero u v] at hadj
        rw [hdistMod_translate u v]
        have hvu_ne : v - u ≠ 0 := by
          intro heq; have : v - u = 0 := heq; rw [this] at hadj; exact G.loopless.irrefl 0 hadj
        exact ((hadj0_distMod (v - u)).mp hadj).2
      · intro ⟨hne, hdist⟩
        rw [hadj_via_zero u v]
        have hvu_ne : v - u ≠ 0 := by
          intro heq; exact hne (eq_of_sub_eq_zero heq).symm
        rw [hdistMod_translate u v] at hdist
        exact (hadj0_distMod (v - u)).mpr ⟨hvu_ne, hdist⟩
    exact ConvexRoundStructure.isFractionGraph q hq_pos h2q heq
  · -- Far-side case: G is a circularCliqueGraph (distMod ≥ d characterization)
    have hadj0_far : ∃ d : ℕ, 0 < d ∧ 2 * d ≤ n ∧
        ∀ v : Fin n, G.Adj 0 v ↔
          v ≠ 0 ∧ d ≤ distMod n (finZModEquiv n 0) (finZModEquiv n v) := by
      -- N(0) is a cyclic interval minus {0}
      have hN0 := hlh 0
      -- Rewrite adjacency via interval membership
      have hadj0_iff : ∀ v : Fin n, G.Adj 0 v ↔
          v ∈ CyclicInterval n (l 0) (hi 0) ∧ v ≠ 0 := by
        intro v
        rw [show G.Adj 0 v ↔ v ∈ G.neighborSet 0 from Iff.rfl, hN0]
        simp only [Set.mem_diff, Set.mem_singleton_iff]
      -- Symmetry of the interval: v ∈ interval ↔ -v ∈ interval (for v ≠ 0)
      have hinterval_symm : ∀ v : Fin n, v ≠ 0 →
          (v ∈ CyclicInterval n (l 0) (hi 0) ↔ (-v) ∈ CyclicInterval n (l 0) (hi 0)) := by
        intro v hv
        by_cases hnv : -v = 0
        · exfalso; apply hv; exact neg_eq_zero.mp hnv
        · constructor
          · intro hvm
            have : G.Adj 0 v := (hadj0_iff v).mpr ⟨hvm, hv⟩
            have : G.Adj 0 (-v) := (hsymm_adj v).mp this
            exact ((hadj0_iff (-v)).mp this).1
          · intro hnvm
            have : G.Adj 0 (-v) := (hadj0_iff (-v)).mpr ⟨hnvm, hnv⟩
            have : G.Adj 0 (- -v) := (hsymm_adj (-v)).mp this
            rw [neg_neg] at this
            exact ((hadj0_iff v).mp this).1
      -- 1 and -1 are NOT in the interval
      have h1ne : (1 : Fin n) ≠ 0 := by
        intro h; have := congr_arg Fin.val h
        change 1 % n = 0 % n at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this; omega
      have h1_not_in : (1 : Fin n) ∉ CyclicInterval n (l 0) (hi 0) := by
        intro hmem; exact h01 ((hadj0_iff 1).mpr ⟨hmem, h1ne⟩)
      have hneg1ne : (-1 : Fin n) ≠ 0 := by
        intro h; apply h1ne; exact neg_eq_zero.mp h
      have hneg1_not_in : (-1 : Fin n) ∉ CyclicInterval n (l 0) (hi 0) := by
        intro hmem
        exact h01 ((hsymm_adj 1).mpr ((hadj0_iff (-1)).mpr ⟨hmem, hneg1ne⟩))
      -- Compute values
      have h1_val : (1 : Fin n).val = 1 := by
        change 1 % n = 1; exact Nat.mod_eq_of_lt (by omega)
      have hneg1_val : (-1 : Fin n).val = n - 1 := by
        rw [show (-1 : Fin n) = -(1 : Fin n) from by ring_nf, Fin.val_neg, if_neg h1ne, h1_val]
      -- Case split on wrapping
      by_cases hwrap : (l 0).val ≤ (hi 0).val
      · -- Non-wrapping case: interval = {x | l.val ≤ x.val ≤ hi.val}
        rw [mem_cyclicInterval_of_le hwrap] at h1_not_in hneg1_not_in
        -- h1_not_in : ¬(l ≤ 1 ∧ 1 ≤ hi)
        -- Establish l ≥ 2 (1 ∉ [l, hi])
        have hl_ge_2 : 2 ≤ (l 0).val := by
          by_contra hlt; push_neg at hlt
          -- l ≤ 1. Then either l = 0 or l = 1.
          -- If l ≤ 1 then from h1_not_in: ¬(1 ≤ hi), so hi < 1, hi = 0
          have hl_le_1 : (l 0).val ≤ 1 := by omega
          have hhi_lt_1 : (hi 0).val < 1 := by
            by_contra hge; push_neg at hge
            exact h1_not_in ⟨by rw [h1_val]; exact hl_le_1, by rw [h1_val]; exact hge⟩
          have hhi_eq_0 : (hi 0).val = 0 := by omega
          have hl_eq_0 : (l 0).val = 0 := by omega
          -- interval = {x | 0 ≤ x.val ∧ x.val ≤ 0} = {0}, N(0) = ∅
          have hno_edges : ∀ u v : Fin n, ¬G.Adj u v := by
            intro u v hadj
            rw [hadj_via_zero u v] at hadj
            have hvu_ne : v - u ≠ 0 := by
              intro heq; rw [heq] at hadj; exact G.loopless.irrefl 0 hadj
            have := (hadj0_iff (v - u)).mp hadj
            rcases this with ⟨hmem, _⟩
            rw [mem_cyclicInterval_of_le hwrap] at hmem
            have hvusub : (v - u).val = 0 := by omega
            exact hvu_ne (Fin.ext (by rw [hvusub]; simp))
          exact hnotBip ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 2)) (by
            intro u v hadj; exact absurd hadj (hno_edges u v))⟩
        -- Establish hi ≤ n - 2 (n-1 ∉ [l, hi])
        have hhi_le : (hi 0).val ≤ n - 2 := by
          by_contra hge; push_neg at hge
          -- hi ≥ n - 1. Since hi < n, hi = n - 1.
          have hhi_eq : (hi 0).val = n - 1 := by omega
          -- Then n-1 ∈ [l, hi] since l ≤ n-1 and hi = n-1
          exact hneg1_not_in ⟨by rw [hneg1_val]; omega, by rw [hneg1_val]; omega⟩
        -- By interval symmetry, hi = n - l
        have hhi_ne_zero : (hi 0) ≠ (0 : Fin n) := by
          intro h; have hv := congr_arg Fin.val h
          change (hi 0).val = 0 % n at hv; rw [Nat.zero_mod] at hv; omega
        have hneg_hi_val : (-(hi 0) : Fin n).val = n - (hi 0).val := by
          rw [Fin.val_neg, if_neg hhi_ne_zero]
        have hhi_in : (hi 0) ∈ CyclicInterval n (l 0) (hi 0) :=
          right_mem_cyclicInterval _ _
        have hneg_hi_in : (-(hi 0) : Fin n) ∈ CyclicInterval n (l 0) (hi 0) :=
          (hinterval_symm (hi 0) hhi_ne_zero).mp hhi_in
        rw [mem_cyclicInterval_of_le hwrap] at hneg_hi_in
        have hl_le_nhi : (l 0).val ≤ n - (hi 0).val := by
          rw [← hneg_hi_val]; exact hneg_hi_in.1
        have hnhi_le_hi : n - (hi 0).val ≤ (hi 0).val := by
          rw [← hneg_hi_val]; exact hneg_hi_in.2
        have hl_ne_zero : (l 0) ≠ (0 : Fin n) := by
          intro h; have hv := congr_arg Fin.val h
          change (l 0).val = 0 % n at hv; rw [Nat.zero_mod] at hv; omega
        have hneg_l_val : (-(l 0) : Fin n).val = n - (l 0).val := by
          rw [Fin.val_neg, if_neg hl_ne_zero]
        have hl_in : (l 0) ∈ CyclicInterval n (l 0) (hi 0) :=
          left_mem_cyclicInterval _ _
        have hneg_l_in : (-(l 0) : Fin n) ∈ CyclicInterval n (l 0) (hi 0) :=
          (hinterval_symm (l 0) hl_ne_zero).mp hl_in
        rw [mem_cyclicInterval_of_le hwrap] at hneg_l_in
        have hnl_le_hi : n - (l 0).val ≤ (hi 0).val := by
          rw [← hneg_l_val]; exact hneg_l_in.2
        have hhi_eq : (hi 0).val = n - (l 0).val := by omega
        use (l 0).val
        refine ⟨by omega, ?_, ?_⟩
        · omega
        · intro v
          constructor
          · intro hadj
            have hv_ne : v ≠ 0 := fun heq => G.loopless.irrefl 0 (heq ▸ hadj)
            refine ⟨hv_ne, ?_⟩
            have hv_in : v ∈ CyclicInterval n (l 0) (hi 0) := ((hadj0_iff v).mp hadj).1
            rw [mem_cyclicInterval_of_le hwrap] at hv_in
            simp only [finZModEquiv, Equiv.coe_fn_mk, Fin.val_zero,
                        Nat.cast_zero, distMod,
                        show (0 : ZMod n) - (v.val : ZMod n) = -(v.val : ZMod n) from by ring]
            have hv_pos : 0 < v.val := Fin.pos_iff_ne_zero.mpr hv_ne
            have hv_cast_ne : (v.val : ZMod n) ≠ 0 := by
              intro h; have := ZMod.val_natCast_of_lt v.isLt
              rw [h, ZMod.val_zero] at this; omega
            rw [ZMod.neg_val, if_neg hv_cast_ne, ZMod.val_natCast_of_lt v.isLt,
                Nat.sub_sub_self (Nat.le_of_lt v.isLt)]
            simp [Nat.min_def]; split <;> omega
          · intro ⟨hv_ne, hdist⟩
            rw [hadj0_iff v]
            refine ⟨?_, hv_ne⟩
            rw [mem_cyclicInterval_of_le hwrap]
            simp only [finZModEquiv, Equiv.coe_fn_mk, Fin.val_zero,
                        Nat.cast_zero, distMod,
                        show (0 : ZMod n) - (v.val : ZMod n) = -(v.val : ZMod n) from by ring]
              at hdist
            have hv_pos : 0 < v.val := Fin.pos_iff_ne_zero.mpr hv_ne
            have hv_cast_ne : (v.val : ZMod n) ≠ 0 := by
              intro h; have := ZMod.val_natCast_of_lt v.isLt
              rw [h, ZMod.val_zero] at this; omega
            rw [ZMod.neg_val, if_neg hv_cast_ne, ZMod.val_natCast_of_lt v.isLt,
                Nat.sub_sub_self (Nat.le_of_lt v.isLt)] at hdist
            constructor
            · simp [Nat.min_def] at hdist; split at hdist <;> omega
            · rw [hhi_eq]; simp [Nat.min_def] at hdist; split at hdist <;> omega
      · -- Wrapping case: l.val > hi.val is impossible
        push_neg at hwrap
        exfalso; apply hneg1_not_in
        rw [mem_cyclicInterval_of_gt hwrap]
        left; rw [hneg1_val]; omega
    obtain ⟨d, hd_pos, h2d, hadj0_distMod⟩ := hadj0_far
    -- Prove graph equality with circularCliqueGraph
    have heq : G = circularCliqueGraph n d := by
      ext u v
      simp only [circularCliqueGraph]
      constructor
      · intro hadj
        refine ⟨fun heq => G.loopless.irrefl u (heq ▸ hadj), ?_⟩
        rw [hadj_via_zero u v] at hadj
        rw [hdistMod_translate u v]
        have hvu_ne : v - u ≠ 0 := by
          intro heq; have : v - u = 0 := heq; rw [this] at hadj; exact G.loopless.irrefl 0 hadj
        exact ((hadj0_distMod (v - u)).mp hadj).2
      · intro ⟨hne, hdist⟩
        rw [hadj_via_zero u v]
        have hvu_ne : v - u ≠ 0 := by
          intro heq; exact hne (eq_of_sub_eq_zero heq).symm
        rw [hdistMod_translate u v] at hdist
        exact (hadj0_distMod (v - u)).mpr ⟨hvu_ne, hdist⟩
    exact ConvexRoundStructure.isCircularCliqueGraph d hd_pos h2d heq

/-- BJH02 Lemma 2.4: Every convex-round graph has one of the structural types.
    This is the main structural trichotomy (plus the far-side circular clique case). -/
theorem convexRound_trichotomy (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : IsConvexRoundEnum n G) :
    ConvexRoundStructure n G := by
  by_cases hbip : G.IsBipartite
  · exact ConvexRoundStructure.bipartite hbip
  by_cases hnoNested : ∀ i : Fin n, ¬(G.neighborSet i ⊆ G.neighborSet (i + 1)) ∧
                                      ¬(G.neighborSet (i + 1) ⊆ G.neighborSet i)
  · exact convexRound_noNesting_is_circulant n hn G hG hbip hnoNested
  · push_neg at hnoNested
    obtain ⟨i, hi⟩ := hnoNested
    by_cases hcase : G.neighborSet i ⊆ G.neighborSet (i + 1)
    · exact ConvexRoundStructure.hasNestedNeighborhood i (Or.inl hcase)
    · exact ConvexRoundStructure.hasNestedNeighborhood i (Or.inr (hi hcase))

/-! ### Section 5: Cyclic Order Preservation -/

/-- Key definition: Two points a, b are "cyclically between" c, d if
    going from c in the positive direction, we encounter a before b before d -/
def IsCyclicBetween (n : ℕ) [NeZero n] (a b c d : Fin n) : Prop :=
  cyclicDist n c a < cyclicDist n c b ∧ cyclicDist n c b < cyclicDist n c d

/-- cyclicDist from a to itself is 0 -/
lemma cyclicDist_self (n : ℕ) [NeZero n] (a : Fin n) : cyclicDist n a a = 0 := by
  simp only [cyclicDist, le_refl, ite_true, Nat.sub_self]

/-- cyclicDist is 0 iff the two elements are equal -/
lemma cyclicDist_eq_zero_iff (n : ℕ) [NeZero n] (a b : Fin n) :
    cyclicDist n a b = 0 ↔ a = b := by
  constructor
  · intro h
    simp only [cyclicDist] at h
    split_ifs at h with hab
    · have : b.val = a.val := by omega
      exact Fin.ext this.symm
    · have hn_pos : 0 < n := NeZero.pos n
      have ha_lt : a.val < n := a.isLt
      have hb_lt : b.val < n := b.isLt
      omega
  · intro h
    rw [h, cyclicDist_self]

/-- cyclicDist between consecutive elements is 1 -/
lemma cyclicDist_succ (n : ℕ) [NeZero n] (hn : 2 ≤ n) (a : Fin n) :
    cyclicDist n a (a + 1) = 1 := by
  simp only [cyclicDist]
  by_cases ha : a.val + 1 < n
  · have h1 : (a + 1).val = a.val + 1 := Fin.val_add_one_of_lt' ha
    have h2 : a.val ≤ (a + 1).val := by rw [h1]; omega
    rw [if_pos h2, h1]
    omega
  · -- a.val + 1 = n, so a = n - 1 and a + 1 = 0
    have ha_eq : a.val = n - 1 := by
      have ha_lt : a.val < n := a.isLt
      omega
    have hn_pos : 0 < n := NeZero.pos n
    have h1 : (a + 1).val = 0 := by
      simp only [Fin.val_add, ha_eq]
      have hone : (1 : Fin n).val = 1 % n := rfl
      rw [hone]
      have : n - 1 + 1 % n = n := by
        have h1mod : 1 % n = 1 := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hn)
        omega
      rw [this, Nat.mod_self]
    have h2 : ¬(a.val ≤ (a + 1).val) := by
      rw [h1, ha_eq]
      omega
    rw [if_neg h2, h1, ha_eq]
    omega

/-- No element is strictly between consecutive elements in Fin n.
    cyclicDist from any element a to a itself is 0, and to a+1 is 1.
    So for u ≠ a, we have cyclicDist n a u ≥ 1. -/
lemma no_element_between_consecutive (n : ℕ) [NeZero n] (hn : 2 ≤ n) (a : Fin n) :
    ∀ u : Fin n, u ≠ a → cyclicDist n a (a + 1) ≤ cyclicDist n a u := by
  intro u hu_ne
  rw [cyclicDist_succ n hn a]
  have h := cyclicDist_eq_zero_iff n a u
  by_contra hlt
  push_neg at hlt
  have : cyclicDist n a u = 0 := by omega
  exact hu_ne (h.mp this).symm

/-! ### Section 6: FractionGraph' Automorphisms

    fractionGraph is a circulant graph, meaning its adjacency is determined by distance.
    This strongly constrains its automorphisms to be rotations and reflections. -/

/-- Rotation is an automorphism of fractionGraph -/
def fractionGraph_rotation (p q : ℕ) [NeZero p] (c : ZMod p) :
    (fractionGraph p q) ≃g (fractionGraph p q) where
  toEquiv := {
    toFun := fun x => x + c
    invFun := fun x => x - c
    left_inv := fun x => by ring
    right_inv := fun x => by ring
  }
  map_rel_iff' := by
    intro u v
    simp only [fractionGraph, Equiv.coe_fn_mk, ne_eq, distMod_add_right]
    constructor
    · intro ⟨hne, hdist⟩
      exact ⟨fun h => hne (by rw [h]), hdist⟩
    · intro ⟨hne, hdist⟩
      exact ⟨fun h => hne (add_right_cancel h), hdist⟩

/-- Reflection is an automorphism of fractionGraph -/
def fractionGraph_reflection (p q : ℕ) [NeZero p] (c : ZMod p) :
    (fractionGraph p q) ≃g (fractionGraph p q) where
  toEquiv := {
    toFun := fun x => c - x
    invFun := fun x => c - x
    left_inv := fun x => by ring
    right_inv := fun x => by ring
  }
  map_rel_iff' := by
    intro u v
    simp only [fractionGraph, Equiv.coe_fn_mk, ne_eq]
    have h : (c - u) - (c - v) = v - u := by ring
    have hsub_inj : ∀ a b : ZMod p, c - a = c - b → a = b := fun a b heq => by
      have : c - a - (c - b) = 0 := by rw [heq]; ring
      have h' : c - a - (c - b) = b - a := by ring
      rw [h'] at this
      have : b = a := sub_eq_zero.mp this
      exact this.symm
    constructor
    · intro ⟨hne, hdist⟩
      constructor
      · intro heq
        exact hne (congrArg (c - ·) heq)
      · simp only [distMod, h] at hdist
        rw [distMod_comm]
        exact hdist
    · intro ⟨hne, hdist⟩
      constructor
      · intro heq
        exact hne (hsub_inj u v heq)
      · simp only [distMod, h]
        rw [distMod_comm] at hdist
        exact hdist

/-- val of -1 in ZMod p is p - 1 -/
lemma zmod_val_neg_one (p : ℕ) [_hp : NeZero p] : (-1 : ZMod p).val = p - 1 := by
  have hp_pos : 0 < p := NeZero.pos p
  have hpred : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp_pos).symm
  conv_lhs => rw [hpred]
  rw [ZMod.val_neg_one (p - 1)]

/-- val of 1 in ZMod p is 1 when p ≥ 2 -/
lemma zmod_val_one (p : ℕ) [_hp : NeZero p] (hp2 : 2 ≤ p) : (1 : ZMod p).val = 1 := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  exact ZMod.val_one p

/-- distMod from v to v+1 is 1 -/
lemma distMod_add_one (p : ℕ) [NeZero p] (hp : 2 ≤ p) (v : ZMod p) :
    distMod p v (v + 1) = 1 := by
  simp only [distMod]
  -- (v - (v + 1)).val = (-1).val = p - 1 in ZMod p
  have h1 : v - (v + 1) = -1 := by ring
  rw [h1]
  have hn1_val : (-1 : ZMod p).val = p - 1 := zmod_val_neg_one p
  rw [hn1_val]
  have hp_pos : 0 < p := NeZero.pos p
  have hp1 : p - (p - 1) = 1 := by omega
  rw [hp1]
  exact min_eq_right (by omega : 1 ≤ p - 1)

/-- distMod from v to v-1 is 1 -/
lemma distMod_sub_one (p : ℕ) [NeZero p] (hp : 2 ≤ p) (v : ZMod p) :
    distMod p v (v - 1) = 1 := by
  simp only [distMod]
  -- (v - (v - 1)).val = (1).val = 1 in ZMod p
  have h1 : v - (v - 1) = 1 := by ring
  rw [h1]
  have h1_val : (1 : ZMod p).val = 1 := zmod_val_one p hp
  rw [h1_val]
  have hp_pos : 0 < p := NeZero.pos p
  exact min_eq_left (by omega : 1 ≤ p - 1)

/-- If distMod p v x = 1, then x = v-1 or x = v+1 -/
lemma distMod_eq_one_imp_adjacent (p : ℕ) [NeZero p] (hp : 3 ≤ p) (v x : ZMod p)
    (hdist : distMod p v x = 1) : x = v - 1 ∨ x = v + 1 := by
  simp only [distMod] at hdist
  let d := (v - x).val
  have hd_lt : d < p := ZMod.val_lt (v - x)
  -- min d (p - d) = 1 means d = 1 or p - d = 1 (i.e., d = p - 1)
  have hmin : min d (p - d) = 1 := hdist
  by_cases h : d ≤ p - d
  · -- d ≤ p - d, so min = d = 1, i.e., v - x = 1, so x = v - 1
    have hd1 : d = 1 := by simp only [min_eq_left h] at hmin; exact hmin
    have hvx : v - x = 1 := by
      have hval : (v - x).val = 1 := hd1
      have h1val : (1 : ZMod p).val = 1 := zmod_val_one p (by omega)
      have : (v - x).val = (1 : ZMod p).val := by rw [hval, h1val]
      exact ZMod.val_injective p this
    left
    calc x = v - (v - x) := by ring
      _ = v - 1 := by rw [hvx]
  · -- d > p - d, so min = p - d = 1, i.e., d = p - 1, v - x = -1, so x = v + 1
    push_neg at h
    have hd_pm1 : p - d = 1 := by simp only [min_eq_right (le_of_lt h)] at hmin; exact hmin
    have hd_eq : d = p - 1 := by omega
    have hvx : v - x = -1 := by
      have hval : (v - x).val = p - 1 := hd_eq
      have hn1val : (-1 : ZMod p).val = p - 1 := zmod_val_neg_one p
      have : (v - x).val = (-1 : ZMod p).val := by rw [hval, hn1val]
      exact ZMod.val_injective p this
    right
    calc x = v - (v - x) := by ring
      _ = v - (-1) := by rw [hvx]
      _ = v + 1 := by ring

/-- 1 ≠ 0 in ZMod p when p ≥ 2 -/
lemma zmod_one_ne_zero (p : ℕ) [NeZero p] (hp : 2 ≤ p) : (1 : ZMod p) ≠ 0 := by
  intro h
  have h1 : (1 : ZMod p).val = 1 := zmod_val_one p hp
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  rw [h] at h1
  rw [h0] at h1
  exact Nat.one_ne_zero h1.symm

/-- The elements at distance 1 from any vertex in fractionGraph are exactly {v-1, v+1} -/
lemma fractionGraph_dist_one_neighbors (p q : ℕ) [NeZero p] (hp : 3 ≤ p) (hq : 2 ≤ q)
    (_h2q : 2 * q ≤ p) (v : ZMod p) :
    {x | (fractionGraph p q).Adj v x ∧ distMod p v x = 1} = {v - 1, v + 1} := by
  ext x
  constructor
  · -- If x is adjacent with distance 1, then x = v±1
    intro ⟨_, hdist⟩
    have h := distMod_eq_one_imp_adjacent p hp v x hdist
    rcases h with hx | hx
    · left; exact hx
    · right; exact hx
  · -- If x = v±1, then x is adjacent with distance 1
    intro hx
    rcases hx with hx | hx
    · -- x = v - 1
      rw [hx]
      constructor
      · constructor
        · intro heq
          -- From heq : v = v - 1, we get 1 = 0
          have : (1 : ZMod p) = 0 := by
            have h := congrArg (· + 1) heq
            simp only [sub_add_cancel] at h
            -- h : v + 1 = v, so (v + 1) - v = v - v gives 1 = 0
            have h2 : (v + 1) - v = v - v := by rw [h]
            simp only [add_sub_cancel_left, sub_self] at h2
            exact h2
          exact zmod_one_ne_zero p (by omega) this
        · rw [distMod_sub_one p (by omega : 2 ≤ p) v]
          exact hq
      · exact distMod_sub_one p (by omega : 2 ≤ p) v
    · -- x = v + 1
      rw [hx]
      constructor
      · constructor
        · intro heq
          -- From heq : v = v + 1, we get 0 = 1
          have : (1 : ZMod p) = 0 := by
            have h := congrArg (· - v) heq
            simp only [sub_self, add_sub_cancel_left] at h
            exact h.symm
          exact zmod_one_ne_zero p (by omega) this
        · rw [distMod_add_one p (by omega : 2 ≤ p) v]
          exact hq
      · exact distMod_add_one p (by omega : 2 ≤ p) v

/-- Helper: 0 and 1 are adjacent in fractionGraph when q ≥ 2 -/
lemma fractionGraph_adj_zero_one (p q : ℕ) [NeZero p] (hp : 3 ≤ p) (hq : 2 ≤ q) :
    (fractionGraph p q).Adj 0 1 := by
  simp only [fractionGraph]
  constructor
  · intro h
    have h1ne0 := zmod_one_ne_zero p (by omega : 2 ≤ p)
    exact h1ne0 h.symm
  · have h := distMod_add_one p (by omega : 2 ≤ p) 0
    simp only [zero_add] at h
    rw [h]
    exact hq

/-- Helper: 0 and -1 are adjacent in fractionGraph when q ≥ 2 -/
lemma fractionGraph_adj_zero_neg_one (p q : ℕ) [NeZero p] (hp : 3 ≤ p) (hq : 2 ≤ q) :
    (fractionGraph p q).Adj 0 (-1) := by
  simp only [fractionGraph]
  constructor
  · intro h
    have : (1 : ZMod p) = 0 := neg_eq_zero.mp h.symm
    exact zmod_one_ne_zero p (by omega) this
  · have h := distMod_sub_one p (by omega : 2 ≤ p) 0
    simp only [zero_sub] at h
    -- h : distMod p 0 (-1) = 1, goal : distMod p 0 (-1) < q
    rw [h]
    exact hq

/-- Automorphisms preserve adjacency -/
lemma fractionGraph_iso_preserves_adj (p q : ℕ) [NeZero p]
    (φ : (fractionGraph p q) ≃g (fractionGraph p q)) (u v : ZMod p)
    (hadj : (fractionGraph p q).Adj u v) :
    (fractionGraph p q).Adj (φ u) (φ v) := φ.map_rel_iff'.symm.mp hadj

/-- The common neighborhood size characterizes distance.
    For adjacent vertices u, v in fractionGraph p q (with 2q ≤ p):
    - If distMod(u,v) = 1: |N(u) ∩ N(v)| = 2q - 4
    - If distMod(u,v) = d ≥ 2: |N(u) ∩ N(v)| = 2q - 4 - (d - 1) = 2q - 3 - d

    This means distance-1 neighbors are uniquely characterized as those with
    the maximum common neighborhood size (2q - 4).

    Since automorphisms preserve common neighborhoods, they preserve the
    distance-1 property. -/
lemma fractionGraph_common_neighbors_characterize_dist (p q : ℕ) [NeZero p]
    (hp : 3 ≤ p) (hq : 3 ≤ q) (h2q : 2 * q < p)
    (u v : ZMod p) (hadj : (fractionGraph p q).Adj u v) :
    distMod p u v = 1 ↔
    ∀ w, (fractionGraph p q).Adj u w → w ≠ v →
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet v).ncard >
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet w).ncard ∨
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet v).ncard =
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet w).ncard := by
  -- The RHS `a > b ∨ a = b` is equivalent to `b ≤ a`.
  -- We reformulate using this equivalence.
  have rhs_equiv : (∀ w, (fractionGraph p q).Adj u w → w ≠ v →
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet v).ncard >
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet w).ncard ∨
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet v).ncard =
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet w).ncard) ↔
    (∀ w, (fractionGraph p q).Adj u w → w ≠ v →
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet w).ncard ≤
      ((fractionGraph p q).neighborSet u ∩ (fractionGraph p q).neighborSet v).ncard) := by
    constructor
    · intro h w hadj hne
      rcases h w hadj hne with hgt | heq
      · exact Nat.le_of_lt hgt
      · exact Nat.le_of_eq heq.symm
    · intro h w hadj hne
      exact (Nat.lt_or_eq_of_le (h w hadj hne)).elim
        (fun hlt => Or.inl hlt) (fun heq => Or.inr heq.symm)
  rw [rhs_equiv]
  -- Now the goal is: distMod p u v = 1 ↔ ∀ w, Adj u w → w ≠ v →
  --   ncard(N(u) ∩ N(w)) ≤ ncard(N(u) ∩ N(v))
  -- We use the fact that ncard(N(u) ∩ N(x)) = ncard(N(u)) - ncard(N(u) \ N(x))
  -- for any adjacent x (since N(u) ∩ N(x) and N(u) \ N(x) partition N(u)).
  -- So the comparison reduces to: ncard(N(u) \ N(v)) ≤ ncard(N(u) \ N(w)).
  --
  -- Key facts (by shift invariance, WLOG u = 0):
  -- * N(u) \ N(x) = {y ∈ N(u) | ¬ Adj x y} = {y | distMod u y < q ∧ (x = y ∨ distMod x y ≥ q)}
  -- * For distMod(u,v) = d with d < q:
  --   ncard(N(u) \ N(v)) = 2*d  (the "boundary" elements that are neighbors of u but not of v)
  --   Specifically: S(v) = {x ∈ N(u) | distMod(v,x) ≥ q} ∪ {v}
  --   The elements at distance q-1, q-2, ..., q-d+1 from u
  --   that are at distance ≥ q from v contribute,
  --   plus v itself. Total = 2d elements (d from each "side").
  --
  -- Forward: if distMod(u,v) = 1, then ncard(N(u)\N(v)) = 2.
  --          For any adjacent w, ncard(N(u)\N(w)) ≥ 2
  --          (since w ∈ N(u)\N(w), plus at least one more).
  --          So ncard(N(u)\N(v)) ≤ ncard(N(u)\N(w)), giving the desired inequality.
  --
  -- Backward: if distMod(u,v) = d ≥ 2, take w with distMod(u,w) = 1 (exists since q ≥ 3).
  --           ncard(N(u)\N(v)) = 2d ≥ 4 > 2 = ncard(N(u)\N(w)).
  --           So ncard(N(u)∩N(w)) > ncard(N(u)∩N(v)), contradicting the ∀ condition.
  --
  -- We prove this using a direct cardinality argument.
  -- Since the full combinatorial argument is complex, we use a cleaner approach:
  -- Define the "anti-neighborhood" S(x) = N(u) \ N(x) for adjacent x.
  -- We compute ncard(S(x)) by direct enumeration.
  --
  -- Instead of full generality, we use two key helper claims:
  -- Claim 1: distMod(u,v) = 1 → ncard(S(v)) ≤ 2
  -- Claim 2: For any w adjacent to u with w ≠ v, ncard(S(w)) ≥ 2
  -- Claim 3: distMod(u,v) ≥ 2 → ncard(S(v)) ≥ 3
  -- Claim 4: distMod(u,w) = 1 → ncard(S(w)) ≤ 2
  --
  -- Forward from Claims 1 + 2: ncard(S(v)) ≤ 2 ≤ ncard(S(w))
  -- Backward contrapositive from Claims 3 + 4: take w with distMod = 1 (exists by q ≥ 3),
  --   ncard(S(v)) ≥ 3 > 2 ≥ ncard(S(w))

  -- We use a cleaner approach: define everything in terms of Finsets for decidability.
  -- The neighborSet of u in fractionGraph can be expressed as a Finset.

  -- For the proof, we use the abstract fact that N(u) ∩ N(x) and N(u) \ N(x) partition N(u),
  -- and that ncard(N(u) \ N(x)) determines the comparison.

  -- Abbreviations:
  set G := fractionGraph p q with hG_def
  set Nu := G.neighborSet u with hNu_def
  -- Key helper: the neighbor set of any vertex in fractionGraph is finite
  have hfin_Nu : Nu.Finite := by
    rw [hNu_def, fractionGraph_neighborSet]
    exact Set.Finite.subset (Set.toFinite _) (fun x _ => trivial)
  -- Helper: N(u) ∩ N(x) is finite
  have hfin_inter : ∀ x, (Nu ∩ G.neighborSet x).Finite :=
    fun x => Set.Finite.subset hfin_Nu Set.inter_subset_left
  -- Helper: N(u) \ N(x) is finite
  have hfin_diff : ∀ x, (Nu \ G.neighborSet x).Finite :=
    fun x => Set.Finite.subset hfin_Nu Set.diff_subset
  -- Key: ncard(N(u) ∩ N(x)) + ncard(N(u) \ N(x)) = ncard(N(u))
  have partition : ∀ x, (Nu ∩ G.neighborSet x).ncard + (Nu \ G.neighborSet x).ncard = Nu.ncard := by
    intro x
    rw [← Set.ncard_union_add_ncard_inter (Nu ∩ G.neighborSet x) (Nu \ G.neighborSet x)
      (hfin_inter x) (hfin_diff x)]
    have union_eq : (Nu ∩ G.neighborSet x) ∪ (Nu \ G.neighborSet x) = Nu := by
      ext y
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
      · intro h1
        by_cases h2 : y ∈ G.neighborSet x
        · left; exact ⟨h1, h2⟩
        · right; exact ⟨h1, h2⟩
    have inter_eq : (Nu ∩ G.neighborSet x) ∩ (Nu \ G.neighborSet x) = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false]
      intro ⟨⟨_, h2⟩, ⟨_, h3⟩⟩
      exact h3 h2
    rw [union_eq, inter_eq]
    simp [Set.ncard_empty]
  -- Therefore the comparison ncard(N(u) ∩ N(w)) ≤ ncard(N(u) ∩ N(v))
  -- is equivalent to ncard(N(u) \ N(v)) ≤ ncard(N(u) \ N(w))
  have comparison_equiv : ∀ x, G.Adj u x →
      ((Nu ∩ G.neighborSet x).ncard ≤ (Nu ∩ G.neighborSet v).ncard ↔
      (Nu \ G.neighborSet v).ncard ≤ (Nu \ G.neighborSet x).ncard) := by
    intro x _
    have hx := partition x
    have hv := partition v
    constructor <;> intro h <;> omega
  -- Now reformulate goal in terms of set differences
  suffices h_main : distMod p u v = 1 ↔
      ∀ w, G.Adj u w → w ≠ v →
        (Nu \ G.neighborSet v).ncard ≤ (Nu \ G.neighborSet w).ncard by
    constructor
    · intro h w hadj_uw hw_ne
      exact (comparison_equiv w hadj_uw).mpr (h_main.mp h w hadj_uw hw_ne)
    · intro h
      exact h_main.mpr fun w hadj_uw hw_ne =>
        (comparison_equiv w hadj_uw).mp (h w hadj_uw hw_ne)
  -- Now we need to compute ncard(Nu \ G.neighborSet x) for various x.
  -- Nu \ G.neighborSet x = {y ∈ Nu | y ∉ G.neighborSet x}
  --                       = {y | Adj u y ∧ ¬ Adj x y}
  --                       = {y | y ≠ u ∧ distMod u y < q ∧ (y = x ∨ distMod x y ≥ q)}

  -- Key characterization of the set difference
  have diff_char : ∀ x, Nu \ G.neighborSet x =
      {y | G.Adj u y ∧ ¬ G.Adj x y} := by
    intro x
    ext y
    simp only [Set.mem_diff, mem_neighborSet, Set.mem_setOf_eq]
    rfl
  -- Now we express Adj conditions more explicitly
  have adj_iff : ∀ a b : ZMod p, G.Adj a b ↔ a ≠ b ∧ distMod p a b < q := by
    intro a b; simp only [hG_def, fractionGraph]
  -- The "anti-neighborhood" S(x) = Nu \ G.neighborSet x
  -- = {y | y ≠ u ∧ distMod u y < q ∧ (y = x ∨ distMod x y ≥ q)}
  have diff_explicit : ∀ x, G.Adj u x →
      Nu \ G.neighborSet x = {y | y ≠ u ∧ distMod p u y < q ∧ (y = x ∨ distMod p x y ≥ q)} := by
    intro x hadj_ux; rw [diff_char]
    ext y; simp only [Set.mem_setOf_eq]
    constructor
    · intro ⟨hadj_uy, hnadj_xy⟩
      rw [adj_iff] at hadj_uy hnadj_xy
      simp only [not_and] at hnadj_xy
      by_cases hyx : y = x
      · exact ⟨hadj_uy.1.symm, hadj_uy.2, Or.inl hyx⟩
      · have hxy : x ≠ y := fun heq => hyx heq.symm
        exact ⟨hadj_uy.1.symm, hadj_uy.2,
          Or.inr (Nat.le_of_not_lt (hnadj_xy hxy))⟩
    · intro ⟨hyu, hdist_uy, hcase⟩
      constructor
      · rw [adj_iff]; exact ⟨hyu.symm, hdist_uy⟩
      · rw [adj_iff]
        push_neg
        intro heq_yx
        rcases hcase with rfl | hge
        · exact absurd rfl heq_yx
        · exact hge
  -- Key claim: x is always in S(x)
  have x_in_diff : ∀ x, G.Adj u x → x ∈ Nu \ G.neighborSet x := by
    intro x hadj_ux
    exact ⟨hadj_ux, G.loopless.irrefl x⟩
  -- The proof now splits into forward and backward directions.
  constructor
  · -- Forward: distMod u v = 1 → ∀ w adj to u, w ≠ v → ncard(S(v)) ≤ ncard(S(w))
    intro hdist1 w hadj_uw hw_ne_v
    -- Strategy: show (1) ncard(S(v)) ≤ 2 and (2) ncard(S(w)) ≥ 2.
    -- For (1): since distMod(u,v) = 1, any y ∈ S(v) \ {v} must satisfy distMod(u,y) = q-1
    -- (by triangle inequality), and of the 2 elements at distance q-1 from u, only one
    -- has distMod(v,·) ≥ q. So S(v) ⊆ {v, boundary_element}.
    -- For (2): w ∈ S(w), and we find another element (the boundary element on the
    -- opposite side from w).

    -- For (2): w ∈ S(w) (by x_in_diff). We need another element in S(w).
    -- Since w ≠ v and hadj, distMod(u,w) ≥ 1.
    -- Consider v: is v ∈ S(w)? v ∈ S(w) iff distMod w v ≥ q (since v ∈ N(u) by hadj).
    -- Not necessarily.
    -- For (2): w ∈ S(w), and the element at distance q-1 from u on the opposite side
    -- from w is also in S(w) (its distance to w is ≥ q), giving ncard(S(w)) ≥ 2.

    -- Part A: ncard(S(v)) ≤ 2
    have h_Sv_le : (Nu \ G.neighborSet v).ncard ≤ 2 := by
      -- Since distMod u v = 1, we have v = u - 1 or v = u + 1.
      rcases distMod_eq_one_imp_adjacent p hp u v hdist1 with rfl | rfl
      · -- Case v = u - 1
        suffices hsub : Nu \ G.neighborSet (u - 1) ⊆
            ({u - 1, u + ↑(q - 1)} : Set (ZMod p)) by
          calc (Nu \ G.neighborSet (u - 1)).ncard
              ≤ ({u - 1, u + ↑(q - 1)} : Set (ZMod p)).ncard :=
                Set.ncard_le_ncard hsub (Set.toFinite _)
            _ ≤ 2 := by
              calc ({u - 1, u + ↑(q - 1)} : Set (ZMod p)).ncard
                  ≤ ({u + ↑(q - 1)} : Set (ZMod p)).ncard + 1 :=
                    Set.ncard_insert_le (u - 1) _
                _ = 1 + 1 := by rw [Set.ncard_singleton]
                _ = 2 := by norm_num
        intro y hy
        rw [diff_explicit (u - 1) hadj] at hy
        simp only [Set.mem_setOf_eq] at hy
        obtain ⟨hyu, hdist_uy, rfl | hdist_vy⟩ := hy
        · exact Set.mem_insert (u - 1) _
        · apply Set.mem_insert_of_mem; rw [Set.mem_singleton_iff]
          -- y ≠ u, distMod(u,y) < q, distMod(u-1, y) ≥ q
          set d := (u - y).val with hd_def
          have hd_lt_p : d < p := ZMod.val_lt (u - y)
          have hmin_lt : min d (p - d) < q := hdist_uy
          -- (u - 1 - y).val = ((u - y).val + (p - 1)) % p  since  u-1-y = (u-y) - 1
          have hd'_eq : (u - 1 - y).val = (d + (p - 1)) % p := by
            have : u - 1 - y = (u - y) + (-1) := by ring
            rw [this, ZMod.val_add]
            have hn1 : (-1 : ZMod p).val = p - 1 := zmod_val_neg_one p
            rw [hn1]
          -- Case split on which side of the circle
          have hd_cases : d < q ∨ p - d < q := by
            by_contra h; push_neg at h
            exact not_lt.mpr (Nat.le_min.mpr ⟨h.1, h.2⟩) hmin_lt
          rcases hd_cases with hd_pos | hd_neg
          · -- Positive side: d < q
            -- d + (p-1) ≥ p - 1 ≥ p - 1. If d = 0, impossible (hyu). So d ≥ 1.
            have hd_pos' : d ≥ 1 := by
              rcases Nat.eq_zero_or_pos d with h0 | hpos
              · exfalso
                have hval0 : (u - y).val = 0 := by rw [← hd_def]; exact h0
                have huy_eq : u - y = 0 := (ZMod.val_eq_zero (u - y)).mp hval0
                exact hyu (eq_of_sub_eq_zero huy_eq).symm
              · exact hpos
            -- (d + (p-1)) % p = d - 1 (since d + (p-1) = (d-1) + p)
            have hmod : (d + (p - 1)) % p = d - 1 := by
              rw [show d + (p - 1) = (d - 1) + 1 * p from by omega]
              rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : d - 1 < p)]
            have hd'_val : (u - 1 - y).val = d - 1 := by rw [hd'_eq, hmod]
            have hdist_vy' : distMod p (u - 1) y = min (d - 1) (p - (d - 1)) := by
              simp only [distMod, hd'_val]
            rw [hdist_vy'] at hdist_vy
            -- min(d-1, p-(d-1)) ≥ q forces d-1 ≥ q, but d < q gives d-1 ≤ q-2.
            -- Contradiction: this case is vacuous (no elements on the positive side).
            exfalso
            have : q ≤ d - 1 := le_trans hdist_vy (min_le_left _ _)
            omega
          · -- Negative side: p - d < q (so d > p - q)
            -- (d + (p-1)) % p: since d > p - q ≥ q (as 2q < p), d ≥ q+1, d + (p-1) ≥ p + q.
            -- d + (p-1) < p + (p-1) = 2p - 1, so (d+(p-1)) % p = d - 1 (since d+(p-1) = (d-1) + p).
            have hd_pos' : d ≥ 1 := by
              rcases Nat.eq_zero_or_pos d with h0 | hpos
              · exfalso
                have hval0 : (u - y).val = 0 := by rw [← hd_def]; exact h0
                have huy_eq : u - y = 0 := (ZMod.val_eq_zero (u - y)).mp hval0
                exact hyu (eq_of_sub_eq_zero huy_eq).symm
              · exact hpos
            have hmod : (d + (p - 1)) % p = d - 1 := by
              rw [show d + (p - 1) = (d - 1) + 1 * p from by omega]
              rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : d - 1 < p)]
            have hd'_val : (u - 1 - y).val = d - 1 := by rw [hd'_eq, hmod]
            have hdist_vy' : distMod p (u - 1) y = min (d - 1) (p - (d - 1)) := by
              simp only [distMod, hd'_val]
            rw [hdist_vy'] at hdist_vy
            -- p - d < q and min(d - 1, p - d + 1) ≥ q
            -- p - d + 1 = p - (d - 1), so min(d-1, p-d+1) ≥ q
            -- d - 1 ≥ q (from min ≥ q) and p - d + 1 ≥ q
            -- Also p - d < q, so p - d ≤ q - 1, d ≥ p - q + 1.
            -- Combined with d < p (always): d ∈ {p-q+1, ..., p-1}.
            -- d - 1 ≥ q forces d ≥ q + 1, and p - (d-1) ≥ q forces d ≤ p - q + 1.
            -- Combined with p - d < q (i.e. d > p - q), we get d = p - q + 1.
            have hd_ge : d ≥ q + 1 := by
              have := le_trans hdist_vy (min_le_left _ _); omega
            have hd_le : d ≤ p - q + 1 := by
              have := le_trans hdist_vy (min_le_right _ _); omega
            have hd_gt : d > p - q := by omega
            have hd_eq : d = p - q + 1 := by omega
            -- So (u - y).val = p - q + 1, meaning u - y = ↑(p - q + 1)
            -- We need to show y = u + ↑(q - 1).
            -- u - y = ↑(p - q + 1) means y = u - ↑(p - q + 1).
            -- u - ↑(p - q + 1) = u + ↑(q - 1) in ZMod p since (p - q + 1) + (q - 1) = p ≡ 0.
            have hval_cast : (↑(p - q + 1) : ZMod p).val = p - q + 1 := by
              rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
            have hsub_eq : u - y = ↑(p - q + 1) :=
              ZMod.val_injective p (by rw [hd_def.symm, hd_eq, hval_cast])
            -- Now show ↑(p - q + 1) = -↑(q - 1) in ZMod p
            have hcast_eq : (↑(p - q + 1) : ZMod p) = -(↑(q - 1) : ZMod p) := by
              rw [eq_neg_iff_add_eq_zero]
              change (↑(p - q + 1) : ZMod p) + (↑(q - 1) : ZMod p) = 0
              rw [← Nat.cast_add]
              rw [show (p - q + 1) + (q - 1) = p from by omega]
              exact ZMod.natCast_self p
            calc y = u - (u - y) := by ring
              _ = u - ↑(p - q + 1) := by rw [hsub_eq]
              _ = u - (-(↑(q - 1) : ZMod p)) := by rw [hcast_eq]
              _ = u + ↑(q - 1) := by ring
      · -- Case v = u + 1
        suffices hsub : Nu \ G.neighborSet (u + 1) ⊆
            ({u + 1, u - ↑(q - 1)} : Set (ZMod p)) by
          calc (Nu \ G.neighborSet (u + 1)).ncard
              ≤ ({u + 1, u - ↑(q - 1)} : Set (ZMod p)).ncard :=
                Set.ncard_le_ncard hsub (Set.toFinite _)
            _ ≤ 2 := by
              calc ({u + 1, u - ↑(q - 1)} : Set (ZMod p)).ncard
                  ≤ ({u - ↑(q - 1)} : Set (ZMod p)).ncard + 1 :=
                    Set.ncard_insert_le (u + 1) _
                _ = 1 + 1 := by rw [Set.ncard_singleton]
                _ = 2 := by norm_num
        intro y hy
        rw [diff_explicit (u + 1) hadj] at hy
        simp only [Set.mem_setOf_eq] at hy
        obtain ⟨hyu, hdist_uy, rfl | hdist_vy⟩ := hy
        · exact Set.mem_insert (u + 1) _
        · apply Set.mem_insert_of_mem; rw [Set.mem_singleton_iff]
          set d := (u - y).val with hd_def
          have hd_lt_p : d < p := ZMod.val_lt (u - y)
          have hmin_lt : min d (p - d) < q := hdist_uy
          have hd'_eq : (u + 1 - y).val = (d + 1) % p := by
            change (u + 1 - y).val = ((u - y).val + 1) % p
            have : u + 1 - y = (u - y) + 1 := by ring
            rw [this, ZMod.val_add]
            haveI : Fact (1 < p) := ⟨by omega⟩
            simp [ZMod.val_one]
          have hd_cases : d < q ∨ p - d < q := by
            by_contra h; push_neg at h
            exact not_lt.mpr (Nat.le_min.mpr ⟨h.1, h.2⟩) hmin_lt
          rcases hd_cases with hd_pos | hd_neg
          · -- Positive side: d < q, so (d+1) % p = d+1
            have hd1_lt_p : d + 1 < p := by omega
            have hd'_val : (u + 1 - y).val = d + 1 := by
              rw [hd'_eq, Nat.mod_eq_of_lt hd1_lt_p]
            have hdist_vy' : distMod p (u + 1) y = min (d + 1) (p - (d + 1)) := by
              simp only [distMod, hd'_val]
            rw [hdist_vy'] at hdist_vy
            have hd1_ge_q : q ≤ d + 1 := le_trans hdist_vy (min_le_left _ _)
            have hd_eq : d = q - 1 := by omega
            have hval2 : (↑(q - 1) : ZMod p).val = q - 1 := by
              rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega : q - 1 < p)
            have hsub_eq : u - y = ↑(q - 1) :=
              ZMod.val_injective p (by rw [hd_def.symm, hd_eq, hval2])
            calc y = u - (u - y) := by ring
              _ = u - ↑(q - 1) := by rw [hsub_eq]
          · -- Negative side: p - d < q
            exfalso
            have hd_gt : d > p - q := by omega
            by_cases hd_pm1 : d = p - 1
            · have hmod0 : (d + 1) % p = 0 := by
                have : d + 1 = p := by omega
                rw [this, Nat.mod_self]
              rw [hmod0] at hd'_eq
              have : distMod p (u + 1) y = 0 := by
                simp only [distMod, hd'_eq]; simp
              omega
            · have hd1_lt_p : d + 1 < p := by omega
              have hd'_val : (u + 1 - y).val = d + 1 := by
                rw [hd'_eq, Nat.mod_eq_of_lt hd1_lt_p]
              have hdist_vy' : distMod p (u + 1) y = min (d + 1) (p - (d + 1)) := by
                simp only [distMod, hd'_val]
              rw [hdist_vy'] at hdist_vy
              have : p - (d + 1) < q := by omega
              have : min (d + 1) (p - (d + 1)) < q :=
                lt_of_le_of_lt (min_le_right _ _) (by assumption)
              omega
    -- Part B: ncard(S(w)) ≥ 2
    have h_Sw_ge : (Nu \ G.neighborSet w).ncard ≥ 2 := by
      -- Element 1: w ∈ S(w)
      have hw_in : w ∈ Nu \ G.neighborSet w := x_in_diff w hadj_uw
      -- Element 2: find y ∈ Nu \ N(w) with y ≠ w
      -- Set dw = distMod(u, w). We know 1 ≤ dw < q.
      have hadj_uw' := hadj_uw
      rw [adj_iff] at hadj_uw'
      have huw_ne := hadj_uw'.1
      have hdist_uw_lt_q := hadj_uw'.2
      have hdist_uw_pos : distMod p u w ≥ 1 := by
        rcases Nat.eq_zero_or_pos (distMod p u w) with h0 | hpos
        · exfalso
          simp only [distMod] at h0
          have hval_lt := ZMod.val_lt (u - w)
          have hval_zero : (u - w).val = 0 := by omega
          exact huw_ne (eq_of_sub_eq_zero ((ZMod.val_eq_zero (u - w)).mp hval_zero))
        · exact hpos
      -- Choose y based on which side of the circle w is on.
      set ew := (w - u).val with hew_def
      have hew_lt_p : ew < p := ZMod.val_lt (w - u)
      have hwu_ne : w - u ≠ 0 := sub_ne_zero.mpr huw_ne.symm
      have hew_pos : ew > 0 := by
        rcases Nat.eq_zero_or_pos ew with h0 | hpos
        · have hval0 : (w - u).val = 0 := by rw [← hew_def]; exact h0
          exact absurd ((ZMod.val_eq_zero _).mp hval0) hwu_ne
        · exact hpos
      -- (u - w).val = p - ew
      have huw_val : (u - w).val = p - ew := by
        have : u - w = -(w - u) := by ring
        rw [this, ZMod.neg_val, if_neg hwu_ne]
      -- distMod p u w = min(p - ew, ew)
      have hdist_uw_eq : distMod p u w = min (p - ew) ew := by
        simp only [distMod, huw_val]; congr 1; omega
      -- Useful casts
      have hq_ne_zero : (q : ZMod p) ≠ 0 := by
        intro h
        have hdvd := (ZMod.natCast_eq_zero_iff q p).mp h
        have := Nat.le_of_dvd (by omega) hdvd; omega
      have hq_val : (q : ZMod p).val = q := by
        rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
      by_cases hside : ew * 2 ≤ p
      · -- w is on the "positive side": ew ≤ p/2
        -- distMod(u,w) = ew
        have hdist_uw_ew : distMod p u w = ew := by
          rw [hdist_uw_eq]; exact min_eq_right (by omega)
        -- Take y = w - ↑q. Then:
        -- (w - y).val = q, so distMod(w, y) = min(q, p-q) = q ≥ q ✓
        -- distMod(u, y) = q - ew < q ✓
        -- y ≠ w since q ≠ 0 in ZMod p
        -- y ≠ u since distMod(u, y) = q - ew ≥ 1
        set y := w - (q : ZMod p)
        have hwy_val : (w - y).val = q := by
          change (w - (w - (q : ZMod p))).val = q
          rw [show w - (w - (q : ZMod p)) = (q : ZMod p) from by ring]
          exact hq_val
        have hdist_wy : distMod p w y = q := by
          simp only [distMod, hwy_val]
          exact min_eq_left (by omega)
        -- Compute distMod(u, y)
        -- u - y = u - (w - ↑q) = (u - w) + ↑q
        have huy_val : (u - y).val = q - ew := by
          change (u - (w - (q : ZMod p))).val = q - ew
          rw [show u - (w - (q : ZMod p)) = (u - w) + (q : ZMod p) from by ring]
          rw [ZMod.val_add, huw_val, hq_val]
          rw [show p - ew + q = (q - ew) + 1 * p from by omega]
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : q - ew < p)]
        have hdist_uy : distMod p u y = q - ew := by
          simp only [distMod, huy_val]
          exact min_eq_left (by omega)
        have hy_ne_w : y ≠ w := by
          intro h
          have : (w - y).val = 0 := by rw [h, sub_self]; exact ZMod.val_zero
          rw [hwy_val] at this; omega
        have hy_ne_u : y ≠ u := by
          intro h; rw [h] at hdist_uy
          simp only [distMod, sub_self, ZMod.val_zero] at hdist_uy; simp at hdist_uy; omega
        have hy_in : y ∈ Nu \ G.neighborSet w := by
          rw [diff_explicit w hadj_uw]; simp only [Set.mem_setOf_eq]
          exact ⟨hy_ne_u, by omega, Or.inr (by omega)⟩
        -- Conclude: {w, y} ⊆ S(w), so ncard ≥ 2
        have hsub : ({w, y} : Set (ZMod p)) ⊆ Nu \ G.neighborSet w := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact hw_in
          · exact hy_in
        have h2 : ({w, y} : Set (ZMod p)).ncard = 2 := Set.ncard_pair hy_ne_w.symm
        linarith [Set.ncard_le_ncard hsub (Set.toFinite _)]
      · -- w is on the "negative side": ew > p/2
        push_neg at hside
        -- distMod(u,w) = p - ew since p - ew < ew
        have hdist_uw_pew : distMod p u w = p - ew := by
          rw [hdist_uw_eq]; exact min_eq_left (by omega)
        -- Since distMod(u,w) < q, we have p - ew < q, i.e. ew > p - q
        have hew_gt : ew > p - q := by omega
        -- Take y = w + ↑q.
        set y := w + (q : ZMod p)
        -- (w - y).val = p - q
        have hwy_val : (w - y).val = p - q := by
          change (w - (w + (q : ZMod p))).val = p - q
          rw [show w - (w + (q : ZMod p)) = -(q : ZMod p) from by ring]
          rw [ZMod.neg_val, if_neg hq_ne_zero, hq_val]
        -- distMod(w, y) = q
        have hdist_wy : distMod p w y = q := by
          simp only [distMod, hwy_val]
          have h_eq : p - (p - q) = q := by omega
          rw [h_eq]; exact min_eq_right (by omega)
        -- Compute (u - y).val
        -- u - y = (u - w) - ↑q = (u - w) + (-↑q)
        -- (u - w).val = p - ew, (-↑q).val = p - q
        -- sum = (p - ew) + (p - q) = 2p - ew - q
        -- Since ew > p - q: ew + q > p, so 2p - ew - q < p.
        -- Since ew < p and q < p: 2p - ew - q > 0.
        -- So (2p - ew - q) % p = 2p - ew - q.
        have huy_val : (u - y).val = 2 * p - ew - q := by
          change (u - (w + (q : ZMod p))).val = 2 * p - ew - q
          rw [show u - (w + (q : ZMod p)) = (u - w) + (-(q : ZMod p)) from by ring]
          rw [ZMod.val_add, huw_val, ZMod.neg_val, if_neg hq_ne_zero, hq_val]
          have h1 : p - ew + (p - q) = 2 * p - ew - q := by omega
          rw [h1, Nat.mod_eq_of_lt (by omega : 2 * p - ew - q < p)]
        -- distMod(u, y) = min(2p - ew - q, ew + q - p)
        -- = ew + q - p (since ew + q - p ≤ 2p - ew - q, as 2ew + 2q ≤ 3p)
        -- = q - (p - ew) = q - distMod(u,w)
        have hdist_uy : distMod p u y = ew + q - p := by
          simp only [distMod, huy_val]
          have h_eq : p - (2 * p - ew - q) = ew + q - p := by omega
          rw [h_eq]
          exact min_eq_right (by omega)
        have hdist_uy_lt_q : distMod p u y < q := by rw [hdist_uy]; omega
        -- y ≠ w
        have hy_ne_w : y ≠ w := by
          intro h
          have : (w - y).val = 0 := by rw [h, sub_self]; exact ZMod.val_zero
          rw [hwy_val] at this; omega
        -- y ≠ u
        have hy_ne_u : y ≠ u := by
          intro h; rw [h] at hdist_uy
          simp only [distMod, sub_self, ZMod.val_zero] at hdist_uy; simp at hdist_uy; omega
        -- y ∈ S(w)
        have hy_in : y ∈ Nu \ G.neighborSet w := by
          rw [diff_explicit w hadj_uw]; simp only [Set.mem_setOf_eq]
          exact ⟨hy_ne_u, hdist_uy_lt_q, Or.inr (by omega)⟩
        -- Conclude: {w, y} ⊆ S(w), ncard ≥ 2
        have hsub : ({w, y} : Set (ZMod p)) ⊆ Nu \ G.neighborSet w := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact hw_in
          · exact hy_in
        have h2 : ({w, y} : Set (ZMod p)).ncard = 2 := Set.ncard_pair hy_ne_w.symm
        linarith [Set.ncard_le_ncard hsub (Set.toFinite _)]
    linarith
  · -- Backward: (∀ w adj to u, w ≠ v → ncard(S(v)) ≤ ncard(S(w))) → distMod u v = 1
    -- Contrapositive: if distMod u v ≥ 2, find w with ncard(S(v)) > ncard(S(w)).
    intro h_all
    by_contra hdist_ne_1
    -- distMod u v ≥ 1 (since u ≠ v by adjacency) and ≠ 1, so distMod u v ≥ 2.
    have hadj_uv := hadj
    rw [adj_iff] at hadj_uv
    have huv_ne := hadj_uv.1
    have hdist_lt_q := hadj_uv.2
    have hdist_pos : distMod p u v ≥ 1 := by
      rcases Nat.eq_zero_or_pos (distMod p u v) with h0 | hpos
      · exfalso
        simp only [distMod] at h0
        have hval := Nat.min_eq_zero_iff.mp h0
        rcases hval with hval | hval
        · exact huv_ne (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp hval))
        · have hlt := ZMod.val_lt (u - v)
          omega
      · exact hpos
    have hdist_ge_2 : distMod p u v ≥ 2 := by omega
    -- Take w = u + 1 (or u - 1) which has distMod u w = 1.
    -- w is adjacent to u since distMod = 1 < q (q ≥ 3).
    -- We need w ≠ v.
    -- Since distMod u v ≥ 2 and distMod u (u+1) = 1, u+1 ≠ v (different distances from u are
    -- insufficient; but actually u+1 could equal v if distMod u v = 1, which we excluded).
    -- More carefully: if u+1 = v, then distMod u v = distMod u (u+1) = 1, contradiction.
    set w := u + 1 with hw_def
    have hdist_w : distMod p u w = 1 := distMod_add_one p (by omega) u
    have hadj_uw : G.Adj u w := by
      rw [adj_iff]
      constructor
      · intro heq
        exact zmod_one_ne_zero p (by omega) (by linear_combination -heq)
      · rw [hdist_w]; omega
    have hw_ne_v : w ≠ v := by
      intro heq
      rw [heq] at hdist_w
      omega
    -- Apply h_all to get ncard(S(v)) ≤ ncard(S(w))
    have hle := h_all w hadj_uw hw_ne_v
    -- Now we show this is false: ncard(S(v)) > ncard(S(w)).
    -- S(v) has ncard ≥ 3 (since distMod(u,v) ≥ 2)
    -- S(w) has ncard ≤ 2 (since distMod(u,w) = 1)
    -- So ncard(S(v)) ≥ 3 > 2 ≥ ncard(S(w)), contradiction.

    -- We establish ncard(S(w)) ≤ 2 (i.e. S(w) has at most 2 elements).
    -- S(w) = {y | y ≠ u ∧ distMod u y < q ∧ (y = w ∨ distMod w y ≥ q)}
    -- Since distMod u w = 1, w = u+1, for y ≠ w:
    -- need distMod w y ≥ q and distMod u y < q.
    -- distMod u y < q and distMod w y ≥ q with distMod u w = 1.
    -- By triangle inequality for distMod: distMod w y ≤ distMod w u + distMod u y = 1 + distMod u y
    -- So q ≤ 1 + distMod u y, giving distMod u y ≥ q-1.
    -- Combined: distMod u y = q-1 (the only possibility in {q-1}).
    -- There are exactly 2 elements at distance q-1 from u: u+(q-1) and u-(q-1).
    -- Of these, one has distMod w · = q-2 < q (NOT in S(w)).
    -- The other has distMod w · = q (IN S(w)).
    -- So S(w) = {w, boundary_element}, ncard(S(w)) = 2.
    -- But we only need ncard(S(w)) ≤ 2.
    -- S(w) ⊆ {w} ∪ {y | distMod p u y = q - 1 ∧ distMod p w y ≥ q}
    -- The second set has at most 1 element that also satisfies distMod w y ≥ q.
    -- (Of the 2 elements at distance q-1 from u, at most 1 satisfies this.)

    -- We establish {v, u+(q-1), u-(q-1)} ⊆ S(v) giving ncard ≥ 3,
    -- and S(w) ⊆ {w, u-(q-1)} giving ncard ≤ 2.

    -- Two key cardinality bounds:
    have h_Sw_le : (Nu \ G.neighborSet w).ncard ≤ 2 := by
      -- S(w) ⊆ {w, u - ↑(q-1)}, so ncard ≤ 2
      suffices hsub : Nu \ G.neighborSet w ⊆ ({w, u - ↑(q - 1)} : Set (ZMod p)) by
        calc (Nu \ G.neighborSet w).ncard
            ≤ ({w, u - ↑(q - 1)} : Set (ZMod p)).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ 2 := by
            calc ({w, u - ↑(q - 1)} : Set (ZMod p)).ncard
                ≤ ({u - ↑(q - 1)} : Set (ZMod p)).ncard + 1 := Set.ncard_insert_le w _
              _ = 1 + 1 := by rw [Set.ncard_singleton]
              _ = 2 := by norm_num
      intro y hy
      rw [diff_explicit w hadj_uw] at hy
      simp only [Set.mem_setOf_eq] at hy
      obtain ⟨hyu, hdist_uy, rfl | hdist_wy⟩ := hy
      · exact Set.mem_insert w _
      · apply Set.mem_insert_of_mem; rw [Set.mem_singleton_iff]
        -- From distMod(u,y) < q and distMod(w,y) ≥ q, deduce y = u - ↑(q-1)
        set d := (u - y).val with hd_def
        have hd_lt_p : d < p := ZMod.val_lt (u - y)
        have hmin_lt : min d (p - d) < q := hdist_uy
        -- (u+1-y).val = ((u-y).val + 1) % p
        have hd'_eq : (u + 1 - y).val = (d + 1) % p := by
          change (u + 1 - y).val = ((u - y).val + 1) % p
          have : u + 1 - y = (u - y) + 1 := by ring
          rw [this, ZMod.val_add]
          haveI : Fact (1 < p) := ⟨by omega⟩
          simp [ZMod.val_one]
        -- Case split on which side of the circle y is on
        have hd_cases : d < q ∨ p - d < q := by
          by_contra h; push_neg at h
          exact not_lt.mpr (Nat.le_min.mpr ⟨h.1, h.2⟩) hmin_lt
        rcases hd_cases with hd_pos | hd_neg
        · -- Positive side: d < q, so (d+1) % p = d+1
          have hd1_lt_p : d + 1 < p := by omega
          have hd'_val : (u + 1 - y).val = d + 1 := by
            rw [hd'_eq, Nat.mod_eq_of_lt hd1_lt_p]
          have hdist_wy' : distMod p w y = min (d + 1) (p - (d + 1)) := by
            simp only [distMod, hw_def, hd'_val]
          rw [hdist_wy'] at hdist_wy
          -- min(d+1, p-(d+1)) ≥ q implies d+1 ≥ q
          have hd1_ge_q : q ≤ d + 1 :=
            le_trans hdist_wy (min_le_left _ _)
          -- d < q and d+1 ≥ q gives d = q-1
          have hd_eq : d = q - 1 := by omega
          -- Deduce y = u - ↑(q-1) via val_injective
          have hval2 : (↑(q - 1) : ZMod p).val = q - 1 := by
            rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega : q - 1 < p)
          have hsub_eq : u - y = ↑(q - 1) :=
            ZMod.val_injective p (by rw [hd_def.symm, hd_eq, hval2])
          calc y = u - (u - y) := by ring
            _ = u - ↑(q - 1) := by rw [hsub_eq]
        · -- Negative side: p - d < q (so d > p - q)
          exfalso
          have hd_gt : d > p - q := by omega
          by_cases hd_pm1 : d = p - 1
          · -- d = p - 1: (d+1) % p = 0, distMod = 0
            have hmod0 : (d + 1) % p = 0 := by
              have : d + 1 = p := by omega
              rw [this, Nat.mod_self]
            rw [hmod0] at hd'_eq
            have : distMod p w y = 0 := by
              simp only [distMod, hw_def, hd'_eq]; simp
            omega
          · -- d < p - 1: (d+1) % p = d+1, distMod = min(d+1, p-d-1) < q
            have hd1_lt_p : d + 1 < p := by omega
            have hd'_val : (u + 1 - y).val = d + 1 := by
              rw [hd'_eq, Nat.mod_eq_of_lt hd1_lt_p]
            have hdist_wy' : distMod p w y = min (d + 1) (p - (d + 1)) := by
              simp only [distMod, hw_def, hd'_val]
            rw [hdist_wy'] at hdist_wy
            have : p - (d + 1) < q := by omega
            have : min (d + 1) (p - (d + 1)) < q :=
              lt_of_le_of_lt (min_le_right _ _) (by assumption)
            omega
    have h_Sv_ge : (Nu \ G.neighborSet v).ncard ≥ 3 := by
      -- We exhibit 3 distinct elements in Nu \ G.neighborSet v.
      set e := (v - u).val with he_def
      have he_lt_p : e < p := ZMod.val_lt (v - u)
      have hvu_ne : v - u ≠ 0 := sub_ne_zero.mpr huv_ne.symm
      have he_pos : e > 0 := by
        rcases Nat.eq_zero_or_pos e with h0 | hpos
        · exact absurd ((ZMod.val_eq_zero _).mp h0) hvu_ne
        · exact hpos
      have huv_val : (u - v).val = p - e := by
        have heq : u - v = -(v - u) := by ring
        rw [heq, ZMod.neg_val, if_neg hvu_ne]
      -- distMod p u v = min(p - e, e)
      have hdist_eq : distMod p u v = min (p - e) e := by
        simp only [distMod, huv_val]; congr 1; omega
      -- Both e and p-e are ≥ 2
      have he_ge_2 : e ≥ 2 := le_trans (hdist_eq ▸ hdist_ge_2) (min_le_right _ _)
      have hpe_ge_2 : p - e ≥ 2 := le_trans (hdist_eq ▸ hdist_ge_2) (min_le_left _ _)
      -- Helper: casts are nonzero
      have hq_ne_zero : (q : ZMod p) ≠ 0 := by
        intro h
        have hdvd := (ZMod.natCast_eq_zero_iff q p).mp h
        have := Nat.le_of_dvd (by omega) hdvd; omega
      have hq1_ne_zero : ((q + 1 : ℕ) : ZMod p) ≠ 0 := by
        intro h
        have hdvd := (ZMod.natCast_eq_zero_iff (q + 1) p).mp h
        have := Nat.le_of_dvd (by omega) hdvd; omega
      have hq_val : (q : ZMod p).val = q := by
        rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
      have hq1_val : ((q + 1 : ℕ) : ZMod p).val = q + 1 := by
        rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
      -- v is always in S(v)
      have hv_in : v ∈ Nu \ G.neighborSet v := x_in_diff v hadj
      by_cases hside : e * 2 ≤ p
      · -- Case 1: v is on the "positive side". Elements: v, v - ↑q, v - ↑(q+1).
        have he_lt_q : e < q := by
          have : distMod p u v = e := by rw [hdist_eq]; exact min_eq_right (by omega)
          omega
        -- Distinctness
        have hne_vq : v ≠ v - (q : ZMod p) := by
          intro h; apply hq_ne_zero
          have : v - (v - (q : ZMod p)) = 0 := by rw [← h]; ring
          rwa [sub_sub_cancel] at this
        have hne_vq1 : v ≠ v - ((q + 1 : ℕ) : ZMod p) := by
          intro h; apply hq1_ne_zero
          have : v - (v - ((q + 1 : ℕ) : ZMod p)) = 0 := by rw [← h]; ring
          rwa [sub_sub_cancel] at this
        have hne_qq1 : v - (q : ZMod p) ≠ v - ((q + 1 : ℕ) : ZMod p) := by
          intro h
          have heq : (q : ZMod p) = ((q + 1 : ℕ) : ZMod p) := sub_right_injective h
          have := congrArg ZMod.val heq; rw [hq_val, hq1_val] at this; omega
        -- distMod p v (v - ↑q) = q ≥ q
        have hdist_v_vq : distMod p v (v - (q : ZMod p)) = q := by
          simp only [distMod, show v - (v - (q : ZMod p)) = (q : ZMod p) from by ring, hq_val]
          exact min_eq_left (by omega)
        -- distMod p u (v - ↑q) = q - e < q
        have hdist_u_vq : distMod p u (v - (q : ZMod p)) = q - e := by
          simp only [distMod, show u - (v - (q : ZMod p)) = (u - v) + (q : ZMod p) from by ring]
          have : ((u - v) + (q : ZMod p)).val = q - e := by
            rw [ZMod.val_add, huv_val, hq_val]
            rw [show p - e + q = q - e + 1 * p from by omega]
            rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : q - e < p)]
          rw [this]; exact min_eq_left (by omega)
        have hvq_ne_u : v - (q : ZMod p) ≠ u := by
          intro h; rw [h] at hdist_u_vq
          simp only [distMod, sub_self, ZMod.val_zero] at hdist_u_vq; simp at hdist_u_vq; omega
        have hvq_in : v - (q : ZMod p) ∈ Nu \ G.neighborSet v := by
          rw [diff_explicit v hadj]; simp only [Set.mem_setOf_eq]
          exact ⟨hvq_ne_u, by omega, Or.inr (by omega)⟩
        -- distMod p v (v - ↑(q+1)) ≥ q
        have hdist_v_vq1_ge : distMod p v (v - ((q + 1 : ℕ) : ZMod p)) ≥ q := by
          simp only [distMod,
            show v - (v - ((q + 1 : ℕ) : ZMod p)) = ((q + 1 : ℕ) : ZMod p) from by ring,
            hq1_val]
          exact le_min (by omega) (by omega)
        -- distMod p u (v - ↑(q+1)) = q + 1 - e < q
        have hdist_u_vq1 : distMod p u (v - ((q + 1 : ℕ) : ZMod p)) = q + 1 - e := by
          simp only [distMod,
            show u - (v - ((q + 1 : ℕ) : ZMod p)) = (u - v) + ((q + 1 : ℕ) : ZMod p)
              from by ring]
          have : ((u - v) + ((q + 1 : ℕ) : ZMod p)).val = q + 1 - e := by
            rw [ZMod.val_add, huv_val, hq1_val]
            rw [show p - e + (q + 1) = q + 1 - e + 1 * p from by omega]
            rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : q + 1 - e < p)]
          rw [this]; exact min_eq_left (by omega)
        have hvq1_ne_u : v - ((q + 1 : ℕ) : ZMod p) ≠ u := by
          intro h; rw [h] at hdist_u_vq1
          simp only [distMod, sub_self, ZMod.val_zero] at hdist_u_vq1
          simp at hdist_u_vq1; omega
        have hvq1_in : v - ((q + 1 : ℕ) : ZMod p) ∈ Nu \ G.neighborSet v := by
          rw [diff_explicit v hadj]; simp only [Set.mem_setOf_eq]
          exact ⟨hvq1_ne_u, by omega, Or.inr hdist_v_vq1_ge⟩
        -- Conclude ncard ≥ 3
        have hsub : ({v, v - (q : ZMod p), v - ((q + 1 : ℕ) : ZMod p)} : Set (ZMod p)) ⊆
            Nu \ G.neighborSet v := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have h3 : ({v, v - (q : ZMod p), v - ((q + 1 : ℕ) : ZMod p)} : Set (ZMod p)).ncard =
            3 := by
          rw [Set.ncard_eq_toFinset_card']
          simp only [Set.toFinset_insert, Set.toFinset_singleton]
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hne_qq1
          · simp only [Finset.mem_insert, Finset.mem_singleton]
            push_neg; exact ⟨hne_vq, hne_vq1⟩
        linarith [Set.ncard_le_ncard hsub (Set.toFinite _)]
      · -- Case 2: v is on the "negative side". Elements: v, v + ↑q, v + ↑(q+1).
        push_neg at hside
        have hpe_lt_q : p - e < q := by
          have : distMod p u v = p - e := by rw [hdist_eq]; exact min_eq_left (by omega)
          omega
        -- Distinctness
        have hne_vq : v ≠ v + (q : ZMod p) := by
          intro h; apply hq_ne_zero
          have : v + (q : ZMod p) - v = 0 := by rw [← h]; ring
          rwa [add_sub_cancel_left] at this
        have hne_vq1 : v ≠ v + ((q + 1 : ℕ) : ZMod p) := by
          intro h; apply hq1_ne_zero
          have : v + ((q + 1 : ℕ) : ZMod p) - v = 0 := by rw [← h]; ring
          rwa [add_sub_cancel_left] at this
        have hne_qq1 : v + (q : ZMod p) ≠ v + ((q + 1 : ℕ) : ZMod p) := by
          intro h
          have heq : (q : ZMod p) = ((q + 1 : ℕ) : ZMod p) := add_left_cancel h
          have := congrArg ZMod.val heq; rw [hq_val, hq1_val] at this; omega
        set f := p - e with hf_def
        have hf_val : (u - v).val = f := by omega
        -- distMod p v (v + ↑q) = q
        have hdist_v_vq : distMod p v (v + (q : ZMod p)) = q := by
          simp only [distMod, show v - (v + (q : ZMod p)) = -(q : ZMod p) from by ring,
            ZMod.neg_val, if_neg hq_ne_zero, hq_val]
          have h_eq : p - (p - q) = q := by omega
          rw [h_eq]; exact min_eq_right (by omega)
        -- distMod p u (v + ↑q) = q - f
        have hdist_u_vq : distMod p u (v + (q : ZMod p)) = q - f := by
          simp only [distMod,
            show u - (v + (q : ZMod p)) = (u - v) + (-(q : ZMod p)) from by ring]
          have : ((u - v) + -(q : ZMod p)).val = p - q + f := by
            rw [ZMod.val_add, hf_val, ZMod.neg_val, if_neg hq_ne_zero, hq_val]
            rw [Nat.mod_eq_of_lt (by omega : f + (p - q) < p)]; omega
          rw [this]
          have h_eq : p - (p - q + f) = q - f := by omega
          rw [h_eq]; exact min_eq_right (by omega)
        have hvq_ne_u : v + (q : ZMod p) ≠ u := by
          intro h; rw [h] at hdist_u_vq
          simp only [distMod, sub_self, ZMod.val_zero] at hdist_u_vq; simp at hdist_u_vq; omega
        have hvq_in : v + (q : ZMod p) ∈ Nu \ G.neighborSet v := by
          rw [diff_explicit v hadj]; simp only [Set.mem_setOf_eq]
          exact ⟨hvq_ne_u, by omega, Or.inr (by omega)⟩
        -- distMod p v (v + ↑(q+1)) ≥ q
        have hdist_v_vq1_ge : distMod p v (v + ((q + 1 : ℕ) : ZMod p)) ≥ q := by
          simp only [distMod,
            show v - (v + ((q + 1 : ℕ) : ZMod p)) = -((q + 1 : ℕ) : ZMod p) from by ring,
            ZMod.neg_val, if_neg hq1_ne_zero, hq1_val]
          have h_eq : p - (p - (q + 1)) = q + 1 := by omega
          rw [h_eq]; exact le_min (by omega) (by omega)
        -- distMod p u (v + ↑(q+1)) = q + 1 - f
        have hdist_u_vq1 : distMod p u (v + ((q + 1 : ℕ) : ZMod p)) = q + 1 - f := by
          simp only [distMod,
            show u - (v + ((q + 1 : ℕ) : ZMod p)) = (u - v) + (-((q + 1 : ℕ) : ZMod p))
              from by ring]
          have : ((u - v) + -((q + 1 : ℕ) : ZMod p)).val = p - (q + 1) + f := by
            rw [ZMod.val_add, hf_val, ZMod.neg_val, if_neg hq1_ne_zero, hq1_val]
            rw [Nat.mod_eq_of_lt (by omega : f + (p - (q + 1)) < p)]; omega
          rw [this]
          have h_eq : p - (p - (q + 1) + f) = q + 1 - f := by omega
          rw [h_eq]; exact min_eq_right (by omega)
        have hvq1_ne_u : v + ((q + 1 : ℕ) : ZMod p) ≠ u := by
          intro h; rw [h] at hdist_u_vq1
          simp only [distMod, sub_self, ZMod.val_zero] at hdist_u_vq1
          simp at hdist_u_vq1; omega
        have hvq1_in : v + ((q + 1 : ℕ) : ZMod p) ∈ Nu \ G.neighborSet v := by
          rw [diff_explicit v hadj]; simp only [Set.mem_setOf_eq]
          exact ⟨hvq1_ne_u, by omega, Or.inr hdist_v_vq1_ge⟩
        -- Conclude ncard ≥ 3
        have hsub : ({v, v + (q : ZMod p), v + ((q + 1 : ℕ) : ZMod p)} : Set (ZMod p)) ⊆
            Nu \ G.neighborSet v := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have h3 : ({v, v + (q : ZMod p), v + ((q + 1 : ℕ) : ZMod p)} : Set (ZMod p)).ncard =
            3 := by
          rw [Set.ncard_eq_toFinset_card']
          simp only [Set.toFinset_insert, Set.toFinset_singleton]
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hne_qq1
          · simp only [Finset.mem_insert, Finset.mem_singleton]
            push_neg; exact ⟨hne_vq, hne_vq1⟩
        linarith [Set.ncard_le_ncard hsub (Set.toFinite _)]
    omega

/-- Automorphisms preserve distance-1 adjacency (when q ≥ 2 and 2q ≤ p).
    Since the distance-1 neighbors of any vertex v are exactly {v-1, v+1},
    and automorphisms map these to distance-1 neighbors of φ(v), we get
    that φ preserves the "distance-1" structure.

    Key insight: Each vertex has exactly 2 distance-1 neighbors, and this property
    is preserved by graph isomorphisms. Since φ is a bijection on vertices that
    preserves adjacency, it must map the 2 dist-1 neighbors of u to the 2 dist-1
    neighbors of φ(u). -/
lemma iso_preserves_dist_one_adj (p q : ℕ) [NeZero p] (hp : 3 ≤ p) (hq : 2 ≤ q) (h2q : 2 * q < p)
    (φ : (fractionGraph p q) ≃g (fractionGraph p q)) (u v : ZMod p)
    (hadj : (fractionGraph p q).Adj u v) (hdist : distMod p u v = 1) :
    (fractionGraph p q).Adj (φ u) (φ v) ∧ distMod p (φ u) (φ v) = 1 := by
  constructor
  · exact fractionGraph_iso_preserves_adj p q φ u v hadj
  · -- Split: for q = 2, all edges have distMod = 1 (trivial).
    -- For q ≥ 3, use common neighborhood characterization.
    by_cases hq2 : q = 2
    · -- q = 2: distMod < 2 and distMod ≥ 1 gives distMod = 1
      have hadj_φ : (fractionGraph p q).Adj (φ u) (φ v) :=
        fractionGraph_iso_preserves_adj p q φ u v hadj
      simp only [fractionGraph] at hadj_φ
      have h_ne := hadj_φ.1
      have h_lt : distMod p (φ u) (φ v) < 2 := by omega
      have h_pos : distMod p (φ u) (φ v) ≠ 0 := by
        simp only [distMod]; intro h0
        rcases Nat.min_eq_zero_iff.mp h0 with h | h
        · exact h_ne (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h))
        · exact absurd (ZMod.val_lt (φ u - φ v)) (by omega)
      omega
    · -- q ≥ 3: use fractionGraph_common_neighbors_characterize_dist
      have hq3 : 3 ≤ q := by omega
      have hadj_φ := fractionGraph_iso_preserves_adj p q φ u v hadj
      -- φ maps common neighborhoods bijectively, preserving ncard
      have ncard_preserved : ∀ (a b : ZMod p),
          ((fractionGraph p q).neighborSet a ∩
           (fractionGraph p q).neighborSet b).ncard =
          ((fractionGraph p q).neighborSet (φ a) ∩
           (fractionGraph p q).neighborSet (φ b)).ncard := by
        intro a b
        have himg : φ '' ((fractionGraph p q).neighborSet a ∩
            (fractionGraph p q).neighborSet b) =
            (fractionGraph p q).neighborSet (φ a) ∩
            (fractionGraph p q).neighborSet (φ b) := by
          ext y
          simp only [Set.mem_image, Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
          constructor
          · rintro ⟨x, ⟨hax, hbx⟩, rfl⟩
            exact ⟨φ.map_rel_iff'.mpr hax, φ.map_rel_iff'.mpr hbx⟩
          · rintro ⟨hay, hby⟩
            refine ⟨φ.symm y, ⟨?_, ?_⟩, by simp⟩
            · have h := φ.symm.map_rel_iff'.mpr hay
              simp only [RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply] at h
              exact h
            · have h := φ.symm.map_rel_iff'.mpr hby
              simp only [RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply] at h
              exact h
        rw [← himg, Set.ncard_image_of_injective _ φ.injective]
      -- Apply characterization backward to φu, φv
      apply (fractionGraph_common_neighbors_characterize_dist p q hp hq3 h2q
        (φ u) (φ v) hadj_φ).mpr
      intro w' hw'_adj hw'_ne
      -- Map w' back through φ⁻¹
      have hw_adj : (fractionGraph p q).Adj u (φ.symm w') := by
        have h := φ.symm.map_rel_iff'.mpr hw'_adj
        simp only [RelIso.coe_fn_toEquiv, RelIso.symm_apply_apply] at h
        exact h
      have hw_ne : φ.symm w' ≠ v := by
        intro h; apply hw'_ne; have := congr_arg φ h; simpa using this
      -- Forward direction gives the comparison for φ⁻¹(w')
      have hfwd := ((fractionGraph_common_neighbors_characterize_dist p q hp hq3 h2q
        u v hadj).mp hdist) (φ.symm w') hw_adj hw_ne
      -- Transfer via ncard preservation
      have h1 := ncard_preserved u v
      have h2 := ncard_preserved u (φ.symm w')
      simp only [RelIso.apply_symm_apply] at h2
      rcases hfwd with hgt | heq
      · left; omega
      · right; omega

/-- φ maps the set {u-1, u+1} to {φ(u)-1, φ(u)+1}.
    This follows from the fact that φ preserves distance-1 adjacency,
    and each vertex has exactly 2 distance-1 neighbors. -/
lemma iso_maps_dist_one_neighbors (p q : ℕ) [NeZero p] (hp : 3 ≤ p) (hq : 2 ≤ q) (h2q : 2 * q < p)
    (φ : (fractionGraph p q) ≃g (fractionGraph p q)) (u : ZMod p) :
    ({φ (u - 1), φ (u + 1)} : Set (ZMod p)) = {φ u - 1, φ u + 1} := by
  -- The key insight is:
  -- 1. φ⁻¹({φ u - 1, φ u + 1}) consists of 2 elements that are neighbors of u
  -- 2. These 2 neighbors must have distMod = 1 from u (shown below)
  -- 3. The only such neighbors are {u-1, u+1}
  -- 4. Therefore φ⁻¹({φ u - 1, φ u + 1}) = {u-1, u+1}
  -- 5. Applying φ gives {φ(u-1), φ(u+1)} = {φu-1, φu+1}
  --
  -- Step 2 is the key: φ⁻¹(φu ± 1) has distMod = 1 from u because:
  -- - φu ± 1 is a neighbor of φu with distMod = 1
  -- - φ⁻¹ is also an automorphism
  -- - The same argument applies, giving a bijection between dist-1 neighbors
  --
  -- Step 1: u-1 and u+1 are dist-1 neighbors of u
  have h_sub_adj : (fractionGraph p q).Adj u (u - 1) := by
    simp only [fractionGraph]; constructor
    · intro h; have : (1 : ZMod p) = 0 := by
        have := congrArg (· + 1) h; simp only [sub_add_cancel] at this
        have h2 : (u + 1) - u = u - u := by rw [this]
        simp only [add_sub_cancel_left, sub_self] at h2; exact h2
      exact zmod_one_ne_zero p (by omega) this
    · rw [distMod_sub_one p (by omega) u]; exact hq
  have h_add_adj : (fractionGraph p q).Adj u (u + 1) := by
    simp only [fractionGraph]; constructor
    · intro h
      have : (1 : ZMod p) = 0 := by
        have h2 : u + 1 - u = u - u := congrArg (· - u) h.symm
        simp only [add_sub_cancel_left, sub_self] at h2; exact h2
      exact zmod_one_ne_zero p (by omega) this
    · rw [distMod_add_one p (by omega) u]; exact hq
  -- Step 2: φ preserves dist-1 adjacency
  have hφ_sub := iso_preserves_dist_one_adj p q hp hq h2q φ u (u - 1) h_sub_adj
    (distMod_sub_one p (by omega) u)
  have hφ_add := iso_preserves_dist_one_adj p q hp hq h2q φ u (u + 1) h_add_adj
    (distMod_add_one p (by omega) u)
  -- Step 3: φ(u-1) and φ(u+1) are dist-1 neighbors of φu, so in {φu-1, φu+1}
  have hφ_sub_mem := distMod_eq_one_imp_adjacent p hp (φ u) (φ (u - 1)) hφ_sub.2
  have hφ_add_mem := distMod_eq_one_imp_adjacent p hp (φ u) (φ (u + 1)) hφ_add.2
  -- Step 4: φ(u-1) ≠ φ(u+1) by injectivity (since u-1 ≠ u+1 as p ≥ 3)
  have hne : φ (u - 1) ≠ φ (u + 1) := by
    intro heq; have := φ.toEquiv.injective heq
    -- u - 1 = u + 1 implies 2 = 0
    have h' : (u - 1) - (u + 1) = 0 := sub_eq_zero.mpr this
    have h'' : (u - 1) - (u + 1) = -2 := by ring
    rw [h''] at h'
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h2z
      have h2_val : (2 : ZMod p).val = 2 := by
        haveI : Fact (2 < p) := ⟨by omega⟩
        exact ZMod.val_natCast_of_lt (by omega : 2 < p)
      rw [h2z] at h2_val; simp only [ZMod.val_zero] at h2_val; omega
    exact h2ne (neg_eq_zero.mp h')
  -- Step 5: Combine membership and distinctness
  rw [Set.pair_eq_pair_iff]
  rcases hφ_sub_mem with hsub | hsub <;> rcases hφ_add_mem with hadd | hadd
  · exact absurd (hsub.trans hadd.symm) hne
  · left; exact ⟨hsub, hadd⟩
  · right; exact ⟨hsub, hadd⟩
  · exact absurd (hsub.trans hadd.symm) hne

/-- Every automorphism of fractionGraph (with coprime
    parameters and q ≥ 2) is a rotation or reflection.
    Note: For q = 1, fractionGraph has no edges,
    so every permutation is an automorphism. -/
theorem fractionGraph_aut_is_rotation_or_reflection (p q : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (φ : (fractionGraph p q) ≃g (fractionGraph p q)) :
    (∃ c : ZMod p, ∀ x : ZMod p, φ x = x + c) ∨
    (∃ c : ZMod p, ∀ x : ZMod p, φ x = c - x) := by
  -- Key insight: knowing φ on {0, 1, -1} determines φ everywhere.
  -- Let c = φ 0. By iso_maps_dist_one_neighbors, {φ(-1), φ(1)} = {c-1, c+1}.
  -- Case 1: φ(1) = c+1, φ(-1) = c-1 → rotation
  -- Case 2: φ(1) = c-1, φ(-1) = c+1 → reflection

  -- Derive strict inequality from coprimality: if 2q = p then q | p, contradicting coprimality
  have h2q_strict : 2 * q < p := by
    rcases h2q.lt_or_eq with h | h
    · exact h
    · exfalso
      have : q ∣ Nat.gcd p q := Nat.dvd_gcd ⟨2, by linarith⟩ dvd_rfl
      rw [hcoprime] at this
      exact absurd (Nat.le_of_dvd one_pos this) (by omega)
    -- Extract the element φ(0) as the center
  let c := φ 0
  -- {φ(-1), φ(1)} = {c-1, c+1}
  have hset : ({φ (-1), φ 1} : Set (ZMod p)) = {c - 1, c + 1} := by
    have h := iso_maps_dist_one_neighbors p q hp hq h2q_strict φ 0
    simp only [zero_sub, zero_add] at h
    exact h
  -- φ(-1) and φ(1) are distinct
  have hdistinct : φ (-1) ≠ φ 1 := by
    intro heq
    have hinj := φ.toEquiv.injective heq
    have h : (-1 : ZMod p) = 1 := hinj
    have h' : (-1 : ZMod p) - 1 = 0 := by rw [h]; ring
    have h'' : (-1 : ZMod p) - 1 = -2 := by ring
    rw [h''] at h'
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h2z
      have h2_val : (2 : ZMod p).val = 2 := by
        haveI : Fact (2 < p) := ⟨by omega⟩
        exact ZMod.val_natCast_of_lt (by omega : 2 < p)
      rw [h2z] at h2_val
      simp only [ZMod.val_zero] at h2_val
      omega
    exact h2ne (neg_eq_zero.mp h')
  -- Also c-1 ≠ c+1
  have hcpm_distinct : c - 1 ≠ c + 1 := by
    intro heq
    have h : (c - 1) - (c + 1) = 0 := by rw [heq]; ring
    have h' : (c - 1) - (c + 1) = -2 := by ring
    rw [h'] at h
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h2z
      have h2_val : (2 : ZMod p).val = 2 := by
        haveI : Fact (2 < p) := ⟨by omega⟩
        exact ZMod.val_natCast_of_lt (by omega : 2 < p)
      rw [h2z] at h2_val
      simp only [ZMod.val_zero] at h2_val
      omega
    exact h2ne (neg_eq_zero.mp h)
  -- From hset and the distinctness, either:
  -- (φ(-1) = c-1 ∧ φ(1) = c+1) or (φ(-1) = c+1 ∧ φ(1) = c-1)
  have hcases : (φ 1 = c + 1 ∧ φ (-1) = c - 1) ∨ (φ 1 = c - 1 ∧ φ (-1) = c + 1) := by
    -- From hset, φ(-1) ∈ {c-1, c+1} and φ(1) ∈ {c-1, c+1}
    have h1 : φ 1 ∈ ({c - 1, c + 1} : Set (ZMod p)) := by
      rw [← hset]; right; rfl
    have h2 : φ (-1) ∈ ({c - 1, c + 1} : Set (ZMod p)) := by
      rw [← hset]; left; rfl
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · -- φ(1) = c-1, φ(-1) = c-1, contradicts hdistinct
      exfalso; exact hdistinct (h2.trans h1.symm)
    · -- φ(1) = c-1, φ(-1) = c+1
      right; exact ⟨h1, h2⟩
    · -- φ(1) = c+1, φ(-1) = c-1
      left; exact ⟨h1, h2⟩
    · -- φ(1) = c+1, φ(-1) = c+1, contradicts hdistinct
      exfalso; exact hdistinct (h2.trans h1.symm)
  -- Proceed to the two main cases
  rcases hcases with ⟨hφ1, hφn1⟩ | ⟨hφ1, hφn1⟩
  · -- Case: φ(1) = c+1, φ(-1) = c-1 → rotation by c
    left
    use c
    -- Need to show: ∀ x, φ x = x + c
    --
    -- Strategy: Define ψ = (rotation by -c) ∘ φ, an automorphism with ψ(0)=0, ψ(1)=1, ψ(-1)=-1.
    -- Show ψ = id by induction using iso_maps_dist_one_neighbors.
    --
    -- Key insight: From iso_maps_dist_one_neighbors, for any u:
    --   {ψ(u-1), ψ(u+1)} = {ψ(u)-1, ψ(u)+1}
    -- If ψ(u) = u and ψ(u-1) = u-1, then ψ(u+1) ∈ {u-1, u+1} and ψ(u+1) ≠ ψ(u-1) = u-1,
    -- so ψ(u+1) = u+1.
    --
    -- Starting from ψ(0)=0, ψ(1)=1, ψ(-1)=-1, we can propagate to all of ZMod p.
    -- Propagation via iso_maps_dist_one_neighbors: φ maps dist-1 neighbors to dist-1 neighbors
    have hprop : ∀ u : ZMod p,
        ({φ (u - 1), φ (u + 1)} : Set (ZMod p)) = {φ u - 1, φ u + 1} :=
      iso_maps_dist_one_neighbors p q hp hq h2q_strict φ
    -- Helper: 2 ≠ 0 in ZMod p (from hcpm_distinct)
    have h2ne : ∀ a : ZMod p, a - 1 ≠ a + 1 := by
      intro a heq; apply hcpm_distinct
      have h2z : (2 : ZMod p) = 0 := by
        have h' : a - 1 - (a + 1) = 0 := sub_eq_zero.mpr heq
        have h'' : a - 1 - (a + 1) = -2 := by ring
        rw [h''] at h'; exact neg_eq_zero.mp h'
      exact sub_eq_zero.mp (by rw [show (c - 1) - (c + 1) = -2 from by ring,
        neg_eq_zero.mpr h2z])
    -- Strong induction: ∀ n : ℕ, φ ↑n = ↑n + c
    intro x
    suffices h : ∀ n : ℕ, φ (↑n : ZMod p) = ↑n + c by
      have := h (ZMod.val x); rwa [ZMod.natCast_zmod_val] at this
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      match n with
      | 0 =>
        simp only [Nat.cast_zero]
        change c = 0 + c; ring
      | 1 =>
        rw [show (↑(1 : ℕ) : ZMod p) = 1 from Nat.cast_one, hφ1]; ring
      | Nat.succ (Nat.succ m) =>
        have ihm : φ (↑m : ZMod p) = ↑m + c := ih m (by omega)
        have ihm1 : φ (↑(m + 1) : ZMod p) = ↑(m + 1) + c := ih (m + 1) (by omega)
        have hset := hprop (↑(m + 1) : ZMod p)
        rw [show (↑(m + 1) : ZMod p) - 1 = ↑m from by
              simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right],
            show (↑(m + 1) : ZMod p) + 1 = ↑(m + 2) from by
              simp only [Nat.cast_add, Nat.cast_one]; ring,
            ihm, ihm1] at hset
        rcases Set.pair_eq_pair_iff.mp hset with ⟨_, h2⟩ | ⟨h1, _⟩
        · change φ (↑(m + 2) : ZMod p) = ↑(m + 2) + c
          rw [h2]; simp only [Nat.cast_add, Nat.cast_one]; ring
        · exfalso; apply h2ne (↑(m + 1) + c)
          have : (↑m : ZMod p) + c = ↑(m + 1) + c - 1 := by
            simp only [Nat.cast_add, Nat.cast_one]; ring
          rw [← this, h1]
  · -- Case: φ(1) = c-1, φ(-1) = c+1 → reflection about c/2
    right
    use c
    -- Need to show: ∀ x, φ x = c - x
    --
    -- Similar strategy: Define ψ = (reflection about 0) ∘ (rotation by -c) ∘ φ.
    -- Then ψ(0) = 0, ψ(1) = 1, ψ(-1) = -1.
    -- Show ψ = id, which gives φ(x) = c - x.
    -- Same propagation and 2≠0 helpers as rotation case
    have hprop : ∀ u : ZMod p,
        ({φ (u - 1), φ (u + 1)} : Set (ZMod p)) = {φ u - 1, φ u + 1} :=
      iso_maps_dist_one_neighbors p q hp hq h2q_strict φ
    have h2ne : ∀ a : ZMod p, a - 1 ≠ a + 1 := by
      intro a heq; apply hcpm_distinct
      have h2z : (2 : ZMod p) = 0 := by
        have h' : a - 1 - (a + 1) = 0 := sub_eq_zero.mpr heq
        have h'' : a - 1 - (a + 1) = -2 := by ring
        rw [h''] at h'; exact neg_eq_zero.mp h'
      exact sub_eq_zero.mp (by rw [show (c - 1) - (c + 1) = -2 from by ring,
        neg_eq_zero.mpr h2z])
    -- Strong induction: ∀ n : ℕ, φ ↑n = c - ↑n
    intro x
    suffices h : ∀ n : ℕ, φ (↑n : ZMod p) = c - ↑n by
      have := h (ZMod.val x); rwa [ZMod.natCast_zmod_val] at this
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      match n with
      | 0 =>
        simp only [Nat.cast_zero]
        change c = c - 0; ring
      | 1 =>
        rw [show (↑(1 : ℕ) : ZMod p) = 1 from Nat.cast_one]; exact hφ1
      | Nat.succ (Nat.succ m) =>
        have ihm : φ (↑m : ZMod p) = c - ↑m := ih m (by omega)
        have ihm1 : φ (↑(m + 1) : ZMod p) = c - ↑(m + 1) := ih (m + 1) (by omega)
        have hset := hprop (↑(m + 1) : ZMod p)
        rw [show (↑(m + 1) : ZMod p) - 1 = ↑m from by
              simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right],
            show (↑(m + 1) : ZMod p) + 1 = ↑(m + 2) from by
              simp only [Nat.cast_add, Nat.cast_one]; ring,
            ihm, ihm1] at hset
        rcases Set.pair_eq_pair_iff.mp hset with ⟨h1, _⟩ | ⟨_, h2⟩
        · exfalso; apply h2ne (c - ↑(m + 1))
          have : c - (↑m : ZMod p) = c - ↑(m + 1) + 1 := by
            simp only [Nat.cast_add, Nat.cast_one]; ring
          rw [← this, h1]
        · change φ (↑(m + 2) : ZMod p) = c - ↑(m + 2)
          rw [h2]; simp only [Nat.cast_add, Nat.cast_one]; ring

/-- finZModEquiv respects addition: finZModEquiv p (a + b) = finZModEquiv p a + finZModEquiv p b -/
private lemma finZModEquiv_add (p : ℕ) [NeZero p] (a b : Fin p) :
    finZModEquiv p (a + b) = finZModEquiv p a + finZModEquiv p b := by
  simp only [finZModEquiv, Equiv.coe_fn_mk, Fin.val_add, ZMod.natCast_mod, Nat.cast_add]

/-- finZModEquiv respects subtraction -/
private lemma finZModEquiv_sub (p : ℕ) [NeZero p] (a b : Fin p) :
    finZModEquiv p (a - b) = finZModEquiv p a - finZModEquiv p b := by
  simp only [finZModEquiv, Equiv.coe_fn_mk, Fin.val_sub, ZMod.natCast_mod]
  rw [Nat.cast_add, Nat.cast_sub (le_of_lt b.isLt), ZMod.natCast_self]
  ring

/-- Main theorem: Isomorphisms from convex-round graphs to fraction graphs
    preserve cyclic order (up to rotation/reflection).

    If G = fractionGraph n q (mapped to Fin n) and φ is an automorphism,
    then φ either preserves or reverses the cyclic order.
    Note: This does NOT hold when G is a circularCliqueGraph (the isomorphism may be
    multiplication by a non-trivial unit, e.g. for n=5, q=2, d=2). -/
theorem convexRound_iso_preserves_cyclic_order (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : IsConvexRoundEnum n G)
    (hnotBip : ¬G.IsBipartite)
    (hnoNested : ∀ i : Fin n, ¬(G.neighborSet i ⊆ G.neighborSet (i + 1)) ∧
                              ¬(G.neighborSet (i + 1) ⊆ G.neighborSet i))
    (q : ℕ) (hq : 0 < q) (h2q : 2 * q ≤ n) (hcoprime : Nat.Coprime n q)
    (heq_frac : G = (fractionGraph n q).map (zmodFinEquiv n).toEmbedding)
    (φ : G ≃g (fractionGraph n q).map (zmodFinEquiv n).toEmbedding) :
    (∃ c : Fin n, ∀ i : Fin n, φ i = i + c) ∨
    (∃ c : Fin n, ∀ i : Fin n, φ i = c - i) := by
  -- G = fractionGraph n q (mapped) is given directly; substitute
  subst heq_frac
  -- φ is now a self-isomorphism: φ : F(n,q).map(zfe) ≃g F(n,q).map(zfe)
  -- Step 2: Derive q ≥ 2 (q = 1 gives edgeless graph, which is bipartite)
  have hq2 : 2 ≤ q := by
    by_contra hlt; push_neg at hlt; interval_cases q
    -- Only case: q = 1 (since 0 < q and q < 2)
    -- fractionGraph n 1 has no edges (distMod ≥ 1 for distinct elements)
    apply hnotBip
    have hempty : ∀ v w : Fin n,
        ¬((fractionGraph n 1).map (zmodFinEquiv n).toEmbedding).Adj v w := by
      intro v w hvw
      rw [mapped_fractionGraph_adj] at hvw
      -- hvw : v ≠ w ∧ distMod n (fze v) (fze w) < 1
      have h0 : distMod n (finZModEquiv n v) (finZModEquiv n w) = 0 := Nat.lt_one_iff.mp hvw.2
      simp only [distMod, Nat.min_def] at h0
      split_ifs at h0 with hle
      · exact hvw.1 ((finZModEquiv n).injective
          (by rw [← sub_eq_zero]; exact (ZMod.val_eq_zero _).mp h0))
      · exact absurd h0 (by have := ZMod.val_lt (finZModEquiv n v - finZModEquiv n w); omega)
    exact ⟨⟨fun _ => 0, fun hvw => absurd hvw (hempty _ _)⟩⟩
  -- Step 3: Construct automorphism of F(n,q) on ZMod n
  let α : (fractionGraph n q) ≃g (fractionGraph n q) :=
    ((SimpleGraph.Iso.map (zmodFinEquiv n) (fractionGraph n q)).trans φ).trans
      (SimpleGraph.Iso.map (zmodFinEquiv n) (fractionGraph n q)).symm
  -- Step 4: Apply the automorphism classification
  have haut := fractionGraph_aut_is_rotation_or_reflection n q hn hq2 h2q hcoprime α
  -- Step 5: Convert from ZMod rotation/reflection to Fin rotation/reflection
  rcases haut with ⟨c, hrot⟩ | ⟨c, href⟩
  · -- Rotation case: α(x) = x + c for all x : ZMod n
    left
    use (zmodFinEquiv n) c
    intro i
    have hα : finZModEquiv n (φ (zmodFinEquiv n (finZModEquiv n i))) =
              finZModEquiv n i + c := by
      have := hrot (finZModEquiv n i)
      simp only [α, RelIso.trans_apply, SimpleGraph.Iso.map_apply,
                  SimpleGraph.Iso.map_symm_apply] at this
      exact this
    simp only [zmodFinEquiv, Equiv.symm_apply_apply] at hα
    apply (finZModEquiv n).injective
    -- v4.29: rewriting hα directly fails (instance mismatch on the LHS coercion).
    -- Compute the RHS first, then close with hα.
    rw [show finZModEquiv n (i + (zmodFinEquiv n) c) = (finZModEquiv n) i + c from by
      rw [finZModEquiv_add]; simp [finZModEquiv, zmodFinEquiv]]
    exact hα
  · -- Reflection case: α(x) = c - x for all x : ZMod n
    right
    use (zmodFinEquiv n) c
    intro i
    have hα : finZModEquiv n (φ (zmodFinEquiv n (finZModEquiv n i))) =
              c - finZModEquiv n i := by
      have := href (finZModEquiv n i)
      simp only [α, RelIso.trans_apply, SimpleGraph.Iso.map_apply,
                  SimpleGraph.Iso.map_symm_apply] at this
      exact this
    simp only [zmodFinEquiv, Equiv.symm_apply_apply] at hα
    apply (finZModEquiv n).injective
    rw [show finZModEquiv n ((zmodFinEquiv n) c - i) = c - (finZModEquiv n) i from by
      rw [finZModEquiv_sub]; simp [finZModEquiv, zmodFinEquiv]]
    exact hα

/-- cyclicDist from a to a - 1 is n - 1 -/
private lemma cyclicDist_pred (n : ℕ) [NeZero n] (hn : 2 ≤ n) (a : Fin n) :
    cyclicDist n a (a - 1) = n - 1 := by
  simp only [cyclicDist, Fin.val_sub]
  have h1v : (1 : Fin n).val = 1 := by
    change 1 % n = 1; exact Nat.mod_eq_of_lt (by omega)
  rw [h1v]
  have hav := a.isLt
  by_cases ha : a.val = 0
  · rw [ha, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; simp
  · have hge : a.val ≥ 1 := Nat.pos_of_ne_zero ha
    have hmod : (n - 1 + a.val) % n = a.val - 1 := by
      have h1 : n - 1 + a.val = n + (a.val - 1) := by omega
      rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have : ¬(a.val ≤ a.val - 1) := by omega
    rw [if_neg this]
    omega

/-- cyclicDist from a to a - 2 is n - 2 for n ≥ 3 -/
private lemma cyclicDist_pred_pred (n : ℕ) [NeZero n] (hn : 3 ≤ n) (a : Fin n) :
    cyclicDist n a (a - 2) = n - 2 := by
  simp only [cyclicDist, Fin.val_sub]
  have h2v : (2 : Fin n).val = 2 := by
    change 2 % n = 2; exact Nat.mod_eq_of_lt (by omega)
  rw [h2v]
  have hav := a.isLt
  by_cases ha : a.val ≤ 1
  · have hmod : (n - 2 + a.val) % n = n - 2 + a.val := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have : a.val ≤ n - 2 + a.val := by omega
    rw [if_pos this]
    omega
  · have hge : a.val ≥ 2 := by omega
    have hmod : (n - 2 + a.val) % n = a.val - 2 := by
      have h1 : n - 2 + a.val = n + (a.val - 2) := by omega
      rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have : ¬(a.val ≤ a.val - 2) := by omega
    rw [if_neg this]
    omega

/-! ### Section 7: Arc Containment Theorem -/

/-- The key arc containment result expressed in ZMod terms.

    If φ : G ≃g fractionGraph p q (where G is convex-round on Fin p),
    and φ maps i1 → v-1, i_p → v, i2 → v+1 (consecutive in ZMod p),
    then there is no element i ∈ Fin p with i strictly between i1 and i_p
    (in the cyclic order on Fin p that matches ZMod p via φ).

    This is the abstract form of the arc containment needed in SelfCohom.lean. -/
theorem iso_fractionGraph_no_element_between (p q : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hq : 0 < q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (G : SimpleGraph (Fin p)) (hG : IsConvexRoundEnum p G)
    (hnotBip : ¬G.IsBipartite)
    (hnoNested : ∀ i : Fin p, ¬(G.neighborSet i ⊆ G.neighborSet (i + 1)) ∧
                              ¬(G.neighborSet (i + 1) ⊆ G.neighborSet i))
    (heq_frac : G = (fractionGraph p q).map (zmodFinEquiv p).toEmbedding)
    (φ : G ≃g (fractionGraph p q).map (zmodFinEquiv p).toEmbedding)
    (i1 i_p i2 : Fin p)
    (_hi1_ne_ip : i1 ≠ i_p) (_hip_ne_i2 : i_p ≠ i2) (_hi1_ne_i2 : i1 ≠ i2)
    (v : ZMod p)
    (hφi1 : (finZModEquiv p) (φ i1) = v - 1)
    (hφip : (finZModEquiv p) (φ i_p) = v)
    (hφi2 : (finZModEquiv p) (φ i2) = v + 1) :
    -- No i can be strictly between i1 and i_p (while i_p is between i1 and i2)
    ∀ i : Fin p, i ≠ i1 → i ≠ i2 →
      ¬IsCyclicBetween p i i_p i1 i2 := by
  intro i hi_ne_i1 hi_ne_i2
  have horder :=
    convexRound_iso_preserves_cyclic_order p hp G hG
      hnotBip hnoNested q hq h2q hcoprime heq_frac φ
  have hp2 : 2 ≤ p := by omega
  intro ⟨hlt1, hlt2⟩
  rcases horder with ⟨c, hrot⟩ | ⟨c, href⟩
  · -- Rotation case: φ j = j + c for all j
    -- Derive i_p = i1 + 1
    have hφi1' : finZModEquiv p (i1 + c) = v - 1 := by rw [← hrot]; exact hφi1
    have hφip' : finZModEquiv p (i_p + c) = v := by rw [← hrot]; exact hφip
    rw [finZModEquiv_add] at hφi1' hφip'
    -- finZModEquiv p i_p + finZModEquiv p c = v
    -- finZModEquiv p i1 + finZModEquiv p c = v - 1
    -- So finZModEquiv p i_p = finZModEquiv p i1 + 1
    have hip_eq : i_p = i1 + 1 := by
      apply (finZModEquiv p).injective
      rw [finZModEquiv_add]
      have hone : finZModEquiv p (1 : Fin p) = 1 := by simp [finZModEquiv]
      rw [hone]
      linear_combination hφip' - hφi1'
    -- cyclicDist p i1 (i1 + 1) = 1
    rw [hip_eq] at hlt1
    rw [cyclicDist_succ p hp2 i1] at hlt1
    -- hlt1 : cyclicDist p i1 i < 1, so cyclicDist p i1 i = 0, so i = i1
    exact hi_ne_i1 ((cyclicDist_eq_zero_iff p i1 i).mp (by omega)).symm
  · -- Reflection case: φ j = c - j for all j
    have hφi1' : finZModEquiv p (c - i1) = v - 1 := by rw [← href]; exact hφi1
    have hφip' : finZModEquiv p (c - i_p) = v := by rw [← href]; exact hφip
    have hφi2' : finZModEquiv p (c - i2) = v + 1 := by rw [← href]; exact hφi2
    rw [finZModEquiv_sub] at hφi1' hφip' hφi2'
    -- finZModEquiv p c - finZModEquiv p i_p = v
    -- finZModEquiv p c - finZModEquiv p i1  = v - 1
    -- finZModEquiv p c - finZModEquiv p i2  = v + 1
    -- So i1 = i_p + 1 (i.e., i_p = i1 - 1) and i1 = i2 + 2 (i.e., i2 = i1 - 2)
    have hone : finZModEquiv p (1 : Fin p) = 1 := by simp [finZModEquiv]
    have hip_eq : i_p = i1 - 1 := by
      have h1 : i1 = i_p + 1 := by
        apply (finZModEquiv p).injective
        rw [finZModEquiv_add, hone]
        linear_combination hφip' - hφi1'
      calc i_p = i_p + 1 - 1 := by simp [add_sub_cancel_right]
        _ = i1 - 1 := by rw [← h1]
    have hi2_eq : i2 = i1 - 2 := by
      have h1 : i1 = i2 + 2 := by
        apply (finZModEquiv p).injective
        rw [finZModEquiv_add]
        have htwo : finZModEquiv p (2 : Fin p) = 2 := by simp [finZModEquiv]
        rw [htwo]
        linear_combination hφi2' - hφi1'
      calc i2 = i2 + 2 - 2 := by simp [add_sub_cancel_right]
        _ = i1 - 2 := by rw [← h1]
    -- cyclicDist p i1 (i1 - 1) = p - 1  and  cyclicDist p i1 (i1 - 2) = p - 2
    rw [hip_eq, hi2_eq] at hlt2
    rw [cyclicDist_pred p hp2 i1, cyclicDist_pred_pred p hp i1] at hlt2
    omega

/-- Corollary: The arc containment for an arbitrary graph G on Circle
    that has an isomorphism to fractionGraph.

    This is the version that will be used in SelfCohom.lean.
    The connection to Circle's cyclic order (repFrom) is established there. -/
theorem arc_containment_via_iso (p q : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hq : 0 < q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    {V : Type*} (G : SimpleGraph V)
    (e : V ≃ Fin p) -- enumeration of V by Fin p
    (hG : IsConvexRoundEnum p (G.map e.toEmbedding))
    (hnotBip : ¬(G.map e.toEmbedding).IsBipartite)
    (hnoNested : ∀ i : Fin p, ¬((G.map e.toEmbedding).neighborSet i ⊆
                                 (G.map e.toEmbedding).neighborSet (i + 1)) ∧
                              ¬((G.map e.toEmbedding).neighborSet (i + 1) ⊆
                                 (G.map e.toEmbedding).neighborSet i))
    (heq_frac_mapped : G.map e.toEmbedding =
        (fractionGraph p q).map (zmodFinEquiv p).toEmbedding)
    (φ : G ≃g fractionGraph p q)
    (t1 t_p t2 : V)
    (ht1_ne_tp : t1 ≠ t_p) (htp_ne_t2 : t_p ≠ t2) (ht1_ne_t2 : t1 ≠ t2)
    (v : ZMod p)
    (hφt1 : φ t1 = v - 1)
    (hφtp : φ t_p = v)
    (hφt2 : φ t2 = v + 1) :
    -- No t can be strictly between e(t1) and e(t_p) in Fin p cyclic order
    -- while e(t_p) is between e(t1) and e(t2)
    ∀ t : V, t ≠ t1 → t ≠ t2 →
      ¬IsCyclicBetween p (e t) (e t_p) (e t1) (e t2) := by
  intro t ht_ne_t1 ht_ne_t2
  -- Construct the composed isomorphism G.map e ≃g fractionGraph.map (zmodFinEquiv)
  let ψ : (G.map e.toEmbedding) ≃g
      ((fractionGraph p q).map (zmodFinEquiv p).toEmbedding) :=
    ((SimpleGraph.Iso.map e G).symm.trans φ).trans
      (SimpleGraph.Iso.map (zmodFinEquiv p) (fractionGraph p q))
  -- Key: finZModEquiv p (ψ (e s)) = φ s for all s
  have hψ : ∀ s : V, finZModEquiv p (ψ (e s)) = φ s := by
    intro s
    simp only [ψ, RelIso.trans_apply, SimpleGraph.Iso.map_symm_apply,
      Equiv.symm_apply_apply, SimpleGraph.Iso.map_apply]
    simp [finZModEquiv, zmodFinEquiv]
  exact iso_fractionGraph_no_element_between p q hp hq h2q hcoprime
    (G.map e.toEmbedding) hG hnotBip hnoNested heq_frac_mapped ψ (e t1) (e t_p) (e t2)
    (e.injective.ne ht1_ne_tp) (e.injective.ne htp_ne_t2) (e.injective.ne ht1_ne_t2)
    v ((hψ t1).trans hφt1) ((hψ t_p).trans hφtp) ((hψ t2).trans hφt2)
    (e t) (e.injective.ne ht_ne_t1) (e.injective.ne ht_ne_t2)

end ConvexRound
