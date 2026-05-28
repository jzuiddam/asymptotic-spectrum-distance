/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Lemmas
import AsymptoticSpectrumDistance.Prerequisites.DistMod

/-!
# Fraction Graphs

This module is the single home of the `fractionGraph` family used throughout
the project:

* `FractionGraphBasic.fractionGraph p q` — the fraction graph E_{p/q}
* `FractionGraphBasic.fractionGraph_adj_add_left` — translation invariance
* `FractionGraphBasic.fractionGraph_scalingMap` — the scaling map
  ZMod a → ZMod c used in the cohomomorphism construction
* `FractionGraphBasic.fractionGraph_scalingMap_isCohom` — the scaling map is a
  cohomomorphism when a/b ≤ c/d
* `FractionGraphBasic.fractionGraph_cohomomorphism` — existence of a
  cohomomorphism E_{a/b} → E_{c/d} when a/b ≤ c/d

The `distMod` family used by these definitions lives in `Prerequisites/DistMod.lean`
(in the same `FractionGraphBasic` namespace).

This file also collects ratio-level properties (vertex-transitivity,
ratio-equality, edgelessness) that are used downstream by the universality
theorem.
-/

namespace FractionGraphBasic

/-! ## Section 1: Fraction Graph Definition -/

/-- The fraction graph E_{p/q} on vertex set ZMod p.
    Two distinct vertices are adjacent iff their distance mod p is < q. -/
def fractionGraph (p q : ℕ) [hp : NeZero p] : SimpleGraph (ZMod p) where
  Adj u v := u ≠ v ∧ distMod p u v < q
  symm := by
    intro u v ⟨hne, hdist⟩
    exact ⟨hne.symm, distMod_comm p u v ▸ hdist⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => (hne rfl).elim⟩

notation "E[" p "/" q "]" => fractionGraph p q

/-- Canonical decidability instance for `(fractionGraph p q).Adj`.

Adjacency is `u ≠ v ∧ distMod p u v < q`, and both conjuncts are decidable. -/
instance fractionGraph_adj_decidable (p q : ℕ) [NeZero p] :
    DecidableRel (fractionGraph p q).Adj := fun u v => by
  change Decidable (u ≠ v ∧ distMod p u v < q)
  exact instDecidableAnd

/-- Adjacency in fraction graph is translation invariant -/
lemma fractionGraph_adj_add_left (p q : ℕ) [NeZero p] (c u v : ZMod p) :
    (fractionGraph p q).Adj (c + u) (c + v) ↔ (fractionGraph p q).Adj u v := by
  simp only [fractionGraph, distMod_add_left, ne_eq, add_left_cancel_iff]

/-! ## Section 2: The scaling map -/

/-- The scaling function from ZMod a to ZMod c: f(x) = x.val * c / a -/
def fractionGraph_scalingMap (a c : ℕ) [NeZero a] [NeZero c] : ZMod a → ZMod c :=
  fun x => (x.val * c / a : ℕ)

/-! ### Helper lemmas for fraction graph cohomomorphism -/

/-- Division distributes over subtraction with inequality: (x-y)*c/a ≤ x*c/a - y*c/a -/
private lemma div_sub_le (a c x y : ℕ) (_ha : 0 < a) (hle : y ≤ x) :
    (x - y) * c / a ≤ x * c / a - y * c / a := by
  have hsum : (x - y) * c + y * c = x * c := by rw [← Nat.add_mul, Nat.sub_add_cancel hle]
  have hdiv := Nat.add_div_le_add_div ((x - y) * c) (y * c) a
  rw [hsum] at hdiv
  have hmono : y * c / a ≤ x * c / a := Nat.div_le_div_right (Nat.mul_le_mul_right c hle)
  omega

/-- Key bound: (a-b)*c/a ≤ c-d when a*d ≤ b*c -/
private lemma sub_mul_div_le (a b c d : ℕ) (ha : 0 < a) (had_le_bc : a * d ≤ b * c) :
    (a - b) * c / a ≤ c - d := by
  have h1 : (a - b) * c ≤ a * c - a * d := by
    rw [Nat.sub_mul]; exact Nat.sub_le_sub_left had_le_bc _
  have h2 : a * c - a * d = a * (c - d) := (Nat.mul_sub a c d).symm
  calc (a - b) * c / a ≤ (a * (c - d)) / a := Nat.div_le_div_right (h1.trans_eq h2)
    _ = c - d := Nat.mul_div_cancel_left (c - d) ha

/-- Strict version: when remainder > 0, we get k*c/a + 1 ≤ c-d -/
private lemma div_add_one_le_of_rem_pos (a b c d k : ℕ) (ha : 0 < a) (hc : 0 < c)
    (had_le_bc : a * d ≤ b * c) (hk_le : k ≤ a - b) (hrem_pos : 0 < k * c % a) :
    k * c / a + 1 ≤ c - d := by
  by_cases hk_lt : k < a - b
  · -- k < a - b case
    have h5 : k * c < (a - b) * c := Nat.mul_lt_mul_of_pos_right hk_lt hc
    have h6 : k * c / a ≤ (a - b) * c / a := Nat.div_le_div_right (le_of_lt h5)
    by_cases heq : k * c / a = (a - b) * c / a
    · -- Same quotient: (a-b)*c % a > k*c % a ≥ 1, so (a-b)*c/a < c-d
      have hab_rem_pos : 0 < (a - b) * c % a := by
        have hmod_lt : k * c % a < (a - b) * c % a := by
          have h7 : k * c = a * (k * c / a) + k * c % a := (Nat.div_add_mod _ a).symm
          have h8 : (a - b) * c = a * ((a - b) * c / a) + (a - b) * c % a :=
            (Nat.div_add_mod _ a).symm
          rw [heq.symm] at h8; omega
        omega
      have hab_strict : (a - b) * c / a < c - d := by
        have h12 : (a - b) * c ≤ a * (c - d) := by
          have : (a - b) * c ≤ a * c - a * d := by
            rw [Nat.sub_mul]; exact Nat.sub_le_sub_left had_le_bc _
          calc (a - b) * c ≤ a * c - a * d := this
            _ = a * (c - d) := (Nat.mul_sub a c d).symm
        have h22 : (a - b) * c = a * ((a - b) * c / a) + (a - b) * c % a :=
          (Nat.div_add_mod _ a).symm
        have h23 : a * ((a - b) * c / a) < a * (c - d) := by omega
        exact Nat.lt_of_mul_lt_mul_left h23
      omega
    · -- Different quotient: k*c/a < (a-b)*c/a ≤ c-d
      have h7 : k * c / a < (a - b) * c / a := Nat.lt_of_le_of_ne h6 heq
      have hab_le := sub_mul_div_le a b c d ha had_le_bc
      omega
  · -- k = a - b case
    push_neg at hk_lt
    have hk_eq : k = a - b := Nat.le_antisymm hk_le hk_lt
    rw [hk_eq] at hrem_pos ⊢
    have hab_strict : (a - b) * c / a < c - d := by
      have h19 : (a - b) * c ≤ a * (c - d) := by
        have : (a - b) * c ≤ a * c - a * d := by
          rw [Nat.sub_mul]; exact Nat.sub_le_sub_left had_le_bc _
        calc (a - b) * c ≤ a * c - a * d := this
          _ = a * (c - d) := (Nat.mul_sub a c d).symm
      have h22 : (a - b) * c = a * ((a - b) * c / a) + (a - b) * c % a :=
        (Nat.div_add_mod _ a).symm
      have h23 : a * ((a - b) * c / a) < a * (c - d) := by omega
      exact Nat.lt_of_mul_lt_mul_left h23
    omega

/-- The scaling map is a cohomomorphism from E_{a/b} to E_{c/d} when a/b ≤ c/d.

    A cohomomorphism maps distinct non-adjacent vertices to distinct non-adjacent vertices,
    i.e., it maps independent sets injectively to independent sets.

    The cohomomorphism is the scaling function f(x) = ⌊x * c / a⌋ = x * c / a (nat div).
-/
theorem fractionGraph_scalingMap_isCohom (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hab_le_cd : (a : ℚ) / b ≤ (c : ℚ) / d) :
    ∀ u v, u ≠ v → ¬(fractionGraph a b).Adj u v →
      fractionGraph_scalingMap a c u ≠ fractionGraph_scalingMap a c v ∧
      ¬(fractionGraph c d).Adj (fractionGraph_scalingMap a c u)
        (fractionGraph_scalingMap a c v) := by
  have ha_pos : 0 < a := NeZero.pos a
  have hc_pos : 0 < c := NeZero.pos c
  -- Key inequality from a/b ≤ c/d: a * d ≤ b * c
  have had_le_bc : a * d ≤ b * c := by
    by_cases hd : d = 0
    · simp only [hd, Nat.cast_zero, div_zero] at hab_le_cd
      have hpos : 0 < (a : ℚ) / b := by positivity
      linarith
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      rw [div_le_div_iff₀ (by positivity : (0:ℚ) < b) (by positivity : (0:ℚ) < d)] at hab_le_cd
      have := (mod_cast hab_le_cd : a * d ≤ c * b); linarith
  -- Key: x.val * c / a < c for any x : ZMod a
  have hf_lt : ∀ x : ZMod a, x.val * c / a < c := fun x =>
    calc x.val * c / a < (a * c) / a :=
        Nat.div_lt_div_of_lt_of_dvd (dvd_mul_right a c)
          (Nat.mul_lt_mul_of_pos_right x.val_lt hc_pos)
      _ = c := Nat.mul_div_cancel_left c ha_pos
  let f := fractionGraph_scalingMap a c
  have hf_val : ∀ x : ZMod a, (f x).val = x.val * c / a := fun x =>
    ZMod.val_cast_of_lt (hf_lt x)
  intro u v huv hnadj
  simp only [fractionGraph, not_and, not_lt] at hnadj
  have hdist_ge_b : distMod a u v ≥ b := hnadj huv
  constructor
  · -- Part 1: f u ≠ f v (injectivity on non-adjacent pairs)
    intro hfeq
    have hval_eq : u.val * c / a = v.val * c / a := by
      rw [← hf_val u, ← hf_val v]; exact congrArg ZMod.val hfeq
    by_cases hd : d = 0
    · simp only [hd, Nat.cast_zero, div_zero] at hab_le_cd
      have hpos : 0 < (a : ℚ) / b := by positivity
      linarith
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    have ha_le_bc : a ≤ b * c := calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * d := Nat.mul_le_mul_left a hd_pos
      _ ≤ b * c := had_le_bc
    -- If f(u) = f(v), they're in same bucket, so |u.val - v.val| * c < a
    -- Since a ≤ bc, |u.val - v.val| < b, contradicting distMod ≥ b
    -- Case split on u.val vs v.val ordering
    rcases le_or_gt u.val v.val with huv_val | huv_val
    · -- Case u.val ≤ v.val
      have hdiff_lt : (v.val - u.val) * c < a := by
        by_contra hge; push_neg at hge
        have hvc : u.val * c + a ≤ v.val * c := by
          have : (v.val - u.val) * c = v.val * c - u.val * c := Nat.sub_mul v.val u.val c; omega
        have hdiv : u.val * c / a < v.val * c / a := by
          have h1 : u.val * c / a + 1 = (u.val * c + a) / a :=
            (Nat.add_div_right (u.val * c) ha_pos).symm
          have h2 : (u.val * c + a) / a ≤ v.val * c / a := Nat.div_le_div_right hvc
          omega
        omega
      have hdiff_lt_b : v.val - u.val < b := by
        by_contra hge; push_neg at hge
        have : b * c ≤ (v.val - u.val) * c := Nat.mul_le_mul_right c hge; omega
      have hdist : distMod a u v ≤ v.val - u.val := by
        simp only [distMod]
        by_cases heq : u.val = v.val
        · exact absurd (ZMod.val_injective a heq) huv
        have hlt : u.val < v.val := lt_of_le_of_ne huv_val heq
        have hsub : (u - v).val = a - (v.val - u.val) := by
          have heq' : u - v = -(v - u) := by ring
          rw [heq', ZMod.neg_val, if_neg (sub_ne_zero.mpr huv.symm)]
          congr 1
          conv_lhs => rw [← ZMod.natCast_zmod_val v, ← ZMod.natCast_zmod_val u]
          rw [ZMod.val_sub (by simp only [ZMod.val_natCast_of_lt u.val_lt,
            ZMod.val_natCast_of_lt v.val_lt]; exact le_of_lt hlt)]
          simp only [ZMod.val_natCast_of_lt v.val_lt, ZMod.val_natCast_of_lt u.val_lt]
        rw [hsub]; apply min_le_of_right_le; omega
      exact absurd hdist_ge_b (not_le.mpr (lt_of_le_of_lt hdist hdiff_lt_b))
    · -- Case v.val < u.val (symmetric)
      have hdiff_lt : (u.val - v.val) * c < a := by
        by_contra hge; push_neg at hge
        have huc : v.val * c + a ≤ u.val * c := by
          have : (u.val - v.val) * c = u.val * c - v.val * c := Nat.sub_mul u.val v.val c; omega
        have hdiv : v.val * c / a < u.val * c / a := by
          have h1 : v.val * c / a + 1 = (v.val * c + a) / a :=
            (Nat.add_div_right (v.val * c) ha_pos).symm
          have h2 : (v.val * c + a) / a ≤ u.val * c / a := Nat.div_le_div_right huc
          omega
        omega
      have hdiff_lt_b : u.val - v.val < b := by
        by_contra hge; push_neg at hge
        have : b * c ≤ (u.val - v.val) * c := Nat.mul_le_mul_right c hge; omega
      have hdist : distMod a u v ≤ u.val - v.val := by
        simp only [distMod]
        have hsub : (u - v).val = u.val - v.val := by
          have hle : v.val ≤ u.val := le_of_lt huv_val
          conv_lhs => rw [← ZMod.natCast_zmod_val u, ← ZMod.natCast_zmod_val v]
          rw [ZMod.val_sub (by simp only [ZMod.val_natCast_of_lt v.val_lt,
            ZMod.val_natCast_of_lt u.val_lt]; exact hle)]
          simp only [ZMod.val_natCast_of_lt u.val_lt, ZMod.val_natCast_of_lt v.val_lt]
        rw [hsub]; apply min_le_of_left_le; exact le_refl _
      exact absurd hdist_ge_b (not_le.mpr (lt_of_le_of_lt hdist hdiff_lt_b))
  · -- Part 2: distMod c (f u) (f v) ≥ d (non-adjacency preserved)
    simp only [fractionGraph, not_and, not_lt]
    intro _
    by_cases hd : d = 0
    · simp [hd]
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    -- Use wlog to assume v.val ≤ u.val; the other case follows by symmetry of distMod
    rename_i hfuv_ne
    wlog hvu : v.val ≤ u.val generalizing u v with Hsym
    · have hdist_sym : distMod a v u ≥ b := distMod_comm a u v ▸ hdist_ge_b
      have := Hsym v u huv.symm (fun h => distMod_comm a u v ▸ hnadj h.symm) hdist_sym
        hfuv_ne.symm (le_of_not_ge hvu)
      rwa [distMod_comm c (f v) (f u)] at this
    -- Now we have v.val ≤ u.val, so δ = (u - v).val = u.val - v.val
    have hvu' : (v.val : ZMod a).val ≤ (u.val : ZMod a).val := by
      simp only [ZMod.val_natCast_of_lt v.val_lt, ZMod.val_natCast_of_lt u.val_lt]; exact hvu
    have hδ_eq : (u - v).val = u.val - v.val := by
      conv_lhs => rw [← ZMod.natCast_zmod_val u, ← ZMod.natCast_zmod_val v]
      rw [ZMod.val_sub hvu']
      simp only [ZMod.val_natCast_of_lt u.val_lt, ZMod.val_natCast_of_lt v.val_lt]
    let δ := u.val - v.val
    have hδ_bounds : b ≤ δ ∧ δ ≤ a - b := by
      have hdm := hdist_ge_b; simp only [distMod, hδ_eq] at hdm
      have hmin := le_min_iff.mp hdm
      exact ⟨hmin.1, by omega⟩
    have hδca_ge_d : d ≤ δ * c / a := by
      rw [Nat.le_div_iff_mul_le ha_pos]
      calc d * a = a * d := Nat.mul_comm d a
        _ ≤ b * c := had_le_bc
        _ ≤ δ * c := Nat.mul_le_mul_right c hδ_bounds.1
    have hf_mono : (f u).val ≥ (f v).val := by
      simp only [hf_val]; exact Nat.div_le_div_right (Nat.mul_le_mul_right c hvu)
    have hfuv_val : (f u - f v).val = (f u).val - (f v).val := ZMod.val_sub hf_mono
    simp only [distMod]
    apply le_min
    · -- d ≤ (f u - f v).val
      rw [hfuv_val, hf_val, hf_val]
      calc d ≤ δ * c / a := hδca_ge_d
        _ ≤ u.val * c / a - v.val * c / a := div_sub_le a c u.val v.val ha_pos hvu
    · -- d ≤ c - (f u - f v).val
      rw [hfuv_val, hf_val, hf_val]
      have hf_u_lt : u.val * c / a < c := hf_lt u
      have hf_v_lt : v.val * c / a < c := hf_lt v
      have hb_le_a : b ≤ a := by
        have := hδ_bounds; omega
      have hd_le_c : d ≤ c := by
        have h1 : a * d ≤ a * c := calc a * d ≤ b * c := had_le_bc
          _ ≤ a * c := Nat.mul_le_mul_right c hb_le_a
        exact Nat.le_of_mul_le_mul_left h1 ha_pos
      suffices h : u.val * c / a - v.val * c / a ≤ c - d by omega
      have hdiff_eq : u.val * c = δ * c + v.val * c := by
        simp only [δ]; rw [← Nat.add_mul, Nat.sub_add_cancel hvu]
      have h_split := Nat.add_div (a := δ * c) (b := v.val * c) ha_pos
      rw [hdiff_eq]
      have hv_div_le : v.val * c / a ≤ u.val * c / a :=
        Nat.div_le_div_right (Nat.mul_le_mul_right c hvu)
      by_cases hremainder : a ≤ δ * c % a + v.val * c % a
      · -- The +1 case: need strict bound
        simp only [if_pos hremainder] at h_split
        have hrem_pos : 0 < δ * c % a := by
          by_contra h; push_neg at h
          have hrem_zero : δ * c % a = 0 := Nat.le_zero.mp h
          rw [hrem_zero] at hremainder
          have hv_rem_lt : v.val * c % a < a := Nat.mod_lt _ ha_pos; omega
        have hstrict := div_add_one_le_of_rem_pos a b c d δ ha_pos hc_pos had_le_bc
          hδ_bounds.2 hrem_pos
        -- Derive: u.val * c / a - v.val * c / a = δ * c / a + 1
        have h_eq : u.val * c / a - v.val * c / a = δ * c / a + 1 := by
          have h1 : u.val * c / a = δ * c / a + v.val * c / a + 1 := by
            rw [hdiff_eq]; exact h_split
          omega
        omega
      · -- No +1 case
        simp only [if_neg hremainder] at h_split
        -- Derive: u.val * c / a - v.val * c / a = δ * c / a
        have h_eq : u.val * c / a - v.val * c / a = δ * c / a := by
          have h1 : u.val * c / a = δ * c / a + v.val * c / a := by
            rw [hdiff_eq]; exact h_split
          omega
        have hδca_le : δ * c / a ≤ c - d := calc
          δ * c / a ≤ (a - b) * c / a := Nat.div_le_div_right (Nat.mul_le_mul_right c hδ_bounds.2)
          _ ≤ c - d := sub_mul_div_le a b c d ha_pos had_le_bc
        omega


/-- The fraction graphs are ordered by cohomomorphism:
    If a/b ≤ c/d, then there exists a cohomomorphism from E_{a/b} to E_{c/d}.
    This is a corollary of `fractionGraph_scalingMap_isCohom`. -/
theorem fractionGraph_cohomomorphism (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hab_le_cd : (a : ℚ) / b ≤ (c : ℚ) / d) :
    ∃ f : ZMod a → ZMod c, ∀ u v, u ≠ v → ¬(fractionGraph a b).Adj u v →
      f u ≠ f v ∧ ¬(fractionGraph c d).Adj (f u) (f v) :=
  ⟨fractionGraph_scalingMap a c, fractionGraph_scalingMap_isCohom a b c d hb_pos hab_le_cd⟩

/-! ## Section 3: Distance-set cardinality and clique-number lemmas

The following lemmas are the consolidated canonical home for the fraction-graph
clique / clique-cover / cohomomorphism-based bounds.  They were previously
duplicated in `Prerequisites/ShannonCapacity.lean`; the consolidated copy now
lives here and is re-exported from `ShannonCapacity` for callers that
`open ShannonCapacity`. -/

/-- Elements with .val difference in [q, p-q] have distMod ≥ q -/
lemma distMod_ge_q_of_val_diff_in_range (p q : ℕ) [NeZero p] (h2q : 2 * q ≤ p)
    (u v : ZMod p) (hle : u.val ≤ v.val) (hdiff_ge : q ≤ v.val - u.val)
    (hdiff_le : v.val - u.val ≤ p - q) : distMod p u v ≥ q := by
  have hval_vu : (v - u).val = v.val - u.val := ZMod.val_sub hle
  rw [distMod_comm]
  simp only [distMod, hval_vu]
  have hp_sub : p - (v.val - u.val) ≥ q := by omega
  exact le_min hdiff_ge hp_sub

/-- Key lemma for Case 2b: If span > p - q, elements partition into low (k < q) and high (k > p-q).
    Cross-pair constraints imply |S| ≤ q. -/
private lemma card_le_of_span_large (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    (S : Finset (ZMod p)) (hS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → distMod p u v < q)
    (min_elem max_elem : ℕ) (x_min x_max : ZMod p)
    (hx_min_S : x_min ∈ S) (hx_max_S : x_max ∈ S)
    (hx_min_val : x_min.val = min_elem) (hx_max_val : x_max.val = max_elem)
    (hmin : ∀ y ∈ S, min_elem ≤ y.val) (hmax : ∀ y ∈ S, y.val ≤ max_elem)
    (hmax_lt : max_elem < p)
    (hspan_large : max_elem - min_elem > p - q) :
    S.card ≤ q := by
  let span := max_elem - min_elem
  have hspan_lt_p : span < p := Nat.lt_of_le_of_lt (Nat.sub_le max_elem min_elem) hmax_lt
  have hspan_le : span ≤ p - 1 := by omega
  have hM_empty : ∀ y ∈ S, ¬(q ≤ y.val - min_elem ∧ y.val - min_elem ≤ p - q) := by
    intro y hyS ⟨hlow, hhigh⟩
    have hy_val_ge : y.val ≥ min_elem := hmin y hyS
    have hx_min_val_eq : x_min.val = min_elem := hx_min_val
    have hdist_ge := distMod_ge_q_of_val_diff_in_range p q h2q x_min y
      (by rw [hx_min_val_eq]; exact hy_val_ge)
      (by rw [hx_min_val_eq]; omega)
      (by rw [hx_min_val_eq]; omega)
    by_cases heq : x_min = y
    · subst heq
      rw [hx_min_val_eq] at hlow
      omega
    · have hdist_lt := hS x_min hx_min_S y hyS heq
      omega
  let L := S.filter (fun y => y.val - min_elem < q)
  let H := S.filter (fun y => y.val - min_elem > p - q)
  have hx_min_in_L : x_min ∈ L := by
    simp only [Finset.mem_filter, L]
    refine ⟨hx_min_S, ?_⟩
    rw [hx_min_val]
    simp [hq]
  have hx_max_in_H : x_max ∈ H := by
    simp only [Finset.mem_filter, H]
    refine ⟨hx_max_S, ?_⟩
    rw [hx_max_val]
    have hmax_ge : max_elem ≥ min_elem := by
      have := hmin x_max hx_max_S
      rw [hx_max_val] at this
      exact this
    omega
  have hS_eq : S = L ∪ H := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, L, H]
    constructor
    · intro hy
      have hy_val_ge := hmin y hy
      by_cases hlow : y.val - min_elem < q
      · left; exact ⟨hy, hlow⟩
      · push_neg at hlow
        right
        refine ⟨hy, ?_⟩
        by_contra hhigh
        push_neg at hhigh
        exact hM_empty y hy ⟨hlow, hhigh⟩
    · intro h
      rcases h with ⟨hy, _⟩ | ⟨hy, _⟩ <;> exact hy
  have hLH_disj : Disjoint L H := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    simp only [Finset.mem_filter, L, H] at hx hy
    intro heq
    subst heq
    omega
  have hspan_bound : span - (p - q) + 1 ≤ q := by omega
  let φ : ZMod p → ℕ := fun y =>
    if y.val - min_elem < q then
      y.val - min_elem
    else
      y.val - min_elem - (p - q)
  have hφ_bound : ∀ y ∈ S, φ y < q := by
    intro y hy
    simp only [φ]
    have hy_val_ge := hmin y hy
    have hy_val_le := hmax y hy
    split_ifs with hlow
    · exact hlow
    · push_neg at hlow
      have hM := hM_empty y hy
      push_neg at hM
      have hy_high := hM hlow
      have : y.val - min_elem ≤ span := by omega
      have := hspan_bound
      omega
  have hφ_inj_on_S : ∀ y1 ∈ S, ∀ y2 ∈ S, φ y1 = φ y2 → y1 = y2 := by
    intro y1 hy1 y2 hy2 heq
    simp only [φ] at heq
    have hv1 := hmin y1 hy1
    have hv2 := hmin y2 hy2
    have hv1_le := hmax y1 hy1
    have hv2_le := hmax y2 hy2
    split_ifs at heq with h1 h2 h2
    · have : y1.val = y2.val := by omega
      exact ZMod.val_injective p this
    · exfalso
      push_neg at h2
      have hy2_in_H : y2.val - min_elem > p - q := by
        have hM := hM_empty y2 hy2
        push_neg at hM
        exact hM h2
      have hdist_val : y2.val - y1.val = p - q := by omega
      have hv1_le' : y1.val ≤ y2.val := by omega
      have hdist := distMod_ge_q_of_val_diff_in_range p q h2q y1 y2 hv1_le'
        (by omega) (by omega)
      have hy1_ne_y2 : y1 ≠ y2 := by
        intro heq'
        subst heq'
        omega
      have hdist_lt := hS y1 hy1 y2 hy2 hy1_ne_y2
      omega
    · exfalso
      push_neg at h1
      have hy1_in_H : y1.val - min_elem > p - q := by
        have hM := hM_empty y1 hy1
        push_neg at hM
        exact hM h1
      have hdist_val : y1.val - y2.val = p - q := by omega
      have hv2_le' : y2.val ≤ y1.val := by omega
      have hdist := distMod_ge_q_of_val_diff_in_range p q h2q y2 y1 hv2_le'
        (by omega) (by omega)
      have hy1_ne_y2 : y1 ≠ y2 := by
        intro heq'
        subst heq'
        omega
      have hdist_lt := hS y2 hy2 y1 hy1 hy1_ne_y2.symm
      omega
    · -- Both in H zone: offsets - (p-q) equal → offsets equal → vals equal
      push_neg at h1 h2
      have hy1_in_H : y1.val - min_elem > p - q := by
        have hM := hM_empty y1 hy1
        push_neg at hM
        exact hM h1
      have hy2_in_H : y2.val - min_elem > p - q := by
        have hM := hM_empty y2 hy2
        push_neg at hM
        exact hM h2
      have : y1.val = y2.val := by omega
      exact ZMod.val_injective p this
  have hφ_inj : Set.InjOn φ S := by
    intro y1 hy1 y2 hy2 heq
    exact hφ_inj_on_S y1 hy1 y2 hy2 heq
  have h_image_subset : S.image φ ⊆ Finset.range q := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨y, hy, rfl⟩ := hn
    exact Finset.mem_range.mpr (hφ_bound y hy)
  calc S.card = (S.image φ).card := (Finset.card_image_of_injOn hφ_inj).symm
    _ ≤ (Finset.range q).card := Finset.card_le_card h_image_subset
    _ = q := Finset.card_range q

/-- A set of vertices in ZMod p with all pairwise distances < q has at most q elements.
This is the key combinatorial lemma for clique bounds in fraction graphs.
Requires 2q ≤ p since for q < p < 2q, the max distance ⌊p/2⌋ < q makes all pairs adjacent. -/
theorem finset_card_le_of_pairwise_dist_lt (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p)
    (S : Finset (ZMod p)) (hS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → distMod p u v < q) :
    S.card ≤ q := by
  by_cases hS_empty : S = ∅
  · simp [hS_empty]
  have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  let vals := S.image (fun x : ZMod p => x.val)
  have hvals_card : vals.card = S.card := Finset.card_image_of_injective S (ZMod.val_injective p)
  obtain ⟨min_elem, hmin_mem, hmin⟩ :=
    vals.exists_min_image id (Finset.image_nonempty.mpr hS_nonempty)
  obtain ⟨max_elem, hmax_mem, hmax⟩ :=
    vals.exists_max_image id (Finset.image_nonempty.mpr hS_nonempty)
  rw [Finset.mem_image] at hmin_mem hmax_mem
  obtain ⟨x_min, hx_min_S, hx_min_val⟩ := hmin_mem
  obtain ⟨x_max, hx_max_S, hx_max_val⟩ := hmax_mem
  let span := max_elem - min_elem
  have hmax_ge_min : max_elem ≥ min_elem := by
    have := hmin max_elem (Finset.mem_image.mpr ⟨x_max, hx_max_S, hx_max_val⟩)
    simp only [id] at this
    exact this
  have hmax_lt : max_elem < p := by rw [← hx_max_val]; exact ZMod.val_lt x_max
  have hmin_lt : min_elem < p := by rw [← hx_min_val]; exact ZMod.val_lt x_min
  by_cases hspan : span < q
  · have hvals_subset : vals ⊆ Finset.Icc min_elem (min_elem + q - 1) := by
      intro v hv
      rw [Finset.mem_Icc]
      constructor
      · exact hmin v hv
      · have hv_le_max : v ≤ max_elem := hmax v hv
        have hmax_eq : max_elem = min_elem + span := by omega
        omega
    have hIcc_card : (Finset.Icc min_elem (min_elem + q - 1)).card = q := by
      rw [Nat.card_Icc]
      omega
    calc S.card = vals.card := hvals_card.symm
      _ ≤ (Finset.Icc min_elem (min_elem + q - 1)).card := Finset.card_le_card hvals_subset
      _ = q := hIcc_card
  · push_neg at hspan
    have hval_diff : (x_max - x_min).val = span := by
      rw [ZMod.val_sub (by rw [hx_max_val, hx_min_val]; exact hmax_ge_min)]
      rw [hx_max_val, hx_min_val]
    have hdist : distMod p x_min x_max = min span (p - span) := by
      rw [distMod_comm]
      simp only [distMod, hval_diff]
    have hx_ne : x_min ≠ x_max := by
      intro heq
      have : x_min.val = x_max.val := by rw [heq]
      rw [hx_min_val, hx_max_val] at this
      have : span = 0 := by omega
      omega
    have hdist_lt_q := hS x_min hx_min_S x_max hx_max_S hx_ne
    by_cases hspan_le_pq : span ≤ p - q
    · have hdist_ge_q : distMod p x_min x_max ≥ q := by
        rw [hdist]
        exact min_span_ge_q_of_in_range p q span hspan hspan_le_pq
      omega
    · push_neg at hspan_le_pq
      have hmin' : ∀ y ∈ S, min_elem ≤ y.val := by
        intro y hy
        have hy_val : y.val ∈ vals := Finset.mem_image_of_mem _ hy
        exact hmin y.val hy_val
      have hmax' : ∀ y ∈ S, y.val ≤ max_elem := by
        intro y hy
        have hy_val : y.val ∈ vals := Finset.mem_image_of_mem _ hy
        exact hmax y.val hy_val
      exact card_le_of_span_large p q hq h2q S hS min_elem max_elem
        x_min x_max hx_min_S hx_max_S hx_min_val hx_max_val hmin' hmax' hmax_lt hspan_le_pq

/-! ## Section 4: Clique Properties of Fraction Graphs -/

/-- A clique in E_{p/q} has size at most q.
Cliques consist of vertices with pairwise distance < q (adjacency condition),
which means at most q consecutive vertices in ZMod p.
Requires 2q ≤ p; for q < p < 2q, the graph is complete so clique number = p > q. -/
theorem cliqueNum_fractionGraph_le (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    (fractionGraph p q).cliqueNum ≤ q := by
  rw [SimpleGraph.cliqueNum]
  apply csSup_le
  · exact ⟨0, ∅, SimpleGraph.isNClique_empty.mpr rfl⟩
  · intro n ⟨S, hS⟩
    have hcard : S.card = n := hS.card_eq
    rw [← hcard]
    apply finset_card_le_of_pairwise_dist_lt p q hq h2q S
    intro u hu v hv huv
    have hclique := hS.isClique
    rw [SimpleGraph.isClique_iff] at hclique
    have hadj := hclique hu hv huv
    simp only [fractionGraph] at hadj
    exact hadj.2

/-- The set {0, 1, ..., q-1} is a clique in E_{p/q}.
    This gives a lower bound ω(E_{p/q}) ≥ q. -/
theorem isClique_range_fractionGraph (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    (fractionGraph p q).IsClique ((Finset.range q).image (fun i : ℕ => (i : ZMod p))) := by
  rw [SimpleGraph.isClique_iff]
  intro u hu v hv huv
  rw [Finset.mem_coe, Finset.mem_image] at hu hv
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  rw [Finset.mem_range] at ha hb
  simp only [fractionGraph]
  constructor
  · exact huv
  · simp only [distMod]
    have hq_le_p : q ≤ p := by omega
    have ha_lt_p : a < p := Nat.lt_of_lt_of_le ha hq_le_p
    have hb_lt_p : b < p := Nat.lt_of_lt_of_le hb hq_le_p
    by_cases hab : a ≤ b
    · have hval : ((a : ZMod p) - (b : ZMod p)).val =
          if a = b then 0 else p - (b - a) := by
        by_cases heq : a = b
        · simp [heq]
        · have hlt : a < b := Nat.lt_of_le_of_ne hab heq
          have hba_pos : 0 < b - a := Nat.sub_pos_of_lt hlt
          have hba_lt_p : b - a < p := by omega
          simp only [heq, ↓reduceIte]
          have h : (a : ZMod p) - (b : ZMod p) = -((b - a : ℕ) : ZMod p) := by
            simp only [Nat.cast_sub (Nat.le_of_lt hlt), neg_sub]
          rw [h]
          have hne : ((b - a : ℕ) : ZMod p) ≠ 0 := by
            rw [ne_eq, ZMod.natCast_eq_zero_iff]
            intro hdvd
            have := Nat.eq_zero_of_dvd_of_lt hdvd hba_lt_p
            omega
          rw [ZMod.neg_val, if_neg hne, ZMod.val_natCast_of_lt hba_lt_p]
      simp only [hval]
      split_ifs with heq
      · exfalso; apply huv; simp [heq]
      · have hlt : a < b := Nat.lt_of_le_of_ne hab heq
        have hba : b - a < q := by omega
        simp only [Nat.min_def]
        split_ifs with h <;> omega
    · push_neg at hab
      have hval : ((a : ZMod p) - (b : ZMod p)).val = a - b := by
        have hab' : (a : ZMod p) - (b : ZMod p) = ((a - b : ℕ) : ZMod p) := by
          simp only [Nat.cast_sub (Nat.le_of_lt hab)]
        rw [hab']
        have hab_lt_p : a - b < p := by omega
        exact ZMod.val_natCast_of_lt hab_lt_p
      rw [hval]
      have hab_lt_q : a - b < q := by omega
      simp only [Nat.min_def]
      split_ifs with h
      · exact hab_lt_q
      · omega

/-- Any translated arc {start, start+1, ..., start+(q-1)} is a clique in E_{p/q}.
    Follows from isClique_range_fractionGraph by translation invariance. -/
theorem isClique_arc (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) (start : ZMod p) :
    (fractionGraph p q).IsClique ((Finset.range q).image (fun j : ℕ => start + j)) := by
  have hbase := isClique_range_fractionGraph p q hq h2q
  rw [SimpleGraph.isClique_iff] at hbase ⊢
  intro u hu v hv huv
  rw [Finset.mem_coe, Finset.mem_image] at hu hv
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  rw [fractionGraph_adj_add_left]
  apply hbase
  · simp only [Finset.mem_coe, Finset.mem_image]; exact ⟨a, ha, rfl⟩
  · simp only [Finset.mem_coe, Finset.mem_image]; exact ⟨b, hb, rfl⟩
  · intro heq; apply huv; simpa using heq

/-- The clique number of E_{p/q} is at least q. -/
theorem cliqueNum_fractionGraph_ge (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    q ≤ (fractionGraph p q).cliqueNum := by
  have hclique := isClique_range_fractionGraph p q hq h2q
  have hq_le_p : q ≤ p := by omega
  have hinj : Set.InjOn (fun i : ℕ => (i : ZMod p)) ↑(Finset.range q) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    have ha_lt_p : a < p := Nat.lt_of_lt_of_le ha hq_le_p
    have hb_lt_p : b < p := Nat.lt_of_lt_of_le hb hq_le_p
    have := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt ha_lt_p, ZMod.val_natCast_of_lt hb_lt_p] at this
    exact this
  have hcard : ((Finset.range q).image (fun i : ℕ => (i : ZMod p))).card = q := by
    rw [Finset.card_image_of_injOn hinj]
    exact Finset.card_range q
  calc q = ((Finset.range q).image (fun i : ℕ => (i : ZMod p))).card := hcard.symm
    _ ≤ (fractionGraph p q).cliqueNum := hclique.card_le_cliqueNum

/-- The clique number of E_{p/q} equals q. -/
theorem cliqueNum_fractionGraph_eq (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    (fractionGraph p q).cliqueNum = q :=
  le_antisymm (cliqueNum_fractionGraph_le p q hq h2q) (cliqueNum_fractionGraph_ge p q hq h2q)

/-! ## Section 5: Fractional Clique Cover -/

/-- The fractional clique cover number of E_{p/q} is at most p/q.
For vertex-transitive graphs G with n vertices and clique number ω,
χ_f(G) = n/ω. For E_{p/q}: ω = q (from cliqueNum_fractionGraph_le), so χ_f = p/q.
Requires 2q ≤ p to ensure arcs are distinct (for q > p/2, some arcs coincide). -/
theorem fractionalCliqueCover_fractionGraph (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    ∃ (cliques : Finset (Finset (ZMod p))) (weights : Finset (ZMod p) → ℝ),
      (∀ C ∈ cliques, (fractionGraph p q).IsClique C) ∧
      (∀ C ∈ cliques, weights C ≥ 0) ∧
      (∀ v : ZMod p, (cliques.filter (v ∈ ·)).sum weights ≥ 1) ∧
      cliques.sum weights ≤ (p : ℝ) / q := by
  let arc (i : ZMod p) : Finset (ZMod p) := (Finset.range q).image (fun j : ℕ => i + (j : ZMod p))
  let cliques : Finset (Finset (ZMod p)) := Finset.univ.image arc
  let weights : Finset (ZMod p) → ℝ := fun _ => (1 : ℝ) / q
  use cliques, weights
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C hC
    rw [Finset.mem_image] at hC
    obtain ⟨i, _, rfl⟩ := hC
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    rw [Finset.mem_range] at ha hb
    simp only [fractionGraph]
    constructor
    · intro heq
      apply huv
      have hab : (a : ZMod p) = (b : ZMod p) := by
        have h := congrArg (· - i) heq
        simp only [add_sub_cancel_left] at h
        exact h
      have hq_le_p : q ≤ p := by omega
      have ha_lt_p : a < p := Nat.lt_of_lt_of_le ha hq_le_p
      have hb_lt_p : b < p := Nat.lt_of_lt_of_le hb hq_le_p
      have heq' : a = b :=
        ZMod.val_cast_of_lt ha_lt_p ▸ ZMod.val_cast_of_lt hb_lt_p ▸ congrArg ZMod.val hab
      simp [heq']
    · simp only [distMod]
      have h_sub : ((i + (a : ZMod p)) - (i + (b : ZMod p))) =
          ((a : ZMod p) - (b : ZMod p)) := by ring
      rw [h_sub]
      have hq_le_p : q ≤ p := by omega
      by_cases hab : b ≤ a
      · have hab' : (a : ZMod p) - (b : ZMod p) = ((a - b : ℕ) : ZMod p) := by
          simp only [Nat.cast_sub hab]
        rw [hab']
        have hab_lt_q : a - b < q := Nat.sub_lt_left_of_lt_add hab (by omega : a < b + q)
        have hab_lt_p : a - b < p := Nat.lt_of_lt_of_le hab_lt_q hq_le_p
        rw [ZMod.val_natCast_of_lt hab_lt_p]
        have hp_sub : p - (a - b) ≥ a - b := by omega
        simp only [Nat.min_def]
        split_ifs with h
        · exact hab_lt_q
        · omega
      · push_neg at hab
        have hab' : a < b := hab
        have hba : (a : ZMod p) - (b : ZMod p) = -((b - a : ℕ) : ZMod p) := by
          simp only [Nat.cast_sub (Nat.le_of_lt hab'), neg_sub]
        rw [hba]
        have hba_lt_q : b - a < q :=
          Nat.sub_lt_left_of_lt_add (Nat.le_of_lt hab') (by omega : b < a + q)
        have hba_lt_p : b - a < p := Nat.lt_of_lt_of_le hba_lt_q hq_le_p
        have hba_pos : 0 < b - a := Nat.sub_pos_of_lt hab'
        have hba_ne_zero : ((b - a : ℕ) : ZMod p) ≠ 0 := by
          rw [ne_eq, ZMod.natCast_eq_zero_iff]
          intro hdvd
          have := Nat.eq_zero_of_dvd_of_lt hdvd hba_lt_p
          omega
        rw [ZMod.neg_val, if_neg hba_ne_zero, ZMod.val_natCast_of_lt hba_lt_p]
        simp only [Nat.min_def]
        split_ifs with h <;> omega
  · intro C _
    simp only [weights]
    positivity
  · intro v
    have h_arcs_in_cliques : ∀ j : ℕ, j < q → arc (v - (j : ZMod p)) ∈ cliques := by
      intro j _
      change arc (v - (j : ZMod p)) ∈ Finset.univ.image arc
      rw [Finset.mem_image]
      exact ⟨v - j, Finset.mem_univ _, rfl⟩
    have h_v_in_arc : ∀ j : ℕ, j < q → v ∈ arc (v - (j : ZMod p)) := by
      intro j hj
      change v ∈ (Finset.range q).image (fun k : ℕ => (v - (j : ZMod p)) + (k : ZMod p))
      rw [Finset.mem_image]
      use j, Finset.mem_range.mpr hj
      ring
    let covering_arcs : Finset (Finset (ZMod p)) :=
      (Finset.range q).image (fun j : ℕ => arc (v - (j : ZMod p)))
    have h_subset : covering_arcs ⊆ cliques.filter (v ∈ ·) := by
      intro C hC
      rw [Finset.mem_filter]
      rw [Finset.mem_image] at hC
      obtain ⟨j, hj, rfl⟩ := hC
      rw [Finset.mem_range] at hj
      exact ⟨h_arcs_in_cliques j hj, h_v_in_arc j hj⟩
    have h_card : covering_arcs.card = q := by
      have h_injective : ∀ j₁ ∈ Finset.range q, ∀ j₂ ∈ Finset.range q,
          arc (v - (j₁ : ZMod p)) = arc (v - (j₂ : ZMod p)) → j₁ = j₂ := by
        intro j₁ hj1 j₂ hj2 heq
        rw [Finset.mem_range] at hj1 hj2
        have h1 : v - (j₁ : ZMod p) ∈ arc (v - (j₁ : ZMod p)) := by
          change v - (j₁ : ZMod p) ∈
            (Finset.range q).image (fun k : ℕ => (v - (j₁ : ZMod p)) + (k : ZMod p))
          rw [Finset.mem_image]
          use 0, Finset.mem_range.mpr hq
          ring
        rw [heq] at h1
        rw [show arc (v - (j₂ : ZMod p)) =
            (Finset.range q).image (fun k : ℕ => (v - (j₂ : ZMod p)) + (k : ZMod p)) from rfl,
            Finset.mem_image] at h1
        obtain ⟨k, hk, hk_eq⟩ := h1
        rw [Finset.mem_range] at hk
        have h_mod : (j₂ : ZMod p) = (j₁ : ZMod p) + (k : ZMod p) := by
          have heq' : v - (j₁ : ZMod p) = v - (j₂ : ZMod p) + (k : ZMod p) := hk_eq.symm
          calc (j₂ : ZMod p) = j₂ + (v - j₁) - (v - j₁) := by ring
            _ = j₂ + (v - j₂ + k) - (v - j₁) := by rw [heq']
            _ = j₁ + k := by ring
        have h2 : v - (j₂ : ZMod p) ∈ arc (v - (j₂ : ZMod p)) := by
          change v - (j₂ : ZMod p) ∈
            (Finset.range q).image (fun k : ℕ => (v - (j₂ : ZMod p)) + (k : ZMod p))
          rw [Finset.mem_image]
          use 0, Finset.mem_range.mpr hq
          ring
        rw [← heq] at h2
        rw [show arc (v - (j₁ : ZMod p)) =
            (Finset.range q).image (fun k : ℕ => (v - (j₁ : ZMod p)) + (k : ZMod p)) from rfl,
            Finset.mem_image] at h2
        obtain ⟨k', hk', hk'_eq⟩ := h2
        rw [Finset.mem_range] at hk'
        have h_mod' : (j₁ : ZMod p) = (j₂ : ZMod p) + (k' : ZMod p) := by
          have heq' : v - (j₂ : ZMod p) = v - (j₁ : ZMod p) + (k' : ZMod p) := hk'_eq.symm
          calc (j₁ : ZMod p) = j₁ + (v - j₂) - (v - j₂) := by ring
            _ = j₁ + (v - j₁ + k') - (v - j₂) := by rw [heq']
            _ = j₂ + k' := by ring
        have hkk' : (k : ZMod p) + (k' : ZMod p) = 0 := by
          have hk_eq : (k : ZMod p) = (j₂ : ZMod p) - (j₁ : ZMod p) := by rw [h_mod]; ring
          have hk'_eq : (k' : ZMod p) = (j₁ : ZMod p) - (j₂ : ZMod p) := by rw [h_mod']; ring
          rw [hk_eq, hk'_eq]; ring
        have hsum_lt : k + k' < 2 * q := by omega
        have hsum_lt_p : k + k' < p := Nat.lt_of_lt_of_le hsum_lt h2q
        rw [← Nat.cast_add] at hkk'
        rw [ZMod.natCast_eq_zero_iff] at hkk'
        have hkk'_eq_zero : k + k' = 0 := Nat.eq_zero_of_dvd_of_lt hkk' hsum_lt_p
        have hk_zero : k = 0 := by omega
        have : (j₁ : ZMod p) = (j₂ : ZMod p) := by
          simp only [hk_zero, Nat.cast_zero, add_zero] at h_mod; exact h_mod.symm
        have hq_le_p : q ≤ p := by omega
        have hj1_lt_p : j₁ < p := Nat.lt_of_lt_of_le hj1 hq_le_p
        have hj2_lt_p : j₂ < p := Nat.lt_of_lt_of_le hj2 hq_le_p
        exact ZMod.val_cast_of_lt hj1_lt_p ▸ ZMod.val_cast_of_lt hj2_lt_p ▸ congrArg ZMod.val this
      have h_inj_on : Set.InjOn (fun j : ℕ => arc (v - (j : ZMod p))) (Finset.range q) := by
        intro j₁ hj1 j₂ hj2 heq
        rw [Finset.coe_range, Set.mem_Iio] at hj1 hj2
        exact h_injective j₁ (Finset.mem_range.mpr hj1) j₂ (Finset.mem_range.mpr hj2) heq
      rw [Finset.card_image_of_injOn h_inj_on, Finset.card_range]
    have h_sum_le : covering_arcs.sum weights ≤ (cliques.filter (v ∈ ·)).sum weights := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
      intro i _ _
      change (1 : ℝ) / q ≥ 0
      positivity
    have h_sum_eq : covering_arcs.sum weights = 1 := by
      simp only [weights, Finset.sum_const, h_card]
      have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      rw [nsmul_eq_mul, mul_one_div, div_self hq_ne]
    linarith
  · have h_card_le : cliques.card ≤ Fintype.card (ZMod p) := Finset.card_image_le
    have h_card_p : Fintype.card (ZMod p) = p := ZMod.card p
    simp only [weights, Finset.sum_const]
    rw [h_card_p] at h_card_le
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
    calc cliques.card • (1 / (q : ℝ))
        = (cliques.card : ℝ) * (1 / q) := by rw [nsmul_eq_mul]
      _ = cliques.card / q := by ring
      _ ≤ p / q := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hq_pos)
          exact_mod_cast h_card_le

/-! ## Ratio-level utilities

Generic fraction-graph properties (ratio, edgeless degenerate cases,
vertex-transitivity, equal-ratio isomorphism). Kept in the same
`FractionGraphBasic` namespace as the rest of the fraction-graph API. -/

/-- The ratio p/q as a rational number -/
def fractionGraphRatio (p q : ℕ) (_ : 0 < p) (_ : 0 < q) : ℚ := p / q

/-! ## Edgeless graph lemmas -/

/-- E_{n/1} has no edges (is the edgeless graph on n vertices) -/
theorem fractionGraph_one_edgeless (n : ℕ) [NeZero n] :
    fractionGraph n 1 = ⊥ := by
  ext i j
  simp only [fractionGraph, distMod, SimpleGraph.bot_adj]
  constructor
  · intro ⟨hne, hlt⟩
    -- min of two natural numbers < 1 means the min is 0
    simp only [Nat.lt_one_iff] at hlt
    -- If min d (n - d) = 0, then d = 0 or n - d = 0
    have hd : (i - j).val = 0 ∨ n - (i - j).val = 0 := Nat.min_eq_zero_iff.mp hlt
    rcases hd with hd | hd
    · -- d = 0 implies i = j
      have hsub_zero : i - j = 0 := by
        rw [← ZMod.val_eq_zero]
        exact hd
      have heq : i = j := sub_eq_zero.mp hsub_zero
      exact hne heq
    · -- n - d = 0 implies d = n, but d < n
      have hval_lt : (i - j).val < n := (i - j).val_lt
      omega
  · intro h
    exact h.elim

/-- For q = 0, the graph has no edges -/
theorem fractionGraph_zero_edgeless (p : ℕ) [NeZero p] :
    fractionGraph p 0 = ⊥ := by
  ext i j
  simp only [fractionGraph, SimpleGraph.bot_adj]
  constructor
  · intro ⟨_, hlt⟩
    exact (Nat.not_lt_zero _ hlt).elim
  · intro h
    exact h.elim

/-! ## Vertex transitivity -/

/-- distMod is translation-invariant (right-addition variant; thin wrapper around
the canonical left-addition lemma `distMod_add_left`). -/
theorem distMod_add_right (p : ℕ) [NeZero p] (a b k : ZMod p) :
    distMod p (a + k) (b + k) = distMod p a b := by
  rw [add_comm a k, add_comm b k]; exact distMod_add_left p k a b

/-- The fraction graph is vertex-transitive: translation acts transitively on vertices.
    The translation φ_k : x ↦ x + k is an automorphism of E_{p/q}. -/
theorem fractionGraph_vertexTransitive (p q : ℕ) [NeZero p] :
    ∀ i j : ZMod p, ∃ φ : fractionGraph p q ≃g fractionGraph p q, φ i = j := by
  intro i j
  -- The automorphism is translation by (j - i)
  let k := j - i
  -- Build the isomorphism
  let φ : fractionGraph p q ≃g fractionGraph p q := {
    toEquiv := {
      toFun := fun x => x + k
      invFun := fun x => x - k
      left_inv := fun x => by simp [k]
      right_inv := fun x => by simp [k]
    }
    map_rel_iff' := by
      intro a b
      simp only [fractionGraph, Equiv.coe_fn_mk]
      constructor
      · intro ⟨hne, hdist⟩
        constructor
        · intro heq
          exact hne (by rw [heq])
        · rw [← distMod_add_right p a b k]
          exact hdist
      · intro ⟨hne, hdist⟩
        constructor
        · intro heq
          have hab : a = b := by
            calc a = a + k - k := by ring
              _ = b + k - k := by rw [heq]
              _ = b := by ring
          exact hne hab
        · rw [distMod_add_right p a b k]
          exact hdist
  }
  use φ
  simp only [φ, k, RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  ring

/-! ## Isomorphism for equal ratios -/

/-- Two fraction graphs with the same ratio and same vertex count are equal. -/
theorem fractionGraph_eq_of_ratio_eq {p q s : ℕ} [NeZero p]
    (hq : 0 < q) (hs : 0 < s)
    (h_eq : (p : ℚ) / q = (p : ℚ) / s) :
    fractionGraph p q = fractionGraph p s := by
  have hp_pos : (p : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne p
  have h_q_eq_s : q = s := by
    have hq_pos : (0 : ℚ) < q := Nat.cast_pos.mpr hq
    have hs_pos : (0 : ℚ) < s := Nat.cast_pos.mpr hs
    have hq_ne : (q : ℚ) ≠ 0 := ne_of_gt hq_pos
    have hs_ne : (s : ℚ) ≠ 0 := ne_of_gt hs_pos
    field_simp at h_eq
    exact_mod_cast h_eq.symm
  rw [h_q_eq_s]

end FractionGraphBasic
