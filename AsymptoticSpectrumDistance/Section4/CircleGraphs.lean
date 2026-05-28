/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section3.FractionGraphs
import AsymptoticSpectrumDistance.Prerequisites.InfiniteGraph
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Circle Graphs (Infinite Graphs on the Circle)

This file defines the circle graphs E_r^o (open) and E_r^c (closed) which are
infinite graphs on the unit circle. These serve as limit points for Cauchy
sequences of fraction graphs.

## Main definitions

* `CircleGraph` : The unit circle as vertex set (ℝ/ℤ)
* `circleGraphOpen r` : E_r^o with Adj u v ↔ d(u,v) < 1/r
* `circleGraphClosed r` : E_r^c with Adj u v ↔ d(u,v) ≤ 1/r

## Main results

* `circleGraph_mono` : r < s → E_r^c ≤ E_r^o ≤ E_s^c ≤ E_s^o
* `circleGraphOpen_equiv_fractionGraph` : E_{p/q}^o ≃ E_{p/q}
* `circleGraphClosed_finite_subgraph` : Finite subgraphs of E_r^c are fraction graphs

## References

* [de Boer, Buys, Zuiddam] Section 4
* [Zhu 1992] Circular chromatic number
-/

namespace AsymptoticSpectrumDistance

open FractionGraphBasic AsymptoticSpectrumGraphs SimpleGraph

/-! ### Circle as Vertex Set -/

/-- The circle group ℝ/ℤ with unit circumference.
    Points are represented as real numbers modulo 1. -/
abbrev Circle := AddCircle (1 : ℝ)

/-- The distance on the circle (minimum of clockwise and counterclockwise).
    This is the arc length min(d, 1-d) where d is the natural distance.
    Uses the metric space structure on AddCircle from Mathlib. -/
noncomputable def circleDistance (u v : Circle) : ℝ := dist u v

/-- Circle distance is symmetric. -/
theorem circleDistance_comm (u v : Circle) :
    circleDistance u v = circleDistance v u :=
  dist_comm u v

/-- Circle distance is non-negative. -/
theorem circleDistance_nonneg (u v : Circle) : 0 ≤ circleDistance u v :=
  dist_nonneg

/-- Circle distance is at most 1/2. -/
theorem circleDistance_le_half (u v : Circle) : circleDistance u v ≤ 1/2 := by
  unfold circleDistance
  rw [dist_eq_norm]
  have h := AddCircle.norm_le_half_period (1 : ℝ) (x := u - v) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [abs_one] at h
  convert h using 1

/-- Circle distance is zero iff points are equal. -/
theorem circleDistance_eq_zero_iff (u v : Circle) :
    circleDistance u v = 0 ↔ u = v :=
  dist_eq_zero

/-! ### Circle Graph Definitions -/

/-- The open circle graph E_r^o: two vertices are adjacent iff their
    distance is strictly less than 1/r. -/
def circleGraphOpen (r : ℝ) (_hr : 2 ≤ r) : SimpleGraph Circle where
  Adj u v := u ≠ v ∧ circleDistance u v < 1/r
  symm := by
    intro u v ⟨hne, hdist⟩
    exact ⟨hne.symm, by rw [circleDistance_comm]; exact hdist⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- The closed circle graph E_r^c: two vertices are adjacent iff their
    distance is at most 1/r. -/
def circleGraphClosed (r : ℝ) (_hr : 2 ≤ r) : SimpleGraph Circle where
  Adj u v := u ≠ v ∧ circleDistance u v ≤ 1/r
  symm := by
    intro u v ⟨hne, hdist⟩
    exact ⟨hne.symm, by rw [circleDistance_comm]; exact hdist⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

notation:max "E[" r "]ᵒ" => circleGraphOpen r
notation:max "E[" r "]ᶜ" => circleGraphClosed r

/-! ### Cohomomorphism Ordering of Circle Graphs -/

/-- The closed circle graph admits a cohomomorphism to the open circle graph via identity.

    The identity is a cohomomorphism since non-edges in the closed graph
    (where d(u,v) > 1/r) remain non-edges in the open graph (since d(u,v) ≥ 1/r). -/
theorem circleGraphClosed_le_open (r : ℝ) (hr : 2 ≤ r) :
    Cohom (circleGraphClosed r hr) (circleGraphOpen r hr) := by
  use id
  intro u v huv hnadj
  constructor
  · exact huv
  · intro hadj_open
    obtain ⟨_, hdist_open⟩ := hadj_open
    simp only [id_eq] at hdist_open
    simp only [circleGraphClosed, ne_eq] at hnadj
    push_neg at hnadj
    have hd_gt : 1/r < circleDistance u v := hnadj huv
    linarith

/-- The circle graphs are monotone in r.
    r < s implies E_r^c ≤ E_r^o ≤ E_s^c ≤ E_s^o

    The identity is a cohomomorphism at each step.
    For E_r^o → E_s^c: non-edges in E_r^o satisfy d(u,v) ≥ 1/r > 1/s, hence non-edges in E_s^c. -/
theorem circleGraph_mono_middle (r s : ℝ) (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r < s) :
    Cohom (circleGraphOpen r hr) (circleGraphClosed s hs) := by
  use id
  intro u v huv hnadj
  constructor
  · exact huv
  · -- Need to show: non-adjacent in E_s^c
    -- hnadj: non-adjacent in E_r^o (source), i.e., d(u,v) ≥ 1/r
    intro hadj_closed
    obtain ⟨_, hdist_closed⟩ := hadj_closed
    simp only [id_eq] at hdist_closed
    -- hdist_closed: d(u,v) ≤ 1/s (adjacent in E_s^c)
    simp only [circleGraphOpen, ne_eq] at hnadj
    push_neg at hnadj
    -- hnadj gives: d(u,v) ≥ 1/r when u ≠ v
    have hd_ge : 1/r ≤ circleDistance u v := hnadj huv
    -- From r < s, we get 1/s < 1/r
    have hinv : 1/s < 1/r := by
      have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
      have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hs
      exact one_div_lt_one_div_of_lt hr_pos hrs
    -- So 1/s < 1/r ≤ d(u,v), but hadj_closed says d(u,v) ≤ 1/s, contradiction
    linarith

/-- Lemma 4.2: The circle graphs are monotone in r.
    r < s implies E_r^c ≤ E_r^o ≤ E_s^c ≤ E_s^o -/
theorem circleGraph_mono (r s : ℝ) (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r < s) :
    Cohom (circleGraphClosed r hr) (circleGraphOpen r hr) ∧
    Cohom (circleGraphOpen r hr) (circleGraphClosed s hs) ∧
    Cohom (circleGraphClosed s hs) (circleGraphOpen s hs) :=
  ⟨circleGraphClosed_le_open r hr, circleGraph_mono_middle r s hr hs hrs,
   circleGraphClosed_le_open s hs⟩

/-! ### Embedding ZMod p into Circle -/

/-- Helper: (a - b).val when a.val < b.val equals n - (b.val - a.val). -/
private lemma zmod_val_sub_of_lt (n : ℕ) [NeZero n] (a b : ZMod n) (h : a.val < b.val) :
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

/-- The embedding function from ZMod p to Circle = AddCircle 1.
    Maps k ↦ k.val / p on the unit circle. -/
noncomputable def embedZMod (p : ℕ) [NeZero p] (k : ZMod p) : Circle :=
  QuotientAddGroup.mk ((k.val : ℝ) / p)

lemma embedZMod_zero (p : ℕ) [NeZero p] : embedZMod p 0 = 0 := by
  simp [embedZMod]

/-- The difference of embeddings equals the embedding of the ZMod difference. -/
private lemma embedZMod_sub_eq (p : ℕ) [hp : NeZero p] (u v : ZMod p) :
    embedZMod p u - embedZMod p v = QuotientAddGroup.mk (((u - v).val : ℝ) / p) := by
  unfold embedZMod
  rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq]
  simp only [AddSubgroup.mem_zmultiples_iff, neg_sub]
  by_cases h : v.val ≤ u.val
  · use 0
    rw [ZMod.val_sub h]
    simp only [Nat.cast_sub h]
    ring
  · push_neg at h
    use 1
    have hval := zmod_val_sub_of_lt p u v h
    have hpn := ZMod.val_lt v
    have hbminus : v.val - u.val ≤ p := by omega
    rw [hval]
    simp only [Nat.cast_sub hbminus, Nat.cast_sub (le_of_lt h)]
    have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    field_simp; ring

/-- Helper: round x = 1 when x ∈ [1/2, 3/2). -/
private lemma round_eq_one_of_mem_Ico {x : ℝ} (h : x ∈ Set.Ico (1 / 2 : ℝ) (3 / 2)) :
    round x = 1 := by
  have h1 : x - 1 ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) := by
    simp only [Set.mem_Ico] at h ⊢; constructor <;> linarith
  have h2 : round (x - 1) = 0 := round_eq_zero_iff.mpr h1
  have h3 : round x = round (x - 1 + 1) := by ring_nf
  rw [h3, round_add_one, h2]; norm_num

/-- distMod = (u-v).val when 2*(u-v).val < p. -/
private lemma distMod_eq_val_of_lt_half (p : ℕ) [hp : NeZero p] (u v : ZMod p)
    (h : 2 * (u - v).val < p) : distMod p u v = (u - v).val := by
  simp only [distMod]; rw [min_eq_left]; omega

/-- distMod = p - (u-v).val when 2*(u-v).val ≥ p. -/
private lemma distMod_eq_p_sub_val (p : ℕ) [hp : NeZero p] (u v : ZMod p)
    (h : p ≤ 2 * (u - v).val) : distMod p u v = p - (u - v).val := by
  simp only [distMod]; rw [min_eq_right]; omega

/-- Key lemma: Circle distance between embedded points equals distMod / p.

    This connects the ZMod distance (distMod) to the AddCircle metric distance.
    Proof uses that round(x) = 0 for x ∈ [-1/2, 1/2) and round(x) = 1 for x ∈ [1/2, 3/2). -/
theorem embedZMod_dist_eq (p : ℕ) [hp : NeZero p] (u v : ZMod p) :
    dist (embedZMod p u) (embedZMod p v) = (distMod p u v : ℝ) / p := by
  rw [dist_eq_norm, embedZMod_sub_eq, UnitAddCircle.norm_eq]
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
  have hval_lt : (u - v).val < p := ZMod.val_lt (u - v)
  have hval_div : ((u - v).val : ℝ) / p < 1 := by rw [div_lt_one hp_pos]; exact_mod_cast hval_lt
  have hval_nonneg : 0 ≤ ((u - v).val : ℝ) / p := by positivity
  by_cases h : 2 * (u - v).val < p
  · -- Case: (u - v).val < p/2, so round = 0
    have hlt_half : ((u - v).val : ℝ) / p < 1 / 2 := by
      rw [div_lt_div_iff₀ hp_pos (by norm_num : (0 : ℝ) < 2)]
      calc ((u - v).val : ℝ) * 2 = 2 * (u - v).val := by ring
        _ < p := by exact_mod_cast h
        _ = 1 * p := by ring
    have hround : round (((u - v).val : ℝ) / p) = 0 :=
      round_eq_zero_iff.mpr ⟨by linarith, hlt_half⟩
    rw [hround, Int.cast_zero, sub_zero, abs_of_nonneg hval_nonneg,
        distMod_eq_val_of_lt_half p u v h]
  · -- Case: (u - v).val ≥ p/2, so round = 1
    push_neg at h
    have hge_half : 1 / 2 ≤ ((u - v).val : ℝ) / p := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hp_pos]
      calc 1 * (p : ℝ) = p := by ring
        _ ≤ 2 * (u - v).val := by exact_mod_cast h
        _ = ((u - v).val : ℝ) * 2 := by ring
    have hround : round (((u - v).val : ℝ) / p) = 1 :=
      round_eq_one_of_mem_Ico ⟨hge_half, by linarith⟩
    rw [hround, Int.cast_one, abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [distMod_eq_p_sub_val p u v h, Nat.cast_sub (le_of_lt hval_lt)]
    field_simp

/-! ### Equivalence with Fraction Graphs -/

/-- The rounding map from Circle to ZMod p.
    Maps each point x to ⌊p * x̃⌋ where x̃ ∈ [0, 1) is the representative of x. -/
noncomputable def roundToZMod (p : ℕ) [NeZero p] (x : Circle) : ZMod p :=
  let x_rep : ℝ := (AddCircle.equivIco 1 0 x).val
  (Int.toNat ⌊p * x_rep⌋ : ZMod p)

/-- distMod of a value with itself is zero. -/
lemma distMod_self (p : ℕ) [NeZero p] (u : ZMod p) : distMod p u u = 0 := by
  simp only [distMod, sub_self, ZMod.val_zero, Nat.sub_zero, Nat.zero_min]

/-- Helper: Point u is in cell k iff k = roundToZMod p u, which means
    the representative of u is in [k.val/p, (k.val+1)/p). -/
lemma point_in_cell_bounds (p : ℕ) [hp : NeZero p] (u : Circle) :
    let x := (AddCircle.equivIco 1 0 u).val
    let k := roundToZMod p u
    (k.val : ℝ) / p ≤ x ∧ x < (k.val + 1 : ℕ) / p := by
  simp only [roundToZMod]
  set x := (AddCircle.equivIco 1 0 u).val
  have hx_ge : 0 ≤ x := (AddCircle.equivIco 1 0 u).prop.1
  have hx_lt : x < 1 := by simpa using (AddCircle.equivIco 1 0 u).prop.2
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
  have hfloor_ge : 0 ≤ ⌊(p : ℝ) * x⌋ := Int.floor_nonneg.mpr (by positivity)
  have hfloor_lt : ⌊(p : ℝ) * x⌋ < p := by
    rw [Int.floor_lt]
    calc (p : ℝ) * x < p * 1 := by apply mul_lt_mul_of_pos_left hx_lt hp_pos
      _ = p := mul_one _
  have hnat : (Int.toNat ⌊p * x⌋ : ZMod p).val = Int.toNat ⌊p * x⌋ := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    exact Int.toNat_lt hfloor_ge |>.mpr hfloor_lt
  have heq : (⌊p * x⌋ : ℝ) = (Int.toNat ⌊p * x⌋ : ℝ) := by
    have h := Int.toNat_of_nonneg hfloor_ge
    -- h : ↑(⌊p * x⌋.toNat) = ⌊p * x⌋ (as integers)
    calc (⌊p * x⌋ : ℝ) = ((⌊p * x⌋.toNat : ℤ) : ℝ) := by rw [h]
      _ = (⌊p * x⌋.toNat : ℝ) := by simp only [Int.cast_natCast]
  constructor
  · -- k.val / p ≤ x
    rw [hnat, div_le_iff₀ hp_pos]
    have := Int.floor_le (p * x)
    calc (Int.toNat ⌊p * x⌋ : ℝ) = ⌊p * x⌋ := heq.symm
      _ ≤ p * x := this
      _ = x * p := by ring
  · -- x < (k.val + 1) / p
    rw [hnat]
    rw [lt_div_iff₀ hp_pos]
    have := Int.lt_floor_add_one (p * x)
    calc x * p = p * x := by ring
      _ < ⌊p * x⌋ + 1 := this
      _ = (Int.toNat ⌊p * x⌋ : ℝ) + 1 := by rw [heq]
      _ = ((Int.toNat ⌊p * x⌋ + 1 : ℕ) : ℝ) := by norm_cast

-- Helper: ZMod subtraction when a.val < b.val (wrap-around case)
private lemma ZMod.val_sub' {n : ℕ} [NeZero n] {a b : ZMod n} (h : a.val < b.val) :
    (a - b).val = n - (b.val - a.val) := by
  have ha_lt : a.val < n := ZMod.val_lt a
  have hb_lt : b.val < n := ZMod.val_lt b
  have hb_ne : b ≠ 0 := by intro heq; simp only [heq, ZMod.val_zero] at h; omega
  haveI : NeZero b := ⟨hb_ne⟩
  rw [sub_eq_add_neg, ZMod.val_add, ZMod.val_neg_of_ne_zero b]
  have h_sum_lt : a.val + (n - b.val) < n := by omega
  rw [Nat.mod_eq_of_lt h_sum_lt]; omega

-- Helper: round x = 1 iff x ∈ [1/2, 3/2)
private lemma round_eq_one_iff' (x : ℝ) : round x = 1 ↔ (1/2 : ℝ) ≤ x ∧ x < 3/2 := by
  constructor
  · intro h
    have h0 : round (x - 1) = 0 := by rw [round_sub_one]; omega
    rw [round_eq_zero_iff, Set.mem_Ico] at h0; constructor <;> linarith
  · intro ⟨h1, h2⟩
    have h0 : round (x - 1) = 0 := by
      rw [round_eq_zero_iff, Set.mem_Ico]; constructor <;> linarith
    have := round_sub_one x; omega

-- Helper: round x = -1 iff x ∈ [-3/2, -1/2)
private lemma round_eq_neg_one_iff' (x : ℝ) : round x = -1 ↔ -(3/2 : ℝ) ≤ x ∧ x < -1/2 := by
  constructor
  · intro h
    have h0 : round (x + 1) = 0 := by rw [round_add_one]; omega
    rw [round_eq_zero_iff, Set.mem_Ico] at h0; constructor <;> linarith
  · intro ⟨h1, h2⟩
    have h0 : round (x + 1) = 0 := by
      rw [round_eq_zero_iff, Set.mem_Ico]; constructor <;> linarith
    have := round_add_one x; omega

/-- Key lemma: If cells k and l have distMod < d, then circleDistance < d/p.

    Proof idea: The rounding map partitions the circle into p cells [k/p, (k+1)/p).
    If two cells have distMod = m, then points in those cells have
    circleDistance < (m + 1)/p. So if distMod < d, then circleDistance < d/p.

    The proof involves case analysis on round(diff) where diff = x_u - x_v:
    - round = 0: |diff| < 1/2, bound by cell widths
    - round = 1: wrap-around case, diff ≥ 1/2
    - round = -1: wrap-around case, diff < -1/2 -/
lemma circleDistance_lt_of_cells_close (p : ℕ) [hp : NeZero p]
    (u v : Circle) (d : ℕ) (_hd_pos : 0 < d)
    (hd : distMod p (roundToZMod p u) (roundToZMod p v) < d) :
    circleDistance u v < (d : ℕ) / (p : ℝ) := by
  set k := roundToZMod p u
  set l := roundToZMod p v
  set m := distMod p k l
  have hm_lt : m < d := hd
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
  -- The key bound: circleDistance < (m+1)/p
  have hbound : circleDistance u v < (m + 1 : ℕ) / (p : ℝ) := by
    -- Setup: get representative coordinates
    set x_u := (AddCircle.equivIco 1 0 u).val
    set x_v := (AddCircle.equivIco 1 0 v).val
    obtain ⟨hk_le, hk_lt⟩ := point_in_cell_bounds p u
    obtain ⟨hl_le, hl_lt⟩ := point_in_cell_bounds p v
    have hx_u_ge : 0 ≤ x_u := (AddCircle.equivIco 1 0 u).prop.1
    have hx_u_lt : x_u < 1 := by simpa using (AddCircle.equivIco 1 0 u).prop.2
    have hx_v_ge : 0 ≤ x_v := (AddCircle.equivIco 1 0 v).prop.1
    have hx_v_lt : x_v < 1 := by simpa using (AddCircle.equivIco 1 0 v).prop.2
    -- Transform goal using UnitAddCircle.norm_eq
    unfold circleDistance
    rw [dist_eq_norm]
    have hquot : u - v = QuotientAddGroup.mk (x_u - x_v) := by
      have hu_eq : u = QuotientAddGroup.mk x_u := by
        have := (AddCircle.equivIco 1 0).symm_apply_apply u
        simp only [AddCircle.equivIco] at this; exact this.symm
      have hv_eq : v = QuotientAddGroup.mk x_v := by
        have := (AddCircle.equivIco 1 0).symm_apply_apply v
        simp only [AddCircle.equivIco] at this; exact this.symm
      simp only [hu_eq, hv_eq, QuotientAddGroup.mk_sub]
    rw [hquot, UnitAddCircle.norm_eq]
    -- Goal: |x_u - x_v - round(x_u - x_v)| < (m + 1) / p
    set diff := x_u - x_v
    have hdiff_bounds : -1 < diff ∧ diff < 1 := ⟨by linarith, by linarith⟩
    -- The circle distance |diff - round(diff)| is always ≤ 1/2
    have hcircle_dist_le_half : |diff - round diff| ≤ 1/2 := abs_sub_round diff
    -- Key strategy: when (m+1)/p > 1/2, use the universal bound |x - round x| ≤ 1/2
    -- When (m+1)/p ≤ 1/2, we need detailed geometric analysis
    by_cases hm_large : (m + 1 : ℕ) * 2 > p
    · -- (m+1)/p > 1/2, so circle distance ≤ 1/2 < (m+1)/p
      have h1 : (1 : ℝ) / 2 < (m + 1 : ℕ) / p := by
        rw [lt_div_iff₀ hp_pos]
        have h2 : (p : ℝ) / 2 < (m + 1 : ℕ) := by
          have hmul : p < (m + 1) * 2 := hm_large
          calc (p : ℝ) / 2 < ((m + 1) * 2 : ℕ) / 2 := by
                apply div_lt_div_of_pos_right (by exact_mod_cast hmul) (by norm_num : (0:ℝ) < 2)
            _ = ((m + 1 : ℕ) * 2) / 2 := by norm_cast
            _ = (m + 1 : ℕ) := by field_simp
        linarith
      calc |diff - round diff| ≤ 1/2 := hcircle_dist_le_half
        _ < (m + 1 : ℕ) / p := h1
    · -- (m+1)*2 ≤ p: cells are close, geometric argument
      -- Strategy: Show forward/backward arc < (m+1)/p using cell bounds
      push_neg at hm_large
      have hk_val_lt_p : k.val < p := ZMod.val_lt k
      have hl_val_lt_p : l.val < p := ZMod.val_lt l
      -- Case split on which direction is shorter
      by_cases h_fwd_short : 2 * (k - l).val ≤ p
      · -- Forward direction is shorter: m = (k-l).val
        have hm_eq : m = (k - l).val := by
          change distMod p k l = (k - l).val
          simp only [distMod, min_eq_left_iff]; omega
        -- Forward arc bound: diff (if ≥0) or diff+1 (if <0) < ((k-l).val + 1)/p
        -- When m = (k-l).val, we have (m+1)/p ≤ 1/2
        have h_fwd_le_half : ((k - l).val + 1 : ℕ) / (p : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hp_pos (by norm_num : (0:ℝ) < 2)]
          have hkl_lt : (k - l).val < p := ZMod.val_lt (k - l)
          have h : ((k - l).val + 1) * 2 ≤ p := by omega
          have hcast : (((k - l).val + 1) * 2 : ℕ) ≤ p := h
          calc (((k - l).val + 1 : ℕ) : ℝ) * 2 ≤ (p : ℝ) := by exact_mod_cast hcast
            _ = 1 * p := by ring
        by_cases hdiff_nonneg : diff ≥ 0
        · -- diff ≥ 0: forward arc = diff
          by_cases hlk : l.val ≤ k.val
          · -- Forward case: diff ≥ 0, l.val ≤ k.val
            have hkl_sub : (k - l).val = k.val - l.val := ZMod.val_sub hlk
            have h_fwd : diff < ((k - l).val + 1 : ℕ) / (p : ℝ) := by
              rw [hkl_sub]
              have h1 : diff < (k.val + 1 : ℕ) / (p : ℝ) - l.val / p := by linarith
              have hle : l.val ≤ k.val + 1 := Nat.le_add_right_of_le hlk
              have h2 : (k.val + 1 : ℕ) / (p : ℝ) - l.val / p = (k.val + 1 - l.val : ℕ) / p := by
                rw [← sub_div, ← Nat.cast_sub hle]
              have h3 : (k.val + 1 - l.val : ℕ) = k.val - l.val + 1 := by omega
              rw [h2, h3] at h1; exact h1
            have hdiff_lt_half : diff < 1 / 2 := lt_of_lt_of_le h_fwd h_fwd_le_half
            have hround0 : round diff = 0 := by
              rw [round_eq_zero_iff, Set.mem_Ico]; constructor <;> linarith
            simp only [hround0, Int.cast_zero, sub_zero, abs_of_nonneg hdiff_nonneg]
            calc diff < ((k - l).val + 1 : ℕ) / p := h_fwd
              _ = (m + 1 : ℕ) / p := by rw [hm_eq]
          · -- l.val > k.val with diff ≥ 0: show diff < 0, contradiction
            push_neg at hlk
            have h1 : x_v ≥ l.val / p := hl_le
            have h2 : x_u < (k.val + 1 : ℕ) / p := hk_lt
            have h3 : (k.val + 1 : ℕ) / (p : ℝ) ≤ l.val / p := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hp_pos); exact_mod_cast hlk
            linarith
        · -- diff < 0: forward arc = diff + 1
          push_neg at hdiff_nonneg
          by_cases hkl : k.val < l.val
          · -- Forward wrap: diff < 0, k.val < l.val
            have hkl_sub : (k - l).val = p - (l.val - k.val) := ZMod.val_sub' hkl
            have h_fwd : diff + 1 < ((k - l).val + 1 : ℕ) / (p : ℝ) := by
              rw [hkl_sub]
              have h1 : diff + 1 < (k.val + 1 : ℕ) / (p : ℝ) - l.val / p + 1 := by linarith
              have hlt2 : l.val - k.val ≤ p := by omega
              have h2 : (k.val + 1 : ℕ) / (p : ℝ) - l.val / p + 1 =
                  (p - (l.val - k.val) + 1 : ℕ) / p := by
                have heq : ((p - (l.val - k.val) + 1 : ℕ) : ℝ) = (p : ℝ) + k.val + 1 - l.val := by
                  have hnat_eq : (p - (l.val - k.val) + 1 : ℕ) = p + k.val + 1 - l.val := by omega
                  rw [hnat_eq]
                  rw [Nat.cast_sub (by omega : l.val ≤ p + k.val + 1)]
                  push_cast; ring
                rw [heq]; field_simp; push_cast; ring
              linarith
            have hfwd_lt_half : diff + 1 < 1 / 2 := lt_of_lt_of_le h_fwd h_fwd_le_half
            have hround_m1 : round diff = -1 := by
              rw [round_eq_neg_one_iff']; constructor <;> linarith [hdiff_bounds.1]
            simp only [hround_m1, Int.cast_neg, Int.cast_one, sub_neg_eq_add]
            rw [abs_of_nonneg (by linarith : 0 ≤ diff + 1)]
            calc diff + 1 < ((k - l).val + 1 : ℕ) / p := h_fwd
              _ = (m + 1 : ℕ) / p := by rw [hm_eq]
          · -- k.val ≥ l.val with diff < 0
            push_neg at hkl
            by_cases hkl_eq : k.val = l.val
            · -- Same cell
              have hm_zero : m = 0 := by
                have hk_eq_l : k = l := ZMod.val_injective p hkl_eq
                change distMod p k l = 0; rw [hk_eq_l, distMod_self]
              have hdiff_abs_small : |diff| < 1 / p := by
                rw [abs_lt]; constructor
                · have hu : x_u ≥ k.val / p := hk_le
                  have hv : x_v < (l.val + 1 : ℕ) / p := hl_lt
                  have h4 : (l.val + 1 : ℕ) / (p : ℝ) - l.val / p = 1 / p := by
                    rw [← sub_div]; congr 1; push_cast; ring
                  have hu' : x_u ≥ l.val / p := by rw [← hkl_eq]; exact hu
                  linarith
                · have hu : x_u < (k.val + 1 : ℕ) / p := hk_lt
                  have hv : x_v ≥ l.val / p := hl_le
                  have h4 : (k.val + 1 : ℕ) / (p : ℝ) - k.val / p = 1 / p := by
                    rw [← sub_div]; congr 1; push_cast; ring
                  have hv' : x_v ≥ k.val / p := by rw [hkl_eq]; exact hv
                  linarith
              have hp_ge_2 : p ≥ 2 := by
                by_contra h; push_neg at h
                have hp_lt_2 : p < 2 := h
                have hp_cases : p = 0 ∨ p = 1 := by omega
                rcases hp_cases with hp0 | hp1
                · exact (NeZero.ne p) hp0
                · -- When p = 1, we have (m+1)*2 ≤ 1, but m ≥ 0 so (m+1)*2 ≥ 2 > 1
                  subst hp1
                  have : (m + 1) * 2 ≥ 2 := by omega
                  omega
              have hp_inv_le : (1 : ℝ) / p ≤ 1 / 2 := by
                rw [div_le_div_iff₀ hp_pos (by norm_num : (0:ℝ) < 2)]
                have hcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge_2
                linarith
              have hround0 : round diff = 0 := by
                rw [round_eq_zero_iff, Set.mem_Ico]
                have := hdiff_abs_small; rw [abs_lt] at this; constructor <;> linarith
              simp only [hround0, Int.cast_zero, sub_zero]
              calc |diff| < 1 / p := hdiff_abs_small
                _ = (0 + 1 : ℕ) / p := by simp
                _ = (m + 1 : ℕ) / p := by rw [hm_zero]
            · -- k.val > l.val: diff > 0, contradiction
              have hkl_gt : k.val > l.val := Nat.lt_of_le_of_ne hkl (Ne.symm hkl_eq)
              have h1 : x_u ≥ k.val / p := hk_le
              have h2 : x_v < (l.val + 1 : ℕ) / p := hl_lt
              have h3 : (l.val + 1 : ℕ) / (p : ℝ) ≤ k.val / p := by
                apply div_le_div_of_nonneg_right _ (le_of_lt hp_pos); exact_mod_cast hkl_gt
              linarith
      · -- Backward direction is shorter: m = p - (k-l).val
        push_neg at h_fwd_short
        have hm_eq : m = p - (k - l).val := distMod_eq_p_sub_val p k l (le_of_lt h_fwd_short)
        -- (l-k).val = p - (k-l).val when k ≠ l
        have h_lk_eq : (l - k).val = p - (k - l).val := by
          have hkl_ne : k ≠ l := by
            intro heq; simp [heq] at h_fwd_short
          have h1 : (k - l).val < p := ZMod.val_lt (k - l)
          have h2 : (l - k).val < p := ZMod.val_lt (l - k)
          have h3 : k - l + (l - k) = 0 := by ring
          have h4 : ((k - l) + (l - k)).val = 0 := by simp [h3]
          have hsum : (k - l).val + (l - k).val = p ∨ (k - l).val + (l - k).val = 0 := by
            have hval_add := ZMod.val_add (k - l) (l - k)
            simp only [h3, ZMod.val_zero] at hval_add
            by_cases hlt : (k - l).val + (l - k).val < p
            · right; rw [Nat.mod_eq_of_lt hlt] at hval_add; exact hval_add.symm
            · left; push_neg at hlt
              have hlt2 : (k - l).val + (l - k).val < 2 * p := by
                have := Nat.add_lt_add h1 h2; omega
              -- sum ∈ [p, 2p) and sum % p = 0, so sum = p
              have hmod : ((k - l).val + (l - k).val) % p = 0 := hval_add.symm
              have hp_pos' : 0 < p := NeZero.pos p
              have hdvd := Nat.dvd_iff_mod_eq_zero.mpr hmod
              have hquot := Nat.div_mul_cancel hdvd
              have hq1 : ((k - l).val + (l - k).val) / p ≥ 1 :=
                (Nat.one_le_div_iff hp_pos').mpr hlt
              have hq2 : ((k - l).val + (l - k).val) / p < 2 := by
                rw [Nat.div_lt_iff_lt_mul hp_pos']; exact hlt2
              have hq_eq_1 : ((k - l).val + (l - k).val) / p = 1 := by omega
              rw [hq_eq_1, Nat.one_mul] at hquot
              exact hquot.symm
          rcases hsum with hsum_p | hsum_0
          · -- From (k-l).val + (l-k).val = p, get (l-k).val = p - (k-l).val
            have hkl_bound : (k - l).val ≤ p := le_of_lt h1
            omega
          · exfalso; have hkeql : k = l := by
              have hkl0 : (k - l).val = 0 := by omega
              have hsub0 : k - l = 0 := (ZMod.val_eq_zero (k - l)).mp hkl0
              exact sub_eq_zero.mp hsub0
            exact hkl_ne hkeql
        rw [← h_lk_eq] at hm_eq
        have h_bwd_le_half : ((l - k).val + 1 : ℕ) / (p : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hp_pos (by norm_num : (0:ℝ) < 2)]
          have hkl_val_pos : 0 < (k - l).val := by
            by_contra h; push_neg at h
            have hkl_val_zero : (k - l).val = 0 := Nat.eq_zero_of_le_zero h
            simp [hkl_val_zero] at h_fwd_short
          rw [h_lk_eq]
          have h : (p - (k - l).val + 1) * 2 ≤ p := by omega
          have hcast : (((p - (k - l).val + 1) * 2 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
          calc (((p - (k - l).val + 1 : ℕ)) : ℝ) * 2 ≤ (p : ℝ) := by exact_mod_cast h
            _ = 1 * p := by ring
        by_cases hdiff_nonpos : diff ≤ 0
        · -- diff ≤ 0: backward arc = -diff
          by_cases hkl : k.val ≤ l.val
          · -- Backward case: diff ≤ 0, k.val ≤ l.val
            have hlk_sub : (l - k).val = l.val - k.val := ZMod.val_sub hkl
            have h_bwd : -diff < ((l - k).val + 1 : ℕ) / (p : ℝ) := by
              rw [hlk_sub]
              have h1 : -diff < (l.val + 1 : ℕ) / (p : ℝ) - k.val / p := by linarith
              have hle : k.val ≤ l.val + 1 := Nat.le_add_right_of_le hkl
              have h2 : (l.val + 1 : ℕ) / (p : ℝ) - k.val / p = (l.val + 1 - k.val : ℕ) / p := by
                rw [← sub_div, ← Nat.cast_sub hle]
              have h3 : (l.val + 1 - k.val : ℕ) = l.val - k.val + 1 := by omega
              rw [h2, h3] at h1; exact h1
            have hdiff_gt_mhalf : -diff < 1 / 2 := lt_of_lt_of_le h_bwd h_bwd_le_half
            have hround0 : round diff = 0 := by
              rw [round_eq_zero_iff, Set.mem_Ico]; constructor <;> linarith
            simp only [hround0, Int.cast_zero, sub_zero, abs_of_nonpos hdiff_nonpos]
            calc -diff < ((l - k).val + 1 : ℕ) / p := h_bwd
              _ = (m + 1 : ℕ) / p := by rw [hm_eq]
          · -- k.val > l.val with diff ≤ 0: show diff > 0, contradiction
            push_neg at hkl
            have h1 : x_u ≥ k.val / p := hk_le
            have h2 : x_v < (l.val + 1 : ℕ) / p := hl_lt
            have h3 : (l.val + 1 : ℕ) / (p : ℝ) ≤ k.val / p := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hp_pos); exact_mod_cast hkl
            linarith
        · -- diff > 0: backward arc = 1 - diff
          push_neg at hdiff_nonpos
          by_cases hlk : l.val < k.val
          · -- Backward wrap: diff > 0, l.val < k.val
            have hlk_sub : (l - k).val = p - (k.val - l.val) := ZMod.val_sub' hlk
            have h_bwd : 1 - diff < ((l - k).val + 1 : ℕ) / (p : ℝ) := by
              rw [hlk_sub]
              have h1 : 1 - diff < 1 - (k.val / (p : ℝ) - (l.val + 1 : ℕ) / p) := by linarith
              have hlt2 : k.val ≤ p := le_of_lt hk_val_lt_p
              have hlt3 : k.val - l.val ≤ p := Nat.sub_le_of_le_add (by omega : k.val ≤ p + l.val)
              have hle_kval : k.val ≤ p + l.val + 1 := by omega
              have heq : 1 - (k.val / (p : ℝ) - (l.val + 1 : ℕ) / p) =
                  (p - (k.val - l.val) + 1 : ℕ) / p := by
                have hnat_eq : (p - (k.val - l.val) + 1 : ℕ) = p + l.val + 1 - k.val := by omega
                rw [hnat_eq]
                have hcast : ((p + l.val + 1 - k.val : ℕ) : ℝ) = (p : ℝ) + l.val + 1 - k.val := by
                  rw [Nat.cast_sub hle_kval]; push_cast; ring
                rw [hcast]
                field_simp; push_cast; ring
              linarith
            have hbwd_lt_half : 1 - diff < 1 / 2 := lt_of_lt_of_le h_bwd h_bwd_le_half
            have hround_1 : round diff = 1 := by
              rw [round_eq_one_iff']; constructor <;> linarith [hdiff_bounds.2]
            simp only [hround_1, Int.cast_one]
            rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 1 - diff)]
            calc 1 - diff < ((l - k).val + 1 : ℕ) / p := h_bwd
              _ = (m + 1 : ℕ) / p := by rw [hm_eq]
          · -- l.val ≥ k.val with diff > 0
            push_neg at hlk
            by_cases hlk_eq : l.val = k.val
            · -- Same cell
              have hm_zero : m = 0 := by
                have hl_eq_k : l = k := ZMod.val_injective p hlk_eq
                change distMod p k l = 0
                rw [hl_eq_k, distMod_self]
              have hdiff_abs_small : |diff| < 1 / p := by
                rw [abs_lt]; constructor
                · have hu : x_u ≥ k.val / p := hk_le
                  have hv : x_v < (l.val + 1 : ℕ) / p := hl_lt
                  have h4 : (l.val + 1 : ℕ) / (p : ℝ) - l.val / p = 1 / p := by
                    rw [← sub_div]; congr 1; push_cast; ring
                  have hu' : x_u ≥ l.val / p := by rw [hlk_eq]; exact hu
                  linarith
                · have hu : x_u < (k.val + 1 : ℕ) / p := hk_lt
                  have hv : x_v ≥ l.val / p := hl_le
                  have h4 : (l.val + 1 : ℕ) / (p : ℝ) - l.val / p = 1 / p := by
                    rw [← sub_div]; congr 1; push_cast; ring
                  have hu' : x_u < (l.val + 1 : ℕ) / p := by rw [hlk_eq]; exact hu
                  linarith
              have hp_ge_2 : p ≥ 2 := by
                by_contra h; push_neg at h
                have hp_01 : p = 0 ∨ p = 1 := by omega
                rcases hp_01 with hp0 | hp1
                · exact (NeZero.ne p) hp0
                · subst hp1
                  have hval : (k - l).val = 0 := by
                    have := ZMod.val_lt (k - l)
                    simp only [Nat.lt_one_iff] at this
                    exact this
                  omega
              have hp_inv_le : (1 : ℝ) / p ≤ 1 / 2 := by
                rw [div_le_div_iff₀ hp_pos (by norm_num : (0:ℝ) < 2)]
                have hcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge_2
                linarith
              have hround0 : round diff = 0 := by
                rw [round_eq_zero_iff, Set.mem_Ico]
                have := hdiff_abs_small; rw [abs_lt] at this; constructor <;> linarith
              simp only [hround0, Int.cast_zero, sub_zero]
              calc |diff| < 1 / p := hdiff_abs_small
                _ = (0 + 1 : ℕ) / p := by simp
                _ = (m + 1 : ℕ) / p := by rw [hm_zero]
            · -- l.val > k.val: diff < 0, contradiction
              have hlk_gt : l.val > k.val := Nat.lt_of_le_of_ne hlk (fun h => hlk_eq h.symm)
              have h1 : x_v ≥ l.val / p := hl_le
              have h2 : x_u < (k.val + 1 : ℕ) / p := hk_lt
              have h3 : (k.val + 1 : ℕ) / (p : ℝ) ≤ l.val / p := by
                apply div_le_div_of_nonneg_right _ (le_of_lt hp_pos); exact_mod_cast hlk_gt
              linarith
  calc circleDistance u v < (m + 1 : ℕ) / (p : ℝ) := hbound
    _ ≤ (d : ℕ) / (p : ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hp_pos)
        simp only [Nat.cast_add, Nat.cast_one]
        have : (m : ℝ) + 1 ≤ d := by exact_mod_cast Nat.succ_le_of_lt hm_lt
        linarith

/-- Cohomomorphism from open circle graph to fraction graph.
    The map rounds each point on the circle to floor(p*x).

    Proof: The roundToZMod map partitions the circle into p cells [k/p, (k+1)/p).
    If two points are in the same cell, their circle distance is < 1/p ≤ q/p = 1/r,
    so they are adjacent in the open circle graph (no constraint).
    If two points are in different cells at ZMod distance d, then their circle distance
    is at least (d-1)/p and at most (d+1)/p. For non-adjacent points with circleDistance ≥ q/p,
    we must have d ≥ q, so they are non-adjacent in the fraction graph. -/
theorem circleGraphOpen_to_fractionGraph (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    let r : ℝ := p / q
    let hr : 2 ≤ r := by
      have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
      calc (2 : ℝ) = 2 * q / q := by field_simp
        _ ≤ p / q := by apply div_le_div_of_nonneg_right (by exact_mod_cast h2q) (le_of_lt hq')
    Cohom (circleGraphOpen r hr) (fractionGraph p q) := by
  intro r hr
  use roundToZMod p
  intro u v huv hnadj
  -- hnadj: u ≠ v but not adjacent in E_r^o, i.e., circleDistance u v ≥ 1/r = q/p
  simp only [circleGraphOpen, ne_eq, not_and, not_lt] at hnadj
  have hcdist_ge : (q : ℝ) / p ≤ circleDistance u v := by
    have hr_eq : 1 / r = q / p := by simp only [one_div, r]; field_simp
    rw [← hr_eq]
    exact hnadj huv
  -- Need to show: roundToZMod p u ≠ roundToZMod p v ∧ ¬(fractionGraph p q).Adj ...
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  constructor
  · -- Show roundToZMod p u ≠ roundToZMod p v
    -- If they were equal (same cell), then circleDistance < 1/p ≤ q/p
    intro heq
    have hlt : circleDistance u v < (1 : ℕ) / (p : ℝ) := by
      apply circleDistance_lt_of_cells_close p u v 1 Nat.one_pos
      simp only [heq, distMod_self, Nat.lt_one_iff]
    simp only [Nat.cast_one] at hlt
    have h1q : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
    have hqp : 1 / (p : ℝ) ≤ q / p := by
      apply div_le_div_of_nonneg_right h1q (le_of_lt hp_pos)
    linarith
  · -- Show ¬(fractionGraph p q).Adj (roundToZMod p u) (roundToZMod p v)
    intro hadj
    simp only [fractionGraph] at hadj
    obtain ⟨_, hdm_lt⟩ := hadj
    -- hadj says distMod < q, so circleDistance < q/p by the key lemma
    have hlt : circleDistance u v < (q : ℕ) / (p : ℝ) :=
      circleDistance_lt_of_cells_close p u v q hq hdm_lt
    -- But we have hcdist_ge: q/p ≤ circleDistance u v, contradiction
    linarith

/-- Cohomomorphism from fraction graph to open circle graph.
    The map embeds vertex k as the point k/p on the circle.

    Proof: The embedding k ↦ k/p preserves non-adjacency because
    distMod(u,v) ≥ q implies circleDistance(u/p, v/p) = distMod/p ≥ q/p = 1/r. -/
theorem fractionGraph_to_circleGraphOpen (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    let r : ℝ := p / q
    let hr : 2 ≤ r := by
      have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
      calc (2 : ℝ) = 2 * q / q := by field_simp
        _ ≤ p / q := by apply div_le_div_of_nonneg_right (by exact_mod_cast h2q) (le_of_lt hq')
    Cohom (fractionGraph p q) (circleGraphOpen r hr) := by
  intro r hr
  use embedZMod p
  intro u v huv hnadj
  constructor
  · -- Show embedZMod p u ≠ embedZMod p v
    intro heq
    have hdist0 : dist (embedZMod p u) (embedZMod p v) = 0 := by rw [heq]; exact dist_self _
    rw [embedZMod_dist_eq] at hdist0
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
    have hdm0 : (distMod p u v : ℝ) = 0 := by
      cases div_eq_zero_iff.mp hdist0 with | inl h => exact h | inr h => linarith
    have hdm_nat : distMod p u v = 0 := by exact_mod_cast hdm0
    -- distMod = min((u-v).val, p - (u-v).val) = 0 means (u-v).val = 0
    simp only [distMod] at hdm_nat
    have hval_lt := ZMod.val_lt (u - v)
    have hval0 : (u - v).val = 0 := by
      rcases Nat.min_eq_zero_iff.mp hdm_nat with h1 | h2
      · exact h1
      · -- p - (u-v).val = 0 means (u-v).val = p, but (u-v).val < p
        omega
    have huv_eq : u - v = 0 := (ZMod.val_eq_zero (u - v)).mp hval0
    exact huv (sub_eq_zero.mp huv_eq)
  · -- Show ¬(circleGraphOpen r hr).Adj (embedZMod p u) (embedZMod p v)
    intro hadj
    obtain ⟨_, hdist_lt⟩ := hadj
    simp only [circleDistance] at hdist_lt
    rw [embedZMod_dist_eq] at hdist_lt
    -- hdist_lt: distMod p u v / p < 1/r = q/p
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hr_eq : 1 / r = q / p := by simp only [one_div, r]; field_simp
    rw [hr_eq] at hdist_lt
    have hdm_lt : (distMod p u v : ℝ) < q := by
      calc (distMod p u v : ℝ) = (distMod p u v : ℝ) / p * p := by field_simp
        _ < q / p * p := by apply mul_lt_mul_of_pos_right hdist_lt hp_pos
        _ = q := by field_simp
    have hdm_lt_nat : distMod p u v < q := by exact_mod_cast hdm_lt
    -- But hnadj says distMod p u v ≥ q
    simp only [fractionGraph, not_and, not_lt] at hnadj
    have hdm_ge : q ≤ distMod p u v := hnadj huv
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hdm_lt_nat hdm_ge)

/-- Lemma 4.4: The open circle graph E_{p/q}^o is equivalent to
    the fraction graph E_{p/q}. -/
theorem circleGraphOpen_equiv_fractionGraph (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    let r : ℝ := p / q
    let hr : 2 ≤ r := by
      have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
      calc (2 : ℝ) = 2 * q / q := by field_simp
        _ ≤ p / q := by apply div_le_div_of_nonneg_right (by exact_mod_cast h2q) (le_of_lt hq')
    -- E_{p/q}^o ≃ E_{p/q} (cohomomorphism in both directions)
    Cohom (circleGraphOpen r hr) (fractionGraph p q) ∧
    Cohom (fractionGraph p q) (circleGraphOpen r hr) :=
  ⟨circleGraphOpen_to_fractionGraph p q hq h2q, fractionGraph_to_circleGraphOpen p q hq h2q⟩

/-! ### Finite Induced Subgraphs -/

/-- Lemma 4.3: Any finite induced subgraph of
    E_r^c is cohomomorphically below some E_{a/b}^o with a/b < r.

    The key insight is that a finite set of points on the circle
    has a minimum pairwise distance, which is strictly positive. -/
theorem circleGraphClosed_finite_subgraph (r : ℝ) (hr : 2 < r)
    (S : Finset Circle) (_hS : S.Nonempty) :
    ∃ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h2b : 2 * b ≤ a) (_hab : (a : ℝ) / b < r),
      haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
      let hs : 2 ≤ (a : ℝ) / b := by
        have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
        calc (2 : ℝ) = 2 * b / b := by field_simp
          _ ≤ a / b := by apply div_le_div_of_nonneg_right (by exact_mod_cast h2b) (le_of_lt hb')
      Cohom ((circleGraphClosed r (le_of_lt hr)).induce (S : Set Circle))
               (circleGraphOpen ((a : ℝ) / b) hs) := by
  classical
  have hr' : 2 ≤ r := le_of_lt hr
  by_cases hnonadj :
      ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ (1 / r) < circleDistance u v
  · -- There is a non-adjacent pair; take the minimum such distance.
    let T : Finset (Circle × Circle) :=
      (S.product S).filter (fun uv => uv.1 ≠ uv.2 ∧ (1 / r) < circleDistance uv.1 uv.2)
    have hT_nonempty : T.Nonempty := by
      rcases hnonadj with ⟨u, hu, v, hv, huv, hdist⟩
      refine ⟨(u, v), ?_⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨hu, hv⟩
      · exact ⟨huv, hdist⟩
    let distSet : Finset ℝ := T.image (fun uv => circleDistance uv.1 uv.2)
    have hdist_nonempty : distSet.Nonempty := by
      rcases hT_nonempty with ⟨uv, huv⟩
      refine ⟨circleDistance uv.1 uv.2, ?_⟩
      exact Finset.mem_image.mpr ⟨uv, huv, rfl⟩
    let δ : ℝ := distSet.min' hdist_nonempty
    have hδ_gt : (1 / r) < δ := by
      have hlt : ∀ y ∈ distSet, (1 / r) < y := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨uv, huv, rfl⟩
        exact (Finset.mem_filter.mp huv).2.2
      have h :=
        (Finset.lt_min'_iff (s := distSet) (x := (1 / r)) (H := hdist_nonempty)).2 hlt
      simpa [δ] using h
    have hδ_pos : 0 < δ := by
      have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr'
      have hpos : 0 < (1 / r) := one_div_pos.mpr hr_pos
      exact lt_trans hpos hδ_gt
    have hδ_le_half : δ ≤ (1 / 2 : ℝ) := by
      rcases hT_nonempty with ⟨uv, huv⟩
      have hmem : circleDistance uv.1 uv.2 ∈ distSet := by
        exact Finset.mem_image.mpr ⟨uv, huv, rfl⟩
      have hmin_le : δ ≤ circleDistance uv.1 uv.2 := by
        simpa [δ] using (Finset.min'_le distSet _ hmem)
      exact hmin_le.trans (circleDistance_le_half _ _)
    let s : ℝ := 1 / δ
    have hs_lt_r : s < r := by
      have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr'
      have hpos : 0 < (1 / r) := one_div_pos.mpr hr_pos
      have h := one_div_lt_one_div_of_lt hpos hδ_gt
      simpa [s] using h
    have hs_ge_two : (2 : ℝ) ≤ s := by
      have h := one_div_le_one_div_of_le hδ_pos hδ_le_half
      simpa [s, one_div] using h
    have hε_pos : 0 < r - s := sub_pos.mpr hs_lt_r
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε_pos
    let b : ℕ := n + 1
    have hb : 0 < b := Nat.succ_pos _
    have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    have hb_lt : (1 : ℝ) / b < r - s := by
      simpa [b, Nat.cast_add, Nat.cast_one] using hn
    let a : ℕ := Nat.floor (s * b) + 1
    have ha : 0 < a := Nat.succ_pos _
    have hfloor_lt : s * b < (a : ℝ) := by
      simpa [a, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (s * b))
    have hfloor_le : (a : ℝ) ≤ s * b + 1 := by
      have hfloor_le' : (Nat.floor (s * b) : ℝ) ≤ s * b := by
        exact Nat.floor_le (by nlinarith : 0 ≤ s * b)
      have : (a : ℝ) ≤ s * b + 1 := by
        simpa [a, Nat.cast_add, Nat.cast_one] using (by linarith [hfloor_le'])
      exact this
    have hs_lt_ab : s < (a : ℝ) / b := by
      have := (lt_div_iff₀ hb_pos).2 hfloor_lt
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hab_le : (a : ℝ) / b ≤ s + (1 : ℝ) / b := by
      have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
      have hmul : (a : ℝ) ≤ (s + (1 : ℝ) / b) * b := by
        calc
          (a : ℝ) ≤ s * b + 1 := hfloor_le
          _ = s * b + (1 : ℝ) / b * b := by field_simp [hb_ne]
          _ = (s + (1 : ℝ) / b) * b := by ring
      exact (div_le_iff₀ hb_pos).2 hmul
    have hab : (a : ℝ) / b < r := by
      have hsum : s + (1 : ℝ) / b < r := by linarith
      exact lt_of_le_of_lt hab_le hsum
    have h2b : 2 * b ≤ a := by
      have h2_le : (2 : ℝ) ≤ (a : ℝ) / b := by
        exact hs_ge_two.trans hs_lt_ab.le
      have h2_mul' : (2 : ℝ) * b ≤ (a : ℝ) / b * b :=
        mul_le_mul_of_nonneg_right h2_le (le_of_lt hb_pos)
      have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
      have h2_mul : (2 : ℝ) * b ≤ a := by
        simpa [div_eq_mul_inv, hb_ne, mul_comm, mul_left_comm, mul_assoc] using h2_mul'
      have h2_mul_nat : ((2 * b : ℕ) : ℝ) ≤ (a : ℕ) := by
        simpa [Nat.cast_mul] using h2_mul
      exact (Nat.cast_le.1 h2_mul_nat)
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    refine ⟨a, b, ha, hb, h2b, hab, ?_⟩
    intro hs
    use Subtype.val
    intro u v huv hnadj
    constructor
    · exact fun h => huv (Subtype.ext h)
    · intro hadj
      have hnadj' : (1 / r) < circleDistance (u : Circle) v := by
        have : ¬(circleGraphClosed r hr').Adj (u : Circle) (v : Circle) := by
          simpa [SimpleGraph.induce_adj, circleGraphClosed] using hnadj
        simp only [circleGraphClosed, ne_eq, not_and, not_le] at this
        exact this (by simpa using huv)
      have hmemT : ((u : Circle), (v : Circle)) ∈ T := by
        refine Finset.mem_filter.mpr ?_
        refine ⟨?_, ?_⟩
        · exact Finset.mem_product.mpr ⟨u.property, v.property⟩
        · exact ⟨by simpa using huv, hnadj'⟩
      have hmemDist : circleDistance (u : Circle) (v : Circle) ∈ distSet := by
        exact Finset.mem_image.mpr ⟨((u : Circle), (v : Circle)), hmemT, rfl⟩
      have hδ_le : δ ≤ circleDistance (u : Circle) (v : Circle) := by
        simpa [δ] using (Finset.min'_le distSet _ hmemDist)
      have hs_pos : 0 < s := by
        have : 0 < (1 / δ) := one_div_pos.mpr hδ_pos
        simpa [s] using this
      have h_inv_lt : (1 : ℝ) / ((a : ℝ) / b) < δ := by
        have h := one_div_lt_one_div_of_lt hs_pos hs_lt_ab
        simpa [s] using h
      have h_inv_le : (1 : ℝ) / ((a : ℝ) / b) ≤ circleDistance (u : Circle) v :=
        h_inv_lt.le.trans hδ_le
      obtain ⟨_, hdist_lt⟩ := (hadj : (circleGraphOpen ((a : ℝ) / b) hs).Adj (u : Circle) v)
      exact (not_lt_of_ge h_inv_le) hdist_lt
  · -- All pairs in S are adjacent in E_r^c, so the induced graph is complete.
    have hcomplete :
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → circleDistance u v ≤ 1 / r := by
      intro u hu v hv huv
      by_contra hgt
      have hgt' : (1 / r) < circleDistance u v := lt_of_not_ge hgt
      exact hnonadj ⟨u, hu, v, hv, huv, hgt'⟩
    have hε_pos : 0 < r - 2 := by linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε_pos
    let b : ℕ := n + 1
    let a : ℕ := Nat.floor ((2 : ℝ) * b) + 1
    have hb : 0 < b := Nat.succ_pos _
    have ha : 0 < a := Nat.succ_pos _
    have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    have hfloor_lt : (2 : ℝ) * b < (a : ℝ) := by
      simpa [a, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one ((2 : ℝ) * b))
    have hfloor_le : (a : ℝ) ≤ (2 : ℝ) * b + 1 := by
      have hfloor_le' : (Nat.floor ((2 : ℝ) * b) : ℝ) ≤ (2 : ℝ) * b := by
        exact Nat.floor_le (by nlinarith : 0 ≤ (2 : ℝ) * b)
      have : (a : ℝ) ≤ (2 : ℝ) * b + 1 := by
        simpa [a, Nat.cast_add, Nat.cast_one] using (by linarith [hfloor_le'])
      exact this
    have hab_le : (a : ℝ) / b ≤ 2 + (1 : ℝ) / b := by
      have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
      have hmul : (a : ℝ) ≤ (2 + (1 : ℝ) / b) * b := by
        calc
          (a : ℝ) ≤ (2 : ℝ) * b + 1 := hfloor_le
          _ = (2 : ℝ) * b + (1 : ℝ) / b * b := by field_simp [hb_ne]
          _ = (2 + (1 : ℝ) / b) * b := by ring
      exact (div_le_iff₀ hb_pos).2 hmul
    have hab : (a : ℝ) / b < r := by
      have hb_lt : (1 : ℝ) / b < r - 2 := by
        simpa [b, Nat.cast_add, Nat.cast_one] using hn
      have hsum : 2 + (1 : ℝ) / b < r := by linarith
      exact lt_of_le_of_lt hab_le hsum
    have h2b : 2 * b ≤ a := by
      have h2_le : (2 : ℝ) ≤ (a : ℝ) / b := by
        have h2_lt : (2 : ℝ) < (a : ℝ) / b := by
          exact (lt_div_iff₀ hb_pos).2 hfloor_lt
        exact h2_lt.le
      have h2_mul' : (2 : ℝ) * b ≤ (a : ℝ) / b * b :=
        mul_le_mul_of_nonneg_right h2_le (le_of_lt hb_pos)
      have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
      have h2_mul : (2 : ℝ) * b ≤ a := by
        simpa [div_eq_mul_inv, hb_ne, mul_comm, mul_left_comm, mul_assoc] using h2_mul'
      have h2_mul_nat : ((2 * b : ℕ) : ℝ) ≤ (a : ℕ) := by
        simpa [Nat.cast_mul] using h2_mul
      exact (Nat.cast_le.1 h2_mul_nat)
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
    refine ⟨a, b, ha, hb, h2b, hab, ?_⟩
    intro hs
    use Subtype.val
    intro u v huv hnadj
    exfalso
    have hnadj' : ¬(circleGraphClosed r hr').Adj (u : Circle) (v : Circle) := by
      simpa [SimpleGraph.induce_adj] using hnadj
    have hdist_le : circleDistance (u : Circle) (v : Circle) ≤ 1 / r := by
      exact hcomplete _ u.property _ v.property (by simpa using huv)
    simp only [circleGraphClosed, ne_eq] at hnadj'
    push_neg at hnadj'
    exact (not_le_of_gt (hnadj' (by simpa using huv))) hdist_le

/-! ### Equidistant Points -/

/-- The set of N equidistant points on the circle: {0, 1/N, 2/N, ..., (N-1)/N}. -/
def equidistantPoints (N : ℕ) [NeZero N] : Set Circle :=
  {x : AddCircle 1 | ∃ k : ZMod N, x = embedZMod N k}

lemma equidistantPoints_eq_range (N : ℕ) [NeZero N] :
    equidistantPoints N = Set.range (embedZMod N) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

lemma equidistantPoints_finite (N : ℕ) [NeZero N] :
    (equidistantPoints N).Finite := by
  classical
  simpa [equidistantPoints_eq_range] using (Set.finite_range (embedZMod N))

/-- The distance between equidistant points is distMod(k,l)/N. -/
private lemma circleDistance_equidistant (N : ℕ) [NeZero N] (k l : ZMod N) :
    circleDistance (embedZMod N k) (embedZMod N l) =
    (distMod N k l : ℝ) / (N : ℝ) := by
  simpa [circleDistance] using (embedZMod_dist_eq N k l)

private lemma embedZMod_injective (N : ℕ) [NeZero N] : Function.Injective (embedZMod N) := by
  intro u v h
  have hdist0 : dist (embedZMod N u) (embedZMod N v) = 0 := by
    simp [h]
  rw [embedZMod_dist_eq] at hdist0
  have hdm0 : (distMod N u v : ℝ) = 0 := by
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    exact (div_eq_zero_iff.mp hdist0).resolve_right (ne_of_gt hN_pos)
  have hdm_nat : distMod N u v = 0 := by exact_mod_cast hdm0
  -- distMod = 0 implies u = v
  simp only [distMod] at hdm_nat
  have hval_lt := ZMod.val_lt (u - v)
  have hval0 : (u - v).val = 0 := by
    rcases Nat.min_eq_zero_iff.mp hdm_nat with h1 | h2
    · exact h1
    · omega
  have huv_eq : u - v = 0 := (ZMod.val_eq_zero (u - v)).mp hval0
  exact sub_eq_zero.mp huv_eq

noncomputable def equidistantPointsEquiv (N : ℕ) [NeZero N] : ZMod N ≃ equidistantPoints N :=
  Equiv.ofBijective
    (fun k => ⟨embedZMod N k, ⟨k, rfl⟩⟩)
    (by
      constructor
      · intro a b h
        have h' : embedZMod N a = embedZMod N b := congrArg Subtype.val h
        exact embedZMod_injective N h'
      · intro x
        rcases x.property with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext
        simp [hk])

/-- Lemma 5.4: For N equidistant points on the circle, the induced subgraph
    of E_r^o is isomorphic to the fraction graph E_{N/q} where q = ⌈N/r⌉.

    Key insight:
    - Points k/N and l/N are adjacent in E_r^o iff d(k/N, l/N) < 1/r
    - d(k/N, l/N) = distMod(k, l) / N
    - So adjacent iff distMod(k, l) < N/r
    - This matches E_{N/q} with q = ⌈N/r⌉ since distMod < N/r ⟺ distMod < q -/
theorem circleGraph_equidistant_induced_open
    (r : ℝ) (hr : 2 ≤ r) (N : ℕ) [NeZero N] (_hN : 2 ≤ N) :
    ∃ (_iso : (circleGraphOpen r hr).induce (equidistantPoints N) ≃g
      fractionGraph N (Nat.ceil ((N : ℝ) / r))), True := by
  -- q = ⌈N/r⌉
  let q := Nat.ceil ((N : ℝ) / r)
  -- The isomorphism sends embedZMod k ↦ k.
  let e := equidistantPointsEquiv N
  have hIso :
      (circleGraphOpen r hr).induce (equidistantPoints N) ≃g fractionGraph N q := by
    refine ⟨e.symm, ?_⟩
    intro a b
    have ha : (a : Circle) = embedZMod N (e.symm a) := by
      have := congrArg Subtype.val (e.apply_symm_apply a)
      exact this.symm
    have hb : (b : Circle) = embedZMod N (e.symm b) := by
      have := congrArg Subtype.val (e.apply_symm_apply b)
      exact this.symm
    have hne : (a : Circle) ≠ b ↔ e.symm a ≠ e.symm b := by
      constructor
      · intro h hkl
        exact h (congrArg Subtype.val (e.symm.injective hkl))
      · intro h hkl
        have hab : a = b := Subtype.ext hkl
        exact h (congrArg e.symm hab)
    have hdist :
        circleDistance (embedZMod N (e.symm a)) (embedZMod N (e.symm b)) < 1 / r ↔
          distMod N (e.symm a) (e.symm b) < q := by
      have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
      have h1 :
          (distMod N (e.symm a) (e.symm b) : ℝ) / (N : ℝ) < 1 / r ↔
            (distMod N (e.symm a) (e.symm b) : ℝ) < (N : ℝ) / r := by
        have h' :
            (distMod N (e.symm a) (e.symm b) : ℝ) / (N : ℝ) < 1 / r ↔
              (distMod N (e.symm a) (e.symm b) : ℝ) < (1 / r) * (N : ℝ) := by
          simpa using
            (div_lt_iff₀ (b := (distMod N (e.symm a) (e.symm b) : ℝ))
              (c := (N : ℝ)) (a := (1 / r)) hN_pos)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
      have h2 :
          distMod N (e.symm a) (e.symm b) < q ↔
            (distMod N (e.symm a) (e.symm b) : ℝ) < (N : ℝ) / r := by
        simpa [q] using
          (Nat.lt_ceil (n := distMod N (e.symm a) (e.symm b)) (a := (N : ℝ) / r))
      have hdist_eq := circleDistance_equidistant N (e.symm a) (e.symm b)
      constructor
      · intro h
        have h' : (distMod N (e.symm a) (e.symm b) : ℝ) / (N : ℝ) < 1 / r := by
          simpa [hdist_eq] using h
        exact (h2.mpr (h1.mp h'))
      · intro h
        have h' : (distMod N (e.symm a) (e.symm b) : ℝ) < (N : ℝ) / r := h2.mp h
        have h'' : (distMod N (e.symm a) (e.symm b) : ℝ) / (N : ℝ) < 1 / r := h1.mpr h'
        simpa [hdist_eq] using h''
    have hiff :
        ((circleGraphOpen r hr).induce (equidistantPoints N)).Adj a b ↔
          (fractionGraph N q).Adj (e.symm a) (e.symm b) := by
      constructor
      · intro hadj
        have hadj' : (a : Circle) ≠ b ∧ circleDistance (a : Circle) (b : Circle) < 1 / r := by
          simpa [SimpleGraph.induce_adj, circleGraphOpen] using hadj
        have hdist' : distMod N (e.symm a) (e.symm b) < q := by
          have : circleDistance (embedZMod N (e.symm a)) (embedZMod N (e.symm b)) < 1 / r := by
            simpa [ha, hb] using hadj'.2
          exact (hdist.mp this)
        have hne' : e.symm a ≠ e.symm b := hne.mp hadj'.1
        simpa [fractionGraph] using And.intro hne' hdist'
      · intro hadj
        have hadj' : e.symm a ≠ e.symm b ∧ distMod N (e.symm a) (e.symm b) < q := by
          simpa [fractionGraph] using hadj
        have hdist' :
            circleDistance (embedZMod N (e.symm a)) (embedZMod N (e.symm b)) < 1 / r :=
          hdist.mpr hadj'.2
        have hne' : (a : Circle) ≠ b := hne.mpr hadj'.1
        have : (a : Circle) ≠ b ∧ circleDistance (a : Circle) (b : Circle) < 1 / r := by
          refine ⟨hne', ?_⟩
          simpa [ha, hb] using hdist'
        simpa [SimpleGraph.induce_adj, circleGraphOpen] using this
    exact hiff.symm
  refine ⟨?_, trivial⟩
  simpa [q] using hIso

/-- Lemma 5.4: For N equidistant points, E_r^c[S_N] ≅ E_{N/q} where q = ⌊N/r⌋ + 1.

    Key insight:
    - Points k/N and l/N are adjacent in E_r^c iff d(k/N, l/N) ≤ 1/r
    - This gives distMod(k, l) ≤ N/r
    - For integer distMod, this is distMod ≤ ⌊N/r⌋ ⟺ distMod < ⌊N/r⌋ + 1 -/
theorem circleGraph_equidistant_induced_closed
    (r : ℝ) (hr : 2 ≤ r) (N : ℕ) [NeZero N] (_hN : 2 ≤ N) :
    ∃ (_iso : (circleGraphClosed r hr).induce (equidistantPoints N) ≃g
      fractionGraph N (Nat.floor ((N : ℝ) / r) + 1)), True := by
  -- q = ⌊N/r⌋ + 1
  let q := Nat.floor ((N : ℝ) / r) + 1
  let e := equidistantPointsEquiv N
  have hIso :
      (circleGraphClosed r hr).induce (equidistantPoints N) ≃g fractionGraph N q := by
    refine ⟨e.symm, ?_⟩
    intro a b
    have ha : (a : Circle) = embedZMod N (e.symm a) := by
      have := congrArg Subtype.val (e.apply_symm_apply a)
      exact this.symm
    have hb : (b : Circle) = embedZMod N (e.symm b) := by
      have := congrArg Subtype.val (e.apply_symm_apply b)
      exact this.symm
    have hne : (a : Circle) ≠ b ↔ e.symm a ≠ e.symm b := by
      constructor
      · intro h hkl
        exact h (congrArg Subtype.val (e.symm.injective hkl))
      · intro h hkl
        have hab : a = b := Subtype.ext hkl
        exact h (congrArg e.symm hab)
    have hdist :
        circleDistance (embedZMod N (e.symm a)) (embedZMod N (e.symm b)) ≤ 1 / r ↔
          distMod N (e.symm a) (e.symm b) < q := by
      have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
      have h1 :
          (distMod N (e.symm a) (e.symm b) : ℝ) / (N : ℝ) ≤ 1 / r ↔
            (distMod N (e.symm a) (e.symm b) : ℝ) ≤ (N : ℝ) / r := by
        have h' :
            (distMod N (e.symm a) (e.symm b) : ℝ) / (N : ℝ) ≤ 1 / r ↔
              (distMod N (e.symm a) (e.symm b) : ℝ) ≤ (1 / r) * (N : ℝ) := by
          simpa using
            (div_le_iff₀ (b := (distMod N (e.symm a) (e.symm b) : ℝ))
              (c := (N : ℝ)) (a := (1 / r)) hN_pos)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
      have h2 :
          distMod N (e.symm a) (e.symm b) < q ↔
            (distMod N (e.symm a) (e.symm b) : ℝ) ≤ (N : ℝ) / r := by
        have hnr_pos : (0 : ℝ) ≤ (N : ℝ) / r := by
          have hN_pos' : (0 : ℝ) ≤ (N : ℝ) := le_of_lt (Nat.cast_pos.mpr (NeZero.pos N))
          have hr_pos' : (0 : ℝ) ≤ r := le_of_lt (by linarith : (0 : ℝ) < r)
          exact div_nonneg hN_pos' hr_pos'
        constructor
        · intro h
          have h' : distMod N (e.symm a) (e.symm b) ≤ Nat.floor ((N : ℝ) / r) := by
            exact Nat.lt_succ_iff.mp (by simpa [q] using h)
          exact (Nat.le_floor_iff hnr_pos).1 h'
        · intro h
          have h' : distMod N (e.symm a) (e.symm b) ≤ Nat.floor ((N : ℝ) / r) := by
            exact (Nat.le_floor_iff hnr_pos).2 h
          have h'' :
              distMod N (e.symm a) (e.symm b) < Nat.floor ((N : ℝ) / r) + 1 :=
            (Nat.lt_succ_iff.mpr h')
          simpa [q] using h''
      have hdist_eq := circleDistance_equidistant N (e.symm a) (e.symm b)
      constructor
      · intro h
        have h' : (distMod N (e.symm a) (e.symm b) : ℝ) / (N : ℝ) ≤ 1 / r := by
          simpa [hdist_eq] using h
        exact (h2.mpr (h1.mp h'))
      · intro h
        have h' : (distMod N (e.symm a) (e.symm b) : ℝ) ≤ (N : ℝ) / r := h2.mp h
        have h'' : (distMod N (e.symm a) (e.symm b) : ℝ) / (N : ℝ) ≤ 1 / r := h1.mpr h'
        simpa [hdist_eq] using h''
    have hiff :
        ((circleGraphClosed r hr).induce (equidistantPoints N)).Adj a b ↔
          (fractionGraph N q).Adj (e.symm a) (e.symm b) := by
      constructor
      · intro hadj
        have hadj' : (a : Circle) ≠ b ∧ circleDistance (a : Circle) (b : Circle) ≤ 1 / r := by
          simpa [SimpleGraph.induce_adj, circleGraphClosed] using hadj
        have hdist' : distMod N (e.symm a) (e.symm b) < q := by
          have : circleDistance (embedZMod N (e.symm a)) (embedZMod N (e.symm b)) ≤ 1 / r := by
            simpa [ha, hb] using hadj'.2
          exact (hdist.mp this)
        have hne' : e.symm a ≠ e.symm b := hne.mp hadj'.1
        simpa [fractionGraph] using And.intro hne' hdist'
      · intro hadj
        have hadj' : e.symm a ≠ e.symm b ∧ distMod N (e.symm a) (e.symm b) < q := by
          simpa [fractionGraph] using hadj
        have hdist' :
            circleDistance (embedZMod N (e.symm a)) (embedZMod N (e.symm b)) ≤ 1 / r :=
          hdist.mpr hadj'.2
        have hne' : (a : Circle) ≠ b := hne.mpr hadj'.1
        have : (a : Circle) ≠ b ∧ circleDistance (a : Circle) (b : Circle) ≤ 1 / r := by
          refine ⟨hne', ?_⟩
          simpa [ha, hb] using hdist'
        simpa [SimpleGraph.induce_adj, circleGraphClosed] using this
    exact hiff.symm
  refine ⟨?_, trivial⟩
  simpa [q] using hIso

/-- Rounding to equidistant points gives a cohomomorphism.

    The rounding map sends each circle point to the nearest equidistant point.
    This is a cohomomorphism because it only decreases distances. -/
theorem circleGraph_rounding_cohom (r : ℝ) (hr : 2 ≤ r) (N : ℕ) [NeZero N]
    (_hN : 2 ≤ N) (hNr : r ≤ (N : ℝ)) :
    ∃ (q : ℕ), 0 < q ∧
      Cohom (circleGraphOpen r hr) (fractionGraph N q) ∧
      Cohom (circleGraphClosed r hr) (fractionGraph N q) := by
  let q := Nat.floor ((N : ℝ) / r)
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
  have hq_pos : 0 < q := by
    have hNr' : (1 : ℝ) ≤ (N : ℝ) / r := by
      have h1 : (1 : ℝ) = r / r := by field_simp [hr_pos.ne']
      have hdiv : (r : ℝ) / r ≤ (N : ℝ) / r :=
        (div_le_div_of_nonneg_right hNr (le_of_lt hr_pos))
      simpa [h1] using hdiv
    have hq_ge1 : 1 ≤ q := (Nat.one_le_floor_iff _).2 hNr'
    exact lt_of_lt_of_le Nat.zero_lt_one hq_ge1
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hq_le : (q : ℝ) ≤ (N : ℝ) / r := by
    have hnonneg : 0 ≤ (N : ℝ) / r := by
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hr_pos)
    exact Nat.floor_le hnonneg
  have hq_div_le : (q : ℝ) / N ≤ 1 / r := by
    have := (div_le_div_of_nonneg_right hq_le (le_of_lt hN_pos))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  refine ⟨q, hq_pos, ?_, ?_⟩
  · -- Open case
    use roundToZMod N
    intro u v huv hnadj
    constructor
    · intro heq
      have hdm_lt :
          distMod N (roundToZMod N u) (roundToZMod N v) < q := by
        simpa [heq, distMod_self] using hq_pos
      have hlt : circleDistance u v < (q : ℕ) / (N : ℝ) :=
        circleDistance_lt_of_cells_close N u v q hq_pos hdm_lt
      have hlt' : circleDistance u v < 1 / r := lt_of_lt_of_le hlt hq_div_le
      simp only [circleGraphOpen, ne_eq, not_and, not_lt] at hnadj
      exact (not_lt_of_ge (hnadj huv)) hlt'
    · intro hadj
      simp only [fractionGraph] at hadj
      obtain ⟨_, hdm_lt⟩ := hadj
      have hlt : circleDistance u v < (q : ℕ) / (N : ℝ) :=
        circleDistance_lt_of_cells_close N u v q hq_pos hdm_lt
      have hlt' : circleDistance u v < 1 / r := lt_of_lt_of_le hlt hq_div_le
      simp only [circleGraphOpen, ne_eq, not_and, not_lt] at hnadj
      exact (not_lt_of_ge (hnadj huv)) hlt'
  · -- Closed case
    use roundToZMod N
    intro u v huv hnadj
    constructor
    · intro heq
      have hdm_lt :
          distMod N (roundToZMod N u) (roundToZMod N v) < q := by
        simpa [heq, distMod_self] using hq_pos
      have hlt : circleDistance u v < (q : ℕ) / (N : ℝ) :=
        circleDistance_lt_of_cells_close N u v q hq_pos hdm_lt
      have hlt' : circleDistance u v < 1 / r := lt_of_lt_of_le hlt hq_div_le
      simp only [circleGraphClosed, ne_eq, not_and, not_le] at hnadj
      exact (lt_asymm hlt' (hnadj huv))
    · intro hadj
      simp only [fractionGraph] at hadj
      obtain ⟨_, hdm_lt⟩ := hadj
      have hlt : circleDistance u v < (q : ℕ) / (N : ℝ) :=
        circleDistance_lt_of_cells_close N u v q hq_pos hdm_lt
      have hlt' : circleDistance u v < 1 / r := lt_of_lt_of_le hlt hq_div_le
      simp only [circleGraphClosed, ne_eq, not_and, not_le] at hnadj
      exact (lt_asymm hlt' (hnadj huv))

theorem circleGraph_rounding_cohom_floor (r : ℝ) (hr : 2 ≤ r) (N : ℕ) [NeZero N]
    (_hN : 2 ≤ N) (hNr : r ≤ (N : ℝ)) :
    0 < Nat.floor ((N : ℝ) / r) ∧
      Cohom (circleGraphOpen r hr) (fractionGraph N (Nat.floor ((N : ℝ) / r))) ∧
      Cohom (circleGraphClosed r hr) (fractionGraph N (Nat.floor ((N : ℝ) / r))) := by
  let q := Nat.floor ((N : ℝ) / r)
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
  have hq_pos : 0 < q := by
    have hNr' : (1 : ℝ) ≤ (N : ℝ) / r := by
      have h1 : (1 : ℝ) = r / r := by field_simp [hr_pos.ne']
      have hdiv : (r : ℝ) / r ≤ (N : ℝ) / r :=
        (div_le_div_of_nonneg_right hNr (le_of_lt hr_pos))
      simpa [h1] using hdiv
    have hq_ge1 : 1 ≤ q := (Nat.one_le_floor_iff _).2 hNr'
    exact lt_of_lt_of_le Nat.zero_lt_one hq_ge1
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hq_le : (q : ℝ) ≤ (N : ℝ) / r := by
    have hnonneg : 0 ≤ (N : ℝ) / r := by
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hr_pos)
    exact Nat.floor_le hnonneg
  have hq_div_le : (q : ℝ) / N ≤ 1 / r := by
    have := (div_le_div_of_nonneg_right hq_le (le_of_lt hN_pos))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  refine ⟨hq_pos, ?_, ?_⟩
  · -- Open case
    use roundToZMod N
    intro u v huv hnadj
    constructor
    · intro heq
      have hdm_lt :
          distMod N (roundToZMod N u) (roundToZMod N v) < q := by
        simpa [heq, distMod_self] using hq_pos
      have hlt : circleDistance u v < (q : ℕ) / (N : ℝ) :=
        circleDistance_lt_of_cells_close N u v q hq_pos hdm_lt
      have hlt' : circleDistance u v < 1 / r := lt_of_lt_of_le hlt hq_div_le
      simp only [circleGraphOpen, ne_eq, not_and, not_lt] at hnadj
      exact (not_lt_of_ge (hnadj huv)) hlt'
    · intro hadj
      simp only [fractionGraph] at hadj
      obtain ⟨_, hdm_lt⟩ := hadj
      have hlt : circleDistance u v < (q : ℕ) / (N : ℝ) :=
        circleDistance_lt_of_cells_close N u v q hq_pos hdm_lt
      have hlt' : circleDistance u v < 1 / r := lt_of_lt_of_le hlt hq_div_le
      simp only [circleGraphOpen, ne_eq, not_and, not_lt] at hnadj
      exact (not_lt_of_ge (hnadj huv)) hlt'
  · -- Closed case
    use roundToZMod N
    intro u v huv hnadj
    constructor
    · intro heq
      have hdm_lt :
          distMod N (roundToZMod N u) (roundToZMod N v) < q := by
        simpa [heq, distMod_self] using hq_pos
      have hlt : circleDistance u v < (q : ℕ) / (N : ℝ) :=
        circleDistance_lt_of_cells_close N u v q hq_pos hdm_lt
      have hlt' : circleDistance u v < 1 / r := lt_of_lt_of_le hlt hq_div_le
      simp only [circleGraphClosed, ne_eq, not_and, not_le] at hnadj
      exact (lt_asymm hlt' (hnadj huv))
    · intro hadj
      simp only [fractionGraph] at hadj
      obtain ⟨_, hdm_lt⟩ := hadj
      have hlt : circleDistance u v < (q : ℕ) / (N : ℝ) :=
        circleDistance_lt_of_cells_close N u v q hq_pos hdm_lt
      have hlt' : circleDistance u v < 1 / r := lt_of_lt_of_le hlt hq_div_le
      simp only [circleGraphClosed, ne_eq, not_and, not_le] at hnadj
      exact (lt_asymm hlt' (hnadj huv))

/-! ### Infinite Graph Structure -/

/-- The fraction graph has a trivial clique cover: each vertex is its own clique.
    The function v ↦ v.val sends each vertex to a distinct Fin p. -/
theorem fractionGraph_cliqueCover (p q : ℕ) [hp : NeZero p] :
    IsCliqueCover (fractionGraph p q) (fun v : ZMod p => (⟨v.val, ZMod.val_lt v⟩ : Fin p)) := by
  intro u v heq
  -- heq says u.val = v.val (as elements of Fin p)
  left
  have huv : u.val = v.val := by simp only [Fin.mk.injEq] at heq; exact heq
  exact ZMod.val_injective p huv

/-- Circle graphs have finite clique covering number.
    Proof: Use the cohomomorphism E_r^o → E_{N/q} (from circleGraph_rounding_cohom)
    and pull back the clique cover from the finite fraction graph. -/
theorem circleGraphOpen_finite_cliqueCover (r : ℝ) (hr : 2 ≤ r) :
    ∃ n : ℕ, ∃ f : Circle → Fin n, IsCliqueCover (circleGraphOpen r hr) f := by
  -- Use circleGraph_rounding_cohom to get a cohomomorphism to a fraction graph
  let N : ℕ := Nat.ceil r
  have hNr : r ≤ (N : ℝ) := by
    simpa [N] using (Nat.le_ceil (a := r))
  have hN : 2 ≤ N := by
    have hN' : (2 : ℝ) ≤ N := le_trans hr hNr
    exact_mod_cast hN'
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hN
  haveI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  obtain ⟨q, _, hcohom_open, _⟩ := circleGraph_rounding_cohom r hr N hN hNr
  -- hcohom_open : Cohom (circleGraphOpen r hr) (fractionGraph N q)
  obtain ⟨φ, hφ⟩ := hcohom_open
  -- φ : Circle → ZMod N is the cohomomorphism
  -- The fraction graph on ZMod N has N vertices
  -- Use fractionGraph_cliqueCover for the clique cover of the fraction graph
  use N
  let c : ZMod N → Fin N := fun v => ⟨v.val, ZMod.val_lt v⟩
  use c ∘ φ
  exact cliqueCover_of_cohom φ hφ (fractionGraph_cliqueCover N q)

/-- Closed circle graphs have finite clique covering number. -/
theorem circleGraphClosed_finite_cliqueCover (r : ℝ) (hr : 2 ≤ r) :
    ∃ n : ℕ, ∃ f : Circle → Fin n, IsCliqueCover (circleGraphClosed r hr) f := by
  -- Use circleGraph_rounding_cohom to get a cohomomorphism to a fraction graph
  let N : ℕ := Nat.ceil r
  have hNr : r ≤ (N : ℝ) := by
    simpa [N] using (Nat.le_ceil (a := r))
  have hN : 2 ≤ N := by
    have hN' : (2 : ℝ) ≤ N := le_trans hr hNr
    exact_mod_cast hN'
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hN
  haveI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  obtain ⟨q, _, _, hcohom_closed⟩ := circleGraph_rounding_cohom r hr N hN hNr
  -- hcohom_closed : Cohom (circleGraphClosed r hr) (fractionGraph N q)
  obtain ⟨φ, hφ⟩ := hcohom_closed
  use N
  let c : ZMod N → Fin N := fun v => ⟨v.val, ZMod.val_lt v⟩
  use c ∘ φ
  exact cliqueCover_of_cohom φ hφ (fractionGraph_cliqueCover N q)

/-- The open circle graph as an InfiniteGraph. -/
def circleGraphOpenInf (r : ℝ) (hr : 2 ≤ r) : InfiniteGraph where
  V := Circle
  graph := circleGraphOpen r hr
  cliqueCover_finite := circleGraphOpen_finite_cliqueCover r hr

/-- The closed circle graph as an InfiniteGraph. -/
def circleGraphClosedInf (r : ℝ) (hr : 2 ≤ r) : InfiniteGraph where
  V := Circle
  graph := circleGraphClosed r hr
  cliqueCover_finite := circleGraphClosed_finite_cliqueCover r hr

/-- The open circle graph `E_{p/q}^o` for a positive rational `p/q > 2`. -/
noncomputable def circleGraphOpenInfPNat (p q : ℕ+) (h2q : 2 * q < p) : InfiniteGraph :=
  circleGraphOpenInf ((p : ℝ) / q) (by
    rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q)

/-- The closed circle graph `E_{p/q}^c` for a positive rational `p/q > 2`. -/
noncomputable def circleGraphClosedInfPNat (p q : ℕ+) (h2q : 2 * q < p) : InfiniteGraph :=
  circleGraphClosedInf ((p : ℝ) / q) (by
    rw [le_div_iff₀ (Nat.cast_pos.mpr q.pos)]; exact_mod_cast le_of_lt h2q)

end AsymptoticSpectrumDistance
