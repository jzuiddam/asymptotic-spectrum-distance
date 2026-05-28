/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section5.SelfCohom
import AsymptoticSpectrumDistance.Section4.CircleGraphLimits
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
-- Imports for covering map theory (Theorem 5.6)
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
-- Imports for integral argument (Lemma 5.4)
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unnecessarySimpa false

namespace AsymptoticSpectrumDistance

open Universality AsymptoticSpectrumGraphs SimpleGraph FractionGraphBasic

/-! ### Gap Lemma for Non-Surjectivity of Rounding -/

/-- Key gap existence lemma: If f(y) and f(x) are far apart (dist > 2/a) and both
    share the same "skeleton" (the other a1-1 points in S_y and S_x), then f(S_y)
    must have a gap > 1/a.

    Proof outline (from Lemma 5.5):
    - S_y = {y, s_1, ..., s_{a1-1}} and S_x = {x, s_1, ..., s_{a1-1}} share skeleton
    - f(S_y) has a1 points in cyclic order on Circle (since it induces E_{a1/q})
    - By fractionGraph_selfCohom_form, automorphisms are rotations/reflections
    - So the cyclic order is (f(y), f(s_1), ..., f(s_{a1-1})) or its reverse
    - f(y) has two cyclic neighbors: f(s_{a1-1}) and f(s_1) (or their image under reflection)
    - The "slot" from f(s_{a1-1}) through f(y) to f(s_1) has width = gap_left + gap_right
    - Since x is also between s_{a1-1} and s_1 in the original (skeleton shared), f(x) is
      in the same slot (between f(s_{a1-1}) and f(s_1))
    - If all gaps ≤ 1/a, then slot width ≤ 2/a, so dist(f(y), f(x)) ≤ 2/a
    - Contrapositive: dist > 2/a implies some gap > 1/a

    Note: The "skeleton" is preserved because S_y \ {y} = S_x \ {x} = {s_1, ..., s_{a1-1}}.
    Both y and x are in the same position relative to the skeleton, so their images
    f(y) and f(x) are in the same "slot" between skeleton neighbors. -/
private lemma gap_exists_of_dist_gt
    (G : SimpleGraph Circle)
    (a a1 : ℕ) [NeZero a] [NeZero a1]
    (S_y : Set Circle) (hS_y_finite : S_y.Finite) (hcard : hS_y_finite.toFinset.card = a1)
    (y x : Circle) (hy : y ∈ S_y) (hx_ne_y : x ≠ y)
    -- S_x shares skeleton with S_y: S_x = insert x (S_y \ {y})
    (S_x : Set Circle) (hS_x : S_x = insert x (S_y \ {y}))
    (f : Circle → Circle)
    (ha_ge : 3 ≤ a) (ha1_ge : 3 ≤ a1)
    -- f(S_y) induces E_{a1/q} in graph G (open or closed)
    (q : ℕ) (hq_ge : 2 ≤ q) (hq_pos : 0 < q) (h2q : 2 * q ≤ a1)
    (hcoprime : Nat.Coprime a1 q)
    (_hiso_y : Nonempty (G.induce (S_y.image f) ≃g
               fractionGraph a1 q))
    -- f(S_x) also induces E_{a1/q} (needed for slot argument)
    (_hiso_x : Nonempty (G.induce (S_x.image f) ≃g
               fractionGraph a1 q))
    (hG_mono : ∀ u v w : Circle, u ≠ v → u ≠ w →
      G.Adj u w → dist u v < dist u w → G.Adj u v)
    (hG_ccw_trans : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
      G.Adj u w → G.Adj u v → repFrom u v < repFrom u w → repFrom u w ≤ 1/2 → G.Adj v w)
    (h_dist : 2 / a < dist (f y) (f x)) :
    ∃ (y₀ : Circle) (gap : ℝ),
      0 < gap ∧ gap ≤ 1 ∧ (1 : ℝ) / a < gap ∧
      ∀ z ∈ S_y.image f, ¬(repFrom y₀ z < gap ∧ repFrom y₀ z > 0) := by
  -- ═══════════════════════════════════════════════════════════════════════════
  -- PROOF BY CONTRAPOSITIVE (Lemma 5.5):
  -- ═══════════════════════════════════════════════════════════════════════════
  --
  -- We prove: dist(f(y), f(x)) > 2/a ⟹ ∃ gap > 1/a in f(S_y)
  --
  -- DETAILED PROOF STRUCTURE (2026-01-09):
  -- ═══════════════════════════════════════════════════════════════════════════
  --
  -- Part 1: Cyclic structure preservation
  -- -------------------------------------
  -- Let φ: S_y → ZMod a1 be an isomorphism (from induced graph to E_{a1/q}) with φ(y) = 0.
  -- Let ψ: f(S_y) → ZMod a1 be an isomorphism (from _hiso) with ψ(f(y)) = 0.
  -- The composition ψ ∘ f|_{S_y} ∘ φ⁻¹: ZMod a1 → ZMod a1 is a cohom.
  -- Since E_{a1/q} is a core (by fractionGraph_selfCohom_isIso), it's a bijection.
  -- By fractionGraph_selfIso_form, it's a rotation (x ↦ a+x) or reflection (x ↦ a-x).
  -- Since (rotation/reflection)(0) = 0, we have a = 0, so:
  --   - Identity case: ψ ∘ f|_{S_y} ∘ φ⁻¹ = id
  --   - Reflection case: ψ ∘ f|_{S_y} ∘ φ⁻¹ = (x ↦ -x)
  --
  -- Part 2: Cyclic neighbors of y and f(y)
  -- --------------------------------------
  -- In S_y (equidistant), the cyclic neighbors of y are s_{a1-1} and s_1.
  -- Under φ: φ(s_1) = 1, φ(s_{a1-1}) = a1-1 (the neighbors of 0 in ZMod a1).
  -- By Part 1:
  --   - Identity: ψ(f(s_1)) = 1, ψ(f(s_{a1-1})) = a1-1
  --   - Reflection: ψ(f(s_1)) = a1-1, ψ(f(s_{a1-1})) = 1
  -- Either way, the cyclic neighbors of f(y) in f(S_y) are f(s_1) and f(s_{a1-1}).
  --
  -- Part 3: Slot argument
  -- ---------------------
  -- The "slot" of f(y) is the arc from f(s_{a1-1}) to f(s_1) passing through f(y).
  -- Since skeleton = S_y \ {y} = S_x \ {x}, and x is also between s_{a1-1} and s_1:
  --   - The same argument (Parts 1-2) applies to S_x and f(S_x)
  --   - The cyclic neighbors of f(x) in f(S_x) are also f(s_1) and f(s_{a1-1})
  -- Therefore f(y) and f(x) are both in the arc from f(s_{a1-1}) to f(s_1).
  -- This arc is the "slot" (the arc NOT containing the other a1-2 skeleton points).
  --
  -- Part 4: Contrapositive
  -- ----------------------
  -- Slot width = dist(f(s_{a1-1}), f(y)) + dist(f(y), f(s_1)) = gap_left + gap_right.
  -- If all gaps in f(S_y) ≤ 1/a, then slot width ≤ 2/a.
  -- Since f(x) is in the slot: dist(f(y), f(x)) ≤ slot width ≤ 2/a.
  -- Contrapositive: dist(f(y), f(x)) > 2/a ⟹ slot width > 2/a ⟹ ∃ gap > 1/a.
  --
  -- Part 5: Witness construction
  -- ----------------------------
  -- The larger of gap_left and gap_right is > 1/a.
  -- This gap is an arc in f(S_y) with no interior f(S_y) points.
  -- Return this as the witness (y₀, gap).
  --
  -- ═══════════════════════════════════════════════════════════════════════════
  -- FORMALIZATION STATUS: Requires helper lemmas for:
  -- 1. Cyclic order on finite Circle subsets (definition + basic properties)
  -- 2. Isomorphism S_y → ZMod a1 preserves cyclic neighbors
  -- 3. fractionGraph_selfIso_form application to ψ ∘ f|_{S_y} ∘ φ⁻¹
  -- 4. Shared skeleton implies same slot
  -- ═══════════════════════════════════════════════════════════════════════════
  --
  -- CONSTRUCTION: We use the slot_argument lemma below.
  -- It captures: if S has a1 points on Circle, f(y), f(x) ∈ f(S), and
  -- all gaps in f(S) are ≤ 1/a, then dist(f(y), f(x)) ≤ 2/a.
  --
  -- The contrapositive gives us our lemma: dist > 2/a ⟹ some gap > 1/a.
  --
  -- By contraposition using same_slot_of_shared_skeleton:
  --
  -- Structure:
  -- 1. same_slot_of_shared_skeleton gives: ∃ s1 s2 in skeleton such that
  --    f(y) and f(x) are both in the arc from f(s1) to f(s2)
  -- 2. This arc has width = repFrom (f s1) (f s2)
  -- 3. The arc width = gap1 + gap2 where gap1, gap2 are consecutive gaps in f(S_y)
  -- 4. If all gaps ≤ 1/a, then arc width ≤ 2/a
  -- 5. Since f(y), f(x) are in this arc: dist(f(y), f(x)) ≤ arc width ≤ 2/a
  -- 6. But h_dist: 2/a < dist(f(y), f(x)), contradiction
  -- 7. Therefore ∃ gap > 1/a
  --
  -- Note: This proof requires _hiso_x : f(S_x) ≃ E_{a1/q}, which should follow from:
  -- - S_x = insert x (S_y \ {y}) has the same structure as S_y
  -- - f is a cohomomorphism preserving the E_{a1/q} structure
  -- This follows from the cohom property of f.
  --
  -- Contrapositive argument:
  by_contra hall_gaps_small
  push_neg at hall_gaps_small
  -- hall_gaps_small : ∀ y₀ gap, 0 < gap → gap ≤ 1 → 1/a < gap →
  --                   ∃ z ∈ S_y.image f, repFrom y₀ z < gap ∧ repFrom y₀ z > 0
  -- This means: for any y₀ and gap > 1/a, there's a point of f(S_y) in (y₀, y₀ + gap)
  -- Equivalently: all gaps in f(S_y) are ≤ 1/a
  --
  -- From this, we derive dist(f(y), f(x)) ≤ 2/a:
  -- - By same_slot_of_shared_skeleton, f(y) and f(x) are in an arc of width ≤ 2/a
  --   (since the arc = two adjacent gaps, each ≤ 1/a)
  -- - Therefore dist(f(y), f(x)) ≤ 2/a
  -- - This contradicts h_dist: 2/a < dist(f(y), f(x))
  --
  -- The detailed wiring requires:
  -- 1. Extracting the slot bounds from same_slot_of_shared_skeleton
  -- 2. Connecting "all gaps ≤ 1/a" to "slot width ≤ 2/a"
  -- 3. Using dist_le_two_over_a_of_same_slot for the final bound
  --
  -- Uses:
  -- - The iso for f(S_x) (derivable from cohom + S_x structure)
  -- - The gap-to-slot-width connection
  --
  -- Key structural argument:
  -- From hall_gaps_small, we have: all gaps in f(S_y) are ≤ 1/a
  -- The slotWidth(f(y)) = gap_left + gap_right ≤ 2/a
  -- By same_slot_of_shared_skeleton, f(x) is in this slot
  -- Therefore dist(f(y), f(x)) ≤ slotWidth ≤ 2/a
  -- But h_dist says 2/a < dist(f(y), f(x)), contradiction
  --
  -- Step 1: Show gap to cyclic successor ≤ 1/a
  -- The cyclic successor of f(y) in f(S_y).toFinset has minimum positive repFrom from f(y)
  -- By hall_gaps_small with y₀ = f(y), for any g > 1/a, there's z with 0 < repFrom(f(y), z) < g
  -- This means the minimum positive repFrom ≤ 1/a
  --
  -- Step 2: Show gap to cyclic predecessor ≤ 1/a (symmetric argument)
  --
  -- Step 3: slotWidth = gap_succ + gap_pred ≤ 2/a
  --
  -- Step 4: f(x) is in the slot (requires same_slot_of_shared_skeleton)
  --
  -- Step 5: dist(f(y), f(x)) ≤ slotWidth ≤ 2/a, contradicting h_dist
  --
  -- Following the proof of Lemma 5.5:
  -- The key insight is that hall_gaps_small says ALL gaps in f(S_y) are ≤ 1/a.
  -- The cyclic successor and predecessor of f(y) in f(S_y) are at distance ≤ 1/a each.
  -- So slotWidth(f(y)) ≤ 2/a, and since f(x) is in this slot, dist(f(y), f(x)) ≤ 2/a.
  --
  -- Step A: Derive x ∈ S_x
  have hx_mem : x ∈ S_x := by
    rw [hS_x]
    exact Set.mem_insert x _
  -- Step B: Apply same_slot_of_shared_skeleton
  have hfxy : f y ≠ f x := by
    intro heq
    rw [heq] at h_dist
    have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (NeZero.pos a)
    have h0 : dist (f x) (f x) = 0 := dist_self (f x)
    have h1 : (0 : ℝ) < 2 / ↑a := div_pos (by positivity) ha_pos
    linarith
  have hslot := same_slot_of_shared_skeleton G a1 q ha1_ge hq_ge hq_pos h2q hcoprime
    S_y hS_y_finite hcard y hy x hx_ne_y S_x hS_x hx_mem f hfxy _hiso_y _hiso_x
    hG_mono hG_ccw_trans
  obtain ⟨s1, s2, hs1_mem, hs2_mem, hs1_ne_s2, hfy_in_arc, hfx_near, harc1_empty,
          harc2_empty⟩ := hslot
  -- hfy_in_arc : repFrom (f s1) (f y) + repFrom (f y) (f s2) ≤ repFrom (f s1) (f s2)
  -- hfx_near : disjunction: f(x) near f(s1) or f(x) near f(s2)
  -- harc1_empty : ∀ t ∈ S_y \ {y}, t ≠ s1 →
  --   ¬(0 < repFrom (f s1) (f t) ∧
  --     repFrom (f s1) (f t) < repFrom (f s1) (f y))
  -- harc2_empty : ∀ t ∈ S_y \ {y}, t ≠ s2 →
  --   ¬(0 < repFrom (f y) (f t) ∧
  --     repFrom (f y) (f t) < repFrom (f y) (f s2))
  --
  -- Step C: Bound the arc width using hall_gaps_small
  -- The arc from f(s1) to f(s2) through f(y) consists of two gaps:
  -- - gap1 = repFrom (f s1) (f y) (arc from f(s1) to f(y))
  -- - gap2 = repFrom (f y) (f s2) (arc from f(y) to f(s2))
  -- By hall_gaps_small, each gap is ≤ 1/a (otherwise there'd be a point inside)
  --
  -- Key insight: s1 and s2 are immediate cyclic neighbors of y (from the construction).
  -- So f(s1) and f(s2) are immediate cyclic neighbors of f(y) in f(S_y).
  -- The arcs [f(s1), f(y)] and [f(y), f(s2)] contain no other f(S_y) points.
  --
  have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (NeZero.pos a)
  -- Bound gap1: repFrom (f s1) (f y) ≤ 1/a
  have hgap1_le : repFrom (f s1) (f y) ≤ 1 / a := by
    by_contra hgap1_gt
    push_neg at hgap1_gt
    -- If repFrom (f s1) (f y) > 1/a, then by hall_gaps_small, there's a point z
    -- with 0 < repFrom (f s1) z < repFrom (f s1) (f y)
    -- This z would be strictly between f(s1) and f(y), contradicting that they're adjacent
    have hgap1_pos : 0 < repFrom (f s1) (f y) := lt_of_lt_of_le (by positivity) (le_of_lt hgap1_gt)
    have hgap1_le_one : repFrom (f s1) (f y) ≤ 1 := le_of_lt (repFrom_lt_one _ _)
    obtain ⟨z, hz_mem, hz_lt, hz_pos⟩ := hall_gaps_small (f s1) (repFrom (f s1) (f y))
      hgap1_pos hgap1_le_one hgap1_gt
    -- z ∈ f(S_y) with 0 < repFrom (f s1) z < repFrom (f s1) (f y)
    -- Since z ∈ f(S_y), there exists t ∈ S_y such that z = f(t)
    rw [Set.mem_image] at hz_mem
    obtain ⟨t, ht_mem, ht_eq⟩ := hz_mem
    rw [← ht_eq] at hz_lt hz_pos
    -- Case analysis on t
    by_cases hty : t = y
    · -- t = y: contradiction with hz_lt (repFrom (f s1) (f y) < repFrom (f s1) (f y))
      rw [hty] at hz_lt
      exact (lt_irrefl _) hz_lt
    · -- t ≠ y: t ∈ S_y \ {y}
      have ht_skel : t ∈ S_y \ {y} := Set.mem_diff_singleton.mpr ⟨ht_mem, hty⟩
      by_cases hts1 : t = s1
      · -- t = s1: contradiction with hz_pos (0 < repFrom (f s1) (f s1) = 0)
        rw [hts1] at hz_pos
        simp [repFrom_self] at hz_pos
      · -- t ≠ s1 and t ∈ S_y \ {y}: contradicts harc1_empty
        exact harc1_empty t ht_skel hts1 ⟨hz_pos, hz_lt⟩
  -- Bound gap2: repFrom (f y) (f s2) ≤ 1/a (symmetric argument)
  have hgap2_le : repFrom (f y) (f s2) ≤ 1 / a := by
    by_contra hgap2_gt
    push_neg at hgap2_gt
    have hgap2_pos : 0 < repFrom (f y) (f s2) := lt_of_lt_of_le (by positivity) (le_of_lt hgap2_gt)
    have hgap2_le_one : repFrom (f y) (f s2) ≤ 1 := le_of_lt (repFrom_lt_one _ _)
    obtain ⟨z, hz_mem, hz_lt, hz_pos⟩ := hall_gaps_small (f y) (repFrom (f y) (f s2))
      hgap2_pos hgap2_le_one hgap2_gt
    -- z ∈ f(S_y) with 0 < repFrom (f y) z < repFrom (f y) (f s2)
    -- Since z ∈ f(S_y), there exists t ∈ S_y such that z = f(t)
    rw [Set.mem_image] at hz_mem
    obtain ⟨t, ht_mem, ht_eq⟩ := hz_mem
    rw [← ht_eq] at hz_lt hz_pos
    -- Case analysis on t
    by_cases hty : t = y
    · -- t = y: contradiction with hz_pos (0 < repFrom (f y) (f y) = 0)
      rw [hty] at hz_pos
      simp [repFrom_self] at hz_pos
    · -- t ≠ y: t ∈ S_y \ {y}
      have ht_skel : t ∈ S_y \ {y} := Set.mem_diff_singleton.mpr ⟨ht_mem, hty⟩
      by_cases hts2 : t = s2
      · -- t = s2: contradiction with hz_lt (repFrom (f y) (f s2) < repFrom (f y) (f s2))
        rw [hts2] at hz_lt
        exact (lt_irrefl _) hz_lt
      · -- t ≠ s2 and t ∈ S_y \ {y}: contradicts harc2_empty
        exact harc2_empty t ht_skel hts2 ⟨hz_pos, hz_lt⟩
  -- Step D: Arc width ≤ 2/a
  have harc_width : repFrom (f s1) (f y) + repFrom (f y) (f s2) ≤ 2 / a := by
    calc repFrom (f s1) (f y) + repFrom (f y) (f s2)
      ≤ 1 / a + 1 / a := add_le_add hgap1_le hgap2_le
      _ = 2 / a := by ring
  -- Step E: Derive f-injectivity on S_y (needed for f(s1) ≠ f(s2))
  have hf_inj : Set.InjOn f S_y := by
    obtain ⟨iso_y⟩ := _hiso_y
    apply Set.injOn_of_ncard_image_eq (s := S_y) (f := f) _ hS_y_finite
    rw [Set.ncard_eq_toFinset_card _ hS_y_finite,
        Set.ncard_eq_toFinset_card _ (hS_y_finite.image f)]
    haveI : Fintype ↥(S_y.image f) := (hS_y_finite.image f).fintype
    haveI : Fintype ↥S_y := hS_y_finite.fintype
    rw [hS_y_finite.card_toFinset, (hS_y_finite.image f).card_toFinset]
    have : Fintype.card ↥(S_y.image f) = a1 := by rw [iso_y.card_eq, ZMod.card a1]
    have : Fintype.card ↥S_y = a1 := by
      rw [hS_y_finite.card_toFinset] at hcard; exact hcard
    omega
  have hfs1_ne_fs2 : f s1 ≠ f s2 := by
    intro h
    exact hs1_ne_s2 (hf_inj (Set.diff_subset hs1_mem) (Set.diff_subset hs2_mem) h)
  -- Step F: dist(f(y), f(x)) ≤ 2/a via case split on hfx_near disjunction
  have hdist_le : dist (f y) (f x) ≤ 2 / a := by
    rcases hfx_near with hfx_left | hfx_right
    · -- Left disjunction: no skeleton-image strictly between f(s1) and f(x)
      -- Key: repFrom (f s1) (f x) ≤ repFrom (f s1) (f s2)
      have hfx_bounded : repFrom (f s1) (f x) ≤ repFrom (f s1) (f s2) := by
        by_contra hgt; push_neg at hgt
        exact hfx_left s2 hs2_mem (Ne.symm hs1_ne_s2)
          ⟨repFrom_pos_of_ne _ _ (Ne.symm hfs1_ne_fs2), hgt⟩
      -- Case split on position of f(x) relative to f(y) in the arc
      by_cases horder : repFrom (f s1) (f y) ≤ repFrom (f s1) (f x)
      · -- f(y) before f(x): dist ≤ repFrom (f y) (f x) ≤ repFrom (f y) (f s2) ≤ 1/a
        have hs1_le_s2 : repFrom (f s1) (f y) ≤ repFrom (f s1) (f s2) := by
          linarith [repFrom_nonneg (f y) (f s2), hfy_in_arc]
        have h_yx_eq := repFrom_ordered (f s1) (f y) (f x) horder
        have h_ys2_eq := repFrom_ordered (f s1) (f y) (f s2) hs1_le_s2
        calc dist (f y) (f x) ≤ repFrom (f y) (f x) := dist_le_repFrom _ _
          _ ≤ repFrom (f y) (f s2) := by linarith
          _ ≤ 1 / a := hgap2_le
          _ ≤ 2 / a := by
              exact div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) (le_of_lt ha_pos)
      · -- f(x) before f(y): dist ≤ repFrom (f x) (f y) ≤ repFrom (f s1) (f y) ≤ 1/a
        push_neg at horder
        have h_xy_eq := repFrom_ordered (f s1) (f x) (f y) (le_of_lt horder)
        calc dist (f y) (f x) = dist (f x) (f y) := dist_comm _ _
          _ ≤ repFrom (f x) (f y) := dist_le_repFrom _ _
          _ ≤ repFrom (f s1) (f y) := by linarith [repFrom_nonneg (f s1) (f x)]
          _ ≤ 1 / a := hgap1_le
          _ ≤ 2 / a := by
              exact div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) (le_of_lt ha_pos)
    · -- Right disjunction: no skeleton-image strictly between f(s2) and f(x)
      -- Strategy: dist(f y, f x) ≤ dist(f y, f s2) + dist(f s2, f x) ≤ 1/a + 1/a = 2/a
      suffices hfs2_fx_le : dist (f s2) (f x) ≤ 1 / a by
        calc dist (f y) (f x)
          ≤ dist (f y) (f s2) + dist (f s2) (f x) := dist_triangle _ _ _
          _ ≤ repFrom (f y) (f s2) + dist (f s2) (f x) :=
              add_le_add (dist_le_repFrom _ _) (le_refl _)
          _ ≤ 1 / a + 1 / a := add_le_add hgap2_le hfs2_fx_le
          _ = 2 / a := by ring
      -- Bound dist(f s2, f x) ≤ 1/a
      by_cases hfs2_fx : f s2 = f x
      · rw [hfs2_fx, _root_.dist_self]; positivity
      · by_cases h_le : repFrom (f s2) (f x) ≤ 1 / a
        · exact le_trans (dist_le_repFrom _ _) h_le
        · -- repFrom (f s2) (f x) > 1/a: derive repFrom (f x) (f s2) < 1/a via complement
          push_neg at h_le
          have h_pos : 0 < repFrom (f s2) (f x) := lt_trans (by positivity) h_le
          have h_le1 : repFrom (f s2) (f x) ≤ 1 := le_of_lt (repFrom_lt_one _ _)
          obtain ⟨z, hz_mem, hz_lt, hz_pos⟩ := hall_gaps_small (f s2)
            (repFrom (f s2) (f x)) h_pos h_le1 (by linarith)
          rw [Set.mem_image] at hz_mem
          obtain ⟨t, ht_mem, rfl⟩ := hz_mem
          by_cases hty : t = y
          · -- z = f(y): repFrom (f s2) (f y) < repFrom (f s2) (f x)
            -- So repFrom (f x) (f s2) = 1 - repFrom(f s2)(f x) < repFrom(f y)(f s2) ≤ 1/a
            rw [hty] at hz_lt hz_pos
            -- hz_lt : repFrom (f s2) (f y) < repFrom (f s2) (f x)
            -- hz_pos : repFrom (f s2) (f y) > 0
            have hfy_ne_fs2 : f y ≠ f s2 := by
              intro h; rw [h] at hz_pos; simp [repFrom_self] at hz_pos
            have h1 := repFrom_add_repFrom_eq_one (f s2) (f y) hfy_ne_fs2
            have h2 := repFrom_add_repFrom_eq_one (f s2) (f x) (Ne.symm hfs2_fx)
            calc dist (f s2) (f x) = dist (f x) (f s2) := dist_comm _ _
              _ ≤ repFrom (f x) (f s2) := dist_le_repFrom _ _
              _ ≤ 1 / a := by linarith
          · -- z = f(t) for t ∈ skeleton, t ≠ s2: contradicts hfx_right
            have ht_skel : t ∈ S_y \ {y} := Set.mem_diff_singleton.mpr ⟨ht_mem, hty⟩
            by_cases hts2 : t = s2
            · subst hts2; simp [repFrom_self] at hz_pos
            · exact absurd ⟨hz_pos, hz_lt⟩ (hfx_right t ht_skel hts2)
  -- Step G: Contradiction
  exact not_lt.mpr hdist_le h_dist

/-- If a finite set S ⊆ Circle has a gap of length > 1/M (an arc with no points of S),
    then there exists a shift such that the shifted rounding map is not surjective.

    Key idea: By choosing the shift appropriately, we can position one cell [t, t+1/M)
    entirely inside the gap. Since the gap has no S-points, that cell has no preimage.

    More precisely: If gap = (y, y + g) with g > 1/M, choose shift t with t ∈ (y, y + g - 1/M).
    Then [t, t + 1/M) ⊆ (y, y + g), and roundToZModShift M t maps no S-point to cell 0. -/
private lemma roundToZModShift_not_surj_of_gap (M : ℕ) [NeZero M] (S : Set Circle) (_hS : S.Finite)
    (y : Circle)
    -- There's an arc (y, y + gap) with no points of S (using repFrom to measure arc length)
    (gap : ℝ) (_hgap_pos : 0 < gap) (_hgap_le : gap ≤ 1)
    (hgap_gt : (1 : ℝ) / M < gap)
    (h_no_points : ∀ z ∈ S, ¬(repFrom y z < gap ∧ repFrom y z > 0)) :
    ∃ t : Circle, ¬Function.Surjective (fun x : S => roundToZModShift M t (x : Circle)) := by
  -- Strategy: Choose t such that [t, t + 1/M) is inside the gap (y, y + gap).
  -- Since gap > 1/M, we can find such t.
  --
  -- Let t = y + δ where δ ∈ (0, gap - 1/M). Then:
  -- - t is in (y, y + gap - 1/M)
  -- - [t, t + 1/M) = (y + δ, y + δ + 1/M) ⊆ (y, y + gap) since δ > 0 and δ + 1/M < gap.
  --
  -- Cell 0 of roundToZModShift M t is [t, t + 1/M) which has no S-points.
  -- Hence roundToZModShift M t is not surjective (0 ∈ ZMod M has no preimage).
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.2 (NeZero.pos M)
  have h1M_pos : (0 : ℝ) < 1 / M := by positivity
  have hδ_exists : 0 < gap - 1 / M := by linarith
  -- Choose the midpoint δ = (gap - 1/M) / 2 to be safe
  set δ : ℝ := (gap - 1 / M) / 2 with hδ_def
  have hδ_pos : 0 < δ := by simp only [hδ_def]; linarith
  have hδ_lt : δ < gap - 1 / M := by simp only [hδ_def]; linarith
  have hδ_lt' : δ + 1 / M < gap := by linarith
  have hδ_lt_one : δ < 1 := by
    calc δ = (gap - 1/M) / 2 := hδ_def
      _ < (1 - 0) / 2 := by linarith
      _ = 1/2 := by ring
      _ < 1 := by norm_num
  -- Now define t = y + δ (using coercion from ℝ to Circle)
  set t : Circle := y + (δ : Circle) with ht_def
  use t
  intro hsurj
  -- hsurj says roundToZModShift M t is surjective on S
  -- This means every k ∈ ZMod M has a preimage
  -- In particular, 0 has a preimage: ∃ z ∈ S, roundToZModShift M t z = 0
  obtain ⟨⟨z, hz⟩, hz0⟩ := hsurj 0
  -- z ∈ S and roundToZModShift M t z = 0
  -- roundToZModShift M t z = roundToZMod M (z - t) = 0
  -- This means z - t ∈ [0, 1/M) in Circle terms
  -- i.e., repFrom t z < 1/M
  --
  -- But we also know z ∈ S, and we chose t such that [t, t + 1/M) ⊆ (y, y + gap)
  -- So if z rounds to 0 (relative to t), then z ∈ [t, t + 1/M) ⊆ (y, y + gap)
  -- This means 0 < repFrom y z < gap, contradicting h_no_points.
  --
  -- Step 1: roundToZMod M (z - t) = 0 means repFrom t z < 1/M
  simp only [roundToZModShift] at hz0
  -- hz0 : roundToZMod M (z - t) = 0
  -- By point_in_cell_bounds, the representative of z - t is in [0/M, 1/M) = [0, 1/M)
  have h_rep_t_z : repFrom t z < 1 / M := by
    have hbounds := point_in_cell_bounds M (z - t)
    simp only [hz0, ZMod.val_zero, Nat.cast_zero, zero_div] at hbounds
    -- hbounds : 0 ≤ (AddCircle.equivIco 1 0 (z - t)).val ∧
    --           (AddCircle.equivIco 1 0 (z - t)).val < 1 / M
    -- repFrom t z = (AddCircle.equivIco 1 0 (z - t)).val by definition
    simp only [repFrom]
    convert hbounds.2
    ring
  -- Step 2: Relate repFrom t z to repFrom y z
  -- We have t = y + δ, so z - t = z - y - δ
  -- repFrom t z = (z - t) mod 1 = (repFrom y z - δ) mod 1
  --
  -- Since 0 ≤ repFrom t z < 1/M < gap and δ > 0, we need repFrom y z ≥ δ
  -- (otherwise repFrom t z would wrap around to 1 + repFrom y z - δ > 1 - δ ≥ 1 - gap/2)
  have h_rep_y_z_ge : δ ≤ repFrom y z := by
    by_contra h_neg
    push_neg at h_neg
    -- If repFrom y z < δ, then repFrom t z = repFrom y z - δ + 1 (wrap around)
    -- But repFrom t z < 1/M, so repFrom y z - δ + 1 < 1/M
    -- i.e., repFrom y z < δ + 1/M - 1 < 0, which contradicts repFrom y z ≥ 0
    --
    -- Key: repFrom t z ≥ 1 - δ when repFrom y z < δ
    -- This is because t = y + δ, so z - t = (z - y) - δ
    -- When (z - y) representative is < δ, the (z - t) representative wraps to ≥ 1 - δ
    have h_wrap : 1 - δ ≤ repFrom t z := by
      simp only [ht_def]
      exact repFrom_shift_wrap_lower y z δ hδ_pos hδ_lt_one h_neg
    -- Now: 1 - δ ≤ repFrom t z < 1/M
    -- So 1 - δ < 1/M, i.e., 1 - 1/M < δ
    -- But δ = (gap - 1/M)/2 and gap ≤ 1, so δ ≤ (1 - 1/M)/2 < 1 - 1/M for M ≥ 2
    have h_contra : 1 - 1 / M < δ := by linarith [h_wrap, h_rep_t_z]
    have hM_ge_2 : (2 : ℝ) ≤ M := by
      by_contra hlt; push_neg at hlt
      have hM_lt_2 : M < 2 := by exact_mod_cast hlt
      have hM_pos := NeZero.pos M
      interval_cases M
      simp only [Nat.cast_one, div_one] at hgap_gt
      linarith [_hgap_le]
    have h_δ_small : δ ≤ (1 - 1 / M) / 2 := by
      simp only [hδ_def]
      have : gap - 1/M ≤ 1 - 1/M := by linarith [_hgap_le]
      linarith
    have h_half : (1 - 1 / M) / 2 < 1 - 1 / M := by
      have h1M_lt_1 : 1 / (M : ℝ) < 1 := by
        rw [div_lt_one hM_pos]
        linarith
      linarith
    linarith
  -- Step 3: Upper bound on repFrom y z
  have h_rep_y_z_lt : repFrom y z < gap := by
    -- repFrom t z = repFrom y z - δ (no wrap since repFrom y z ≥ δ)
    -- So repFrom y z = repFrom t z + δ < 1/M + δ < gap
    have h_no_wrap : repFrom t z = repFrom y z - δ := by
      simp only [ht_def]
      exact repFrom_shift_no_wrap y z δ hδ_pos hδ_lt_one h_rep_y_z_ge
    linarith [h_rep_t_z, hδ_lt', h_no_wrap]
  -- Step 4: Contradiction with h_no_points
  have h_rep_y_z_pos : 0 < repFrom y z := lt_of_lt_of_le hδ_pos h_rep_y_z_ge
  exact h_no_points z hz ⟨h_rep_y_z_lt, h_rep_y_z_pos⟩

/-- roundToZModShift is a cohomomorphism from circleGraphOpen to fractionGraph.
    This follows because roundToZModShift M t x = roundToZMod M (x - t), and
    translation by -t is an automorphism of the circle graph (distance-preserving). -/
private lemma roundToZModShift_cohom_open (r : ℝ) (hr : 2 ≤ r) (M : ℕ) [NeZero M]
    (_hM : 2 ≤ M) (hMr : r ≤ (M : ℝ)) (t : Circle) :
    IsCohom (circleGraphOpen r hr) (fractionGraph M (Nat.floor ((M : ℝ) / r)))
      (roundToZModShift M t) := by
  -- Key fact: circleDistance (u - t) (v - t) = circleDistance u v (translation invariance)
  have hdist_translate : ∀ u v : Circle, circleDistance (u - t) (v - t) = circleDistance u v := by
    intro u v
    simp only [circleDistance, dist_eq_norm, sub_sub_sub_cancel_right]
  -- Setup: parameters for the proof (replicate circleGraph_rounding_cohom_floor)
  let q := Nat.floor ((M : ℝ) / r)
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
  have hq_pos : 0 < q := by
    have hMr' : (1 : ℝ) ≤ (M : ℝ) / r := by
      have h1 : (1 : ℝ) = r / r := by field_simp [hr_pos.ne']
      have hdiv : (r : ℝ) / r ≤ (M : ℝ) / r := div_le_div_of_nonneg_right hMr (le_of_lt hr_pos)
      simpa [h1] using hdiv
    have hq_ge1 : 1 ≤ q := (Nat.one_le_floor_iff _).2 hMr'
    exact lt_of_lt_of_le Nat.zero_lt_one hq_ge1
  have hN_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hq_le : (q : ℝ) ≤ (M : ℝ) / r :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) (le_of_lt hr_pos))
  have hq_div_le : (q : ℝ) / M ≤ 1 / r := by
    have := div_le_div_of_nonneg_right hq_le (le_of_lt hN_pos)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- Main proof: non-edges map to non-edges
  intro u v huv hnonadj
  simp only [circleGraphOpen, ne_eq, not_and, not_lt] at hnonadj
  -- u' = u - t, v' = v - t have the same circle distance as u, v
  set u' := u - t with hu'_def
  set v' := v - t with hv'_def
  have hdist_eq : circleDistance u' v' = circleDistance u v := hdist_translate u v
  have hnonadj' : circleDistance u' v' ≥ 1 / r := by rw [hdist_eq]; exact hnonadj huv
  constructor
  · -- roundToZModShift M t u ≠ roundToZModShift M t v
    intro heq
    simp only [roundToZModShift] at heq
    -- heq: roundToZMod M u' = roundToZMod M v'
    have hdm_lt : distMod M (roundToZMod M u') (roundToZMod M v') < q := by
      rw [heq, distMod_self]; exact hq_pos
    have hlt : circleDistance u' v' < (q : ℕ) / (M : ℝ) :=
      circleDistance_lt_of_cells_close M u' v' q hq_pos hdm_lt
    have hlt' : circleDistance u' v' < 1 / r := lt_of_lt_of_le hlt hq_div_le
    exact not_lt.mpr hnonadj' hlt'
  · -- ¬(fractionGraph M q).Adj (roundToZModShift M t u) (roundToZModShift M t v)
    intro hadj
    simp only [roundToZModShift, fractionGraph] at hadj
    obtain ⟨_, hdm_lt⟩ := hadj
    have hlt : circleDistance u' v' < (q : ℕ) / (M : ℝ) :=
      circleDistance_lt_of_cells_close M u' v' q hq_pos hdm_lt
    have hlt' : circleDistance u' v' < 1 / r := lt_of_lt_of_le hlt hq_div_le
    exact not_lt.mpr hnonadj' hlt'

/-- If a subset S of the circle graph is isomorphic to E_{N/q}, and r ≤ M < N,
    then rounding from the circle graph to M equidistant points gives a cohomomorphism
    from E_{N/q} to E_{M/q'} where q' = ⌊M/r⌋. -/
private lemma rounding_gives_cohom_to_fraction (r : ℝ) (hr : 2 ≤ r)
    (N M q : ℕ) [NeZero N] [NeZero M]
    (hMr : r ≤ (M : ℝ)) (_hM : 2 ≤ M) (S : Set Circle)
    (hiso : Nonempty ((circleGraphOpen r hr).induce S ≃g fractionGraph N q)) :
    Cohom (fractionGraph N q) (fractionGraph M (Nat.floor ((M : ℝ) / r))) := by
  -- Compose: E_{N/q} ≃ induced[S] ---> Circle --roundToZMod--> E_{M/⌊M/r⌋}
  -- Step 1: Get cohomomorphism from fractionGraph N q to induced S
  rcases hiso with ⟨iso⟩
  have hcohom_iso : Cohom (fractionGraph N q) ((circleGraphOpen r hr).induce S) :=
    cohom_of_iso iso.symm
  -- Step 2: Induced subgraph has cohomomorphism to the full graph
  have hcohom_induced : Cohom ((circleGraphOpen r hr).induce S) (circleGraphOpen r hr) :=
    induced_cohom (circleGraphOpen r hr) S
  -- Step 3: Rounding gives cohomomorphism from circle graph to fraction graph
  have hcohom_round := circleGraph_rounding_cohom_floor r hr M _hM hMr
  have hcohom_round_open := hcohom_round.2.1
  -- Step 4: Compose all three
  exact Cohom.trans (Cohom.trans hcohom_iso hcohom_induced) hcohom_round_open

/-- Key helper: If f(S_y) has a gap > 1/a, then we can construct Cohom E_{a1/q} E_{a0/b0}.
    This is the core of the gap contradiction argument (tex lines 2300-2302).

    Construction:
    1. Gap > 1/a → roundToZModShift a t is non-surjective for some shift t
    2. Composition: E_{a1/q} → S_y → f(S_y) → (rounding) → E_{a/b}
    3. Non-surjective → image ⊆ E_{a/b} \ {v} for some v
    4. E_{a/b} \ {v} → E_{a0/b0} by fractionGraph_remove_vertex_equiv
    5. Compose to get Cohom E_{a1/q} E_{a0/b0} -/
private lemma gap_gives_cohom_to_predecessor
    (r : ℝ) (hr : 2 ≤ r)
    (G : SimpleGraph Circle) (hG_ge : circleGraphOpen r hr ≤ G)
    (a b a1 q a0 b0 : ℕ) [NeZero a] [NeZero a1] [NeZero a0]
    (_ha_pos : 0 < a) (_hb_pos : 0 < b) (hb_ge_2 : 2 ≤ b) (h2b : 2 * b ≤ a)
    (ha0_pos : 0 < a0) (hb0_pos : 0 < b0) (_h2b0 : 2 * b0 ≤ a0)
    (ha0_lt : a0 < a) (hb0_lt : b0 < b)
    (hcoprime_ab : Nat.Coprime a b)
    (hpred_det : a * b0 - b * a0 = 1)
    (_h2q : 2 * q ≤ a1) (_hq_pos : 0 < q)
    (hMr : r ≤ (a : ℝ)) -- r ≤ a ensures rounding gives cohom
    (hfloor : Nat.floor ((a : ℝ) / r) = b) -- floor(a/r) = b
    -- Gap information: there's a gap > 1/a in f(S_y)
    (S_y : Set Circle) (_hS_y_finite : S_y.Finite)
    (f : Circle → Circle)
    (y₀ : Circle) (gap : ℝ) (hgap_pos : 0 < gap) (hgap_le : gap ≤ 1) (hgap_gt : (1 : ℝ) / a < gap)
    (h_no_points : ∀ z ∈ S_y.image f, ¬(repFrom y₀ z < gap ∧ repFrom y₀ z > 0))
    -- Isomorphism: S_y ≃ E_{a1/q} in graph G
    (hiso : Nonempty (G.induce S_y ≃g fractionGraph a1 q))
    -- f is a cohom on the graph G
    (hf : IsCohom G G f) :
    Cohom (fractionGraph a1 q) (fractionGraph a0 b0) := by
  -- Step 1: Get non-surjective rounding shift
  have hfSy_finite := Set.Finite.image f _hS_y_finite
  have h_nonsurj := roundToZModShift_not_surj_of_gap a (S_y.image f) hfSy_finite
    y₀ gap hgap_pos hgap_le hgap_gt h_no_points
  obtain ⟨t, hnsurj⟩ := h_nonsurj
  -- hnsurj : ¬Function.Surjective (fun x : S_y.image f => roundToZModShift a t x.val)
  -- Step 2: Build the composition cohom E_{a1/q} → E_{a/b}
  -- 2a: E_{a1/q} → induced S_y (via iso)
  rcases hiso with ⟨iso⟩
  have hcohom_iso : Cohom (fractionGraph a1 q) (G.induce S_y) :=
    cohom_of_iso iso.symm
  -- 2b: induced S_y → G (inclusion)
  have hcohom_induced : Cohom (G.induce S_y) G :=
    induced_cohom G S_y
  -- 2c: G → G (via f)
  have hcohom_f : Cohom G G := ⟨f, hf⟩
  -- 2d: G → E_{a/b} (via roundToZModShift a t)
  -- The rounding is a cohom from circleGraphOpen, and since open ≤ G,
  -- it is also a cohom from G (G has fewer non-edges to preserve).
  have ha_ge_2 : 2 ≤ a := by
    have h1 : 4 ≤ 2 * b := Nat.mul_le_mul_left 2 hb_ge_2
    have h2 : 4 ≤ a := le_trans h1 h2b
    omega
  have hround_cohom_open := roundToZModShift_cohom_open r hr a ha_ge_2 hMr t
  -- Convert floor condition
  rw [hfloor] at hround_cohom_open
  -- Derive cohom from G using monotonicity: open ≤ G ⟹ open non-edges ⊇ G non-edges
  have hround_cohom : IsCohom G (fractionGraph a b) (roundToZModShift a t) := by
    intro u v huv hnadj
    exact hround_cohom_open u v huv (fun hadj => hnadj (hG_ge hadj))
  have hcohom_round : Cohom G (fractionGraph a b) :=
    ⟨roundToZModShift a t, hround_cohom⟩
  -- 2e: Compose to get E_{a1/q} → E_{a/b}
  have hcohom_comp : Cohom (fractionGraph a1 q) (fractionGraph a b) :=
    Cohom.trans (Cohom.trans (Cohom.trans hcohom_iso hcohom_induced) hcohom_f) hcohom_round
  -- Step 3: Non-surjective → image misses some vertex v
  -- The composed function is roundToZModShift a t ∘ f ∘ (S_y embedding)
  -- On S_y, the final step roundToZModShift a t ∘ f is non-surjective
  -- So the image is a proper subset of ZMod a
  -- Step 4: Factor through E_{a/b} \ {v}
  -- Use fractionGraph_remove_vertex_equiv with (a, b) to get predecessor
  have h_remove := fractionGraph_remove_vertex_equiv a b hb_ge_2 h2b hcoprime_ab (0 : ZMod a)
  obtain ⟨p', q', hp'_pos, hq'_pos, hp'_lt, hq'_lt, hbezout, hcohom_fwd, _hcohom_bwd⟩ := h_remove
  -- By uniqueness of Stern-Brocot predecessor, (p', q') = (a0, b0)
  have huniq := sternBrocotPredecessor_unique a b a0 b0 p' q' hcoprime_ab
    ha0_pos ha0_lt hb0_pos hb0_lt hp'_pos hp'_lt hq'_pos hq'_lt hpred_det hbezout
  -- Step 4: Extract the missed vertex from non-surjectivity
  -- hnsurj : ¬Surjective (fun x : S_y.image f => roundToZModShift a t x.val)
  -- This means ∃ v ∈ ZMod a, v is not in the image
  simp only [Function.Surjective, not_forall] at hnsurj
  obtain ⟨v, hv_not_in_image⟩ := hnsurj
  -- hv_not_in_image : ∀ x : S_y.image f, roundToZModShift a t x.val ≠ v
  -- (equivalently: ¬∃ x, roundToZModShift a t x.val = v)
  -- Step 5: Use fractionGraph_remove_vertex_equiv with the missed vertex v
  have h_remove_v := fractionGraph_remove_vertex_equiv a b hb_ge_2 h2b hcoprime_ab v
  obtain ⟨p'', q'', hp''_pos, hq''_pos, hp''_lt, hq''_lt, hbezout', hcohom_fwd_v, _⟩ := h_remove_v
  -- By uniqueness, (p'', q'') = (a0, b0) as well (predecessor is independent of removed vertex)
  have huniq' := sternBrocotPredecessor_unique a b a0 b0 p'' q'' hcoprime_ab
    ha0_pos ha0_lt hb0_pos hb0_lt hp''_pos hp''_lt hq''_pos hq''_lt hpred_det hbezout'
  have ha0_eq_p'' : a0 = p'' := huniq'.1
  have hb0_eq_q'' : b0 = q'' := huniq'.2
  subst ha0_eq_p'' hb0_eq_q''
  -- hcohom_fwd_v : Cohom ((fractionGraph a b).induce {x | x ≠ v}) (fractionGraph a0 b0)
  -- Step 6: Factor through {x | x ≠ v}
  -- The composition map is: g := roundToZModShift a t ∘ f ∘ (inclusion ∘ iso⁻¹)
  -- Its image is ⊆ {x | x ≠ v} because:
  -- - The image of iso⁻¹ is S_y
  -- - The image of inclusion ∘ iso⁻¹ is S_y (as a subset of Circle)
  -- - The image of f ∘ inclusion ∘ iso⁻¹ is f(S_y) = S_y.image f
  -- - The image of roundToZModShift a t on f(S_y) excludes v (by hv_not_in_image)
  -- Define the composed function
  let g : ZMod a1 → ZMod a := fun w => roundToZModShift a t (f (iso.symm w).val)
  -- Show g maps into {x | x ≠ v}
  have hg_avoids_v : ∀ w : ZMod a1, g w ≠ v := by
    intro w
    -- iso.symm w ∈ S_y, so f (iso.symm w) ∈ f(S_y) = S_y.image f
    have hfw_mem : f (iso.symm w).val ∈ S_y.image f := Set.mem_image_of_mem f (iso.symm w).property
    -- hv_not_in_image : ¬∃ x : S_y.image f, roundToZModShift a t x.val = v
    -- We prove g w ≠ v by contradiction
    intro heq
    -- heq : g w = v, i.e., roundToZModShift a t (f (iso.symm w).val) = v
    apply hv_not_in_image
    exact ⟨⟨f (iso.symm w).val, hfw_mem⟩, heq⟩
  -- Use isCohom_corestrict to factor through {x | x ≠ v}
  -- First, show g is a cohom from E_{a1/q} to E_{a/b}
  have hg_cohom : IsCohom (fractionGraph a1 q) (fractionGraph a b) g := by
    -- g is the composition of cohoms, which is a cohom
    intro u w huw hnadj
    -- Extract the cohom property from hcohom_comp
    obtain ⟨g', hg'⟩ := hcohom_comp
    -- Show g is a cohom by composing the cohom property of each piece:
    -- iso.symm, inclusion, f, and roundToZModShift
    have iso_cohom : IsCohom (fractionGraph a1 q) (G.induce S_y)
        (fun v => iso.symm v) := by
      intro x y hxy hnadj'
      constructor
      · intro heq
        have := iso.symm.injective heq
        exact hxy this
      · intro hadj
        apply hnadj'
        exact iso.symm.map_adj_iff.mp hadj
    have incl_cohom : IsCohom (G.induce S_y) G
        (fun s => s.val) := by
      intro x y hxy hnadj'
      constructor
      · intro heq
        exact hxy (Subtype.ext heq)
      · simp only [SimpleGraph.induce_adj] at hnadj' ⊢
        exact hnadj'
    have f_cohom := hf
    -- Compose the cohoms
    have comp1 := IsCohom.comp iso_cohom incl_cohom
    have comp2 := IsCohom.comp comp1 f_cohom
    have comp3 := IsCohom.comp comp2 hround_cohom
    -- comp3 is the cohom for g
    exact comp3 u w huw hnadj
  -- Factor through {x | x ≠ v}
  have hg_corestrict : IsCohom (fractionGraph a1 q)
      ((fractionGraph a b).induce {x : ZMod a | x ≠ v})
      (fun w => ⟨g w, hg_avoids_v w⟩) :=
    isCohom_corestrict g hg_cohom {x | x ≠ v} hg_avoids_v
  -- Compose with hcohom_fwd_v to get Cohom E_{a1/q} E_{a0/b0}
  have hcohom_to_pred : Cohom (fractionGraph a1 q) (fractionGraph a0 b0) :=
    Cohom.trans ⟨_, hg_corestrict⟩ hcohom_fwd_v
  exact hcohom_to_pred

/-- Key lemma for continuity: Given convergent pairs from odd_even_convergent_pair_data_large_both,
    if f is a self-cohom on an irrational circle graph and S_y induces E_{a1/q} for some q,
    then dist(f(y), f(x)) ≤ 2/a where a = p_{2n-1}.

    This captures the proof structure (Lemma 5.5):
    - S_y (a1 equidistant points with y replacing x) induces E_{a1/q}
    - f(S_y) also induces E_{a1/q'} for some q' (by core argument)
    - All gaps in f(S_y) are ≤ 1/a (gap contradiction argument using a/b neighbor)
    - f(x) and f(y) are in the same "slot", so dist(f(x), f(y)) ≤ 2/a

    Key: The bound 2/a only depends on a (the gap bound parameter), not on q.
    The convergent structure ensures a/b is a Stern-Brocot neighbor of a1/b1,
    which enables the gap contradiction argument.

    The proof outline:
    1. S_y = {y, s_1, ..., s_{a1-1}} has a1 points inducing E_{a1/q}
    2. The "skeleton" {s_1, ..., s_{a1-1}} is shared between S_x and S_y
    3. f(S_y) = {f(y), f(s_1), ..., f(s_{a1-1})} also induces E_{a1/q'}
    4. If any gap in f(S_y) > 1/a, by roundToZModShift_not_surj_of_gap,
       rounding to a points misses a cell, giving non-surjective cohom
    5. This contradicts cohom ordering (via fractionGraph_no_cohom_to_predecessor)
    6. So all gaps ≤ 1/a
    7. f(S_x) shares skeleton with f(S_y), so f(x) and f(y) are in same "slot"
    8. Slot has width ≤ 2/a, so dist(f(x), f(y)) ≤ 2/a

    The predecessor (a0, b0) is the Stern-Brocot predecessor of (a, b).
    For convergents, this is p_{2n-2}/q_{2n-2} when (a,b) = p_{2n-1}/q_{2n-1}.
    The ordering hypothesis ha1q_gt_a0b0 says a1/q > a0/b0, which holds because:
    - q = b1 = ceil(a1/r) (for even convergent a1/b1 < r)
    - Even convergents increase: a1/b1 > p_{2n-2}/q_{2n-2} = a0/b0 -/
private lemma selfCohom_dist_bound_from_convergents
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (a b a1 q : ℕ) [NeZero a1]
    -- Predecessor of (a, b): Stern-Brocot predecessor = previous even convergent
    (a0 b0 : ℕ)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (ha1_pos : 0 < a1) (hq_pos : 0 < q)
    (ha0_pos : 0 < a0) (hb0_pos : 0 < b0)
    (h2b : 2 * b ≤ a)
    (h2q : 2 * q ≤ a1) -- Ratio condition for E_{a1/q}
    (hq_ge_2 : 2 ≤ q) -- q ≥ 2 (even convergent denominator)
    (hcoprime_a1q : Nat.Coprime a1 q) -- coprimality of convergent pair
    (h2b0 : 2 * b0 ≤ a0)
    -- Predecessor relationship: a * b0 - b * a0 = 1
    (ha0_lt : a0 < a) (hb0_lt : b0 < b)
    (hpred_det : a * b0 - b * a0 = 1)
    -- Convergent bounds: a0/b0 < r < a/b (even predecessor below r, odd above r)
    (ha0b0_lt_r : (a0 : ℝ) / b0 < r) (hr_lt_ab : r < (a : ℝ) / b)
    -- Ordering: a1/q > a0/b0 (even convergents increase)
    (ha1q_gt_a0b0 : a1 * b0 > a0 * q)
    (herr_a1q : r - (a1 : ℝ) / q < 1 / (q : ℝ) ^ 2)
    (f : Circle → Circle) (x y : Circle) (hyx : y ≠ x)
    (hf_open : IsCohom (circleGraphOpen r hr) (circleGraphOpen r hr) f)
    (hiso : Nonempty ((circleGraphOpen r hr).induce
        (insert y (equidistantPointsShift a1 x \ ({x} : Set Circle))) ≃g
      fractionGraph a1 q)) :
    dist (f y) (f x) ≤ 2 / a := by
  -- The proof follows the structure of Lemma 5.5.
  --
  -- Full proof structure:
  --
  -- Key insight: For convergent pairs from odd_even_convergent_pair_data_large_both:
  -- - (a, b) = (p_{2n-1}, q_{2n-1}) is odd convergent above r
  -- - (a1, b1) = (p_{2n}, q_{2n}) is even convergent below r
  -- - q = ⌈a1/r⌉ = b1 (by ceil_convergent_even_eq_den)
  -- - Determinant: a1 * b - b1 * a = -1 (Stern-Brocot neighbors)
  --
  -- Gap contradiction: If any gap in f(S_y) > 1/a:
  -- 1. Rounding to a points is non-surjective (roundToZModShift_not_surj_of_gap)
  -- 2. Rounding gives cohom E_{a1/q} → E_{a/floor(a/r)} = E_{a/b} (floor_convergent_odd_eq_den)
  -- 3. Non-surjective cohom factors through E_{a/b} \ {v} ≃ E_{predecessor(a/b)}
  -- 4. By CFA(2), predecessor(a/b) = (p_{2n-2}/q_{2n-2}) (previous even convergent)
  -- 5. Even convergents increase: a1/b1 = p_{2n}/q_{2n} > p_{2n-2}/q_{2n-2}
  -- 6. Since q = b1, we have cohom E_{a1/b1} → E_{p_{2n-2}/q_{2n-2}}
  -- 7. By fractionGraph_no_cohom_to_predecessor, contradiction!
  --
  -- Distance extraction: All gaps ≤ 1/a → dist(f(x), f(y)) ≤ 2/a
  -- - f(skeleton) is shared between f(S_x) and f(S_y)
  -- - f(x) and f(y) are in the same "slot" of width ≤ 2/a
  --
  -- Key infrastructure already in place:
  -- - roundToZModShift_not_surj_of_gap
  -- - rounding_gives_cohom_to_fraction
  -- - fractionGraph_remove_vertex_equiv (Section3/FractionGraphs.lean)
  -- - fractionGraph_no_cohom_to_predecessor
  -- - sternBrocot_predecessor_lt (Section3/FractionGraphs.lean)
  -- - ceil_convergent_even_eq_den
  -- - floor_convergent_odd_eq_den
  --
  have ha_pos' : (0 : ℝ) < a := Nat.cast_pos.mpr ha_pos
  have ha_ne_zero : (a : ℝ) ≠ 0 := ne_of_gt ha_pos'
  -- Use the trivial circle distance bound as a baseline
  have hdist_le_half : dist (f y) (f x) ≤ 1 / 2 := circleDistance_le_half (f y) (f x)
  -- For a ≤ 4: 2/a ≥ 1/2, so the trivial bound suffices
  -- For a > 4: 2/a < 1/2, so we need the full gap argument
  by_cases ha_le : a ≤ 4
  · -- When a ≤ 4: 2/a ≥ 1/2, so trivial bound dist ≤ 1/2 ≤ 2/a works
    have h2a_ge : (1 : ℝ) / 2 ≤ 2 / a := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) ha_pos']
      have : (a : ℝ) ≤ 4 := by exact_mod_cast ha_le
      linarith
    exact le_trans hdist_le_half h2a_ge
  · -- When a > 4: Need the full gap argument (see proof structure above)
    -- The proof shows all gaps in f(S_y) are ≤ 1/a by contradiction:
    --
    -- Gap contradiction structure (tex lines 2300-2302):
    -- 1. If some gap > 1/a, rounding to a equidistant points misses a cell
    -- 2. This gives non-surjective cohom E_{a1/q} → E_{a/b} (where floor(a/r) = b)
    -- 3. Non-surjective means image in E_{a/b} \ {v} ≃ E_{a0/b0} (predecessor)
    -- 4. So we have Cohom (fractionGraph a1 q) (fractionGraph a0 b0)
    -- 5. By fractionGraph_ordering_reverse: a1 * b0 ≤ a0 * q
    -- 6. But ha1q_gt_a0b0 says a1 * b0 > a0 * q
    -- 7. Contradiction! So all gaps ≤ 1/a.
    --
    -- Distance extraction: Once we know all gaps ≤ 1/a:
    -- - f(skeleton) divides the circle into a1-1 arcs
    -- - f(y) is in one arc of width ≤ 2/a (since gap ≤ 1/a on each side)
    -- - f(x) is also in the same arc (by symmetric argument with S_x)
    -- - Hence dist(f(y), f(x)) ≤ 2/a
    --
    -- Key lemmas used:
    -- - roundToZModShift_not_surj_of_gap: gap > 1/M → rounding non-surjective
    -- - rounding_gives_cohom_to_fraction: rounding cohom E_{N/q} → E_{M/floor(M/r)}
    -- - fractionGraph_remove_vertex_equiv: E_{p/q} \ {v} ≃ E_{predecessor(p,q)}
    -- - fractionGraph_ordering_reverse: Cohom implies ordering
    --
    -- The predecessor info (a0, b0, hpred_det, ha1q_gt_a0b0) enables the contradiction.
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
    haveI : NeZero a0 := ⟨Nat.pos_iff_ne_zero.mp ha0_pos⟩
    -- Step 1: Get the ordering contradiction from predecessor
    have hord_contradiction : a1 * b0 ≤ a0 * q → False := by
      intro hle
      have hgt := ha1q_gt_a0b0
      omega
    -- Step 2: Show any cohom E_{a1/q} → E_{a0/b0} contradicts ordering
    have hno_cohom : ¬Cohom (fractionGraph a1 q) (fractionGraph a0 b0) := by
      intro hcohom
      -- fractionGraph_ordering_reverse gives (a1 : ℚ) / q ≤ (a0 : ℚ) / b0
      have hord_rat := fractionGraph_ordering_reverse a1 q a0 b0 hq_pos hb0_pos h2q h2b0 hcohom
      -- Convert to natural number multiplication: a1 * b0 ≤ a0 * q
      have hord : a1 * b0 ≤ a0 * q := by
        have h_q_pos : (0 : ℚ) < q := Nat.cast_pos.mpr hq_pos
        have h_b0_pos : (0 : ℚ) < b0 := Nat.cast_pos.mpr hb0_pos
        have h_q_ne : (q : ℚ) ≠ 0 := ne_of_gt h_q_pos
        -- a1/q ≤ a0/b0 means a1/q * b0 ≤ a0 (using le_div_iff₀)
        have h1 : (a1 : ℚ) / q * b0 ≤ a0 := (le_div_iff₀ h_b0_pos).mp hord_rat
        have h2 : (a1 : ℚ) * b0 / q ≤ a0 := by convert h1 using 1; ring
        -- Multiply both sides by q
        have h3 : (a1 : ℚ) * b0 = (a1 : ℚ) * b0 / q * q := by field_simp
        have h4 : (a1 : ℚ) * b0 ≤ (a0 : ℚ) * q := by
          calc (a1 : ℚ) * b0 = (a1 : ℚ) * b0 / q * q := h3
            _ ≤ a0 * q := mul_le_mul_of_nonneg_right h2 (le_of_lt h_q_pos)
        exact_mod_cast h4
      exact hord_contradiction hord
    -- Step 3: Derive auxiliary facts needed for fractionGraph_remove_vertex_equiv
    -- 3a: 2 ≤ b (from hb0_pos and hb0_lt)
    have hb_ge_2 : 2 ≤ b := by
      have hb0_ge_1 : 1 ≤ b0 := hb0_pos
      omega
    -- 3b: Coprimality of a and b (from hpred_det: a * b0 - b * a0 = 1)
    have hcoprime_ab : Nat.Coprime a b := by
      apply Nat.coprime_of_dvd'
      intro d _hd hda hdb
      -- Convert to integers for subtraction
      have h1 : (d : ℤ) ∣ (a * b0 : ℤ) := Int.ofNat_dvd.mpr (hda.mul_right b0)
      have h2 : (d : ℤ) ∣ (b * a0 : ℤ) := Int.ofNat_dvd.mpr (hdb.mul_right a0)
      have hsub : (d : ℤ) ∣ ((a * b0 : ℤ) - (b * a0 : ℤ)) := dvd_sub h1 h2
      -- a * b0 - b * a0 = 1 (from hpred_det, converted to ℤ)
      have hconv : (a * b0 : ℤ) - (b * a0 : ℤ) = 1 := by
        have h' : a * b0 = b * a0 + 1 := by omega
        omega
      rw [hconv] at hsub
      have hd_eq_1 := Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp hsub)
      simp [hd_eq_1]
    -- Step 4: Gap bound proof by contradiction
    -- We prove: dist(f(y), f(x)) ≤ 2/a by showing all gaps in f(S_y) are ≤ 1/a
    --
    -- Key insight: If any gap > 1/a, we can construct a cohom to predecessor:
    -- 1. roundToZModShift_not_surj_of_gap gives non-surjective rounding for some shift
    -- 2. The composition E_{a1/q} → Circle → E_{a/b} is non-surjective
    -- 3. Non-surjective cohom factors through E_{a/b} - v
    -- 4. E_{a/b} - v ≃ E_{a0/b0} by fractionGraph_remove_vertex_equiv
    -- 5. Cohom E_{a1/q} E_{a0/b0} contradicts hno_cohom
    --
    -- Gap argument (Lemma 5.5):
    -- - If gap > 1/a, rounding to a points misses a cell
    -- - This gives non-surjective cohom to E_{a/b}
    -- - E_{a/b} - v ≃ E_{a0/b0} (predecessor)
    -- - Cohom E_{a1/q} E_{a0/b0} contradicts ordering
    --
    -- Distance extraction once gaps ≤ 1/a are established:
    -- f(y) is adjacent to skeleton points f(s_i), f(s_j) in cyclic order
    -- The arc from f(s_i) to f(y) to f(s_j) has length ≤ 2 * (1/a) = 2/a
    -- f(x) is also in this arc (same skeleton), so dist(f(y), f(x)) ≤ 2/a
    --
    -- Gap argument via contradiction:
    by_contra h_not_le
    push_neg at h_not_le
    -- h_not_le : 2 / a < dist (f y) (f x)
    -- This means f(y) and f(x) are "far apart"
    -- Need to show this implies a gap > 1/a in f(S_y)
    -- Then apply the gap contradiction argument
    --
    -- The key lemma chain:
    -- 1. dist(f(y), f(x)) > 2/a implies ∃ gap > 1/a in f(S_y)
    -- 2. Gap > 1/a → rounding non-surjective (roundToZModShift_not_surj_of_gap)
    -- 3. Non-surjective → Cohom E_{a1/q} E_{a0/b0} (via fractionGraph_remove_vertex_equiv)
    -- 4. Contradiction with hno_cohom
    --
    -- For step 3, we need:
    -- - The rounding gives cohom E_{a1/q} → E_{a/b} (by rounding_gives_cohom_to_fraction)
    -- - Non-surjective factors through E_{a/b}.induce (image)
    -- - image ⊆ {x | x ≠ v} for some v
    -- - E_{a/b} - v ≃ E_{a0/b0}
    have h_remove := fractionGraph_remove_vertex_equiv a b hb_ge_2 h2b hcoprime_ab (0 : ZMod a)
    obtain ⟨p', q', hp'_pos, hq'_pos, hp'_lt, hq'_lt, hbezout, hcohom_fwd, hcohom_bwd⟩ := h_remove
    -- hbezout : a * q' - b * p' = 1
    -- This means (p', q') is the Stern-Brocot predecessor of (a, b)
    -- By uniqueness, p' = a0 and q' = b0
    -- Need to verify: a * b0 - b * a0 = 1 = a * q' - b * p' and p' < a, q' < b
    -- By Stern-Brocot predecessor uniqueness (from hpred_det), we have p' = a0, q' = b0
    -- Use sternBrocotPredecessor_unique to show (p', q') = (a0, b0)
    have huniq := sternBrocotPredecessor_unique a b a0 b0 p' q' hcoprime_ab
      ha0_pos ha0_lt hb0_pos hb0_lt hp'_pos hp'_lt hq'_pos hq'_lt hpred_det hbezout
    have ha0_eq_p' : a0 = p' := huniq.1
    have hb0_eq_q' : b0 = q' := huniq.2
    -- Now we know E_{a/b} - v ≃ E_{a0/b0}
    -- Substitute: E[p'/q'] becomes E[a0/b0]
    subst ha0_eq_p' hb0_eq_q'
    -- hcohom_fwd : Cohom (E_{a/b}.induce {x | x ≠ 0}) E_{a0/b0}
    -- hcohom_bwd : Cohom E_{a0/b0} (E_{a/b}.induce {x | x ≠ 0})
    --
    -- The gap argument: if dist(f(y), f(x)) > 2/a, there's a gap > 1/a
    -- This leads to non-surjective cohom to E_{a/b}, factoring through E_{a/b} - v
    -- Then Cohom E_{a1/q} E_{a0/b0}, contradicting hno_cohom
    -- ═══════════════════════════════════════════════════════════════════════════
    -- GAP ARGUMENT: Construct Cohom E_{a1/q} E_{a0/b0} from dist > 2/a
    -- ═══════════════════════════════════════════════════════════════════════════
    -- Following Lemma 5.5:
    --
    -- Step 1: f(S_y) has a1 points forming a cyclic order on Circle
    --         (from hiso and the cohom f preserving structure)
    --
    -- Step 2: dist(f(y), f(x)) > 2/a implies ∃ gap > 1/a in f(S_y)
    --         Proof: f(y) is adjacent to skeleton points f(s_i), f(s_j) in cyclic order.
    --         If all gaps ≤ 1/a, then the arc containing f(y) has width ≤ 2/a.
    --         f(x) is also in this arc (same skeleton in S_x).
    --         So dist(f(y), f(x)) ≤ 2/a. Contrapositive gives gap > 1/a.
    --
    -- Step 3: Gap > 1/a → non-surjective rounding for some shift
    --         By roundToZModShift_not_surj_of_gap with M = a
    --
    -- Step 4: Composition E_{a1/q} → f(S_y) → E_{a/b} is a cohom
    --         - hiso gives S_y ≃ E_{a1/q}
    --         - f: S_y → f(S_y) is cohom (restriction of hf_open)
    --         - roundToZModShift a t: Circle → E_{a/b} is cohom (by circle_rounding)
    --         - floor(a/r) = b by floor_convergent_odd_eq_den
    --
    -- Step 5: Non-surjective cohom factors through E_{a/b} - v
    --         By isCohom_corestrict to image, which misses some v ∈ ZMod a
    --
    -- Step 6: E_{a/b} - v → E_{a0/b0} by hcohom_fwd
    --
    -- Step 7: Transitivity: Cohom E_{a1/q} E_{a0/b0}
    --         Contradiction with hno_cohom!
    -- ═══════════════════════════════════════════════════════════════════════════
    -- ═══════════════════════════════════════════════════════════════════════════
    -- CONSTRUCTION: Cohom E[a1/q] E[a0/b0] from dist > 2/a
    -- ═══════════════════════════════════════════════════════════════════════════
    -- The detailed construction follows Lemma 5.5:
    -- 1. dist(f(y), f(x)) > 2/a implies there's a gap > 1/a in f(S_y)
    -- 2. A gap > 1/a means rounding to a equidistant points (with appropriate shift)
    --    is non-surjective (by roundToZModShift_not_surj_of_gap)
    -- 3. The composition E[a1/q] → S_y → Circle → Circle → E[a/b] is a cohom
    -- 4. The non-surjective image misses some vertex v ∈ ZMod a
    -- 5. Factor through E[a/b].induce{x | x ≠ v} ≃ E[a0/b0] (predecessor)
    -- 6. This gives Cohom E[a1/q] E[a0/b0], contradicting hno_cohom
    --
    -- The key infrastructure:
    -- - roundToZModShift_cohom_open: rounding with shift is a cohom
    -- - roundToZModShift_not_surj_of_gap: gap > 1/a implies non-surjective rounding
    -- - hcohom_fwd: E[a/b].induce{x | x ≠ 0} → E[a0/b0]
    -- - floor_convergent_odd_eq_den: floor(a/r) = b
    --
    -- Uses:
    -- 1. Gap existence lemma: dist > 2/a implies gap > 1/a in f(S_y)
    -- 2. Corestriction/factoring lemmas for non-surjective cohoms
    -- 3. Matching floor(a/r) = b
    --
    -- PROOF STRUCTURE:
    -- ════════════════════════════════════════════════════════════════════════
    -- Let S_y = insert y (equidistantPointsShift a1 x \ {x})
    -- Let skeleton = equidistantPointsShift a1 x \ {x} = S_y \ {y}
    --
    -- Step A: f(S_y) structure
    --   - S_y ≃ E_{a1/q} (from hiso)
    --   - f: circleGraphOpen r → circleGraphOpen r is cohom (from hf_open)
    --   - f(S_y) ≃ E_{a1/q} (by core argument: finite_induce + CFA)
    --
    -- Step B: Slot argument (KEY LEMMA)
    --   - f(skeleton) = f(S_y) \ {f(y)} has a1-1 points
    --   - f(y) is in a "slot" of f(skeleton) with cyclic neighbors f(s_prev), f(s_next)
    --   - By shared skeleton: x is in same position as y relative to skeleton
    --   - Therefore f(x) is in same slot as f(y) relative to f(skeleton)
    --   - If all gaps ≤ 1/a, then slot width ≤ 2/a
    --   - Contrapositive: dist(f(y), f(x)) > 2/a implies ∃ gap > 1/a
    --
    -- Step C: Rounding gives cohom to E_{a/b}
    --   - floor(a/r) = b (by floor_convergent_odd_eq_den, since a/b = p_{2n-1}/q_{2n-1})
    --   - roundToZModShift_cohom_open: Circle → E_{a/floor(a/r)} = E_{a/b} is cohom
    --
    -- Step D: Non-surjective rounding from gap
    --   - Gap > 1/a in f(S_y) (from Step B)
    --   - roundToZModShift_not_surj_of_gap: ∃ shift t, rounding misses cell v
    --   - Composition E_{a1/q} → S_y → f(S_y) → E_{a/b} is non-surjective
    --
    -- Step E: Factor through vertex removal
    --   - Non-surjective image ⊆ E_{a/b}.induce {x | x ≠ v}
    --   - Use isCohom_corestrict for factoring
    --   - Need to translate v to 0: E_{a/b} is vertex-transitive
    --   - hcohom_fwd: E_{a/b}.induce {x | x ≠ 0} → E_{a0/b0}
    --
    -- Step F: Derive contradiction
    --   - Compose: Cohom E_{a1/q} E_{a0/b0}
    --   - Contradicts hno_cohom
    -- ════════════════════════════════════════════════════════════════════════
    --
    -- Use the proved lemmas to complete the proof.
    -- The full proof follows Lemma 5.5.
    --
    -- Step A: Define S_y, get properties
    let S_y := insert y (equidistantPointsShift a1 x \ ({x} : Set Circle))
    have hS_y_finite : S_y.Finite := Set.Finite.insert y
      ((equidistantPointsShift_finite a1 x).subset (Set.diff_subset))
    have ha1_ge_3 : 3 ≤ a1 := by
      -- From h2b0 : 2 * b0 ≤ a0, so a0 ≥ 2 * b0
      -- From ha1q_gt_a0b0 : a1 * b0 > a0 * q ≥ (2 * b0) * q = 2 * b0 * q
      -- Dividing by b0 > 0: a1 > 2 * q
      -- Since a1, q are naturals and q ≥ 1: a1 ≥ 2 * q + 1 ≥ 3
      have h_a0_ge : 2 * b0 ≤ a0 := h2b0
      have h_strict : (2 * q) * b0 < a1 * b0 := by
        calc (2 * q) * b0 = 2 * b0 * q := by ring
          _ ≤ a0 * q := Nat.mul_le_mul_right q h_a0_ge
          _ < a1 * b0 := ha1q_gt_a0b0
      have h_a1_gt : 2 * q < a1 := Nat.lt_of_mul_lt_mul_right h_strict
      omega
    have hcard_y : hS_y_finite.toFinset.card = a1 :=
      fractionGraph_iso_card r hr a1 q S_y hS_y_finite hiso
    have hy_mem : y ∈ S_y := Set.mem_insert y _
    -- Derive y ∉ equidistantPointsShift a1 x from cardinality
    have hy_not_in_eps : y ∉ equidistantPointsShift a1 x := by
      intro hy_in
      -- If y ∈ equidistantPointsShift a1 x, since hyx.symm : y ≠ x, we have y ∈ skeleton
      have hy_skel : y ∈ equidistantPointsShift a1 x \ {x} := by
        refine ⟨hy_in, ?_⟩
        exact fun h => hyx h
      -- So S_y = insert y skeleton = skeleton (y is already there)
      have hS_y_eq : S_y = equidistantPointsShift a1 x \ {x} :=
        Set.insert_eq_self.mpr hy_skel
      -- Get isomorphism for equidistantPointsShift using the proved lemma
      have hiso_eps : Nonempty ((circleGraphOpen r hr).induce (equidistantPointsShift a1 x) ≃g
          fractionGraph a1 q) :=
        equidistantPointsShift_iso_from_swap_iso r hr hirr a1 q hq_pos h2q x y hyx.symm hiso
      -- Therefore |equidistantPointsShift a1 x| = a1
      have heps_card : (equidistantPointsShift_finite a1 x).toFinset.card = a1 :=
        fractionGraph_iso_card r hr a1 q _ (equidistantPointsShift_finite a1 x)
          hiso_eps
      -- x ∈ equidistantPointsShift a1 x
      have hx_in : x ∈ equidistantPointsShift a1 x :=
        mem_equidistantPointsShift a1 x
      -- |skeleton| = a1 - 1
      have hskel_finite :=
        (equidistantPointsShift_finite a1 x).subset
          (Set.diff_subset : _ \ {x} ⊆ _)
      have hskel_card :
          hskel_finite.toFinset.card = a1 - 1 := by
        have h_eq : hskel_finite.toFinset =
            (equidistantPointsShift_finite a1 x).toFinset
              \ {x} := by
          ext z
          simp only [Set.Finite.mem_toFinset, Set.mem_diff, Set.mem_singleton_iff,
            Finset.mem_sdiff, Finset.mem_singleton]
        rw [h_eq, Finset.card_sdiff]
        have hx_in_finset : x ∈ (equidistantPointsShift_finite a1 x).toFinset :=
          (Set.Finite.mem_toFinset _).mpr hx_in
        have hinter : ({x} : Finset Circle) ∩ (equidistantPointsShift_finite a1 x).toFinset = {x} :=
          Finset.singleton_inter_of_mem hx_in_finset
        rw [hinter, Finset.card_singleton, heps_card]
      -- S_y = skeleton, so |S_y| = |skeleton| = a1 - 1
      have h_finset_eq : hS_y_finite.toFinset = hskel_finite.toFinset := by
        ext z
        simp only [Set.Finite.mem_toFinset, hS_y_eq]
      rw [h_finset_eq] at hcard_y
      -- But hcard_y says |S_y| = a1, contradiction
      omega
    -- Step B: Define S_x = equidistantPointsShift a1 x
    let S_x := equidistantPointsShift a1 x
    have hS_x_eq : S_x = insert x (S_y \ {y}) :=
      equidistantPointsShift_insert_diff_eq a1 x y hyx.symm hy_not_in_eps
    -- Step C: Get isomorphism for S_x with parameter r
    have hiso_Sx_r : Nonempty ((circleGraphOpen r hr).induce S_x ≃g fractionGraph a1 q) :=
      equidistantPointsShift_iso_from_swap_iso r hr hirr a1 q hq_pos h2q x y hyx.symm hiso
    -- Step D: Get isomorphisms for f(S_y) and f(S_x) using the proved lemmas
    have hiso_fSy_r := cohom_image_preserves_fractionGraph_iso (circleGraphOpen r hr) r hr hirr
      (finite_induce_open r hr)
      a1 q hq_pos h2q hcoprime_a1q herr_a1q S_y hS_y_finite hiso f hf_open
    have hiso_fSx_r := cohom_image_preserves_fractionGraph_iso (circleGraphOpen r hr) r hr hirr
      (finite_induce_open r hr)
      a1 q hq_pos h2q hcoprime_a1q herr_a1q
      S_x (equidistantPointsShift_finite a1 x) hiso_Sx_r f hf_open
    -- Step E: Apply gap_exists_of_dist_gt (now uses parameter r directly)
    have ha_ge_3 : 3 ≤ a := by
      have h1 : 2 * b ≤ a := h2b
      have h2 : 2 ≤ b := hb_ge_2
      omega
    -- Monotonicity of circleGraphOpen
    have hG_mono_open : ∀ u v w : Circle, u ≠ v → u ≠ w →
        (circleGraphOpen r hr).Adj u w → dist u v < dist u w →
        (circleGraphOpen r hr).Adj u v := by
      intro u v w huv _huw ⟨_, hdw⟩ hdist
      exact ⟨huv, lt_trans hdist hdw⟩
    have hG_ccw_trans_open : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
        (circleGraphOpen r hr).Adj u w → (circleGraphOpen r hr).Adj u v →
        repFrom u v < repFrom u w → repFrom u w ≤ 1/2 →
        (circleGraphOpen r hr).Adj v w := by
      intro u v w huv _huw hvw ⟨_, hduw⟩ ⟨_, _⟩ hrep_lt hrep_le
      refine ⟨hvw, ?_⟩
      simp only [circleDistance] at hduw ⊢
      linarith [dist_le_repFrom v w, repFrom_ordered u v w (le_of_lt hrep_lt),
        repFrom_pos_of_ne u v (Ne.symm huv), dist_eq_repFrom_of_le_half u w hrep_le]
    have hgap := gap_exists_of_dist_gt (circleGraphOpen r hr)
      a a1 S_y hS_y_finite hcard_y y x hy_mem hyx.symm
      S_x hS_x_eq f ha_ge_3 ha1_ge_3 q hq_ge_2 hq_pos h2q hcoprime_a1q hiso_fSy_r hiso_fSx_r
      hG_mono_open hG_ccw_trans_open h_not_le
    -- Step G: Apply gap_gives_cohom_to_predecessor
    obtain ⟨y₀, gap, hgap_pos, hgap_le, hgap_gt, h_no_points⟩ := hgap
    have hfloor : Nat.floor ((a : ℝ) / r) = b :=
      floor_convergent_from_pred r hr hirr a b a0 b0 ha_pos hb_pos h2b ha0_pos ha0_lt hb0_pos hb0_lt
        hpred_det ha0b0_lt_r hr_lt_ab
    have hMr : r ≤ (a : ℝ) := r_le_convergent r hr a b hb_pos hfloor
    have hcohom := gap_gives_cohom_to_predecessor r hr (circleGraphOpen r hr) le_rfl
      a b a1 q a0 b0 ha_pos hb_pos hb_ge_2 h2b
      ha0_pos hb0_pos h2b0 ha0_lt hb0_lt hcoprime_ab hpred_det h2q hq_pos hMr hfloor
      S_y hS_y_finite f y₀ gap hgap_pos hgap_le hgap_gt h_no_points hiso hf_open
    -- Step H: Contradiction
    exact hno_cohom hcohom

/-- Closed case variant of selfCohom_dist_bound_from_convergents.
    The proof is symmetric to the open case. -/
private lemma selfCohom_dist_bound_from_convergents_closed
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (a b a1 q : ℕ) [NeZero a1]
    -- Predecessor of (a, b): same as open case
    (a0 b0 : ℕ)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (ha1_pos : 0 < a1) (hq_pos : 0 < q)
    (ha0_pos : 0 < a0) (hb0_pos : 0 < b0)
    (h2b : 2 * b ≤ a)
    (h2q : 2 * q ≤ a1) -- Ratio condition for E_{a1/q}
    (hq_ge_2 : 2 ≤ q) -- q ≥ 2 (even convergent denominator)
    (hcoprime_a1q : Nat.Coprime a1 q) -- coprimality of convergent pair
    (h2b0 : 2 * b0 ≤ a0)
    (ha0_lt : a0 < a) (hb0_lt : b0 < b)
    (hpred_det : a * b0 - b * a0 = 1)
    -- Convergent bounds: a0/b0 < r < a/b (even predecessor below r, odd above r)
    (ha0b0_lt_r : (a0 : ℝ) / b0 < r) (hr_lt_ab : r < (a : ℝ) / b)
    (ha1q_gt_a0b0 : a1 * b0 > a0 * q)
    (herr_a1q : r - (a1 : ℝ) / q < 1 / (q : ℝ) ^ 2)
    (hq_ceil : q = Nat.ceil ((a1 : ℝ) / r)) -- q equals ceil(a1/r)
    (f : Circle → Circle) (x y : Circle) (hyx : y ≠ x)
    (hf_closed : IsCohom (circleGraphClosed r hr) (circleGraphClosed r hr) f)
    (hiso : Nonempty ((circleGraphClosed r hr).induce
        (insert y (equidistantPointsShift a1 x \ ({x} : Set Circle))) ≃g
      fractionGraph a1 q)) :
    dist (f y) (f x) ≤ 2 / a := by
  -- Symmetric to the open case. See selfCohom_dist_bound_from_convergents for detailed comments.
  have ha_pos' : (0 : ℝ) < a := Nat.cast_pos.mpr ha_pos
  have ha_ne_zero : (a : ℝ) ≠ 0 := ne_of_gt ha_pos'
  have hdist_le_half : dist (f y) (f x) ≤ 1 / 2 := circleDistance_le_half (f y) (f x)
  by_cases ha_le : a ≤ 4
  · have h2a_ge : (1 : ℝ) / 2 ≤ 2 / a := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) ha_pos']
      have : (a : ℝ) ≤ 4 := by exact_mod_cast ha_le
      linarith
    exact le_trans hdist_le_half h2a_ge
  · -- a > 4 case: Full gap argument (symmetric to open case)
    -- Setup: same as open case
    haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha_pos⟩
    haveI : NeZero a0 := ⟨Nat.pos_iff_ne_zero.mp ha0_pos⟩
    -- Step 1: Get the ordering contradiction from predecessor
    have hord_contradiction : a1 * b0 ≤ a0 * q → False := by
      intro hle
      have hgt := ha1q_gt_a0b0
      omega
    -- Step 2: Show any cohom E_{a1/q} → E_{a0/b0} contradicts ordering
    have hno_cohom : ¬Cohom (fractionGraph a1 q) (fractionGraph a0 b0) := by
      intro hcohom
      have hord_rat := fractionGraph_ordering_reverse a1 q a0 b0 hq_pos hb0_pos h2q h2b0 hcohom
      have hord : a1 * b0 ≤ a0 * q := by
        have h_q_pos : (0 : ℚ) < q := Nat.cast_pos.mpr hq_pos
        have h_b0_pos : (0 : ℚ) < b0 := Nat.cast_pos.mpr hb0_pos
        have h_q_ne : (q : ℚ) ≠ 0 := ne_of_gt h_q_pos
        have h1 : (a1 : ℚ) / q * b0 ≤ a0 := (le_div_iff₀ h_b0_pos).mp hord_rat
        have h2 : (a1 : ℚ) * b0 / q ≤ a0 := by convert h1 using 1; ring
        have h3 : (a1 : ℚ) * b0 = (a1 : ℚ) * b0 / q * q := by field_simp
        have h4 : (a1 : ℚ) * b0 ≤ (a0 : ℚ) * q := by
          calc (a1 : ℚ) * b0 = (a1 : ℚ) * b0 / q * q := h3
            _ ≤ a0 * q := mul_le_mul_of_nonneg_right h2 (le_of_lt h_q_pos)
        exact_mod_cast h4
      exact hord_contradiction hord
    -- Step 3: Auxiliary facts for fractionGraph_remove_vertex_equiv
    have hb_ge_2 : 2 ≤ b := by
      have hb0_ge_1 : 1 ≤ b0 := hb0_pos
      omega
    have hcoprime_ab : Nat.Coprime a b := by
      apply Nat.coprime_of_dvd'
      intro d _hd hda hdb
      have h1 : (d : ℤ) ∣ (a * b0 : ℤ) := Int.ofNat_dvd.mpr (hda.mul_right b0)
      have h2 : (d : ℤ) ∣ (b * a0 : ℤ) := Int.ofNat_dvd.mpr (hdb.mul_right a0)
      have hsub : (d : ℤ) ∣ ((a * b0 : ℤ) - (b * a0 : ℤ)) := dvd_sub h1 h2
      have hconv : (a * b0 : ℤ) - (b * a0 : ℤ) = 1 := by
        have h' : a * b0 = b * a0 + 1 := by omega
        omega
      rw [hconv] at hsub
      have hd_eq_1 := Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp hsub)
      simp [hd_eq_1]
    -- Step 4: Gap bound proof by contradiction
    -- Key insight: gap_gives_cohom_to_predecessor is generalized to any graph G
    -- with circleGraphOpen ≤ G. Since open ≤ closed (open has fewer edges),
    -- the rounding cohom works for closed too (fewer non-edges to preserve).
    by_contra h_not_le
    push_neg at h_not_le
    have hopen_le_closed : circleGraphOpen r hr ≤ circleGraphClosed r hr := by
      intro u v ⟨hne, hdist⟩
      exact ⟨hne, le_of_lt hdist⟩
    -- Step A: Define S_y, get properties
    let S_y := insert y (equidistantPointsShift a1 x \ ({x} : Set Circle))
    have hS_y_finite : S_y.Finite := Set.Finite.insert y
      ((equidistantPointsShift_finite a1 x).subset (Set.diff_subset))
    have ha1_ge_3 : 3 ≤ a1 := by
      have h_a0_ge : 2 * b0 ≤ a0 := h2b0
      have h_strict : (2 * q) * b0 < a1 * b0 := by
        calc (2 * q) * b0 = 2 * b0 * q := by ring
          _ ≤ a0 * q := Nat.mul_le_mul_right q h_a0_ge
          _ < a1 * b0 := ha1q_gt_a0b0
      have h_a1_gt : 2 * q < a1 := Nat.lt_of_mul_lt_mul_right h_strict
      omega
    have hcard_y : hS_y_finite.toFinset.card = a1 :=
      fractionGraph_iso_card_closed r hr a1 q S_y hS_y_finite hiso
    have hy_mem : y ∈ S_y := Set.mem_insert y _
    -- Derive y ∉ equidistantPointsShift a1 x from cardinality
    have hy_not_in_eps : y ∉ equidistantPointsShift a1 x := by
      intro hy_in
      have hy_skel : y ∈ equidistantPointsShift a1 x \ {x} := by
        refine ⟨hy_in, ?_⟩
        exact fun h => hyx h
      have hS_y_eq : S_y = equidistantPointsShift a1 x \ {x} :=
        Set.insert_eq_self.mpr hy_skel
      -- Get closed iso for equidistantPointsShift using open→closed equality
      have ha1_ge_2 : 2 ≤ a1 := by omega
      rcases circleGraph_equidistant_induced_open r hr a1 ha1_ge_2 with ⟨iso_base, _⟩
      have iso_shift := (circleGraphOpen_induce_shift_iso r hr a1 x).trans iso_base
      -- Convert to closed iso
      have hopen_eq_closed := circleGraphOpen_induce_eq_closed_equidistant r hr hirr a1 x
      have iso_closed_eps : (circleGraphClosed r hr).induce (equidistantPointsShift a1 x) ≃g
          fractionGraph a1 (Nat.ceil ((a1 : ℝ) / r)) := by
        rw [← hopen_eq_closed]; exact iso_shift
      have heps_card : (equidistantPointsShift_finite a1 x).toFinset.card = a1 :=
        fractionGraph_iso_card_closed r hr a1 (Nat.ceil ((a1 : ℝ) / r)) _
          (equidistantPointsShift_finite a1 x) ⟨iso_closed_eps⟩
      have hx_in : x ∈ equidistantPointsShift a1 x :=
        mem_equidistantPointsShift a1 x
      have hskel_finite :=
        (equidistantPointsShift_finite a1 x).subset
          (Set.diff_subset : _ \ {x} ⊆ _)
      have hskel_card :
          hskel_finite.toFinset.card = a1 - 1 := by
        have h_eq : hskel_finite.toFinset =
            (equidistantPointsShift_finite a1 x).toFinset
              \ {x} := by
          ext z
          simp only [Set.Finite.mem_toFinset, Set.mem_diff, Set.mem_singleton_iff,
            Finset.mem_sdiff, Finset.mem_singleton]
        rw [h_eq, Finset.card_sdiff]
        have hx_in_finset : x ∈ (equidistantPointsShift_finite a1 x).toFinset :=
          (Set.Finite.mem_toFinset _).mpr hx_in
        have hinter : ({x} : Finset Circle) ∩ (equidistantPointsShift_finite a1 x).toFinset = {x} :=
          Finset.singleton_inter_of_mem hx_in_finset
        rw [hinter, Finset.card_singleton, heps_card]
      have h_finset_eq : hS_y_finite.toFinset = hskel_finite.toFinset := by
        ext z
        simp only [Set.Finite.mem_toFinset, hS_y_eq]
      rw [h_finset_eq] at hcard_y
      omega
    -- Step B: Define S_x = equidistantPointsShift a1 x
    let S_x := equidistantPointsShift a1 x
    have hS_x_eq : S_x = insert x (S_y \ {y}) :=
      equidistantPointsShift_insert_diff_eq a1 x y hyx.symm hy_not_in_eps
    -- Step C: Get closed isomorphism for S_x
    -- Get the open equidistant iso and convert to closed
    have ha1_ge_2 : 2 ≤ a1 := by omega
    rcases circleGraph_equidistant_induced_open r hr a1 ha1_ge_2 with ⟨iso_base, _⟩
    have iso_shift := (circleGraphOpen_induce_shift_iso r hr a1 x).trans iso_base
    have hopen_eq_closed := circleGraphOpen_induce_eq_closed_equidistant r hr hirr a1 x
    have hiso_Sx_closed : Nonempty ((circleGraphClosed r hr).induce S_x ≃g fractionGraph a1 q) :=
      by
      change Nonempty ((circleGraphClosed r hr).induce (equidistantPointsShift a1 x) ≃g
                       fractionGraph a1 q)
      rw [← hopen_eq_closed, hq_ceil]
      exact ⟨iso_shift⟩
    -- Step D: Get isomorphisms for f(S_y) and f(S_x) using cohom_image_preserves
    have hiso_fSy := cohom_image_preserves_fractionGraph_iso (circleGraphClosed r hr) r hr hirr
      (finite_induce_closed r hr)
      a1 q hq_pos h2q hcoprime_a1q herr_a1q S_y hS_y_finite hiso f hf_closed
    have hiso_fSx := cohom_image_preserves_fractionGraph_iso (circleGraphClosed r hr) r hr hirr
      (finite_induce_closed r hr)
      a1 q hq_pos h2q hcoprime_a1q herr_a1q S_x
        (equidistantPointsShift_finite a1 x) hiso_Sx_closed
        f hf_closed
    -- Step E: Apply gap_exists_of_dist_gt (already generalized to any graph)
    have ha_ge_3 : 3 ≤ a := by
      have h1 : 2 * b ≤ a := h2b
      have h2 : 2 ≤ b := hb_ge_2
      omega
    -- Monotonicity of circleGraphClosed
    have hG_mono_closed : ∀ u v w : Circle, u ≠ v → u ≠ w →
        (circleGraphClosed r hr).Adj u w → dist u v < dist u w →
        (circleGraphClosed r hr).Adj u v := by
      intro u v w huv _huw ⟨_hne, hdw⟩ hdist
      exact ⟨huv, le_of_lt (lt_of_lt_of_le hdist hdw)⟩
    have hG_ccw_trans_closed : ∀ u v w : Circle, u ≠ v → u ≠ w → v ≠ w →
        (circleGraphClosed r hr).Adj u w → (circleGraphClosed r hr).Adj u v →
        repFrom u v < repFrom u w → repFrom u w ≤ 1/2 → (circleGraphClosed r hr).Adj v w := by
      intro u v w huv _huw hvw ⟨_, hduw⟩ ⟨_, _⟩ hrep_lt hrep_le
      refine ⟨hvw, ?_⟩
      simp only [circleDistance] at hduw ⊢
      linarith [dist_le_repFrom v w, repFrom_ordered u v w (le_of_lt hrep_lt),
        repFrom_pos_of_ne u v (Ne.symm huv), dist_eq_repFrom_of_le_half u w hrep_le]
    have hgap := gap_exists_of_dist_gt
      (circleGraphClosed r hr) a a1 S_y hS_y_finite
      hcard_y y x hy_mem hyx.symm
      S_x hS_x_eq f ha_ge_3 ha1_ge_3 q hq_ge_2 hq_pos h2q hcoprime_a1q hiso_fSy hiso_fSx
      hG_mono_closed hG_ccw_trans_closed h_not_le
    -- Step F: Apply gap_gives_cohom_to_predecessor (now generalized to G with open ≤ G)
    obtain ⟨y₀, gap, hgap_pos, hgap_le, hgap_gt, h_no_points⟩ := hgap
    have hfloor : Nat.floor ((a : ℝ) / r) = b :=
      floor_convergent_from_pred r hr hirr a b a0 b0 ha_pos hb_pos h2b ha0_pos ha0_lt hb0_pos hb0_lt
        hpred_det ha0b0_lt_r hr_lt_ab
    have hMr : r ≤ (a : ℝ) := r_le_convergent r hr a b hb_pos hfloor
    have hcohom := gap_gives_cohom_to_predecessor r hr (circleGraphClosed r hr) hopen_le_closed
      a b a1 q a0 b0 ha_pos hb_pos hb_ge_2 h2b
      ha0_pos hb0_pos h2b0 ha0_lt hb0_lt hcoprime_ab hpred_det h2q hq_pos hMr hfloor
      S_y hS_y_finite f y₀ gap hgap_pos hgap_le hgap_gt h_no_points hiso hf_closed
    -- Step G: Contradiction
    exact hno_cohom hcohom

/-- Lemma 5.5: Self-cohomomorphisms of irrational circle graphs are continuous.

    Proof outline:
    1. For irrational r, take convergents p_{2n}/q_{2n} and p_{2n-1}/q_{2n-1}
    2. For any x ∈ C, the p_{2n} equidistant points containing x induce E_{p_{2n}/q_{2n}}
    3. For y close to x, swap set S_y = {y, s_1, ..., s_{p_{2n}-1}} still induces E_{p_{2n}/q_{2n}}
    4. f(S_y) must induce E_{p_{2n}/q_{2n}} (by cohomomorphism ordering arguments)
    5. Key claim: distance between consecutive points in f(S_y) is ≤ 1/p_{2n-1}
       - If not, rounding to p_{2n-1} equidistant points gives non-surjective cohom
       - This contradicts fractionGraph_no_cohom_to_predecessor
    6. Hence f maps an arc around x to an arc of length ≤ 1/p_{2n-1}, proving continuity -/
theorem circleGraph_selfCohom_continuous (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (f : Circle → Circle)
    (hf : IsCohom (circleGraphOpen r hr) (circleGraphOpen r hr) f ∨
          IsCohom (circleGraphClosed r hr) (circleGraphClosed r hr) f) :
    Continuous f := by
  -- Since r is irrational and r ≥ 2, we have r > 2 (as 2 is rational)
  have hr' : 2 < r := by
    have h2_rat : ¬Irrational (2 : ℝ) := Nat.not_irrational 2
    rcases lt_or_eq_of_le hr with hlt | heq
    · exact hlt
    · exfalso; rw [← heq] at hirr; exact h2_rat hirr
  -- The proof follows the structure of Lemma 5.5
  -- We prove continuity at each point x using the ε-δ definition
  rw [Metric.continuous_iff]
  intro x ε hε_pos
  -- Step 1: Choose n large enough so that 2/p_{2n-1} < ε
  -- Following Lemma 5.5, we use odd_even_convergent_pair_data_large_both_ext to get:
  -- (a, b) = (p_{2n-1}, q_{2n-1}) - odd convergent (for gap bound)
  -- (a1, b1) = (p_{2n}, q_{2n}) - even convergent (for equidistant points)
  -- Key structure:
  -- - Use a1 = p_{2n} equidistant points, which induce E_{a1/b1}
  -- - Gap bound 1/a = 1/p_{2n-1}
  -- - Since a < a1, we have 1/a > 1/a1 = average gap, so bound is achievable
  -- - If gap > 1/a, rounding gives non-surj cohom E_{a1/b1} → E_{a/b}
  -- - E_{a/b} \ {v} ≃ E_{p_{2n-2}/q_{2n-2}} (predecessor)
  -- - Since p_{2n-2}/q_{2n-2} < p_{2n}/q_{2n} = a1/b1, this contradicts ordering
  set N := Nat.ceil (2 / ε) + 1 with hN_def
  rcases odd_even_convergent_pair_data_large_both_ext r hr' hirr N with
    ⟨n, a, b, a1, b1, ha_pos, hb_pos, ha1_pos, hb1_pos, h2b, h2b1, hratio, hratio1,
     hdet, hb_lt_b1, hN_le_a, hN_le_a1,
     hn_ge_5, hgt_odd, hgt_even, hgt_2n_minus_2, hnums_odd, hdens_odd, hnums_even, hdens_even⟩
  -- Note: hratio : convergent(2n-1) = a/b (odd, above r, for gap bound)
  --       hratio1 : convergent(2n) = a1/b1 (even, below r, for equidistant points)
  --       hdet : a1 * b - b1 * a = -1 (they are Stern-Brocot neighbors)
  --       hN_le_a : N ≤ a (key bound for gap bound)
  --       hN_le_a1 : N ≤ a1
  --       hn_ge_5 : 5 ≤ n (from extended theorem)
  --       hnums_odd : nums(2n-1) = a, hdens_odd : dens(2n-1) = b (identification)
  --       hnums_even : nums(2n) = a1, hdens_even : dens(2n) = b1 (identification)
  -- Step 1b: Compute the predecessor (a0, b0) = (p_{2n-2}, q_{2n-2})
  -- The predecessor of odd convergent (2n-1) is the previous even convergent (2n-2)
  -- By CFA(2) determinant: p_{2n-1} * q_{2n-2} - q_{2n-1} * p_{2n-2} = 1
  have hn_ge_1 : 1 ≤ n := le_trans (by omega : 1 ≤ 5) hn_ge_5
  have hidx_prev : 2 * n - 2 + 1 = 2 * n - 1 := by omega
  -- Get the (2n-2) convergent data using nums_dens_det_irrational_int
  rcases nums_dens_det_irrational_int r hirr (2 * n - 2) with
    ⟨A0, B0, A_odd, B_odd, hA0, hB0, hA_odd, hB_odd, hdet_prev⟩
  -- Convert A0, B0 to natural numbers
  have hB0posR : 0 < (B0 : ℝ) := by
    have h := dens_pos_of_irrational r hirr (2 * n - 2)
    simpa [hB0] using h
  have hB0pos : 0 < B0 := by exact_mod_cast hB0posR
  have hA0posR : 0 < (A0 : ℝ) := by
    -- Even convergent > 2 implies numerator > 2 * denominator > 0
    have hgt : (2 : ℝ) < (r.convergent (2 * n - 2) : ℝ) := hgt_2n_minus_2
    have hratio0 : (r.convergent (2 * n - 2) : ℝ) = (A0 : ℝ) / B0 := by
      have hconv := convergent_cast_eq_nums_div_dens r (2 * n - 2)
      simpa [hA0, hB0] using hconv
    have h : (2 : ℝ) < (A0 : ℝ) / B0 := by rwa [← hratio0]
    have h' : (2 : ℝ) * B0 < A0 := by
      have h'' := mul_lt_mul_of_pos_right h hB0posR
      simp only [div_mul_cancel₀ (A0 : ℝ) (ne_of_gt hB0posR)] at h''
      linarith
    linarith
  have hA0pos : 0 < A0 := by exact_mod_cast hA0posR
  set a0 : ℕ := Int.toNat A0
  set b0 : ℕ := Int.toNat B0
  have hA0_nat : (a0 : ℤ) = A0 := Int.toNat_of_nonneg (le_of_lt hA0pos)
  have hB0_nat : (b0 : ℤ) = B0 := Int.toNat_of_nonneg (le_of_lt hB0pos)
  have ha0_pos : 0 < a0 := by
    apply Nat.pos_of_ne_zero; intro h
    have : (a0 : ℤ) = 0 := by simp [h]
    rw [hA0_nat] at this
    exact (ne_of_gt hA0pos) this
  have hb0_pos : 0 < b0 := by
    apply Nat.pos_of_ne_zero; intro h
    have : (b0 : ℤ) = 0 := by simp [h]
    rw [hB0_nat] at this
    exact (ne_of_gt hB0pos) this
  -- The (2n-2) convergent is a0/b0
  have hratio0 : (r.convergent (2 * n - 2) : ℝ) = (a0 : ℝ) / b0 := by
    have hconv := convergent_cast_eq_nums_div_dens r (2 * n - 2)
    simp only [hA0, hB0] at hconv
    have hA0_cast : (A0 : ℝ) = (a0 : ℝ) := by
      have h : (a0 : ℤ) = A0 := hA0_nat
      calc (A0 : ℝ) = ((a0 : ℤ) : ℝ) := by rw [h]
        _ = (a0 : ℝ) := by simp
    have hB0_cast : (B0 : ℝ) = (b0 : ℝ) := by
      have h : (b0 : ℤ) = B0 := hB0_nat
      calc (B0 : ℝ) = ((b0 : ℤ) : ℝ) := by rw [h]
        _ = (b0 : ℝ) := by simp
    rw [hA0_cast, hB0_cast] at hconv
    exact hconv
  -- Predecessor determinant: a * b0 - b * a0 = 1
  -- The (2n-2) → (2n-1) determinant gives A0 * B_odd - B0 * A_odd = (-1)^{2n-1}
  -- where (A_odd, B_odd) = (p_{2n-1}, q_{2n-1}) = (a, b)
  -- From the extended theorem, we have nums/dens identification:
  -- hnums_odd : nums(2n-1) = (a : ℝ), hdens_odd : dens(2n-1) = (b : ℝ)
  have hA_odd_eq : (GenContFract.of r).nums (2 * n - 1) = (a : ℝ) := hnums_odd
  have hB_odd_eq : (GenContFract.of r).dens (2 * n - 1) = (b : ℝ) := hdens_odd
  -- The predecessor relationship
  -- From nums_dens_det_irrational_int: A0 * B_odd - B0 * A_odd = (-1)^(2n-1) = -1
  -- hA_odd at index 2n-2+1 = 2n-1 gives A_odd = nums(2n-1) = a (via hA_odd_eq)
  -- hB_odd gives B_odd = dens(2n-1) = b (via hB_odd_eq)
  -- So: a0 * b - b0 * a = -1, hence a * b0 - b * a0 = 1
  have hpred_det : a * b0 - b * a0 = 1 := by
    -- First identify A_odd = a and B_odd = b
    have hA_odd' : A_odd = (a : ℤ) := by
      have h1 : (A_odd : ℝ) = (GenContFract.of r).nums (2 * n - 1) := by
        simp only [hidx_prev] at hA_odd; exact hA_odd.symm
      have h2 : (GenContFract.of r).nums (2 * n - 1) = (a : ℝ) := hA_odd_eq
      have h3 : (A_odd : ℝ) = (a : ℝ) := h1.trans h2
      exact_mod_cast h3
    have hB_odd' : B_odd = (b : ℤ) := by
      have h1 : (B_odd : ℝ) = (GenContFract.of r).dens (2 * n - 1) := by
        simp only [hidx_prev] at hB_odd; exact hB_odd.symm
      have h2 : (GenContFract.of r).dens (2 * n - 1) = (b : ℝ) := hB_odd_eq
      have h3 : (B_odd : ℝ) = (b : ℝ) := h1.trans h2
      exact_mod_cast h3
    -- The determinant: A0 * B_odd - B0 * A_odd = (-1)^(2n-1) = -1
    have hpow : (-1 : ℤ)^(2 * n - 2 + 1) = -1 := by
      simp only [hidx_prev]
      have h_ge : 1 ≤ n := le_trans (by omega : 1 ≤ 5) hn_ge_5
      have hodd : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
      exact hodd.neg_one_pow
    have hdet' : A0 * B_odd - B0 * A_odd = -1 := by simp only [hpow] at hdet_prev; exact hdet_prev
    -- Substitute A_odd = a, B_odd = b, A0 = a0, B0 = b0
    have hdet'' : (a0 : ℤ) * b - (b0 : ℤ) * a = -1 := by
      have h := hdet'
      rw [← hA0_nat, ← hB0_nat, hA_odd', hB_odd'] at h
      exact h
    -- Rearrange: a * b0 - b * a0 = -(a0 * b - b0 * a) = 1
    have h_rearr : (a : ℤ) * b0 - (b : ℤ) * a0 = -((a0 : ℤ) * b - (b0 : ℤ) * a) := by ring
    rw [hdet''] at h_rearr
    simp at h_rearr
    omega
  -- Ordering: a0 < a, b0 < b (convergent numerators/denominators increase)
  -- First prove hb0_lt using dens_lt_succ_of_irrational
  have hb0_lt : b0 < b := by
    have hden_lt := dens_lt_succ_of_irrational r hirr (2 * n - 3)
    have h1 : 2 * n - 3 + 1 = 2 * n - 2 := by omega
    have h2 : 2 * n - 3 + 2 = 2 * n - 1 := by omega
    have hlt : (GenContFract.of r).dens (2 * n - 2) < (GenContFract.of r).dens (2 * n - 1) := by
      simpa [h1, h2] using hden_lt
    have h_B0 : (GenContFract.of r).dens (2 * n - 2) = (B0 : ℝ) := hB0
    have h_b0 : (B0 : ℝ) = (b0 : ℝ) := by simp [← hB0_nat]
    have h_b : (GenContFract.of r).dens (2 * n - 1) = (b : ℝ) := hB_odd_eq
    have hlt' : (b0 : ℝ) < (b : ℝ) := by
      calc (b0 : ℝ) = (B0 : ℝ) := h_b0.symm
        _ = (GenContFract.of r).dens (2 * n - 2) := h_B0.symm
        _ < (GenContFract.of r).dens (2 * n - 1) := hlt
        _ = (b : ℝ) := h_b
    exact_mod_cast hlt'
  -- Now derive ha0_lt from hpred_det and hb0_lt
  have ha0_lt : a0 < a := by
    -- From hpred_det : a * b0 - b * a0 = 1 and b > b0, if a ≤ a0 then:
    -- a * b0 - b * a0 ≤ a0 * b0 - b * a0 = a0 * (b0 - b) < 0
    -- But a * b0 - b * a0 = 1 > 0, contradiction. So a > a0.
    by_contra h_not_lt
    push_neg at h_not_lt
    have h_le : a ≤ a0 := h_not_lt
    have h1 : (a : ℤ) * b0 ≤ (a0 : ℤ) * b0 :=
      mul_le_mul_of_nonneg_right (by omega : (a : ℤ) ≤ a0) (by omega)
    have h2 : (a0 : ℤ) * b0 - (b : ℤ) * a0 = (a0 : ℤ) * ((b0 : ℤ) - b) := by ring
    have h3 : (b0 : ℤ) - (b : ℤ) < 0 := by omega
    have h4 : (a0 : ℤ) * ((b0 : ℤ) - b) < 0 := by
      have ha0_pos' : 0 < (a0 : ℤ) := by omega
      exact Int.mul_neg_of_pos_of_neg ha0_pos' h3
    have h5 : (a0 : ℤ) * b0 - (b : ℤ) * a0 < 0 := by linarith
    have h6 : (a : ℤ) * b0 - (b : ℤ) * a0 ≤ (a0 : ℤ) * b0 - (b : ℤ) * a0 := by linarith
    have h7 : (a : ℤ) * b0 - (b : ℤ) * a0 < 0 := by linarith
    have h8 : (a : ℤ) * b0 - (b : ℤ) * a0 = 1 := by omega
    omega
  -- 2 * b0 ≤ a0 (convergent > 2)
  have h2b0 : 2 * b0 ≤ a0 := by
    -- From hgt_2n_minus_2 : 2 < convergent(2n-2) = a0/b0
    have hb0_pos' : (0 : ℝ) < b0 := Nat.cast_pos.mpr hb0_pos
    have h : (2 : ℝ) < (a0 : ℝ) / b0 := by rwa [← hratio0]
    have h' : 2 * (b0 : ℝ) < (a0 : ℝ) := by
      calc (2 : ℝ) * b0 = 2 * b0 := rfl
        _ < (a0 / b0) * b0 := by apply mul_lt_mul_of_pos_right h hb0_pos'
        _ = a0 := by field_simp
    exact_mod_cast le_of_lt h'
  -- Even convergents increase: a1/b1 > a0/b0, i.e., a1 * b0 > a0 * b1
  -- Proof: Use recurrence a1 = gp.b * a + a0, b1 = gp.b * b + b0
  -- Then a1 * b0 - a0 * b1 = gp.b * (a * b0 - a0 * b) = gp.b * 1 = gp.b ≥ 1
  have ha1b0_gt_a0b1 : a1 * b0 > a0 * b1 := by
    -- Get the partial quotient at index 2n-1 for the recurrence
    have hnot : ¬(GenContFract.of r).TerminatedAt (2 * n - 1) :=
      not_terminatedAt_of_irrational r hirr (2 * n - 1)
    have hnone : (GenContFract.of r).s.get? (2 * n - 1) ≠ none := by
      simpa [GenContFract.terminatedAt_iff_s_none] using hnot
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp hnone
    -- gp.a = 1 for continued fractions of reals
    have hgp_a : gp.a = (1 : ℝ) := by
      simpa using (GenContFract.of_partNum_eq_one (v := r) (n := 2 * n - 1) (a := gp.a)
        (GenContFract.partNum_eq_s_a (g := GenContFract.of r) (n := 2 * n - 1) hgp))
    -- gp.b ≥ 1 (partial quotients are positive integers)
    obtain ⟨z_b, hz_b⟩ := GenContFract.exists_int_eq_of_partDen (v := r)
      (n := 2 * n - 1) (b := gp.b)
        (GenContFract.partDen_eq_s_b (g := GenContFract.of r) (n := 2 * n - 1) hgp)
    -- z_b ≥ 1 because partial quotients of GenContFract.of are floors of ≥ 1 values
    have hz_b_ge_1 : 1 ≤ z_b := by
      -- Use the partial quotient bound lemma: 1 ≤ gp.b
      have hb_ge : (1 : ℝ) ≤ gp.b := GenContFract.of_one_le_get?_partDen
        (v := r) (n := 2 * n - 1) (b := gp.b)
        (GenContFract.partDen_eq_s_b (g := GenContFract.of r) (n := 2 * n - 1) hgp)
      have h' : (1 : ℝ) ≤ (z_b : ℝ) := by rw [← hz_b]; exact hb_ge
      exact_mod_cast h'
    -- Index arithmetic: (2n-2) + 2 = 2n
    have hidx_2n : 2 * n - 2 + 2 = 2 * n := by omega
    have hidx_2n1 : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    -- Recurrence for nums: nums(2n) = gp.b * nums(2n-1) + gp.a * nums(2n-2)
    have hrec_nums : (GenContFract.of r).nums (2 * n) =
        gp.b * (GenContFract.of r).nums (2 * n - 1) +
          gp.a * (GenContFract.of r).nums (2 * n - 2) := by
      have h := GenContFract.nums_recurrence (g := GenContFract.of r) (n := 2 * n - 2) (gp := gp)
        (by simp only [hidx_2n1]; exact hgp) (rfl) (rfl)
      simp only [hidx_2n, hidx_2n1] at h; exact h
    -- Recurrence for dens: dens(2n) = gp.b * dens(2n-1) + gp.a * dens(2n-2)
    have hrec_dens : (GenContFract.of r).dens (2 * n) =
        gp.b * (GenContFract.of r).dens (2 * n - 1) +
          gp.a * (GenContFract.of r).dens (2 * n - 2) := by
      have h := GenContFract.dens_recurrence (g := GenContFract.of r) (n := 2 * n - 2) (gp := gp)
        (by simp only [hidx_2n1]; exact hgp) (rfl) (rfl)
      simp only [hidx_2n, hidx_2n1] at h; exact h
    -- Substitute nums and dens identifications
    have ha1_rec : (a1 : ℝ) = gp.b * a + 1 * a0 := by
      have h := hrec_nums
      rw [hnums_even, hnums_odd] at h
      have hA0_eq : (GenContFract.of r).nums (2 * n - 2) = (a0 : ℝ) := by simp [hA0, ← hA0_nat]
      rw [hA0_eq, hgp_a] at h
      exact_mod_cast h
    have hb1_rec : (b1 : ℝ) = gp.b * b + 1 * b0 := by
      have h := hrec_dens
      rw [hdens_even, hdens_odd] at h
      have hB0_eq : (GenContFract.of r).dens (2 * n - 2) = (b0 : ℝ) := by simp [hB0, ← hB0_nat]
      rw [hB0_eq, hgp_a] at h
      exact_mod_cast h
    -- Compute a1 * b0 - a0 * b1 = gp.b * (a * b0 - a0 * b)
    have hcalc : (a1 : ℤ) * b0 - (a0 : ℤ) * b1 = z_b * ((a : ℤ) * b0 - (a0 : ℤ) * b) := by
      have ha1' : (a1 : ℤ) = z_b * a + a0 := by
        have h : (a1 : ℝ) = z_b * a + a0 := by simp only [ha1_rec, hz_b]; ring
        exact_mod_cast h
      have hb1' : (b1 : ℤ) = z_b * b + b0 := by
        have h : (b1 : ℝ) = z_b * b + b0 := by simp only [hb1_rec, hz_b]; ring
        exact_mod_cast h
      calc (a1 : ℤ) * b0 - (a0 : ℤ) * b1
          = (z_b * a + a0) * b0 - a0 * (z_b * b + b0) := by rw [ha1', hb1']
        _ = z_b * a * b0 + a0 * b0 - a0 * z_b * b - a0 * b0 := by ring
        _ = z_b * (a * b0 - a0 * b) := by ring
    -- Use hpred_det: a * b0 - b * a0 = 1
    have hpred_det' : (a : ℤ) * b0 - (a0 : ℤ) * b = 1 := by
      -- hpred_det is over Nat, convert to Int
      have hpred_nat : a * b0 = b * a0 + 1 := by omega
      have h : (a : ℤ) * (b0 : ℤ) = (b : ℤ) * (a0 : ℤ) + 1 := by exact_mod_cast hpred_nat
      linarith
    rw [hpred_det'] at hcalc
    -- So a1 * b0 - a0 * b1 = z_b ≥ 1 > 0
    have hgt_zero : (a1 : ℤ) * b0 - (a0 : ℤ) * b1 ≥ 1 := by linarith
    omega
  -- The gap bound is 1/a = 1/p_{2n-1}. We need 2/a < ε.
  -- Since N ≤ a and N > 2/ε, we get a > 2/ε, hence 2/a < ε.
  have ha_gt : (2 / ε : ℝ) < a := by
    have hN_gt : (2 / ε : ℝ) < N := by
      have h1 : (2 / ε : ℝ) < 2 / ε + 1 := lt_add_one _
      have h2 : 2 / ε + 1 ≤ Nat.ceil (2 / ε) + 1 := by
        have hceil := Nat.le_ceil (2 / ε)
        linarith
      have h3 : (Nat.ceil (2 / ε) + 1 : ℝ) = N := by simp [hN_def]
      linarith
    calc (2 / ε : ℝ) < N := hN_gt
      _ ≤ a := by exact_mod_cast hN_le_a
  have hε_bound : (2 : ℝ) / a < ε := by
    have ha_pos' : (0 : ℝ) < a := Nat.cast_pos.mpr ha_pos
    have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos'
    have hε_ne : (ε : ℝ) ≠ 0 := ne_of_gt hε_pos
    calc (2 : ℝ) / a = (2 / ε) * (ε / a) := by field_simp
      _ < a * (ε / a) := by apply mul_lt_mul_of_pos_right ha_gt; positivity
      _ = ε := by field_simp
  -- Step 2: Get δ from the swap isomorphism lemma
  -- The set of a1 equidistant points containing x induces E_{a1/b1}
  haveI : NeZero a1 := ⟨Nat.pos_iff_ne_zero.mp ha1_pos⟩
  have ha1_ge : 2 ≤ a1 := by
    have h2b1_le := h2b1
    have hb1_ge_1 : 1 ≤ b1 := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hb1_pos)
    omega
  -- Use the new variants that expose q = Nat.ceil(a1/r) for open, q = floor+1 for closed
  rcases circleGraphOpen_induce_swap_iso_q_eq_ceil r hr hirr a1 ha1_ge x with
    ⟨δ₀, hδ₀_pos, hδ₀⟩
  rcases circleGraphClosed_induce_swap_iso_q_eq_floor_succ r hr hirr a1 ha1_ge x with
    ⟨δ₁, hδ₁_pos, hδ₁⟩
  -- Use the minimum of the two deltas
  set δ := min δ₀ δ₁ with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_pos hδ₁_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  -- Case split: y = x is trivial
  by_cases hyx : y = x
  · subst hyx; simp only [_root_.dist_self]; exact hε_pos
  -- For y ≠ x, we use the swap isomorphism
  have hδ₀_le : δ ≤ δ₀ := min_le_left _ _
  have hδ₁_le : δ ≤ δ₁ := min_le_right _ _
  have hy₀ : circleDistance y x < δ₀ := lt_of_lt_of_le hy hδ₀_le
  have hy₁ : circleDistance y x < δ₁ := lt_of_lt_of_le hy hδ₁_le
  -- Get isomorphism: S_y induces E_{a1/q} where q is known explicitly
  rcases hf with hf_open | hf_closed
  · -- Open case: q = Nat.ceil(a1/r) = b1 by ceil_convergent_even_eq_den
    rcases hδ₀ y hy₀ hyx with ⟨hq₀_pos, hiso_open⟩
    -- The q here is Nat.ceil(a1/r) by construction
    set q₀ := Nat.ceil ((a1 : ℝ) / r) with hq₀_def
    -- Show q₀ = b1 using ceil_convergent_even_eq_den
    have hq₀_eq_b1 : q₀ = b1 := by
      rcases ceil_convergent_even_eq_den_ext r hirr n hgt_even with
        ⟨a', b', ha'_pos, hb'_pos, hratio', hceil', hnums_ext, hdens_ext⟩
      have ha'_eq_a1 : a' = a1 := by
        have h : (a' : ℝ) = (a1 : ℝ) := hnums_ext.symm.trans hnums_even
        exact_mod_cast h
      have hb'_eq_b1 : b' = b1 := by
        have h : (b' : ℝ) = (b1 : ℝ) := hdens_ext.symm.trans hdens_even
        exact_mod_cast h
      rw [hq₀_def, ← hb'_eq_b1, ← hceil', ha'_eq_a1]
    have h2q₀ : 2 * q₀ ≤ a1 := by rw [hq₀_eq_b1]; exact h2b1
    -- Derive 2 ≤ q₀ from convergent properties: b0 ≥ 1, b0 < b, b < b1
    have hq₀_ge_2 : 2 ≤ q₀ := by rw [hq₀_eq_b1]; omega
    -- Coprimality of a1 and q₀ from determinant: a1 * b - b1 * a = -1
    have hcoprime_a1_q₀ : Nat.Coprime a1 q₀ := by
      rw [hq₀_eq_b1]
      apply Nat.coprime_of_dvd'
      intro d _hd hda1 hdb1
      have h1 : (d : ℤ) ∣ ((a1 : ℤ) * b) := by exact_mod_cast hda1.mul_right b
      have h2 : (d : ℤ) ∣ ((b1 : ℤ) * a) := by exact_mod_cast hdb1.mul_right a
      have hsub : (d : ℤ) ∣ (-1 : ℤ) := by
        have h := dvd_sub h1 h2; rwa [hdet] at h
      exact_mod_cast dvd_neg.mp hsub
    have ha1q₀_gt_a0b0 : a1 * b0 > a0 * q₀ := by rw [hq₀_eq_b1]; exact ha1b0_gt_a0b1
    -- Derive convergent bounds for floor_convergent_from_pred
    -- Even convergent at index 2n-2 is below r: a0/b0 < r
    have ha0b0_lt_r : (a0 : ℝ) / b0 < r := by
      have hconv_even := convergent_even_lt_irrational r hirr (n - 1)
      have hidx : 2 * (n - 1) = 2 * n - 2 := by omega
      rw [hidx] at hconv_even
      rw [hratio0] at hconv_even
      exact hconv_even
    -- Odd convergent at index 2n-1 is above r: r < a/b
    have hr_lt_ab : r < (a : ℝ) / b := by
      have hconv_odd := convergent_odd_gt_irrational r hirr (n - 1)
      have hidx : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
      rw [hidx] at hconv_odd
      rw [hratio] at hconv_odd
      exact hconv_odd
    -- Derive error bound: r - a1/q₀ < 1/q₀²
    -- From abs_sub_convs_le: |r - convs(2n)| ≤ 1/(dens(2n) * dens(2n+1))
    -- Since dens(2n) = q₀ and dens(2n+1) > dens(2n), this is < 1/q₀²
    have herr_a1q₀ : r - (a1 : ℝ) / q₀ < 1 / (q₀ : ℝ) ^ 2 := by
      have hnotterm := not_terminatedAt_of_irrational r hirr (2 * n)
      have hbound := GenContFract.abs_sub_convs_le hnotterm
      -- Identify convs(2n) = nums(2n)/dens(2n) = a1/q₀
      have hq₀_dens : (q₀ : ℝ) = (GenContFract.of r).dens (2 * n) := by
        rw [hq₀_eq_b1]; exact hdens_even.symm
      have ha1_convs : (GenContFract.of r).convs (2 * n) = (a1 : ℝ) / q₀ := by
        rw [GenContFract.conv_eq_num_div_den, hnums_even, hq₀_dens]
      rw [ha1_convs] at hbound
      -- Even convergent < r, so |r - a1/q₀| = r - a1/q₀
      have heven_lt : (a1 : ℝ) / q₀ < r := by
        have h := convergent_even_lt_irrational r hirr n
        rw [convergent_cast_eq_nums_div_dens, hnums_even, hdens_even] at h
        have hb1_eq : (b1 : ℝ) = (q₀ : ℝ) := by exact_mod_cast hq₀_eq_b1.symm
        rwa [hb1_eq] at h
      have habs_eq : |r - (a1 : ℝ) / q₀| = r - (a1 : ℝ) / q₀ :=
        abs_of_pos (sub_pos.mpr heven_lt)
      rw [habs_eq] at hbound
      -- Now: r - a1/q₀ ≤ 1/(dens(2n) * dens(2n+1)) < 1/dens(2n)² = 1/q₀²
      -- dens(2n) < dens(2n+1) from dens_lt_succ_of_irrational at index 2n-1
      have hdens_lt : (GenContFract.of r).dens (2 * n) <
          (GenContFract.of r).dens (2 * n + 1) := by
        have h := dens_lt_succ_of_irrational r hirr (2 * n - 1)
        simp only [show 2 * n - 1 + 1 = 2 * n from by omega,
                    show 2 * n - 1 + 2 = 2 * n + 1 from by omega] at h
        exact h
      have hd_pos : (0 : ℝ) < (GenContFract.of r).dens (2 * n) := by
        rw [← hq₀_dens]; exact Nat.cast_pos.mpr hq₀_pos
      calc r - (a1 : ℝ) / q₀
        _ ≤ 1 / ((GenContFract.of r).dens (2 * n) *
              (GenContFract.of r).dens (2 * n + 1)) := hbound
        _ < 1 / ((GenContFract.of r).dens (2 * n) *
              (GenContFract.of r).dens (2 * n)) := by
            exact div_lt_div_of_pos_left one_pos (mul_pos hd_pos hd_pos)
              (mul_lt_mul_of_pos_left hdens_lt hd_pos)
        _ = 1 / (q₀ : ℝ) ^ 2 := by
            congr 1; rw [← hq₀_dens]; ring
    have hdist_bound := selfCohom_dist_bound_from_convergents r hr hirr
      a b a1 q₀
      a0 b0  -- predecessor
      ha_pos hb_pos ha1_pos hq₀_pos
      ha0_pos hb0_pos
      h2b
      h2q₀ hq₀_ge_2 hcoprime_a1_q₀
      h2b0
      ha0_lt hb0_lt
      hpred_det
      ha0b0_lt_r hr_lt_ab
      ha1q₀_gt_a0b0
      herr_a1q₀
      f x y hyx hf_open hiso_open
    -- Convert circleDistance to dist and use the chain: dist ≤ 2/a < ε
    have ha_pos' : (0 : ℝ) < a := Nat.cast_pos.mpr ha_pos
    calc dist (f y) (f x) ≤ 2 / a := hdist_bound
      _ < ε := hε_bound
  · -- Closed case: q = Nat.floor(a1/r) + 1 = Nat.ceil(a1/r) = b1 (since r is irrational)
    rcases hδ₁ y hy₁ hyx with ⟨hq₁_pos, hiso_closed⟩
    -- The q here is Nat.floor(a1/r) + 1 by construction
    set q₁ := Nat.floor ((a1 : ℝ) / r) + 1 with hq₁_def
    -- Show q₁ = b1: floor(a1/r) + 1 = ceil(a1/r) = b1 (since a1/r is not an integer)
    have hq₁_eq_b1 : q₁ = b1 := by
      -- For irrational r, a1/r is not a natural number, so floor + 1 = ceil
      have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
      have ha1_pos_r : 0 < (a1 : ℝ) := Nat.cast_pos.mpr ha1_pos
      have hdiv_pos : 0 < (a1 : ℝ) / r := div_pos ha1_pos_r hr_pos
      -- Key: a1/r ≠ n for any natural n, because r is irrational
      have h_not_nat : ∀ m : ℕ, (a1 : ℝ) / r ≠ m := by
        intro m heq
        by_cases hm : m = 0
        · simp only [hm, Nat.cast_zero] at heq
          have : 0 < (a1 : ℝ) / r := hdiv_pos
          linarith
        · have hr_eq : r = (a1 : ℝ) / m := by field_simp [hm] at heq ⊢; linarith
          -- r = a1/m is rational, contradicting hirr
          have hrat : ¬Irrational r := by
            rw [hr_eq]
            simp only [Irrational, not_not]
            use (a1 : ℚ) / m
            push_cast
            rfl
          exact hrat hirr
      have h_x_ne_floor : (a1 : ℝ) / r ≠ Nat.floor ((a1 : ℝ) / r) :=
        h_not_nat (Nat.floor ((a1 : ℝ) / r))
      have hfloor_lt : (Nat.floor ((a1 : ℝ) / r) : ℝ) < (a1 : ℝ) / r := by
        have hle : (Nat.floor ((a1 : ℝ) / r) : ℝ) ≤ (a1 : ℝ) / r :=
          Nat.floor_le (le_of_lt hdiv_pos)
        exact lt_of_le_of_ne hle (ne_comm.mp h_x_ne_floor)
      have hlt_floor_add_one : (a1 : ℝ) / r < (Nat.floor ((a1 : ℝ) / r) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hfloor_add_one_eq_ceil : Nat.floor ((a1 : ℝ) / r) + 1 = Nat.ceil ((a1 : ℝ) / r) := by
        symm
        rw [Nat.ceil_eq_iff (by omega : Nat.floor ((a1 : ℝ) / r) + 1 ≠ 0)]
        constructor
        · simp only [Nat.add_sub_cancel]
          exact hfloor_lt
        · push_cast
          linarith
      rw [hq₁_def, hfloor_add_one_eq_ceil]
      -- Now ceil(a1/r) = b1 by ceil_convergent_even_eq_den
      rcases ceil_convergent_even_eq_den_ext r hirr n hgt_even with
        ⟨a', b', ha'_pos, hb'_pos, hratio', hceil', hnums_ext, hdens_ext⟩
      have ha'_eq_a1 : a' = a1 := by
        have h : (a' : ℝ) = (a1 : ℝ) := hnums_ext.symm.trans hnums_even
        exact_mod_cast h
      have hb'_eq_b1 : b' = b1 := by
        have h : (b' : ℝ) = (b1 : ℝ) := hdens_ext.symm.trans hdens_even
        exact_mod_cast h
      rw [← hb'_eq_b1, ← hceil', ha'_eq_a1]
    have h2q₁ : 2 * q₁ ≤ a1 := by rw [hq₁_eq_b1]; exact h2b1
    -- Derive 2 ≤ q₁ from convergent properties: b0 ≥ 1, b0 < b, b < b1
    have hq₁_ge_2 : 2 ≤ q₁ := by rw [hq₁_eq_b1]; omega
    -- Coprimality of a1 and q₁ from determinant: a1 * b - b1 * a = -1
    have hcoprime_a1_q₁ : Nat.Coprime a1 q₁ := by
      rw [hq₁_eq_b1]
      apply Nat.coprime_of_dvd'
      intro d _hd hda1 hdb1
      have h1 : (d : ℤ) ∣ ((a1 : ℤ) * b) := by exact_mod_cast hda1.mul_right b
      have h2 : (d : ℤ) ∣ ((b1 : ℤ) * a) := by exact_mod_cast hdb1.mul_right a
      have hsub : (d : ℤ) ∣ (-1 : ℤ) := by
        have h := dvd_sub h1 h2; rwa [hdet] at h
      exact_mod_cast dvd_neg.mp hsub
    have ha1q₁_gt_a0b0 : a1 * b0 > a0 * q₁ := by rw [hq₁_eq_b1]; exact ha1b0_gt_a0b1
    -- Derive convergent bounds for floor_convergent_from_pred (same as open case)
    have ha0b0_lt_r' : (a0 : ℝ) / b0 < r := by
      have hconv_even := convergent_even_lt_irrational r hirr (n - 1)
      have hidx : 2 * (n - 1) = 2 * n - 2 := by omega
      rw [hidx] at hconv_even
      rw [hratio0] at hconv_even
      exact hconv_even
    have hr_lt_ab' : r < (a : ℝ) / b := by
      have hconv_odd := convergent_odd_gt_irrational r hirr (n - 1)
      have hidx : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
      rw [hidx] at hconv_odd
      rw [hratio] at hconv_odd
      exact hconv_odd
    -- Prove q₁ = ceil(a1/r) for the closed case lemma
    have hq₁_ceil : q₁ = Nat.ceil ((a1 : ℝ) / r) := by
      rw [hq₁_def]
      have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
      have ha1_pos_r : 0 < (a1 : ℝ) := Nat.cast_pos.mpr ha1_pos
      have hdiv_pos : 0 < (a1 : ℝ) / r := div_pos ha1_pos_r hr_pos
      symm
      rw [Nat.ceil_eq_iff (by omega : Nat.floor ((a1 : ℝ) / r) + 1 ≠ 0)]
      constructor
      · simp only [Nat.add_sub_cancel]
        have hle : (Nat.floor ((a1 : ℝ) / r) : ℝ) ≤ (a1 : ℝ) / r :=
          Nat.floor_le (le_of_lt hdiv_pos)
        have h_not_nat : (a1 : ℝ) / r ≠ Nat.floor ((a1 : ℝ) / r) := by
          intro heq
          have hm := Nat.floor ((a1 : ℝ) / r)
          by_cases hm0 : Nat.floor ((a1 : ℝ) / r) = 0
          · simp only [hm0, Nat.cast_zero] at heq; linarith
          · have hr_eq : r = (a1 : ℝ) / Nat.floor ((a1 : ℝ) / r) := by
              field_simp [show (Nat.floor ((a1 : ℝ) / r) : ℝ) ≠ 0
                from Nat.cast_ne_zero.mpr hm0] at heq ⊢
              linarith
            have hrat : ¬Irrational r := by
              rw [hr_eq]; simp only [Irrational, not_not]
              use (a1 : ℚ) / Nat.floor ((a1 : ℝ) / r); push_cast; rfl
            exact hrat hirr
        exact lt_of_le_of_ne hle (ne_comm.mp h_not_nat)
      · push_cast
        linarith [Nat.lt_floor_add_one ((a1 : ℝ) / r)]
    -- Derive error bound: r - a1/q₁ < 1/q₁² (same as open case, q₁ = b1)
    have herr_a1q₁ : r - (a1 : ℝ) / q₁ < 1 / (q₁ : ℝ) ^ 2 := by
      have hnotterm := not_terminatedAt_of_irrational r hirr (2 * n)
      have hbound := GenContFract.abs_sub_convs_le hnotterm
      have hq₁_dens : (q₁ : ℝ) = (GenContFract.of r).dens (2 * n) := by
        rw [hq₁_eq_b1]; exact hdens_even.symm
      have ha1_convs : (GenContFract.of r).convs (2 * n) = (a1 : ℝ) / q₁ := by
        rw [GenContFract.conv_eq_num_div_den, hnums_even, hq₁_dens]
      rw [ha1_convs] at hbound
      have heven_lt : (a1 : ℝ) / q₁ < r := by
        have h := convergent_even_lt_irrational r hirr n
        rw [convergent_cast_eq_nums_div_dens, hnums_even, hdens_even] at h
        have hb1_eq : (b1 : ℝ) = (q₁ : ℝ) := by exact_mod_cast hq₁_eq_b1.symm
        rwa [hb1_eq] at h
      have habs_eq : |r - (a1 : ℝ) / q₁| = r - (a1 : ℝ) / q₁ :=
        abs_of_pos (sub_pos.mpr heven_lt)
      rw [habs_eq] at hbound
      have hdens_lt : (GenContFract.of r).dens (2 * n) <
          (GenContFract.of r).dens (2 * n + 1) := by
        have h := dens_lt_succ_of_irrational r hirr (2 * n - 1)
        simp only [show 2 * n - 1 + 1 = 2 * n from by omega,
                    show 2 * n - 1 + 2 = 2 * n + 1 from by omega] at h
        exact h
      have hd_pos : (0 : ℝ) < (GenContFract.of r).dens (2 * n) := by
        rw [← hq₁_dens]; exact Nat.cast_pos.mpr hq₁_pos
      calc r - (a1 : ℝ) / q₁
        _ ≤ 1 / ((GenContFract.of r).dens (2 * n) *
              (GenContFract.of r).dens (2 * n + 1)) := hbound
        _ < 1 / ((GenContFract.of r).dens (2 * n) *
              (GenContFract.of r).dens (2 * n)) := by
            exact div_lt_div_of_pos_left one_pos (mul_pos hd_pos hd_pos)
              (mul_lt_mul_of_pos_left hdens_lt hd_pos)
        _ = 1 / (q₁ : ℝ) ^ 2 := by
            congr 1; rw [← hq₁_dens]; ring
    have hdist_bound := selfCohom_dist_bound_from_convergents_closed r hr hirr
      a b a1 q₁
      a0 b0  -- predecessor
      ha_pos hb_pos ha1_pos hq₁_pos
      ha0_pos hb0_pos
      h2b
      h2q₁ hq₁_ge_2 hcoprime_a1_q₁
      h2b0
      ha0_lt hb0_lt
      hpred_det
      ha0b0_lt_r' hr_lt_ab'
      ha1q₁_gt_a0b0
      herr_a1q₁
      hq₁_ceil
      f x y hyx hf_closed hiso_closed
    -- Convert circleDistance to dist and use the chain: dist ≤ 2/a < ε
    have ha_pos' : (0 : ℝ) < a := Nat.cast_pos.mpr ha_pos
    calc dist (f y) (f x) ≤ 2 / a := hdist_bound
      _ < ε := hε_bound

/-- Theorem 5.6: Self-cohomomorphisms of irrational circle graphs are
    rotations possibly composed with reflections.

    Proof outline (Theorem 5.6):

    **Step 1: Continuity** (done via circleGraph_selfCohom_continuous)

    **Step 2: Lift to ℝ**
    By the covering map π : ℝ → AddCircle 1 (see AddCircle.isCoveringMap_coe), the continuous
    map f : Circle → Circle lifts to a continuous g : ℝ → ℝ with π ∘ g = f ∘ π.
    (Mathlib: IsCoveringMap.existsUnique_continuousMap_lifts applied to f ∘ π.)

    **Step 3: Degree d**
    The degree d ∈ ℤ is defined by g(x+1) = g(x) + d. This is the winding number of f.
    (Mathlib: CircleDeg1Lift structure handles d = 1 case; general d requires extension.)

    By composing with reflection x ↦ -x if needed, we may assume d ≥ 0.

    **Step 4: Cohomomorphism bounds**
    The cohom property implies: for (x,y) ∈ ℝ × (1/r, 1-1/r), there exists m_{x,y} ∈ ℤ such that
      g(x+y) - g(x) ∈ [m_{x,y} + 1/r, m_{x,y} + 1 - 1/r].
    By connectedness of ℝ × (1/r, 1-1/r) and continuity of g, the integer m is constant.

    **Step 5: Integration argument**
    For y ∈ [1/r, 1-1/r], the integral ∫₀¹ (g(x+y) - g(x)) dx must lie in [m+1/r, m+1-1/r].
    Computing: ∫₀¹ (g(x+y) - g(x)) dx = ∫_y^1 g + ∫_0^y g(·+1) - ∫_0^1 g = d·y.
    Since d·y ∈ [m+1/r, m+1-1/r] for all y ∈ [1/r, 1-1/r], we get m = 0 and d = 1.

    **Step 6: Exact translation**
    Since g(x+1/r) - g(x) ≥ 1/r for all x (cohom lower bound), and ∫₀¹ (g(x+1/r)-g(x)) dx = 1/r
    (from d = 1), we must have g(x+1/r) - g(x) = 1/r for all x.

    **Step 7: Irrationality conclusion**
    The function h(x) = g(x) - x has period 1 (since g(x+1) = g(x)+1) and period 1/r
    (from step 6). Since 1/r is irrational, h must be constant. Thus g(x) = c + x for some c,
    and f is the rotation by π(c).

    **Mathlib infrastructure**:
    - AddCircle.isCoveringMap_coe: π : ℝ → AddCircle is covering map
    - IsCoveringMap.existsUnique_continuousMap_lifts: unique lift through covering
    - CircleDeg1Lift: structure for degree 1 lifts with translation number theory
    - MeasureTheory.integral_eq: integration theorems
    - Irrational: properties of irrational numbers -/
-- Helper: Two elements of ℝ project to the same Circle point iff they differ by an integer
private lemma circleProj_eq_iff_diff_int (x y : ℝ) :
    (QuotientAddGroup.mk x : Circle) = QuotientAddGroup.mk y ↔ ∃ n : ℤ, x - y = n := by
  constructor
  · intro h
    have h' := QuotientAddGroup.eq.mp h
    rw [AddSubgroup.mem_zmultiples_iff] at h'
    obtain ⟨n, hn⟩ := h'
    use -n
    simp only [zsmul_eq_mul, mul_one] at hn
    push_cast; ring_nf at hn ⊢; linarith
  · intro ⟨n, hn⟩
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
    use -n
    simp only [zsmul_eq_mul, mul_one]
    push_cast; ring_nf; linarith

-- Helper: x + 1 and x project to the same Circle point
private lemma circleProj_add_one (x : ℝ) :
    (QuotientAddGroup.mk (x + 1) : Circle) = QuotientAddGroup.mk x := by
  rw [circleProj_eq_iff_diff_int]; use 1; ring

-- Helper: A continuous ℝ-valued function that takes integer values is locally constant
private lemma locally_const_of_cont_int_valued {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (hfint : ∀ x, ∃ n : ℤ, f x = n) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨n, hn⟩ := hfint x
  have hU : IsOpen (f ⁻¹' (Set.Ioo ((n : ℝ) - 1/2) (n + 1/2))) :=
    isOpen_Ioo.preimage hf
  have hx_in : x ∈ f ⁻¹' (Set.Ioo ((n : ℝ) - 1/2) (n + 1/2)) := by
    simp only [Set.mem_preimage, Set.mem_Ioo, hn]
    constructor <;> linarith
  filter_upwards [hU.mem_nhds hx_in] with y hy
  simp only [Set.mem_preimage, Set.mem_Ioo] at hy
  obtain ⟨m, hm⟩ := hfint y
  rw [hm] at hy
  have hm_eq_n : m = n := by
    have h1 : (n : ℝ) - 1/2 < (m : ℝ) := hy.1
    have h2 : (m : ℝ) < (n : ℝ) + 1/2 := hy.2
    have h3 : (m : ℝ) > (n : ℝ) - 1 := by linarith
    have h4 : (m : ℝ) < (n : ℝ) + 1 := by linarith
    have h5 : n - 1 < m := by exact_mod_cast h3
    have h6 : m < n + 1 := by exact_mod_cast h4
    omega
  rw [hm, hm_eq_n, hn]

-- Helper: Integer-valued continuous functions are constant on preconnected spaces
private lemma int_valued_const_of_cont_real {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (f : X → ℝ) (hf : Continuous f) (hfint : ∀ x, ∃ n : ℤ, f x = n) :
    ∀ x y, f x = f y :=
  (locally_const_of_cont_int_valued f hf hfint).apply_eq_of_preconnectedSpace

-- Helper: round(-1/2) = 0
private lemma round_neg_half : round ((-1 : ℝ) / 2) = 0 := by
  rw [round_eq_zero_iff, Set.mem_Ico]
  constructor <;> linarith

-- Helper: For |z| < 1/2, round z = 0
private lemma round_eq_zero_of_abs_lt_half (z : ℝ) (hz : |z| < 1 / 2) : round z = 0 := by
  rw [round_eq_zero_iff, Set.mem_Ico]
  constructor
  · have := (abs_lt.mp hz).1; linarith
  · exact (abs_lt.mp hz).2

-- Helper: For 1/2 ≤ z < 1, round z = 1
private lemma round_eq_one_of_half_le_lt_one (z : ℝ) (hz1 : 1 / 2 ≤ z) (hz2 : z < 1) :
    round z = 1 := by
  rw [round_eq, Int.floor_eq_iff]
  simp only [Int.cast_one]
  constructor <;> linarith

-- Helper: For -1 < z < -1/2, round z = -1
private lemma round_eq_neg_one_of_neg_one_lt_lt_neg_half (z : ℝ) (hz1 : -1 < z) (hz2 : z < -1 / 2) :
    round z = -1 := by
  rw [round_eq, Int.floor_eq_iff]
  simp only [Int.cast_neg, Int.cast_one]
  constructor <;> linarith

-- Key lemma: For |z| < 1 and r ≥ 2, circle norm ≥ 1/r ↔ 1/r ≤ |z| ≤ 1 - 1/r
private lemma addCircle_norm_ge_iff_bounds (z : ℝ) (hz : |z| < 1) (r : ℝ) (hr : 2 ≤ r) :
    ‖(z : AddCircle (1 : ℝ))‖ ≥ 1 / r ↔ 1 / r ≤ |z| ∧ |z| ≤ 1 - 1 / r := by
  rw [AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  have hz' : -1 < z ∧ z < 1 := abs_lt.mp hz
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hr_inv_le_half : 1 / r ≤ 1 / 2 := by
    rw [one_div, one_div, inv_le_inv₀ hr_pos (by norm_num : (0 : ℝ) < 2)]
    exact hr
  constructor
  · intro h
    by_cases hzabs : |z| < 1 / 2
    · have hr0 : round z = 0 := round_eq_zero_of_abs_lt_half z hzabs
      simp only [hr0, sub_zero, Int.cast_zero] at h
      exact ⟨h, by linarith⟩
    · push_neg at hzabs
      by_cases hzpos : 0 ≤ z
      · have hz_ge : 1 / 2 ≤ z := by rw [abs_of_nonneg hzpos] at hzabs; exact hzabs
        have hr1 : round z = 1 := round_eq_one_of_half_le_lt_one z hz_ge hz'.2
        simp only [hr1, Int.cast_one] at h
        rw [abs_sub_comm, abs_of_pos (by linarith : 0 < 1 - z)] at h
        rw [abs_of_nonneg hzpos]
        exact ⟨by linarith, by linarith⟩
      · push_neg at hzpos
        have hz_le : z ≤ -1 / 2 := by rw [abs_of_neg hzpos] at hzabs; linarith
        by_cases hz_eq : z = -1 / 2
        · subst hz_eq
          have hround : round ((-1 : ℝ) / 2) = 0 := round_neg_half
          simp only [hround, sub_zero, Int.cast_zero] at h
          simp only [abs_neg, abs_div, abs_one, abs_two] at h
          simp only [abs_neg, abs_div, abs_one, abs_two]
          constructor
          · exact h
          · linarith
        · have hz_lt : z < -1 / 2 := lt_of_le_of_ne hz_le hz_eq
          have hr_neg1 : round z = -1 := round_eq_neg_one_of_neg_one_lt_lt_neg_half z hz'.1 hz_lt
          simp only [hr_neg1, Int.cast_neg, Int.cast_one, sub_neg_eq_add] at h
          rw [abs_of_pos (by linarith : 0 < z + 1)] at h
          rw [abs_of_neg hzpos]
          exact ⟨by linarith, by linarith⟩
  · intro ⟨h1, h2⟩
    by_cases hzabs : |z| < 1 / 2
    · have hr0 : round z = 0 := round_eq_zero_of_abs_lt_half z hzabs
      simp only [hr0, sub_zero, Int.cast_zero]
      exact h1
    · push_neg at hzabs
      by_cases hzpos : 0 ≤ z
      · have hz_ge : 1 / 2 ≤ z := by rw [abs_of_nonneg hzpos] at hzabs; exact hzabs
        have hr1 : round z = 1 := round_eq_one_of_half_le_lt_one z hz_ge hz'.2
        simp only [hr1, Int.cast_one]
        rw [abs_sub_comm, abs_of_pos (by linarith : 0 < 1 - z)]
        rw [abs_of_nonneg hzpos] at h2
        linarith
      · push_neg at hzpos
        have hz_le : z ≤ -1 / 2 := by rw [abs_of_neg hzpos] at hzabs; linarith
        by_cases hz_eq : z = -1 / 2
        · subst hz_eq
          have hround : round ((-1 : ℝ) / 2) = 0 := round_neg_half
          simp only [hround, sub_zero, Int.cast_zero]
          simp only [abs_neg, abs_div, abs_one, abs_two] at h1
          simp only [abs_neg, abs_div, abs_one, abs_two]
          linarith
        · have hz_lt : z < -1 / 2 := lt_of_le_of_ne hz_le hz_eq
          have hr_neg1 : round z = -1 := round_eq_neg_one_of_neg_one_lt_lt_neg_half z hz'.1 hz_lt
          simp only [hr_neg1, Int.cast_neg, Int.cast_one, sub_neg_eq_add]
          rw [abs_of_pos (by linarith : 0 < z + 1)]
          rw [abs_of_neg hzpos] at h2
          linarith

-- Helper: Circle norm ≥ 1/r implies |z| ≥ 1/r (for any z)
private lemma abs_ge_of_addCircle_norm_ge (z : ℝ) (r : ℝ) (_hr : 2 ≤ r)
    (h : ‖(z : AddCircle (1 : ℝ))‖ ≥ 1 / r) : |z| ≥ 1 / r := by
  -- The circle norm is |z - round z| where round z is the closest integer to z
  -- We have |z - round z| ≤ |z - 0| = |z| (round achieves the minimum)
  -- So |z| ≥ |z - round z| ≥ 1/r
  rw [AddCircle.norm_eq] at h
  simp only [inv_one, one_mul, mul_one] at h
  -- h : |z - round z| ≥ 1/r
  -- Need: |z - round z| ≤ |z|
  have hround_min : |z - round z| ≤ |z| := by
    by_cases h0 : round z = 0
    · simp [h0]
    · -- round z ≠ 0, so z is closer to round z than to 0
      -- By abs_sub_round: |z - round z| ≤ 1/2
      -- If |z| < 1/2, then round z = 0 (contradiction)
      -- So |z| ≥ 1/2 ≥ |z - round z|
      by_cases hz : |z| < 1/2
      · -- If |z| < 1/2, then round z = 0 (contradiction with h0)
        have hround_zero : round z = 0 := by
          rw [round_eq_zero_iff, Set.mem_Ico]
          constructor
          · have := (abs_lt.mp hz).1; linarith
          · exact (abs_lt.mp hz).2
        exact absurd hround_zero h0
      · push_neg at hz
        -- |z| ≥ 1/2 ≥ |z - round z| (by abs_sub_round)
        calc |z - round z| ≤ 1/2 := abs_sub_round z
          _ ≤ |z| := hz
  linarith

-- Helper: Strict bounds 1/r < |z| < 1 - 1/r imply circle norm > 1/r
-- This is needed for the closed graph case where non-adjacency requires strict inequality
private lemma addCircle_norm_gt_of_strict_bounds (z : ℝ) (r : ℝ) (hr : 2 ≤ r)
    (h1 : 1 / r < |z|) (h2 : |z| < 1 - 1 / r) : ‖(z : AddCircle (1 : ℝ))‖ > 1 / r := by
  have hz_lt_1 : |z| < 1 := by
    calc |z| < 1 - 1/r := h2
      _ ≤ 1 := by linarith [one_div_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr)]
  rw [AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  have hz' : -1 < z ∧ z < 1 := abs_lt.mp hz_lt_1
  have hr_inv_le_half : 1 / r ≤ 1 / 2 := by
    have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
    rw [one_div, one_div, inv_le_inv₀ hr_pos (by norm_num : (0 : ℝ) < 2)]
    exact hr
  by_cases hzabs : |z| < 1 / 2
  · -- |z| < 1/2, so round z = 0 and norm = |z| > 1/r
    have hr0 : round z = 0 := round_eq_zero_of_abs_lt_half z hzabs
    simp only [hr0, sub_zero, Int.cast_zero]
    exact h1
  · push_neg at hzabs
    by_cases hzpos : 0 ≤ z
    · -- z ≥ 1/2, so round z = 1 and norm = 1 - z
      have hz_ge : 1 / 2 ≤ z := by rw [abs_of_nonneg hzpos] at hzabs; exact hzabs
      have hr1 : round z = 1 := round_eq_one_of_half_le_lt_one z hz_ge hz'.2
      simp only [hr1, Int.cast_one]
      rw [abs_sub_comm, abs_of_pos (by linarith : 0 < 1 - z)]
      rw [abs_of_nonneg hzpos] at h2
      linarith
    · push_neg at hzpos
      have hz_le : z ≤ -1 / 2 := by rw [abs_of_neg hzpos] at hzabs; linarith
      by_cases hz_eq : z = -1 / 2
      · -- z = -1/2, round z = 0, norm = 1/2 > 1/r (since r ≥ 2)
        subst hz_eq
        have hround : round ((-1 : ℝ) / 2) = 0 := round_neg_half
        simp only [hround, sub_zero, Int.cast_zero]
        simp only [abs_neg, abs_div, abs_one, abs_two]
        -- Need 1/2 > 1/r, which follows from r ≥ 2
        linarith
      · -- z < -1/2, round z = -1, norm = z + 1 = |z| - 1 + 1... hmm
        have hz_lt : z < -1 / 2 := lt_of_le_of_ne hz_le hz_eq
        have hr_neg1 : round z = -1 := round_eq_neg_one_of_neg_one_lt_lt_neg_half z hz'.1 hz_lt
        simp only [hr_neg1, Int.cast_neg, Int.cast_one, sub_neg_eq_add]
        rw [abs_of_pos (by linarith : 0 < z + 1)]
        rw [abs_of_neg hzpos] at h2
        linarith

-- Helper: The covering map from ℝ to Circle
private def circleProj : ℝ → Circle := QuotientAddGroup.mk

-- Helper: circleDistance on projections equals AddCircle norm of difference
private lemma circleDistance_of_proj (x y : ℝ) :
    circleDistance (circleProj x) (circleProj y) = ‖(x - y : AddCircle (1 : ℝ))‖ := by
  rw [circleDistance, dist_eq_norm]
  congr 1

-- Helper: The covering map is indeed a covering map
private lemma circleProj_isCoveringMap : IsCoveringMap circleProj :=
  AddCircle.isCoveringMap_coe 1

-- Helper: For continuous f : Circle → Circle, there exists a lift g : ℝ → ℝ
-- satisfying circleProj ∘ g = f ∘ circleProj
private lemma exists_lift_of_continuous (f : Circle → Circle) (hcont : Continuous f) :
    ∃ g : C(ℝ, ℝ), circleProj ∘ g = f ∘ circleProj := by
  -- Use the covering map lifting theorem
  -- ℝ is simply connected (via contractibility) and locally path connected
  haveI : SimplyConnectedSpace ℝ := inferInstance
  haveI : LocPathConnectedSpace ℝ := inferInstance
  -- f ∘ circleProj is continuous
  let f_comp_proj : C(ℝ, Circle) := ⟨f ∘ circleProj, hcont.comp continuous_coinduced_rng⟩
  -- Choose e₀ ∈ ℝ such that circleProj e₀ = f(circleProj 0) = f(0)
  -- Since QuotientAddGroup.mk is surjective, we can find such an e₀
  -- The simplest choice is e₀ = 0 when f(0) = 0 (since circleProj 0 = 0)
  -- For general f(0), we use the fact that Circle is the quotient of ℝ by ℤ
  obtain ⟨e₀, he₀⟩ := Quotient.exists_rep (f 0)
  -- Note: he₀ : Quotient.mk'' e₀ = f 0, and circleProj = QuotientAddGroup.mk
  have he₀' : circleProj e₀ = f 0 := he₀
  -- Apply the lifting theorem
  have h_eq : circleProj e₀ = f_comp_proj 0 := by
    simp only [circleProj]
    -- circleProj 0 = 0 in Circle, so f_comp_proj 0 = f(circleProj 0) = f 0
    change circleProj e₀ = f (circleProj 0)
    rw [he₀']
    rfl
  rcases circleProj_isCoveringMap.existsUnique_continuousMap_lifts f_comp_proj 0 e₀ h_eq
    with ⟨g, ⟨_, hg_lifts⟩, _⟩
  refine ⟨g, ?_⟩
  ext x
  have := congr_fun hg_lifts x
  simp only [Function.comp_apply] at this
  exact this

-- A lift g of f : Circle → Circle satisfies g(x+1) = g(x) + d for some integer d
-- This integer d is the degree of f
private lemma lift_satisfies_degree
    (f : Circle → Circle) (_hcont : Continuous f) (g : C(ℝ, ℝ))
    (hg : circleProj ∘ g = f ∘ circleProj) :
    ∃ d : ℤ, ∀ x : ℝ, g (x + 1) = g x + d := by
  -- g(x + 1) projects to the same point as g(x) on Circle
  have h_proj_eq : ∀ x, circleProj (g (x + 1)) = circleProj (g x) := fun x => by
    calc circleProj (g (x + 1)) = (circleProj ∘ g) (x + 1) := rfl
      _ = (f ∘ circleProj) (x + 1) := by rw [hg]
      _ = f (circleProj (x + 1)) := rfl
      _ = f (circleProj x) := by rw [circleProj]; exact congrArg f (circleProj_add_one x)
      _ = (f ∘ circleProj) x := rfl
      _ = (circleProj ∘ g) x := by rw [← hg]
      _ = circleProj (g x) := rfl
  -- So g(x + 1) - g(x) ∈ ℤ for all x
  have h_diff_int : ∀ x, ∃ n : ℤ, g (x + 1) - g x = n := fun x => by
    rw [circleProj] at h_proj_eq
    exact (circleProj_eq_iff_diff_int (g (x + 1)) (g x)).mp (h_proj_eq x)
  -- The function δ(x) := g(x + 1) - g(x) is continuous and integer-valued
  have hδ_cont : Continuous (fun x => g (x + 1) - g x) :=
    (g.2.comp (continuous_id.add continuous_const)).sub g.2
  -- By the lemma, δ is constant on ℝ (which is preconnected)
  have hδ_const := int_valued_const_of_cont_real (fun x => g (x + 1) - g x) hδ_cont h_diff_int
  -- Extract the constant value
  obtain ⟨d, hd⟩ := h_diff_int 0
  use d
  intro x
  have h := hδ_const x 0
  simp only at h
  rw [← hd]
  linarith

-- Key lemma: For a cohomomorphism f of an irrational circle graph, the degree |d| = 1
-- This follows from the integration argument in the tex proof (lines 2320-2325)
-- Proof outline:
-- 1. For y ∈ (1/r, 1-1/r), cohomomorphism property gives g(x+y) - g(x) ∈ [m+1/r, m+1-1/r]
-- 2. By continuity/connectedness, m is constant (doesn't depend on x or y)
-- 3. Integrate: ∫₀¹ (g(x+y) - g(x)) dx = d·y
-- 4. So d·y ∈ [m+1/r, m+1-1/r] for all y ∈ [1/r, 1-1/r]
-- 5. These constraints force m = 0 and d = 1 (or d = -1 by symmetry with reflection)
set_option maxHeartbeats 1600000 in -- needed for degree_one_of_cohom proof complexity
private lemma degree_one_of_cohom
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (f : Circle → Circle) (_hcont : Continuous f) (g : C(ℝ, ℝ))
    (hg : circleProj ∘ g = f ∘ circleProj)
    (d : ℤ) (hd : ∀ x : ℝ, g (x + 1) = g x + d)
    (hf : IsCohom (circleGraphOpen r hr) (circleGraphOpen r hr) f ∨
          IsCohom (circleGraphClosed r hr) (circleGraphClosed r hr) f) :
    d = 1 ∨ d = -1 := by
  -- Step 0: Basic setup
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr
  have hr_gt_2 : 2 < r := by
    rcases hr.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hirr; exact Nat.not_irrational 2 hirr
  have h1r_pos : 0 < 1/r := by positivity
  have h1r_lt_half : 1/r < 1/2 := by
    rw [one_div_lt_one_div hr_pos (by norm_num : (0:ℝ) < 2)]
    exact hr_gt_2
  have h_gap_exists : 1/r < 1 - 1/r := by linarith
  -- Step 1: The cohomomorphism property gives bounds on g(x+y) - g(x)
  -- For y ∈ (1/r, 1-1/r), the points circleProj x and circleProj (x+y) are non-adjacent
  -- in the circle graph, so f(circleProj x) and f(circleProj(x+y)) are non-adjacent.
  -- This means |g(x+y) - g(x) - m| ≥ 1/r for some integer m (the winding number).
  -- The constraint is: g(x+y) - g(x) ∈ [m + 1/r, m + 1 - 1/r] for some m.

  -- Step 2: The key integration argument
  -- ∫₀¹ (g(x+y) - g(x)) dx = ∫_y^1 g dx + ∫_0^y g(x+1) dx - ∫₀¹ g dx
  --                       = ∫_y^1 g dx + ∫_0^y (g x + d) dx - ∫₀¹ g dx
  --                       = d·y
  -- This must be in [m + 1/r, m + 1 - 1/r] for fixed m and all y ∈ [1/r, 1-1/r].
  -- So d·(1/r) ≥ m + 1/r and d·(1-1/r) ≤ m + 1 - 1/r.
  -- From d/r ≥ m + 1/r: d ≥ m·r + 1
  -- From d(1-1/r) ≤ m + 1 - 1/r: d ≤ (m+1)·r/(r-1) - 1/(r-1) = (m·r + r - 1)/(r-1)
  -- For m = 0: d ≥ 1 and d ≤ (r-1)/(r-1) = 1, so d = 1.
  -- For m = -1: d ≥ -r + 1 and d ≤ (-r + r - 1)/(r-1) = -1/(r-1), so d ≤ 0.
  --             Combined with d ≥ 1 - r > -1 (for r > 2), we need d = 0 or negative.
  --             But d = 0 gives d/r = 0 which should be ≥ -1 + 1/r = -1 + 1/r < 0. ✗
  -- So the only valid options are m = 0 with d = 1, or by reflection symmetry, d = -1.

  -- Direct case analysis: d = 0 and |d| ≥ 2 each lead to contradiction.
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨hd_ne_1, hd_ne_neg1⟩ := h_neg
  -- d ≠ 1 and d ≠ -1. We derive a contradiction using the cohomomorphism structure.
  -- The degree d determines how many times the image wraps around.
  -- For a cohomomorphism, the wrapping must be compatible with the gap structure.
  -- Specifically, |d| = 1 is forced by the irrationality of r and the gap bounds.

  -- Case analysis: d = 0 leads to contradiction (map is constant on homotopy classes)
  -- |d| ≥ 2 leads to contradiction (too much compression/expansion)

  -- For d = 0: g(x+1) = g(x), so g is 1-periodic.
  -- Then f is a well-defined map Circle → Circle that doesn't increase distance significantly.
  -- But cohomomorphism requires non-adjacent points to map to non-adjacent points.
  -- For d = 0, the image is contained in a single period, causing distance compression.

  -- For |d| ≥ 2: The map wraps around multiple times.
  -- This causes too much "stretching" which violates the gap lower bound.

  -- The detailed proof uses the integration argument:
  -- ∫₀¹ (g(x+y) - g(x)) dx = d·y for y ∈ [1/r, 1-1/r]
  -- This integral must be in [m + 1/r, m + 1 - 1/r] by the cohomomorphism gap property.
  -- For y = 1/r: d/r ∈ [m + 1/r, m + 1 - 1/r]
  -- For y = 1 - 1/r: d(1-1/r) ∈ [m + 1/r, m + 1 - 1/r]
  -- These constraints, combined with m being an integer, force d = ±1.

  -- Technical proof using the constraints from the integration argument:
  -- The key is that d·y must be in [m+1/r, m+1-1/r] for all y ∈ [1/r, 1-1/r]
  -- and some fixed integer m.
  --
  -- Case d = 0: 0 ∉ [m+1/r, m+1-1/r] for any integer m (since 1/r > 0 and m+1-1/r < 0 for m < 0)
  -- Case |d| ≥ 2: The range d·[1/r, 1-1/r] has length |d|·(1-2/r) > 1-2/r,
  --               but [m+1/r, m+1-1/r] has length 1-2/r, so the range can't fit.
  --
  -- The detailed integration argument:
  -- ∫₀¹ (g(x+y) - g(x)) dx = d·y, and this must be in [m+1/r, m+1-1/r].
  -- For y = 1/r: d/r ∈ [m+1/r, m+1-1/r] → m+1 ≤ d ≤ m·r + r - 1
  -- For y = 1-1/r: d(1-1/r) ∈ [m+1/r, m+1-1/r] → 1/(r-1) · (m·r+1) ≤ d ≤ m+1
  -- Combined: d = m+1 (when the constraints are compatible)
  -- Only m = 0 (d = 1) and m = -1 (d = -1) give valid integer solutions.

  -- Proof by case analysis on the value of d
  rcases Int.lt_trichotomy d 0 with hd_neg | hd_zero | hd_pos
  · -- d < 0: Since d ≠ -1, we have d ≤ -2
    have hd_le_neg2 : d ≤ -2 := by omega
    -- The argument mirrors the d ≥ 2 case.
    -- The integration gives: ∫₀¹ (g(x+y) - g(x)) dx = d·y
    -- For y ∈ [1/r, 1-1/r], d·y ranges from d(1-1/r) to d/r (since d < 0).
    -- The range has length |d|·(1-2/r) ≥ 2·(1-2/r) > 1-2/r = band length.
    -- So d·y cannot stay in any single band.
    --
    -- The formal argument: for d ≤ -2 and any m ∈ ℤ,
    -- the constraints that both d/r and d(1-1/r) are in [m+1/r, m+1-1/r]
    -- lead to contradictions.
    --
    -- For m = -1: d/r ∈ [-1+1/r, -1/r].
    --             d ∈ [-r+1, -1].
    --             d(1-1/r) ∈ [-1+1/r, -1/r].
    --             d ∈ [(-r+1)/(r-1), -1/(r-1)] = [-1, -1/(r-1)].
    --             Combined: d ∈ [-r+1, -1] ∩ [-1, -1/(r-1)] = {-1} for r > 2.
    --             But d ≤ -2, contradiction.
    --
    -- For m ≤ -2: The analysis is similar - the constraints narrow to a range
    --             that doesn't contain any integer ≤ -2.
    --
    -- Key arithmetic facts for the range length argument:
    -- For d ≤ -2, the argument is symmetric to d ≥ 2
    -- For even d (like -2, -4), d/2 is an integer, and integers are not in any band
    -- For odd d (like -3, -5), the range length exceeds band length
    exfalso
    -- Key lemma: any integer is not in any band
    have h_int_not_in_band : ∀ n : ℤ, ∀ m : ℤ, ¬((m : ℝ) + 1/r ≤ n ∧ (n : ℝ) ≤ m + 1 - 1/r) := by
      intro n m ⟨h_lower, h_upper⟩
      have h1r_pos : 0 < 1/r := by positivity
      -- From h_lower: m + 1/r ≤ n, so m < n (since 1/r > 0)
      have h1 : (m : ℝ) < n := by linarith
      -- From h_upper: n ≤ m + 1 - 1/r < m + 1, so n < m + 1
      have h2 : (n : ℝ) < m + 1 := by linarith
      -- Convert to integer inequalities
      have h_m_lt_n : m < n := Int.cast_lt.mp h1
      have h_n_lt_m1 : n < m + 1 := by
        have h2' : (n : ℝ) < (m + 1 : ℤ) := by simp only [Int.cast_add, Int.cast_one]; exact h2
        exact Int.cast_lt.mp h2'
      -- m < n and n < m + 1 implies m < n < m + 1, impossible for integers
      omega
    -- For even d ≤ -2, d/2 is an integer not in any band
    -- For odd d ≤ -3, need range length argument
    -- We handle d = -2 explicitly; for d ≤ -3, similar argument or range length
    -- The key is: integral = d/2 must be in band m₀, but d/2 (for d = -2) = -1 is not in any band
    -- Replicate the d = 0 infrastructure for the integration argument
    have h_half_in_range' : 1/r < (1:ℝ)/2 ∧ (1:ℝ)/2 < 1 - 1/r := by
      constructor
      · rw [one_div, one_div, inv_lt_inv₀ hr_pos (by norm_num : (0:ℝ) < 2)]; exact hr_gt_2
      · have h2r : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
        linarith
    let δ' : ℝ → ℝ := fun x => g (x + 1/2) - g x
    have hδ'_cont : Continuous δ' :=
      (g.continuous.comp
        (continuous_id.add continuous_const)).sub
        g.continuous
    -- The integral of δ' over [0,1] equals d/2
    have h_integral_eq' :
        ∫ x in (0:ℝ)..1, δ' x = (d : ℝ) / 2 := by
      have hg_int : IntervalIntegrable (↑g)
          MeasureTheory.volume 0 1 :=
        g.continuous.intervalIntegrable 0 1
      have h_shift_int :
          IntervalIntegrable (fun x => g (x + 1/2))
            MeasureTheory.volume 0 1 :=
        (g.continuous.comp
          (continuous_id.add
            continuous_const)).intervalIntegrable 0 1
      have h_subst :
          ∫ x in (0:ℝ)..1, g (x + 1/2) =
          ∫ x in (1/2:ℝ)..(3/2), g x := by
        have :=
          intervalIntegral.integral_comp_add_right
            (a := (0:ℝ)) (b := (1:ℝ))
            (fun x => g x) (1/2 : ℝ)
        simp only at this
        convert this using 2 <;> ring
      have h_split :
          ∫ x in (1/2:ℝ)..(3/2), g x =
          (∫ x in (1/2:ℝ)..1, g x)
            + ∫ x in (1:ℝ)..(3/2), g x :=
        (intervalIntegral.integral_add_adjacent_intervals
          (g.continuous.intervalIntegrable _ _)
          (g.continuous.intervalIntegrable _ _)).symm
      have h_period :
          ∫ x in (1:ℝ)..(3/2), g x =
          ∫ x in (0:ℝ)..(1/2), g (x + 1) := by
        have :=
          intervalIntegral.integral_comp_add_right
            (a := (0:ℝ)) (b := (1/2:ℝ))
            (fun x => g x) (1 : ℝ)
        simp only at this
        convert this.symm using 2 <;> ring
      have h_degree :
          ∫ x in (0:ℝ)..(1/2), g (x + 1) =
          (∫ x in (0:ℝ)..(1/2), g x)
            + d * (1/2) := by
        calc ∫ x in (0:ℝ)..(1/2), g (x + 1)
            = ∫ x in (0:ℝ)..(1/2), (g x + d) := by
              apply intervalIntegral.integral_congr
              intro x _; exact hd x
          _ = (∫ x in (0:ℝ)..(1/2), g x)
              + ∫ x in (0:ℝ)..(1/2), (d : ℝ) := by
              rw [intervalIntegral.integral_add
                (g.continuous.intervalIntegrable _ _)
                (continuous_const.intervalIntegrable
                  _ _)]
          _ = (∫ x in (0:ℝ)..(1/2), g x)
              + d * (1/2) := by
              simp only [
                intervalIntegral.integral_const,
                sub_zero, smul_eq_mul, mul_comm]
      have h_combine :
          ∫ x in (1/2:ℝ)..(3/2), g x =
          (∫ x in (0:ℝ)..1, g x) + d * (1/2) := by
        rw [h_split, h_period, h_degree]
        have h_split' :
            (∫ x in (0:ℝ)..(1/2), g x)
              + ∫ x in (1/2:ℝ)..1, g x =
            ∫ x in (0:ℝ)..1, g x :=
          intervalIntegral.integral_add_adjacent_intervals
            (g.continuous.intervalIntegrable _ _)
            (g.continuous.intervalIntegrable _ _)
        linarith
      calc ∫ x in (0:ℝ)..1, δ' x
          = ∫ x in (0:ℝ)..1, (g (x + 1/2) - g x) :=
            rfl
        _ = (∫ x in (0:ℝ)..1, g (x + 1/2))
            - ∫ x in (0:ℝ)..1, g x := by
            rw [intervalIntegral.integral_sub
              h_shift_int hg_int]
        _ = ((∫ x in (0:ℝ)..1, g x) + d * (1/2))
            - ∫ x in (0:ℝ)..1, g x := by
            rw [h_subst, h_combine]
        _ = d * (1/2) := by ring
        _ = d / 2 := by ring
    -- For d = -2 specifically, d/2 = -1 which is not in any band
    -- For odd d ≤ -3, the range argument applies (deferred)
    by_cases hd_even : 2 ∣ d
    · -- d is even, so d/2 is an integer
      obtain ⟨k, hk⟩ := hd_even
      have hk_eq : d / 2 = k := by omega
      have hk_le : k ≤ -1 := by omega
      -- Replicate the infrastructure from d = 0 case
      -- Step 3: Points are non-adjacent since distance 1/2 > 1/r
      have h_dist_half' : ∀ x : ℝ, circleDistance (circleProj x) (circleProj (x + 1/2)) = 1/2 := by
        intro x
        rw [circleDistance_of_proj, ← AddCircle.coe_sub]
        have h_diff : x - (x + 1/2) = -(1/2 : ℝ) := by ring
        rw [h_diff]
        have h1_ne : (1 : ℝ) ≠ 0 := one_ne_zero
        rw [(AddCircle.norm_coe_eq_abs_iff 1 h1_ne).mpr]
        · simp only [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
        · simp only [abs_neg, abs_one, one_div]; norm_num
      have h_nonadj' : ∀ x : ℝ,
          ¬(circleGraphOpen r hr).Adj
            (circleProj x) (circleProj (x + 1/2)) := by
        intro x
        simp only [circleGraphOpen]
        push_neg; intro _
        rw [h_dist_half']
        linarith [h_half_in_range'.1]
      -- Step 4: By cohom, |δ'(x) - round(δ'(x))| ≥ 1/r for all x
      have h_gap' : ∀ x : ℝ, 1/r ≤ |δ' x - round (δ' x)| := by
        intro x
        have h_nonadj_x := h_nonadj' x
        have h_ne : circleProj x ≠ circleProj (x + 1/2) := by
          intro heq
          have hdist := h_dist_half' x
          rw [heq] at hdist
          simp only [circleDistance, _root_.dist_self] at hdist
          norm_num at hdist
        have hfx : f (circleProj x) = circleProj (g x) := by
          have := congrFun hg x; simp only [Function.comp_apply] at this; exact this.symm
        have hfx2 : f (circleProj (x + 1/2)) = circleProj (g (x + 1/2)) := by
          have := congrFun hg (x + 1/2); simp only [Function.comp_apply] at this; exact this.symm
        have h_neg_δ' : (g x - g (x + 1/2) : ℝ) = -δ' x := by simp only [δ']; ring
        have h_gx_ne : circleProj (g x) ≠ circleProj (g (x + 1/2)) := by
          rw [← hfx, ← hfx2]
          rcases hf with hf_open | hf_closed
          · exact (hf_open (circleProj x) (circleProj (x + 1/2)) h_ne h_nonadj_x).1
          · have h_nonadj_closed :
                ¬(circleGraphClosed r hr).Adj
                  (circleProj x)
                  (circleProj (x + 1/2)) := by
              simp only [circleGraphClosed,
                not_and_or, not_not, not_le]
              right; rw [h_dist_half']
              exact h_half_in_range'.1
            exact (hf_closed (circleProj x)
              (circleProj (x + 1/2))
              h_ne h_nonadj_closed).1
        rcases hf with hf_open | hf_closed
        · have hcoh := hf_open (circleProj x) (circleProj (x + 1/2)) h_ne h_nonadj_x
          have h_not_adj := hcoh.2
          simp only [circleGraphOpen, not_and_or, not_not, not_lt] at h_not_adj
          rcases h_not_adj with h_eq | h_dist
          · rw [hfx, hfx2] at h_eq; exact absurd h_eq h_gx_ne
          · rw [hfx, hfx2, circleDistance_of_proj, ← AddCircle.coe_sub, h_neg_δ'] at h_dist
            rw [AddCircle.coe_neg, norm_neg, AddCircle.norm_eq 1] at h_dist
            simp only [inv_one, one_mul, mul_one] at h_dist
            exact h_dist
        · have h_nonadj_closed :
              ¬(circleGraphClosed r hr).Adj
                (circleProj x)
                (circleProj (x + 1/2)) := by
            simp only [circleGraphClosed,
              not_and_or, not_not, not_le]
            right; rw [h_dist_half']
            exact h_half_in_range'.1
          have hcoh := hf_closed (circleProj x)
            (circleProj (x + 1/2))
            h_ne h_nonadj_closed
          have h_not_adj := hcoh.2
          simp only [circleGraphClosed, not_and_or, not_not, not_le] at h_not_adj
          rcases h_not_adj with h_eq | h_dist
          · rw [hfx, hfx2] at h_eq; exact absurd h_eq h_gx_ne
          · rw [hfx, hfx2, circleDistance_of_proj, ← AddCircle.coe_sub, h_neg_δ'] at h_dist
            rw [AddCircle.coe_neg, norm_neg, AddCircle.norm_eq 1] at h_dist
            simp only [inv_one, one_mul, mul_one] at h_dist; exact le_of_lt h_dist
      -- Step 5: δ'(x) ∈ some band [m + 1/r, m + 1 - 1/r]
      have h_in_band' : ∀ x : ℝ, ∃ m : ℤ, m + 1/r ≤ δ' x ∧ δ' x ≤ m + 1 - 1/r := by
        intro x
        have hgap := h_gap' x
        have hround_bound : |δ' x - round (δ' x)| ≤ 1/2 := abs_sub_round (δ' x)
        by_cases hpos : δ' x - round (δ' x) ≥ 0
        · use round (δ' x)
          have h1 : δ' x - round (δ' x) ≥ 1/r := by
            rw [abs_of_nonneg hpos] at hgap; exact hgap
          have h2 : δ' x - round (δ' x) ≤ 1/2 := by
            rw [abs_of_nonneg hpos] at hround_bound
            exact hround_bound
          constructor <;> linarith [h1r_lt_half]
        · push_neg at hpos
          use round (δ' x) - 1
          have hneg : δ' x - round (δ' x) < 0 := hpos
          have h1 : -(δ' x - round (δ' x)) ≥ 1/r := by
            rw [abs_of_neg hneg] at hgap; exact hgap
          have h2 : -(δ' x - round (δ' x)) ≤ 1/2 := by
            rw [abs_of_neg hneg] at hround_bound
            exact hround_bound
          simp only [Int.cast_sub, Int.cast_one]
          constructor <;> linarith [h1r_lt_half]
      -- Step 6: By connectedness, δ'([0,1]) is in a single band
      have h_image_preconn' :
          IsPreconnected (Set.range
            (fun x : Set.Icc (0:ℝ) 1 => δ' x.val)) := by
        have h_conn : IsConnected (Set.Icc (0:ℝ) 1) := isConnected_Icc (by norm_num : (0:ℝ) ≤ 1)
        have h_eq : (Set.range (fun x : Set.Icc (0:ℝ) 1 => δ' x.val)) = δ' '' Set.Icc 0 1 := by
          ext y; simp only [Set.mem_range, Set.mem_image]
          constructor
          · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
          · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
        rw [h_eq]
        exact h_conn.isPreconnected.image _ hδ'_cont.continuousOn
      have h_bands_disjoint' : ∀ m₁ m₂ : ℤ, m₁ ≠ m₂ →
          Disjoint (Set.Icc (m₁ + 1/r) (m₁ + 1 - 1/r)) (Set.Icc (m₂ + 1/r) (m₂ + 1 - 1/r)) := by
        intro m₁ m₂ hne
        rw [Set.disjoint_iff]
        intro y ⟨hy1, hy2⟩
        simp only [Set.mem_Icc] at hy1 hy2
        have h1 : (m₁ : ℝ) + 1/r ≤ m₂ + 1 - 1/r := le_trans hy1.1 hy2.2
        have h2 : (m₂ : ℝ) + 1/r ≤ m₁ + 1 - 1/r := le_trans hy2.1 hy1.2
        have h_2r_lt_1 : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
        have h_diff1 : (m₁ : ℝ) - m₂ < 1 := by linarith
        have h_diff2 : (m₂ : ℝ) - m₁ < 1 := by linarith
        have h_eq : m₁ = m₂ := by
          have h_diff_lt : -(1 : ℝ) < m₁ - m₂ ∧ (m₁ : ℝ) - m₂ < 1 := by constructor <;> linarith
          have h_int : (m₁ - m₂ : ℤ) = 0 := by
            have h1' : (-1 : ℤ) < m₁ - m₂ := by
              have : (-1 : ℝ) < m₁ - m₂ := h_diff_lt.1
              exact_mod_cast this
            have h2' : m₁ - m₂ < 1 := by
              have : (m₁ : ℝ) - m₂ < 1 := h_diff_lt.2
              exact_mod_cast this
            omega
          linarith [h_int]
        exact hne h_eq
      -- Pick the band containing δ'(0)
      obtain ⟨m₀', hm₀'_band⟩ := h_in_band' 0
      -- Show all δ' values on [0,1] are in this band
      have hm₀'_all : ∀ x ∈ Set.Icc (0:ℝ) 1, m₀' + 1/r ≤ δ' x ∧ δ' x ≤ m₀' + 1 - 1/r := by
        intro x hx
        obtain ⟨m, hm⟩ := h_in_band' x
        by_contra h_not_in
        simp only [not_and_or, not_le] at h_not_in
        have h_m_ne : m ≠ m₀' := by
          intro heq; subst heq
          rcases h_not_in with h | h
          · linarith [hm.1]
          · linarith [hm.2]
        rcases lt_trichotomy m₀' m with h_lt | h_eq | h_gt
        · have h_le : m₀' + 1 ≤ m := Int.add_one_le_of_lt h_lt
          have h_le_real : (m₀' : ℝ) + 1 ≤ m := by exact_mod_cast h_le
          have h_delta_0_le : δ' 0 ≤ m₀' + 1 - 1/r := hm₀'_band.2
          have h_delta_x_ge : m + 1/r ≤ δ' x := hm.1
          set v : ℝ := m₀' + 1 with hv_def
          have h_δ0_lt_v : δ' 0 < v := by
            calc δ' 0 ≤ m₀' + 1 - 1/r := h_delta_0_le
              _ < m₀' + 1 := by linarith [hr]
          have h_v_lt_δx : v < δ' x := by
            calc v = m₀' + 1 := rfl
              _ ≤ m := h_le_real
              _ < m + 1/r := by linarith [hr]
              _ ≤ δ' x := h_delta_x_ge
          have h_x_nonneg : 0 ≤ x := hx.1
          have h_ivt := intermediate_value_Icc h_x_nonneg hδ'_cont.continuousOn
          have hv_mem : v ∈ Set.Icc (δ' 0) (δ' x) := ⟨le_of_lt h_δ0_lt_v, le_of_lt h_v_lt_δx⟩
          obtain ⟨t, _, ht_eq⟩ := h_ivt hv_mem
          obtain ⟨m', hm'⟩ := h_in_band' t
          rw [ht_eq] at hm'
          have h_m'_le : m' ≤ m₀' := by
            have h1 : (m' : ℝ) + 1/r ≤ m₀' + 1 := hm'.1
            have h3 : (m' : ℝ) < m₀' + 1 := by linarith [hr]
            exact Int.le_of_lt_add_one (by exact_mod_cast h3)
          have h_m'_ge : m₀' + 1 ≤ m' := by
            have h1 : (m₀' : ℝ) + 1 ≤ m' + 1 - 1/r := hm'.2
            have h3 : (m₀' : ℝ) < m' := by linarith [hr]
            exact Int.add_one_le_of_lt (by exact_mod_cast h3)
          omega
        · exact h_m_ne h_eq.symm
        · have h_le : m ≤ m₀' - 1 := Int.le_sub_one_of_lt h_gt
          have h_le_real : (m : ℝ) ≤ m₀' - 1 := by exact_mod_cast h_le
          have h_delta_0_ge : m₀' + 1/r ≤ δ' 0 := hm₀'_band.1
          have h_delta_x_le : δ' x ≤ m + 1 - 1/r := hm.2
          set v : ℝ := (m₀' : ℝ) with hv_def
          have h_v_lt_δ0 : v < δ' 0 := by
            calc v = m₀' := rfl
              _ < m₀' + 1/r := by linarith [hr]
              _ ≤ δ' 0 := h_delta_0_ge
          have h_δx_lt_v : δ' x < v := by
            calc δ' x ≤ m + 1 - 1/r := h_delta_x_le
              _ ≤ (m₀' - 1) + 1 - 1/r := by linarith
              _ = m₀' - 1/r := by ring
              _ < m₀' := by linarith [hr]
          have h_x_nonneg : 0 ≤ x := hx.1
          have h_ivt' := intermediate_value_Icc' h_x_nonneg hδ'_cont.continuousOn
          have hv_mem : v ∈ Set.Icc (δ' x) (δ' 0) := ⟨le_of_lt h_δx_lt_v, le_of_lt h_v_lt_δ0⟩
          obtain ⟨t, _, ht_eq⟩ := h_ivt' hv_mem
          obtain ⟨m', hm'⟩ := h_in_band' t
          rw [ht_eq] at hm'
          have h_m'_le : m' ≤ m₀' - 1 := by
            have h1 : (m' : ℝ) + 1/r ≤ m₀' := hm'.1
            have h3 : (m' : ℝ) < m₀' := by linarith [hr]
            exact Int.le_sub_one_of_lt (by exact_mod_cast h3)
          have h_m'_ge : m₀' ≤ m' := by
            have h1 : (m₀' : ℝ) ≤ m' + 1 - 1/r := hm'.2
            have h3 : (m₀' : ℝ) - 1 < m' := by linarith [hr]
            have h4 : m₀' - 1 < m' := by exact_mod_cast h3
            omega
          omega
      -- Step 7: Integral is in the band
      have h_integral_in_band' :
          m₀' + 1/r ≤ ∫ x in (0:ℝ)..1, δ' x ∧
          ∫ x in (0:ℝ)..1, δ' x ≤ m₀' + 1 - 1/r := by
        have hδ'_int : IntervalIntegrable δ' MeasureTheory.volume 0 1 :=
          hδ'_cont.intervalIntegrable 0 1
        constructor
        · have h_lower : ∀ x ∈ Set.Icc (0:ℝ) 1, m₀' + 1/r ≤ δ' x :=
            fun x hx => (hm₀'_all x hx).1
          calc m₀' + 1/r
              = ∫ _ in (0:ℝ)..1, (m₀' + 1/r : ℝ) := by
                simp [intervalIntegral.integral_const]
            _ ≤ ∫ x in (0:ℝ)..1, δ' x := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
                · exact continuous_const.intervalIntegrable 0 1
                · exact hδ'_int
                · exact h_lower
        · have h_upper :
              ∀ x ∈ Set.Icc (0:ℝ) 1,
                δ' x ≤ m₀' + 1 - 1/r :=
            fun x hx => (hm₀'_all x hx).2
          calc ∫ x in (0:ℝ)..1, δ' x ≤ ∫ _ in (0:ℝ)..1, (m₀' + 1 - 1/r : ℝ) := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
                · exact hδ'_int
                · exact continuous_const.intervalIntegrable 0 1
                · exact h_upper
            _ = m₀' + 1 - 1/r := by simp [intervalIntegral.integral_const]
      -- Step 8: The integral is d/2 = k (an integer), but k ∉ any band
      have h_integral_is_k : ∫ x in (0:ℝ)..1, δ' x = k := by
        rw [h_integral_eq']
        have hk_real : (d : ℝ) / 2 = k := by
          have : d = 2 * k := hk
          rw [this]
          push_cast
          ring
        exact hk_real
      rw [h_integral_is_k] at h_integral_in_band'
      exact h_int_not_in_band k m₀' h_integral_in_band'
    · -- d is odd with |d| ≥ 3 (i.e., d ≤ -3), use range length argument
      have hd_le_neg3 : d ≤ -3 := by
        have h1 : d ≤ -2 := hd_le_neg2
        have h2 : ¬(2 ∣ d) := hd_even
        by_contra h_neg
        push_neg at h_neg
        (interval_cases d; simp_all)
      have hd_abs_ge_3 : 3 ≤ |d| := by
        simp only [abs_of_neg (by omega : d < 0)]
        omega
      -- Key arithmetic: range length exceeds band length
      have h_band_length : (1 : ℝ) - 2/r > 0 := by
        have h2r : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
        linarith
      have h_range_exceeds_band : |d| * (1 - 2/r) > 1 - 2/r := by
        have h1 : (3 : ℝ) ≤ |d| := by exact_mod_cast hd_abs_ge_3
        have h2 : (1 : ℝ) < 3 := by norm_num
        calc |d| * (1 - 2/r) ≥ 3 * (1 - 2/r) := by
              apply mul_le_mul_of_nonneg_right h1 (le_of_lt h_band_length)
          _ > 1 * (1 - 2/r) := mul_lt_mul_of_pos_right h2 h_band_length
          _ = 1 - 2/r := one_mul _
      -- Pick y₁, y₂ in (1/r, 1-1/r) with gap 1/2 - 1/r, show d*y₁ and d*y₂ too far for same band
      have h_d_neg : d < 0 := by omega
      have hd_real_neg : (d : ℝ) < 0 := by exact_mod_cast h_d_neg
      -- Pick two y values in (1/r, 1-1/r) that are sufficiently far apart.
      -- y₁ = 1/4 + 1/(2r) and y₂ = 3/4 - 1/(2r), gap = 1/2 - 1/r = (r-2)/(2r)
      -- These are in (1/r, 1-1/r) because:
      -- y₁ = 1/4 + 1/(2r) > 1/r iff 1/4 > 1/r - 1/(2r) = 1/(2r) iff r > 2.
      -- y₁ < 1 - 1/r iff 1/4 + 1/(2r) < 1 - 1/r iff 1/4 < 1 - 1/r - 1/(2r) = 1 - 3/(2r).
      --   For r > 2: 3/(2r) < 3/4, so 1 - 3/(2r) > 1/4. True.
      -- y₂ > 1/r iff 3/4 - 1/(2r) > 1/r iff 3/4 > 3/(2r) iff r > 2.
      -- y₂ < 1 - 1/r iff 3/4 - 1/(2r) < 1 - 1/r iff 3/4 < 1 - 1/r + 1/(2r) = 1 - 1/(2r).
      --   For r > 2: 1/(2r) < 1/4, so 1 - 1/(2r) > 3/4. True.
      set y₁ : ℝ := 1/4 + 1/(2*r) with hy₁_def
      set y₂ : ℝ := 3/4 - 1/(2*r) with hy₂_def
      have h_inv_2r_pos : (0:ℝ) < 1/(2*r) := by positivity
      have h_inv_2r_eq : 1/r = 2 * (1/(2*r)) := by field_simp
      have hy₁_lower : 1/r < y₁ := by
        rw [hy₁_def, h_inv_2r_eq]; linarith
      have hy₁_upper : y₁ < 1 - 1/r := by
        rw [hy₁_def, h_inv_2r_eq]; nlinarith
      have hy₂_lower : 1/r < y₂ := by
        rw [hy₂_def, h_inv_2r_eq]; nlinarith
      have hy₂_upper : y₂ < 1 - 1/r := by
        rw [hy₂_def, h_inv_2r_eq]; nlinarith
      have hy₁_lt_y₂ : y₁ < y₂ := by
        rw [hy₁_def, hy₂_def]; linarith
      -- The gap: y₂ - y₁ = 1/2 - 1/r
      have h_diff_y : y₂ - y₁ = 1/2 - 1/r := by
        rw [hy₁_def, hy₂_def]; field_simp; ring
      -- |d| * gap > 1 - 2/r
      have h_range_span : |(d : ℝ)| * (y₂ - y₁) > 1 - 2/r := by
        rw [h_diff_y]
        have h1 : (1:ℝ) - 2/r = 2 * (1/2 - 1/r) := by ring
        rw [h1]
        have h3 : (2 : ℝ) < |(d : ℝ)| := by
          rw [abs_of_neg (show (d : ℝ) < 0 from by exact_mod_cast h_d_neg)]
          linarith [show (d : ℝ) ≤ -3 from by exact_mod_cast hd_le_neg3]
        have h4 : (0 : ℝ) < 1/2 - 1/r := by
          linarith [show 2/r < 1 from by rw [div_lt_one hr_pos]; exact hr_gt_2]
        nlinarith
      -- d*y₁ - d*y₂ > 1 - 2/r (since d < 0 reverses direction)
      have h_dy_diff_large : d * y₁ - d * y₂ > 1 - 2/r := by
        have h1 : d * y₁ - d * y₂ = |(d : ℝ)| * (y₂ - y₁) := by
          rw [abs_of_neg (show (d : ℝ) < 0 from by exact_mod_cast h_d_neg)]; ring
        linarith [h_range_span]
      -- Band width bound: if a, b in same band, |a - b| ≤ 1 - 2/r
      have h_same_band_bound : ∀ m : ℤ, ∀ a b : ℝ,
          (m + 1/r ≤ a ∧ a ≤ m + 1 - 1/r) →
          (m + 1/r ≤ b ∧ b ≤ m + 1 - 1/r) →
          |a - b| ≤ 1 - 2/r := by
        intro m a b ⟨ha_lo, ha_hi⟩ ⟨hb_lo, hb_hi⟩
        have h2r : 2 / r = 2 * (1 / r) := by ring
        rw [h2r]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      -- General distance and non-adjacency for y ∈ (1/r, 1-1/r)
      have h_circle_dist_gt : ∀ y : ℝ, 1/r < y → y < 1 - 1/r → ∀ x : ℝ,
          1/r < circleDistance (circleProj x) (circleProj (x + y)) ∧
          circleProj x ≠ circleProj (x + y) := by
        intro y hy_lo hy_hi x
        have h_eq : circleDistance (circleProj x) (circleProj (x + y)) =
            ‖((-y : ℝ) : AddCircle (1 : ℝ))‖ := by
          rw [circleDistance_of_proj, ← AddCircle.coe_sub]
          congr 1; ring_nf
        rw [h_eq, AddCircle.norm_eq (1 : ℝ)]
        simp only [inv_one, one_mul, mul_one]
        constructor
        · by_cases hy_half : y ≤ 1/2
          · have h_round : round (-y) = 0 := by
              rw [round_eq_zero_iff]; constructor <;> linarith
            rw [h_round, Int.cast_zero, sub_zero, abs_neg, abs_of_pos (show 0 < y by linarith)]
            exact hy_lo
          · push_neg at hy_half
            have h_round : round (-y) = -1 := by
              apply round_eq_neg_one_of_neg_one_lt_lt_neg_half <;> linarith
            rw [h_round, Int.cast_neg, Int.cast_one,
                show (-y : ℝ) - -1 = 1 - y by ring, abs_of_pos (show 0 < 1 - y by linarith)]
            linarith
        · intro heq
          have h_norm_pos : 0 < ‖((-y : ℝ) : AddCircle (1 : ℝ))‖ := by
            rw [AddCircle.norm_eq (1 : ℝ), inv_one, one_mul, mul_one]
            by_cases hy_half : y ≤ 1/2
            · have h_round : round (-y) = 0 := by
                rw [round_eq_zero_iff]; constructor <;> linarith
              rw [h_round, Int.cast_zero, sub_zero, abs_neg, abs_of_pos (show 0 < y by linarith)]
              linarith
            · push_neg at hy_half
              have h_round : round (-y) = -1 := by
                apply round_eq_neg_one_of_neg_one_lt_lt_neg_half <;> linarith
              rw [h_round, Int.cast_neg, Int.cast_one,
                  show (-y : ℝ) - -1 = 1 - y by ring, abs_of_pos (show 0 < 1 - y by linarith)]
              linarith
          have h0 : circleDistance (circleProj x) (circleProj (x + y)) = 0 := by
            rw [circleDistance, heq, _root_.dist_self]
          rw [h_eq] at h0; linarith
      -- Cohom gap for general y
      have h_cohom_gap_general : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∀ x : ℝ, 1/r ≤ |g (x + y) - g x - round (g (x + y) - g x)| := by
        intro y hy_lo hy_hi x
        have ⟨h_dist_gt, h_ne_y⟩ := h_circle_dist_gt y hy_lo hy_hi x
        have h_nonadj_y : ¬(circleGraphOpen r hr).Adj (circleProj x) (circleProj (x + y)) := by
          simp only [circleGraphOpen, not_and_or, not_lt]; right; linarith
        have hfx : f (circleProj x) = circleProj (g x) := by
          have := congrFun hg x; simp only [Function.comp_apply] at this; exact this.symm
        have hfxy : f (circleProj (x + y)) = circleProj (g (x + y)) := by
          have := congrFun hg (x + y); simp only [Function.comp_apply] at this; exact this.symm
        have h_neg_δy : (g x - g (x + y) : ℝ) = -(g (x + y) - g x) := by ring
        have h_gx_ne : circleProj (g x) ≠ circleProj (g (x + y)) := by
          rw [← hfx, ← hfxy]
          rcases hf with hf_open | hf_closed
          · exact (hf_open (circleProj x) (circleProj (x + y)) h_ne_y h_nonadj_y).1
          · have h_nonadj_closed :
                ¬(circleGraphClosed r hr).Adj
                  (circleProj x)
                  (circleProj (x + y)) := by
              simp only [circleGraphClosed,
                not_and_or, not_not, not_le]
              right; linarith
            exact (hf_closed (circleProj x)
              (circleProj (x + y))
              h_ne_y h_nonadj_closed).1
        rcases hf with hf_open | hf_closed
        · have hcoh := hf_open (circleProj x)
            (circleProj (x + y))
            h_ne_y h_nonadj_y
          have h_not_adj := hcoh.2
          simp only [circleGraphOpen,
            not_and_or, not_not, not_lt]
            at h_not_adj
          rcases h_not_adj with h_eq | h_dist
          · rw [hfx, hfxy] at h_eq
            exact absurd h_eq h_gx_ne
          · rw [hfx, hfxy, circleDistance_of_proj,
              ← AddCircle.coe_sub,
              h_neg_δy] at h_dist
            rw [AddCircle.coe_neg, norm_neg,
              AddCircle.norm_eq 1] at h_dist
            simp only [inv_one, one_mul,
              mul_one] at h_dist
            exact h_dist
        · have h_nonadj_closed :
              ¬(circleGraphClosed r hr).Adj
                (circleProj x)
                (circleProj (x + y)) := by
            simp only [circleGraphClosed,
              not_and_or, not_not, not_le]
            right; linarith
          have hcoh := hf_closed (circleProj x)
            (circleProj (x + y))
            h_ne_y h_nonadj_closed
          have h_not_adj := hcoh.2
          simp only [circleGraphClosed, not_and_or, not_not, not_le] at h_not_adj
          rcases h_not_adj with h_eq | h_dist
          · rw [hfx, hfxy] at h_eq; exact absurd h_eq h_gx_ne
          · rw [hfx, hfxy, circleDistance_of_proj, ← AddCircle.coe_sub, h_neg_δy] at h_dist
            rw [AddCircle.coe_neg, norm_neg, AddCircle.norm_eq 1] at h_dist
            simp only [inv_one, one_mul, mul_one] at h_dist
            exact le_of_lt h_dist
      -- For y ∈ (1/r, 1-1/r), g(x+y) - g(x) is in some band
      have h_in_band_general : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∀ x : ℝ, ∃ m : ℤ, m + 1/r ≤ g (x + y) - g x ∧ g (x + y) - g x ≤ m + 1 - 1/r := by
        intro y hy_lo hy_hi x
        have hgap := h_cohom_gap_general y hy_lo hy_hi x
        have hround_bound : |g (x + y) - g x - round (g (x + y) - g x)| ≤ 1/2 := abs_sub_round _
        set δ := g (x + y) - g x with hδ_def
        by_cases hpos : δ - round δ ≥ 0
        · use round δ
          have h1 : δ - round δ ≥ 1/r := by rw [abs_of_nonneg hpos] at hgap; exact hgap
          have h2 : δ - round δ ≤ 1/2 := by
            rw [abs_of_nonneg hpos] at hround_bound
            exact hround_bound
          constructor <;> linarith [h1r_lt_half]
        · push_neg at hpos
          use round δ - 1
          have hneg : δ - round δ < 0 := hpos
          have h1 : -(δ - round δ) ≥ 1/r := by rw [abs_of_neg hneg] at hgap; exact hgap
          have h2 : -(δ - round δ) ≤ 1/2 := by
            rw [abs_of_neg hneg] at hround_bound
            exact hround_bound
          simp only [Int.cast_sub, Int.cast_one]
          constructor <;> linarith [h1r_lt_half]
      -- Connectedness argument: for fixed y, m(x, y) is constant in x
      have h_band_constant_in_x : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∃ m₀ : ℤ, ∀ x ∈ Set.Icc (0:ℝ) 1,
            m₀ + 1/r ≤ g (x + y) - g x
            ∧ g (x + y) - g x ≤ m₀ + 1 - 1/r := by
        intro y hy_lo hy_hi
        let δ_y : ℝ → ℝ := fun x => g (x + y) - g x
        have hδ_y_cont : Continuous δ_y :=
          (g.continuous.comp
            (continuous_id.add continuous_const)).sub
            g.continuous
        -- Pick band for x = 0
        obtain ⟨m₀, hm₀_band⟩ := h_in_band_general y hy_lo hy_hi 0
        use m₀
        -- Show all x ∈ [0,1] are in the same band, using IVT argument
        intro x hx
        obtain ⟨m, hm⟩ := h_in_band_general y hy_lo hy_hi x
        by_contra h_not_in
        simp only [not_and_or, not_le] at h_not_in
        have h_m_ne : m ≠ m₀ := by
          intro heq; subst heq
          rcases h_not_in with h | h
          · linarith [hm.1]
          · linarith [hm.2]
        -- IVT argument: if δ_y(0) and δ_y(x) are in different bands, there's a gap value in between
        rcases lt_trichotomy m₀ m with h_lt | h_eq | h_gt
        · -- m₀ < m: gap at integer m₀ + 1
          have h_le : m₀ + 1 ≤ m := Int.add_one_le_of_lt h_lt
          have h_le_real : (m₀ : ℝ) + 1 ≤ m := by exact_mod_cast h_le
          set v : ℝ := m₀ + 1 with hv_def
          have h_δ0_lt_v : δ_y 0 < v := by
            calc δ_y 0 ≤ m₀ + 1 - 1/r := hm₀_band.2
              _ < m₀ + 1 := by linarith [hr]
          have h_v_lt_δx : v < δ_y x := by
            calc v = m₀ + 1 := rfl
              _ ≤ m := h_le_real
              _ < m + 1/r := by linarith [hr]
              _ ≤ δ_y x := hm.1
          have h_x_nonneg : 0 ≤ x := hx.1
          have h_ivt := intermediate_value_Icc h_x_nonneg hδ_y_cont.continuousOn
          have hv_mem : v ∈ Set.Icc (δ_y 0) (δ_y x) := ⟨le_of_lt h_δ0_lt_v, le_of_lt h_v_lt_δx⟩
          obtain ⟨t, ht_mem, ht_eq⟩ := h_ivt hv_mem
          obtain ⟨m', hm'⟩ := h_in_band_general y hy_lo hy_hi t
          -- ht_eq : δ_y t = v, unfold to get g (t + y) - g t = v
          have ht_val : g (t + y) - g t = v := ht_eq
          have h_m'_le : m' ≤ m₀ := by
            have h1 : (m' : ℝ) + 1/r ≤ v := by linarith [ht_val, hm'.1]
            have h3 : (m' : ℝ) < m₀ + 1 := by linarith [hr]
            exact Int.le_of_lt_add_one (by exact_mod_cast h3)
          have h_m'_ge : m₀ + 1 ≤ m' := by
            have h1 : v ≤ m' + 1 - 1/r := by linarith [ht_val, hm'.2]
            have h3 : (m₀ : ℝ) < m' := by linarith [hr]
            exact Int.add_one_le_of_lt (by exact_mod_cast h3)
          omega
        · exact h_m_ne h_eq.symm
        · -- m < m₀: gap at integer m₀
          have h_le : m ≤ m₀ - 1 := Int.le_sub_one_of_lt h_gt
          have h_le_real : (m : ℝ) ≤ m₀ - 1 := by exact_mod_cast h_le
          set v : ℝ := (m₀ : ℝ) with hv_def
          have h_v_lt_δ0 : v < δ_y 0 := by
            calc v = m₀ := rfl
              _ < m₀ + 1/r := by linarith [hr]
              _ ≤ δ_y 0 := hm₀_band.1
          have h_δx_lt_v : δ_y x < v := by
            calc δ_y x ≤ m + 1 - 1/r := hm.2
              _ ≤ (m₀ - 1) + 1 - 1/r := by linarith
              _ = m₀ - 1/r := by ring
              _ < m₀ := by linarith [hr]
          have h_x_nonneg : 0 ≤ x := hx.1
          have h_ivt' := intermediate_value_Icc' h_x_nonneg hδ_y_cont.continuousOn
          have hv_mem : v ∈ Set.Icc (δ_y x) (δ_y 0) := ⟨le_of_lt h_δx_lt_v, le_of_lt h_v_lt_δ0⟩
          obtain ⟨t, _, ht_eq⟩ := h_ivt' hv_mem
          obtain ⟨m', hm'⟩ := h_in_band_general y hy_lo hy_hi t
          have ht_val : g (t + y) - g t = v := ht_eq
          have h_m'_le : m' ≤ m₀ - 1 := by
            have h1 : (m' : ℝ) + 1/r ≤ v := by linarith [ht_val, hm'.1]
            have h3 : (m' : ℝ) < m₀ := by linarith [hr]
            exact Int.le_sub_one_of_lt (by exact_mod_cast h3)
          have h_m'_ge : m₀ ≤ m' := by
            have h1 : v ≤ m' + 1 - 1/r := by linarith [ht_val, hm'.2]
            have h3 : (m₀ : ℝ) - 1 < m' := by linarith [hr]
            have h4 : m₀ - 1 < m' := by exact_mod_cast h3
            omega
          omega
      -- For y ∈ (1/r, 1-1/r), the integral ∫₀¹ δ_y dx = d*y
      have h_integral_eq_dy : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∫ x in (0:ℝ)..1, (g (x + y) - g x) = d * y := by
        intro y _ _
        have hg_int_all : ∀ a b, IntervalIntegrable (↑g) MeasureTheory.volume a b :=
          fun a b => g.continuous.intervalIntegrable a b
        have h_shift_int : IntervalIntegrable (fun x => g (x + y)) MeasureTheory.volume 0 1 :=
          (g.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable 0 1
        have h_subst : ∫ x in (0:ℝ)..1, g (x + y) = ∫ x in y..(1 + y), g x := by
          have :=
            intervalIntegral.integral_comp_add_right
              (a := (0:ℝ)) (b := (1:ℝ))
              (fun x => g x) y
          simp only at this
          (convert this using 2; ring)
        -- Split the integral at 1: ∫_y^{1+y} = ∫_y^1 + ∫_1^{1+y}
        have h_split : ∫ x in y..(1 + y), g x = (∫ x in y..1, g x) + ∫ x in (1:ℝ)..(1 + y), g x :=
          (intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _) (hg_int_all _ _)).symm
        -- Substitution for ∫_1^{1+y}: let u = x - 1, so ∫_1^{1+y} g(x) dx = ∫_0^y g(u+1) du
        have h_shift_back : ∫ x in (1:ℝ)..(1 + y), g x = ∫ x in (0:ℝ)..y, g (x + 1) := by
          have :=
            intervalIntegral.integral_comp_add_right
              (a := (0:ℝ)) (b := y)
              (fun x => g x) (1 : ℝ)
          simp only at this
          convert this.symm using 2 <;> ring
        have h_degree : ∫ x in (0:ℝ)..y, g (x + 1) = (∫ x in (0:ℝ)..y, g x) + d * y := by
          calc ∫ x in (0:ℝ)..y, g (x + 1)
              = ∫ x in (0:ℝ)..y, (g x + d) := by
                apply intervalIntegral.integral_congr; intro x _; exact hd x
            _ = (∫ x in (0:ℝ)..y, g x) + ∫ x in (0:ℝ)..y, (d : ℝ) := by
                rw [intervalIntegral.integral_add
                  (hg_int_all _ _)
                  (continuous_const.intervalIntegrable
                    _ _)]
            _ = (∫ x in (0:ℝ)..y, g x) + d * y := by
                simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
        -- Combine: ∫_y^{1+y} g = ∫_y^1 g + ∫_0^y g + d*y = ∫_0^1 g + d*y
        have h_combine : ∫ x in y..(1 + y), g x = (∫ x in (0:ℝ)..1, g x) + d * y := by
          rw [h_split, h_shift_back, h_degree]
          have h_split' : (∫ x in (0:ℝ)..y, g x) + ∫ x in y..1, g x =
              ∫ x in (0:ℝ)..1, g x :=
            intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _)
              (hg_int_all _ _)
          linarith
        calc ∫ x in (0:ℝ)..1, (g (x + y) - g x)
            = (∫ x in (0:ℝ)..1, g (x + y)) - ∫ x in (0:ℝ)..1, g x := by
              rw [intervalIntegral.integral_sub h_shift_int (hg_int_all 0 1)]
          _ = ((∫ x in (0:ℝ)..1, g x) + d * y) - ∫ x in (0:ℝ)..1, g x := by
            rw [h_subst, h_combine]
          _ = d * y := by ring
      -- Integral is in the band
      have h_integral_in_band : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∃ m₀ : ℤ, m₀ + 1/r ≤ d * y ∧ d * y ≤ m₀ + 1 - 1/r := by
        intro y hy_lo hy_hi
        obtain ⟨m₀, hm₀_all⟩ := h_band_constant_in_x y hy_lo hy_hi
        use m₀
        have hδ_y_cont : Continuous (fun x => g (x + y) - g x) :=
          (g.continuous.comp (continuous_id.add continuous_const)).sub g.continuous
        have hδ_y_int : IntervalIntegrable (fun x => g (x + y) - g x)
            MeasureTheory.volume 0 1 :=
          hδ_y_cont.intervalIntegrable 0 1
        have h_lower : ∀ x ∈ Set.Icc (0:ℝ) 1, m₀ + 1/r ≤ g (x + y) - g x :=
          fun x hx => (hm₀_all x hx).1
        have h_upper :
            ∀ x ∈ Set.Icc (0:ℝ) 1,
              g (x + y) - g x ≤ m₀ + 1 - 1/r :=
          fun x hx => (hm₀_all x hx).2
        rw [← h_integral_eq_dy y hy_lo hy_hi]
        constructor
        · calc m₀ + 1/r
              = ∫ _ in (0:ℝ)..1, (m₀ + 1/r : ℝ) := by
                simp [intervalIntegral.integral_const]
            _ ≤ ∫ x in (0:ℝ)..1, (g (x + y) - g x) := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
                · exact continuous_const.intervalIntegrable 0 1
                · exact hδ_y_int
                · exact h_lower
        · calc ∫ x in (0:ℝ)..1, (g (x + y) - g x)
              ≤ ∫ _ in (0:ℝ)..1, (m₀ + 1 - 1/r : ℝ) := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
                · exact hδ_y_int
                · exact continuous_const.intervalIntegrable 0 1
                · exact h_upper
            _ = m₀ + 1 - 1/r := by simp [intervalIntegral.integral_const]
      -- Now the final contradiction: d*y₁ and d*y₂ must be in bands, but they're too far apart.
      -- Get the bands for y₁ and y₂
      obtain ⟨m₁, hm₁⟩ := h_integral_in_band y₁ hy₁_lower hy₁_upper
      obtain ⟨m₂, hm₂⟩ := h_integral_in_band y₂ hy₂_lower hy₂_upper
      -- Connectedness in y: m₁ = m₂ (by IVT, if different bands, d*y passes through a gap)
      have h_m₁_eq_m₂ : m₁ = m₂ := by
        by_contra h_ne
        let F : ℝ → ℝ := fun y => d * y
        have hF_cont : Continuous F := continuous_const.mul continuous_id
        rcases lt_trichotomy m₁ m₂ with h_lt | h_eq | h_gt
        · -- m₁ < m₂: band m₁ below band m₂, but d < 0 so F(y₁) > F(y₂), contradiction
          have h_band_order : m₁ + 1 - 1/r < m₂ + 1/r := by
            have h1 : m₁ + 1 ≤ m₂ := Int.add_one_le_of_lt h_lt
            have h2 : (m₁ + 1 : ℝ) ≤ m₂ := by exact_mod_cast h1
            linarith [hr]
          have h1 : F y₁ ≤ m₁ + 1 - 1/r := hm₁.2
          have h2 : m₂ + 1/r ≤ F y₂ := hm₂.1
          have h3 : F y₁ < F y₂ := lt_of_le_of_lt h1 (lt_of_lt_of_le h_band_order h2)
          have h4 : F y₂ < F y₁ := by
            simp only [F]
            have h_neg_d : (d : ℝ) < 0 := hd_real_neg
            nlinarith
          linarith
        -- m₁ = m₂ case
        · exact h_ne h_eq
        -- m₁ > m₂ case
        · -- m₁ > m₂: F(y₁) > F(y₂) consistent, use IVT to find gap crossing
          have h_gap_value : m₂ + 1 - 1/r < (m₂ + 1 : ℝ) ∧ (m₂ + 1 : ℝ) < m₁ + 1/r := by
            constructor
            · linarith [hr]
            · have h1 : m₂ + 1 ≤ m₁ := Int.add_one_le_of_lt h_gt
              have h2 : (m₂ + 1 : ℝ) ≤ m₁ := by exact_mod_cast h1
              linarith [hr]
          -- Establish F bounds and the value between bands
          have hF_y₂_upper : F y₂ ≤ m₂ + 1 - 1/r := hm₂.2
          have hF_y₁_lower : m₁ + 1/r ≤ F y₁ := hm₁.1
          have hv_between : F y₂ < (m₂ + 1 : ℝ) ∧ (m₂ + 1 : ℝ) < F y₁ := by
            constructor
            · calc F y₂ ≤ m₂ + 1 - 1/r := hF_y₂_upper
                _ < m₂ + 1 := by linarith [hr]
            · calc (m₂ + 1 : ℝ) < m₁ + 1/r := h_gap_value.2
                _ ≤ F y₁ := hF_y₁_lower
          -- Apply IVT to find a gap crossing point
          have h_ivt_F := intermediate_value_Icc' (le_of_lt hy₁_lt_y₂) hF_cont.continuousOn
          have hv_mem : (m₂ + 1 : ℝ) ∈ Set.Icc (F y₂) (F y₁) :=
            ⟨le_of_lt hv_between.1, le_of_lt hv_between.2⟩
          obtain ⟨y_gap, hy_gap_mem, hy_gap_eq⟩ := h_ivt_F hv_mem
          -- y_gap ∈ [y₁, y₂] ⊆ (1/r, 1-1/r), so F(y_gap) must be in some band.
          have hy_gap_lo : 1/r < y_gap := lt_of_lt_of_le hy₁_lower hy_gap_mem.1
          have hy_gap_hi : y_gap < 1 - 1/r := lt_of_le_of_lt hy_gap_mem.2 hy₂_upper
          obtain ⟨m_gap, hm_gap⟩ := h_integral_in_band y_gap hy_gap_lo hy_gap_hi
          -- But F(y_gap) = d * y_gap = m₂ + 1, which is not in any band.
          have hy_gap_val : d * y_gap = (m₂ + 1 : ℝ) := hy_gap_eq
          rw [hy_gap_val] at hm_gap
          have : (m₂ + 1 : ℝ) = ((m₂ + 1 : ℤ) : ℝ) := by push_cast; ring
          rw [this] at hm_gap
          exact h_int_not_in_band (m₂ + 1) m_gap hm_gap
      -- Now use m₁ = m₂ and the bound on band width.
      rw [h_m₁_eq_m₂] at hm₁
      have h_same_band := h_same_band_bound m₂ (d * y₁) (d * y₂) hm₁ hm₂
      have h_abs_diff : |d * y₁ - d * y₂| = d * y₁ - d * y₂ := by
        apply abs_of_pos; linarith
      rw [h_abs_diff] at h_same_band
      linarith
  · -- d = 0
    -- d = 0 means d·y = 0 for all y, but 0 ∉ [m+1/r, m+1-1/r] for any integer m
    -- For 0 ∈ [m+1/r, m+1-1/r] we need:
    -- m + 1/r ≤ 0  →  m ≤ -1/r < 0  →  m ≤ -1 (since m is integer)
    -- m + 1 - 1/r ≥ 0  →  m ≥ 1/r - 1 > -1 (for r ≥ 2)  →  m ≥ 0 (since m is integer)
    -- These are contradictory: m ≤ -1 and m ≥ 0 is impossible.
    -- Therefore d = 0 leads to contradiction (d·y can't be in any valid interval)
    exfalso
    -- d = 0 implies d·y = 0, which can't lie in any interval [m+1/r, m+1-1/r]:
    -- m ≥ 0 gives lower bound ≥ 1/r > 0; m ≤ -1 gives upper bound ≤ -1/r < 0.
    have h_d_eq_0 : d = 0 := hd_zero
    -- With d = 0, g(x+1) = g(x), so g is 1-periodic
    -- The integration argument: ∫₀¹ (g(x+y) - g(x)) dx = d·y = 0
    -- But cohom requires this to be in [m + 1/r, m + 1 - 1/r] for some m
    -- 0 can't be in any such interval:
    -- m ≥ 0: lower bound m + 1/r ≥ 1/r > 0
    -- m ≤ -1: upper bound m + 1 - 1/r ≤ -1/r < 0
    --
    -- We use y = 1/2 which satisfies 1/r < 1/2 < 1 - 1/r for r > 2.
    -- The circle distance between circleProj(x) and circleProj(x + 1/2) is 1/2.
    -- By cohom, circleDistance(f(circleProj(x)), f(circleProj(x + 1/2))) ≥ 1/r.
    -- This means |g(x + 1/2) - g(x) - m| ≥ 1/r for the nearest integer m,
    -- i.e., g(x + 1/2) - g(x) ∈ [m + 1/r, m + 1 - 1/r] for some m.
    -- By connectedness, the same m works for all x.
    -- But ∫₀¹ (g(x + 1/2) - g(x)) dx = 0 must be in [m + 1/r, m + 1 - 1/r].
    -- This is impossible for any integer m.
    --
    -- Proof: Show 0 ∉ [m + 1/r, m + 1 - 1/r] for any m ∈ ℤ
    -- This is a pure arithmetic fact that doesn't depend on the full integration machinery.
    have h_no_m : ∀ m : ℤ, ¬(m + 1/r ≤ (0:ℝ) ∧ 0 ≤ m + 1 - 1/r) := by
      intro m ⟨h_lower, h_upper⟩
      -- From h_lower: m + 1/r ≤ 0 → m ≤ -1/r
      -- From h_upper: 0 ≤ m + 1 - 1/r → m ≥ 1/r - 1
      have h1 : (m : ℝ) ≤ -(1/r) := by linarith
      have h2 : (m : ℝ) ≥ 1/r - 1 := by linarith
      -- Combined: 1/r - 1 ≤ m ≤ -1/r
      -- For r > 1: 1/r < 1, so 1/r - 1 < 0 and -1/r > -1
      -- For r > 2: 1/r < 1/2, so 1/r - 1 > -1 and -1/r > -1/2
      -- So m ∈ [1/r - 1, -1/r] ⊂ (-1, 0) (since r > 2)
      -- But (-1, 0) contains no integers!
      have h_r_pos : (0 : ℝ) < r := by linarith
      -- m < 0 since m ≤ -1/r < 0
      have h_1r_pos : 0 < 1/r := by positivity
      have h_neg_1r : -(1/r) < 0 := by linarith
      have h_m_lt_0 : (m : ℝ) < 0 := lt_of_le_of_lt h1 h_neg_1r
      -- m > -1 since m ≥ 1/r - 1 > -1 (because 1/r > 0)
      have h_1r_pos' : 0 < 1/r := by positivity
      have h_lower_bd : -1 < 1/r - 1 := by linarith
      have h_m_gt_neg1 : (-1 : ℝ) < m := lt_of_lt_of_le h_lower_bd h2
      -- m is an integer with -1 < m < 0, contradiction
      have h_m_ge_0 : 0 ≤ m := by
        by_contra h_neg
        push_neg at h_neg
        have hm_le : m ≤ -1 := Int.le_sub_one_of_lt h_neg
        have hm_le_real : (m : ℝ) ≤ -1 := by exact_mod_cast hm_le
        linarith
      have h_m_ge_0_real : (0 : ℝ) ≤ m := by exact_mod_cast h_m_ge_0
      linarith
    -- Step 1: Define δ(x) = g(x + 1/2) - g(x)
    have h_half_in_range : 1/r < (1:ℝ)/2 ∧ (1:ℝ)/2 < 1 - 1/r := by
      constructor
      · have h_2_lt_r : (2:ℝ) < r := hr_gt_2
        have hr_pos : (0:ℝ) < r := by linarith
        rw [one_div, one_div, inv_lt_inv₀ hr_pos (by norm_num : (0:ℝ) < 2)]
        exact h_2_lt_r
      · have h2r : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
        linarith
    let δ : ℝ → ℝ := fun x => g (x + 1/2) - g x
    have hδ_cont : Continuous δ := by
      refine Continuous.sub ?_ g.continuous
      exact g.continuous.comp (continuous_id.add continuous_const)
    -- Step 2: Circle distance between circleProj(x) and circleProj(x + 1/2) is 1/2
    have h_dist_half : ∀ x : ℝ, circleDistance (circleProj x) (circleProj (x + 1/2)) = 1/2 := by
      intro x
      rw [circleDistance_of_proj]
      -- ‖(x - (x + 1/2) : AddCircle 1)‖ = 1/2
      -- Use AddCircle.coe_sub to relate the difference to ℝ
      rw [← AddCircle.coe_sub]
      have h_diff : x - (x + 1/2) = -(1/2 : ℝ) := by ring
      rw [h_diff]
      have h1_ne : (1 : ℝ) ≠ 0 := one_ne_zero
      rw [(AddCircle.norm_coe_eq_abs_iff 1 h1_ne).mpr]
      · simp only [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      · simp only [abs_neg, abs_one, one_div]
        norm_num
    -- Step 3: Points are non-adjacent since distance 1/2 > 1/r
    have h_nonadj : ∀ x : ℝ, ¬(circleGraphOpen r hr).Adj (circleProj x) (circleProj (x + 1/2)) := by
      intro x
      simp only [circleGraphOpen]
      push_neg
      intro _
      rw [h_dist_half]
      linarith [h_half_in_range.1]
    -- Step 4: By cohom, |δ(x) - round(δ(x))| ≥ 1/r for all x
    have h_gap : ∀ x : ℝ, 1/r ≤ |δ x - round (δ x)| := by
      intro x
      have h_nonadj_x := h_nonadj x
      -- The points are distinct since distance = 1/2 > 0
      have h_ne : circleProj x ≠ circleProj (x + 1/2) := by
        intro heq
        have hdist := h_dist_half x
        rw [heq] at hdist
        simp only [circleDistance, _root_.dist_self] at hdist
        norm_num at hdist
      -- Use hg to relate f to g
      have hfx : f (circleProj x) = circleProj (g x) := by
        have := congrFun hg x
        simp only [Function.comp_apply] at this
        exact this.symm
      have hfx2 : f (circleProj (x + 1/2)) = circleProj (g (x + 1/2)) := by
        have := congrFun hg (x + 1/2)
        simp only [Function.comp_apply] at this
        exact this.symm
      -- Compute g x - g(x + 1/2) = -δ x
      have h_neg_δ : (g x - g (x + 1/2) : ℝ) = -δ x := by simp only [δ]; ring
      -- The images are also distinct
      have h_gx_ne : circleProj (g x) ≠ circleProj (g (x + 1/2)) := by
        rw [← hfx, ← hfx2]
        rcases hf with hf_open | hf_closed
        · exact (hf_open (circleProj x) (circleProj (x + 1/2)) h_ne
                 h_nonadj_x).1
        · have h_nonadj_closed :
              ¬(circleGraphClosed r hr).Adj (circleProj x) (circleProj (x + 1/2))
              := by
            simp only [circleGraphClosed, not_and_or, not_not, not_le]
            right
            rw [h_dist_half]
            exact h_half_in_range.1
          exact (hf_closed (circleProj x) (circleProj (x + 1/2)) h_ne
                 h_nonadj_closed).1
      -- Case split on open vs closed cohom
      rcases hf with hf_open | hf_closed
      · -- Open cohom case
        have hcoh := hf_open (circleProj x) (circleProj (x + 1/2)) h_ne h_nonadj_x
        have h_not_adj := hcoh.2
        -- ¬(E[r]ᵒ hr).Adj means ¬(ne ∧ dist < 1/r), i.e., = ∨ dist ≥ 1/r
        simp only [circleGraphOpen, not_and_or, not_not, not_lt] at h_not_adj
        -- h_not_adj : f(...) = f(...) ∨ 1/r ≤ circleDistance(...)
        rcases h_not_adj with h_eq | h_dist
        · rw [hfx, hfx2] at h_eq; exact absurd h_eq h_gx_ne
        · rw [hfx, hfx2, circleDistance_of_proj, ← AddCircle.coe_sub, h_neg_δ] at h_dist
          rw [AddCircle.coe_neg, norm_neg, AddCircle.norm_eq 1] at h_dist
          simp only [inv_one, one_mul, mul_one] at h_dist
          exact h_dist
      · -- Closed cohom case
        have h_nonadj_closed :
            ¬(circleGraphClosed r hr).Adj
              (circleProj x)
              (circleProj (x + 1/2)) := by
          simp only [circleGraphClosed,
            not_and_or, not_not, not_le]
          right
          rw [h_dist_half]
          exact h_half_in_range.1
        have hcoh := hf_closed (circleProj x) (circleProj (x + 1/2)) h_ne h_nonadj_closed
        have h_not_adj := hcoh.2
        simp only [circleGraphClosed, not_and_or, not_not, not_le] at h_not_adj
        -- h_not_adj : f(...) = f(...) ∨ 1/r < circleDistance(...)
        rcases h_not_adj with h_eq | h_dist
        · rw [hfx, hfx2] at h_eq; exact absurd h_eq h_gx_ne
        · rw [hfx, hfx2, circleDistance_of_proj, ← AddCircle.coe_sub, h_neg_δ] at h_dist
          rw [AddCircle.coe_neg, norm_neg, AddCircle.norm_eq 1] at h_dist
          simp only [inv_one, one_mul, mul_one] at h_dist
          exact le_of_lt h_dist
    -- Step 5: δ(x) ∈ some band [m + 1/r, m + 1 - 1/r]
    have h_in_band : ∀ x : ℝ, ∃ m : ℤ, m + 1/r ≤ δ x ∧ δ x ≤ m + 1 - 1/r := by
      intro x
      have hgap := h_gap x
      have hround_bound : |δ x - round (δ x)| ≤ 1/2 := abs_sub_round (δ x)
      by_cases hpos : δ x - round (δ x) ≥ 0
      · -- δ x - round(δ x) ∈ [1/r, 1/2]
        use round (δ x)
        have h1 : δ x - round (δ x) ≥ 1/r := by rw [abs_of_nonneg hpos] at hgap; exact hgap
        have h2 : δ x - round (δ x) ≤ 1/2 := by
          rw [abs_of_nonneg hpos] at hround_bound
          exact hround_bound
        constructor <;> linarith [h1r_lt_half]
      · -- δ x - round(δ x) ∈ [-1/2, -1/r], use m = round(δ x) - 1
        push_neg at hpos
        use round (δ x) - 1
        have hneg : δ x - round (δ x) < 0 := hpos
        have h1 : -(δ x - round (δ x)) ≥ 1/r := by rw [abs_of_neg hneg] at hgap; exact hgap
        have h2 : -(δ x - round (δ x)) ≤ 1/2 := by
          rw [abs_of_neg hneg] at hround_bound
          exact hround_bound
        simp only [Int.cast_sub, Int.cast_one]
        constructor <;> linarith [h1r_lt_half]
    -- Step 6: By connectedness, δ([0,1]) is in a single band
    have h_image_preconn : IsPreconnected (Set.range (fun x : Set.Icc (0:ℝ) 1 => δ x.val)) := by
      have h_conn : IsConnected (Set.Icc (0:ℝ) 1) := isConnected_Icc (by norm_num : (0:ℝ) ≤ 1)
      have h_eq : (Set.range (fun x : Set.Icc (0:ℝ) 1 => δ x.val)) = δ '' Set.Icc 0 1 := by
        ext y
        simp only [Set.mem_range, Set.mem_image]
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x.val, x.property, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
      rw [h_eq]
      exact h_conn.isPreconnected.image _ hδ_cont.continuousOn
    -- The bands are pairwise disjoint
    have h_bands_disjoint : ∀ m₁ m₂ : ℤ, m₁ ≠ m₂ →
        Disjoint (Set.Icc (m₁ + 1/r) (m₁ + 1 - 1/r)) (Set.Icc (m₂ + 1/r) (m₂ + 1 - 1/r)) := by
      intro m₁ m₂ hne
      rw [Set.disjoint_iff]
      intro y ⟨hy1, hy2⟩
      simp only [Set.mem_Icc] at hy1 hy2
      have h1 : (m₁ : ℝ) + 1/r ≤ m₂ + 1 - 1/r := le_trans hy1.1 hy2.2
      have h2 : (m₂ : ℝ) + 1/r ≤ m₁ + 1 - 1/r := le_trans hy2.1 hy1.2
      have h_2r_lt_1 : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
      -- From h1: m₁ - m₂ ≤ 1 - 2/r < 1
      -- From h2: m₂ - m₁ ≤ 1 - 2/r < 1
      -- Combined: |m₁ - m₂| < 1, but m₁ - m₂ is an integer, so m₁ = m₂
      have h_diff1 : (m₁ : ℝ) - m₂ < 1 := by linarith
      have h_diff2 : (m₂ : ℝ) - m₁ < 1 := by linarith
      have h_abs : |(m₁ : ℝ) - m₂| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      have h_eq : m₁ = m₂ := by
        have h_diff_lt : -(1 : ℝ) < m₁ - m₂ ∧ (m₁ : ℝ) - m₂ < 1 := by
          constructor <;> linarith
        have h_int : (m₁ - m₂ : ℤ) = 0 := by
          have h1' : (-1 : ℤ) < m₁ - m₂ := by
            have : (-1 : ℝ) < m₁ - m₂ := h_diff_lt.1
            exact_mod_cast this
          have h2' : m₁ - m₂ < 1 := by
            have : (m₁ : ℝ) - m₂ < 1 := h_diff_lt.2
            exact_mod_cast this
          omega
        linarith [h_int]
      exact hne h_eq
    -- Pick the band containing δ(0)
    obtain ⟨m₀, hm₀_band⟩ := h_in_band 0
    -- Show all δ values on [0,1] are in this band
    have hm₀ : ∀ x ∈ Set.Icc (0:ℝ) 1, m₀ + 1/r ≤ δ x ∧ δ x ≤ m₀ + 1 - 1/r := by
      intro x hx
      obtain ⟨m, hm⟩ := h_in_band x
      by_contra h_not_in
      simp only [not_and_or, not_le] at h_not_in
      -- δ(x) is in band m, which is different from band m₀
      have h_m_ne : m ≠ m₀ := by
        intro heq
        subst heq
        rcases h_not_in with h | h
        · linarith [hm.1]
        · linarith [hm.2]
      -- Use connectedness argument: if δ(0) ∈ band m₀ and δ(x) ∈ band m with m ≠ m₀,
      -- then by IVT δ must take a value between the bands (in the gap)
      -- But such a value is not in any band, contradicting h_in_band
      rcases lt_trichotomy m₀ m with h_lt | h_eq | h_gt
      · -- m₀ < m: gap exists between band m₀ and band m
        -- Use v = m₀ + 1 (an integer in the gap between consecutive bands)
        -- The gap between band m₀ and band (m₀+1) is (m₀ + 1 - 1/r, m₀ + 1 + 1/r)
        -- The integer m₀ + 1 is in this gap and not in any band
        have h_le : m₀ + 1 ≤ m := Int.add_one_le_of_lt h_lt
        have h_le_real : (m₀ : ℝ) + 1 ≤ m := by exact_mod_cast h_le
        -- δ(0) ≤ m₀ + 1 - 1/r < m₀ + 1 < m₀ + 1 + 1/r ≤ m + 1/r ≤ δ(x)
        have h_delta_0_le : δ 0 ≤ m₀ + 1 - 1/r := hm₀_band.2
        have h_delta_x_ge : m + 1/r ≤ δ x := hm.1
        -- Set v = m₀ + 1 (the integer in the gap)
        set v : ℝ := m₀ + 1 with hv_def
        have h_δ0_lt_v : δ 0 < v := by
          calc δ 0 ≤ m₀ + 1 - 1/r := h_delta_0_le
            _ < m₀ + 1 := by linarith [hr]
        have h_v_lt_δx : v < δ x := by
          calc v = m₀ + 1 := rfl
            _ ≤ m := h_le_real
            _ < m + 1/r := by linarith [hr]
            _ ≤ δ x := h_delta_x_ge
        -- By IVT, there exists t ∈ [0, x] with δ(t) = v
        have h_x_nonneg : 0 ≤ x := hx.1
        have h_ivt := intermediate_value_Icc h_x_nonneg hδ_cont.continuousOn
        have hv_mem : v ∈ Set.Icc (δ 0) (δ x) := ⟨le_of_lt h_δ0_lt_v, le_of_lt h_v_lt_δx⟩
        obtain ⟨t, ht_mem, ht_eq⟩ := h_ivt hv_mem
        -- But v = m₀ + 1 is not in any band
        obtain ⟨m', hm'⟩ := h_in_band t
        rw [ht_eq] at hm'
        -- We have: m' + 1/r ≤ m₀ + 1 ≤ m' + 1 - 1/r
        -- From the lower bound: m' + 1/r ≤ m₀ + 1, so m' ≤ m₀ + 1 - 1/r < m₀ + 1, so m' ≤ m₀
        -- From the upper bound: m₀ + 1 ≤ m' + 1 - 1/r, so m₀ + 1/r ≤ m', so m₀ < m', so m' ≥ m₀ + 1
        -- Contradiction: m' ≤ m₀ and m' ≥ m₀ + 1
        have h_m'_le : m' ≤ m₀ := by
          have h1 : (m' : ℝ) + 1/r ≤ m₀ + 1 := hm'.1
          have h2 : (m' : ℝ) ≤ m₀ + 1 - 1/r := by linarith
          have h3 : (m' : ℝ) < m₀ + 1 := by linarith [hr]
          exact Int.le_of_lt_add_one (by exact_mod_cast h3)
        have h_m'_ge : m₀ + 1 ≤ m' := by
          have h1 : (m₀ : ℝ) + 1 ≤ m' + 1 - 1/r := hm'.2
          have h2 : (m₀ : ℝ) + 1/r ≤ m' := by linarith
          have h3 : (m₀ : ℝ) < m' := by linarith [hr]
          exact Int.add_one_le_of_lt (by exact_mod_cast h3)
        omega
      · exact h_m_ne h_eq.symm
      · -- m < m₀: symmetric case using v = m₀ (integer in gap)
        -- The gap between band (m₀-1) and band m₀ is (m₀ - 1/r, m₀ + 1/r)
        -- The integer m₀ is in this gap
        have h_le : m ≤ m₀ - 1 := Int.le_sub_one_of_lt h_gt
        have h_le_real : (m : ℝ) ≤ m₀ - 1 := by exact_mod_cast h_le
        -- δ(0) ≥ m₀ + 1/r > m₀ and δ(x) ≤ m + 1 - 1/r ≤ m₀ - 1/r < m₀
        have h_delta_0_ge : m₀ + 1/r ≤ δ 0 := hm₀_band.1
        have h_delta_x_le : δ x ≤ m + 1 - 1/r := hm.2
        -- Set v = m₀
        set v : ℝ := (m₀ : ℝ) with hv_def
        have h_v_lt_δ0 : v < δ 0 := by
          calc v = m₀ := rfl
            _ < m₀ + 1/r := by linarith [hr]
            _ ≤ δ 0 := h_delta_0_ge
        have h_δx_lt_v : δ x < v := by
          calc δ x ≤ m + 1 - 1/r := h_delta_x_le
            _ ≤ (m₀ - 1) + 1 - 1/r := by linarith
            _ = m₀ - 1/r := by ring
            _ < m₀ := by linarith [hr]
        -- By IVT on [0, x] with δ(x) < v < δ(0)
        have h_x_nonneg : 0 ≤ x := hx.1
        have h_ivt := intermediate_value_Icc h_x_nonneg hδ_cont.continuousOn
        -- Since δ(x) < v < δ(0), v is between them but in "reverse" order
        -- We need v ∈ [min(δ 0, δ x), max(δ 0, δ x)]
        have hv_mem : v ∈ Set.Icc (δ x) (δ 0) := ⟨le_of_lt h_δx_lt_v, le_of_lt h_v_lt_δ0⟩
        -- IVT gives us t with δ(t) in between
        have h_ivt' := intermediate_value_Icc' h_x_nonneg hδ_cont.continuousOn
        obtain ⟨t, ht_mem, ht_eq⟩ := h_ivt' hv_mem
        -- But v = m₀ is not in any band
        obtain ⟨m', hm'⟩ := h_in_band t
        rw [ht_eq] at hm'
        -- We have: m' + 1/r ≤ m₀ ≤ m' + 1 - 1/r
        -- From lower bound: m' + 1/r ≤ m₀, so m' ≤ m₀ - 1/r, so m' ≤ m₀ - 1
        -- From upper bound: m₀ ≤ m' + 1 - 1/r, so m₀ - 1 + 1/r ≤ m', so m₀ - 1 < m', so m' ≥ m₀
        have h_m'_le : m' ≤ m₀ - 1 := by
          have h1 : (m' : ℝ) + 1/r ≤ m₀ := hm'.1
          have h2 : (m' : ℝ) ≤ m₀ - 1/r := by linarith
          have h3 : (m' : ℝ) < m₀ := by linarith [hr]
          exact Int.le_sub_one_of_lt (by exact_mod_cast h3)
        have h_m'_ge : m₀ ≤ m' := by
          have h1 : (m₀ : ℝ) ≤ m' + 1 - 1/r := hm'.2
          have h2 : (m₀ : ℝ) - 1 + 1/r ≤ m' := by linarith
          have h3 : (m₀ : ℝ) - 1 < m' := by linarith [hr]
          have h4 : m₀ - 1 < m' := by exact_mod_cast h3
          omega
        omega
    -- Step 7: Compute integral ∫₀¹ δ dx = d·(1/2) = 0 (since d = 0)
    have h_integral_eq : ∫ x in (0:ℝ)..1, δ x = (d : ℝ) * (1/2) := by
      have hg_int_all : ∀ a b, IntervalIntegrable (↑g) MeasureTheory.volume a b :=
        fun a b => g.continuous.intervalIntegrable a b
      have h_shift_int : IntervalIntegrable (fun x => g (x + 1/2)) MeasureTheory.volume 0 1 :=
        (g.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable 0 1
      have h_subst : ∫ x in (0:ℝ)..1, g (x + 1/2) =
          ∫ x in (1/2:ℝ)..(3/2), g x := by
        have := intervalIntegral.integral_comp_add_right
          (a := (0:ℝ)) (b := (1:ℝ)) (fun x => g x) (1/2 : ℝ)
        simp only [] at this
        convert this using 2 <;> ring
      have h_split : ∫ x in (1/2:ℝ)..(3/2), g x =
          (∫ x in (1/2:ℝ)..1, g x) +
          ∫ x in (1:ℝ)..(3/2), g x :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hg_int_all _ _) (hg_int_all _ _)).symm
      have h_period : ∫ x in (1:ℝ)..(3/2), g x =
          ∫ x in (0:ℝ)..(1/2), g (x + 1) := by
        have :=
          intervalIntegral.integral_comp_add_right
            (a := (0:ℝ)) (b := (1/2:ℝ))
            (fun x => g x) (1 : ℝ)
        simp only [] at this
        convert this.symm using 2 <;> ring
      have h_degree :
          ∫ x in (0:ℝ)..(1/2), g (x + 1) =
          (∫ x in (0:ℝ)..(1/2), g x) + d * (1/2) := by
        calc ∫ x in (0:ℝ)..(1/2), g (x + 1)
            = ∫ x in (0:ℝ)..(1/2), (g x + d) := by
              apply intervalIntegral.integral_congr
              intro x _; exact hd x
          _ = (∫ x in (0:ℝ)..(1/2), g x)
              + ∫ x in (0:ℝ)..(1/2), (d : ℝ) := by
              rw [intervalIntegral.integral_add
                (hg_int_all _ _)
                (continuous_const.intervalIntegrable
                  _ _)]
          _ = (∫ x in (0:ℝ)..(1/2), g x)
              + d * (1/2) := by
              simp only [
                intervalIntegral.integral_const,
                sub_zero, smul_eq_mul, mul_comm]
      have h_combine :
          ∫ x in (1/2:ℝ)..(3/2), g x =
          (∫ x in (0:ℝ)..1, g x) + d * (1/2) := by
        rw [h_split, h_period, h_degree]
        have h_split' :
            (∫ x in (0:ℝ)..(1/2), g x)
              + ∫ x in (1/2:ℝ)..1, g x =
            ∫ x in (0:ℝ)..1, g x :=
          intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _) (hg_int_all _ _)
        linarith
      have hg_int : IntervalIntegrable (↑g) MeasureTheory.volume 0 1 := hg_int_all 0 1
      calc ∫ x in (0:ℝ)..1, δ x
          = ∫ x in (0:ℝ)..1, (g (x + 1/2) - g x) := by rfl
        _ = (∫ x in (0:ℝ)..1, g (x + 1/2)) - ∫ x in (0:ℝ)..1, g x := by
            rw [intervalIntegral.integral_sub h_shift_int hg_int]
        _ = ((∫ x in (0:ℝ)..1, g x) + d * (1/2)) - ∫ x in (0:ℝ)..1, g x := by
            rw [h_subst, h_combine]
        _ = d * (1/2) := by ring
    -- Step 8: For d = 0, integral = 0
    have h_integral_zero : ∫ x in (0:ℝ)..1, δ x = 0 := by
      rw [h_integral_eq, hd_zero]
      simp
    -- Step 9: If δ([0,1]) ⊆ [m₀ + 1/r, m₀ + 1 - 1/r], integral ∈ [m₀ + 1/r, m₀ + 1 - 1/r]
    have h_integral_in_band : m₀ + 1/r ≤ ∫ x in (0:ℝ)..1, δ x ∧
        ∫ x in (0:ℝ)..1, δ x ≤ m₀ + 1 - 1/r := by
      have hδ_int : IntervalIntegrable δ MeasureTheory.volume 0 1 := hδ_cont.intervalIntegrable 0 1
      constructor
      · -- Lower bound using MeasureTheory.integral_mono
        have h_lower : ∀ x ∈ Set.Icc (0:ℝ) 1, m₀ + 1/r ≤ δ x := fun x hx => (hm₀ x hx).1
        calc m₀ + 1/r = ∫ _ in (0:ℝ)..1, (m₀ + 1/r : ℝ) := by
              simp [intervalIntegral.integral_const]
          _ ≤ ∫ x in (0:ℝ)..1, δ x := by
              apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
              · exact continuous_const.intervalIntegrable 0 1
              · exact hδ_int
              · exact h_lower
      · -- Upper bound
        have h_upper : ∀ x ∈ Set.Icc (0:ℝ) 1, δ x ≤ m₀ + 1 - 1/r := fun x hx => (hm₀ x hx).2
        calc ∫ x in (0:ℝ)..1, δ x
            ≤ ∫ _ in (0:ℝ)..1, (m₀ + 1 - 1/r : ℝ) := by
              apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
              · exact hδ_int
              · exact continuous_const.intervalIntegrable 0 1
              · exact h_upper
          _ = m₀ + 1 - 1/r := by simp [intervalIntegral.integral_const]
    -- Step 10: Contradiction: 0 ∈ [m₀ + 1/r, m₀ + 1 - 1/r] but h_no_m says no
    rw [h_integral_zero] at h_integral_in_band
    exact h_no_m m₀ h_integral_in_band
  · -- d > 0: Since d ≠ 1, we have d ≥ 2
    have hd_ge_2 : d ≥ 2 := by omega
    -- The integration argument: ∫₀¹ (g(x+y) - g(x)) dx = d·y
    -- For y varying in [1/r, 1-1/r], d·y ranges from d/r to d(1-1/r).
    -- This range has length d·(1-2/r).
    -- Each valid band [m+1/r, m+1-1/r] has length 1-2/r.
    -- For d ≥ 2 and r > 2: d·(1-2/r) ≥ 2·(1-2/r) > 1-2/r.
    -- So the range of d·y exceeds any single band's length.
    -- By IVT, as y varies continuously, d·y must leave any single band,
    -- crossing into the forbidden zone around some integer.
    -- This contradicts the cohom constraint.
    --
    -- Key arithmetic: for r > 2, 1 - 2/r > 0.
    -- Band length = 1 - 2/r.
    -- Range length = d·(1-2/r) with d ≥ 2.
    -- So range length ≥ 2·(1-2/r) > 1·(1-2/r) = band length.
    have h_band_length_pos : 0 < 1 - 2/r := by
      have h2r : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
      linarith
    have h_range_length : (d : ℝ) * (1 - 2/r) ≥ 2 * (1 - 2/r) := by
      have hd_real : (2 : ℝ) ≤ d := by exact_mod_cast hd_ge_2
      have h_pos : 0 < 1 - 2/r := h_band_length_pos
      nlinarith
    -- The range [d/r, d(1-1/r)] has length d(1-2/r) > 1-2/r
    -- But any path in this range that stays in valid bands can traverse at most 1-2/r
    -- (since bands are disjoint with gaps of 2/r around each integer).
    -- This is a contradiction, so d ≥ 2 is impossible.
    --
    -- The formal proof follows the integration + connectedness argument.
    -- For each fixed y, the function x ↦ g(x+y)-g(x) stays in one band.
    -- The integral ∫₀¹(g(x+y)-g(x))dx = d·y is in that band.
    -- As y varies in [1/r, 1-1/r], d·y varies continuously.
    -- The endpoints d/r and d(1-1/r) differ by d(1-2/r) > 1-2/r.
    -- So d·y cannot stay in a single band of length 1-2/r.
    -- By connectedness, the only way to move between bands is through the gap.
    -- But the gap is the forbidden zone, contradicting the cohom constraint.
    --
    -- The arithmetic shows that no single band can contain both d/r and d(1-1/r):
    -- If d/r ∈ [m+1/r, m+1-1/r], then d/r ≥ m + 1/r, so d ≥ mr + 1.
    -- Also d/r ≤ m + 1 - 1/r, so d ≤ mr + r - 1.
    -- If d(1-1/r) ∈ [m+1/r, m+1-1/r], then d(r-1)/r ≥ m + 1/r.
    -- So d ≥ (mr + 1)r/(r-1) = (mr + 1)·r/(r-1).
    -- Also d(r-1)/r ≤ m + 1 - 1/r = (mr + r - 1)/r.
    -- So d ≤ (mr + r - 1)/(r-1).
    --
    -- For m = 0: d ≥ 1 and d ≤ r-1 from first.
    --           d ≥ r/(r-1) > 1 and d ≤ (r-1)/(r-1) = 1 from second.
    --           Combined: d = 1, contradicting d ≥ 2.
    -- For m ≥ 1: d ≥ mr+1 ≥ r+1 > 3 (for r > 2) from first.
    --            d ≤ (mr+r-1)/(r-1) ≤ (r+r-1)/(r-1) = (2r-1)/(r-1) < 3 for r > 2.
    --            (Check: (2r-1)/(r-1) = 2 + 1/(r-1) < 3 for r > 2.)
    --            Contradiction: d > 3 but d < 3.
    --
    -- For d ≥ 2, we use the integration argument similar to d = 0 case
    -- The key observation: for even d, d/2 is an integer, and integers are not in any band
    -- For odd d ≥ 3, we need the "range length exceeds band length" argument
    exfalso
    -- Key lemma: any integer is not in any band
    have h_int_not_in_band : ∀ n : ℤ, ∀ m : ℤ,
        ¬((m : ℝ) + 1/r ≤ n ∧ (n : ℝ) ≤ m + 1 - 1/r) := by
      intro n m ⟨h_lower, h_upper⟩
      have h1r_pos : 0 < 1/r := by positivity
      -- From h_lower: m + 1/r ≤ n, so m < n (since 1/r > 0)
      have h1 : (m : ℝ) < n := by linarith
      -- From h_upper: n ≤ m + 1 - 1/r < m + 1, so n < m + 1
      have h2 : (n : ℝ) < m + 1 := by linarith
      -- Convert to integer inequalities
      have h_m_lt_n : m < n := Int.cast_lt.mp h1
      have h_n_lt_m1 : n < m + 1 := by
        have h2' : (n : ℝ) < (m + 1 : ℤ) := by
          simp only [Int.cast_add, Int.cast_one]
          exact h2
        exact Int.cast_lt.mp h2'
      -- m < n and n < m + 1 implies m < n < m + 1, impossible for integers
      omega
    -- Replicate integration infrastructure from d = 0 case
    have h_half_in_range' : 1/r < (1:ℝ)/2 ∧ (1:ℝ)/2 < 1 - 1/r := by
      constructor
      · rw [one_div, one_div, inv_lt_inv₀ hr_pos (by norm_num : (0:ℝ) < 2)]
        exact hr_gt_2
      · have h2r : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
        linarith
    let δ' : ℝ → ℝ := fun x => g (x + 1/2) - g x
    have hδ'_cont : Continuous δ' :=
      (g.continuous.comp (continuous_id.add continuous_const)).sub g.continuous
    -- The integral of δ' over [0,1] equals d/2
    have h_integral_eq' : ∫ x in (0:ℝ)..1, δ' x = (d : ℝ) / 2 := by
      have hg_int : IntervalIntegrable (↑g) MeasureTheory.volume 0 1 :=
        g.continuous.intervalIntegrable 0 1
      have h_shift_int : IntervalIntegrable (fun x => g (x + 1/2))
          MeasureTheory.volume 0 1 :=
        (g.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable 0 1
      have h_subst :
          ∫ x in (0:ℝ)..1, g (x + 1/2) =
          ∫ x in (1/2:ℝ)..(3/2), g x := by
        have :=
          intervalIntegral.integral_comp_add_right
            (a := (0:ℝ)) (b := (1:ℝ))
            (fun x => g x) (1/2 : ℝ)
        simp only at this
        convert this using 2 <;> ring
      have h_split :
          ∫ x in (1/2:ℝ)..(3/2), g x =
          (∫ x in (1/2:ℝ)..1, g x)
            + ∫ x in (1:ℝ)..(3/2), g x :=
        (intervalIntegral.integral_add_adjacent_intervals
          (g.continuous.intervalIntegrable _ _)
          (g.continuous.intervalIntegrable _ _)).symm
      have h_period :
          ∫ x in (1:ℝ)..(3/2), g x =
          ∫ x in (0:ℝ)..(1/2), g (x + 1) := by
        have :=
          intervalIntegral.integral_comp_add_right
            (a := (0:ℝ)) (b := (1/2:ℝ))
            (fun x => g x) (1 : ℝ)
        simp only at this
        convert this.symm using 2 <;> ring
      have h_degree :
          ∫ x in (0:ℝ)..(1/2), g (x + 1) =
          (∫ x in (0:ℝ)..(1/2), g x)
            + d * (1/2) := by
        calc ∫ x in (0:ℝ)..(1/2), g (x + 1)
            = ∫ x in (0:ℝ)..(1/2), (g x + d) := by
              apply intervalIntegral.integral_congr
              intro x _; exact hd x
          _ = (∫ x in (0:ℝ)..(1/2), g x)
              + ∫ x in (0:ℝ)..(1/2), (d : ℝ) := by
              rw [intervalIntegral.integral_add
                (g.continuous.intervalIntegrable _ _)
                (continuous_const.intervalIntegrable
                  _ _)]
          _ = (∫ x in (0:ℝ)..(1/2), g x)
              + d * (1/2) := by
              simp only [
                intervalIntegral.integral_const,
                sub_zero, smul_eq_mul, mul_comm]
      have h_combine :
          ∫ x in (1/2:ℝ)..(3/2), g x =
          (∫ x in (0:ℝ)..1, g x) + d * (1/2) := by
        rw [h_split, h_period, h_degree]
        have h_split' :
            (∫ x in (0:ℝ)..(1/2), g x)
              + ∫ x in (1/2:ℝ)..1, g x =
            ∫ x in (0:ℝ)..1, g x :=
          intervalIntegral.integral_add_adjacent_intervals
            (g.continuous.intervalIntegrable _ _)
            (g.continuous.intervalIntegrable _ _)
        linarith
      calc ∫ x in (0:ℝ)..1, δ' x
          = ∫ x in (0:ℝ)..1, (g (x + 1/2) - g x) :=
            rfl
        _ = (∫ x in (0:ℝ)..1, g (x + 1/2))
            - ∫ x in (0:ℝ)..1, g x := by
            rw [intervalIntegral.integral_sub
              h_shift_int hg_int]
        _ = ((∫ x in (0:ℝ)..1, g x) + d * (1/2))
            - ∫ x in (0:ℝ)..1, g x := by
            rw [h_subst, h_combine]
        _ = d * (1/2) := by ring
        _ = d / 2 := by ring
    -- For d = 2 specifically, d/2 = 1 which is not in any band
    -- For odd d ≥ 3, the range argument applies
    by_cases hd_even : 2 ∣ d
    · -- d is even, so d/2 is an integer
      obtain ⟨k, hk⟩ := hd_even
      have hk_eq : d / 2 = k := by omega
      have hk_ge : k ≥ 1 := by omega
      -- Replicate the infrastructure from d = 0 / d ≤ -2 even case
      have h_dist_half'' : ∀ x : ℝ, circleDistance (circleProj x) (circleProj (x + 1/2)) = 1/2 := by
        intro x
        rw [circleDistance_of_proj, ← AddCircle.coe_sub]
        have h_diff : x - (x + 1/2) = -(1/2 : ℝ) := by ring
        rw [h_diff]
        have h1_ne : (1 : ℝ) ≠ 0 := one_ne_zero
        rw [(AddCircle.norm_coe_eq_abs_iff 1 h1_ne).mpr]
        · simp only [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
        · simp only [abs_neg, abs_one, one_div]; norm_num
      have h_nonadj'' : ∀ x : ℝ,
          ¬(circleGraphOpen r hr).Adj
            (circleProj x)
            (circleProj (x + 1/2)) := by
        intro x
        simp only [circleGraphOpen]
        push_neg; intro _
        rw [h_dist_half'']
        linarith [h_half_in_range'.1]
      have h_gap'' : ∀ x : ℝ, 1/r ≤ |δ' x - round (δ' x)| := by
        intro x
        have h_nonadj_x := h_nonadj'' x
        have h_ne : circleProj x ≠ circleProj (x + 1/2) := by
          intro heq
          have hdist := h_dist_half'' x
          rw [heq] at hdist
          simp only [circleDistance, _root_.dist_self] at hdist
          norm_num at hdist
        have hfx : f (circleProj x) = circleProj (g x) := by
          have := congrFun hg x; simp only [Function.comp_apply] at this; exact this.symm
        have hfx2 : f (circleProj (x + 1/2)) = circleProj (g (x + 1/2)) := by
          have := congrFun hg (x + 1/2); simp only [Function.comp_apply] at this; exact this.symm
        have h_neg_δ' : (g x - g (x + 1/2) : ℝ) = -δ' x := by simp only [δ']; ring
        have h_gx_ne : circleProj (g x) ≠ circleProj (g (x + 1/2)) := by
          rw [← hfx, ← hfx2]
          rcases hf with hf_open | hf_closed
          · exact (hf_open (circleProj x) (circleProj (x + 1/2)) h_ne h_nonadj_x).1
          · have h_nonadj_closed :
                ¬(circleGraphClosed r hr).Adj
                  (circleProj x)
                  (circleProj (x + 1/2)) := by
              simp only [circleGraphClosed,
                not_and_or, not_not, not_le]
              right; rw [h_dist_half'']
              exact h_half_in_range'.1
            exact (hf_closed (circleProj x)
              (circleProj (x + 1/2))
              h_ne h_nonadj_closed).1
        rcases hf with hf_open | hf_closed
        · have hcoh := hf_open (circleProj x)
            (circleProj (x + 1/2)) h_ne h_nonadj_x
          have h_not_adj := hcoh.2
          simp only [circleGraphOpen, not_and_or, not_not, not_lt] at h_not_adj
          rcases h_not_adj with h_eq | h_dist
          · rw [hfx, hfx2] at h_eq; exact absurd h_eq h_gx_ne
          · rw [hfx, hfx2, circleDistance_of_proj, ← AddCircle.coe_sub, h_neg_δ'] at h_dist
            rw [AddCircle.coe_neg, norm_neg, AddCircle.norm_eq 1] at h_dist
            simp only [inv_one, one_mul, mul_one]
              at h_dist
            exact h_dist
        · have h_nonadj_closed :
              ¬(circleGraphClosed r hr).Adj
                (circleProj x)
                (circleProj (x + 1/2)) := by
            simp only [circleGraphClosed,
              not_and_or, not_not, not_le]
            right; rw [h_dist_half'']
            exact h_half_in_range'.1
          have hcoh := hf_closed (circleProj x)
            (circleProj (x + 1/2))
            h_ne h_nonadj_closed
          have h_not_adj := hcoh.2
          simp only [circleGraphClosed, not_and_or, not_not, not_le] at h_not_adj
          rcases h_not_adj with h_eq | h_dist
          · rw [hfx, hfx2] at h_eq; exact absurd h_eq h_gx_ne
          · rw [hfx, hfx2, circleDistance_of_proj, ← AddCircle.coe_sub, h_neg_δ'] at h_dist
            rw [AddCircle.coe_neg, norm_neg, AddCircle.norm_eq 1] at h_dist
            simp only [inv_one, one_mul, mul_one] at h_dist; exact le_of_lt h_dist
      have h_in_band'' : ∀ x : ℝ, ∃ m : ℤ, m + 1/r ≤ δ' x ∧ δ' x ≤ m + 1 - 1/r := by
        intro x
        have hgap := h_gap'' x
        have hround_bound : |δ' x - round (δ' x)| ≤ 1/2 := abs_sub_round (δ' x)
        by_cases hpos : δ' x - round (δ' x) ≥ 0
        · use round (δ' x)
          have h1 : δ' x - round (δ' x) ≥ 1/r := by rw [abs_of_nonneg hpos] at hgap; exact hgap
          have h2 : δ' x - round (δ' x) ≤ 1/2 := by
            rw [abs_of_nonneg hpos] at hround_bound
            exact hround_bound
          constructor <;> linarith [h1r_lt_half]
        · push_neg at hpos
          use round (δ' x) - 1
          have hneg : δ' x - round (δ' x) < 0 := hpos
          have h1 : -(δ' x - round (δ' x)) ≥ 1/r := by rw [abs_of_neg hneg] at hgap; exact hgap
          have h2 : -(δ' x - round (δ' x)) ≤ 1/2 := by
            rw [abs_of_neg hneg] at hround_bound
            exact hround_bound
          simp only [Int.cast_sub, Int.cast_one]
          constructor <;> linarith [h1r_lt_half]
      have h_image_preconn'' :
          IsPreconnected (Set.range
            (fun x : Set.Icc (0:ℝ) 1 =>
              δ' x.val)) := by
        have h_conn : IsConnected (Set.Icc (0:ℝ) 1) := isConnected_Icc (by norm_num : (0:ℝ) ≤ 1)
        have h_eq : (Set.range (fun x : Set.Icc (0:ℝ) 1 => δ' x.val)) = δ' '' Set.Icc 0 1 := by
          ext y; simp only [Set.mem_range, Set.mem_image]
          constructor
          · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
          · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
        rw [h_eq]
        exact h_conn.isPreconnected.image _ hδ'_cont.continuousOn
      have h_bands_disjoint'' : ∀ m₁ m₂ : ℤ, m₁ ≠ m₂ →
          Disjoint (Set.Icc (m₁ + 1/r) (m₁ + 1 - 1/r)) (Set.Icc (m₂ + 1/r) (m₂ + 1 - 1/r)) := by
        intro m₁ m₂ hne
        rw [Set.disjoint_iff]
        intro y ⟨hy1, hy2⟩
        simp only [Set.mem_Icc] at hy1 hy2
        have h1 : (m₁ : ℝ) + 1/r ≤ m₂ + 1 - 1/r := le_trans hy1.1 hy2.2
        have h2 : (m₂ : ℝ) + 1/r ≤ m₁ + 1 - 1/r := le_trans hy2.1 hy1.2
        have h_2r_lt_1 : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
        have h_diff1 : (m₁ : ℝ) - m₂ < 1 := by linarith
        have h_diff2 : (m₂ : ℝ) - m₁ < 1 := by linarith
        have h_eq : m₁ = m₂ := by
          have h_diff_lt : -(1 : ℝ) < m₁ - m₂ ∧ (m₁ : ℝ) - m₂ < 1 := by constructor <;> linarith
          have h_int : (m₁ - m₂ : ℤ) = 0 := by
            have h1' : (-1 : ℤ) < m₁ - m₂ := by
              have : (-1 : ℝ) < m₁ - m₂ := h_diff_lt.1
              exact_mod_cast this
            have h2' : m₁ - m₂ < 1 := by
              have : (m₁ : ℝ) - m₂ < 1 := h_diff_lt.2
              exact_mod_cast this
            omega
          linarith [h_int]
        exact hne h_eq
      obtain ⟨m₀'', hm₀''_band⟩ := h_in_band'' 0
      have hm₀''_all : ∀ x ∈ Set.Icc (0:ℝ) 1, m₀'' + 1/r ≤ δ' x ∧ δ' x ≤ m₀'' + 1 - 1/r := by
        intro x hx
        obtain ⟨m, hm⟩ := h_in_band'' x
        by_contra h_not_in
        simp only [not_and_or, not_le] at h_not_in
        have h_m_ne : m ≠ m₀'' := by
          intro heq; subst heq
          rcases h_not_in with h | h
          · linarith [hm.1]
          · linarith [hm.2]
        rcases lt_trichotomy m₀'' m with h_lt | h_eq | h_gt
        · have h_le : m₀'' + 1 ≤ m := Int.add_one_le_of_lt h_lt
          have h_le_real : (m₀'' : ℝ) + 1 ≤ m := by exact_mod_cast h_le
          have h_delta_0_le : δ' 0 ≤ m₀'' + 1 - 1/r := hm₀''_band.2
          have h_delta_x_ge : m + 1/r ≤ δ' x := hm.1
          set v : ℝ := m₀'' + 1 with hv_def
          have h_δ0_lt_v : δ' 0 < v := by
            calc δ' 0 ≤ m₀'' + 1 - 1/r := h_delta_0_le
              _ < m₀'' + 1 := by linarith [hr]
          have h_v_lt_δx : v < δ' x := by
            calc v = m₀'' + 1 := rfl
              _ ≤ m := h_le_real
              _ < m + 1/r := by linarith [hr]
              _ ≤ δ' x := h_delta_x_ge
          have h_x_nonneg : 0 ≤ x := hx.1
          have h_ivt := intermediate_value_Icc h_x_nonneg hδ'_cont.continuousOn
          have hv_mem : v ∈ Set.Icc (δ' 0) (δ' x) := ⟨le_of_lt h_δ0_lt_v, le_of_lt h_v_lt_δx⟩
          obtain ⟨t, _, ht_eq⟩ := h_ivt hv_mem
          obtain ⟨m', hm'⟩ := h_in_band'' t
          rw [ht_eq] at hm'
          have h_m'_le : m' ≤ m₀'' := by
            have h1 : (m' : ℝ) + 1/r ≤ m₀'' + 1 := hm'.1
            have h3 : (m' : ℝ) < m₀'' + 1 := by linarith [hr]
            exact Int.le_of_lt_add_one (by exact_mod_cast h3)
          have h_m'_ge : m₀'' + 1 ≤ m' := by
            have h1 : (m₀'' : ℝ) + 1 ≤ m' + 1 - 1/r := hm'.2
            have h3 : (m₀'' : ℝ) < m' := by linarith [hr]
            exact Int.add_one_le_of_lt (by exact_mod_cast h3)
          omega
        · exact h_m_ne h_eq.symm
        · have h_le : m ≤ m₀'' - 1 := Int.le_sub_one_of_lt h_gt
          have h_le_real : (m : ℝ) ≤ m₀'' - 1 := by exact_mod_cast h_le
          have h_delta_0_ge : m₀'' + 1/r ≤ δ' 0 := hm₀''_band.1
          have h_delta_x_le : δ' x ≤ m + 1 - 1/r := hm.2
          set v : ℝ := (m₀'' : ℝ) with hv_def
          have h_v_lt_δ0 : v < δ' 0 := by
            calc v = m₀'' := rfl
              _ < m₀'' + 1/r := by linarith [hr]
              _ ≤ δ' 0 := h_delta_0_ge
          have h_δx_lt_v : δ' x < v := by
            calc δ' x ≤ m + 1 - 1/r := h_delta_x_le
              _ ≤ (m₀'' - 1) + 1 - 1/r := by linarith
              _ = m₀'' - 1/r := by ring
              _ < m₀'' := by linarith [hr]
          have h_x_nonneg : 0 ≤ x := hx.1
          have h_ivt' := intermediate_value_Icc' h_x_nonneg hδ'_cont.continuousOn
          have hv_mem : v ∈ Set.Icc (δ' x) (δ' 0) := ⟨le_of_lt h_δx_lt_v, le_of_lt h_v_lt_δ0⟩
          obtain ⟨t, _, ht_eq⟩ := h_ivt' hv_mem
          obtain ⟨m', hm'⟩ := h_in_band'' t
          rw [ht_eq] at hm'
          have h_m'_le : m' ≤ m₀'' - 1 := by
            have h1 : (m' : ℝ) + 1/r ≤ m₀'' := hm'.1
            have h3 : (m' : ℝ) < m₀'' := by linarith [hr]
            exact Int.le_sub_one_of_lt (by exact_mod_cast h3)
          have h_m'_ge : m₀'' ≤ m' := by
            have h1 : (m₀'' : ℝ) ≤ m' + 1 - 1/r := hm'.2
            have h3 : (m₀'' : ℝ) - 1 < m' := by linarith [hr]
            have h4 : m₀'' - 1 < m' := by exact_mod_cast h3
            omega
          omega
      have h_integral_in_band'' : m₀'' + 1/r ≤ ∫ x in (0:ℝ)..1, δ' x ∧
          ∫ x in (0:ℝ)..1, δ' x ≤ m₀'' + 1 - 1/r := by
        have hδ'_int :
            IntervalIntegrable δ' MeasureTheory.volume
              0 1 :=
          hδ'_cont.intervalIntegrable 0 1
        constructor
        · have h_lower : ∀ x ∈ Set.Icc (0:ℝ) 1, m₀'' + 1/r ≤ δ' x := fun x hx => (hm₀''_all x hx).1
          calc m₀'' + 1/r
              = ∫ _ in (0:ℝ)..1, (m₀'' + 1/r : ℝ) := by
                simp [intervalIntegral.integral_const]
            _ ≤ ∫ x in (0:ℝ)..1, δ' x := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
                · exact continuous_const.intervalIntegrable 0 1
                · exact hδ'_int
                · exact h_lower
        · have h_upper :
              ∀ x ∈ Set.Icc (0:ℝ) 1,
                δ' x ≤ m₀'' + 1 - 1/r :=
            fun x hx => (hm₀''_all x hx).2
          calc ∫ x in (0:ℝ)..1, δ' x ≤ ∫ _ in (0:ℝ)..1, (m₀'' + 1 - 1/r : ℝ) := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
                · exact hδ'_int
                · exact continuous_const.intervalIntegrable 0 1
                · exact h_upper
            _ = m₀'' + 1 - 1/r := by simp [intervalIntegral.integral_const]
      have h_integral_is_k : ∫ x in (0:ℝ)..1, δ' x = k := by
        rw [h_integral_eq']
        have hk_real : (d : ℝ) / 2 = k := by
          have : d = 2 * k := hk
          rw [this]
          push_cast
          ring
        exact hk_real
      rw [h_integral_is_k] at h_integral_in_band''
      exact h_int_not_in_band k m₀'' h_integral_in_band''
    · -- d is odd with |d| ≥ 3 (i.e., d ≥ 3), use range length argument
      -- Symmetric to the d ≤ -3 case
      have hd_ge_3 : d ≥ 3 := by
        -- d ≥ 2, d is odd, so d ≥ 3
        have h1 : d ≥ 2 := hd_ge_2
        have h2 : ¬(2 ∣ d) := hd_even
        by_contra h_neg
        push_neg at h_neg
        (interval_cases d; simp_all)
      have hd_abs_ge_3 : 3 ≤ |d| := by
        simp only [abs_of_pos (by omega : 0 < d)]
        omega
      -- Key arithmetic: range length exceeds band length
      have h_band_length : (1 : ℝ) - 2/r > 0 := by
        have h2r : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
        linarith
      have h_range_exceeds_band : |d| * (1 - 2/r) > 1 - 2/r := by
        have h1 : (3 : ℝ) ≤ |d| := by exact_mod_cast hd_abs_ge_3
        have h2 : (1 : ℝ) < 3 := by norm_num
        calc |d| * (1 - 2/r) ≥ 3 * (1 - 2/r) := by
              apply mul_le_mul_of_nonneg_right h1 (le_of_lt h_band_length)
          _ > 1 * (1 - 2/r) := mul_lt_mul_of_pos_right h2 h_band_length
          _ = 1 - 2/r := one_mul _
      -- The argument is symmetric to d ≤ -3:
      -- Range of d·y for y ∈ (1/r, 1-1/r) has length |d|·(1-2/r) > band length
      -- So no single band can contain all integral values, contradicting connectedness

      -- The proof is essentially the same as the d ≤ -3 case, with d > 0 instead of d < 0.
      have h_d_pos : d > 0 := by omega
      have hd_real_pos : (d : ℝ) > 0 := by exact_mod_cast h_d_pos
      -- Pick two y values in (1/r, 1-1/r)
      set ε : ℝ := (1 - 2/r)/4 with hε_def
      have hε_pos : 0 < ε := by simp only [hε_def]; linarith
      set y₁ : ℝ := 1/r + ε with hy₁_def
      set y₂ : ℝ := 1 - 1/r - ε with hy₂_def
      have h_3eps : 3 * ε = 3/4 - 3/(2*r) := by rw [hε_def]; ring
      have hε_val : ε = 1/4 - 1/(2*r) := by rw [hε_def]; field_simp; ring
      have h_inv_2r_pos : (0:ℝ) < 1/(2*r) := by positivity
      have h_inv_2r_eq : 1/r = 2 * (1/(2*r)) := by field_simp
      have hy₁_lower : 1/r < y₁ := by rw [hy₁_def]; linarith
      have hy₁_upper : y₁ < 1 - 1/r := by
        rw [hy₁_def, hε_val, h_inv_2r_eq]
        linarith
      have hy₂_lower : 1/r < y₂ := by
        rw [hy₂_def, hε_val, h_inv_2r_eq]
        linarith
      have hy₂_upper : y₂ < 1 - 1/r := by rw [hy₂_def]; linarith
      have hy₁_lt_y₂ : y₁ < y₂ := by
        rw [hy₁_def, hy₂_def, hε_val, h_inv_2r_eq]
        linarith
      -- Compute the difference y₂ - y₁ and the range span
      have h_diff_y : y₂ - y₁ = 1 - 2/r - 2 * ε := by rw [hy₁_def, hy₂_def]; ring
      have h_diff_y' : y₂ - y₁ = (1 - 2/r)/2 := by rw [h_diff_y, hε_def]; ring
      have h_range_span : |(d : ℝ)| * (y₂ - y₁) > 1 - 2/r := by
        rw [h_diff_y']
        have h1 : (1:ℝ) - 2/r = 2 * ((1 - 2/r)/2) := by ring
        rw [h1]
        have h3 : (2 : ℝ) < |(d : ℝ)| := by
          rw [abs_of_pos (show (d : ℝ) > 0 from by exact_mod_cast h_d_pos)]
          linarith [show (d : ℝ) ≥ 3 from by exact_mod_cast hd_ge_3]
        have h4 : (0 : ℝ) < (1 - 2/r)/2 := by linarith
        nlinarith
      -- Since d > 0 and y₁ < y₂, we have d*y₁ < d*y₂
      have h_dy_diff_large : d * y₂ - d * y₁ > 1 - 2/r := by
        have h1 : d * y₂ - d * y₁ = |(d : ℝ)| * (y₂ - y₁) := by
          rw [abs_of_pos (show (d : ℝ) > 0 from by exact_mod_cast h_d_pos)]
          ring
        linarith [h_range_span]
      -- Same band bound lemma
      have h_same_band_bound : ∀ m : ℤ, ∀ a b : ℝ,
          (m + 1/r ≤ a ∧ a ≤ m + 1 - 1/r) →
          (m + 1/r ≤ b ∧ b ≤ m + 1 - 1/r) →
          |a - b| ≤ 1 - 2/r := by
        intro m a b ⟨ha_lo, ha_hi⟩ ⟨hb_lo, hb_hi⟩
        have h2r : 2 / r = 2 * (1 / r) := by ring
        rw [h2r]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      -- Cohom gap for general y ∈ (1/r, 1-1/r): same as d ≤ -3 case
      have h_circle_dist_gt : ∀ y : ℝ, 1/r < y → y < 1 - 1/r → ∀ x : ℝ,
          1/r < circleDistance (circleProj x) (circleProj (x + y)) ∧
          circleProj x ≠ circleProj (x + y) := by
        intro y hy_lo hy_hi x
        have h_eq : circleDistance (circleProj x) (circleProj (x + y)) =
            ‖((-y : ℝ) : AddCircle (1 : ℝ))‖ := by
          rw [circleDistance_of_proj, ← AddCircle.coe_sub]
          congr 1; ring_nf
        rw [h_eq, AddCircle.norm_eq (1 : ℝ)]
        simp only [inv_one, one_mul, mul_one]
        constructor
        · by_cases hy_half : y ≤ 1/2
          · have h_round : round (-y) = 0 := by
              rw [round_eq_zero_iff]; constructor <;> linarith
            rw [h_round, Int.cast_zero, sub_zero, abs_neg, abs_of_pos (show 0 < y by linarith)]
            exact hy_lo
          · push_neg at hy_half
            have h_round : round (-y) = -1 := by
              apply round_eq_neg_one_of_neg_one_lt_lt_neg_half <;> linarith
            rw [h_round, Int.cast_neg, Int.cast_one,
                show (-y : ℝ) - -1 = 1 - y by ring, abs_of_pos (show 0 < 1 - y by linarith)]
            linarith
        · intro heq
          have h_norm_pos : 0 < ‖((-y : ℝ) : AddCircle (1 : ℝ))‖ := by
            rw [AddCircle.norm_eq (1 : ℝ), inv_one, one_mul, mul_one]
            by_cases hy_half : y ≤ 1/2
            · have h_round : round (-y) = 0 := by
                rw [round_eq_zero_iff]; constructor <;> linarith
              rw [h_round, Int.cast_zero, sub_zero, abs_neg, abs_of_pos (show 0 < y by linarith)]
              linarith
            · push_neg at hy_half
              have h_round : round (-y) = -1 := by
                apply round_eq_neg_one_of_neg_one_lt_lt_neg_half <;> linarith
              rw [h_round, Int.cast_neg, Int.cast_one,
                  show (-y : ℝ) - -1 = 1 - y by ring, abs_of_pos (show 0 < 1 - y by linarith)]
              linarith
          have h0 : circleDistance (circleProj x) (circleProj (x + y)) = 0 := by
            rw [circleDistance, heq, _root_.dist_self]
          rw [h_eq] at h0; linarith
      have h_cohom_gap_general : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∀ x : ℝ, 1/r ≤ |g (x + y) - g x - round (g (x + y) - g x)| := by
        intro y hy_lo hy_hi x
        have ⟨h_dist_gt, h_ne_y⟩ := h_circle_dist_gt y hy_lo hy_hi x
        have h_nonadj_y : ¬(circleGraphOpen r hr).Adj (circleProj x) (circleProj (x + y)) := by
          simp only [circleGraphOpen, not_and_or, not_lt]; right; linarith
        have hfx : f (circleProj x) = circleProj (g x) := by
          have := congrFun hg x; simp only [Function.comp_apply] at this; exact this.symm
        have hfxy : f (circleProj (x + y)) = circleProj (g (x + y)) := by
          have := congrFun hg (x + y); simp only [Function.comp_apply] at this; exact this.symm
        have h_neg_δy : (g x - g (x + y) : ℝ) = -(g (x + y) - g x) := by ring
        have h_gx_ne : circleProj (g x) ≠ circleProj (g (x + y)) := by
          rw [← hfx, ← hfxy]
          rcases hf with hf_open | hf_closed
          · exact (hf_open (circleProj x) (circleProj (x + y)) h_ne_y h_nonadj_y).1
          · have h_nonadj_closed :
                ¬(circleGraphClosed r hr).Adj
                  (circleProj x)
                  (circleProj (x + y)) := by
              simp only [circleGraphClosed,
                not_and_or, not_not, not_le]
              right; linarith
            exact (hf_closed (circleProj x)
              (circleProj (x + y))
              h_ne_y h_nonadj_closed).1
        rcases hf with hf_open | hf_closed
        · have hcoh := hf_open (circleProj x)
            (circleProj (x + y))
            h_ne_y h_nonadj_y
          have h_not_adj := hcoh.2
          simp only [circleGraphOpen,
            not_and_or, not_not, not_lt]
            at h_not_adj
          rcases h_not_adj with h_eq | h_dist
          · rw [hfx, hfxy] at h_eq
            exact absurd h_eq h_gx_ne
          · rw [hfx, hfxy, circleDistance_of_proj,
              ← AddCircle.coe_sub,
              h_neg_δy] at h_dist
            rw [AddCircle.coe_neg, norm_neg,
              AddCircle.norm_eq 1] at h_dist
            simp only [inv_one, one_mul,
              mul_one] at h_dist
            exact h_dist
        · have h_nonadj_closed :
              ¬(circleGraphClosed r hr).Adj
                (circleProj x)
                (circleProj (x + y)) := by
            simp only [circleGraphClosed,
              not_and_or, not_not, not_le]
            right; linarith
          have hcoh := hf_closed (circleProj x)
            (circleProj (x + y))
            h_ne_y h_nonadj_closed
          have h_not_adj := hcoh.2
          simp only [circleGraphClosed, not_and_or, not_not, not_le] at h_not_adj
          rcases h_not_adj with h_eq | h_dist
          · rw [hfx, hfxy] at h_eq; exact absurd h_eq h_gx_ne
          · rw [hfx, hfxy, circleDistance_of_proj, ← AddCircle.coe_sub, h_neg_δy] at h_dist
            rw [AddCircle.coe_neg, norm_neg, AddCircle.norm_eq 1] at h_dist
            simp only [inv_one, one_mul, mul_one] at h_dist
            exact le_of_lt h_dist
      -- For y in (1/r, 1-1/r), g(x+y) - g(x) is in some band
      have h_in_band_general : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∀ x : ℝ, ∃ m : ℤ, m + 1/r ≤ g (x + y) - g x ∧ g (x + y) - g x ≤ m + 1 - 1/r := by
        intro y hy_lo hy_hi x
        have hgap := h_cohom_gap_general y hy_lo hy_hi x
        have hround_bound : |g (x + y) - g x - round (g (x + y) - g x)| ≤ 1/2 := abs_sub_round _
        set δ := g (x + y) - g x with hδ_def
        by_cases hpos : δ - round δ ≥ 0
        · use round δ
          have h1 : δ - round δ ≥ 1/r := by rw [abs_of_nonneg hpos] at hgap; exact hgap
          have h2 : δ - round δ ≤ 1/2 := by
            rw [abs_of_nonneg hpos] at hround_bound
            exact hround_bound
          constructor <;> linarith [h1r_lt_half]
        · push_neg at hpos
          use round δ - 1
          have hneg : δ - round δ < 0 := hpos
          have h1 : -(δ - round δ) ≥ 1/r := by rw [abs_of_neg hneg] at hgap; exact hgap
          have h2 : -(δ - round δ) ≤ 1/2 := by
            rw [abs_of_neg hneg] at hround_bound
            exact hround_bound
          simp only [Int.cast_sub, Int.cast_one]
          constructor <;> linarith [h1r_lt_half]
      -- Connectedness: for fixed y, m(x, y) is constant in x
      have h_band_constant_in_x : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∃ m₀ : ℤ, ∀ x ∈ Set.Icc (0:ℝ) 1,
            m₀ + 1/r ≤ g (x + y) - g x
            ∧ g (x + y) - g x ≤ m₀ + 1 - 1/r := by
        intro y hy_lo hy_hi
        let δ_y : ℝ → ℝ := fun x => g (x + y) - g x
        have hδ_y_cont : Continuous δ_y :=
          (g.continuous.comp
            (continuous_id.add continuous_const)).sub
            g.continuous
        obtain ⟨m₀, hm₀_band⟩ := h_in_band_general y hy_lo hy_hi 0
        use m₀
        intro x hx
        obtain ⟨m, hm⟩ := h_in_band_general y hy_lo hy_hi x
        by_contra h_not_in
        simp only [not_and_or, not_le] at h_not_in
        have h_m_ne : m ≠ m₀ := by
          intro heq; subst heq
          rcases h_not_in with h | h
          · linarith [hm.1]
          · linarith [hm.2]
        rcases lt_trichotomy m₀ m with h_lt | h_eq | h_gt
        · have h_le : m₀ + 1 ≤ m := Int.add_one_le_of_lt h_lt
          have h_le_real : (m₀ : ℝ) + 1 ≤ m := by exact_mod_cast h_le
          set v : ℝ := m₀ + 1 with hv_def
          have h_δ0_lt_v : δ_y 0 < v := by
            calc δ_y 0 ≤ m₀ + 1 - 1/r := hm₀_band.2
              _ < m₀ + 1 := by linarith [hr]
          have h_v_lt_δx : v < δ_y x := by
            calc v = m₀ + 1 := rfl
              _ ≤ m := h_le_real
              _ < m + 1/r := by linarith [hr]
              _ ≤ δ_y x := hm.1
          have h_x_nonneg : 0 ≤ x := hx.1
          have h_ivt := intermediate_value_Icc h_x_nonneg hδ_y_cont.continuousOn
          have hv_mem : v ∈ Set.Icc (δ_y 0) (δ_y x) := ⟨le_of_lt h_δ0_lt_v, le_of_lt h_v_lt_δx⟩
          obtain ⟨t, _, ht_eq⟩ := h_ivt hv_mem
          obtain ⟨m', hm'⟩ := h_in_band_general y hy_lo hy_hi t
          have ht_val : g (t + y) - g t = v := ht_eq
          have h_m'_le : m' ≤ m₀ := by
            have h1 : (m' : ℝ) + 1/r ≤ v := by linarith [ht_val, hm'.1]
            have h3 : (m' : ℝ) < m₀ + 1 := by linarith [hr]
            exact Int.le_of_lt_add_one (by exact_mod_cast h3)
          have h_m'_ge : m₀ + 1 ≤ m' := by
            have h1 : v ≤ m' + 1 - 1/r := by linarith [ht_val, hm'.2]
            have h3 : (m₀ : ℝ) < m' := by linarith [hr]
            exact Int.add_one_le_of_lt (by exact_mod_cast h3)
          omega
        · exact h_m_ne h_eq.symm
        · have h_le : m ≤ m₀ - 1 := Int.le_sub_one_of_lt h_gt
          have h_le_real : (m : ℝ) ≤ m₀ - 1 := by exact_mod_cast h_le
          set v : ℝ := (m₀ : ℝ) with hv_def
          have h_v_lt_δ0 : v < δ_y 0 := by
            calc v = m₀ := rfl
              _ < m₀ + 1/r := by linarith [hr]
              _ ≤ δ_y 0 := hm₀_band.1
          have h_δx_lt_v : δ_y x < v := by
            calc δ_y x ≤ m + 1 - 1/r := hm.2
              _ ≤ (m₀ - 1) + 1 - 1/r := by linarith
              _ = m₀ - 1/r := by ring
              _ < m₀ := by linarith [hr]
          have h_x_nonneg : 0 ≤ x := hx.1
          have h_ivt' := intermediate_value_Icc' h_x_nonneg hδ_y_cont.continuousOn
          have hv_mem : v ∈ Set.Icc (δ_y x) (δ_y 0) := ⟨le_of_lt h_δx_lt_v, le_of_lt h_v_lt_δ0⟩
          obtain ⟨t, _, ht_eq⟩ := h_ivt' hv_mem
          obtain ⟨m', hm'⟩ := h_in_band_general y hy_lo hy_hi t
          have ht_val : g (t + y) - g t = v := ht_eq
          have h_m'_le : m' ≤ m₀ - 1 := by
            have h1 : (m' : ℝ) + 1/r ≤ v := by linarith [ht_val, hm'.1]
            have h3 : (m' : ℝ) < m₀ := by linarith [hr]
            exact Int.le_sub_one_of_lt (by exact_mod_cast h3)
          have h_m'_ge : m₀ ≤ m' := by
            have h1 : v ≤ m' + 1 - 1/r := by linarith [ht_val, hm'.2]
            have h3 : (m₀ : ℝ) - 1 < m' := by linarith [hr]
            have h4 : m₀ - 1 < m' := by exact_mod_cast h3
            omega
          omega
      -- For y in (1/r, 1-1/r), the integral equals d*y
      have h_integral_eq_dy : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∫ x in (0:ℝ)..1, (g (x + y) - g x) = d * y := by
        intro y _ _
        have hg_int_all : ∀ a b, IntervalIntegrable (↑g) MeasureTheory.volume a b :=
          fun a b => g.continuous.intervalIntegrable a b
        have h_shift_int : IntervalIntegrable (fun x => g (x + y)) MeasureTheory.volume 0 1 :=
          (g.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable 0 1
        have h_subst : ∫ x in (0:ℝ)..1, g (x + y) = ∫ x in y..(1 + y), g x := by
          have :=
            intervalIntegral.integral_comp_add_right
              (a := (0:ℝ)) (b := (1:ℝ))
              (fun x => g x) y
          simp only at this; (convert this using 2; ring)
        have h_split : ∫ x in y..(1 + y), g x = (∫ x in y..1, g x) + ∫ x in (1:ℝ)..(1 + y), g x :=
          (intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _) (hg_int_all _ _)).symm
        have h_shift_back : ∫ x in (1:ℝ)..(1 + y), g x = ∫ x in (0:ℝ)..y, g (x + 1) := by
          have :=
            intervalIntegral.integral_comp_add_right
              (a := (0:ℝ)) (b := y)
              (fun x => g x) (1 : ℝ)
          simp only at this; convert this.symm using 2 <;> ring
        have h_degree : ∫ x in (0:ℝ)..y, g (x + 1) = (∫ x in (0:ℝ)..y, g x) + d * y := by
          calc ∫ x in (0:ℝ)..y, g (x + 1)
              = ∫ x in (0:ℝ)..y, (g x + d) := by
                apply intervalIntegral.integral_congr
                intro x _; exact hd x
            _ = (∫ x in (0:ℝ)..y, g x) + ∫ x in (0:ℝ)..y, (d : ℝ) := by
                rw [intervalIntegral.integral_add
                  (hg_int_all _ _)
                  (continuous_const.intervalIntegrable
                    _ _)]
            _ = (∫ x in (0:ℝ)..y, g x) + d * y := by
                simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
        have h_combine : ∫ x in y..(1 + y), g x = (∫ x in (0:ℝ)..1, g x) + d * y := by
          rw [h_split, h_shift_back, h_degree]
          have h_split' : (∫ x in (0:ℝ)..y, g x) + ∫ x in y..1, g x = ∫ x in (0:ℝ)..1, g x :=
            intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _) (hg_int_all _ _)
          linarith
        calc ∫ x in (0:ℝ)..1, (g (x + y) - g x)
            = (∫ x in (0:ℝ)..1, g (x + y)) - ∫ x in (0:ℝ)..1, g x := by
              rw [intervalIntegral.integral_sub h_shift_int (hg_int_all 0 1)]
          _ = ((∫ x in (0:ℝ)..1, g x) + d * y) - ∫ x in (0:ℝ)..1, g x := by rw [h_subst, h_combine]
          _ = d * y := by ring
      -- Integral is in the band
      have h_integral_in_band : ∀ y : ℝ, 1/r < y → y < 1 - 1/r →
          ∃ m₀ : ℤ, m₀ + 1/r ≤ d * y ∧ d * y ≤ m₀ + 1 - 1/r := by
        intro y hy_lo hy_hi
        obtain ⟨m₀, hm₀_all⟩ := h_band_constant_in_x y hy_lo hy_hi
        use m₀
        have hδ_y_cont : Continuous (fun x => g (x + y) - g x) :=
          (g.continuous.comp (continuous_id.add continuous_const)).sub g.continuous
        have hδ_y_int : IntervalIntegrable (fun x => g (x + y) - g x) MeasureTheory.volume 0 1 :=
          hδ_y_cont.intervalIntegrable 0 1
        have h_lower :
            ∀ x ∈ Set.Icc (0:ℝ) 1,
              m₀ + 1/r ≤ g (x + y) - g x :=
          fun x hx => (hm₀_all x hx).1
        have h_upper :
            ∀ x ∈ Set.Icc (0:ℝ) 1,
              g (x + y) - g x ≤ m₀ + 1 - 1/r :=
          fun x hx => (hm₀_all x hx).2
        rw [← h_integral_eq_dy y hy_lo hy_hi]
        constructor
        · calc m₀ + 1/r
              = ∫ _ in (0:ℝ)..1, (m₀ + 1/r : ℝ) := by
                simp [intervalIntegral.integral_const]
            _ ≤ ∫ x in (0:ℝ)..1, (g (x + y) - g x) := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
                · exact continuous_const.intervalIntegrable 0 1
                · exact hδ_y_int
                · exact h_lower
        · calc ∫ x in (0:ℝ)..1, (g (x + y) - g x)
              ≤ ∫ _ in (0:ℝ)..1, (m₀ + 1 - 1/r : ℝ) := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
                · exact hδ_y_int
                · exact continuous_const.intervalIntegrable 0 1
                · exact h_upper
            _ = m₀ + 1 - 1/r := by simp [intervalIntegral.integral_const]
      -- Extract the bands for y₁ and y₂
      obtain ⟨m₁, hm₁⟩ := h_integral_in_band y₁ hy₁_lower hy₁_upper
      obtain ⟨m₂, hm₂⟩ := h_integral_in_band y₂ hy₂_lower hy₂_upper
      -- Connectedness in y: m₁ = m₂
      have h_m₁_eq_m₂ : m₁ = m₂ := by
        by_contra h_ne
        let F : ℝ → ℝ := fun y => d * y
        have hF_cont : Continuous F := continuous_const.mul continuous_id
        rcases lt_trichotomy m₁ m₂ with h_lt | h_eq | h_gt
        · -- m₁ < m₂: band m₁ is below band m₂
          -- Since d > 0, F is increasing, so F(y₁) < F(y₂)
          -- F(y₁) ∈ band m₁, F(y₂) ∈ band m₂, band m₁ < band m₂
          -- By IVT, F passes through the gap between bands.
          have h_band_order : m₁ + 1 - 1/r < m₂ + 1/r := by
            have h1 : m₁ + 1 ≤ m₂ := Int.add_one_le_of_lt h_lt
            have h2 : (m₁ + 1 : ℝ) ≤ m₂ := by exact_mod_cast h1
            linarith [hr]
          have h_gap_value : m₁ + 1 - 1/r < (m₁ + 1 : ℝ) ∧ (m₁ + 1 : ℝ) < m₂ + 1/r := by
            constructor
            · linarith [hr]
            · have h1 : m₁ + 1 ≤ m₂ := Int.add_one_le_of_lt h_lt
              have h2 : (m₁ + 1 : ℝ) ≤ m₂ := by exact_mod_cast h1
              linarith [hr]
          have hF_y₁_upper : F y₁ ≤ m₁ + 1 - 1/r := hm₁.2
          have hF_y₂_lower : m₂ + 1/r ≤ F y₂ := hm₂.1
          have hv_between : F y₁ < (m₁ + 1 : ℝ) ∧ (m₁ + 1 : ℝ) < F y₂ := by
            constructor
            · calc F y₁ ≤ m₁ + 1 - 1/r := hF_y₁_upper
                _ < m₁ + 1 := by linarith [hr]
            · calc (m₁ + 1 : ℝ) < m₂ + 1/r := h_gap_value.2
                _ ≤ F y₂ := hF_y₂_lower
          have h_ivt_F := intermediate_value_Icc (le_of_lt hy₁_lt_y₂) hF_cont.continuousOn
          have hv_mem : (m₁ + 1 : ℝ) ∈ Set.Icc (F y₁) (F y₂) :=
            ⟨le_of_lt hv_between.1, le_of_lt hv_between.2⟩
          obtain ⟨y_gap, hy_gap_mem, hy_gap_eq⟩ := h_ivt_F hv_mem
          have hy_gap_lo : 1/r < y_gap := lt_of_lt_of_le hy₁_lower hy_gap_mem.1
          have hy_gap_hi : y_gap < 1 - 1/r := lt_of_le_of_lt hy_gap_mem.2 hy₂_upper
          obtain ⟨m_gap, hm_gap⟩ := h_integral_in_band y_gap hy_gap_lo hy_gap_hi
          have hy_gap_val : d * y_gap = (m₁ + 1 : ℝ) := hy_gap_eq
          rw [hy_gap_val] at hm_gap
          have : (m₁ + 1 : ℝ) = ((m₁ + 1 : ℤ) : ℝ) := by push_cast; ring
          rw [this] at hm_gap
          exact h_int_not_in_band (m₁ + 1) m_gap hm_gap
        -- m₁ = m₂ case
        · exact h_ne h_eq
        -- m₁ > m₂ case
        · -- m₁ > m₂: band m₁ above band m₂, but d > 0 so F increasing, contradiction
          have h_band_order' : m₂ + 1 - 1/r < m₁ + 1/r := by
            have h1 : m₂ + 1 ≤ m₁ := Int.add_one_le_of_lt h_gt
            have h2 : (m₂ + 1 : ℝ) ≤ m₁ := by exact_mod_cast h1
            linarith [hr]
          -- F(y₁) ∈ [m₁+1/r, m₁+1-1/r], F(y₂) ∈ [m₂+1/r, m₂+1-1/r]
          -- With m₁ > m₂, band m₁ has higher values.
          -- F(y₂) ≤ m₂ + 1 - 1/r < m₁ + 1/r ≤ F(y₁), so F(y₂) < F(y₁).
          -- But d > 0 and y₂ > y₁, so F(y₂) = d*y₂ > d*y₁ = F(y₁). Contradiction.
          have h1 : F y₂ ≤ m₂ + 1 - 1/r := hm₂.2
          have h2 : m₁ + 1/r ≤ F y₁ := hm₁.1
          have h3 : F y₂ < F y₁ := calc F y₂ ≤ m₂ + 1 - 1/r := h1
            _ < m₁ + 1/r := h_band_order'
            _ ≤ F y₁ := h2
          have h4 : F y₁ < F y₂ := by
            simp only [F]
            have h_pos_d : (d : ℝ) > 0 := hd_real_pos
            nlinarith
          linarith
      -- Use m₁ = m₂ and the bound on band width
      rw [h_m₁_eq_m₂] at hm₁
      have h_same_band := h_same_band_bound m₂ (d * y₁) (d * y₂) hm₁ hm₂
      have h_abs_diff : |d * y₁ - d * y₂| = d * y₂ - d * y₁ := by
        have h_diff_neg : d * y₁ - d * y₂ < 0 := by nlinarith
        rw [abs_of_neg h_diff_neg]; ring
      rw [h_abs_diff] at h_same_band
      linarith

-- Key lemma: A degree 1 lift with d = 1 that is a cohom must be a translation g(x) = c + x
-- This follows from the irrationality argument in the tex proof (lines 2325-2326)
-- The hypothesis only needs the lower bound: non-adjacent points map to non-adjacent points
private lemma degree_one_lift_is_translation
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (g : C(ℝ, ℝ)) (hd : ∀ x : ℝ, g (x + 1) = g x + 1)
    (hg_lower : ∀ x y : ℝ, 1/r < |y - x| → |y - x| < 1 - 1/r → 1/r ≤ |g y - g x|) :
    ∃ c : ℝ, ∀ x : ℝ, g x = c + x := by
  -- Define h(x) = g(x) - x. We'll show h is constant.
  let h : ℝ → ℝ := fun x => g x - x
  have h_cont : Continuous h := g.continuous.sub continuous_id
  -- h is 1-periodic: h(x + 1) = g(x + 1) - (x + 1) = g(x) + 1 - x - 1 = h(x)
  have h_periodic : ∀ x, h (x + 1) = h x := fun x => by simp only [h]; rw [hd x]; ring
  have hr_pos : 0 < r := by linarith
  -- Key step: h also has period 1/r.
  -- Proof outline:
  -- 1. r > 2 since r is irrational and r ≥ 2 (2 is rational)
  -- 2. For ε ∈ (0, 1-2/r), hg_lower gives |g(x+1/r+ε) - g(x)| ≥ 1/r
  -- 3. Taking ε→0 by continuity: |g(x+1/r) - g(x)| ≥ 1/r
  -- 4. So h(x+1/r) - h(x) = g(x+1/r) - g(x) - 1/r ∈ (-∞,-2/r] ∪ [0,∞)
  -- 5. By connectedness of ℝ, the continuous function x ↦ h(x+1/r)-h(x) has connected image,
  --    so it's either all ≤ -2/r or all ≥ 0
  -- 6. If all ≤ -2/r, then h(n/r) ≤ h(0) - 2n/r → -∞, contradicting boundedness of h
  -- 7. So h(x+1/r) - h(x) ≥ 0 for all x
  -- 8. By density of {n/r mod 1 : n ∈ ℤ} and continuity, h must be constant
  have h_period_inv_r : ∀ x, h (x + 1/r) = h x := by
    -- Step 1: r > 2 since r is irrational and r ≥ 2 (2 is rational)
    have hr_gt_2 : 2 < r := by
      rcases hr.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hirr
        exact Nat.not_irrational 2 hirr
    -- Step 2-3: |g(x + 1/r) - g(x)| ≥ 1/r for all x
    -- We use continuity: for ε > 0 small enough, |g(x + 1/r + ε) - g(x)| ≥ 1/r
    -- and taking ε → 0 we get |g(x + 1/r) - g(x)| ≥ 1/r
    have hg_gap : ∀ x, 1/r ≤ |g (x + 1/r) - g x| := by
      intro x
      -- Key: 1/r < 1 - 1/r when r > 2, so there's a gap to use hg_lower
      -- For ε ∈ (0, 1-2/r), hg_lower gives |g(x+1/r+ε) - g(x)| ≥ 1/r
      -- Taking ε → 0⁺ gives |g(x+1/r) - g(x)| ≥ 1/r by continuity
      -- The formal proof requires a limit argument with nhdsWithin
      -- The formal proof requires a limit argument with nhdsWithin
      have h2r_lt : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
      have h_gap : 0 < 1 - 2/r := by linarith
      have h1r_pos : 0 < 1/r := by positivity
      have h_one_r_lt : 1/r < 1 - 1/r := by
        have heq : 1/r + 1/r = 2/r := by ring
        linarith
      -- For any ε ∈ (0, 1-2/r), we have:
      -- |(x+1/r+ε) - x| = 1/r + ε ∈ (1/r, 1-1/r)
      -- so by hg_lower, |g(x+1/r+ε) - g(x)| ≥ 1/r
      have h_bound_for_eps : ∀ ε : ℝ, 0 < ε → ε < 1 - 2/r → 1/r ≤ |g (x + 1/r + ε) - g x| := by
        intro ε hε_pos hε_small
        apply hg_lower
        · rw [show x + 1/r + ε - x = 1/r + ε by ring, abs_of_pos (by linarith : 1/r + ε > 0)]
          linarith
        · rw [show x + 1/r + ε - x = 1/r + ε by ring, abs_of_pos (by linarith : 1/r + ε > 0)]
          have h1 : 1 - 2/r = 1 - 1/r - 1/r := by ring
          have h2 : 1/r + ε < 1/r + (1 - 2/r) := by linarith
          linarith [h1]
      -- By continuity of g, taking ε → 0 gives |g(x+1/r) - g(x)| ≥ 1/r
      by_contra h_neg
      push_neg at h_neg
      set gap := 1/r - |g (x + 1/r) - g x| with hgap_def
      have hgap_pos : 0 < gap := by simp only [hgap_def]; linarith
      obtain ⟨δ_cont, hδ_pos, hδ_cont⟩ := Metric.continuousAt_iff.mp
        g.continuous.continuousAt gap hgap_pos
      set ε := min δ_cont (1 - 2/r) / 2 with hε_def
      have hε_pos : 0 < ε := by simp only [hε_def]; positivity
      have hε_lt_δ : ε < δ_cont := by simp only [hε_def]; linarith [min_le_left δ_cont (1 - 2/r)]
      have hε_lt_bound : ε < 1 - 2/r := by
        simp only [hε_def]; linarith [min_le_right δ_cont (1 - 2/r)]
      have h_apply := h_bound_for_eps ε hε_pos hε_lt_bound
      have hdist : Dist.dist (x + 1/r + ε) (x + 1/r) < δ_cont := by
        rw [Real.dist_eq, show (x + 1/r + ε) - (x + 1/r) = ε by ring, abs_of_pos hε_pos]
        exact hε_lt_δ
      have hcont_app := hδ_cont hdist
      rw [Real.dist_eq] at hcont_app
      have htri : |g (x + 1/r + ε) - g x| ≤
          |g (x + 1/r + ε) - g (x + 1/r)| + |g (x + 1/r) - g x| := abs_sub_le _ _ _
      have h_final : |g (x + 1/r + ε) - g x| < 1/r := by
        calc |g (x + 1/r + ε) - g x|
            ≤ |g (x + 1/r + ε) - g (x + 1/r)| + |g (x + 1/r) - g x| := htri
          _ < gap + |g (x + 1/r) - g x| := by linarith
          _ = 1/r := by simp only [hgap_def]; ring
      linarith
    -- Step 4: h(x+1/r) - h(x) = g(x+1/r) - g(x) - 1/r, and |g(x+1/r) - g(x)| ≥ 1/r
    -- means h(x+1/r) - h(x) ∈ (-∞, -2/r] ∪ [0, ∞)
    -- Define δ(x) = h(x + 1/r) - h(x)
    let δ : ℝ → ℝ := fun x => h (x + 1/r) - h x
    have hδ_cont : Continuous δ := by
      refine Continuous.sub ?_ h_cont
      exact h_cont.comp (continuous_id.add continuous_const)
    have hδ_eq : ∀ x, δ x = g (x + 1/r) - g x - 1/r := fun x => by simp only [δ, h]; ring
    -- δ(x) ∈ (-∞, -2/r] ∪ [0, ∞)
    have hδ_range : ∀ x, δ x ≤ -2/r ∨ 0 ≤ δ x := by
      intro x
      have habs := hg_gap x
      -- habs: 1/r ≤ |g(x+1/r) - g(x)|
      -- This means g(x+1/r) - g(x) ≥ 1/r or g(x+1/r) - g(x) ≤ -1/r
      rw [hδ_eq]
      have h1r_pos : 0 < 1/r := by positivity
      have h_or : g (x + 1/r) - g x ≥ 1/r ∨ g (x + 1/r) - g x ≤ -(1/r) := by
        rw [le_abs] at habs
        rcases habs with h | h
        · left; exact h
        · right; linarith
      rcases h_or with hge' | hle'
      · right; linarith
      · left
        -- hle': g(x+1/r) - g(x) <= -(1/r)
        -- δ x = g(x+1/r) - g(x) - 1/r <= -(1/r) - 1/r = -2/r
        have heq1 : -(1/r) = -1/r := by ring
        have heq2 : -1/r - 1/r = -2/r := by ring
        linarith
    -- Step 5: By connectedness, δ is either all ≤ -2/r or all ≥ 0
    -- The image of ℝ under δ is connected (preconnected)
    have hδ_image_preconn : IsPreconnected (Set.range δ) := by
      rw [← Set.image_univ]
      exact isPreconnected_univ.image δ hδ_cont.continuousOn
    -- The image is contained in (-∞, -2/r] ∪ [0, ∞), a disjoint union
    -- By preconnectedness, it must be contained in one of them
    have hδ_cases : (∀ x, δ x ≤ -2/r) ∨ (∀ x, 0 ≤ δ x) := by
      -- The two sets are (-∞, -2/r] = Iic (-2/r) and [0, ∞) = Ici 0
      -- They are disjoint since -2/r < 0 (as r > 0)
      have h_neg_2r_neg : -2/r < 0 := by
        have h2r_pos : 0 < 2/r := by positivity
        have heq : -2/r = -(2/r) := by ring
        linarith
      have h_disj : Disjoint (Set.Iic (-2/r)) (Set.Ici (0 : ℝ)) := by
        rw [Set.disjoint_iff]
        intro y ⟨hy1, hy2⟩
        simp only [Set.mem_Iic] at hy1
        simp only [Set.mem_Ici] at hy2
        linarith
      -- range δ ⊆ Iic (-2/r) ∪ Ici 0
      have h_subset : Set.range δ ⊆ Set.Iic (-2/r) ∪ Set.Ici 0 := by
        intro y hy
        rcases hy with ⟨x, rfl⟩
        rcases hδ_range x with h | h
        · left; exact h
        · right; exact h
      -- Both sets are closed
      have h_closed_l : IsClosed (Set.Iic (-2/r)) := isClosed_Iic
      have h_closed_r : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
      -- By preconnectedness, range δ ⊆ one of them
      -- Use: if a preconnected set is contained in a disjoint union of closed sets,
      -- it's contained in one of them
      by_cases h_empty_l : (Set.range δ ∩ Set.Iic (-2/r)).Nonempty
      · -- range δ meets Iic (-2/r)
        by_cases h_empty_r : (Set.range δ ∩ Set.Ici 0).Nonempty
        · -- range δ meets both, contradiction with preconnectedness
          exfalso
          have h_cover : Set.range δ ⊆ Set.Iic (-2/r) ∪ Set.Ici 0 := h_subset
          -- Use isPreconnected_closed_iff
          rw [isPreconnected_closed_iff] at hδ_image_preconn
          have := hδ_image_preconn (Set.Iic (-2/r)) (Set.Ici 0) h_closed_l h_closed_r
            h_cover h_empty_l h_empty_r
          -- this says (range δ ∩ (Iic (-2/r) ∩ Ici 0)).Nonempty
          rcases this with ⟨y, hy_range, hy_l, hy_r⟩
          simp only [Set.mem_Iic] at hy_l
          simp only [Set.mem_Ici] at hy_r
          linarith
        · -- range δ only meets Iic (-2/r), so all ≤ -2/r
          left
          intro x
          have hx : δ x ∈ Set.range δ := Set.mem_range_self x
          rcases hδ_range x with h | h
          · exact h
          · exfalso
            apply h_empty_r
            exact ⟨δ x, hx, h⟩
      · -- range δ doesn't meet Iic (-2/r), so all ≥ 0
        right
        intro x
        have hx : δ x ∈ Set.range δ := Set.mem_range_self x
        rcases hδ_range x with h | h
        · exfalso
          apply h_empty_l
          exact ⟨δ x, hx, h⟩
        · exact h
    -- Step 6: Rule out the case δ x ≤ -2/r for all x
    -- If so, then h(n/r) = h(0) + sum of δ(k/r) for k = 0, ..., n-1
    -- and δ(k/r) ≤ -2/r, so h(n/r) ≤ h(0) - 2n/r → -∞
    -- But h is bounded (continuous and 1-periodic)
    have h_not_all_neg : ¬(∀ x, δ x ≤ -2/r) := by
      intro h_all_neg
      -- h is bounded because it's continuous and 1-periodic
      have h_periodic' : Function.Periodic h 1 := h_periodic
      have h_bdd : Bornology.IsBounded (Set.range h) :=
        h_periodic'.isBounded_of_continuous one_ne_zero h_cont
      -- Get a bound M such that |h(x)| ≤ M for all x
      rw [Metric.isBounded_range_iff] at h_bdd
      obtain ⟨C, hC⟩ := h_bdd
      -- For n ∈ ℕ, h(n/r) ≤ h(0) - 2n/r
      have h_descent : ∀ n : ℕ, h (n/r) ≤ h 0 - 2*n/r := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have key : h ((↑(n + 1))/r) = h ((n:ℝ)/r) + δ ((n:ℝ)/r) := by
            simp only [δ]
            have heq : (n : ℝ)/r + 1/r = (↑(n + 1))/r := by
              simp only [Nat.cast_add, Nat.cast_one]
              ring
            rw [← heq]
            ring
          rw [key]
          have hδ_neg := h_all_neg ((n:ℝ)/r)
          calc h ((n:ℝ)/r) + δ ((n:ℝ)/r) ≤ h ((n:ℝ)/r) + (-2/r) := by linarith
            _ ≤ (h 0 - 2*(n:ℝ)/r) + (-2/r) := by linarith
            _ = h 0 - 2*(↑(n + 1))/r := by simp only [Nat.cast_add, Nat.cast_one]; ring
      -- We need 2*n/r > C to contradict 2*n/r <= C
      have h_unbdd : ∃ n : ℕ, 2*(n:ℝ)/r > C := by
        use Nat.ceil (C * r / 2 + 1)
        have hceil : (Nat.ceil (C * r / 2 + 1) : ℝ) ≥ C * r / 2 + 1 := Nat.le_ceil _
        have step1 : 2 * (Nat.ceil (C * r / 2 + 1) : ℝ) ≥ 2 * (C * r / 2 + 1) := by linarith
        have step2 : 2 * (Nat.ceil (C * r / 2 + 1) : ℝ) / r ≥ 2 * (C * r / 2 + 1) / r := by
          apply div_le_div_of_nonneg_right step1 (le_of_lt hr_pos)
        have h2 : 2 * (C * r / 2 + 1) / r = C + 2/r := by field_simp
        rw [h2] at step2
        have h2r_pos : 0 < 2/r := by positivity
        linarith
      obtain ⟨n, hn⟩ := h_unbdd
      have h_contra := h_descent n
      have h_bd := hC 0 (n/r)
      rw [Real.dist_eq] at h_bd
      have h_abs : |h (n/r) - h 0| ≤ C := by rw [abs_sub_comm]; exact h_bd
      have h_lower : h (n/r) ≥ h 0 - C := by
        rw [abs_le] at h_abs
        linarith
      -- From h_contra: h(n/r) <= h 0 - 2*n/r
      -- From h_lower: h(n/r) >= h 0 - C
      -- So h 0 - C <= h 0 - 2*n/r, i.e., 2*n/r <= C
      -- But hn: 2*n/r > C, contradiction
      have h_chain : 2*(n:ℝ)/r ≤ C := by linarith
      linarith
    -- So we must have δ x ≥ 0 for all x
    rcases hδ_cases with h_all_neg | h_all_pos
    · exact absurd h_all_neg h_not_all_neg
    -- Step 7: Similarly, we need δ x ≤ 0 for all x
    -- We use a symmetric argument: define δ' x = h(x) - h(x+1/r) = -δ x
    -- The same analysis applies to δ', so either δ' ≤ -2/r or δ' ≥ 0
    -- If δ' ≤ -2/r, i.e., δ ≥ 2/r, then h(0) - h(n/r) ≤ -2n/r → -∞, contradiction
    -- So δ' ≥ 0, i.e., δ ≤ 0
    have h_all_nonpos : ∀ x, δ x ≤ 0 := by
      -- Define δ' x = -δ x = h x - h(x + 1/r)
      let δ' : ℝ → ℝ := fun x => -δ x
      have hδ'_cont : Continuous δ' := hδ_cont.neg
      -- δ'(x) = h x - h(x + 1/r) = -(g(x + 1/r) - g x - 1/r) = g x - g(x + 1/r) + 1/r
      have hδ'_eq : ∀ x, δ' x = g x - g (x + 1/r) + 1/r := fun x => by
        simp only [δ', δ, h]
        ring
      -- δ'(x) = -δ(x). We know δ(x) ∈ (-∞, -2/r] ∪ [0, ∞)
      -- So δ'(x) ∈ (-∞, 0] ∪ [2/r, ∞)
      have hδ'_range : ∀ x, δ' x ≤ 0 ∨ 2/r ≤ δ' x := by
        intro x
        have hδ_range_x := hδ_range x
        simp only [δ'] at *
        rcases hδ_range_x with hneg | hpos
        · -- δ x ≤ -2/r, so -δ x ≥ 2/r
          right
          have heq : -2/r = -(2/r) := by ring
          rw [heq] at hneg
          linarith
        · -- δ x ≥ 0, so -δ x ≤ 0
          left; linarith
      -- By connectedness argument, either δ' ≤ 0 for all x or δ' ≥ 2/r for all x
      have hδ'_image_preconn : IsPreconnected (Set.range δ') := by
        rw [← Set.image_univ]
        exact isPreconnected_univ.image δ' hδ'_cont.continuousOn
      have hδ'_cases : (∀ x, δ' x ≤ 0) ∨ (∀ x, 2/r ≤ δ' x) := by
        have h_2r_pos : 0 < 2/r := by positivity
        have h_subset : Set.range δ' ⊆ Set.Iic 0 ∪ Set.Ici (2/r) := by
          intro y hy
          rcases hy with ⟨x, rfl⟩
          rcases hδ'_range x with h | h
          · left; exact h
          · right; exact h
        have h_closed_l : IsClosed (Set.Iic (0 : ℝ)) := isClosed_Iic
        have h_closed_r : IsClosed (Set.Ici (2/r)) := isClosed_Ici
        by_cases h_empty_l : (Set.range δ' ∩ Set.Iic 0).Nonempty
        · by_cases h_empty_r : (Set.range δ' ∩ Set.Ici (2/r)).Nonempty
          · exfalso
            rw [isPreconnected_closed_iff] at hδ'_image_preconn
            have := hδ'_image_preconn (Set.Iic 0) (Set.Ici (2/r)) h_closed_l h_closed_r
              h_subset h_empty_l h_empty_r
            rcases this with ⟨y, _, hy_l, hy_r⟩
            simp only [Set.mem_Iic] at hy_l
            simp only [Set.mem_Ici] at hy_r
            linarith
          · left
            intro x
            rcases hδ'_range x with h | h
            · exact h
            · exfalso; apply h_empty_r; exact ⟨δ' x, Set.mem_range_self x, h⟩
        · right
          intro x
          rcases hδ'_range x with h | h
          · exfalso; apply h_empty_l; exact ⟨δ' x, Set.mem_range_self x, h⟩
          · exact h
      -- Rule out δ' ≥ 2/r using boundedness
      -- If δ' x ≥ 2/r for all x, then δ x ≤ -2/r for all x
      -- (same as before, h would go to -∞)
      have h_not_all_big : ¬(∀ x, 2/r ≤ δ' x) := by
        intro h_all_big
        have h_periodic' : Function.Periodic h 1 := h_periodic
        have h_bdd : Bornology.IsBounded (Set.range h) :=
          h_periodic'.isBounded_of_continuous one_ne_zero h_cont
        rw [Metric.isBounded_range_iff] at h_bdd
        obtain ⟨C, hC⟩ := h_bdd
        -- δ' x ≥ 2/r means -δ x ≥ 2/r, i.e., δ x ≤ -2/r
        -- So h(n/r) - h(0) = Σ δ(k/r) for k = 0..n-1 ≤ -2n/r
        have h_descent' : ∀ n : ℕ, h (n/r) ≤ h 0 - 2*n/r := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            have key : h ((↑(n + 1))/r) = h ((n:ℝ)/r) + δ ((n:ℝ)/r) := by
              simp only [δ]
              have heq : (n : ℝ)/r + 1/r = (↑(n + 1))/r := by
                simp only [Nat.cast_add, Nat.cast_one]
                ring
              rw [← heq]
              ring
            rw [key]
            have hδ_small : δ ((n:ℝ)/r) ≤ -2/r := by
              have hbig := h_all_big ((n:ℝ)/r)
              simp only [δ'] at hbig
              -- hbig: 2/r ≤ -δ(n/r), so δ(n/r) ≤ -(2/r) = -2/r
              have heq' : -(2/r) = -2/r := by ring
              linarith
            have heq : -2/r = -(2/r) := by ring
            calc h ((n:ℝ)/r) + δ ((n:ℝ)/r) ≤ h ((n:ℝ)/r) + (-(2/r)) := by rw [← heq]; linarith
              _ ≤ (h 0 - 2*(n:ℝ)/r) + (-(2/r)) := by linarith
              _ = h 0 - 2*(↑(n + 1))/r := by simp only [Nat.cast_add, Nat.cast_one]; ring
        -- We need 2*n/r > C to get h(n/r) < h 0 - C
        have h_unbdd : ∃ n : ℕ, 2*n/r > C := by
          use Nat.ceil (C * r / 2 + 1)
          have hceil : (Nat.ceil (C * r / 2 + 1) : ℝ) ≥ C * r / 2 + 1 := Nat.le_ceil _
          have h2 : 2 * (C * r / 2 + 1) / r = C + 2/r := by field_simp
          have step1 : 2 * (Nat.ceil (C * r / 2 + 1) : ℝ) ≥ 2 * (C * r / 2 + 1) := by linarith
          have step2 : 2 * (Nat.ceil (C * r / 2 + 1) : ℝ) / r ≥ 2 * (C * r / 2 + 1) / r := by
            apply div_le_div_of_nonneg_right step1 (le_of_lt hr_pos)
          rw [h2] at step2
          have h2r_pos : 0 < 2/r := by positivity
          linarith
        obtain ⟨n, hn⟩ := h_unbdd
        have h_desc := h_descent' n
        have h_bd := hC 0 (n/r)
        rw [Real.dist_eq] at h_bd
        have h_lower : h 0 - C ≤ h (n/r) := by
          rw [abs_le] at h_bd
          linarith
        -- From h_desc: h(n/r) ≤ h 0 - 2*n/r
        -- From h_lower: h 0 - C ≤ h(n/r)
        -- Chain: h 0 - C ≤ h(n/r) ≤ h 0 - 2*n/r
        -- So -C ≤ -2*n/r, i.e., 2*n/r ≤ C
        -- But hn says 2*n/r > C
        have h_ineq : h 0 - C ≤ h 0 - 2*(n:ℝ)/r := by
          calc h 0 - C ≤ h (n/r) := h_lower
            _ ≤ h 0 - 2*(n:ℝ)/r := h_desc
        have h_contra : 2*(n:ℝ)/r ≤ C := by linarith
        linarith
      rcases hδ'_cases with h_small | h_big
      · -- δ' x ≤ 0 for all x means δ x ≥ 0 for all x (consistent with h_all_pos)
        -- We need to show δ = 0 everywhere
        -- If δ(x₀) > 0 for some x₀, we show h is unbounded using density
        -- Key: δ is 1-periodic since h is 1-periodic
        have hδ_periodic : Function.Periodic δ 1 := by
          intro x
          simp only [δ]
          -- Need: h((x+1) + 1/r) - h(x+1) = h(x + 1/r) - h(x)
          have h1 : h ((x + 1) + 1/r) = h (x + 1/r + 1) := by ring_nf
          have h2 : h (x + 1/r + 1) = h (x + 1/r) := h_periodic (x + 1/r)
          have h3 : h (x + 1) = h x := h_periodic x
          rw [h1, h2, h3]
        by_contra h_not_zero
        push_neg at h_not_zero
        obtain ⟨x₀, hx₀_pos⟩ := h_not_zero
        -- h is bounded
        have h_periodic' : Function.Periodic h 1 := h_periodic
        have h_bdd : Bornology.IsBounded (Set.range h) :=
          h_periodic'.isBounded_of_continuous one_ne_zero h_cont
        rw [Metric.isBounded_range_iff] at h_bdd
        obtain ⟨C, hC⟩ := h_bdd
        -- δ is 1-periodic and continuous, so also bounded
        have hδ_periodic_fn : Function.Periodic δ 1 := hδ_periodic
        have hδ_bdd : Bornology.IsBounded (Set.range δ) :=
          hδ_periodic_fn.isBounded_of_continuous one_ne_zero hδ_cont
        -- By continuity at x₀, δ > δ(x₀)/2 in a neighborhood
        obtain ⟨η, hη_pos, hη_cont⟩ := Metric.continuousAt_iff.mp
          (hδ_cont.continuousAt (x := x₀)) (δ x₀ / 2) (by linarith)
        -- By density of {n/r mod 1 : n ∈ ℕ}, we can find arbitrarily many n
        -- such that n/r mod 1 is close to x₀ mod 1
        -- For such n, δ(x₀ + n/r) = δ(x₀ + (n/r mod 1)) (by periodicity) is close to δ(x₀)
        -- The sum h(x₀ + N/r) - h(x₀) = Σ δ(x₀ + k/r) accumulates these positive contributions
        -- Since {n/r mod 1} visits a neighborhood of x₀ mod 1 infinitely often,
        -- the sum grows without bound, contradicting boundedness of h
        -- Integral argument (Theorem 5.6):
        -- ∫₀¹ δ = 0 by periodicity of h, but δ ≥ 0 continuous with δ(x₀) > 0
        -- implies ∫₀¹ δ > 0. Contradiction.
        open MeasureTheory in
        -- The integral ∫₀¹ δ dx = 0 by the following argument:
        -- ∫₀¹ (g(x+1/r) - g(x)) dx = 1/r (using degree relation and change of variables)
        -- δ(x) = g(x+1/r) - g(x) - 1/r
        -- So ∫₀¹ δ dx = 1/r - 1/r = 0
        have hδ_int : IntervalIntegrable δ MeasureTheory.volume 0 1 :=
          hδ_cont.intervalIntegrable 0 1
        have h_delta_integral : ∫ x in (0:ℝ)..1, δ x = 0 := by
          -- The integral computation uses:
          -- 1. ∫₀¹ g(x+1/r) dx = ∫_{1/r}^{1+1/r} g(u) du by substitution
          -- 2. Split: ∫_{1/r}^{1+1/r} = ∫_{1/r}^1 + ∫_1^{1+1/r}
          -- 3. For ∫_1^{1+1/r}, substitute u = v+1: = ∫_0^{1/r} g(v+1) dv = ∫_0^{1/r} (g(v)+1) dv
          -- 4. Combine to get ∫₀¹ g(x+1/r) dx = ∫₀¹ g(x) dx + 1/r
          -- 5. So ∫₀¹ (g(x+1/r) - g(x)) dx = 1/r
          -- 6. Since δ(x) = g(x+1/r) - g(x) - 1/r, we have ∫₀¹ δ = 1/r - 1/r = 0
          -- First establish integrability of g over needed intervals
          have hg_cont : Continuous g := g.continuous
          have hg_int_01 : IntervalIntegrable (↑g) MeasureTheory.volume 0 1 :=
            hg_cont.intervalIntegrable 0 1
          have hg_int_all : ∀ a b, IntervalIntegrable (↑g) MeasureTheory.volume a b :=
            fun a b => hg_cont.intervalIntegrable a b
          have hr_inv_pos : 0 < 1/r := by positivity
          -- Key computation: ∫₀¹ g(x + 1/r) dx = ∫_{1/r}^{1+1/r} g dx (substitution)
          have h_subst : ∫ x in (0:ℝ)..1, g (x + 1/r) = ∫ x in (1/r:ℝ)..(1 + 1/r), g x := by
            simp only [intervalIntegral.integral_comp_add_right]
            ring_nf
          -- Split ∫_{1/r}^{1+1/r} g = ∫_{1/r}^1 g + ∫_1^{1+1/r} g
          have h_split : ∫ x in (1/r:ℝ)..(1 + 1/r), g x =
              (∫ x in (1/r:ℝ)..1, g x) + ∫ x in (1:ℝ)..(1 + 1/r), g x := by
            rw [intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _) (hg_int_all _ _)]
          -- For ∫_1^{1+1/r} g, use substitution u = x - 1 and degree relation
          have h_degree_int : ∫ x in (1:ℝ)..(1 + 1/r), g x = (∫ x in (0:ℝ)..(1/r), g x) + 1/r := by
            have h_sub : ∫ x in (1:ℝ)..(1 + 1/r), g x = ∫ x in (0:ℝ)..(1/r), g (x + 1) := by
              have key : ∫ x in (0:ℝ)..(1/r), g (x + 1) = ∫ x in (0+1:ℝ)..(1/r + 1), g x :=
                intervalIntegral.integral_comp_add_right (fun x => g x) 1
              simp only [zero_add] at key
              rw [key]
              (congr 1; ring)
            rw [h_sub]
            -- g(x + 1) = g(x) + 1, so ∫ g(x+1) = ∫ g(x) + ∫ 1 = ∫ g(x) + 1/r
            have h_eq : ∀ x, g (x + 1) = g x + 1 := hd
            calc ∫ x in (0:ℝ)..(1/r), g (x + 1)
                = ∫ x in (0:ℝ)..(1/r), (g x + 1) := by
                  apply intervalIntegral.integral_congr
                  intro x _; exact h_eq x
              _ = (∫ x in (0:ℝ)..(1/r), g x) + ∫ x in (0:ℝ)..(1/r), (1:ℝ) := by
                  rw [intervalIntegral.integral_add
                  (hg_int_all _ _)
                  (continuous_const.intervalIntegrable
                    _ _)]
              _ = (∫ x in (0:ℝ)..(1/r), g x) + 1/r := by
                  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
          -- Combine: ∫_{1/r}^{1+1/r} g = ∫_{1/r}^1 g + ∫_0^{1/r} g + 1/r = ∫_0^1 g + 1/r
          have h_combine : ∫ x in (1/r:ℝ)..(1 + 1/r), g x = (∫ x in (0:ℝ)..1, g x) + 1/r := by
            rw [h_split, h_degree_int]
            -- ∫_{1/r}^1 g + (∫_0^{1/r} g + 1/r)
            --   = (∫_0^{1/r} g + ∫_{1/r}^1 g) + 1/r
            --   = ∫_0^1 g + 1/r
            have h_adj :
                (∫ x in (0:ℝ)..(1/r), g x)
                  + ∫ x in (1/r:ℝ)..1, g x =
                ∫ x in (0:ℝ)..1, g x :=
              intervalIntegral.integral_add_adjacent_intervals
                (hg_int_all _ _) (hg_int_all _ _)
            linarith
          -- So ∫₀¹ g(x + 1/r) dx = ∫₀¹ g dx + 1/r
          have h_shift_eq : ∫ x in (0:ℝ)..1, g (x + 1/r) = (∫ x in (0:ℝ)..1, g x) + 1/r := by
            rw [h_subst, h_combine]
          -- Now compute ∫₀¹ δ
          -- δ(x) = g(x + 1/r) - g(x) - 1/r
          have h_δ_expand : ∫ x in (0:ℝ)..1, δ x =
              (∫ x in (0:ℝ)..1, g (x + 1/r)) - (∫ x in (0:ℝ)..1, g x) - 1/r := by
            have h_int_shift : IntervalIntegrable (fun x => g (x + 1/r)) MeasureTheory.volume 0 1 :=
              (hg_cont.comp (continuous_add_right (1/r))).intervalIntegrable 0 1
            calc ∫ x in (0:ℝ)..1, δ x
                = ∫ x in (0:ℝ)..1, (g (x + 1/r) - g x - 1/r) := by
                  apply intervalIntegral.integral_congr
                  intro x _; exact hδ_eq x
              _ = (∫ x in (0:ℝ)..1, (g (x + 1/r) - g x)) - 1/r := by
                  -- Rewrite integrand: (a - b) - c = (a - b) + (-c)
                  have h_eq : ∀ x,
                      (g (x + 1/r) - g x - 1/r : ℝ) =
                      (g (x + 1/r) - g x)
                        + (-(1/r)) := by
                    intro x; ring
                  rw [intervalIntegral.integral_congr (fun x _ => h_eq x)]
                  rw [intervalIntegral.integral_add (h_int_shift.sub hg_int_01)
                      (continuous_const.intervalIntegrable 0 1)]
                  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_neg]
                  ring
              _ = ((∫ x in (0:ℝ)..1, g (x + 1/r)) - ∫ x in (0:ℝ)..1, g x) - 1/r := by
                  rw [intervalIntegral.integral_sub h_int_shift hg_int_01]
          rw [h_δ_expand, h_shift_eq]
          ring
        -- Step 4: δ ≥ 0 continuous, ∫ δ = 0 implies δ = 0 a.e., hence everywhere
        -- If δ(x₀) > 0, then by continuity the support of δ contains a neighborhood
        -- which has positive measure, so ∫ δ > 0, contradiction
        -- The support of δ intersected with [0,1] has positive measure
        have h_support_pos : 0 < volume (Function.support δ ∩ Set.Ioc 0 1) := by
          -- Use periodicity to find a point in (0,1] where δ > 0
          -- Then by continuity there's a neighborhood of positive measure
          -- Find y in (0,1] with δ(y) > 0 using periodicity
          let y := Int.fract x₀
          have hy_in_Ico : y ∈ Set.Ico 0 1 := ⟨Int.fract_nonneg x₀, Int.fract_lt_one x₀⟩
          have hδ_y_pos : 0 < δ y := by
            -- δ(y) = δ(fract(x₀)) = δ(x₀ - floor(x₀)) = δ(x₀) by periodicity
            have h_eq : δ y = δ x₀ := by
              have : y = x₀ - ↑(Int.floor x₀) := Int.self_sub_floor x₀
              rw [this]
              have hper : δ (x₀ - ↑(Int.floor x₀)) = δ x₀ := by
                have key := hδ_periodic.sub_zsmul_eq (Int.floor x₀) (x := x₀)
                simp only [zsmul_one] at key
                exact key
              exact hper
            rw [h_eq]
            exact hx₀_pos
          -- y is in the support of δ
          have hy_support : y ∈ Function.support δ := by
            rw [Function.mem_support]
            linarith
          -- By continuity at y, there's an open ball where δ > 0
          have hy_cont : ContinuousAt δ y := hδ_cont.continuousAt
          obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.continuousAt_iff.mp hy_cont (δ y / 2) (by linarith)
          -- The ball B(y, ε) ∩ (0, 1) has positive measure
          -- Take a smaller interval contained in both the ball and (0, 1)
          have h_Ioo_pos : 0 < volume (Set.Ioo (max 0 (y - ε/2)) (min 1 (y + ε/2))) := by
            rw [Real.volume_Ioo]
            apply ENNReal.ofReal_pos.mpr
            have hy_pos : 0 ≤ y := hy_in_Ico.1
            have hy_lt : y < 1 := hy_in_Ico.2
            -- max 0 (y - ε/2) < min 1 (y + ε/2) because y ∈ [0,1) and ε > 0
            have h_lt : max 0 (y - ε/2) < min 1 (y + ε/2) := by
              calc max 0 (y - ε/2)
                  ≤ y := by simp only [max_le_iff]; constructor <;> linarith
                _ < min 1 (y + ε/2) := by simp only [lt_min_iff]; constructor <;> linarith
            linarith
          -- Every point in this interval has δ > 0
          have h_Ioo_support : Set.Ioo (max 0 (y - ε/2)) (min 1 (y + ε/2)) ⊆
              Function.support δ ∩ Set.Ioc 0 1 := by
            intro z hz
            have hz_close : Dist.dist z y < ε := by
              rw [Real.dist_eq]
              have h1_left : z > max 0 (y - ε/2) := hz.1
              have h1_right : z < min 1 (y + ε/2) := hz.2
              have h2_left : max 0 (y - ε/2) ≥ y - ε/2 := le_max_right _ _
              have h2_right : min 1 (y + ε/2) ≤ y + ε/2 := min_le_right _ _
              have h3_left : z > y - ε/2 := lt_of_le_of_lt h2_left h1_left
              have h3_right : z < y + ε/2 := lt_of_lt_of_le h1_right h2_right
              have h_diff_lower : z - y > -ε/2 := by linarith
              have h_diff_upper : z - y < ε/2 := by linarith
              have h_half_lt : ε/2 < ε := by linarith
              have h_neg_lt : -ε < -ε/2 := by linarith
              rw [abs_lt]
              exact ⟨by linarith, by linarith⟩
            have hδ_z_close : Dist.dist (δ z) (δ y) < δ y / 2 := hε_ball hz_close
            constructor
            · -- z ∈ support δ, i.e., δ z ≠ 0
              rw [Function.mem_support]
              have hδ_z_pos : δ z > δ y / 2 := by
                rw [Real.dist_eq, abs_sub_lt_iff] at hδ_z_close
                linarith
              linarith
            · -- z ∈ Ioc 0 1
              constructor
              · have h1 : 0 ≤ max 0 (y - ε/2) := le_max_left _ _
                have h2 : max 0 (y - ε/2) < z := hz.1
                linarith
              · have h1 : z < min 1 (y + ε/2) := hz.2
                have h2 : min 1 (y + ε/2) ≤ 1 := min_le_left _ _
                linarith
          exact lt_of_lt_of_le h_Ioo_pos (measure_mono h_Ioo_support)
        -- Now use: ∫ δ = 0, δ ≥ 0, but support ∩ Ioc 0 1 has positive measure
        -- This contradicts integral_eq_zero_iff_of_nonneg_ae
        have h_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 1 ∪ Set.Ioc 1 0)] δ := by
          apply Filter.Eventually.of_forall
          intro x
          exact h_all_pos x
        have h_int_eq_zero_iff := intervalIntegral.integral_eq_zero_iff_of_nonneg_ae h_nonneg hδ_int
        rw [h_delta_integral] at h_int_eq_zero_iff
        -- So δ = 0 a.e. on Ioc 0 1 ∪ Ioc 1 0 = Ioc 0 1
        have h_Ioc_empty : Set.Ioc (1:ℝ) 0 = ∅ := Set.Ioc_eq_empty (by linarith : ¬(1:ℝ) < 0)
        simp only [h_Ioc_empty, Set.union_empty] at h_int_eq_zero_iff h_nonneg
        have hδ_ae_zero : δ =ᵐ[volume.restrict (Set.Ioc 0 1)] 0 := h_int_eq_zero_iff.mp trivial
        -- But support δ ∩ Ioc 0 1 has positive measure, so δ ≠ 0 a.e.
        -- This gives the contradiction
        have h_contra : volume (Function.support δ ∩ Set.Ioc 0 1) = 0 := by
          -- If δ =ᵐ[μ.restrict S] 0, then μ.restrict S (support δ) = 0
          -- which means μ (support δ ∩ S) = 0
          -- Use measure_support_eq_zero_iff: μ f.support = 0 ↔ f =ᵐ[μ] 0
          have h_supp_zero : (volume.restrict (Set.Ioc 0 1)) (Function.support δ) = 0 := by
            rw [Measure.measure_support_eq_zero_iff (μ := volume.restrict (Set.Ioc 0 1))]
            exact hδ_ae_zero
          -- Use restrict_apply': μ.restrict s t = μ (t ∩ s) when s is measurable
          have h_meas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
          rw [MeasureTheory.Measure.restrict_apply' h_meas] at h_supp_zero
          exact h_supp_zero
        exact absurd h_contra (ne_of_gt h_support_pos)
      · exact absurd h_big h_not_all_big
    -- So δ x ≥ 0 and δ x ≤ 0, hence δ x = 0
    intro x
    have h1 := h_all_pos x
    have h2 := h_all_nonpos x
    linarith
  -- Now h has periods 1 and 1/r. Since r is irrational, ℤ + ℤ·(1/r) is dense.
  have h_dense_periods : Dense (AddSubgroup.closure {(1 : ℝ), 1/r} : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff]
    simp only [one_div, inv_inv]
    exact hirr
  -- Define the set of periods of h
  let periods : Set ℝ := {t | ∀ x, h (x + t) = h x}
  -- 1 and 1/r are periods
  have h1_period : (1 : ℝ) ∈ periods := fun x => h_periodic x
  have h_inv_r_period : (1/r : ℝ) ∈ periods := fun x => h_period_inv_r x
  -- periods is a subgroup
  have periods_zero : (0 : ℝ) ∈ periods := fun x => by simp
  have periods_add : ∀ s t, s ∈ periods → t ∈ periods → s + t ∈ periods := by
    intro s t hs ht x
    calc h (x + (s + t)) = h ((x + s) + t) := by ring_nf
      _ = h (x + s) := ht (x + s)
      _ = h x := hs x
  have periods_neg : ∀ s, s ∈ periods → -s ∈ periods := by
    intro s hs x
    have key : h ((x + (-s)) + s) = h (x + (-s)) := hs (x + (-s))
    simp only [neg_add_cancel_right] at key
    exact key.symm
  -- periods contains AddSubgroup.closure {1, 1/r}
  have h_subgroup_periods : (AddSubgroup.closure {(1 : ℝ), 1/r} : Set ℝ) ⊆ periods := by
    intro t ht
    refine AddSubgroup.closure_induction (p := fun s _ => s ∈ periods) ?_ periods_zero ?_ ?_ ht
    · intro s hs
      rcases hs with rfl | rfl
      · exact h1_period
      · exact h_inv_r_period
    · intro s₁ s₂ _ _ hs₁ hs₂; exact periods_add s₁ s₂ hs₁ hs₂
    · intro s _ hs; exact periods_neg s hs
  -- h is constant: continuous + constant on dense set of translates
  have h_const : ∃ c, ∀ x, h x = c := by
    use h 0
    intro x
    have hx_in : x ∈ closure (AddSubgroup.closure {(1 : ℝ), 1/r} : Set ℝ) :=
      h_dense_periods.closure_eq ▸ trivial
    rw [mem_closure_iff_seq_limit] at hx_in
    obtain ⟨seq, hseq_mem, hseq_lim⟩ := hx_in
    have hseq_val : ∀ n, h (seq n) = h 0 := fun n => by
      have hmem : seq n ∈ periods := h_subgroup_periods (hseq_mem n)
      have := hmem 0
      simp only [zero_add] at this; exact this
    have hlim : Filter.Tendsto (fun n => h (seq n)) Filter.atTop (nhds (h x)) :=
      h_cont.tendsto x |>.comp hseq_lim
    have hlim' : Filter.Tendsto (fun n => h (seq n)) Filter.atTop (nhds (h 0)) := by
      simp only [hseq_val]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hlim'
  obtain ⟨c, hc⟩ := h_const
  exact ⟨c, fun x => by have := hc x; simp only [h] at this; linarith⟩

-- Key lemma: A degree -1 lift that is a cohom must be a translation composed with negation
-- Proof is symmetric to degree_one_lift_is_translation with h(x) = g(x) + x instead of g(x) - x
private lemma degree_neg_one_lift_is_reflection
    (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (g : C(ℝ, ℝ)) (hd : ∀ x : ℝ, g (x + 1) = g x - 1)
    (hg_lower : ∀ x y : ℝ, 1/r < |y - x| → |y - x| < 1 - 1/r → 1/r ≤ |g y - g x|) :
    ∃ c : ℝ, ∀ x : ℝ, g x = c - x := by
  -- Define h(x) = g(x) + x. We'll show h is constant.
  let h : ℝ → ℝ := fun x => g x + x
  have h_cont : Continuous h := g.continuous.add continuous_id
  -- h is 1-periodic: h(x + 1) = g(x + 1) + (x + 1) = g(x) - 1 + x + 1 = h(x)
  have h_periodic : ∀ x, h (x + 1) = h x := fun x => by simp only [h]; rw [hd x]; ring
  have hr_pos : 0 < r := by linarith
  -- Key step: h also has period 1/r (same argument as degree_one case)
  have h_period_inv_r : ∀ x, h (x + 1/r) = h x := by
    -- Same proof outline as degree_one_lift_is_translation but with sign flips
    -- Since r > 2 (from hr and irrationality), 1/r < 1 - 1/r
    have hr_gt_2 : 2 < r := by
      rcases (eq_or_lt_of_le hr) with rfl | h
      · exact absurd (Irrational.ne_int hirr 2) (by norm_num : ¬((2:ℝ) ≠ ↑(2:ℤ)))
      · exact h
    -- The gap bound gives |g(x + 1/r) - g(x)| ≥ 1/r via limit
    have hg_gap : ∀ x, 1/r ≤ |g (x + 1/r) - g x| := by
      intro x
      -- Key: 1/r < 1 - 1/r when r > 2, so there's a gap to use hg_lower
      -- For ε ∈ (0, 1-2/r), hg_lower gives |g(x+1/r+ε) - g(x)| ≥ 1/r
      -- Taking ε → 0⁺ gives |g(x+1/r) - g(x)| ≥ 1/r by continuity
      have h2r_lt : 2/r < 1 := by rw [div_lt_one hr_pos]; exact hr_gt_2
      have h_gap : 0 < 1 - 2/r := by linarith
      have h1r_pos : 0 < 1/r := by positivity
      have h_one_r_lt : 1/r < 1 - 1/r := by
        have heq : 1/r + 1/r = 2/r := by ring
        linarith
      -- For any ε ∈ (0, 1-2/r), we have:
      -- |(x+1/r+ε) - x| = 1/r + ε ∈ (1/r, 1-1/r)
      -- so by hg_lower, |g(x+1/r+ε) - g(x)| ≥ 1/r
      have h_bound_for_eps : ∀ ε : ℝ, 0 < ε → ε < 1 - 2/r → 1/r ≤ |g (x + 1/r + ε) - g x| := by
        intro ε hε_pos hε_small
        apply hg_lower
        · rw [show x + 1/r + ε - x = 1/r + ε by ring, abs_of_pos (by linarith : 1/r + ε > 0)]
          linarith
        · rw [show x + 1/r + ε - x = 1/r + ε by ring, abs_of_pos (by linarith : 1/r + ε > 0)]
          have h1 : 1 - 2/r = 1 - 1/r - 1/r := by ring
          have h2 : 1/r + ε < 1/r + (1 - 2/r) := by linarith
          linarith [h1]
      -- By continuity of g, taking ε → 0 gives |g(x+1/r) - g(x)| ≥ 1/r
      by_contra h_neg
      push_neg at h_neg
      set gap := 1/r - |g (x + 1/r) - g x| with hgap_def
      have hgap_pos : 0 < gap := by simp only [hgap_def]; linarith
      obtain ⟨δ_cont, hδ_pos, hδ_cont⟩ := Metric.continuousAt_iff.mp
        g.continuous.continuousAt gap hgap_pos
      set ε := min δ_cont (1 - 2/r) / 2 with hε_def
      have hε_pos : 0 < ε := by simp only [hε_def]; positivity
      have hε_lt_δ : ε < δ_cont := by simp only [hε_def]; linarith [min_le_left δ_cont (1 - 2/r)]
      have hε_lt_bound : ε < 1 - 2/r := by
        simp only [hε_def]; linarith [min_le_right δ_cont (1 - 2/r)]
      have h_apply := h_bound_for_eps ε hε_pos hε_lt_bound
      have hdist : Dist.dist (x + 1/r + ε) (x + 1/r) < δ_cont := by
        rw [Real.dist_eq, show (x + 1/r + ε) - (x + 1/r) = ε by ring, abs_of_pos hε_pos]
        exact hε_lt_δ
      have hclose := hδ_cont hdist
      rw [Real.dist_eq] at hclose
      have h_at_eps : |g (x + 1/r + ε) - g x| ≥ 1/r := h_apply
      have h_triangle : |g (x + 1/r + ε) - g x| ≤
          |g (x + 1/r + ε) - g (x + 1/r)| + |g (x + 1/r) - g x| := by
        have h_decomp :
            g (x + 1/r + ε) - g x =
            (g (x + 1/r + ε) - g (x + 1/r))
              + (g (x + 1/r) - g x) := by ring
        rw [h_decomp]
        simp only [abs_add_le]
      have h_bound : |g (x + 1/r + ε) - g (x + 1/r)| < gap := hclose
      have h_final : 1/r ≤ |g (x + 1/r + ε) - g (x + 1/r)| + |g (x + 1/r) - g x| :=
        h_at_eps.trans h_triangle
      simp only [hgap_def] at h_bound
      linarith
    -- Define δ(x) = h(x + 1/r) - h(x) = g(x + 1/r) - g(x) + 1/r
    let δ : ℝ → ℝ := fun x => h (x + 1/r) - h x
    have hδ_cont : Continuous δ := by
      apply Continuous.sub
      · exact h_cont.comp (continuous_add_right (1/r))
      · exact h_cont
    have hδ_eq : ∀ x, δ x = g (x + 1/r) - g x + 1/r := by
      intro x; simp only [δ, h]; ring
    -- The constraint: |g(x + 1/r) - g(x)| ≥ 1/r means g(x+1/r) - g(x) ≤ -1/r or ≥ 1/r
    -- So δ = g(x+1/r) - g(x) + 1/r satisfies δ ≤ 0 or δ ≥ 2/r
    have hδ_range : ∀ x, δ x ≤ 0 ∨ 2/r ≤ δ x := by
      intro x
      have habs := hg_gap x
      -- habs : 1/r ≤ |g(x+1/r) - g(x)|
      -- This means g(x+1/r) - g(x) ≤ -1/r or g(x+1/r) - g(x) ≥ 1/r
      have hδ_x : δ x = g (x + 1/r) - g x + 1/r := hδ_eq x
      by_cases hdiff : g (x + 1/r) - g x ≤ 0
      · -- diff ≤ 0, so |diff| = -diff ≥ 1/r, hence diff ≤ -1/r
        left
        have h1 : |g (x + 1/r) - g x| = -(g (x + 1/r) - g x) := abs_of_nonpos hdiff
        rw [h1] at habs
        -- habs : 1/r ≤ -(g (x + 1/r) - g x), i.e., g (x + 1/r) - g x ≤ -1/r
        simp only [neg_sub] at habs
        -- Now habs : 1/r ≤ g x - g (x + 1/r)
        -- So g (x + 1/r) ≤ g x - 1/r, i.e., g (x + 1/r) - g x ≤ -1/r
        -- δ x = g(x+1/r) - g(x) + 1/r ≤ -1/r + 1/r = 0
        have hδ_bound : δ x ≤ 0 := by
          rw [hδ_x]
          linarith
        exact hδ_bound
      · -- diff > 0, so |diff| = diff ≥ 1/r
        push_neg at hdiff
        right
        have h1 : |g (x + 1/r) - g x| = g (x + 1/r) - g x := abs_of_pos hdiff
        rw [h1] at habs
        -- habs : 1/r ≤ g(x+1/r) - g(x)
        -- So δ x = g(x+1/r) - g(x) + 1/r ≥ 1/r + 1/r = 2/r
        calc δ x = g (x + 1/r) - g x + 1/r := hδ_x
          _ ≥ 1/r + 1/r := by linarith
          _ = 2/r := by ring
    -- By connectedness of ℝ, range of δ is connected
    have hδ_image_preconn : IsPreconnected (Set.range δ) :=
      isPreconnected_range hδ_cont
    -- If δ ≤ 0 for all x, we're in the "all small" case (will show δ = 0)
    -- If δ ≥ 2/r for all x, we're in the "all big" case (leads to contradiction)
    -- By connectedness, one of these must hold (range can't hit both (−∞, 0] and [2/r, ∞))
    by_cases h_all_nonpos : ∀ x, δ x ≤ 0
    · -- Case: δ x ≤ 0 for all x. We show δ = 0 using the same integral argument.
      by_cases h_all_nonneg : ∀ x, 0 ≤ δ x
      · -- If δ ≤ 0 and δ ≥ 0, then δ = 0
        intro x; have h1 := h_all_nonpos x; have h2 := h_all_nonneg x; linarith
      · -- There exists x₀ with δ(x₀) < 0
        push_neg at h_all_nonneg
        obtain ⟨x₀, hx₀_neg⟩ := h_all_nonneg
        -- δ is 1-periodic
        have hδ_periodic : Function.Periodic δ 1 := by
          intro x; simp only [δ]
          have h1 : h ((x + 1) + 1/r) = h (x + 1/r + 1) := by ring_nf
          have h2 : h (x + 1/r + 1) = h (x + 1/r) := h_periodic (x + 1/r)
          have h3 : h (x + 1) = h x := h_periodic x
          rw [h1, h2, h3]
        -- Use integral argument: ∫₀¹ δ = 0 (by degree relation), but δ ≤ 0 with δ(x₀) < 0
        -- leads to contradiction
        open MeasureTheory in
        have hδ_int : IntervalIntegrable δ MeasureTheory.volume 0 1 :=
          hδ_cont.intervalIntegrable 0 1
        have h_delta_integral : ∫ x in (0:ℝ)..1, δ x = 0 := by
          -- For degree -1: g(x+1) = g(x) - 1
          -- ∫₀¹ g(x+1/r) dx = ∫_{1/r}^{1+1/r} g dx (substitution)
          -- = ∫_{1/r}^1 g + ∫_1^{1+1/r} g
          -- = ∫_{1/r}^1 g + ∫_0^{1/r} g(u+1) du = ∫_{1/r}^1 g + ∫_0^{1/r} (g(u) - 1) du
          -- = ∫_{1/r}^1 g + ∫_0^{1/r} g - 1/r = ∫₀¹ g - 1/r
          -- So ∫₀¹ (g(x+1/r) - g(x)) dx = -1/r
          -- δ(x) = g(x+1/r) - g(x) + 1/r, so ∫₀¹ δ = -1/r + 1/r = 0
          have hg_cont : Continuous g := g.continuous
          have hg_int_all : ∀ a b, IntervalIntegrable (↑g) MeasureTheory.volume a b :=
            fun a b => hg_cont.intervalIntegrable a b
          have h_subst : ∫ x in (0:ℝ)..1, g (x + 1/r) = ∫ x in (1/r:ℝ)..(1 + 1/r), g x := by
            simp only [intervalIntegral.integral_comp_add_right]; ring_nf
          have h_split : ∫ x in (1/r:ℝ)..(1 + 1/r), g x =
              (∫ x in (1/r:ℝ)..1, g x) + ∫ x in (1:ℝ)..(1 + 1/r), g x := by
            rw [intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _) (hg_int_all _ _)]
          have h_degree_int : ∫ x in (1:ℝ)..(1 + 1/r), g x = (∫ x in (0:ℝ)..(1/r), g x) - 1/r := by
            have h_sub : ∫ x in (1:ℝ)..(1 + 1/r), g x = ∫ x in (0:ℝ)..(1/r), g (x + 1) := by
              have key : ∫ x in (0:ℝ)..(1/r), g (x + 1) = ∫ x in (0+1:ℝ)..(1/r + 1), g x :=
                intervalIntegral.integral_comp_add_right (fun x => g x) 1
              simp only [zero_add] at key
              rw [key]
              (congr 1; ring)
            rw [h_sub]
            have h_eq : ∀ x, g (x + 1) = g x - 1 := hd
            calc ∫ x in (0:ℝ)..(1/r), g (x + 1)
                = ∫ x in (0:ℝ)..(1/r), (g x - 1) := by
                  apply intervalIntegral.integral_congr; intro x _; exact h_eq x
              _ = (∫ x in (0:ℝ)..(1/r), g x) - ∫ x in (0:ℝ)..(1/r), (1:ℝ) := by
                  rw [intervalIntegral.integral_sub (hg_int_all _ _)
                    (continuous_const.intervalIntegrable _ _)]
              _ = (∫ x in (0:ℝ)..(1/r), g x) - 1/r := by
                  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
          have h_combine : ∫ x in (1/r:ℝ)..(1 + 1/r), g x = (∫ x in (0:ℝ)..1, g x) - 1/r := by
            rw [h_split, h_degree_int]
            have h_adj :
                (∫ x in (0:ℝ)..(1/r), g x)
                  + ∫ x in (1/r:ℝ)..1, g x =
                ∫ x in (0:ℝ)..1, g x :=
              intervalIntegral.integral_add_adjacent_intervals
                (hg_int_all _ _) (hg_int_all _ _)
            linarith
          have h_shift_eq : ∫ x in (0:ℝ)..1, g (x + 1/r) = (∫ x in (0:ℝ)..1, g x) - 1/r := by
            rw [h_subst, h_combine]
          have hg_int_01 : IntervalIntegrable (↑g) MeasureTheory.volume 0 1 :=
            hg_cont.intervalIntegrable 0 1
          have h_int_shift : IntervalIntegrable (fun x => g (x + 1/r)) MeasureTheory.volume 0 1 :=
            (hg_cont.comp (continuous_add_right (1/r))).intervalIntegrable 0 1
          calc ∫ x in (0:ℝ)..1, δ x
              = ∫ x in (0:ℝ)..1, (g (x + 1/r) - g x + 1/r) := by
                apply intervalIntegral.integral_congr; intro x _; exact hδ_eq x
            _ = (∫ x in (0:ℝ)..1, (g (x + 1/r) - g x)) + (∫ x in (0:ℝ)..1, (1/r : ℝ)) := by
                simp only [
                  intervalIntegral.integral_add
                    (h_int_shift.sub hg_int_01)
                    (continuous_const.intervalIntegrable
                      0 1)]
            _ = (∫ x in (0:ℝ)..1, (g (x + 1/r) - g x)) + 1/r := by
                simp only [intervalIntegral.integral_const]
                norm_num
            _ = ((∫ x in (0:ℝ)..1, g (x + 1/r)) - ∫ x in (0:ℝ)..1, g x) + 1/r := by
                rw [intervalIntegral.integral_sub h_int_shift hg_int_01]
            _ = 0 := by
                rw [h_shift_eq]
                ring
            _ = 0 := by ring
        -- δ ≤ 0 everywhere, ∫ δ = 0, so δ = 0 a.e.
        -- But δ(x₀) < 0 and continuous, so support has positive measure: contradiction
        have h_support_pos : 0 < volume (Function.support δ ∩ Set.Ioc 0 1) := by
          let y := Int.fract x₀
          have hy_in_Ico : y ∈ Set.Ico 0 1 := ⟨Int.fract_nonneg x₀, Int.fract_lt_one x₀⟩
          have hδ_y_neg : δ y < 0 := by
            have h_eq : δ y = δ x₀ := by
              have : y = x₀ - ↑(Int.floor x₀) := Int.self_sub_floor x₀
              rw [this]
              have hper : δ (x₀ - ↑(Int.floor x₀)) = δ x₀ := by
                have : δ (x₀ - ↑(Int.floor x₀) • 1) =
                    δ x₀ :=
                  hδ_periodic.sub_zsmul_eq (Int.floor x₀)
                simp only [zsmul_one] at this
                exact this
              exact hper
            rw [h_eq]; exact hx₀_neg
          have hy_support : y ∈ Function.support δ := by
            rw [Function.mem_support]; linarith
          have hy_cont : ContinuousAt δ y := hδ_cont.continuousAt
          obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.continuousAt_iff.mp hy_cont (-δ y / 2) (by linarith)
          have h_Ioo_pos : 0 < volume (Set.Ioo (max 0 (y - ε/2)) (min 1 (y + ε/2))) := by
            rw [Real.volume_Ioo]; apply ENNReal.ofReal_pos.mpr
            have hy_pos : 0 ≤ y := hy_in_Ico.1
            have hy_lt : y < 1 := hy_in_Ico.2
            have h_le : max 0 (y - ε/2) ≤ y := by simp [hy_pos]; linarith
            have h_lt : y < min 1 (y + ε/2) := by simp [hy_lt]; linarith
            linarith
          have h_Ioo_support : Set.Ioo (max 0 (y - ε/2)) (min 1 (y + ε/2)) ⊆
              Function.support δ ∩ Set.Ioc 0 1 := by
            intro z hz
            have hz_close : Dist.dist z y < ε := by
              rw [Real.dist_eq, abs_sub_lt_iff]
              have h1 : max 0 (y - ε/2) < z := hz.1
              have h2 : z < min 1 (y + ε/2) := hz.2
              have h3 : max 0 (y - ε/2) ≥ y - ε/2 := le_max_right _ _
              have h4 : z > y - ε/2 := lt_of_le_of_lt h3 h1
              have h5 : z - y > -ε/2 := by linarith
              have h6 : (-ε : ℝ) < -ε/2 := by nlinarith [hε_pos]
              have h7 : min 1 (y + ε/2) ≤ y + ε/2 := min_le_right _ _
              have h8 : z < y + ε/2 := lt_of_lt_of_le h2 h7
              have h9 : z - y < ε/2 := by linarith
              have h10 : (ε/2 : ℝ) < ε := by nlinarith [hε_pos]
              constructor
              · linarith [h5, h6]
              · linarith [h9, h10]
            have hδ_z_close : Dist.dist (δ z) (δ y) < -δ y / 2 := hε_ball hz_close
            constructor
            · rw [Function.mem_support]
              have hδ_z_neg : δ z < δ y / 2 := by
                rw [Real.dist_eq, abs_sub_lt_iff] at hδ_z_close; linarith
              linarith
            · constructor
              · have h1 : max 0 (y - ε/2) < z := hz.1
                have h2 : 0 ≤ max 0 (y - ε/2) := le_max_left _ _
                linarith
              · have h1 : z < min 1 (y + ε/2) := hz.2
                have h2 : min 1 (y + ε/2) ≤ 1 := min_le_left _ _
                linarith
          exact lt_of_lt_of_le h_Ioo_pos (measure_mono h_Ioo_support)
        -- Now derive contradiction
        have h_nonpos : δ ≤ᵐ[volume.restrict (Set.Ioc 0 1 ∪ Set.Ioc 1 0)] 0 := by
          apply Filter.Eventually.of_forall; intro x; exact h_all_nonpos x
        -- Negate δ to get nonneg function
        have h_neg_delta_integral : ∫ x in (0:ℝ)..1, (-δ) x = 0 := by
          simp only [Pi.neg_apply]
          rw [intervalIntegral.integral_neg, h_delta_integral, neg_zero]
        have h_neg_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 1 ∪ Set.Ioc 1 0)] (-δ) := by
          apply Filter.Eventually.of_forall
          intro x
          simp only [Pi.zero_apply, Pi.neg_apply,
            Left.nonneg_neg_iff]
          exact h_all_nonpos x
        have h_neg_int :
            IntervalIntegrable (-δ) MeasureTheory.volume
              0 1 :=
          hδ_int.neg
        have h_int_eq_zero_iff :=
          intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
            h_neg_nonneg h_neg_int
        rw [h_neg_delta_integral] at h_int_eq_zero_iff
        have h_Ioc_empty : Set.Ioc (1:ℝ) 0 = ∅ := Set.Ioc_eq_empty (by linarith : ¬(1:ℝ) < 0)
        simp only [h_Ioc_empty, Set.union_empty] at h_int_eq_zero_iff h_neg_nonneg
        have hδ_neg_ae_zero :
            (-δ) =ᵐ[volume.restrict (Set.Ioc 0 1)]
              0 :=
          h_int_eq_zero_iff.mp trivial
        have hδ_ae_zero : δ =ᵐ[volume.restrict (Set.Ioc 0 1)] 0 := by
          filter_upwards [hδ_neg_ae_zero] with x hx
          simp only [Pi.neg_apply, Pi.zero_apply] at hx
          have : -δ x = 0 := hx
          have : δ x = 0 := by linarith
          exact this
        have h_contra : volume (Function.support δ ∩ Set.Ioc 0 1) = 0 := by
          have h_supp_zero : (volume.restrict (Set.Ioc 0 1)) (Function.support δ) = 0 := by
            rw [Measure.measure_support_eq_zero_iff (μ := volume.restrict (Set.Ioc 0 1))]
            exact hδ_ae_zero
          have h_meas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
          rw [MeasureTheory.Measure.restrict_apply' h_meas] at h_supp_zero
          exact h_supp_zero
        exact absurd h_contra (ne_of_gt h_support_pos)
    · -- Case: not all δ ≤ 0, so some δ ≥ 2/r
      -- By connectedness, if range hits both (−∞, 0] and [2/r, ∞), it must contain [0, 2/r]
      -- But hδ_range says δ ≤ 0 or δ ≥ 2/r (disjoint), so this is impossible
      -- Hence δ ≥ 2/r for all x
      push_neg at h_all_nonpos
      obtain ⟨x₁, hx₁_pos⟩ := h_all_nonpos
      have h_all_big : ∀ x, 2/r ≤ δ x := by
        intro x
        rcases hδ_range x with h | h
        · -- δ x ≤ 0, but we also have x₁ with δ x₁ > 0, so δ x₁ ≥ 2/r
          rcases hδ_range x₁ with h₁ | h₁
          · linarith
          · -- Range contains a point ≤ 0 and a point ≥ 2/r
            -- By connectedness, range contains [0, 2/r], including 1/r
            have h_connected := hδ_image_preconn
            have h_mem_δx : δ x ∈ Set.range δ := ⟨x, rfl⟩
            have h_mem_δx₁ : δ x₁ ∈ Set.range δ := ⟨x₁, rfl⟩
            have h_mid : (1:ℝ)/r ∈ Set.Icc (δ x) (δ x₁) := by
              constructor
              · -- Need: δ x ≤ 1/r, we have h : δ x ≤ 0 and 0 < 1/r
                have h_pos : 0 < 1/r := one_div_pos.mpr hr_pos
                linarith
              · -- Need: 1/r ≤ δ x₁, we have h₁ : 2/r ≤ δ x₁
                have h_lt : 1/r < 2/r := by
                  have : (1:ℝ) < 2 := one_lt_two
                  exact div_lt_div_of_pos_right this hr_pos
                linarith
            have h_in_range : (1:ℝ)/r ∈ Set.range δ := by
              have h_ord : (Set.range δ).OrdConnected :=
                isPreconnected_iff_ordConnected.mp h_connected
              exact h_ord.out h_mem_δx h_mem_δx₁ h_mid
            obtain ⟨y, hy⟩ := h_in_range
            rcases hδ_range y with hy_case | hy_case
            · -- hy : δ y = 1/r, hy_case : δ y ≤ 0, but 1/r > 0, contradiction
              have h_pos : 0 < 1/r := one_div_pos.mpr hr_pos
              linarith
            · -- hy : δ y = 1/r, hy_case : 2/r ≤ δ y, so 2/r ≤ 1/r, but r > 2, contradiction
              have h_lt : 1/r < 2/r := by
                have : (1:ℝ) < 2 := one_lt_two
                exact div_lt_div_of_pos_right this hr_pos
              linarith
        · exact h
      -- But if δ ≥ 2/r > 0 everywhere, then ∫ δ > 0, contradicting ∫ δ = 0
      have hδ_int : IntervalIntegrable δ MeasureTheory.volume 0 1 :=
        hδ_cont.intervalIntegrable 0 1
      have hg_cont : Continuous g := g.continuous
      have hg_int_all : ∀ a b, IntervalIntegrable (↑g) MeasureTheory.volume a b :=
        fun a b => hg_cont.intervalIntegrable a b
      have h_delta_integral : ∫ x in (0:ℝ)..1, δ x = 0 := by
        have h_subst : ∫ x in (0:ℝ)..1, g (x + 1/r) = ∫ x in (1/r:ℝ)..(1 + 1/r), g x := by
          simp only [intervalIntegral.integral_comp_add_right]; ring_nf
        have h_split : ∫ x in (1/r:ℝ)..(1 + 1/r), g x =
            (∫ x in (1/r:ℝ)..1, g x) + ∫ x in (1:ℝ)..(1 + 1/r), g x := by
          rw [intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _) (hg_int_all _ _)]
        have h_degree_int : ∫ x in (1:ℝ)..(1 + 1/r), g x = (∫ x in (0:ℝ)..(1/r), g x) - 1/r := by
          have h_sub : ∫ x in (1:ℝ)..(1 + 1/r), g x = ∫ x in (0:ℝ)..(1/r), g (x + 1) := by
            have key : ∫ x in (0:ℝ)..(1/r), g (x + 1) = ∫ x in (0+1:ℝ)..(1/r + 1), g x :=
              intervalIntegral.integral_comp_add_right (fun x => g x) 1
            simp only [zero_add] at key
            rw [key]
            (congr 1; ring)
          rw [h_sub]
          have h_eq : ∀ x, g (x + 1) = g x - 1 := hd
          calc ∫ x in (0:ℝ)..(1/r), g (x + 1)
              = ∫ x in (0:ℝ)..(1/r), (g x - 1) := by
                apply intervalIntegral.integral_congr; intro x _; exact h_eq x
            _ = (∫ x in (0:ℝ)..(1/r), g x) - ∫ x in (0:ℝ)..(1/r), (1:ℝ) := by
                rw [intervalIntegral.integral_sub (hg_int_all _ _)
                  (continuous_const.intervalIntegrable _ _)]
            _ = (∫ x in (0:ℝ)..(1/r), g x) - 1/r := by
                simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
        have h_combine : ∫ x in (1/r:ℝ)..(1 + 1/r), g x = (∫ x in (0:ℝ)..1, g x) - 1/r := by
          rw [h_split, h_degree_int]
          have h_adj : (∫ x in (0:ℝ)..(1/r), g x) + ∫ x in (1/r:ℝ)..1, g x = ∫ x in (0:ℝ)..1, g x :=
            intervalIntegral.integral_add_adjacent_intervals (hg_int_all _ _) (hg_int_all _ _)
          linarith
        have h_shift_eq : ∫ x in (0:ℝ)..1, g (x + 1/r) = (∫ x in (0:ℝ)..1, g x) - 1/r := by
          rw [h_subst, h_combine]
        have hg_int_01 : IntervalIntegrable (↑g) MeasureTheory.volume 0 1 :=
          hg_cont.intervalIntegrable 0 1
        have h_int_shift : IntervalIntegrable (fun x => g (x + 1/r)) MeasureTheory.volume 0 1 :=
          (hg_cont.comp (continuous_add_right (1/r))).intervalIntegrable 0 1
        calc ∫ x in (0:ℝ)..1, δ x
            = ∫ x in (0:ℝ)..1, (g (x + 1/r) - g x + 1/r) := by
              apply intervalIntegral.integral_congr; intro x _; exact hδ_eq x
          _ = (∫ x in (0:ℝ)..1, (g (x + 1/r) - g x)) + 1/r := by
              -- The integrand is (g (x + 1/r) - g x) + 1/r = (diff) + const
              -- Split using integral_add: ∫ (f + g) = ∫ f + ∫ g
              have h_add : ∫ x in (0:ℝ)..1, ((g (x + 1/r) - g x) + (1/r : ℝ)) =
                  (∫ x in (0:ℝ)..1, (g (x + 1/r) - g x)) + ∫ x in (0:ℝ)..1, (1/r : ℝ) :=
                intervalIntegral.integral_add (h_int_shift.sub hg_int_01)
                  (continuous_const.intervalIntegrable 0 1)
              simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h_add
              exact h_add
          _ = ((∫ x in (0:ℝ)..1, g (x + 1/r)) - ∫ x in (0:ℝ)..1, g x) + 1/r := by
              rw [intervalIntegral.integral_sub h_int_shift hg_int_01]
          _ = (((∫ x in (0:ℝ)..1, g x) - 1/r) - ∫ x in (0:ℝ)..1, g x) + 1/r := by
              rw [h_shift_eq]
          _ = 0 := by ring
      -- But ∫ δ = 0 and δ ≥ 2/r > 0, so ∫ δ ≥ 2/r > 0, contradiction
      have h_int_pos : 0 < ∫ x in (0:ℝ)..1, δ x := by
        have h_all_pos : ∀ x, 0 < δ x := fun x => by
          have := h_all_big x
          have h2r_pos : 0 < 2/r := by positivity
          linarith
        exact
          intervalIntegral.intervalIntegral_pos_of_pos
            hδ_int h_all_pos
            (by linarith : (0:ℝ) < 1)
      linarith
  have h_dense_periods : Dense (AddSubgroup.closure {(1 : ℝ), 1/r} : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff]
    simp only [one_div, inv_inv]
    exact hirr
  let periods : Set ℝ := {t | ∀ x, h (x + t) = h x}
  have h1_period : (1 : ℝ) ∈ periods := fun x => h_periodic x
  have h_inv_r_period : (1/r : ℝ) ∈ periods := fun x => h_period_inv_r x
  have periods_zero : (0 : ℝ) ∈ periods := fun x => by simp
  have periods_add : ∀ s t, s ∈ periods → t ∈ periods → s + t ∈ periods := by
    intro s t hs ht x
    calc h (x + (s + t)) = h ((x + s) + t) := by ring_nf
      _ = h (x + s) := ht (x + s)
      _ = h x := hs x
  have periods_neg : ∀ s, s ∈ periods → -s ∈ periods := by
    intro s hs x
    have key : h ((x + (-s)) + s) = h (x + (-s)) := hs (x + (-s))
    simp only [neg_add_cancel_right] at key
    exact key.symm
  have h_subgroup_periods : (AddSubgroup.closure {(1 : ℝ), 1/r} : Set ℝ) ⊆ periods := by
    intro t ht
    refine AddSubgroup.closure_induction (p := fun s _ => s ∈ periods) ?mem ?zero ?add ?neg ht
    case mem =>
      intro s hs
      rcases hs with rfl | rfl
      · exact h1_period
      · exact h_inv_r_period
    case zero => exact periods_zero
    case add => intro s₁ s₂ _ _ hs₁ hs₂; exact periods_add s₁ s₂ hs₁ hs₂
    case neg => intro s _ hs; exact periods_neg s hs
  have h_const : ∃ c, ∀ x, h x = c := by
    use h 0
    intro x
    have hx_in : x ∈ closure (AddSubgroup.closure {(1 : ℝ), 1/r} : Set ℝ) :=
      h_dense_periods.closure_eq ▸ trivial
    rw [mem_closure_iff_seq_limit] at hx_in
    obtain ⟨seq, hseq_mem, hseq_lim⟩ := hx_in
    have hseq_val : ∀ n, h (seq n) = h 0 := fun n => by
      have hmem : seq n ∈ periods := h_subgroup_periods (hseq_mem n)
      have := hmem 0
      simp only [zero_add] at this; exact this
    have hlim : Filter.Tendsto (fun n => h (seq n)) Filter.atTop (nhds (h x)) :=
      h_cont.tendsto x |>.comp hseq_lim
    have hlim' : Filter.Tendsto (fun n => h (seq n)) Filter.atTop (nhds (h 0)) := by
      simp only [hseq_val]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hlim'
  obtain ⟨c, hc⟩ := h_const
  exact ⟨c, fun x => by have := hc x; simp only [h] at this; linarith⟩

theorem circleGraph_selfCohom_form (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (f : Circle → Circle)
    (hf : IsCohom (circleGraphOpen r hr) (circleGraphOpen r hr) f ∨
          IsCohom (circleGraphClosed r hr) (circleGraphClosed r hr) f) :
    -- f is a rotation or a rotation composed with reflection
    ∃ (a : Circle) (sgn : Bool),
      if sgn then ∀ x, f x = a + x else ∀ x, f x = a - x := by
  -- Step 1: f is continuous by Lemma 5.5
  have hcont : Continuous f := circleGraph_selfCohom_continuous r hr hirr f hf
  -- Step 2: Lift f to g : ℝ → ℝ via the covering map
  obtain ⟨g, hg_lifts⟩ := exists_lift_of_continuous f hcont
  -- Step 3: g satisfies g(x+1) = g(x) + d for some degree d
  obtain ⟨d, hd⟩ := lift_satisfies_degree f hcont g hg_lifts
  -- Step 4: The cohom property implies |d| = 1
  rcases degree_one_of_cohom r hr hirr f hcont g hg_lifts d hd hf with hd1 | hd_neg1
  · -- Case d = 1: f is a rotation
    -- Step 5a: g(x) = c + x for some c
    -- The lower bound follows from the cohom property
    have hg_lower : ∀ x y : ℝ, 1/r < |y - x| → |y - x| < 1 - 1/r → 1/r ≤ |g y - g x| := by
      intro x y hxy_lower hxy_upper
      -- From the bounds on |y - x|, circleProj x and circleProj y are non-adjacent
      have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
      have hxy_lt_1 : |y - x| < 1 := by
        calc |y - x| < 1 - 1/r := hxy_upper
          _ ≤ 1 - 0 := by linarith [one_div_pos.mpr hr_pos]
          _ = 1 := by ring
      have hne : circleProj x ≠ circleProj y := by
        intro heq
        have heq' : (QuotientAddGroup.mk x : Circle) = QuotientAddGroup.mk y := heq
        rw [circleProj_eq_iff_diff_int] at heq'
        obtain ⟨n, hn⟩ := heq'
        rcases eq_or_ne n 0 with h0 | hne_n
        · -- n = 0, so x - y = 0, contradicting |y - x| > 1/r > 0
          simp only [h0, Int.cast_zero] at hn
          have habs0 : |y - x| = 0 := by simp [abs_sub_comm, hn]
          have hpos : 0 < 1 / r := by positivity
          linarith
        · -- n ≠ 0, so |x - y| = |n| ≥ 1, contradicting |y - x| < 1
          have hn_abs : |y - x| = |(n : ℝ)| := by
            have hyx : y - x = -(n : ℝ) := by linarith
            rw [hyx, abs_neg]
          have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
            rw [← Int.cast_abs]
            exact_mod_cast Int.one_le_abs hne_n
          linarith
      -- Circle distance ≥ 1/r means non-adjacent in the open graph
      -- Note: (y - x : AddCircle 1) = ↑y - ↑x since the quotient map is a group hom
      have h_norm_xy : ‖((y : AddCircle (1 : ℝ)) - x)‖ ≥ 1 / r := by
        rw [← AddCircle.coe_sub]
        have h := addCircle_norm_ge_iff_bounds (y - x) hxy_lt_1 r hr
        rw [h]
        constructor <;> linarith
      have h_dist_xy : circleDistance (circleProj x) (circleProj y) ≥ 1 / r := by
        have h := circleDistance_of_proj x y
        rw [h]
        have heq_norm : ‖(x - y : AddCircle (1 : ℝ))‖ = ‖(y - x : AddCircle (1 : ℝ))‖ := by
          have : (x - y : AddCircle (1 : ℝ)) = -(y - x : AddCircle (1 : ℝ)) := by
            simp [sub_eq_add_neg]
          rw [this, norm_neg]
        rw [heq_norm]
        exact h_norm_xy
      -- Non-adjacent in the graph
      have hnonadj : ¬(circleGraphOpen r hr).Adj (circleProj x) (circleProj y) := by
        simp only [circleGraphOpen]
        intro ⟨_, hdist⟩
        linarith
      -- By cohom property, f(circleProj x) and f(circleProj y) are non-adjacent
      rcases hf with hf_open | hf_closed
      · -- Open case
        have hcohom := hf_open (circleProj x) (circleProj y) hne hnonadj
        have h_dist_fg : circleDistance (f (circleProj x)) (f (circleProj y)) ≥ 1 / r := by
          have ⟨_, hnadj'⟩ := hcohom
          simp only [circleGraphOpen] at hnadj'
          push_neg at hnadj'
          exact hnadj' hcohom.1
        -- Using hg_lifts: f(circleProj x) = circleProj(g x)
        have heq_x : f (circleProj x) = circleProj (g x) := by
          have h := congr_fun hg_lifts x
          simp only [Function.comp_apply] at h
          exact h.symm
        have heq_y : f (circleProj y) = circleProj (g y) := by
          have h := congr_fun hg_lifts y
          simp only [Function.comp_apply] at h
          exact h.symm
        rw [heq_x, heq_y, circleDistance_of_proj] at h_dist_fg
        have h_ge := abs_ge_of_addCircle_norm_ge (g x - g y) r hr h_dist_fg
        rw [abs_sub_comm] at h_ge
        exact h_ge
      · -- Closed case: we have strict inequality for non-adjacency
        -- Use the strict bound lemma: 1/r < |y - x| < 1 - 1/r implies ‖·‖ > 1/r
        have h_norm_xy_strict : ‖(y - x : AddCircle (1 : ℝ))‖ > 1 / r :=
          addCircle_norm_gt_of_strict_bounds (y - x) r hr hxy_lower hxy_upper
        have h_dist_xy_strict : circleDistance (circleProj x) (circleProj y) > 1 / r := by
          have h := circleDistance_of_proj x y
          rw [h]
          have heq_norm : ‖(x - y : AddCircle (1 : ℝ))‖ = ‖(y - x : AddCircle (1 : ℝ))‖ := by
            have : (x - y : AddCircle (1 : ℝ)) = -(y - x : AddCircle (1 : ℝ)) := by
              simp [sub_eq_add_neg]
            rw [this, norm_neg]
          rw [heq_norm]
          exact h_norm_xy_strict
        -- First show non-adjacent in closed graph (requires circleDistance > 1/r)
        have hnonadj_closed : ¬(circleGraphClosed r hr).Adj (circleProj x) (circleProj y) := by
          simp only [circleGraphClosed]
          intro ⟨_, hdist⟩
          linarith
        have hcohom := hf_closed (circleProj x) (circleProj y) hne hnonadj_closed
        have h_dist_fg : circleDistance (f (circleProj x)) (f (circleProj y)) > 1 / r := by
          have ⟨_, hnadj'⟩ := hcohom
          simp only [circleGraphClosed] at hnadj'
          push_neg at hnadj'
          exact hnadj' hcohom.1
        have heq_x : f (circleProj x) = circleProj (g x) := by
          have h := congr_fun hg_lifts x
          simp only [Function.comp_apply] at h
          exact h.symm
        have heq_y : f (circleProj y) = circleProj (g y) := by
          have h := congr_fun hg_lifts y
          simp only [Function.comp_apply] at h
          exact h.symm
        rw [heq_x, heq_y, circleDistance_of_proj] at h_dist_fg
        have h_ge := abs_ge_of_addCircle_norm_ge (g x - g y) r hr (le_of_lt h_dist_fg)
        rw [abs_sub_comm] at h_ge
        exact h_ge
    have hd' : ∀ x : ℝ, g (x + 1) = g x + 1 := by
      intro x
      have := hd x
      simp only [hd1, Int.cast_one] at this
      exact this
    obtain ⟨c, hc⟩ := degree_one_lift_is_translation r hr hirr g hd' hg_lower
    -- Step 6a: f(x) = [c] + x where [c] = circleProj c
    use (circleProj c), true
    simp only [↓reduceIte]
    intro x
    -- For any x' : ℝ with circleProj x' = x, we have f(x) = circleProj(g(x')) = circleProj(c + x')
    -- = circleProj(c) + circleProj(x') = [c] + x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    -- Note: circleProj = QuotientAddGroup.mk = ⟦·⟧ by definition
    have hx'_proj : circleProj x' = x := hx'
    calc f x = f (circleProj x') := by rw [hx'_proj]
      _ = circleProj (g x') := by
          have h := congr_fun hg_lifts x'
          simp only [Function.comp_apply] at h
          exact h.symm
      _ = circleProj (c + x') := by rw [hc]
      _ = circleProj c + circleProj x' := AddCircle.coe_add 1 c x'
      _ = circleProj c + x := by rw [hx'_proj]
  · -- Case d = -1: f is a reflection
    -- The lower bound follows from the cohom property (same as d = 1 case)
    have hg_lower : ∀ x y : ℝ, 1/r < |y - x| → |y - x| < 1 - 1/r → 1/r ≤ |g y - g x| := by
      intro x y hxy_lower hxy_upper
      have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
      have hxy_lt_1 : |y - x| < 1 := by
        calc |y - x| < 1 - 1/r := hxy_upper
          _ ≤ 1 - 0 := by linarith [one_div_pos.mpr hr_pos]
          _ = 1 := by ring
      have hne : circleProj x ≠ circleProj y := by
        intro heq
        have heq' : (QuotientAddGroup.mk x : Circle) = QuotientAddGroup.mk y := heq
        rw [circleProj_eq_iff_diff_int] at heq'
        obtain ⟨n, hn⟩ := heq'
        rcases eq_or_ne n 0 with h0 | hne_n
        · simp only [h0, Int.cast_zero] at hn
          have habs0 : |y - x| = 0 := by simp [abs_sub_comm, hn]
          have hpos : 0 < 1 / r := by positivity
          linarith
        · have hn_abs : |y - x| = |(n : ℝ)| := by
            have hyx : y - x = -(n : ℝ) := by linarith
            rw [hyx, abs_neg]
          have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
            rw [← Int.cast_abs]
            exact_mod_cast Int.one_le_abs hne_n
          linarith
      have h_norm_xy : ‖((y : AddCircle (1 : ℝ)) - x)‖ ≥ 1 / r := by
        rw [← AddCircle.coe_sub]
        have h := addCircle_norm_ge_iff_bounds (y - x) hxy_lt_1 r hr
        rw [h]
        constructor <;> linarith
      have h_dist_xy : circleDistance (circleProj x) (circleProj y) ≥ 1 / r := by
        have h := circleDistance_of_proj x y
        rw [h]
        have heq_norm : ‖(x - y : AddCircle (1 : ℝ))‖ = ‖(y - x : AddCircle (1 : ℝ))‖ := by
          have : (x - y : AddCircle (1 : ℝ)) = -(y - x : AddCircle (1 : ℝ)) := by
            simp [sub_eq_add_neg]
          rw [this, norm_neg]
        -- h_norm_xy has type ‖↑y - ↑x‖ ≥ 1/r = ‖((y : AddCircle 1) - x)‖ ≥ 1/r
        -- We need ‖(x - y : AddCircle 1)‖ ≥ 1/r = ‖↑x - ↑y‖ ≥ 1/r
        -- These are equal by heq_norm
        rw [heq_norm]
        convert h_norm_xy using 1
      have hnonadj : ¬(circleGraphOpen r hr).Adj (circleProj x) (circleProj y) := by
        simp only [circleGraphOpen]
        intro ⟨_, hdist⟩
        linarith
      rcases hf with hf_open | hf_closed
      · have hcohom := hf_open (circleProj x) (circleProj y) hne hnonadj
        have h_dist_fg : circleDistance (f (circleProj x)) (f (circleProj y)) ≥ 1 / r := by
          have ⟨_, hnadj'⟩ := hcohom
          simp only [circleGraphOpen] at hnadj'
          push_neg at hnadj'
          exact hnadj' hcohom.1
        have heq_x : f (circleProj x) = circleProj (g x) := by
          have h := congr_fun hg_lifts x
          simp only [Function.comp_apply] at h
          exact h.symm
        have heq_y : f (circleProj y) = circleProj (g y) := by
          have h := congr_fun hg_lifts y
          simp only [Function.comp_apply] at h
          exact h.symm
        rw [heq_x, heq_y, circleDistance_of_proj] at h_dist_fg
        have h_ge := abs_ge_of_addCircle_norm_ge (g x - g y) r hr h_dist_fg
        rw [abs_sub_comm] at h_ge
        exact h_ge
      · have h_norm_xy_strict : ‖(y - x : AddCircle (1 : ℝ))‖ > 1 / r :=
          addCircle_norm_gt_of_strict_bounds (y - x) r hr hxy_lower hxy_upper
        have h_dist_xy_strict : circleDistance (circleProj x) (circleProj y) > 1 / r := by
          have h := circleDistance_of_proj x y
          rw [h]
          have heq_norm : ‖(x - y : AddCircle (1 : ℝ))‖ = ‖(y - x : AddCircle (1 : ℝ))‖ := by
            have : (x - y : AddCircle (1 : ℝ)) = -(y - x : AddCircle (1 : ℝ)) := by
              simp [sub_eq_add_neg]
            rw [this, norm_neg]
          rw [heq_norm]
          exact h_norm_xy_strict
        have hnonadj_closed : ¬(circleGraphClosed r hr).Adj (circleProj x) (circleProj y) := by
          simp only [circleGraphClosed]
          intro ⟨_, hdist⟩
          linarith
        have hcohom := hf_closed (circleProj x) (circleProj y) hne hnonadj_closed
        have h_dist_fg : circleDistance (f (circleProj x)) (f (circleProj y)) > 1 / r := by
          have ⟨_, hnadj'⟩ := hcohom
          simp only [circleGraphClosed] at hnadj'
          push_neg at hnadj'
          exact hnadj' hcohom.1
        have heq_x : f (circleProj x) = circleProj (g x) := by
          have h := congr_fun hg_lifts x
          simp only [Function.comp_apply] at h
          exact h.symm
        have heq_y : f (circleProj y) = circleProj (g y) := by
          have h := congr_fun hg_lifts y
          simp only [Function.comp_apply] at h
          exact h.symm
        rw [heq_x, heq_y, circleDistance_of_proj] at h_dist_fg
        have h_ge := abs_ge_of_addCircle_norm_ge (g x - g y) r hr (le_of_lt h_dist_fg)
        rw [abs_sub_comm] at h_ge
        exact h_ge
    have hd_eq : ∀ x : ℝ, g (x + 1) = g x - 1 := by
      intro x
      have := hd x
      simp only [hd_neg1, Int.cast_neg, Int.cast_one] at this
      linarith
    obtain ⟨c, hc⟩ := degree_neg_one_lift_is_reflection r hr hirr g hd_eq hg_lower
    use (circleProj c), false
    simp only [Bool.false_eq_true, ↓reduceIte]
    intro x
    -- For any x' : ℝ with circleProj x' = x, we have f(x) = circleProj(g(x')) = circleProj(c - x')
    -- = circleProj(c) - circleProj(x') = [c] - x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    have hx'_proj : circleProj x' = x := hx'
    calc f x = f (circleProj x') := by rw [hx'_proj]
      _ = circleProj (g x') := by
          have h := congr_fun hg_lifts x'
          simp only [Function.comp_apply] at h
          exact h.symm
      _ = circleProj (c - x') := by rw [hc]
      _ = circleProj c - circleProj x' := AddCircle.coe_sub 1 c x'
      _ = circleProj c - x := by rw [hx'_proj]

/-! ### Non-Equivalence of Open and Closed Circle Graphs -/

/-- **Theorem 5.7**: For rational p/q > 2, E_{p/q}^c and E_{p/q}^o are not equivalent.

    Proof: Suppose E_{p/q}^o ≤ E_{p/q}^c via some cohomomorphism f.
    Since E_{p/q} ≃ E_{p/q}^o, we get a cohomomorphism E_{p/q} → E_{p/q}^c.
    The image is finite, so by Lemma 4.3 it's ≤ E_{a/b}^o for some a/b < p/q.
    Thus E_{p/q} ≤ E_{a/b}, contradicting the ordering of fraction graphs. -/
theorem circleGraph_not_equiv_rational (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q < p) -- Note: strict inequality for p/q > 2
    (hr : 2 ≤ (p : ℝ) / q) :
    ¬(Cohom (circleGraphOpen ((p : ℝ)/q) hr)
               (circleGraphClosed ((p : ℝ)/q) hr)) := by
  classical
  intro hcohom
  have h2q_le : 2 * q ≤ p := le_of_lt h2q
  have hfrac_equiv :
      Cohom (circleGraphOpen ((p : ℝ) / q) hr) (fractionGraph p q) ∧
        Cohom (fractionGraph p q) (circleGraphOpen ((p : ℝ) / q) hr) := by
    simpa using (circleGraphOpen_equiv_fractionGraph p q hq h2q_le)
  have hfrac_to_closed :
      Cohom (fractionGraph p q) (circleGraphClosed ((p : ℝ) / q) hr) :=
    Cohom.trans hfrac_equiv.2 hcohom
  rcases hfrac_to_closed with ⟨f, hf⟩
  let S : Finset Circle := Finset.univ.image f
  have hS_nonempty : S.Nonempty := by
    refine ⟨f 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hS_mem : ∀ v, f v ∈ (S : Set Circle) := by
    intro v
    change f v ∈ S
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hfrac_to_induced :
      Cohom (fractionGraph p q)
        ((circleGraphClosed ((p : ℝ) / q) hr).induce (S : Set Circle)) := by
    refine ⟨_, isCohom_corestrict f hf (S : Set Circle) hS_mem⟩
  have hr_lt : 2 < (p : ℝ) / q := by
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have h2q_lt' : (2 : ℝ) * q < p := by exact_mod_cast h2q
    simpa [mul_comm] using (lt_div_iff₀ hq_pos).2 h2q_lt'
  rcases circleGraphClosed_finite_subgraph ((p : ℝ) / q) hr_lt S hS_nonempty with
    ⟨a, b, ha, hb, h2b, hab, hcohom_S_to_open⟩
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp ha⟩
  have hs : 2 ≤ (a : ℝ) / b := by
    have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    calc (2 : ℝ) = 2 * b / b := by field_simp
      _ ≤ a / b := by
        apply div_le_div_of_nonneg_right (by exact_mod_cast h2b) (le_of_lt hb')
  have hcohom_S_to_open' :
      Cohom ((circleGraphClosed ((p : ℝ) / q) hr).induce (S : Set Circle))
        (circleGraphOpen ((a : ℝ) / b) hs) := by
    simpa [hs] using hcohom_S_to_open
  have hfrac_to_open :
      Cohom (fractionGraph p q) (circleGraphOpen ((a : ℝ) / b) hs) :=
    Cohom.trans hfrac_to_induced hcohom_S_to_open'
  have hopen_to_frac :
      Cohom (circleGraphOpen ((a : ℝ) / b) hs) (fractionGraph a b) := by
    have h_equiv_ab :
        Cohom (circleGraphOpen ((a : ℝ) / b) hs) (fractionGraph a b) ∧
          Cohom (fractionGraph a b) (circleGraphOpen ((a : ℝ) / b) hs) := by
      simpa using (circleGraphOpen_equiv_fractionGraph a b hb h2b)
    exact h_equiv_ab.1
  have hfrac_to_frac : Cohom (fractionGraph p q) (fractionGraph a b) :=
    Cohom.trans hfrac_to_open hopen_to_frac
  have hrat_le : (p : ℚ) / q ≤ (a : ℚ) / b :=
    fractionGraph_ordering_reverse p q a b hq hb h2q_le h2b hfrac_to_frac
  have hreal_le : (p : ℝ) / q ≤ (a : ℝ) / b := by
    have h' : ((p : ℚ) / q : ℝ) ≤ ((a : ℚ) / b : ℝ) := by
      simpa using (Rat.cast_le (K := ℝ)).2 hrat_le
    simpa using h'
  exact (not_lt_of_ge hreal_le) hab

/-- **Theorem 5.8**: For irrational r > 2, E_r^c and E_r^o are not equivalent.

    Proof: Suppose f : E_r^o → E_r^c is a cohomomorphism.
    Then f is also a cohomomorphism E_r^o → E_r^o (since E_r^c ≤ E_r^o).
    By Theorem 5.6, f is a rotation (± reflection).
    But rotations are distance-preserving.
    Points at distance exactly 1/r exist in E_r^o (not adjacent).
    Their images are also at distance 1/r.
    But in E_r^c, distance ≤ 1/r means adjacent, contradiction. -/
theorem circleGraph_not_equiv_irrational (r : ℝ) (hr : 2 < r) (hirr : Irrational r) :
    ¬(Cohom (circleGraphOpen r (le_of_lt hr))
               (circleGraphClosed r (le_of_lt hr))) := by
  classical
  intro hcohom
  rcases hcohom with ⟨f, hf⟩
  have hclosed_open :
      IsCohom (circleGraphClosed r (le_of_lt hr)) (circleGraphOpen r (le_of_lt hr)) id := by
    intro u v huv hnadj
    constructor
    · exact huv
    · intro hadj_open
      obtain ⟨_, hdist_open⟩ := hadj_open
      simp only [id_eq] at hdist_open
      simp only [circleGraphClosed, ne_eq] at hnadj
      push_neg at hnadj
      have hd_gt : 1 / r < circleDistance u v := hnadj huv
      linarith
  have hf_open_open :
      IsCohom (circleGraphOpen r (le_of_lt hr)) (circleGraphOpen r (le_of_lt hr)) f := by
    simpa using (IsCohom.comp hf hclosed_open)
  have hform :=
    circleGraph_selfCohom_form r (le_of_lt hr) hirr f (Or.inl hf_open_open)
  rcases hform with ⟨a, sgn, hform⟩
  let u : Circle := 0
  let v : Circle := (1 / r : ℝ)
  have hirr_inv : Irrational (1 / r) := by
    simpa [one_div] using (Irrational.inv hirr)
  have huv : u ≠ v := by
    intro h
    have hzero : ((1 / r : ℝ) : Circle) = 0 := by
      simpa [u, v] using h.symm
    have h' : ∃ n : ℤ, (n : ℝ) = 1 / r := by
      rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := 1 / r)).1 hzero with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa using hn
    rcases h' with ⟨n, hn⟩
    exact (hirr_inv.ne_int n) (by simpa [hn])
  have hdist_uv : circleDistance u v = 1 / r := by
    have hr_pos : 0 < r := lt_trans (by norm_num) hr
    have hpos : 0 < (1 / r) := one_div_pos.mpr hr_pos
    have hlt : (1 / r) < (1 / 2 : ℝ) := by
      have h2_pos : (0 : ℝ) < 2 := by norm_num
      simpa using (one_div_lt_one_div_of_lt h2_pos hr)
    have hle_half : |1 / r| ≤ (1 : ℝ) / 2 := by
      have hle : (1 / r) ≤ (1 / 2 : ℝ) := le_of_lt hlt
      have hle' : (1 / |r|) ≤ (1 / 2 : ℝ) := by
        simpa [abs_of_pos hr_pos] using hle
      simpa [abs_one_div] using hle'
    have hle_half' : |1 / r| ≤ |(1 : ℝ)| / 2 := by
      simpa using hle_half
    have hnorm : ‖((1 / r : ℝ) : Circle)‖ = |1 / r| := by
      simpa using (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := 1 / r)
        (hp := by norm_num)).2 hle_half'
    have hdist : circleDistance (0 : Circle) ((1 / r : ℝ) : Circle) =
        ‖((1 / r : ℝ) : Circle)‖ := by
      simp [circleDistance, dist_eq_norm, sub_eq_add_neg]
    calc
      circleDistance u v = ‖((1 / r : ℝ) : Circle)‖ := by simpa [u, v] using hdist
      _ = |1 / r| := hnorm
      _ = 1 / r := abs_of_pos hpos
  have hnonadj_open : ¬(circleGraphOpen r (le_of_lt hr)).Adj u v := by
    intro hadj
    obtain ⟨_, hlt⟩ := hadj
    have hge : (1 / r) ≤ circleDistance u v := by
      simpa [hdist_uv] using (le_rfl : (1 / r) ≤ 1 / r)
    exact (not_lt_of_ge hge) hlt
  have hfu_fv_ne : f u ≠ f v := (hf u v huv hnonadj_open).1
  have hdist_f : circleDistance (f u) (f v) = 1 / r := by
    by_cases hsgn : sgn
    · have hf_eq : ∀ x, f x = a + x := by simpa [hsgn] using hform
      have hdist_f' : circleDistance (f u) (f v) = circleDistance u v := by
        simp [hf_eq, circleDistance, dist_add_left]
      simpa [hdist_uv] using hdist_f'
    · have hf_eq : ∀ x, f x = a - x := by simpa [hsgn] using hform
      have hdist_neg : circleDistance (-u) (-v) = circleDistance u v := by
        have hdist' : dist (-u) (-v) = dist u v := by
          calc
            dist (-u) (-v) = ‖(-u) - (-v)‖ := dist_eq_norm_sub _ _
            _ = ‖-(u - v)‖ := by
              have : (-u) - (-v) = -(u - v) := by abel
              simpa [this]
            _ = ‖u - v‖ := by simpa using (norm_neg (u - v))
            _ = dist u v := (dist_eq_norm_sub _ _).symm
        simpa [circleDistance] using hdist'
      have hdist_f' : circleDistance (f u) (f v) = circleDistance u v := by
        calc
          circleDistance (f u) (f v) = circleDistance (a - u) (a - v) := by
            simp [hf_eq]
          _ = circleDistance (-u) (-v) := by
            simp [circleDistance, sub_eq_add_neg, dist_add_left]
          _ = circleDistance u v := hdist_neg
      simpa [hdist_uv] using hdist_f'
  have hadj_closed : (circleGraphClosed r (le_of_lt hr)).Adj (f u) (f v) := by
    refine ⟨hfu_fv_ne, ?_⟩
    have : circleDistance (f u) (f v) ≤ 1 / r := by
      simpa [hdist_f] using (le_rfl : (1 / r) ≤ 1 / r)
    exact this
  exact (hf u v huv hnonadj_open).2 hadj_closed

/-- **Theorem 5.7 / 5.8** (real-`r` rational case): for rational `r > 2`, the
    open circle graph does not cohomomorphism-embed into the closed circle graph.
    Covers the rational branch of the combined main theorem. -/
theorem circleGraph_not_equiv_rational_real (r : ℝ) (hr : 2 < r) (hrat : ¬Irrational r) :
    ¬(Cohom (circleGraphOpen r (le_of_lt hr))
               (circleGraphClosed r (le_of_lt hr))) := by
  classical
  have hrat' : ∃ a b : ℤ, b ≠ 0 ∧ r = (a : ℝ) / b := by
    have h' : ¬ (∀ a b : ℤ, b ≠ 0 → r ≠ (a : ℝ) / b) := by
      simpa [irrational_iff_ne_rational] using hrat
    push_neg at h'
    rcases h' with ⟨a, b, hb, hrab⟩
    exact ⟨a, b, hb, by simpa [hrab]⟩
  rcases hrat' with ⟨a, b, hb, hrab⟩
  let qrat : ℚ := Rat.divInt a b
  have hqrat : r = (qrat : ℝ) := by
    have hcast : (qrat : ℝ) = (a : ℝ) / b := by
      simpa [qrat] using (Rat.cast_divInt a b : _)
    calc
      r = (a : ℝ) / b := hrab
      _ = (qrat : ℝ) := by simpa [hcast]
  have hqrat_gt : (2 : ℚ) < qrat := by
    have : ((2 : ℚ) : ℝ) < (qrat : ℝ) := by
      have : (2 : ℝ) < (qrat : ℝ) := by simpa [hqrat] using hr
      simpa using this
    exact (Rat.cast_lt).1 this
  have hqrat_pos : 0 < qrat := lt_trans (by norm_num) hqrat_gt
  have hnum_pos : 0 < qrat.num := (Rat.num_pos).2 hqrat_pos
  have hnum_nonneg : 0 ≤ qrat.num := le_of_lt hnum_pos
  let p : ℕ := Int.toNat qrat.num
  let q : ℕ := qrat.den
  have hp_pos : 0 < p := by
    have : ((0 : ℕ) : ℤ) < qrat.num := by simpa using hnum_pos
    simpa [p] using (Int.lt_toNat).2 this
  have hq_pos : 0 < q := by
    simpa [q] using (Rat.den_pos qrat)
  have h2q : 2 * q < p := by
    have h_int : (2 : ℤ) * qrat.den < qrat.num := by
      simpa using (Rat.lt_iff (2 : ℚ) qrat).1 hqrat_gt
    have h_int' : ((2 * qrat.den : ℕ) : ℤ) < qrat.num := by
      simpa using h_int
    simpa [p, q] using (Int.lt_toNat).2 h_int'
  have hnum_nat : ((p : ℕ) : ℝ) = (qrat.num : ℝ) := by
    have hnum_nat_z : ((Int.toNat qrat.num : ℤ)) = qrat.num :=
      Int.toNat_of_nonneg hnum_nonneg
    simpa [p] using (show ((Int.toNat qrat.num : ℕ) : ℝ) = (qrat.num : ℝ) by
      exact_mod_cast hnum_nat_z)
  have hqrat_eq : (qrat : ℝ) = (p : ℝ) / q := by
    calc
      (qrat : ℝ) = (qrat.num : ℝ) / qrat.den := by
        simpa [Rat.cast_def]
      _ = (p : ℝ) / q := by
        simp [p, q, hnum_nat]
  have hrle : 2 ≤ (p : ℝ) / q := by
    have : 2 ≤ (qrat : ℝ) := by
      have : 2 ≤ r := le_of_lt hr
      simpa [hqrat] using this
    simpa [hqrat_eq] using this
  have hrpq : r = (p : ℝ) / q := by
    simpa [hqrat] using hqrat_eq
  have hp_nezero : NeZero p := ⟨ne_of_gt hp_pos⟩
  have hcontra :
      ¬(Cohom (circleGraphOpen ((p : ℝ) / q) hrle)
                 (circleGraphClosed ((p : ℝ) / q) hrle)) :=
    circleGraph_not_equiv_rational (p := p) (q := q) (hq := hq_pos) (h2q := h2q) (hr := hrle)
  simpa [hrpq] using hcontra

/-- Main theorem: For any `r ≥ 2`, `E_r^c` and `E_r^o` are not equivalent.

    This combines body Theorems 5.7 (rational case, `p/q ∈ ℚ_{≥2}`) and
    5.8 (irrational case, `r ∈ ℝ_{>2}`). The `r > 2` branch delegates to
    the existing irrational/rational subcases; the `r = 2` branch uses
    the direct antipodal argument: on `Circle`, every distinct pair has
    distance `≤ 1/2`, so `E_2^c` is the complete graph on `Circle`,
    while `E_2^o` is missing exactly the antipodal pairs (distance
    `= 1/2`). Any cohomomorphism `f : E_2^o → E_2^c` applied to an
    antipodal pair `(u, u*)` (non-edge in `E_2^o`) would need to send
    `f u ≠ f u*` to a non-edge in the complete graph `E_2^c`, which is
    impossible. -/
theorem circleGraph_open_closed_not_equiv (r : ℝ) (hr : 2 ≤ r) :
    ¬(Cohom (circleGraphOpen r hr)
               (circleGraphClosed r hr) ∧
      Cohom (circleGraphClosed r hr)
               (circleGraphOpen r hr)) := by
  intro ⟨hoc, _⟩
  rcases lt_or_eq_of_le hr with hgt | heq
  · -- Strict case: r > 2. Delegate to existing irrational/rational subcases.
    -- The existing subroutines take `hr : 2 < r` and use `le_of_lt hr` internally;
    -- by proof irrelevance, the `Cohom` hypothesis transports across.
    have hoc' : Cohom (circleGraphOpen r (le_of_lt hgt))
                       (circleGraphClosed r (le_of_lt hgt)) := hoc
    by_cases hirr : Irrational r
    · exact circleGraph_not_equiv_irrational r hgt hirr hoc'
    · exact circleGraph_not_equiv_rational_real r hgt hirr hoc'
  · -- r = 2 case: direct antipodal argument.
    -- At r = 2, circleGraphClosed 2 is the complete graph on Circle
    -- (every distinct pair has distance ≤ 1/2 = 1/r), while circleGraphOpen 2
    -- has u ≁ v exactly when circleDistance u v = 1/2 (antipodal pairs).
    -- Pick any u and its antipodal v: f u ≠ f v but they are non-adjacent
    -- in the complete graph circleGraphClosed 2, contradiction.
    subst heq
    obtain ⟨f, hf⟩ := hoc
    -- Pick u = 0 ∈ Circle and its antipode v with circleDistance u v = 1/2.
    let u : Circle := 0
    obtain ⟨v, hv_ne, hdist⟩ := circleDistance_exists_antipodal u
    -- Non-adjacency in circleGraphOpen 2: distance = 1/2 is not < 1/2.
    have hnonadj_open : ¬(circleGraphOpen 2 hr).Adj u v := by
      intro ⟨_, hd⟩
      rw [hdist] at hd
      linarith
    -- IsCohom gives f u ≠ f v and ¬(circleGraphClosed 2).Adj (f u) (f v).
    have hu_ne_v : u ≠ v := hv_ne.symm
    obtain ⟨hfne, hfnadj⟩ := hf u v hu_ne_v hnonadj_open
    -- But circleGraphClosed 2 is the complete graph (every distinct pair adjacent),
    -- since circleDistance w w' ≤ 1/2 = 1/2 always (circleDistance_le_half).
    apply hfnadj
    refine ⟨hfne, ?_⟩
    -- Need: circleDistance (f u) (f v) ≤ 1/2.
    simpa using circleDistance_le_half (f u) (f v)

/-! ### Consequences -/

-- Remark: The analogous question for tensors is open.
-- If ω = 2 (matrix multiplication exponent equals 2), then the matrix
-- multiplication tensors would provide examples of asymptotically
-- equivalent but not equivalent tensors.
--
-- This is a mathematical remark, not a theorem to be formalized.

end AsymptoticSpectrumDistance
