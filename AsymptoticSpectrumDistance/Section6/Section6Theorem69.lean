/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Theorem 6.9 (`th:discont`): unified statement

Paper line 2806–2807:
> "The discontinuities of `α₃` restricted to `(ℚ ∩ [2, 3])³` are, up to
>  permutation, at [12 tuples listed]."

This file packages the 12 individual disc theorems
(`alpha3_222_isDiscontinuity`, …, `alpha3_14o5_14o5_14o5_isDiscontinuity`)
into a single statement quantified over the canonical list of 12 tuples and
their permutations.

## Main definitions

* `knownDiscList : List (FracTuple 3)` — the 12 listed tuples in their
  paper-canonical (sorted-multiset, lowest-terms) form.
* `IsKnownDiscMod v` — `v` matches one of the 12 listed multisets up to
  permutation. Equivalent to `∃ σ, ∃ w ∈ knownDiscList, v ∘ σ = w`.

## Main results

* `theorem_6_9_forward` — every `IsKnownDiscMod v` is an `IsDiscontinuityK`.
  This is the "(←) direction" of paper Theorem 6.9, packaged into a single
  statement. The full bidirectional theorem `theorem_6_9_full` (with
  `q_i ≥ 2` per slot) and the fully unconditional form
  `theorem_6_9_unconditional_of_alpha2_classification` (parameterized only
  by the residual α₂ converse) live in `Section6DiscontinuityKConverse.lean`.
-/
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityK_5o2_5o2_8o3
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityK_8o3_8o3_8o3
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityK_9o4_7o3_5o2
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityK_11o5_11o4_11o4
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityK_11o4_11o4_11o4
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityK_14o5_14o5_14o5
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKCandidates

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## The 12 disc tuples in canonical form -/

/-- Tuple `(5/2, 5/2, 8/3)` (paper Theorem 6.9 case 7). -/
def triple_5o2_5o2_8o3 : FracTuple 3 := ![(5, 2), (5, 2), (8, 3)]

/-- Tuple `(8/3, 8/3, 8/3)` (paper Theorem 6.9 case 8). -/
def triple_8o3_8o3_8o3 : FracTuple 3 := ![(8, 3), (8, 3), (8, 3)]

/-- Tuple `(9/4, 7/3, 5/2)` (paper Theorem 6.9 case 9). -/
def triple_9o4_7o3_5o2 : FracTuple 3 := ![(9, 4), (7, 3), (5, 2)]

/-- Tuple `(11/5, 11/4, 11/4)` (paper Theorem 6.9 case 10). -/
def triple_11o5_11o4_11o4 : FracTuple 3 := ![(11, 5), (11, 4), (11, 4)]

/-- Tuple `(11/4, 11/4, 11/4)` (paper Theorem 6.9 case 11). -/
def triple_11o4_11o4_11o4 : FracTuple 3 := ![(11, 4), (11, 4), (11, 4)]

/-- Tuple `(14/5, 14/5, 14/5)` (paper Theorem 6.9 case 12). -/
def triple_14o5_14o5_14o5 : FracTuple 3 := ![(14, 5), (14, 5), (14, 5)]

/-- The 12 paper-canonical α₃-disc tuples (paper Theorem 6.9 cases 1–12).
    Each tuple is in lowest terms and sorted; the actual disc set is closed
    under permutation, so a `FracTuple 3` is a disc iff some permutation of it
    appears in `knownDiscList`. -/
def knownDiscList : List (FracTuple 3) :=
  [ triple222,
    triple223,
    triple233,
    triple333,
    triple_2_5o2_5o2,
    triple_5o2_5o2_3,
    triple_5o2_5o2_8o3,
    triple_8o3_8o3_8o3,
    triple_9o4_7o3_5o2,
    triple_11o5_11o4_11o4,
    triple_11o4_11o4_11o4,
    triple_14o5_14o5_14o5 ]

/-- `v : FracTuple 3` matches one of the 12 paper-canonical disc tuples up
    to permutation. -/
def IsKnownDiscMod (v : FracTuple 3) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∃ w ∈ knownDiscList, v ∘ σ = w

/-! ## Forward direction: every `IsKnownDiscMod` is an `IsDiscontinuityK` -/

/-- The 12 individual disc theorems collected as one list-membership claim:
    every tuple in `knownDiscList` is `IsDiscontinuityK`. -/
theorem isDiscontinuityK_of_mem_knownDiscList {w : FracTuple 3}
    (hw : w ∈ knownDiscList) : IsDiscontinuityK w := by
  -- 12-way case split on `w ∈ knownDiscList`.
  simp only [knownDiscList, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact alphaK_222_isDiscontinuityK
  · exact alphaK_223_isDiscontinuityK
  · exact alphaK_233_isDiscontinuityK
  · exact alphaK_333_isDiscontinuityK
  · exact alphaK_2_5o2_5o2_isDiscontinuityK
  · -- triple_5o2_5o2_3 = (consInt 3 pair5o2_5o2) ∘ Equiv.swap (0 : Fin 3) 2
    have heq : triple_5o2_5o2_3 = (consInt 3 pair5o2_5o2) ∘ Equiv.swap (0 : Fin 3) 2 := by
      funext i
      fin_cases i <;> decide
    rw [heq]
    exact alphaK_5o2_5o2_3_isDiscontinuityK
  · exact (isDiscontinuity_iff_isDiscontinuityK _).mp alpha3_5o2_5o2_8o3_isDiscontinuity
  · exact (isDiscontinuity_iff_isDiscontinuityK _).mp alpha3_8o3_8o3_8o3_isDiscontinuity
  · exact (isDiscontinuity_iff_isDiscontinuityK _).mp alpha3_9o4_7o3_5o2_isDiscontinuity
  · exact (isDiscontinuity_iff_isDiscontinuityK _).mp alpha3_11o5_11o4_11o4_isDiscontinuity
  · exact (isDiscontinuity_iff_isDiscontinuityK _).mp alpha3_11o4_11o4_11o4_isDiscontinuity
  · exact (isDiscontinuity_iff_isDiscontinuityK _).mp alpha3_14o5_14o5_14o5_isDiscontinuity

/-- **Theorem 6.9 (forward direction, `th:discont` ←).**
    Every tuple matching one of the 12 paper-canonical multisets is an
    α₃-discontinuity in `(ℚ ∩ [2, 3])³`. -/
theorem theorem_6_9_forward {v : FracTuple 3} (h : IsKnownDiscMod v) :
    IsDiscontinuityK v := by
  obtain ⟨σ, w, hw_mem, hwv⟩ := h
  -- v ∘ σ = w, so isDiscontinuityK_perm at σ takes IsDiscontinuityK v to
  -- IsDiscontinuityK (v ∘ σ) = IsDiscontinuityK w.
  have h_disc_w : IsDiscontinuityK w := isDiscontinuityK_of_mem_knownDiscList hw_mem
  rw [← hwv] at h_disc_w
  exact (isDiscontinuityK_perm σ).mpr h_disc_w

end Section6
