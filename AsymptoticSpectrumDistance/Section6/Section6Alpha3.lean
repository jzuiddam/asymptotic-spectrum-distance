/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Theorem 6.9: Twelve α₃ Values

Computes α₃(r₁, r₂, r₃) = α(E_{r₁} ⊠ E_{r₂} ⊠ E_{r₃}) for the 12 discontinuity triples
from Theorem 6.9 of the paper.

Cases 1-5, 12 use the integer factor lemma (α(E_n ⊠ G) = n·α(G)) and Theorem 6.5.
Cases 6, 9, 11 use the nested floor bound (tight) with explicit independent sets (native_decide).
Cases 10 uses the nested floor bound with an IS found by Gurobi.
Cases 7-8 use Baumert slicing for the upper bound (nested floor not tight); see Section6UpperBounds.lean.

## Main results

- `alpha3_2_2_2` through `alpha3_3_3_3`: the 12 specific α₃ values
-/
import AsymptoticSpectrumDistance.Section6.Section6IntegerFactor
import AsymptoticSpectrumDistance.Section6.Section6TwoFactor
import AsymptoticSpectrumDistance.Section6.Section6UpperBounds

open ShannonCapacity

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Decidability instances -/

instance strongProduct3_adj_decidable
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ) [NeZero p₁] [NeZero p₂] [NeZero p₃] :
    DecidableRel (strongProduct (fractionGraph p₁ q₁)
      (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).Adj :=
  fun a b => by unfold strongProduct; simp only; exact instDecidableAnd

/-! ## Bridge lemma: list pairwise non-adjacency implies independence -/

set_option linter.unusedFintypeInType false in
private lemma indepSet_of_list_pairwise {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (l : List V)
    (hpw : l.Pairwise (fun a b => ¬G.Adj a b)) :
    G.IsIndepSet (l.toFinset : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb _ hadj
  have ha' := List.mem_toFinset.mp (Finset.mem_coe.mp ha)
  have hb' := List.mem_toFinset.mp (Finset.mem_coe.mp hb)
  have hsymm : Symmetric (fun (a b : V) => ¬G.Adj a b) := by
    intro x y h h'
    exact h (G.symm h')
  exact (hpw.forall_of_forall hsymm (fun x _ => SimpleGraph.irrefl G) ha' hb') hadj

/-! ## Helper for evaluating nested floor expressions

`floor_val` (`⌊a⌋₊ = n` from `n ≤ a < n+1`) lives in
`Section6UpperBoundsCommon` and is reused below. -/

/-! ## Cases 1-5, 12: Integer factor cases -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 1: α₃(2, 2, 2) = 8. All edgeless factors. -/
theorem alpha3_2_2_2 :
    (strongProduct (fractionGraph 2 1)
      (strongProduct (fractionGraph 2 1) (fractionGraph 2 1))).indepNum = 8 := by
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  rw [fractionGraph_one_indepNum 2 (by omega)]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 2: α₃(2, 2, 3) = 12. -/
theorem alpha3_2_2_3 :
    (strongProduct (fractionGraph 2 1)
      (strongProduct (fractionGraph 2 1) (fractionGraph 3 1))).indepNum = 12 := by
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  rw [fractionGraph_one_indepNum 3 (by omega)]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 3: α₃(2, 3, 3) = 18. -/
theorem alpha3_2_3_3 :
    (strongProduct (fractionGraph 2 1)
      (strongProduct (fractionGraph 3 1) (fractionGraph 3 1))).indepNum = 18 := by
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega)]
  rw [fractionGraph_one_indepNum 3 (by omega)]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 4: α₃(2, 5/2, 5/2) = 10. Integer factor + Theorem 6.5. -/
theorem alpha3_2_5o2_5o2 :
    (strongProduct (fractionGraph 2 1)
      (strongProduct (fractionGraph 5 2) (fractionGraph 5 2))).indepNum = 10 := by
  rw [indepNum_strongProduct_edgeless_fraction 2 (by omega)]
  rw [theorem_6_5 5 2 5 2 (by omega) (by omega) (by omega) (by omega)]
  push_cast; simp only [min_self]
  have h1 : ⌊(5:ℝ)/2⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1]; push_cast
  have h2 : ⌊(5:ℝ)/2 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h2]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 5: α₃(5/2, 5/2, 3) = 15. Integer factor + Theorem 6.5. -/
theorem alpha3_5o2_5o2_3 :
    (strongProduct (fractionGraph 3 1)
      (strongProduct (fractionGraph 5 2) (fractionGraph 5 2))).indepNum = 15 := by
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega)]
  rw [theorem_6_5 5 2 5 2 (by omega) (by omega) (by omega) (by omega)]
  push_cast; simp only [min_self]
  have h1 : ⌊(5:ℝ)/2⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h1]; push_cast
  have h2 : ⌊(5:ℝ)/2 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
  rw [h2]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 12: α₃(3, 3, 3) = 27. All edgeless factors. -/
theorem alpha3_3_3_3 :
    (strongProduct (fractionGraph 3 1)
      (strongProduct (fractionGraph 3 1) (fractionGraph 3 1))).indepNum = 27 := by
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega)]
  rw [indepNum_strongProduct_edgeless_fraction 3 (by omega)]
  rw [fractionGraph_one_indepNum 3 (by omega)]

/-! ## Case 6: (9/4, 7/3, 5/2), α₃ = 9. Nested floor tight. -/

/-- Orbit {(t, 4t mod 7, 4t mod 5) : t ∈ Z₉}. -/
private def case6_list : List (ZMod 9 × (ZMod 7 × ZMod 5)) :=
  (List.range 9).map fun (t : ℕ) =>
    ((t : ZMod 9), (((4 * t : ℕ) : ZMod 7), ((4 * t : ℕ) : ZMod 5)))

set_option maxRecDepth 512 in
private theorem case6_pairwise :
    case6_list.Pairwise (fun a b =>
      ¬(strongProduct (fractionGraph 9 4)
        (strongProduct (fractionGraph 7 3) (fractionGraph 5 2))).Adj a b) := by
  native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 6: α₃(9/4, 7/3, 5/2) = 9. -/
theorem alpha3_9o4_7o3_5o2 :
    (strongProduct (fractionGraph 9 4)
      (strongProduct (fractionGraph 7 3) (fractionGraph 5 2))).indepNum = 9 := by
  apply le_antisymm
  · calc _ ≤ ⌊(9:ℝ)/4 * ⌊(7:ℝ)/3 * ⌊(5:ℝ)/2⌋₊⌋₊⌋₊ :=
          nested_floor_three 9 4 7 3 5 2 (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
      _ = 9 := by
          have h1 : ⌊(5:ℝ)/2⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
          rw [h1]; push_cast
          have h2 : ⌊(7:ℝ)/3 * 2⌋₊ = 4 := floor_val (by positivity) (by norm_num) (by norm_num)
          rw [h2]; push_cast
          exact floor_val (by positivity) (by norm_num) (by norm_num)
  · have hindep := indepSet_of_list_pairwise _ case6_list case6_pairwise
    have hcard : case6_list.toFinset.card = 9 := by native_decide
    calc 9 = case6_list.toFinset.card := hcard.symm
      _ ≤ _ := SimpleGraph.IsIndepSet.card_le_indepNum hindep

/-! ## Case 7: (5/2, 5/2, 8/3), α₃ = 11. Nested floor gives 12, UB via Baumert. -/

/-- IS found by Gurobi optimization. -/
private def case7_list : List (ZMod 5 × (ZMod 5 × ZMod 8)) :=
  [((0:ZMod 5), ((1:ZMod 5), (0:ZMod 8))),
   ((0:ZMod 5), ((3:ZMod 5), (6:ZMod 8))),
   ((0:ZMod 5), ((4:ZMod 5), (1:ZMod 8))),
   ((1:ZMod 5), ((1:ZMod 5), (5:ZMod 8))),
   ((2:ZMod 5), ((1:ZMod 5), (2:ZMod 8))),
   ((2:ZMod 5), ((3:ZMod 5), (1:ZMod 8))),
   ((2:ZMod 5), ((4:ZMod 5), (4:ZMod 8))),
   ((3:ZMod 5), ((0:ZMod 5), (7:ZMod 8))),
   ((3:ZMod 5), ((2:ZMod 5), (6:ZMod 8))),
   ((4:ZMod 5), ((0:ZMod 5), (4:ZMod 8))),
   ((4:ZMod 5), ((2:ZMod 5), (3:ZMod 8)))]

set_option maxRecDepth 512 in
private theorem case7_pairwise :
    case7_list.Pairwise (fun a b =>
      ¬(strongProduct (fractionGraph 5 2)
        (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).Adj a b) := by
  native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 7: α₃(5/2, 5/2, 8/3) = 11.
Upper bound requires an ad hoc argument (nested floor gives 12). -/
theorem alpha3_5o2_5o2_8o3 :
    (strongProduct (fractionGraph 5 2)
      (strongProduct (fractionGraph 5 2) (fractionGraph 8 3))).indepNum = 11 := by
  apply le_antisymm
  · exact alpha3_5o2_5o2_8o3_le
  · have hindep := indepSet_of_list_pairwise _ case7_list case7_pairwise
    have hcard : case7_list.toFinset.card = 11 := by native_decide
    calc 11 = case7_list.toFinset.card := hcard.symm
      _ ≤ _ := SimpleGraph.IsIndepSet.card_le_indepNum hindep

/-! ## Case 8: (8/3, 8/3, 8/3), α₃ = 12. Nested floor gives 13, UB via Baumert. -/

/-- IS found by Gurobi optimization. Not an orbit (see paper Remark after Thm 6.9). -/
private def case8_list : List (ZMod 8 × (ZMod 8 × ZMod 8)) :=
  [((0:ZMod 8), ((0:ZMod 8), (0:ZMod 8))),
   ((0:ZMod 8), ((6:ZMod 8), (3:ZMod 8))),
   ((1:ZMod 8), ((4:ZMod 8), (7:ZMod 8))),
   ((2:ZMod 8), ((1:ZMod 8), (3:ZMod 8))),
   ((3:ZMod 8), ((4:ZMod 8), (4:ZMod 8))),
   ((3:ZMod 8), ((7:ZMod 8), (6:ZMod 8))),
   ((4:ZMod 8), ((2:ZMod 8), (7:ZMod 8))),
   ((4:ZMod 8), ((5:ZMod 8), (1:ZMod 8))),
   ((5:ZMod 8), ((0:ZMod 8), (2:ZMod 8))),
   ((6:ZMod 8), ((5:ZMod 8), (6:ZMod 8))),
   ((7:ZMod 8), ((1:ZMod 8), (5:ZMod 8))),
   ((7:ZMod 8), ((3:ZMod 8), (2:ZMod 8)))]

set_option maxRecDepth 512 in
private theorem case8_pairwise :
    case8_list.Pairwise (fun a b =>
      ¬(strongProduct (fractionGraph 8 3)
        (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).Adj a b) := by
  native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 8: α₃(8/3, 8/3, 8/3) = 12.
Upper bound requires an ad hoc argument (nested floor gives 13). -/
theorem alpha3_8o3_8o3_8o3 :
    (strongProduct (fractionGraph 8 3)
      (strongProduct (fractionGraph 8 3) (fractionGraph 8 3))).indepNum = 12 := by
  apply le_antisymm
  · exact alpha3_8o3_8o3_8o3_le
  · have hindep := indepSet_of_list_pairwise _ case8_list case8_pairwise
    have hcard : case8_list.toFinset.card = 12 := by native_decide
    calc 12 = case8_list.toFinset.card := hcard.symm
      _ ≤ _ := SimpleGraph.IsIndepSet.card_le_indepNum hindep

/-! ## Case 9: (11/5, 11/4, 11/4), α₃ = 11. Nested floor tight. -/

/-- Orbit {(t, 4t, 2t) : t ∈ Z₁₁}. -/
private def case9_list : List (ZMod 11 × (ZMod 11 × ZMod 11)) :=
  (List.range 11).map fun (t : ℕ) =>
    ((t : ZMod 11), (((4 * t : ℕ) : ZMod 11), ((2 * t : ℕ) : ZMod 11)))

set_option maxRecDepth 512 in
private theorem case9_pairwise :
    case9_list.Pairwise (fun a b =>
      ¬(strongProduct (fractionGraph 11 5)
        (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).Adj a b) := by
  native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 9: α₃(11/5, 11/4, 11/4) = 11. -/
theorem alpha3_11o5_11o4_11o4 :
    (strongProduct (fractionGraph 11 5)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).indepNum = 11 := by
  apply le_antisymm
  · calc _ ≤ ⌊(11:ℝ)/5 * ⌊(11:ℝ)/4 * ⌊(11:ℝ)/4⌋₊⌋₊⌋₊ :=
          nested_floor_three 11 5 11 4 11 4 (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
      _ = 11 := by
          have h1 : ⌊(11:ℝ)/4⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
          rw [h1]; push_cast
          have h2 : ⌊(11:ℝ)/4 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
          rw [h2]; push_cast
          exact floor_val (by positivity) (by norm_num) (by norm_num)
  · have hindep := indepSet_of_list_pairwise _ case9_list case9_pairwise
    have hcard : case9_list.toFinset.card = 11 := by native_decide
    calc 11 = case9_list.toFinset.card := hcard.symm
      _ ≤ _ := SimpleGraph.IsIndepSet.card_le_indepNum hindep

/-! ## Case 10: (11/4, 11/4, 11/4), α₃ = 13. Nested floor tight. -/

/-- IS found by Gurobi optimization. -/
private def case10_list : List (ZMod 11 × (ZMod 11 × ZMod 11)) :=
  [((0:ZMod 11), ((3:ZMod 11), (9:ZMod 11))),
   ((1:ZMod 11), ((10:ZMod 11), (3:ZMod 11))),
   ((2:ZMod 11), ((3:ZMod 11), (5:ZMod 11))),
   ((3:ZMod 11), ((7:ZMod 11), (8:ZMod 11))),
   ((4:ZMod 11), ((0:ZMod 11), (10:ZMod 11))),
   ((4:ZMod 11), ((4:ZMod 11), (1:ZMod 11))),
   ((5:ZMod 11), ((8:ZMod 11), (4:ZMod 11))),
   ((6:ZMod 11), ((1:ZMod 11), (6:ZMod 11))),
   ((7:ZMod 11), ((5:ZMod 11), (8:ZMod 11))),
   ((8:ZMod 11), ((2:ZMod 11), (2:ZMod 11))),
   ((8:ZMod 11), ((9:ZMod 11), (0:ZMod 11))),
   ((9:ZMod 11), ((6:ZMod 11), (4:ZMod 11))),
   ((10:ZMod 11), ((10:ZMod 11), (7:ZMod 11)))]

set_option maxRecDepth 512 in
private theorem case10_pairwise :
    case10_list.Pairwise (fun a b =>
      ¬(strongProduct (fractionGraph 11 4)
        (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).Adj a b) := by
  native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 10: α₃(11/4, 11/4, 11/4) = 13. -/
theorem alpha3_11o4_11o4_11o4 :
    (strongProduct (fractionGraph 11 4)
      (strongProduct (fractionGraph 11 4) (fractionGraph 11 4))).indepNum = 13 := by
  apply le_antisymm
  · calc _ ≤ ⌊(11:ℝ)/4 * ⌊(11:ℝ)/4 * ⌊(11:ℝ)/4⌋₊⌋₊⌋₊ :=
          nested_floor_three 11 4 11 4 11 4 (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
      _ = 13 := by
          have h1 : ⌊(11:ℝ)/4⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
          rw [h1]; push_cast
          have h2 : ⌊(11:ℝ)/4 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
          rw [h2]; push_cast
          exact floor_val (by positivity) (by norm_num) (by norm_num)
  · have hindep := indepSet_of_list_pairwise _ case10_list case10_pairwise
    have hcard : case10_list.toFinset.card = 13 := by native_decide
    calc 13 = case10_list.toFinset.card := hcard.symm
      _ ≤ _ := SimpleGraph.IsIndepSet.card_le_indepNum hindep

/-! ## Case 11: (14/5, 14/5, 14/5), α₃ = 14. Nested floor tight. -/

/-- Orbit {(t, 3t, 9t) : t ∈ Z₁₄}. -/
private def case11_list : List (ZMod 14 × (ZMod 14 × ZMod 14)) :=
  (List.range 14).map fun (t : ℕ) =>
    ((t : ZMod 14), (((3 * t : ℕ) : ZMod 14), ((9 * t : ℕ) : ZMod 14)))

set_option maxRecDepth 512 in
private theorem case11_pairwise :
    case11_list.Pairwise (fun a b =>
      ¬(strongProduct (fractionGraph 14 5)
        (strongProduct (fractionGraph 14 5) (fractionGraph 14 5))).Adj a b) := by
  native_decide

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Case 11: α₃(14/5, 14/5, 14/5) = 14. -/
theorem alpha3_14o5_14o5_14o5 :
    (strongProduct (fractionGraph 14 5)
      (strongProduct (fractionGraph 14 5) (fractionGraph 14 5))).indepNum = 14 := by
  apply le_antisymm
  · calc _ ≤ ⌊(14:ℝ)/5 * ⌊(14:ℝ)/5 * ⌊(14:ℝ)/5⌋₊⌋₊⌋₊ :=
          nested_floor_three 14 5 14 5 14 5 (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
      _ = 14 := by
          have h1 : ⌊(14:ℝ)/5⌋₊ = 2 := floor_val (by positivity) (by norm_num) (by norm_num)
          rw [h1]; push_cast
          have h2 : ⌊(14:ℝ)/5 * 2⌋₊ = 5 := floor_val (by positivity) (by norm_num) (by norm_num)
          rw [h2]; push_cast
          exact floor_val (by positivity) (by norm_num) (by norm_num)
  · have hindep := indepSet_of_list_pairwise _ case11_list case11_pairwise
    have hcard : case11_list.toFinset.card = 14 := by native_decide
    calc 14 = case11_list.toFinset.card := hcard.symm
      _ ≤ _ := SimpleGraph.IsIndepSet.card_le_indepNum hindep

/-! ## Left-associated wrappers for paper-API delegation (Main.lean)

Each `_main` wrapper restates an `alpha3_*` theorem in the left-associated form
`(A ⊠ B ⊠ C).indepNum = N` (matching the paper-API shape used by `Main.lean`),
delegating to the right-associated `alpha3_*` via `indepNum_strongProduct_assoc`. -/

/-- Left-assoc wrapper for `alpha3_2_2_2`. -/
theorem alpha3_2_2_2_main :
    (fractionGraph 2 1 ⊠ fractionGraph 2 1 ⊠ fractionGraph 2 1).indepNum = 8 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_2_2_2

/-- Left-assoc wrapper for `alpha3_2_2_3`. -/
theorem alpha3_2_2_3_main :
    (fractionGraph 2 1 ⊠ fractionGraph 2 1 ⊠ fractionGraph 3 1).indepNum = 12 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_2_2_3

/-- Left-assoc wrapper for `alpha3_2_3_3`. -/
theorem alpha3_2_3_3_main :
    (fractionGraph 2 1 ⊠ fractionGraph 3 1 ⊠ fractionGraph 3 1).indepNum = 18 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_2_3_3

/-- Left-assoc wrapper for `alpha3_2_5o2_5o2`. -/
theorem alpha3_2_5o2_5o2_main :
    (fractionGraph 2 1 ⊠ fractionGraph 5 2 ⊠ fractionGraph 5 2).indepNum = 10 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_2_5o2_5o2

/-- Left-assoc wrapper for `alpha3_5o2_5o2_3`.
    (Uses `indepNum_strongProduct_comm` to swap; underlying lemma is stated as
    `(3) ⊠ (5/2) ⊠ (5/2)` because Case 5 uses the integer-factor short proof.) -/
theorem alpha3_5o2_5o2_3_main :
    (fractionGraph 5 2 ⊠ fractionGraph 5 2 ⊠ fractionGraph 3 1).indepNum = 15 := by
  rw [indepNum_strongProduct_comm]; exact alpha3_5o2_5o2_3

/-- Left-assoc wrapper for `alpha3_5o2_5o2_8o3`. -/
theorem alpha3_5o2_5o2_8o3_main :
    (fractionGraph 5 2 ⊠ fractionGraph 5 2 ⊠ fractionGraph 8 3).indepNum = 11 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_5o2_5o2_8o3

/-- Left-assoc wrapper for `alpha3_8o3_8o3_8o3`. -/
theorem alpha3_8o3_8o3_8o3_main :
    (fractionGraph 8 3 ⊠ fractionGraph 8 3 ⊠ fractionGraph 8 3).indepNum = 12 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_8o3_8o3_8o3

/-- Left-assoc wrapper for `alpha3_9o4_7o3_5o2`. -/
theorem alpha3_9o4_7o3_5o2_main :
    (fractionGraph 9 4 ⊠ fractionGraph 7 3 ⊠ fractionGraph 5 2).indepNum = 9 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_9o4_7o3_5o2

/-- Left-assoc wrapper for `alpha3_11o5_11o4_11o4`. -/
theorem alpha3_11o5_11o4_11o4_main :
    (fractionGraph 11 5 ⊠ fractionGraph 11 4 ⊠ fractionGraph 11 4).indepNum = 11 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_11o5_11o4_11o4

/-- Left-assoc wrapper for `alpha3_11o4_11o4_11o4`. -/
theorem alpha3_11o4_11o4_11o4_main :
    (fractionGraph 11 4 ⊠ fractionGraph 11 4 ⊠ fractionGraph 11 4).indepNum = 13 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_11o4_11o4_11o4

/-- Left-assoc wrapper for `alpha3_14o5_14o5_14o5`. -/
theorem alpha3_14o5_14o5_14o5_main :
    (fractionGraph 14 5 ⊠ fractionGraph 14 5 ⊠ fractionGraph 14 5).indepNum = 14 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_14o5_14o5_14o5

/-- Left-assoc wrapper for `alpha3_3_3_3`. -/
theorem alpha3_3_3_3_main :
    (fractionGraph 3 1 ⊠ fractionGraph 3 1 ⊠ fractionGraph 3 1).indepNum = 27 := by
  rw [ShannonCapacity.indepNum_strongProduct_assoc]; exact alpha3_3_3_3

end Section6
