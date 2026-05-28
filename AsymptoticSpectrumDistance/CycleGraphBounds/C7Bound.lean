/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shannon Capacity Lower Bound for C₇

Proves Θ(C₇) ≥ 367^{1/5} ≈ 3.258 using an explicit independent set in C₇^{⊠5}.

## Architecture

Following the pattern from C15IndependentSetFast.lean:
1. **Computation**: verify pairwise non-adjacency of 367 vertices in C₇^{⊠5}
   via `native_decide` on raw ℕ encodings.
2. **Soundness bridge**: prove graph adjacency implies raw adjacency
   (49-case `native_decide` + coordinate-wise argument).

The 367 vertices were obtained via nondeterministic rounding from the orbit
{t·(1,7,49,343,109) mod 382 : t ∈ ℤ₃₈₂} in E_{382/108}^{⊠5}, followed by
ILP optimization. The bound α(C₇^{⊠5}) ≥ 367 is due to Polak–Schrijver (2019).

## Main results

- `C7_5_indepNum_bound`: `(strongPower (fractionGraph 7 2) 5).indepNum ≥ 367`
- `shannonCapacity_cycleGraph_7_lower`:
    `shannonCapacity (SimpleGraph.cycleGraph 7) ≥ (367 : ℝ) ^ ((1 : ℝ) / 5)`
-/
import AsymptoticSpectrumDistance.CycleGraphBounds.C7Data
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import Mathlib.Data.Set.Pairwise.List

open ShannonCapacity C7Data

set_option linter.style.nativeDecide false
set_option linter.style.show false

namespace C7Bound

/-! ## Raw adjacency check for C₇^{⊠5} -/

/-- Check if two base-7 digits are equal or adjacent on C₇ (distance < 2). -/
def digitEqOrAdj (a b : ℕ) : Bool :=
  a == b || (a + 1) % 7 == b || (b + 1) % 7 == a

/-- Raw adjacency check: are two base-7 encoded vertices adjacent in C₇^{⊠5}? -/
def adjRaw (v w : ℕ) : Bool :=
  v != w &&
  digitEqOrAdj (v / 2401 % 7) (w / 2401 % 7) &&
  digitEqOrAdj (v / 343 % 7) (w / 343 % 7) &&
  digitEqOrAdj (v / 49 % 7) (w / 49 % 7) &&
  digitEqOrAdj (v / 7 % 7) (w / 7 % 7) &&
  digitEqOrAdj (v % 7) (w % 7)

/-- Pairwise check: no two raw vertices are adjacent. -/
def checkPairwiseRaw : Bool :=
  C7_5_rawList.all fun v =>
    C7_5_rawList.all fun w =>
      v == w || !adjRaw v w

/-! ## Computational verification -/

theorem checkPairwiseRaw_eq : checkPairwiseRaw = true := by native_decide

/-! ## Soundness bridge: raw check → graph-theoretic independence

We connect `adjRaw` to the graph adjacency via a `native_decide`
(49 cases) at the coordinate level.
-/

/-- `digitEqOrAdj` matches "equal or adjacent on C₇" for digits < 7.
    Verified by exhaustive check over all 49 pairs. -/
def checkDigitBridge : Bool :=
  (List.range 7).all fun a =>
    (List.range 7).all fun b =>
      digitEqOrAdj a b ==
        decide ((a : ZMod 7) = (b : ZMod 7) ∨
                (fractionGraph 7 2).Adj (a : ZMod 7) (b : ZMod 7))

theorem checkDigitBridge_eq : checkDigitBridge = true := by native_decide

theorem digitEqOrAdj_iff (a b : ℕ) (ha : a < 7) (hb : b < 7) :
    digitEqOrAdj a b =
      decide ((a : ZMod 7) = (b : ZMod 7) ∨
              (fractionGraph 7 2).Adj (a : ZMod 7) (b : ZMod 7)) := by
  have h := checkDigitBridge_eq
  simp only [checkDigitBridge, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  exact h a ha b hb

theorem digitEqOrAdj_of_eq_or_adj (a b : ℕ) (ha : a < 7) (hb : b < 7)
    (h : (a : ZMod 7) = (b : ZMod 7) ∨
         (fractionGraph 7 2).Adj (a : ZMod 7) (b : ZMod 7)) :
    digitEqOrAdj a b = true := by
  rw [digitEqOrAdj_iff a b ha hb]; simp [h]

/-- All raw vertices have all digits < 7. -/
theorem rawList_digits_valid (v : ℕ) (_ : v ∈ C7_5_rawList) :
    v / 2401 % 7 < 7 ∧ v / 343 % 7 < 7 ∧ v / 49 % 7 < 7 ∧
    v / 7 % 7 < 7 ∧ v % 7 < 7 :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
   Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
   Nat.mod_lt _ (by norm_num)⟩

/-- Strong product adjacency implies raw adjacency for valid encodings. -/
theorem adj_implies_adjRaw (v w : ℕ)
    (hv : v / 2401 % 7 < 7 ∧ v / 343 % 7 < 7 ∧ v / 49 % 7 < 7 ∧
          v / 7 % 7 < 7 ∧ v % 7 < 7)
    (hw : w / 2401 % 7 < 7 ∧ w / 343 % 7 < 7 ∧ w / 49 % 7 < 7 ∧
          w / 7 % 7 < 7 ∧ w % 7 < 7)
    (hadj : (strongPower (fractionGraph 7 2) 5).Adj (decodeVertex v) (decodeVertex w)) :
    adjRaw v w = true := by
  obtain ⟨hne, hcoord⟩ := hadj
  simp only [adjRaw, Bool.and_eq_true, bne_iff_ne]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro heq; apply hne; subst heq; rfl
  · have h0 := hcoord 0
    simp only [decodeVertex] at h0
    rw [← ZMod.natCast_mod (v / 2401) 7, ← ZMod.natCast_mod (w / 2401) 7] at h0
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.1 hw.1 h0
  · have h1 := hcoord 1
    simp only [decodeVertex] at h1
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.2.1 hw.2.1 h1
  · have h2 := hcoord 2
    simp only [decodeVertex] at h2
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.2.2.1 hw.2.2.1 h2
  · have h3 := hcoord 3
    simp only [decodeVertex] at h3
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.2.2.2.1 hw.2.2.2.1 h3
  · have h4 := hcoord 4
    simp only [decodeVertex] at h4
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.2.2.2.2 hw.2.2.2.2 h4

/-! ## Combining raw check with bridge -/

theorem not_adjRaw_of_mem (v w : ℕ) (hv : v ∈ C7_5_rawList) (hw : w ∈ C7_5_rawList)
    (hne : v ≠ w) : adjRaw v w = false := by
  have h := checkPairwiseRaw_eq
  simp only [checkPairwiseRaw, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at h
  have := h v hv w hw
  simp only [hne, false_or] at this
  exact this

/-- The pairwise non-adjacency theorem in C₇^{⊠5}. -/
theorem C7_5_pairwise_nonadj : C7_5_vertices.Pairwise
    (fun u v => ¬(strongPower (fractionGraph 7 2) 5).Adj u v) := by
  show (C7_5_rawList.map decodeVertex).Pairwise _
  rw [List.pairwise_map]
  have hnodup : C7_5_rawList.Nodup := by native_decide
  apply hnodup.pairwise_of_set_pairwise
  intro a ha b hb hne hadj
  have h1 : adjRaw a b = true :=
    adj_implies_adjRaw a b (rawList_digits_valid a ha) (rawList_digits_valid b hb) hadj
  have h2 : adjRaw a b = false := not_adjRaw_of_mem a b ha hb hne
  exact absurd h1 (by simp [h2])

/-! ## Independence in C₇^{⊠5} -/

theorem C7_5_nodup : C7_5_vertices.Nodup := by native_decide

theorem C7_5_length : C7_5_vertices.length = 367 := by native_decide

def C7_5_finset : Finset (Fin 5 → ZMod 7) :=
  ⟨↑C7_5_vertices, Multiset.coe_nodup.mpr C7_5_nodup⟩

theorem C7_5_card : C7_5_finset.card = 367 := by
  simp [C7_5_finset, Multiset.coe_card, C7_5_length]

theorem C7_5_isIndepSet : (strongPower (fractionGraph 7 2) 5).IsIndepSet
    (↑C7_5_finset : Set (Fin 5 → ZMod 7)) := by
  intro a ha b hb hab
  have ha' : a ∈ C7_5_vertices := by
    simpa [C7_5_finset, Finset.mem_mk, Multiset.mem_coe] using ha
  have hb' : b ∈ C7_5_vertices := by
    simpa [C7_5_finset, Finset.mem_mk, Multiset.mem_coe] using hb
  have hsym : Symmetric (fun u v : Fin 5 → ZMod 7 =>
      ¬(strongPower (fractionGraph 7 2) 5).Adj u v) := by
    intro a b h hadj; exact h hadj.symm
  exact C7_5_pairwise_nonadj.forall hsym ha' hb' hab

theorem C7_5_indepNum_bound :
    (strongPower (fractionGraph 7 2) 5).indepNum ≥ 367 := by
  have h := SimpleGraph.IsIndepSet.card_le_indepNum C7_5_isIndepSet
  rw [C7_5_card] at h; exact h

theorem shannonCapacity_cycleGraph_7_lower :
    shannonCapacity (SimpleGraph.cycleGraph 7) ≥ (367 : ℝ) ^ ((1 : ℝ) / 5) := by
  rw [shannonCapacity_iso (cycleGraph_iso_fractionGraph_two 7 (by norm_num))]
  calc shannonCapacity (fractionGraph 7 2)
      ≥ ((strongPower (fractionGraph 7 2) 5).indepNum : ℝ) ^ ((1 : ℝ) / 5) :=
        shannonCapacity_ge_root _ 5 (by norm_num)
    _ ≥ (367 : ℝ) ^ ((1 : ℝ) / 5) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast C7_5_indepNum_bound

end C7Bound
