/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shannon Capacity Lower Bound for C₅

Proves Θ(C₅) ≥ 5^{1/2} = √5 ≈ 2.236 using an orbit construction in E_{5/2}^{⊠2}.

The orbit {t · (1,2) : t ∈ ℤ₅} gives 5 vertices in E_{5/2}^{⊠2} = C₅^{⊠2}.
This construction is due to Shannon (1956). The matching upper bound
Θ(C₅) ≤ √5 is due to Lovász (1979).

## Main results

- `C5_2_indepNum_bound`: `(strongPower (fractionGraph 5 2) 2).indepNum ≥ 5`
- `shannonCapacity_cycleGraph_5_lower`:
    `shannonCapacity (SimpleGraph.cycleGraph 5) ≥ (5 : ℝ) ^ ((1 : ℝ) / 2)`
-/
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import Mathlib.Data.Set.Pairwise.List

open ShannonCapacity

set_option linter.style.nativeDecide false

namespace C5Bound

/-! ## Data -/

/-- Decode a raw ℕ to a vertex in (ZMod 5)^2.
    Encoding: v = a * 5 + b with a, b < 5. -/
def decodeVertex (v : ℕ) : Fin 2 → ZMod 5 :=
  fun i => match i with
    | 0 => (v / 5 % 5 : ℕ)
    | 1 => (v % 5 : ℕ)

/-- The 5 orbit vertices {t · (1,2) mod 5 : t = 0, ..., 4}
    encoded as raw natural numbers (base-5 representation). -/
def rawList : List ℕ :=
  (List.range 5).map fun t =>
    (t % 5) * 5 + ((2 * t) % 5)

def vertexList : List (Fin 2 → ZMod 5) :=
  rawList.map decodeVertex

/-! ## Raw adjacency check for E_{5/2}^{⊠2} -/

/-- Raw circular distance between two values modulo 5. -/
def distModRaw (a b : ℕ) : ℕ :=
  let diff := if a ≥ b then a - b else b - a
  min diff (5 - diff)

/-- Check if two coordinates are "equal or adjacent" in E_{5/2}:
    distMod 5 a b < 2 (which includes a = b since distMod = 0). -/
def digitClose (a b : ℕ) : Bool :=
  distModRaw a b < 2

/-- Raw adjacency in E_{5/2}^{⊠2}. -/
def adjRaw (v w : ℕ) : Bool :=
  v != w &&
  digitClose (v / 5 % 5) (w / 5 % 5) &&
  digitClose (v % 5) (w % 5)

/-- Pairwise non-adjacency check: no two raw vertices are adjacent. -/
def checkPairwiseRaw : Bool :=
  rawList.all fun v =>
    rawList.all fun w =>
      v == w || !adjRaw v w

/-! ## Computational verification -/

theorem checkPairwiseRaw_eq : checkPairwiseRaw = true := by native_decide

/-! ## Soundness bridge -/

/-- `digitClose` matches "equal or adjacent on E_{5/2}" for digits < 5.
    Verified by exhaustive check over all 25 pairs. -/
def checkDigitBridge : Bool :=
  (List.range 5).all fun a =>
    (List.range 5).all fun b =>
      digitClose a b ==
        decide ((a : ZMod 5) = (b : ZMod 5) ∨
                (fractionGraph 5 2).Adj (a : ZMod 5) (b : ZMod 5))

theorem checkDigitBridge_eq : checkDigitBridge = true := by native_decide

theorem digitClose_iff (a b : ℕ) (ha : a < 5) (hb : b < 5) :
    digitClose a b =
      decide ((a : ZMod 5) = (b : ZMod 5) ∨
              (fractionGraph 5 2).Adj (a : ZMod 5) (b : ZMod 5)) := by
  have h := checkDigitBridge_eq
  simp only [checkDigitBridge, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  exact h a ha b hb

theorem digitClose_of_eq_or_adj (a b : ℕ) (ha : a < 5) (hb : b < 5)
    (h : (a : ZMod 5) = (b : ZMod 5) ∨
         (fractionGraph 5 2).Adj (a : ZMod 5) (b : ZMod 5)) :
    digitClose a b = true := by
  rw [digitClose_iff a b ha hb]; simp [h]

/-- All raw vertices have all digits < 5. -/
theorem rawList_digits_valid (v : ℕ) (_ : v ∈ rawList) :
    v / 5 % 5 < 5 ∧ v % 5 < 5 :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

/-- Strong product adjacency implies raw adjacency for valid encodings. -/
theorem adj_implies_adjRaw (v w : ℕ)
    (hv : v / 5 % 5 < 5 ∧ v % 5 < 5)
    (hw : w / 5 % 5 < 5 ∧ w % 5 < 5)
    (hadj : (strongPower (fractionGraph 5 2) 2).Adj
      (decodeVertex v) (decodeVertex w)) :
    adjRaw v w = true := by
  obtain ⟨hne, hcoord⟩ := hadj
  simp only [adjRaw, Bool.and_eq_true, bne_iff_ne]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro heq; apply hne; subst heq; rfl
  · have h0 := hcoord 0
    simp only [decodeVertex] at h0
    exact digitClose_of_eq_or_adj _ _ hv.1 hw.1 h0
  · have h1 := hcoord 1
    simp only [decodeVertex] at h1
    exact digitClose_of_eq_or_adj _ _ hv.2 hw.2 h1

/-! ## Combining raw check with bridge -/

theorem not_adjRaw_of_mem (v w : ℕ) (hv : v ∈ rawList) (hw : w ∈ rawList)
    (hne : v ≠ w) : adjRaw v w = false := by
  have h := checkPairwiseRaw_eq
  simp only [checkPairwiseRaw, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at h
  have := h v hv w hw
  simp only [hne, false_or] at this
  exact this

/-- The pairwise non-adjacency theorem in E_{5/2}^{⊠2}. -/
theorem pairwise_nonadj : vertexList.Pairwise
    (fun u v => ¬(strongPower (fractionGraph 5 2) 2).Adj u v) := by
  change (rawList.map decodeVertex).Pairwise _
  rw [List.pairwise_map]
  have hnodup : rawList.Nodup := by native_decide
  apply hnodup.pairwise_of_set_pairwise
  intro a ha b hb hne hadj
  have h1 : adjRaw a b = true :=
    adj_implies_adjRaw a b (rawList_digits_valid a ha) (rawList_digits_valid b hb) hadj
  have h2 : adjRaw a b = false := not_adjRaw_of_mem a b ha hb hne
  exact absurd h1 (by simp [h2])

/-! ## Independence in E_{5/2}^{⊠2} -/

theorem vertexList_nodup : vertexList.Nodup := by native_decide

theorem vertexList_length : vertexList.length = 5 := by native_decide

def finset5 : Finset (Fin 2 → ZMod 5) :=
  ⟨↑vertexList, Multiset.coe_nodup.mpr vertexList_nodup⟩

theorem finset5_card : finset5.card = 5 := by
  simp [finset5, Multiset.coe_card, vertexList_length]

theorem finset5_isIndepSet : (strongPower (fractionGraph 5 2) 2).IsIndepSet
    (↑finset5 : Set (Fin 2 → ZMod 5)) := by
  intro a ha b hb hab
  have ha' : a ∈ vertexList := by
    simpa [finset5, Finset.mem_mk, Multiset.mem_coe] using ha
  have hb' : b ∈ vertexList := by
    simpa [finset5, Finset.mem_mk, Multiset.mem_coe] using hb
  have hsym : Symmetric (fun u v : Fin 2 → ZMod 5 =>
      ¬(strongPower (fractionGraph 5 2) 2).Adj u v) := by
    intro a b h hadj; exact h hadj.symm
  exact pairwise_nonadj.forall hsym ha' hb' hab

/-! ## Shannon capacity bound -/

theorem C5_2_indepNum_bound :
    (strongPower (fractionGraph 5 2) 2).indepNum ≥ 5 := by
  have h := SimpleGraph.IsIndepSet.card_le_indepNum finset5_isIndepSet
  rw [finset5_card] at h; exact h

theorem shannonCapacity_cycleGraph_5_lower :
    shannonCapacity (SimpleGraph.cycleGraph 5) ≥ (5 : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [shannonCapacity_iso (cycleGraph_iso_fractionGraph_two 5 (by norm_num))]
  calc shannonCapacity (fractionGraph 5 2)
      ≥ ((strongPower (fractionGraph 5 2) 2).indepNum : ℝ) ^ ((1 : ℝ) / 2) :=
        shannonCapacity_ge_root _ 2 (by norm_num)
    _ ≥ (5 : ℝ) ^ ((1 : ℝ) / 2) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast C5_2_indepNum_bound

end C5Bound
