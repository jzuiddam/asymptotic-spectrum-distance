/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shannon Capacity Lower Bound for C₁₁

Proves Θ(C₁₁) ≥ 148^{1/3} ≈ 5.289 using an orbit construction in E_{148/27}^{⊠3}.

## Architecture

Following the pattern from C15ThirdPower.lean:
1. **Computation**: verify pairwise non-adjacency of 148 orbit vertices in E_{148/27}^{⊠3}
   via `native_decide` on raw ℕ encodings.
2. **Soundness bridge**: prove graph adjacency implies raw adjacency
   (21,904-case `native_decide` + coordinate-wise argument).
3. **Transfer**: use cohomomorphism E_{148/27} → E_{11/2} = C₁₁ (since 148/27 ≤ 11/2)
   and strong power lifting to get α(C₁₁³) ≥ 148.

The orbit {t · (1, 11, 121) mod 148 : t = 0, ..., 147} gives 148 vertices in (ℤ/148ℤ)³.
These are independent in E_{148/27}^{⊠3} and transfer to E_{11/2}^{⊠3} via the
fraction graph cohomomorphism (148 · 2 ≤ 11 · 27, i.e. 296 ≤ 297).

## Main results

- `C11_3_indepNum_bound`: `(strongPower (fractionGraph 11 2) 3).indepNum ≥ 148`
- `shannonCapacity_cycleGraph_11_lower`:
    `shannonCapacity (SimpleGraph.cycleGraph 11) ≥ (148 : ℝ) ^ ((1 : ℝ) / 3)`
-/
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import Mathlib.Data.Set.Pairwise.List

open ShannonCapacity

set_option linter.style.nativeDecide false

namespace C11Bound

/-! ## Data -/

/-- Decode a raw ℕ to a vertex in (ZMod 148)^3.
    Encoding: v = a * 21904 + b * 148 + c with a, b, c < 148. -/
def decodeVertex (v : ℕ) : Fin 3 → ZMod 148 :=
  fun i => match i with
    | 0 => (v / 21904 % 148 : ℕ)
    | 1 => (v / 148 % 148 : ℕ)
    | 2 => (v % 148 : ℕ)

/-- The 148 orbit vertices {t · (1, 11, 121) mod 148 : t = 0, ..., 147}
    encoded as raw natural numbers (base-148 representation). -/
def rawList : List ℕ :=
  (List.range 148).map fun t =>
    (t % 148) * 21904 + ((11 * t) % 148) * 148 + ((121 * t) % 148)

def vertexList : List (Fin 3 → ZMod 148) :=
  rawList.map decodeVertex

/-! ## Raw adjacency check for E_{148/27}^{⊠3} -/

/-- Raw circular distance between two values modulo 148. -/
def distModRaw (a b : ℕ) : ℕ :=
  let diff := if a ≥ b then a - b else b - a
  min diff (148 - diff)

/-- Check if two coordinates are "equal or adjacent" in E_{148/27}:
    distMod 148 a b < 27 (which includes a = b since distMod = 0). -/
def digitClose (a b : ℕ) : Bool :=
  distModRaw a b < 27

/-- Raw adjacency in E_{148/27}^{⊠3}. -/
def adjRaw (v w : ℕ) : Bool :=
  v != w &&
  digitClose (v / 21904 % 148) (w / 21904 % 148) &&
  digitClose (v / 148 % 148) (w / 148 % 148) &&
  digitClose (v % 148) (w % 148)

/-- Pairwise non-adjacency check: no two raw vertices are adjacent. -/
def checkPairwiseRaw : Bool :=
  rawList.all fun v =>
    rawList.all fun w =>
      v == w || !adjRaw v w

/-! ## Computational verification -/

theorem checkPairwiseRaw_eq : checkPairwiseRaw = true := by native_decide

/-! ## Soundness bridge: raw check → graph-theoretic independence

We connect `adjRaw` to the graph adjacency via a `native_decide`
(21,904 cases) at the coordinate level.
-/

/-- `digitClose` matches "equal or adjacent on E_{148/27}" for digits < 148.
    Verified by exhaustive check over all 21,904 pairs. -/
def checkDigitBridge : Bool :=
  (List.range 148).all fun a =>
    (List.range 148).all fun b =>
      digitClose a b ==
        decide ((a : ZMod 148) = (b : ZMod 148) ∨
                (fractionGraph 148 27).Adj (a : ZMod 148) (b : ZMod 148))

theorem checkDigitBridge_eq : checkDigitBridge = true := by native_decide

theorem digitClose_iff (a b : ℕ) (ha : a < 148) (hb : b < 148) :
    digitClose a b =
      decide ((a : ZMod 148) = (b : ZMod 148) ∨
              (fractionGraph 148 27).Adj (a : ZMod 148) (b : ZMod 148)) := by
  have h := checkDigitBridge_eq
  simp only [checkDigitBridge, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  exact h a ha b hb

theorem digitClose_of_eq_or_adj (a b : ℕ) (ha : a < 148) (hb : b < 148)
    (h : (a : ZMod 148) = (b : ZMod 148) ∨
         (fractionGraph 148 27).Adj (a : ZMod 148) (b : ZMod 148)) :
    digitClose a b = true := by
  rw [digitClose_iff a b ha hb]; simp [h]

/-- All raw vertices have all digits < 148. -/
theorem rawList_digits_valid (v : ℕ) (_ : v ∈ rawList) :
    v / 21904 % 148 < 148 ∧ v / 148 % 148 < 148 ∧ v % 148 < 148 :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
   Nat.mod_lt _ (by norm_num)⟩

/-- Strong product adjacency implies raw adjacency for valid encodings. -/
theorem adj_implies_adjRaw (v w : ℕ)
    (hv : v / 21904 % 148 < 148 ∧ v / 148 % 148 < 148 ∧ v % 148 < 148)
    (hw : w / 21904 % 148 < 148 ∧ w / 148 % 148 < 148 ∧ w % 148 < 148)
    (hadj : (strongPower (fractionGraph 148 27) 3).Adj
      (decodeVertex v) (decodeVertex w)) :
    adjRaw v w = true := by
  obtain ⟨hne, hcoord⟩ := hadj
  simp only [adjRaw, Bool.and_eq_true, bne_iff_ne]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- v ≠ w
    intro heq; apply hne; subst heq; rfl
  · -- coordinate 0
    have h0 := hcoord 0
    simp only [decodeVertex] at h0
    exact digitClose_of_eq_or_adj _ _ hv.1 hw.1 h0
  · -- coordinate 1
    have h1 := hcoord 1
    simp only [decodeVertex] at h1
    exact digitClose_of_eq_or_adj _ _ hv.2.1 hw.2.1 h1
  · -- coordinate 2
    have h2 := hcoord 2
    simp only [decodeVertex] at h2
    exact digitClose_of_eq_or_adj _ _ hv.2.2 hw.2.2 h2

/-! ## Combining raw check with bridge -/

theorem not_adjRaw_of_mem (v w : ℕ) (hv : v ∈ rawList) (hw : w ∈ rawList)
    (hne : v ≠ w) : adjRaw v w = false := by
  have h := checkPairwiseRaw_eq
  simp only [checkPairwiseRaw, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at h
  have := h v hv w hw
  simp only [hne, false_or] at this
  exact this

/-- The pairwise non-adjacency theorem in E_{148/27}^{⊠3}. -/
theorem pairwise_nonadj : vertexList.Pairwise
    (fun u v => ¬(strongPower (fractionGraph 148 27) 3).Adj u v) := by
  change (rawList.map decodeVertex).Pairwise _
  rw [List.pairwise_map]
  have hnodup : rawList.Nodup := by native_decide
  apply hnodup.pairwise_of_set_pairwise
  intro a ha b hb hne hadj
  have h1 : adjRaw a b = true :=
    adj_implies_adjRaw a b (rawList_digits_valid a ha) (rawList_digits_valid b hb) hadj
  have h2 : adjRaw a b = false := not_adjRaw_of_mem a b ha hb hne
  exact absurd h1 (by simp [h2])

/-! ## Independence in E_{148/27}^{⊠3} -/

theorem vertexList_nodup : vertexList.Nodup := by native_decide

theorem vertexList_length : vertexList.length = 148 := by native_decide

def finset148 : Finset (Fin 3 → ZMod 148) :=
  ⟨↑vertexList, Multiset.coe_nodup.mpr vertexList_nodup⟩

theorem finset148_card : finset148.card = 148 := by
  simp [finset148, Multiset.coe_card, vertexList_length]

theorem finset148_isIndepSet : (strongPower (fractionGraph 148 27) 3).IsIndepSet
    (↑finset148 : Set (Fin 3 → ZMod 148)) := by
  intro a ha b hb hab
  have ha' : a ∈ vertexList := by
    simpa [finset148, Finset.mem_mk, Multiset.mem_coe] using ha
  have hb' : b ∈ vertexList := by
    simpa [finset148, Finset.mem_mk, Multiset.mem_coe] using hb
  have hsym : Symmetric (fun u v : Fin 3 → ZMod 148 =>
      ¬(strongPower (fractionGraph 148 27) 3).Adj u v) := by
    intro a b h hadj; exact h hadj.symm
  exact pairwise_nonadj.forall hsym ha' hb' hab

/-! ## Transfer: E_{148/27}^{⊠3} → E_{11/2}^{⊠3} via cohomomorphism

Since 148/27 ≤ 11/2 (equivalently, 148·2 = 296 ≤ 297 = 11·27), there exists a
cohomomorphism from E_{148/27} to E_{11/2}. This lifts to the strong powers,
giving α(E_{11/2}^{⊠3}) ≥ α(E_{148/27}^{⊠3}) ≥ 148.
-/

/-- The main independence number bound for E_{11/2}^{⊠3}. -/
theorem C11_3_indepNum_bound :
    (strongPower (fractionGraph 11 2) 3).indepNum ≥ 148 := by
  -- Step 1: Get cohomomorphism E_{148/27} → E_{11/2}
  have hcohom := fractionGraph_cohomomorphism 148 27 11 2
    (by norm_num) (by norm_num : (148 : ℚ) / 27 ≤ (11 : ℚ) / 2)
  -- hcohom : Cohom (fractionGraph 148 27) (fractionGraph 11 2)
  -- Step 2: Lift cohomomorphism to strong powers
  have hcohom_power := Cohom.strongPower hcohom 3
  -- Step 3: Apply alpha monotonicity
  obtain ⟨f_power, hf_power⟩ := hcohom_power
  have halpha_le : (strongPower (fractionGraph 148 27) 3).indepNum ≤
      (strongPower (fractionGraph 11 2) 3).indepNum :=
    SimpleGraph.independenceNumber_le_of_cohomomorphism _ _ f_power hf_power
  -- Step 4: α(E_{148/27}^{⊠3}) ≥ 148 from our independent set
  have halpha_ge : (strongPower (fractionGraph 148 27) 3).indepNum ≥ 148 := by
    have h := SimpleGraph.IsIndepSet.card_le_indepNum finset148_isIndepSet
    rw [finset148_card] at h; exact h
  -- Combine
  omega

theorem shannonCapacity_cycleGraph_11_lower :
    shannonCapacity (SimpleGraph.cycleGraph 11) ≥ (148 : ℝ) ^ ((1 : ℝ) / 3) := by
  rw [shannonCapacity_iso (cycleGraph_iso_fractionGraph_two 11 (by norm_num))]
  calc shannonCapacity (fractionGraph 11 2)
      ≥ ((strongPower (fractionGraph 11 2) 3).indepNum : ℝ) ^ ((1 : ℝ) / 3) :=
        shannonCapacity_ge_root _ 3 (by norm_num)
    _ ≥ (148 : ℝ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast C11_3_indepNum_bound

end C11Bound
