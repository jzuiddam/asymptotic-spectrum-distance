/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shannon Capacity Lower Bound for C₁₃

Proves Θ(C₁₃) ≥ 247^{1/3} ≈ 6.274 using an orbit construction in E_{247/38}^{⊠3}.

## Architecture

Following the pattern from C11Bound.lean:
1. **Computation**: verify pairwise non-adjacency of 247 orbit vertices in E_{247/38}^{⊠3}
   via `native_decide` on raw ℕ encodings.
2. **Soundness bridge**: prove graph adjacency implies raw adjacency
   (61,009-case `native_decide` + coordinate-wise argument).
3. **Transfer**: use cohomomorphism E_{247/38} → E_{13/2} = C₁₃ (since 247/38 ≤ 13/2)
   and strong power lifting to get α(C₁₃³) ≥ 247.

The orbit {t · (1, 19, 117) mod 247 : t = 0, ..., 246} gives 247 vertices in (ℤ/247ℤ)³.
These are independent in E_{247/38}^{⊠3} and transfer to E_{13/2}^{⊠3} via the
fraction graph cohomomorphism (247 · 2 = 494 ≤ 494 = 13 · 38).

## Main results

- `C13_3_indepNum_bound`: `(strongPower (fractionGraph 13 2) 3).indepNum ≥ 247`
- `shannonCapacity_cycleGraph_13_lower`:
    `shannonCapacity (SimpleGraph.cycleGraph 13) ≥ (247 : ℝ) ^ ((1 : ℝ) / 3)`
-/
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import Mathlib.Data.Set.Pairwise.List

open ShannonCapacity

set_option linter.style.nativeDecide false

namespace C13Bound

/-! ## Data -/

/-- Decode a raw ℕ to a vertex in (ZMod 247)^3.
    Encoding: v = a * 61009 + b * 247 + c with a, b, c < 247. -/
def decodeVertex (v : ℕ) : Fin 3 → ZMod 247 :=
  fun i => match i with
    | 0 => (v / 61009 % 247 : ℕ)
    | 1 => (v / 247 % 247 : ℕ)
    | 2 => (v % 247 : ℕ)

/-- The 247 orbit vertices {t · (1, 19, 117) mod 247 : t = 0, ..., 246}
    encoded as raw natural numbers (base-247 representation). -/
def rawList : List ℕ :=
  (List.range 247).map fun t =>
    (t % 247) * 61009 + ((19 * t) % 247) * 247 + ((117 * t) % 247)

def vertexList : List (Fin 3 → ZMod 247) :=
  rawList.map decodeVertex

/-! ## Raw adjacency check for E_{247/38}^{⊠3} -/

/-- Raw circular distance between two values modulo 247. -/
def distModRaw (a b : ℕ) : ℕ :=
  let diff := if a ≥ b then a - b else b - a
  min diff (247 - diff)

/-- Check if two coordinates are "equal or adjacent" in E_{247/38}:
    distMod 247 a b < 38 (which includes a = b since distMod = 0). -/
def digitClose (a b : ℕ) : Bool :=
  distModRaw a b < 38

/-- Raw adjacency in E_{247/38}^{⊠3}. -/
def adjRaw (v w : ℕ) : Bool :=
  v != w &&
  digitClose (v / 61009 % 247) (w / 61009 % 247) &&
  digitClose (v / 247 % 247) (w / 247 % 247) &&
  digitClose (v % 247) (w % 247)

/-- Pairwise non-adjacency check: no two raw vertices are adjacent. -/
def checkPairwiseRaw : Bool :=
  rawList.all fun v =>
    rawList.all fun w =>
      v == w || !adjRaw v w

/-! ## Computational verification -/

theorem checkPairwiseRaw_eq : checkPairwiseRaw = true := by native_decide

/-! ## Soundness bridge: raw check → graph-theoretic independence

We connect `adjRaw` to the graph adjacency via a `native_decide`
(61,009 cases) at the coordinate level.
-/

/-- `digitClose` matches "equal or adjacent on E_{247/38}" for digits < 247.
    Verified by exhaustive check over all 61,009 pairs. -/
def checkDigitBridge : Bool :=
  (List.range 247).all fun a =>
    (List.range 247).all fun b =>
      digitClose a b ==
        decide ((a : ZMod 247) = (b : ZMod 247) ∨
                (fractionGraph 247 38).Adj (a : ZMod 247) (b : ZMod 247))

theorem checkDigitBridge_eq : checkDigitBridge = true := by native_decide

theorem digitClose_iff (a b : ℕ) (ha : a < 247) (hb : b < 247) :
    digitClose a b =
      decide ((a : ZMod 247) = (b : ZMod 247) ∨
              (fractionGraph 247 38).Adj (a : ZMod 247) (b : ZMod 247)) := by
  have h := checkDigitBridge_eq
  simp only [checkDigitBridge, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  exact h a ha b hb

theorem digitClose_of_eq_or_adj (a b : ℕ) (ha : a < 247) (hb : b < 247)
    (h : (a : ZMod 247) = (b : ZMod 247) ∨
         (fractionGraph 247 38).Adj (a : ZMod 247) (b : ZMod 247)) :
    digitClose a b = true := by
  rw [digitClose_iff a b ha hb]; simp [h]

/-- All raw vertices have all digits < 247. -/
theorem rawList_digits_valid (v : ℕ) (_ : v ∈ rawList) :
    v / 61009 % 247 < 247 ∧ v / 247 % 247 < 247 ∧ v % 247 < 247 :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
   Nat.mod_lt _ (by norm_num)⟩

/-- Strong product adjacency implies raw adjacency for valid encodings. -/
theorem adj_implies_adjRaw (v w : ℕ)
    (hv : v / 61009 % 247 < 247 ∧ v / 247 % 247 < 247 ∧ v % 247 < 247)
    (hw : w / 61009 % 247 < 247 ∧ w / 247 % 247 < 247 ∧ w % 247 < 247)
    (hadj : (strongPower (fractionGraph 247 38) 3).Adj
      (decodeVertex v) (decodeVertex w)) :
    adjRaw v w = true := by
  obtain ⟨hne, hcoord⟩ := hadj
  simp only [adjRaw, Bool.and_eq_true, bne_iff_ne]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro heq; apply hne; subst heq; rfl
  · have h0 := hcoord 0
    simp only [decodeVertex] at h0
    exact digitClose_of_eq_or_adj _ _ hv.1 hw.1 h0
  · have h1 := hcoord 1
    simp only [decodeVertex] at h1
    exact digitClose_of_eq_or_adj _ _ hv.2.1 hw.2.1 h1
  · have h2 := hcoord 2
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

/-- The pairwise non-adjacency theorem in E_{247/38}^{⊠3}. -/
theorem pairwise_nonadj : vertexList.Pairwise
    (fun u v => ¬(strongPower (fractionGraph 247 38) 3).Adj u v) := by
  change (rawList.map decodeVertex).Pairwise _
  rw [List.pairwise_map]
  have hnodup : rawList.Nodup := by native_decide
  apply hnodup.pairwise_of_set_pairwise
  intro a ha b hb hne hadj
  have h1 : adjRaw a b = true :=
    adj_implies_adjRaw a b (rawList_digits_valid a ha) (rawList_digits_valid b hb) hadj
  have h2 : adjRaw a b = false := not_adjRaw_of_mem a b ha hb hne
  exact absurd h1 (by simp [h2])

/-! ## Independence in E_{247/38}^{⊠3} -/

theorem vertexList_nodup : vertexList.Nodup := by native_decide

theorem vertexList_length : vertexList.length = 247 := by native_decide

def finset247 : Finset (Fin 3 → ZMod 247) :=
  ⟨↑vertexList, Multiset.coe_nodup.mpr vertexList_nodup⟩

theorem finset247_card : finset247.card = 247 := by
  simp [finset247, Multiset.coe_card, vertexList_length]

theorem finset247_isIndepSet : (strongPower (fractionGraph 247 38) 3).IsIndepSet
    (↑finset247 : Set (Fin 3 → ZMod 247)) := by
  intro a ha b hb hab
  have ha' : a ∈ vertexList := by
    simpa [finset247, Finset.mem_mk, Multiset.mem_coe] using ha
  have hb' : b ∈ vertexList := by
    simpa [finset247, Finset.mem_mk, Multiset.mem_coe] using hb
  have hsym : Symmetric (fun u v : Fin 3 → ZMod 247 =>
      ¬(strongPower (fractionGraph 247 38) 3).Adj u v) := by
    intro a b h hadj; exact h hadj.symm
  exact pairwise_nonadj.forall hsym ha' hb' hab

/-! ## Transfer: E_{247/38}^{⊠3} → E_{13/2}^{⊠3} via cohomomorphism

Since 247/38 ≤ 13/2 (equivalently, 247·2 = 494 ≤ 494 = 13·38), there exists a
cohomomorphism from E_{247/38} to E_{13/2}. This lifts to the strong powers,
giving α(E_{13/2}^{⊠3}) ≥ α(E_{247/38}^{⊠3}) ≥ 247.
-/

/-- The main independence number bound for E_{13/2}^{⊠3}. -/
theorem C13_3_indepNum_bound :
    (strongPower (fractionGraph 13 2) 3).indepNum ≥ 247 := by
  -- Step 1: Get cohomomorphism E_{247/38} → E_{13/2}
  have hcohom := fractionGraph_cohomomorphism 247 38 13 2
    (by norm_num) (by norm_num : (247 : ℚ) / 38 ≤ (13 : ℚ) / 2)
  -- Step 2: Lift cohomomorphism to strong powers
  have hcohom_power := Cohom.strongPower hcohom 3
  -- Step 3: Apply alpha monotonicity
  obtain ⟨f_power, hf_power⟩ := hcohom_power
  have halpha_le : (strongPower (fractionGraph 247 38) 3).indepNum ≤
      (strongPower (fractionGraph 13 2) 3).indepNum :=
    SimpleGraph.independenceNumber_le_of_cohomomorphism _ _ f_power hf_power
  -- Step 4: α(E_{247/38}^{⊠3}) ≥ 247 from our independent set
  have halpha_ge : (strongPower (fractionGraph 247 38) 3).indepNum ≥ 247 := by
    have h := SimpleGraph.IsIndepSet.card_le_indepNum finset247_isIndepSet
    rw [finset247_card] at h; exact h
  -- Combine
  omega

theorem shannonCapacity_cycleGraph_13_lower :
    shannonCapacity (SimpleGraph.cycleGraph 13) ≥ (247 : ℝ) ^ ((1 : ℝ) / 3) := by
  rw [shannonCapacity_iso (cycleGraph_iso_fractionGraph_two 13 (by norm_num))]
  calc shannonCapacity (fractionGraph 13 2)
      ≥ ((strongPower (fractionGraph 13 2) 3).indepNum : ℝ) ^ ((1 : ℝ) / 3) :=
        shannonCapacity_ge_root _ 3 (by norm_num)
    _ ≥ (247 : ℝ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast C13_3_indepNum_bound

end C13Bound
