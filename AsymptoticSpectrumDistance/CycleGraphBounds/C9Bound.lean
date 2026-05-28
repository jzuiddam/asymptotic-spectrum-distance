/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shannon Capacity Lower Bound for C₉

Proves Θ(C₉) ≥ 81^{1/3} ≈ 4.327 using an orbit construction in E_{9/2}^{⊠3}.

## Architecture

Similar to C5Bound.lean (H = G, no cohomomorphism needed):
1. **Computation**: verify pairwise non-adjacency of 81 orbit vertices in E_{9/2}^{⊠3}
   via `native_decide` on raw ℕ encodings.
2. **Soundness bridge**: prove graph adjacency implies raw adjacency
   (81-case `native_decide` + coordinate-wise argument).
3. **Direct bound**: α(E_{9/2}^{⊠3}) ≥ 81 immediately gives Θ(C₉) ≥ 81^{1/3}.

The orbit {s · (1,0,2) + t · (0,1,4) : s,t ∈ ℤ₉} gives 81 = 9² vertices in (ℤ/9ℤ)³.
Since E_{9/2} = C₉, no cohomomorphism transfer is needed.

## Main results

- `C9_3_indepNum_bound`: `(strongPower (fractionGraph 9 2) 3).indepNum ≥ 81`
- `shannonCapacity_cycleGraph_9_lower`:
    `shannonCapacity (SimpleGraph.cycleGraph 9) ≥ (81 : ℝ) ^ ((1 : ℝ) / 3)`
-/
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import Mathlib.Data.Set.Pairwise.List

open ShannonCapacity

set_option linter.style.nativeDecide false

namespace C9Bound

/-! ## Data -/

/-- Decode a raw ℕ to a vertex in (ZMod 9)^3.
    Encoding: v = a * 81 + b * 9 + c with a, b, c < 9. -/
def decodeVertex (v : ℕ) : Fin 3 → ZMod 9 :=
  fun i => match i with
    | 0 => (v / 81 % 9 : ℕ)
    | 1 => (v / 9 % 9 : ℕ)
    | 2 => (v % 9 : ℕ)

/-- The 81 orbit vertices {s · (1,0,2) + t · (0,1,4) : s,t ∈ ℤ₉}
    encoded as raw natural numbers (base-9 representation). -/
def rawList : List ℕ :=
  (List.range 9).flatMap fun s =>
    (List.range 9).map fun t =>
      (s % 9) * 81 + (t % 9) * 9 + ((2 * s + 4 * t) % 9)

def vertexList : List (Fin 3 → ZMod 9) :=
  rawList.map decodeVertex

/-! ## Raw adjacency check for E_{9/2}^{⊠3} -/

/-- Raw circular distance between two values modulo 9. -/
def distModRaw (a b : ℕ) : ℕ :=
  let diff := if a ≥ b then a - b else b - a
  min diff (9 - diff)

/-- Check if two coordinates are "equal or adjacent" in E_{9/2}:
    distMod 9 a b < 2 (which includes a = b since distMod = 0). -/
def digitClose (a b : ℕ) : Bool :=
  distModRaw a b < 2

/-- Raw adjacency in E_{9/2}^{⊠3}. -/
def adjRaw (v w : ℕ) : Bool :=
  v != w &&
  digitClose (v / 81 % 9) (w / 81 % 9) &&
  digitClose (v / 9 % 9) (w / 9 % 9) &&
  digitClose (v % 9) (w % 9)

/-- Pairwise non-adjacency check: no two raw vertices are adjacent. -/
def checkPairwiseRaw : Bool :=
  rawList.all fun v =>
    rawList.all fun w =>
      v == w || !adjRaw v w

/-! ## Computational verification -/

theorem checkPairwiseRaw_eq : checkPairwiseRaw = true := by native_decide

/-! ## Soundness bridge: raw check → graph-theoretic independence

We connect `adjRaw` to the graph adjacency via a `native_decide`
(81 cases) at the coordinate level.
-/

/-- `digitClose` matches "equal or adjacent on E_{9/2}" for digits < 9.
    Verified by exhaustive check over all 81 pairs. -/
def checkDigitBridge : Bool :=
  (List.range 9).all fun a =>
    (List.range 9).all fun b =>
      digitClose a b ==
        decide ((a : ZMod 9) = (b : ZMod 9) ∨
                (fractionGraph 9 2).Adj (a : ZMod 9) (b : ZMod 9))

theorem checkDigitBridge_eq : checkDigitBridge = true := by native_decide

theorem digitClose_iff (a b : ℕ) (ha : a < 9) (hb : b < 9) :
    digitClose a b =
      decide ((a : ZMod 9) = (b : ZMod 9) ∨
              (fractionGraph 9 2).Adj (a : ZMod 9) (b : ZMod 9)) := by
  have h := checkDigitBridge_eq
  simp only [checkDigitBridge, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  exact h a ha b hb

theorem digitClose_of_eq_or_adj (a b : ℕ) (ha : a < 9) (hb : b < 9)
    (h : (a : ZMod 9) = (b : ZMod 9) ∨
         (fractionGraph 9 2).Adj (a : ZMod 9) (b : ZMod 9)) :
    digitClose a b = true := by
  rw [digitClose_iff a b ha hb]; simp [h]

/-- All raw vertices have all digits < 9. -/
theorem rawList_digits_valid (v : ℕ) (_ : v ∈ rawList) :
    v / 81 % 9 < 9 ∧ v / 9 % 9 < 9 ∧ v % 9 < 9 :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
   Nat.mod_lt _ (by norm_num)⟩

/-- Strong product adjacency implies raw adjacency for valid encodings. -/
theorem adj_implies_adjRaw (v w : ℕ)
    (hv : v / 81 % 9 < 9 ∧ v / 9 % 9 < 9 ∧ v % 9 < 9)
    (hw : w / 81 % 9 < 9 ∧ w / 9 % 9 < 9 ∧ w % 9 < 9)
    (hadj : (strongPower (fractionGraph 9 2) 3).Adj
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

/-- The pairwise non-adjacency theorem in E_{9/2}^{⊠3}. -/
theorem pairwise_nonadj : vertexList.Pairwise
    (fun u v => ¬(strongPower (fractionGraph 9 2) 3).Adj u v) := by
  change (rawList.map decodeVertex).Pairwise _
  rw [List.pairwise_map]
  have hnodup : rawList.Nodup := by native_decide
  apply hnodup.pairwise_of_set_pairwise
  intro a ha b hb hne hadj
  have h1 : adjRaw a b = true :=
    adj_implies_adjRaw a b (rawList_digits_valid a ha) (rawList_digits_valid b hb) hadj
  have h2 : adjRaw a b = false := not_adjRaw_of_mem a b ha hb hne
  exact absurd h1 (by simp [h2])

/-! ## Independence in E_{9/2}^{⊠3} -/

theorem vertexList_nodup : vertexList.Nodup := by native_decide

theorem vertexList_length : vertexList.length = 81 := by native_decide

def finset81 : Finset (Fin 3 → ZMod 9) :=
  ⟨↑vertexList, Multiset.coe_nodup.mpr vertexList_nodup⟩

theorem finset81_card : finset81.card = 81 := by
  simp [finset81, Multiset.coe_card, vertexList_length]

theorem finset81_isIndepSet : (strongPower (fractionGraph 9 2) 3).IsIndepSet
    (↑finset81 : Set (Fin 3 → ZMod 9)) := by
  intro a ha b hb hab
  have ha' : a ∈ vertexList := by
    simpa [finset81, Finset.mem_mk, Multiset.mem_coe] using ha
  have hb' : b ∈ vertexList := by
    simpa [finset81, Finset.mem_mk, Multiset.mem_coe] using hb
  have hsym : Symmetric (fun u v : Fin 3 → ZMod 9 =>
      ¬(strongPower (fractionGraph 9 2) 3).Adj u v) := by
    intro a b h hadj; exact h hadj.symm
  exact pairwise_nonadj.forall hsym ha' hb' hab

/-! ## Shannon capacity bound (no cohomomorphism needed since H = G) -/

/-- The main independence number bound for E_{9/2}^{⊠3}. -/
theorem C9_3_indepNum_bound :
    (strongPower (fractionGraph 9 2) 3).indepNum ≥ 81 := by
  have h := SimpleGraph.IsIndepSet.card_le_indepNum finset81_isIndepSet
  rw [finset81_card] at h; exact h

theorem shannonCapacity_cycleGraph_9_lower :
    shannonCapacity (SimpleGraph.cycleGraph 9) ≥ (81 : ℝ) ^ ((1 : ℝ) / 3) := by
  rw [shannonCapacity_iso (cycleGraph_iso_fractionGraph_two 9 (by norm_num))]
  calc shannonCapacity (fractionGraph 9 2)
      ≥ ((strongPower (fractionGraph 9 2) 3).indepNum : ℝ) ^ ((1 : ℝ) / 3) :=
        shannonCapacity_ge_root _ 3 (by norm_num)
    _ ≥ (81 : ℝ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast C9_3_indepNum_bound

end C9Bound
