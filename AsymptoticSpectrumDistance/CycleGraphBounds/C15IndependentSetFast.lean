/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Fast Independent Set Verification for C_15^{⊠4}

Verifies that the 2842 vertices from Appendix B form an independent set in C₁₅^{⊠4},
proving Theorem 6.2: α(C₁₅^{⊠4}) ≥ 2842 and Θ(C₁₅) ≥ 2842^{1/4} ≈ 7.301.

## Architecture

The key idea is to separate the computational check from the mathematical proof:

1. **Computation**: verify pairwise non-adjacency on raw ℕ encodings via `native_decide`.
2. **Soundness bridge**: a small proof (225-case `native_decide` + coordinate-wise argument)
   shows that graph-theoretic adjacency in C₁₅^{⊠4} implies raw adjacency.
3. **Contradiction**: if two vertices were adjacent in the graph, they would be raw-adjacent,
   but the computational check says no two are — contradiction.

This avoids the expensive `native_decide` on `ZMod 15` function-type equality that
the now-removed direct approach used.

## Verification strategies benchmarked

Three raw-ℕ checkers are included for comparison. Interpreter timings (`#eval`) on
n = 2842 vertices, each with 80 neighbors in C₁₅^{⊠4}:

| # | Approach                      | Time      | Relative |
|---|-------------------------------|-----------|----------|
| 0 | Direct ZMod (removed; was the slow path) | 115,902ms | 1×       |
| 1 | O(n²) raw ℕ pairwise          | 10,574ms  | 11×      |
| 2 | O(n×80) lookup table           | 358ms     | 324×     |
| 3 | O(n×80×log n) binary search    | 1,784ms   | 65×      |

Under `native_decide` (compiled), approaches 1–3 all build in ~64s (compilation-dominated)
vs ~161s for the removed approach 0. The soundness bridge uses approach 1 (`checkPairwiseRaw`).

## Main results

- `C15_4_indepNum_bound`: `(strongPower (fractionGraph 15 2) 4).indepNum ≥ 2842`
- `C15_4_indepNum_bound_cycle`: same in cycle-graph form (paper-API wrapper)
-/
import AsymptoticSpectrumDistance.CycleGraphBounds.C15Data
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import Mathlib.Data.Set.Pairwise.List

open ShannonCapacity C15Data

set_option linter.style.nativeDecide false
set_option linter.style.show false

/-! ## Approach 1: O(n²) on raw ℕ arithmetic -/

/-- Check if two base-15 digits are equal or adjacent on C₁₅ (distance < 2). -/
def digitEqOrAdj (a b : ℕ) : Bool :=
  a == b || (a + 1) % 15 == b || (b + 1) % 15 == a

/-- Raw adjacency check: are two base-15 encoded vertices adjacent in C₁₅^{⊠4}? -/
def adjRaw (v w : ℕ) : Bool :=
  v != w &&
  digitEqOrAdj (v / 3375 % 15) (w / 3375 % 15) &&
  digitEqOrAdj (v / 225 % 15) (w / 225 % 15) &&
  digitEqOrAdj (v / 15 % 15) (w / 15 % 15) &&
  digitEqOrAdj (v % 15) (w % 15)

/-- Pairwise check: no two raw vertices are adjacent. O(n²) but on raw ℕ. -/
def checkPairwiseRaw : Bool :=
  C15_4_rawList.all fun v =>
    C15_4_rawList.all fun w =>
      v == w || !adjRaw v w

/-! ### Benchmark 1: O(n²) raw arithmetic -/

theorem checkPairwiseRaw_eq : checkPairwiseRaw = true := by native_decide

/-! ## Approach 2: O(n×80) neighbor enumeration with lookup table -/

/-- Boolean lookup table of size 15⁴ = 50625. -/
def mkLookupTable (rawVerts : List ℕ) : Array Bool :=
  rawVerts.foldl (fun a v => if v < a.size then a.set! v true else a)
    (Array.mk (List.replicate 50625 false))

/-- For each vertex, enumerate all 80 neighbors and check none are in the set. -/
def checkIndepFast : Bool :=
  let lookup := mkLookupTable C15_4_rawList
  let offsets : List ℕ := [0, 1, 14]  -- 0, +1, -1 mod 15
  C15_4_rawList.all fun v =>
    let d0 := v / 3375
    let d1 := v / 225 % 15
    let d2 := v / 15 % 15
    let d3 := v % 15
    offsets.all fun δ0 =>
      offsets.all fun δ1 =>
        offsets.all fun δ2 =>
          offsets.all fun δ3 =>
            if δ0 == 0 && δ1 == 0 && δ2 == 0 && δ3 == 0 then true
            else
              let w := ((d0 + δ0) % 15) * 3375 + ((d1 + δ1) % 15) * 225 +
                       ((d2 + δ2) % 15) * 15 + ((d3 + δ3) % 15)
              !(lookup.getD w false)

/-! ### Benchmark 2: O(n×80) neighbor enumeration -/

theorem checkIndepFast_eq : checkIndepFast = true := by native_decide

/-! ## Approach 3: O(n × 80 × log n) sorted binary search -/

/-- Independence check using sorted array + binary search.
    Sorts the raw list, then for each vertex checks that none of its 80
    neighbors appear via `Array.binSearch`. O(n × 80 × log n). -/
def checkIndepSorted : Bool :=
  let sorted := (C15_4_rawList.mergeSort (· ≤ ·)).toArray
  let offsets : List Nat := [0, 1, 14]  -- 0, +1, -1 mod 15
  C15_4_rawList.all fun v =>
    let d0 := v / 3375
    let d1 := v / 225 % 15
    let d2 := v / 15 % 15
    let d3 := v % 15
    offsets.all fun δ0 =>
      offsets.all fun δ1 =>
        offsets.all fun δ2 =>
          offsets.all fun δ3 =>
            if δ0 == 0 && δ1 == 0 && δ2 == 0 && δ3 == 0 then true
            else
              let w := ((d0 + δ0) % 15) * 3375 + ((d1 + δ1) % 15) * 225 +
                       ((d2 + δ2) % 15) * 15 + ((d3 + δ3) % 15)
              (sorted.binSearch w (· < ·)).isNone

/-! ### Benchmark 3: O(n × 80 × log n) sorted binary search -/

theorem checkIndepSorted_eq : checkIndepSorted = true := by native_decide

/-! ## Soundness bridge: raw check → graph-theoretic independence

We connect `adjRaw` to the graph adjacency via a small `native_decide`
(225 cases) at the coordinate level.
-/

/-- `digitEqOrAdj` matches "equal or adjacent on C₁₅" for digits < 15.
    Verified by exhaustive check over all 225 pairs. -/
def checkDigitBridge : Bool :=
  (List.range 15).all fun a =>
    (List.range 15).all fun b =>
      digitEqOrAdj a b ==
        decide ((a : ZMod 15) = (b : ZMod 15) ∨
                (fractionGraph 15 2).Adj (a : ZMod 15) (b : ZMod 15))

theorem checkDigitBridge_eq : checkDigitBridge = true := by native_decide

theorem digitEqOrAdj_iff (a b : ℕ) (ha : a < 15) (hb : b < 15) :
    digitEqOrAdj a b =
      decide ((a : ZMod 15) = (b : ZMod 15) ∨
              (fractionGraph 15 2).Adj (a : ZMod 15) (b : ZMod 15)) := by
  have h := checkDigitBridge_eq
  simp only [checkDigitBridge, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  exact h a ha b hb

theorem digitEqOrAdj_of_eq_or_adj (a b : ℕ) (ha : a < 15) (hb : b < 15)
    (h : (a : ZMod 15) = (b : ZMod 15) ∨
         (fractionGraph 15 2).Adj (a : ZMod 15) (b : ZMod 15)) :
    digitEqOrAdj a b = true := by
  rw [digitEqOrAdj_iff a b ha hb]; simp [h]

/-- All raw vertices have all digits < 15 (trivially true since x % 15 < 15). -/
theorem rawList_digits_valid (v : ℕ) (_ : v ∈ C15_4_rawList) :
    v / 3375 % 15 < 15 ∧ v / 225 % 15 < 15 ∧ v / 15 % 15 < 15 ∧ v % 15 < 15 :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
   Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

/-- Strong product adjacency implies raw adjacency for valid encodings. -/
theorem adj_implies_adjRaw (v w : ℕ)
    (hv : v / 3375 % 15 < 15 ∧ v / 225 % 15 < 15 ∧ v / 15 % 15 < 15 ∧ v % 15 < 15)
    (hw : w / 3375 % 15 < 15 ∧ w / 225 % 15 < 15 ∧ w / 15 % 15 < 15 ∧ w % 15 < 15)
    (hadj : (strongPower (fractionGraph 15 2) 4).Adj (decodeVertex v) (decodeVertex w)) :
    adjRaw v w = true := by
  obtain ⟨hne, hcoord⟩ := hadj
  simp only [adjRaw, Bool.and_eq_true, bne_iff_ne]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- v ≠ w
    intro heq; apply hne; subst heq; rfl
  · -- coordinate 0: decodeVertex uses (v / 3375 : ZMod 15)
    have h0 := hcoord 0
    simp only [decodeVertex] at h0
    -- h0 : (v/3375 : ZMod 15) = (w/3375 : ZMod 15) ∨ Adj (v/3375 : ZMod 15) (w/3375 : ZMod 15)
    -- Need: digitEqOrAdj (v/3375%15) (w/3375%15) = true
    rw [← ZMod.natCast_mod (v / 3375) 15, ← ZMod.natCast_mod (w / 3375) 15] at h0
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.1 hw.1 h0
  · -- coordinate 1: decodeVertex already has (v / 225 % 15 : ZMod 15)
    have h1 := hcoord 1
    simp only [decodeVertex] at h1
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.2.1 hw.2.1 h1
  · -- coordinate 2
    have h2 := hcoord 2
    simp only [decodeVertex] at h2
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.2.2.1 hw.2.2.1 h2
  · -- coordinate 3
    have h3 := hcoord 3
    simp only [decodeVertex] at h3
    exact digitEqOrAdj_of_eq_or_adj _ _ hv.2.2.2 hw.2.2.2 h3

/-! ## Main result: combining the raw check with the bridge -/

theorem not_adjRaw_of_mem (v w : ℕ) (hv : v ∈ C15_4_rawList) (hw : w ∈ C15_4_rawList)
    (hne : v ≠ w) : adjRaw v w = false := by
  have h := checkPairwiseRaw_eq
  simp only [checkPairwiseRaw, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at h
  have := h v hv w hw
  simp only [hne, false_or] at this
  exact this

/-- The pairwise non-adjacency theorem, proven via raw arithmetic bridge. -/
theorem C15_4_pairwise_nonadj : C15_4_vertices.Pairwise
    (fun u v => ¬(strongPower (fractionGraph 15 2) 4).Adj u v) := by
  show (C15_4_rawList.map decodeVertex).Pairwise _
  rw [List.pairwise_map]
  have hnodup : C15_4_rawList.Nodup := by native_decide
  apply hnodup.pairwise_of_set_pairwise
  intro a ha b hb hne hadj
  have h1 : adjRaw a b = true :=
    adj_implies_adjRaw a b (rawList_digits_valid a ha) (rawList_digits_valid b hb) hadj
  have h2 : adjRaw a b = false := not_adjRaw_of_mem a b ha hb hne
  exact absurd h1 (by simp [h2])

/-! ## Alternative theorems derived from fast check -/

theorem C15_4_nodup : C15_4_vertices.Nodup := by native_decide

theorem C15_4_length : C15_4_vertices.length = 2842 := by native_decide

def C15_4_finset : Finset (Fin 4 → ZMod 15) :=
  ⟨↑C15_4_vertices, Multiset.coe_nodup.mpr C15_4_nodup⟩

theorem C15_4_card : C15_4_finset.card = 2842 := by
  simp [C15_4_finset, Multiset.coe_card, C15_4_length]

theorem C15_4_isIndepSet : (strongPower (fractionGraph 15 2) 4).IsIndepSet
    (↑C15_4_finset : Set (Fin 4 → ZMod 15)) := by
  intro a ha b hb hab
  have ha' : a ∈ C15_4_vertices := by
    simpa [C15_4_finset, Finset.mem_mk, Multiset.mem_coe] using ha
  have hb' : b ∈ C15_4_vertices := by
    simpa [C15_4_finset, Finset.mem_mk, Multiset.mem_coe] using hb
  have hsym : Symmetric (fun u v : Fin 4 → ZMod 15 =>
      ¬(strongPower (fractionGraph 15 2) 4).Adj u v) := by
    intro a b h hadj; exact h hadj.symm
  exact C15_4_pairwise_nonadj.forall hsym ha' hb' hab

theorem C15_4_indepNum_bound :
    (strongPower (fractionGraph 15 2) 4).indepNum ≥ 2842 := by
  have h := SimpleGraph.IsIndepSet.card_le_indepNum C15_4_isIndepSet
  rw [C15_4_card] at h; exact h

/-- Paper-API wrapper: `α(C₁₅^{⊠4}) ≥ 2842` for the cycle graph form
    (delegates to `C15_4_indepNum_bound` via `cycleGraph_iso_fractionGraph_two`). -/
theorem C15_4_indepNum_bound_cycle :
    (ShannonCapacity.strongPower (SimpleGraph.cycleGraph 15) 4).indepNum ≥ 2842 := by
  rw [show (ShannonCapacity.strongPower (SimpleGraph.cycleGraph 15) 4).indepNum =
      (ShannonCapacity.strongPower (fractionGraph 15 2) 4).indepNum from
    independenceNumber_iso
      (strongPower_iso (cycleGraph_iso_fractionGraph_two 15 (by norm_num)) 4)]
  exact C15_4_indepNum_bound
