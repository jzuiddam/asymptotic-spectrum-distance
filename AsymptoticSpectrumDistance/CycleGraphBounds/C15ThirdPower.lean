/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Independent Set in C₁₅^{⊠3}: Theorem 6.1

Proves α(C₁₅³) ≥ 382 and Θ(C₁₅) ≥ 382^{1/3} ≈ 7.257 using an orbit construction.

## Architecture

Following the pattern from C15IndependentSetFast.lean:
1. **Computation**: verify pairwise non-adjacency of 382 orbit vertices in E_{383/51}^{⊠3}
   via `native_decide` on raw ℕ encodings.
2. **Soundness bridge**: prove graph adjacency implies raw adjacency
   (146,689-case `native_decide` + coordinate-wise argument).
3. **Transfer**: use vertex removal (E_{383/51} - {0} ≃ E_{15/2} = C₁₅) and strong power
   cohomomorphism lifting to get α(C₁₅³) ≥ 382.

The orbit {t · (1, 75, 263) mod 383 : t = 1, ..., 382} gives 382 vertices with all nonzero
coordinates in (ℤ/383ℤ)³ (since 383 is prime and gcd(75, 383) = gcd(263, 383) = 1).
These are independent in E_{383/51}^{⊠3} and transfer to E_{15/2}^{⊠3} via the vertex
removal cohomomorphism (383·2 - 51·15 = 1).

## Main results

- `C15_3_indepNum_bound`: `(strongPower (fractionGraph 15 2) 3).indepNum ≥ 382`
- `C15_3_indepNum_bound_cycle`: same in cycle-graph form (paper-API wrapper)
-/
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import AsymptoticSpectrumDistance.Section3.FractionGraphs
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import Mathlib.Data.Set.Pairwise.List

open ShannonCapacity

set_option linter.style.nativeDecide false

namespace C15ThirdPower

/-! ## Data -/

/-- Decode a raw ℕ to a vertex in (ZMod 383)^3.
    Encoding: v = a * 146689 + b * 383 + c with a, b, c < 383. -/
def decodeVertex (v : ℕ) : Fin 3 → ZMod 383 :=
  fun i => match i with
    | 0 => (v / 146689 % 383 : ℕ)
    | 1 => (v / 383 % 383 : ℕ)
    | 2 => (v % 383 : ℕ)

/-- The 382 orbit vertices {t · (1, 75, 263) mod 383 : t = 1, ..., 382}
    encoded as raw natural numbers (base-383 representation). -/
def rawList : List ℕ :=
  (List.range 382).map fun i =>
    let t := i + 1
    (t % 383) * 146689 + ((75 * t) % 383) * 383 + ((263 * t) % 383)

def vertexList : List (Fin 3 → ZMod 383) :=
  rawList.map decodeVertex

/-! ## Raw adjacency check for E_{383/51}^{⊠3} -/

/-- Raw circular distance between two values modulo 383. -/
def distModRaw (a b : ℕ) : ℕ :=
  let diff := if a ≥ b then a - b else b - a
  min diff (383 - diff)

/-- Check if two coordinates are "equal or adjacent" in E_{383/51}:
    distMod 383 a b < 51 (which includes a = b since distMod = 0). -/
def digitClose (a b : ℕ) : Bool :=
  distModRaw a b < 51

/-- Raw adjacency in E_{383/51}^{⊠3}. -/
def adjRaw (v w : ℕ) : Bool :=
  v != w &&
  digitClose (v / 146689 % 383) (w / 146689 % 383) &&
  digitClose (v / 383 % 383) (w / 383 % 383) &&
  digitClose (v % 383) (w % 383)

/-- Pairwise non-adjacency check: no two raw vertices are adjacent. -/
def checkPairwiseRaw : Bool :=
  rawList.all fun v =>
    rawList.all fun w =>
      v == w || !adjRaw v w

/-! ## Computational verification -/

theorem checkPairwiseRaw_eq : checkPairwiseRaw = true := by native_decide

/-! ## Soundness bridge: raw check → graph-theoretic independence

We connect `adjRaw` to the graph adjacency via a `native_decide`
(146,689 cases) at the coordinate level.
-/

/-- `digitClose` matches "equal or adjacent on E_{383/51}" for digits < 383.
    Verified by exhaustive check over all 146,689 pairs. -/
def checkDigitBridge : Bool :=
  (List.range 383).all fun a =>
    (List.range 383).all fun b =>
      digitClose a b ==
        decide ((a : ZMod 383) = (b : ZMod 383) ∨
                (fractionGraph 383 51).Adj (a : ZMod 383) (b : ZMod 383))

theorem checkDigitBridge_eq : checkDigitBridge = true := by native_decide

theorem digitClose_iff (a b : ℕ) (ha : a < 383) (hb : b < 383) :
    digitClose a b =
      decide ((a : ZMod 383) = (b : ZMod 383) ∨
              (fractionGraph 383 51).Adj (a : ZMod 383) (b : ZMod 383)) := by
  have h := checkDigitBridge_eq
  simp only [checkDigitBridge, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  exact h a ha b hb

theorem digitClose_of_eq_or_adj (a b : ℕ) (ha : a < 383) (hb : b < 383)
    (h : (a : ZMod 383) = (b : ZMod 383) ∨
         (fractionGraph 383 51).Adj (a : ZMod 383) (b : ZMod 383)) :
    digitClose a b = true := by
  rw [digitClose_iff a b ha hb]; simp [h]

/-- All raw vertices have all digits < 383 (trivially true since x % 383 < 383). -/
theorem rawList_digits_valid (v : ℕ) (_ : v ∈ rawList) :
    v / 146689 % 383 < 383 ∧ v / 383 % 383 < 383 ∧ v % 383 < 383 :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
   Nat.mod_lt _ (by norm_num)⟩

/-- Strong product adjacency implies raw adjacency for valid encodings. -/
theorem adj_implies_adjRaw (v w : ℕ)
    (hv : v / 146689 % 383 < 383 ∧ v / 383 % 383 < 383 ∧ v % 383 < 383)
    (hw : w / 146689 % 383 < 383 ∧ w / 383 % 383 < 383 ∧ w % 383 < 383)
    (hadj : (strongPower (fractionGraph 383 51) 3).Adj
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

/-- The pairwise non-adjacency theorem in E_{383/51}^{⊠3}. -/
theorem pairwise_nonadj : vertexList.Pairwise
    (fun u v => ¬(strongPower (fractionGraph 383 51) 3).Adj u v) := by
  change (rawList.map decodeVertex).Pairwise _
  rw [List.pairwise_map]
  have hnodup : rawList.Nodup := by native_decide
  apply hnodup.pairwise_of_set_pairwise
  intro a ha b hb hne hadj
  have h1 : adjRaw a b = true :=
    adj_implies_adjRaw a b (rawList_digits_valid a ha) (rawList_digits_valid b hb) hadj
  have h2 : adjRaw a b = false := not_adjRaw_of_mem a b ha hb hne
  exact absurd h1 (by simp [h2])

/-! ## Independence in E_{383/51}^{⊠3} -/

theorem vertexList_nodup : vertexList.Nodup := by native_decide

theorem vertexList_length : vertexList.length = 382 := by native_decide

def finset383 : Finset (Fin 3 → ZMod 383) :=
  ⟨↑vertexList, Multiset.coe_nodup.mpr vertexList_nodup⟩

theorem finset383_card : finset383.card = 382 := by
  simp [finset383, Multiset.coe_card, vertexList_length]

theorem finset383_isIndepSet : (strongPower (fractionGraph 383 51) 3).IsIndepSet
    (↑finset383 : Set (Fin 3 → ZMod 383)) := by
  intro a ha b hb hab
  have ha' : a ∈ vertexList := by
    simpa [finset383, Finset.mem_mk, Multiset.mem_coe] using ha
  have hb' : b ∈ vertexList := by
    simpa [finset383, Finset.mem_mk, Multiset.mem_coe] using hb
  have hsym : Symmetric (fun u v : Fin 3 → ZMod 383 =>
      ¬(strongPower (fractionGraph 383 51) 3).Adj u v) := by
    intro a b h hadj; exact h hadj.symm
  exact pairwise_nonadj.forall hsym ha' hb' hab

/-! ## Transfer: E_{383/51}^{⊠3} → E_{15/2}^{⊠3} via vertex removal

The key is that all 382 orbit vertices have nonzero coordinates (since 383 is prime),
so they lie in the induced subgraph (E_{383/51} - {0})^{⊠3}. The vertex removal theorem
gives E_{383/51} - {0} ≃ E_{15/2} = C₁₅ (since 383·2 - 51·15 = 1).
-/

/-- All 382 orbit vertices have all nonzero coordinates. -/
def checkNonzeroCoords : Bool :=
  rawList.all fun v =>
    (v / 146689 % 383 : ℕ) != 0 &&
    (v / 383 % 383 : ℕ) != 0 &&
    (v % 383 : ℕ) != 0

theorem checkNonzeroCoords_eq : checkNonzeroCoords = true := by native_decide

private theorem natCast_ne_zero_of_mod_ne_zero (n : ℕ) (h : n % 383 ≠ 0) :
    ((n : ℕ) : ZMod 383) ≠ 0 := by
  intro hzero
  apply h
  have hdvd : 383 ∣ n := (ZMod.natCast_eq_zero_iff n 383).mp hzero
  omega

theorem vertex_coords_nonzero (v : ℕ) (hv : v ∈ rawList) (i : Fin 3) :
    decodeVertex v i ≠ (0 : ZMod 383) := by
  have h := checkNonzeroCoords_eq
  simp only [checkNonzeroCoords, List.all_eq_true, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h v hv
  fin_cases i <;> simp only [decodeVertex]
  · -- coordinate 0: (v / 146689 % 383 : ℕ) ≠ 0 in ZMod 383
    rw [ZMod.natCast_mod]; exact natCast_ne_zero_of_mod_ne_zero (v / 146689) h0
  · -- coordinate 1: (v / 383 % 383 : ℕ) ≠ 0 in ZMod 383
    rw [ZMod.natCast_mod]; exact natCast_ne_zero_of_mod_ne_zero (v / 383) h1
  · -- coordinate 2: (v % 383 : ℕ) ≠ 0 in ZMod 383
    rw [ZMod.natCast_mod]; exact natCast_ne_zero_of_mod_ne_zero v h2

/-- The main independence number bound for E_{15/2}^{⊠3}.

    Proof strategy:
    1. 382 vertices independent in E_{383/51}^{⊠3} (computational)
    2. All have nonzero coordinates → lie in (E_{383/51} - {0})^{⊠3}
    3. Vertex removal: E_{383/51} - {0} →_cohom E_{15/2} (Stern-Brocot: 383·2 - 51·15 = 1)
    4. Lift to strong power: (E_{383/51} - {0})^{⊠3} →_cohom E_{15/2}^{⊠3}
    5. α monotone under cohomomorphism: α(E_{15/2}^{⊠3}) ≥ 382 -/
theorem C15_3_indepNum_bound :
    (strongPower (fractionGraph 15 2) 3).indepNum ≥ 382 := by
  -- Step 1: Get vertex removal cohomomorphism
  -- fractionGraph_remove_vertex_equiv uses FractionGraphBasic.fractionGraph
  have hremove := AsymptoticSpectrumDistance.fractionGraph_remove_vertex_equiv 383 51
    (by norm_num) (by norm_num) (by native_decide) (0 : ZMod 383)
  obtain ⟨p', q', hp'_pos, hq'_pos, hp'_lt, hq'_lt, hbezout, hcohom_fwd, _hcohom_bwd⟩ := hremove
  -- Step 2: Verify p' = 15, q' = 2 from the Bezout equation
  -- 383 · q' - 51 · p' = 1. With p' < 383 and q' < 51 and positivity,
  -- the unique solution is p' = 15, q' = 2 (since 383·2 - 51·15 = 766 - 765 = 1).
  have hp'_eq : p' = 15 := by
    have := AsymptoticSpectrumDistance.sternBrocotPredecessor_unique 383 51 p' q' 15 2
      (by native_decide : Nat.Coprime 383 51) hp'_pos hp'_lt hq'_pos hq'_lt
      (by norm_num : 0 < 15) (by norm_num : 15 < 383)
      (by norm_num : 0 < 2) (by norm_num : 2 < 51)
      hbezout (by norm_num : 383 * 2 - 51 * 15 = 1)
    exact this.1
  have hq'_eq : q' = 2 := by
    have := AsymptoticSpectrumDistance.sternBrocotPredecessor_unique 383 51 p' q' 15 2
      (by native_decide : Nat.Coprime 383 51) hp'_pos hp'_lt hq'_pos hq'_lt
      (by norm_num : 0 < 15) (by norm_num : 15 < 383)
      (by norm_num : 0 < 2) (by norm_num : 2 < 51)
      hbezout (by norm_num : 383 * 2 - 51 * 15 = 1)
    exact this.2
  subst hp'_eq; subst hq'_eq
  -- Now hcohom_fwd : Cohom ((FractionGraphBasic.fractionGraph 383 51).induce {x | x ≠ 0})
  --                            (FractionGraphBasic.fractionGraph 15 2)
  -- Step 3: Lift cohomomorphism to strong powers
  haveI : NeZero (15 : ℕ) := ⟨by norm_num⟩
  have hcohom_power := Cohom.strongPower hcohom_fwd 3
  -- hcohom_power : SimpleGraph.strongPower ((...).induce {x | x ≠ 0}) 3 ≤_G
  --               SimpleGraph.strongPower (FractionGraphBasic.fractionGraph 15 2) 3
  -- Step 5: Construct independent set in the induced subgraph's strong power
  -- First, lift the 382 vertices to the subtype {x : ZMod 383 | x ≠ 0}
  let liftedVertices : List (Fin 3 → {x : ZMod 383 | x ≠ 0}) :=
    rawList.attach.map fun ⟨v, hv⟩ =>
      fun i => ⟨decodeVertex v i, vertex_coords_nonzero v hv i⟩
  -- Show these are independent in the induced strong power
  have hlifted_nodup : liftedVertices.Nodup := by
    apply List.Nodup.map_on _ (List.nodup_attach.mpr (by native_decide : rawList.Nodup))
    intro ⟨a, ha⟩ _ ⟨b, hb⟩ _ heq
    ext1
    have hfun : decodeVertex a = decodeVertex b :=
      funext fun i => congrArg Subtype.val (congr_fun heq i)
    exact List.inj_on_of_nodup_map vertexList_nodup ha hb hfun
  have hlifted_length : liftedVertices.length = 382 := by
    simp only [liftedVertices, List.length_map, List.length_attach, rawList, List.length_range]
  let liftedFinset : Finset (Fin 3 → {x : ZMod 383 | x ≠ 0}) :=
    ⟨↑liftedVertices, Multiset.coe_nodup.mpr hlifted_nodup⟩
  have hlifted_card : liftedFinset.card = 382 := by
    simp [liftedFinset, Multiset.coe_card]
    exact hlifted_length
  -- Step 5a: Prove pairwise non-adjacency for the lifted vertices
  -- (adjacency in induced power → adjacency in full power → contradiction with pairwise_nonadj)
  have hlifted_pairwise : liftedVertices.Pairwise
      (fun a b => ¬(SimpleGraph.strongPower ((FractionGraphBasic.fractionGraph 383 51).induce
        {x : ZMod 383 | x ≠ 0}) 3).Adj a b) := by
    simp only [liftedVertices]
    rw [List.pairwise_map]
    apply (List.nodup_attach.mpr (by native_decide : rawList.Nodup)).pairwise_of_set_pairwise
    intro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hne hadj_induced
    -- From adjacency in the induced power, derive adjacency in the full power
    have hadj_full : (strongPower (fractionGraph 383 51) 3).Adj
        (decodeVertex a) (decodeVertex b) := by
      constructor
      · intro heq; exact hadj_induced.1 (funext fun i => Subtype.ext (congr_fun heq i))
      · intro i
        cases hadj_induced.2 i with
        | inl h => left; exact congrArg Subtype.val h
        | inr h => right; exact h
    -- But they are non-adjacent by pairwise_nonadj
    have hsym : Symmetric (fun u v : Fin 3 → ZMod 383 =>
        ¬(strongPower (fractionGraph 383 51) 3).Adj u v) := by
      intro x y h hadj; exact h hadj.symm
    exact pairwise_nonadj.forall hsym
      (List.mem_map_of_mem (f := decodeVertex) ha)
      (List.mem_map_of_mem (f := decodeVertex) hb)
      (fun heq => hne (Subtype.ext (List.inj_on_of_nodup_map vertexList_nodup ha hb heq)))
      hadj_full
  -- Step 5b: Convert pairwise to IsIndepSet
  have hlifted_indep :
      (SimpleGraph.strongPower ((FractionGraphBasic.fractionGraph 383 51).induce
        {x : ZMod 383 | x ≠ 0}) 3).IsIndepSet
        (↑liftedFinset : Set (Fin 3 → {x : ZMod 383 | x ≠ 0})) := by
    intro a ha b hb hab
    have ha' : a ∈ liftedVertices := ha
    have hb' : b ∈ liftedVertices := hb
    have hsym : Symmetric (fun u v : Fin 3 → {x : ZMod 383 | x ≠ 0} =>
        ¬(SimpleGraph.strongPower ((FractionGraphBasic.fractionGraph 383 51).induce
          {x : ZMod 383 | x ≠ 0}) 3).Adj u v) := by
      intro x y h hadj; exact h hadj.symm
    exact hlifted_pairwise.forall hsym ha' hb' hab
  -- Step 6: Apply alpha monotonicity
  -- α(induced power) ≤ α(E_{15/2}^{⊠3}) via cohomomorphism
  obtain ⟨f_power, hf_power⟩ := hcohom_power
  have halpha_le : (SimpleGraph.strongPower
      ((FractionGraphBasic.fractionGraph 383 51).induce {x : ZMod 383 | x ≠ 0}) 3).indepNum ≤
      (SimpleGraph.strongPower (FractionGraphBasic.fractionGraph 15 2) 3).indepNum :=
    SimpleGraph.independenceNumber_le_of_cohomomorphism _ _ f_power hf_power
  -- α(induced power) ≥ 382 from our independent set
  have halpha_ge :
      (SimpleGraph.strongPower ((FractionGraphBasic.fractionGraph 383 51).induce
        {x : ZMod 383 | x ≠ 0}) 3).indepNum ≥ 382 := by
    have h := SimpleGraph.IsIndepSet.card_le_indepNum (G :=
      SimpleGraph.strongPower ((FractionGraphBasic.fractionGraph 383 51).induce
        {x : ZMod 383 | x ≠ 0}) 3) (t := liftedFinset) hlifted_indep
    rw [hlifted_card] at h; exact h
  -- Combine: α(E_{15/2}^{⊠3}) ≥ 382 (namespace bridge is definitional)
  change (SimpleGraph.strongPower
    (FractionGraphBasic.fractionGraph 15 2) 3).indepNum ≥ 382
  omega

/-- Paper-API wrapper: `α(C₁₅^{⊠3}) ≥ 382` for the cycle graph form
    (delegates to `C15_3_indepNum_bound` via `cycleGraph_iso_fractionGraph_two`). -/
theorem C15_3_indepNum_bound_cycle :
    (ShannonCapacity.strongPower (SimpleGraph.cycleGraph 15) 3).indepNum ≥ 382 := by
  rw [show (ShannonCapacity.strongPower (SimpleGraph.cycleGraph 15) 3).indepNum =
      (ShannonCapacity.strongPower (fractionGraph 15 2) 3).indepNum from
    SimpleGraph.independenceNumber_iso
      (ShannonCapacity.strongPower_iso (cycleGraph_iso_fractionGraph_two 15 (by norm_num)) 3)]
  exact C15_3_indepNum_bound

end C15ThirdPower
