/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Theorem 6.9 converse — bounded-candidate enumeration scaffolding

The (→) direction of paper Theorem 6.9 (`th:discont`, line 2806–2807): every
α₃-discontinuity in `(ℚ ∩ [2, 3])³` matches one of the 12 listed multisets up
to permutation. This file builds the case-analysis scaffolding for the converse:
a refined `BoundedDiscCandidates` finset, the per-disc membership theorem, and
a parameterized form of the converse.

## What this file provides

* `BoundedDiscCandidates : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))` — a refinement
  of `discCandidates` (in `Section6DiscontinuityKCandidates.lean`) that further
  filters by the per-candidate numerator bound `(v i).1 ≤ alphaK v` (equivalent
  in disc cases to numerator ≤ `nestedFloor3NatMin (toNatTriple v)`).
* `isDiscontinuityK_imp_mem_BoundedDiscCandidates` — every α₃-disc in
  `(ℚ ∩ [2, 3])³` (lowest terms, all denominators ≥ 2) lands in
  `BoundedDiscCandidates`. This shrinks the candidate set from `discCandidates`'
  ~59,000 to a much smaller pruned set per disc.
* `theorem_6_9_converse_of_bounded_classification` — parameterized converse:
  if every triple in `BoundedDiscCandidates` either matches a known disc or
  is not a disc (witness: a strictly smaller valid `u` with same `α₃`), then
  every `IsDiscontinuityK v` (valid + lowest-terms + ≤3) yields `IsKnownDiscMod v`.

The integer-slot case (denominator = 1 at some slot) is handled separately
because `discCandidates` allows integer slots (q = 1) but `BoundedDiscCandidates`
follows the same convention. Integer-disc cases are covered by the 6 of 12
known discs in `knownDiscList` whose representatives have integer slots.
-/

import AsymptoticSpectrumDistance.Section6.Section6Theorem69
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKAlphaTable
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKCandidates
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKNumerator
import AsymptoticSpectrumDistance.Section6.Section6Diagonal
import AsymptoticSpectrumDistance.Section6.Section6UpperBounds

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## The bounded-numerator candidate set

`discCandidates` (in `Section6DiscontinuityKCandidates.lean`) is the cube of
`fracPairCandidates`, allowing each slot's numerator to be up to 27 (the
loose bound `α₃(3, 3, 3) = 27`). For most slots this is far too generous; a
tighter per-tuple bound is `(v i).1 ≤ alphaK v`, which by `nested_floor_three`
is at most `nestedFloor3NatMin (toNatTriple v)`.

`BoundedDiscCandidates` filters `discCandidates` by this tighter constraint.
A disc in `(ℚ ∩ [2, 3])³` (in lowest terms) lands in `BoundedDiscCandidates`,
not just `discCandidates`. -/

/-- Bool-valued: each numerator in a `(ℕ × ℕ)³` triple is at most `B`. -/
def boundedNumerator (B : ℕ) (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (t.1.1 ≤ B ∧ t.2.1.1 ≤ B ∧ t.2.2.1 ≤ B)

/-- The bounded-numerator subset of `discCandidates`. Every α₃-disc lies here:
    each numerator is bounded by `nestedFloor3NatMin t`, the tightest nested-floor
    upper bound on `alphaK` (over the 6 slot-permutations), which is itself an
    upper bound on the disc's `alphaK` (by `nested_floor_three`). -/
def BoundedDiscCandidates :
    Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  discCandidates.filter (fun t => boundedNumerator (nestedFloor3NatMin t) t)

@[simp] lemma mem_BoundedDiscCandidates
    {t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)} :
    t ∈ BoundedDiscCandidates ↔
      t ∈ discCandidates ∧
        boundedNumerator (nestedFloor3NatMin t) t = true := by
  simp [BoundedDiscCandidates]

/-! ## Per-disc α₃ upper bound: `nestedFloor3NatMin` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For any valid `v : FracTuple 3`, `alphaK v ≤ nestedFloor3NatMin (toNatTriple v)`.
    Direct from `alpha3_le_nestedFloor3Nat` in any of the 6 slot orderings,
    plus αₖ-permutation invariance. -/
theorem alphaK_le_nestedFloor3NatMin
    {v : FracTuple 3} (hv : ValidK v) :
    alphaK v ≤ nestedFloor3NatMin (FracTuple.toNatTriple v) := by
  -- Unpack the per-permutation bound.
  have h_assoc : alphaK v =
      (strongProduct (fractionGraph (v 0).1 (v 0).2)
        (strongProduct (fractionGraph (v 1).1 (v 1).2)
          (fractionGraph (v 2).1 (v 2).2))).indepNum := by
    rw [alphaK_three]
    unfold alpha3
    exact ShannonCapacity.indepNum_strongProduct_assoc _ _ _
  -- Identity ordering already gives one of the 6 cases.
  haveI : NeZero ((v 0).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 0).1.pos⟩
  haveI : NeZero ((v 1).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 1).1.pos⟩
  haveI : NeZero ((v 2).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 2).1.pos⟩
  have h2q : ∀ i, 2 * ((v i).2 : ℕ) ≤ ((v i).1 : ℕ) := fun i => by exact_mod_cast hv i
  have hq : ∀ i, 0 < ((v i).2 : ℕ) := fun i => (v i).2.pos
  have h_id : alphaK v ≤ nestedFloor3Nat
      ((v 0).1 : ℕ) ((v 0).2 : ℕ)
      ((v 1).1 : ℕ) ((v 1).2 : ℕ)
      ((v 2).1 : ℕ) ((v 2).2 : ℕ) := by
    rw [h_assoc]
    exact alpha3_le_nestedFloor3Nat
      ((v 0).1 : ℕ) ((v 0).2 : ℕ) ((v 1).1 : ℕ) ((v 1).2 : ℕ)
      ((v 2).1 : ℕ) ((v 2).2 : ℕ)
      (hq 0) (h2q 0) (hq 1) (h2q 1) (hq 2) (h2q 2)
  -- nestedFloor3NatMin is the min of 6 nestedFloor3Nat values, including the
  -- identity case. So alphaK v ≤ identity floor, which is ≥ min.
  -- For the other 5 perms, monotonicity needs alphaK_perm + the same bound;
  -- but we just need ≤ min, so the identity case suffices on one side. WAIT:
  -- min is the SMALLEST of the 6, so we need alphaK ≤ min, not ≥. We need
  -- the per-perm bound for ALL 6 perms. Apply alphaK_perm to each.
  -- Compute the bound at each of the 6 permutations.
  -- We use that `alphaK v = alphaK (v ∘ σ)` for any σ, hence the bound at
  -- σ-reordering applies.
  -- The 6 perms below use the existing FracTuple structure.
  -- It's cleaner: nestedFloor3NatMin t ≥ alphaK only if alphaK ≤ each of the 6
  -- floors. So we need each of the 6 perm bounds.
  set t := FracTuple.toNatTriple v with ht_def
  -- Notation: t = ((p₀, q₀), (p₁, q₁), (p₂, q₂)).
  -- nestedFloor3NatMin computes min over all 6 orderings of (p_i, q_i).
  -- We bound alphaK by each of the 6 nested floors via alphaK_perm.
  -- For permutation σ, alphaK v = alphaK (v ∘ σ), and applying h_id-style
  -- bound to (v ∘ σ) gives the σ-permuted nested floor.
  -- All 6 cases are concrete; do them via fin_cases-style.
  -- Define helper: the bound for each ordering of slots i₀ i₁ i₂.
  have hperm : ∀ (σ : Equiv.Perm (Fin 3)),
      alphaK v ≤ nestedFloor3Nat
        (((v ∘ σ) 0).1 : ℕ) (((v ∘ σ) 0).2 : ℕ)
        (((v ∘ σ) 1).1 : ℕ) (((v ∘ σ) 1).2 : ℕ)
        (((v ∘ σ) 2).1 : ℕ) (((v ∘ σ) 2).2 : ℕ) := by
    intro σ
    rw [alphaK_perm v σ]
    have hv_σ : ValidK (v ∘ σ) := fun i => hv (σ i)
    have h2q_σ : ∀ i, 2 * (((v ∘ σ) i).2 : ℕ) ≤ (((v ∘ σ) i).1 : ℕ) :=
      fun i => by exact_mod_cast hv_σ i
    have hq_σ : ∀ i, 0 < (((v ∘ σ) i).2 : ℕ) := fun i => ((v ∘ σ) i).2.pos
    haveI : NeZero (((v ∘ σ) 0).1 : ℕ) :=
      ⟨Nat.pos_iff_ne_zero.mp ((v ∘ σ) 0).1.pos⟩
    haveI : NeZero (((v ∘ σ) 1).1 : ℕ) :=
      ⟨Nat.pos_iff_ne_zero.mp ((v ∘ σ) 1).1.pos⟩
    haveI : NeZero (((v ∘ σ) 2).1 : ℕ) :=
      ⟨Nat.pos_iff_ne_zero.mp ((v ∘ σ) 2).1.pos⟩
    have h_assoc_σ : alphaK (v ∘ σ) =
        (strongProduct (fractionGraph ((v ∘ σ) 0).1 ((v ∘ σ) 0).2)
          (strongProduct (fractionGraph ((v ∘ σ) 1).1 ((v ∘ σ) 1).2)
            (fractionGraph ((v ∘ σ) 2).1 ((v ∘ σ) 2).2))).indepNum := by
      rw [alphaK_three]
      unfold alpha3
      exact ShannonCapacity.indepNum_strongProduct_assoc _ _ _
    rw [h_assoc_σ]
    exact alpha3_le_nestedFloor3Nat
      (((v ∘ σ) 0).1 : ℕ) (((v ∘ σ) 0).2 : ℕ)
      (((v ∘ σ) 1).1 : ℕ) (((v ∘ σ) 1).2 : ℕ)
      (((v ∘ σ) 2).1 : ℕ) (((v ∘ σ) 2).2 : ℕ)
      (hq_σ 0) (h2q_σ 0) (hq_σ 1) (h2q_σ 1) (hq_σ 2) (h2q_σ 2)
  -- Define the 6 perms explicitly and reduce nestedFloor3NatMin to a min
  -- over them.
  unfold nestedFloor3NatMin
  -- Now the goal: alphaK v ≤ min of 6 nestedFloor3Nat applications.
  -- Bound each by `hperm` at the appropriate permutation.
  set p0 := ((v 0).1 : ℕ); set q0 := ((v 0).2 : ℕ)
  set p1 := ((v 1).1 : ℕ); set q1 := ((v 1).2 : ℕ)
  set p2 := ((v 2).1 : ℕ); set q2 := ((v 2).2 : ℕ)
  -- t.1 = (p0, q0), t.2.1 = (p1, q1), t.2.2 = (p2, q2). The 6 nested floors
  -- in `nestedFloor3NatMin` use combinations (a, b, c) ranging over perms of
  -- the 3 entries. They map onto: 1=id, swap12, swap01, cycle 0→1→2 (b,c,a),
  -- cycle 0→2→1 (c,a,b), swap02. We need a perm σ of Fin 3 for each.
  -- Specifically:
  --   nestedFloor3Nat p0 q0 p1 q1 p2 q2 (entries a, b, c at positions 0,1,2): σ = 1.
  --   nestedFloor3Nat p0 q0 p2 q2 p1 q1 (a, c, b): σ = swap 1 2.
  --   nestedFloor3Nat p1 q1 p0 q0 p2 q2 (b, a, c): σ = swap 0 1.
  --   nestedFloor3Nat p1 q1 p2 q2 p0 q0 (b, c, a):
  --       σ 0 = 1, σ 1 = 2, σ 2 = 0. This is swap 1 2 ∘ swap 0 2 in left-comp.
  --   nestedFloor3Nat p2 q2 p0 q0 p1 q1 (c, a, b):
  --       σ 0 = 2, σ 1 = 0, σ 2 = 1. swap 0 2 ∘ swap 1 2.
  --   nestedFloor3Nat p2 q2 p1 q1 p0 q0 (c, b, a): σ = swap 0 2.
  refine le_min (le_min (le_min ?_ ?_) (le_min ?_ ?_)) (le_min ?_ ?_)
  · -- σ = 1.
    have h := hperm 1
    simp only [Equiv.Perm.coe_one, Function.comp, id_eq] at h
    exact h
  · -- σ = swap 1 2.
    have h := hperm (Equiv.swap 1 2)
    have h0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have h1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := Equiv.swap_apply_left 1 2
    have h2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := Equiv.swap_apply_right 1 2
    simp only [Function.comp, h0, h1, h2] at h
    exact h
  · -- σ = swap 0 1.
    have h := hperm (Equiv.swap 0 1)
    have h0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have h1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    have h2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    simp only [Function.comp, h0, h1, h2] at h
    exact h
  · -- σ with σ 0 = 1, σ 1 = 2, σ 2 = 0 (cycle 0→1→2→0).
    -- This is `swap 1 2 * swap 0 2`: read right-to-left composition.
    -- (swap 0 2) 0 = 2, (swap 1 2) 2 = 1. So (swap 1 2 * swap 0 2) 0 = 1. ✓
    -- (swap 0 2) 1 = 1, (swap 1 2) 1 = 2. So σ 1 = 2. ✓
    -- (swap 0 2) 2 = 0, (swap 1 2) 0 = 0. So σ 2 = 0. ✓
    have h := hperm (Equiv.swap 1 2 * Equiv.swap 0 2)
    have h0 : (Equiv.swap (1:Fin 3) 2 * Equiv.swap (0:Fin 3) 2) 0 = 1 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
    have h1 : (Equiv.swap (1:Fin 3) 2 * Equiv.swap (0:Fin 3) 2) 1 = 2 := by
      rw [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (by decide : (1:Fin 3) ≠ 0)
            (by decide : (1:Fin 3) ≠ 2),
          Equiv.swap_apply_left]
    have h2 : (Equiv.swap (1:Fin 3) 2 * Equiv.swap (0:Fin 3) 2) 2 = 0 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1)
            (by decide : (0:Fin 3) ≠ 2)]
    simp only [Function.comp, h0, h1, h2] at h
    exact h
  · -- σ with σ 0 = 2, σ 1 = 0, σ 2 = 1.
    -- This is `swap 0 2 * swap 1 2`:
    -- (swap 1 2) 0 = 0, (swap 0 2) 0 = 2. So σ 0 = 2. ✓
    -- (swap 1 2) 1 = 2, (swap 0 2) 2 = 0. So σ 1 = 0. ✓
    -- (swap 1 2) 2 = 1, (swap 0 2) 1 = 1. So σ 2 = 1. ✓
    have h := hperm (Equiv.swap 0 2 * Equiv.swap 1 2)
    have h0 : (Equiv.swap (0:Fin 3) 2 * Equiv.swap (1:Fin 3) 2) 0 = 2 := by
      rw [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 3) ≠ 1)
            (by decide : (0:Fin 3) ≠ 2),
          Equiv.swap_apply_left]
    have h1 : (Equiv.swap (0:Fin 3) 2 * Equiv.swap (1:Fin 3) 2) 1 = 0 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
    have h2 : (Equiv.swap (0:Fin 3) 2 * Equiv.swap (1:Fin 3) 2) 2 = 1 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne (by decide : (1:Fin 3) ≠ 0)
            (by decide : (1:Fin 3) ≠ 2)]
    simp only [Function.comp, h0, h1, h2] at h
    exact h
  · -- σ = swap 0 2.
    have h := hperm (Equiv.swap 0 2)
    have h0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := Equiv.swap_apply_left 0 2
    have h1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have h2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := Equiv.swap_apply_right 0 2
    simp only [Function.comp, h0, h1, h2] at h
    exact h

/-! ## Bounded-numerator membership for discs

Combines `isDiscontinuityK_imp_mem_discCandidates` with the per-slot numerator
bound `(v i).1 ≤ alphaK v` (from `alphaK_ge_num_at_of_isDiscontinuityK`) and
`alphaK v ≤ nestedFloor3NatMin (toNatTriple v)` (above). -/

/-- **Refined main theorem.** Every α₃-disc with each denominator ≥ 2
    (lowest terms) has its `toNatTriple` in `BoundedDiscCandidates`. -/
theorem isDiscontinuityK_imp_mem_BoundedDiscCandidates
    {v : FracTuple 3} (hv_valid : ValidK v) (hv_disc : IsDiscontinuityK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3)
    (hv_coprime : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ))
    (hv_q_ge2 : ∀ i, 2 ≤ ((v i).2 : ℕ)) :
    FracTuple.toNatTriple v ∈ BoundedDiscCandidates := by
  rw [mem_BoundedDiscCandidates]
  refine ⟨?_, ?_⟩
  · -- Membership in `discCandidates`.
    exact isDiscontinuityK_imp_mem_discCandidates hv_valid hv_disc hv_le3
      hv_coprime hv_q_ge2
  · -- Bounded numerator: each (v i).1 ≤ alphaK v ≤ nestedFloor3NatMin (toNatTriple v).
    have hα_ub : alphaK v ≤ nestedFloor3NatMin (FracTuple.toNatTriple v) :=
      alphaK_le_nestedFloor3NatMin hv_valid
    have h_pi_le : ∀ i, ((v i).1 : ℕ) ≤ nestedFloor3NatMin (FracTuple.toNatTriple v) := by
      intro i
      have h_pi := alphaK_ge_num_at_of_isDiscontinuityK hv_valid hv_disc i
        (hv_q_ge2 i) (hv_coprime i)
      omega
    -- Decode `boundedNumerator` into a conjunction of three numerator-≤-B claims.
    unfold boundedNumerator FracTuple.toNatTriple
    simp only [decide_eq_true_eq]
    exact ⟨h_pi_le 0, h_pi_le 1, h_pi_le 2⟩

/-! ## Toolkit: from `(p, q)` to `ℕ+ × ℕ+`

For the parameterized converse below, we need to talk about FracTuples whose
slots come from a `(ℕ × ℕ)³` triple in `BoundedDiscCandidates`. Membership in
`fracPairCandidates` ensures `1 ≤ q` and `2 ≤ p`, so `ℕ+`-coercions are
well-defined. -/

/-- Construct a `ℕ+` from a positive `ℕ`. -/
private def toPNatPos (n : ℕ) (hn : 0 < n) : ℕ+ := ⟨n, hn⟩

/-- For a triple in `discCandidates`, each `(p, q)` pair has `p ≥ 2` and
    `q ≥ 1` (so both are positive `ℕ+`). -/
private lemma pos_of_mem_fracPairCandidates {p q : ℕ}
    (h : (p, q) ∈ fracPairCandidates) : 0 < p ∧ 0 < q := by
  rw [mem_fracPairCandidates] at h
  exact ⟨by omega, by omega⟩

/-- Reconstruct a `FracTuple 3` from a `(ℕ × ℕ)³` triple all of whose pairs
    are in `fracPairCandidates`. -/
private def fracTupleOf (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates) : FracTuple 3 :=
  ![ (toPNatPos t.1.1 (pos_of_mem_fracPairCandidates h0).1,
      toPNatPos t.1.2 (pos_of_mem_fracPairCandidates h0).2),
     (toPNatPos t.2.1.1 (pos_of_mem_fracPairCandidates h1).1,
      toPNatPos t.2.1.2 (pos_of_mem_fracPairCandidates h1).2),
     (toPNatPos t.2.2.1 (pos_of_mem_fracPairCandidates h2).1,
      toPNatPos t.2.2.2 (pos_of_mem_fracPairCandidates h2).2) ]

/-- The reconstructed `fracTupleOf` has its `toNatTriple` equal to the original. -/
private lemma fracTupleOf_toNatTriple_eq (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates) :
    FracTuple.toNatTriple (fracTupleOf t h0 h1 h2) = t := by
  unfold fracTupleOf FracTuple.toNatTriple toPNatPos
  rfl

/-- The reconstructed `fracTupleOf` is `ValidK`. -/
private lemma fracTupleOf_valid (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates) :
    ValidK (fracTupleOf t h0 h1 h2) := by
  intro i
  have hf : ∀ {p q : ℕ}, (p, q) ∈ fracPairCandidates → 2 * q ≤ p := by
    intro p q h; rw [mem_fracPairCandidates] at h; exact h.2.2.2.2.1
  fin_cases i
  · -- slot 0: 2 * (q-pnat) ≤ p-pnat. Reduce via underlying nats.
    have h2q : 2 * t.1.2 ≤ t.1.1 := hf h0
    change 2 * ((fracTupleOf t h0 h1 h2 0).2 : ℕ+) ≤ (fracTupleOf t h0 h1 h2 0).1
    -- The `(fracTupleOf t _ _ _) 0` is the pair `(toPNatPos t.1.1 _, toPNatPos t.1.2 _)`.
    have h_p : ((fracTupleOf t h0 h1 h2 0).1 : ℕ) = t.1.1 := rfl
    have h_q : ((fracTupleOf t h0 h1 h2 0).2 : ℕ) = t.1.2 := rfl
    -- Convert pnat goal to nat goal.
    have : ((2 * ((fracTupleOf t h0 h1 h2 0).2 : ℕ+) : ℕ+) : ℕ) ≤
           (((fracTupleOf t h0 h1 h2 0).1 : ℕ+) : ℕ) := by
      push_cast; rw [h_p, h_q]; exact h2q
    exact_mod_cast this
  · -- slot 1
    have h2q : 2 * t.2.1.2 ≤ t.2.1.1 := hf h1
    change 2 * ((fracTupleOf t h0 h1 h2 1).2 : ℕ+) ≤ (fracTupleOf t h0 h1 h2 1).1
    have h_p : ((fracTupleOf t h0 h1 h2 1).1 : ℕ) = t.2.1.1 := rfl
    have h_q : ((fracTupleOf t h0 h1 h2 1).2 : ℕ) = t.2.1.2 := rfl
    have : ((2 * ((fracTupleOf t h0 h1 h2 1).2 : ℕ+) : ℕ+) : ℕ) ≤
           (((fracTupleOf t h0 h1 h2 1).1 : ℕ+) : ℕ) := by
      push_cast; rw [h_p, h_q]; exact h2q
    exact_mod_cast this
  · -- slot 2
    have h2q : 2 * t.2.2.2 ≤ t.2.2.1 := hf h2
    change 2 * ((fracTupleOf t h0 h1 h2 2).2 : ℕ+) ≤ (fracTupleOf t h0 h1 h2 2).1
    have h_p : ((fracTupleOf t h0 h1 h2 2).1 : ℕ) = t.2.2.1 := rfl
    have h_q : ((fracTupleOf t h0 h1 h2 2).2 : ℕ) = t.2.2.2 := rfl
    have : ((2 * ((fracTupleOf t h0 h1 h2 2).2 : ℕ+) : ℕ+) : ℕ) ≤
           (((fracTupleOf t h0 h1 h2 2).1 : ℕ+) : ℕ) := by
      push_cast; rw [h_p, h_q]; exact h2q
    exact_mod_cast this

/-! ## Parameterized converse: `theorem_6_9_converse_of_bounded_classification`

If every triple `t ∈ BoundedDiscCandidates` is "classified" — meaning either
the canonical `FracTuple 3` reconstruction `fracTupleOf t` is `IsKnownDiscMod`,
or `fracTupleOf t` is non-disc (i.e., admits a strictly smaller valid `u` with
`alphaK u ≥ alphaK (fracTupleOf t)`) — then the converse of Theorem 6.9 holds.

This is the form a `decide` / `native_decide` enumeration over
`BoundedDiscCandidates` would discharge. -/

/-- The classification predicate per bounded candidate. -/
def IsClassifiedNat (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates) : Prop :=
  IsKnownDiscMod (fracTupleOf t h0 h1 h2) ∨ ¬ IsDiscontinuityK (fracTupleOf t h0 h1 h2)

/-! ## Bridge: `alphaK` agrees on `v` and its `fracTupleOf` reconstruction -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- If `v : FracTuple 3` has `(v i).1 = (fracTupleOf t _ _ _) i .1` and same for
    `(v i).2`, then `alphaK v = alphaK (fracTupleOf t _ _ _)`. The two tuples
    are pointwise equal as `ℕ+ × ℕ+` since both numerator and denominator are
    `PNat.mk` of the same nat. So this is `congrArg`. -/
private lemma fracTupleOf_eq_of_toNatTriple
    {v : FracTuple 3} (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (h_eq : FracTuple.toNatTriple v = t) :
    v = fracTupleOf t h0 h1 h2 := by
  -- Each slot's nat-triple components agree (extracted from h_eq).
  have h0p : ((v 0).1 : ℕ) = t.1.1 := by
    have h := congrArg (·.1.1) h_eq; simpa [FracTuple.toNatTriple] using h
  have h0q : ((v 0).2 : ℕ) = t.1.2 := by
    have h := congrArg (·.1.2) h_eq; simpa [FracTuple.toNatTriple] using h
  have h1p : ((v 1).1 : ℕ) = t.2.1.1 := by
    have h := congrArg (·.2.1.1) h_eq; simpa [FracTuple.toNatTriple] using h
  have h1q : ((v 1).2 : ℕ) = t.2.1.2 := by
    have h := congrArg (·.2.1.2) h_eq; simpa [FracTuple.toNatTriple] using h
  have h2p : ((v 2).1 : ℕ) = t.2.2.1 := by
    have h := congrArg (·.2.2.1) h_eq; simpa [FracTuple.toNatTriple] using h
  have h2q : ((v 2).2 : ℕ) = t.2.2.2 := by
    have h := congrArg (·.2.2.2) h_eq; simpa [FracTuple.toNatTriple] using h
  -- Build the slot equalities; each side is a `(ℕ+, ℕ+)` pair, matched by
  -- their nat coercions.
  funext i
  fin_cases i
  · -- slot 0
    change v 0 = (toPNatPos t.1.1 _, toPNatPos t.1.2 _)
    apply Prod.ext
    · -- numerator
      apply PNat.coe_inj.mp
      simp [toPNatPos, h0p]
    · -- denominator
      apply PNat.coe_inj.mp
      simp [toPNatPos, h0q]
  · -- slot 1
    change v 1 = (toPNatPos t.2.1.1 _, toPNatPos t.2.1.2 _)
    apply Prod.ext
    · apply PNat.coe_inj.mp
      simp [toPNatPos, h1p]
    · apply PNat.coe_inj.mp
      simp [toPNatPos, h1q]
  · -- slot 2
    change v 2 = (toPNatPos t.2.2.1 _, toPNatPos t.2.2.2 _)
    apply Prod.ext
    · apply PNat.coe_inj.mp
      simp [toPNatPos, h2p]
    · apply PNat.coe_inj.mp
      simp [toPNatPos, h2q]

/-- **Theorem 6.9 (converse, parameterized by bounded-set classification).**
    If every triple in `BoundedDiscCandidates` (with auto-derived
    `fracPairCandidates`-membership) is either `IsKnownDiscMod` or non-disc,
    then every α₃-disc in `(ℚ ∩ [2, 3])³` (lowest terms, all denominators ≥ 2)
    is `IsKnownDiscMod`.

    The classification hypothesis is the form a per-tuple `decide` /
    `native_decide` enumeration would produce: for each of the (~1000s of)
    bounded candidates, either match it to one of the 12 known discs, or
    exhibit a witness `u <ₚ v` with `alphaK u ≥ alphaK v` (negating
    `IsDiscontinuityK`).

    Caveat: this form requires hypothesis on `(v i).2 ≥ 2` (no integer
    slots). The integer-slot case is handled by `lem:disc-integer`
    (`isDiscontinuityK_consInt`/`forward`) reducing it to a `FracTuple 2`
    disc analysis; the 2-factor disc analysis follows
    `IsDiscontinuity₂_iff_isDiscontinuityK` + the disc points of α₂ in
    `Section6DiscontinuityAlpha2.lean`. The full integration of integer-slot
    cases into a single converse statement is completed downstream in
    `Section6DiscontinuityAlpha2Converse.theorem_6_9` and `Main.lean`'s
    `main_theorem_6_9`. -/
theorem theorem_6_9_converse_of_bounded_classification
    (h_class : ∀ t ∈ BoundedDiscCandidates,
      ∀ (h0 : t.1 ∈ fracPairCandidates)
        (h1 : t.2.1 ∈ fracPairCandidates)
        (h2 : t.2.2 ∈ fracPairCandidates),
        IsClassifiedNat t h0 h1 h2)
    {v : FracTuple 3} (hv_valid : ValidK v) (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3)
    (hv_coprime : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ))
    (hv_q_ge2 : ∀ i, 2 ≤ ((v i).2 : ℕ))
    (hv_disc : IsDiscontinuityK v) :
    IsKnownDiscMod v := by
  set t := FracTuple.toNatTriple v with ht_def
  have ht_mem : t ∈ BoundedDiscCandidates :=
    isDiscontinuityK_imp_mem_BoundedDiscCandidates hv_valid hv_disc hv_le3
      hv_coprime hv_q_ge2
  have ht_dc : t ∈ discCandidates := (mem_BoundedDiscCandidates.mp ht_mem).1
  -- discCandidates membership unpacks into per-slot fracPairCandidates membership.
  unfold discCandidates at ht_dc
  rw [Finset.mem_product, Finset.mem_product] at ht_dc
  obtain ⟨h0, h1, h2⟩ := ht_dc
  -- Apply the classification hypothesis.
  have h_class_t := h_class t ht_mem h0 h1 h2
  -- v = fracTupleOf t h0 h1 h2.
  have h_v_eq : v = fracTupleOf t h0 h1 h2 :=
    fracTupleOf_eq_of_toNatTriple t h0 h1 h2 ht_def.symm
  rcases h_class_t with h_known | h_not_disc
  · -- IsKnownDiscMod (fracTupleOf ...). Transfer back to v via h_v_eq.
    rw [h_v_eq]; exact h_known
  · -- ¬ IsDiscontinuityK (fracTupleOf ...). But hv_disc : IsDiscontinuityK v
    -- and v = fracTupleOf ..., so contradiction.
    rw [h_v_eq] at hv_disc
    exact absurd hv_disc h_not_disc

/-! ## Bool-level classifier infrastructure

A computable classifier that, for each `t : (ℕ × ℕ)³`, returns `true` if `t`
is either a known disc multiset OR a non-disc certified by one of the
available algebraic upper bounds (nested floor, interval bounds, Baumert
bounds, mixed bounds).

The classifier compiles to a `native_decide`-friendly Bool predicate. The
correctness theorem `decideClassified_correct` proves that whenever it
returns `true`, `IsClassifiedNat t h0 h1 h2` holds.
-/

/-! ### Bool predicates: known-disc match, multiset matching, etc. -/

/-- The 12 paper-canonical α₃-disc multisets in `(ℕ × ℕ)³` form, with their
    α₃ values. Used by the classifier for "is t a known disc?" checks and for
    `alphaDiscBelowValue` (the largest α₃ over known discs ≤ₚ t). -/
def knownDiscNatList : List (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) :=
  [ (((2, 1), (2, 1), (2, 1)), 8),
    (((2, 1), (2, 1), (3, 1)), 12),
    (((2, 1), (3, 1), (3, 1)), 18),
    (((3, 1), (3, 1), (3, 1)), 27),
    (((2, 1), (5, 2), (5, 2)), 10),
    (((3, 1), (5, 2), (5, 2)), 15),
    (((5, 2), (5, 2), (8, 3)), 11),
    (((8, 3), (8, 3), (8, 3)), 12),
    (((9, 4), (7, 3), (5, 2)), 9),
    (((11, 5), (11, 4), (11, 4)), 11),
    (((11, 4), (11, 4), (11, 4)), 13),
    (((14, 5), (14, 5), (14, 5)), 14) ]

/-- `t` matches the multiset of `m` (some permutation of `t` equals `m` as
    pointed `(ℕ × ℕ)³`). Bool-level for `native_decide`. -/
def matchesMultisetNat (t m : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  let ⟨a, b, c⟩ := t
  let ⟨x, y, z⟩ := m
  (a == x && b == y && c == z) || (a == x && b == z && c == y) ||
  (a == y && b == x && c == z) || (a == y && b == z && c == x) ||
  (a == z && b == x && c == y) || (a == z && b == y && c == x)

/-- `t` matches one of the 12 paper-canonical disc multisets. -/
def isKnownDiscNat (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  knownDiscNatList.any (fun (m, _) => matchesMultisetNat t m)

/-- The largest `α₃(d)` over known disc multisets `d` with `d ≤ₚ t`
    (multiset). Used as a lower bound on `α₃(t)` (by monotonicity) for
    establishing non-disc witnesses. -/
def alphaDiscBelowValue (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  knownDiscNatList.foldl (fun acc (m, αm) =>
    if lePermNat m t = true then max acc αm else acc) 0

/-- Strict version: largest `α₃(d)` over known discs `d` with `d <ₚ t`
    (strict multiset less-than). Used to construct strict witnesses for
    Route B of the converse. -/
def alphaDiscStrictBelowValue (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  knownDiscNatList.foldl (fun acc (m, αm) =>
    if ltPermNat m t = true then max acc αm else acc) 0

/-! ### Max numerator -/

/-- Max numerator across the three slots of `t`. -/
def maxNumeratorNat (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  max t.1.1 (max t.2.1.1 t.2.2.1)

/-! ### Combined per-tuple upper bound on `alphaK`

The bound combines (a) `nestedFloor3NatMin`, (b) the diagonal interval bounds
(`α ≤ 8` if all ratios `< 5/2`; `≤ 10` if all `< 8/3`; `≤ 12` if all `< 11/4`),
and (c) the 15 Baumert match-bounds.

For each candidate `t`, we use whichever bounds apply, taking the minimum.
The Bool predicate `existingUpperBoundLeNat t B` returns `true` iff
`B` is a known upper bound for `alphaK (fracTupleOf t)`.

Since the algebraic bound theorems live at the Prop/term level (not Bool), the
correctness lemma combines them by case analysis on each component. -/

/-- Bool: all three slot ratios are `< num/den`. -/
def allRatiosLtNat (num den : ℕ) (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (den * t.1.1 < num * t.1.2 ∧
          den * t.2.1.1 < num * t.2.1.2 ∧
          den * t.2.2.1 < num * t.2.2.2)

/-- Bool: `t` matches one of the 15 Baumert multisets, returning the
    corresponding bound (or none, encoded as `(false, 0)`). -/
def baumertBoundNat (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Option ℕ :=
  let candidates : List (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) :=
    [ (((5, 2), (5, 2), (8, 3)), 11),
      (((8, 3), (8, 3), (8, 3)), 12),
      (((7, 3), (7, 3), (7, 3)), 8),
      (((5, 2), (5, 2), (5, 2)), 10),
      (((5, 2), (8, 3), (8, 3)), 11),
      (((9, 4), (9, 4), (5, 2)), 8),
      (((9, 4), (9, 4), (8, 3)), 8),
      (((8, 3), (11, 4), (13, 5)), 12),
      (((11, 4), (11, 4), (13, 5)), 12),
      (((11, 4), (13, 5), (13, 5)), 12),
      (((8, 3), (8, 3), (11, 4)), 12),
      (((8, 3), (11, 4), (11, 4)), 12),
      (((5, 2), (5, 2), (11, 4)), 11),
      (((5, 2), (8, 3), (11, 4)), 11),
      (((5, 2), (11, 4), (11, 4)), 11) ]
  let matched := candidates.filter (fun (m, _) => matchesMultisetNat t m)
  matched.foldl (fun acc (_, b) =>
    match acc with
    | none => some b
    | some a => some (min a b)) none

/-- Combined upper bound on `alphaK` from `nestedFloor3NatMin`, the three
    interval bounds, and the 15 Baumert multiset bounds. -/
def existingUpperBoundNat (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  let nf := nestedFloor3NatMin t
  let nf := if allRatiosLtNat 5 2 t then min nf 8 else nf
  let nf := if allRatiosLtNat 8 3 t then min nf 10 else nf
  let nf := if allRatiosLtNat 11 4 t then min nf 12 else nf
  match baumertBoundNat t with
  | none => nf
  | some b => min nf b

/-! ### Bool classifier `decideNonDiscNat`

For a non-known `t`, the classifier returns `true` if either Route A
(`existingUpperBoundNat t < maxNumeratorNat t`) or Route B
(`existingUpperBoundNat t ≤ alphaDiscStrictBelowValue t`) certifies that
`fracTupleOf t` cannot be an α₃-discontinuity. -/

/-- Bool decision: `t` is either a known disc, or one of Route A / Route B
    rules out `IsDiscontinuityK (fracTupleOf t)`. -/
def decideClassifiedNat (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  isKnownDiscNat t ||
  decide (existingUpperBoundNat t < maxNumeratorNat t) ||
  knownDiscNatList.any (fun (d, αd) =>
    lePermNat d t && !lePermNat t d &&
    decide (existingUpperBoundNat t ≤ αd))

/-! ## Bridge: `lePermK` ↔ `lePermNat`

We need to lift the Bool-level multiset-`≤` `lePermNat` to the `Prop`-level
`lePermK` so witnesses constructed Bool-level can be used as actual
`FracTuple` discontinuity witnesses. -/

/-- Bool-level `≤` on a single `(p, q)` pair (rationals) lifts to `≤` on `toRat`. -/
private lemma toRat_le_of_lePairNat
    {p1 q1 p2 q2 : ℕ+} (h : lePairNat (p1, q1) (p2, q2) = true) :
    ((p1 : ℕ) : ℚ) / ((q1 : ℕ) : ℚ) ≤ ((p2 : ℕ) : ℚ) / ((q2 : ℕ) : ℚ) := by
  unfold lePairNat at h
  simp only [decide_eq_true_eq] at h
  have hq1_pos : (0 : ℚ) < ((q1 : ℕ) : ℚ) := by exact_mod_cast q1.pos
  have hq2_pos : (0 : ℚ) < ((q2 : ℕ) : ℚ) := by exact_mod_cast q2.pos
  rw [div_le_div_iff₀ hq1_pos hq2_pos]
  exact_mod_cast h

/-! ### Construct a `FracTuple 3` from a `(ℕ × ℕ)³` triple of `fracPairCandidates` -/

/-- The disc tuple multisets in `(ℕ × ℕ)³` form (just keys of `knownDiscNatList`). -/
def knownDiscMults : List ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  knownDiscNatList.map (·.1)

/-! ## α-value at known disc multisets

For each of the 12 paper canonical disc multisets `d` (with α-value `αd`), we
have `alphaK (fracTupleFromKnownMult d) = αd`. The proof packages this as a
list-indexed lookup. -/

/-- Pair up `knownDiscList` (canonical FracTuple form) with α-values.
    Order matches `knownDiscNatList`. -/
def knownDiscWithAlpha : List (FracTuple 3 × ℕ) :=
  [ (triple222, 8),
    (triple223, 12),
    (triple233, 18),
    (triple333, 27),
    (triple_2_5o2_5o2, 10),
    (triple_5o2_5o2_3, 15),
    (triple_5o2_5o2_8o3, 11),
    (triple_8o3_8o3_8o3, 12),
    (triple_9o4_7o3_5o2, 9),
    (triple_11o5_11o4_11o4, 11),
    (triple_11o4_11o4_11o4, 13),
    (triple_14o5_14o5_14o5, 14) ]

/-! ### Algebraic upper bound on `alphaK (fracTupleOf t)`

The bound `existingUpperBoundNat t` aggregates the four sources of upper
bounds: nested floor (any of 6 perms), interval bounds, Baumert match. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The interval bound at `5/2`: if all ratios are `< 5/2`, then `alphaK ≤ 8`. -/
private lemma alphaK_le_of_allRatiosLt_5_2
    {v : FracTuple 3} (hv : ValidK v)
    (h : allRatiosLtNat 5 2 (FracTuple.toNatTriple v) = true) :
    alphaK v ≤ 8 := by
  unfold allRatiosLtNat FracTuple.toNatTriple at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  haveI : NeZero ((v 0).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 0).1.pos⟩
  haveI : NeZero ((v 1).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 1).1.pos⟩
  haveI : NeZero ((v 2).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 2).1.pos⟩
  have h2q0 : 2 * ((v 0).2 : ℕ) ≤ ((v 0).1 : ℕ) := by exact_mod_cast hv 0
  have h2q1 : 2 * ((v 1).2 : ℕ) ≤ ((v 1).1 : ℕ) := by exact_mod_cast hv 1
  have h2q2 : 2 * ((v 2).2 : ℕ) ≤ ((v 2).1 : ℕ) := by exact_mod_cast hv 2
  rw [alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_le_8_of_lt_5o2 _ _ _ _ _ _
    (v 0).2.pos h2q0 h0
    (v 1).2.pos h2q1 h1
    (v 2).2.pos h2q2 h2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The interval bound at `8/3`: if all ratios are `< 8/3`, then `alphaK ≤ 10`. -/
private lemma alphaK_le_of_allRatiosLt_8_3
    {v : FracTuple 3} (hv : ValidK v)
    (h : allRatiosLtNat 8 3 (FracTuple.toNatTriple v) = true) :
    alphaK v ≤ 10 := by
  unfold allRatiosLtNat FracTuple.toNatTriple at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  haveI : NeZero ((v 0).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 0).1.pos⟩
  haveI : NeZero ((v 1).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 1).1.pos⟩
  haveI : NeZero ((v 2).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 2).1.pos⟩
  have h2q0 : 2 * ((v 0).2 : ℕ) ≤ ((v 0).1 : ℕ) := by exact_mod_cast hv 0
  have h2q1 : 2 * ((v 1).2 : ℕ) ≤ ((v 1).1 : ℕ) := by exact_mod_cast hv 1
  have h2q2 : 2 * ((v 2).2 : ℕ) ≤ ((v 2).1 : ℕ) := by exact_mod_cast hv 2
  rw [alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_le_10_of_lt_8o3 _ _ _ _ _ _
    (v 0).2.pos h2q0 h0
    (v 1).2.pos h2q1 h1
    (v 2).2.pos h2q2 h2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The interval bound at `11/4`: if all ratios are `< 11/4`, then `alphaK ≤ 12`. -/
private lemma alphaK_le_of_allRatiosLt_11_4
    {v : FracTuple 3} (hv : ValidK v)
    (h : allRatiosLtNat 11 4 (FracTuple.toNatTriple v) = true) :
    alphaK v ≤ 12 := by
  unfold allRatiosLtNat FracTuple.toNatTriple at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  haveI : NeZero ((v 0).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 0).1.pos⟩
  haveI : NeZero ((v 1).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 1).1.pos⟩
  haveI : NeZero ((v 2).1 : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (v 2).1.pos⟩
  have h2q0 : 2 * ((v 0).2 : ℕ) ≤ ((v 0).1 : ℕ) := by exact_mod_cast hv 0
  have h2q1 : 2 * ((v 1).2 : ℕ) ≤ ((v 1).1 : ℕ) := by exact_mod_cast hv 1
  have h2q2 : 2 * ((v 2).2 : ℕ) ≤ ((v 2).1 : ℕ) := by exact_mod_cast hv 2
  rw [alphaK_three]
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_le_12_of_lt_11o4 _ _ _ _ _ _
    (v 0).2.pos h2q0 h0
    (v 1).2.pos h2q1 h1
    (v 2).2.pos h2q2 h2

/-- For triples in `discCandidates`, the auto-derived q ≥ 2 condition can
    fail (the candidate set allows q = 1, integer slots). When q = 1, Route A
    cannot directly close the candidate (the numerator-bound theorem assumes
    q ≥ 2 for non-trivial coprimality). The integer-slot case is handled by
    `lem:disc-integer` (paper line 2851), reducing to a 2-factor analysis.

    For triples with all q ≥ 2, the `mem_fracPairCandidates` membership and
    the lowest-terms hypothesis decode the prerequisite hypotheses. -/
private lemma fracTupleOf_q_coprime_of_q_ge2
    (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (h_q_ge2 : 2 ≤ t.1.2 ∧ 2 ≤ t.2.1.2 ∧ 2 ≤ t.2.2.2)
    (h_coprime : Nat.Coprime t.1.1 t.1.2 ∧
                 Nat.Coprime t.2.1.1 t.2.1.2 ∧
                 Nat.Coprime t.2.2.1 t.2.2.2) :
    (∀ i, 2 ≤ ((fracTupleOf t h0 h1 h2 i).2 : ℕ)) ∧
    (∀ i, Nat.Coprime ((fracTupleOf t h0 h1 h2 i).1 : ℕ)
                       ((fracTupleOf t h0 h1 h2 i).2 : ℕ)) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact h_q_ge2.1
    · exact h_q_ge2.2.1
    · exact h_q_ge2.2.2
  · fin_cases i
    · exact h_coprime.1
    · exact h_coprime.2.1
    · exact h_coprime.2.2

/-! ## Route B infrastructure: `lePermNat`/α-values/canonical-tuple helpers

The bridge `lePermNat d (toNatTriple v) → lePermK (canonical d) v` and the
α-values, ValidK proofs, and `toNatTriple` rfl-lemmas at each of the 12
canonical disc FracTuples are shared infrastructure used by
`routeB_via_disc_full` (the Baumert-aware Route B). -/

/-! ### Bridge: `lePermNat d (toNatTriple v) → lePermK (canonical d) v`

Given a canonical FracTuple `d` of one of the 12 discs, if
`lePermNat (toNatTriple d) (toNatTriple v) = true`, then `lePermK d v`. The
proof: the 6 disjuncts of `lePermNat` correspond to the 6 permutations of
`Fin 3`, each providing a witness `σ` for `lePermK`. -/

/-- Bool→Prop conversion for `lePairNat`: `lePairNat (p1, q1) (p2, q2) = true ↔
    (p1 : ℚ) / q1 ≤ (p2 : ℚ) / q2` (when q1, q2 > 0). One direction (the easier). -/
private lemma toRat_pair_le_of_lePairNat
    (p1 q1 p2 q2 : ℕ) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (h : lePairNat (p1, q1) (p2, q2) = true) :
    ((p1 : ℚ) / (q1 : ℚ)) ≤ ((p2 : ℚ) / (q2 : ℚ)) := by
  unfold lePairNat at h
  simp only [decide_eq_true_eq] at h
  have hq1_pos : (0 : ℚ) < (q1 : ℚ) := by exact_mod_cast hq1
  have hq2_pos : (0 : ℚ) < (q2 : ℚ) := by exact_mod_cast hq2
  rw [div_le_div_iff₀ hq1_pos hq2_pos]
  exact_mod_cast h

/-- Helper: given pairwise `lePairNat`-truth at three matched slot pairs of
    `FracTuple 3`s `u` and `v`, and a `σ : Equiv.Perm (Fin 3)` matching the
    three pairings, conclude `lePermK u v` via the σ. -/
private lemma lePermK_of_three_lePairNat
    (u v : FracTuple 3) (σ : Equiv.Perm (Fin 3))
    (h0 : lePairNat (((u (σ 0)).1 : ℕ), ((u (σ 0)).2 : ℕ))
                    (((v 0).1 : ℕ), ((v 0).2 : ℕ)) = true)
    (h1 : lePairNat (((u (σ 1)).1 : ℕ), ((u (σ 1)).2 : ℕ))
                    (((v 1).1 : ℕ), ((v 1).2 : ℕ)) = true)
    (h2 : lePairNat (((u (σ 2)).1 : ℕ), ((u (σ 2)).2 : ℕ))
                    (((v 2).1 : ℕ), ((v 2).2 : ℕ)) = true) :
    lePermK u v := by
  refine ⟨σ, fun i => ?_⟩
  -- Per-slot conversion at any i.
  have hk : ∀ k : Fin 3,
      lePairNat (((u (σ k)).1 : ℕ), ((u (σ k)).2 : ℕ))
                 (((v k).1 : ℕ), ((v k).2 : ℕ)) = true →
      FracTuple.toRat u (σ k) ≤ FracTuple.toRat v k := by
    intro k h
    unfold FracTuple.toRat
    exact toRat_pair_le_of_lePairNat _ _ _ _ (u (σ k)).2.pos (v k).2.pos h
  -- Three cases: i = 0, 1, 2.
  fin_cases i
  · exact hk 0 h0
  · exact hk 1 h1
  · exact hk 2 h2

/-- Helper: extract the 6 disjuncts of `lePermNat u v = true` as an Or-chain
    of triples of `lePairNat ... = true`. -/
private lemma lePermNat_decompose
    (u v : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h : lePermNat u v = true) :
    (lePairNat u.1 v.1 = true ∧ lePairNat u.2.1 v.2.1 = true ∧ lePairNat u.2.2 v.2.2 = true) ∨
    (lePairNat u.1 v.1 = true ∧ lePairNat u.2.2 v.2.1 = true ∧ lePairNat u.2.1 v.2.2 = true) ∨
    (lePairNat u.2.1 v.1 = true ∧ lePairNat u.1 v.2.1 = true ∧ lePairNat u.2.2 v.2.2 = true) ∨
    (lePairNat u.2.1 v.1 = true ∧ lePairNat u.2.2 v.2.1 = true ∧ lePairNat u.1 v.2.2 = true) ∨
    (lePairNat u.2.2 v.1 = true ∧ lePairNat u.1 v.2.1 = true ∧ lePairNat u.2.1 v.2.2 = true) ∨
    (lePairNat u.2.2 v.1 = true ∧ lePairNat u.2.1 v.2.1 = true ∧ lePairNat u.1 v.2.2 = true) := by
  -- Decompose u, v so the lePermNat let-binders reduce.
  obtain ⟨a, b, c⟩ := u
  obtain ⟨x, y, z⟩ := v
  -- After destructuring, `lePermNat (a, b, c) (x, y, z)` reduces by `let`-binders.
  -- The hypothesis `h` is of the underlying Bool-disjunction form.
  change ((lePairNat a x && lePairNat b y && lePairNat c z) ||
          (lePairNat a x && lePairNat c y && lePairNat b z) ||
          (lePairNat b x && lePairNat a y && lePairNat c z) ||
          (lePairNat b x && lePairNat c y && lePairNat a z) ||
          (lePairNat c x && lePairNat a y && lePairNat b z) ||
          (lePairNat c x && lePairNat b y && lePairNat a z)) = true at h
  change (lePairNat a x = true ∧ lePairNat b y = true ∧ lePairNat c z = true) ∨
         (lePairNat a x = true ∧ lePairNat c y = true ∧ lePairNat b z = true) ∨
         (lePairNat b x = true ∧ lePairNat a y = true ∧ lePairNat c z = true) ∨
         (lePairNat b x = true ∧ lePairNat c y = true ∧ lePairNat a z = true) ∨
         (lePairNat c x = true ∧ lePairNat a y = true ∧ lePairNat b z = true) ∨
         (lePairNat c x = true ∧ lePairNat b y = true ∧ lePairNat a z = true)
  -- Manually peel the Bool-or chain using Bool.or_eq_true.
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.or_eq_true] at h
        rcases h with h | h
        · rw [Bool.or_eq_true] at h
          rcases h with h | h
          · rw [Bool.and_eq_true, Bool.and_eq_true] at h
            exact Or.inl ⟨h.1.1, h.1.2, h.2⟩
          · rw [Bool.and_eq_true, Bool.and_eq_true] at h
            exact Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩)
        · rw [Bool.and_eq_true, Bool.and_eq_true] at h
          exact Or.inr (Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩))
      · rw [Bool.and_eq_true, Bool.and_eq_true] at h
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩)))
    · rw [Bool.and_eq_true, Bool.and_eq_true] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩))))
  · rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1.1, h.1.2, h.2⟩))))

/-- **lePermNat → lePermK bridge for FracTuple 3.** If
    `lePermNat (toNatTriple u) (toNatTriple v) = true`, then `lePermK u v`. -/
lemma lePermK_of_lePermNat (u v : FracTuple 3)
    (h : lePermNat (FracTuple.toNatTriple u) (FracTuple.toNatTriple v) = true) :
    lePermK u v := by
  rcases lePermNat_decompose _ _ h with
    ⟨h0, h1, h2⟩ | ⟨h0, h2, h1⟩ | ⟨h1, h0, h2⟩ |
    ⟨h1, h2, h0⟩ | ⟨h2, h0, h1⟩ | ⟨h2, h1, h0⟩
  · -- σ = 1 (identity)
    refine lePermK_of_three_lePairNat u v 1 ?_ ?_ ?_ <;>
      (simp only [Equiv.Perm.coe_one, id_eq, FracTuple.toNatTriple] at *; assumption)
  · -- σ = swap 1 2: σ 0 = 0, σ 1 = 2, σ 2 = 1
    refine lePermK_of_three_lePairNat u v (Equiv.swap 1 2) ?_ ?_ ?_
    · have hσ : (Equiv.swap (1:Fin 3) 2) 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      rw [hσ]; exact h0
    · have hσ : (Equiv.swap (1:Fin 3) 2) 1 = 2 := Equiv.swap_apply_left 1 2
      rw [hσ]; exact h2
    · have hσ : (Equiv.swap (1:Fin 3) 2) 2 = 1 := Equiv.swap_apply_right 1 2
      rw [hσ]; exact h1
  · -- σ = swap 0 1: σ 0 = 1, σ 1 = 0, σ 2 = 2
    refine lePermK_of_three_lePairNat u v (Equiv.swap 0 1) ?_ ?_ ?_
    · have hσ : (Equiv.swap (0:Fin 3) 1) 0 = 1 := Equiv.swap_apply_left 0 1
      rw [hσ]; exact h1
    · have hσ : (Equiv.swap (0:Fin 3) 1) 1 = 0 := Equiv.swap_apply_right 0 1
      rw [hσ]; exact h0
    · have hσ : (Equiv.swap (0:Fin 3) 1) 2 = 2 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      rw [hσ]; exact h2
  · -- σ with σ 0 = 1, σ 1 = 2, σ 2 = 0
    refine lePermK_of_three_lePairNat u v (Equiv.swap 1 2 * Equiv.swap 0 2) ?_ ?_ ?_
    · have hσ : (Equiv.swap (1:Fin 3) 2 * Equiv.swap (0:Fin 3) 2) 0 = 1 := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [hσ]; exact h1
    · have hσ : (Equiv.swap (1:Fin 3) 2 * Equiv.swap (0:Fin 3) 2) 1 = 2 := by
        rw [Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (show (1:Fin 3) ≠ 0 by decide)
              (show (1:Fin 3) ≠ 2 by decide),
            Equiv.swap_apply_left]
      rw [hσ]; exact h2
    · have hσ : (Equiv.swap (1:Fin 3) 2 * Equiv.swap (0:Fin 3) 2) 2 = 0 := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne (show (0:Fin 3) ≠ 1 by decide)
              (show (0:Fin 3) ≠ 2 by decide)]
      rw [hσ]; exact h0
  · -- σ with σ 0 = 2, σ 1 = 0, σ 2 = 1
    refine lePermK_of_three_lePairNat u v (Equiv.swap 0 2 * Equiv.swap 1 2) ?_ ?_ ?_
    · have hσ : (Equiv.swap (0:Fin 3) 2 * Equiv.swap (1:Fin 3) 2) 0 = 2 := by
        rw [Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (show (0:Fin 3) ≠ 1 by decide)
              (show (0:Fin 3) ≠ 2 by decide),
            Equiv.swap_apply_left]
      rw [hσ]; exact h2
    · have hσ : (Equiv.swap (0:Fin 3) 2 * Equiv.swap (1:Fin 3) 2) 1 = 0 := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [hσ]; exact h0
    · have hσ : (Equiv.swap (0:Fin 3) 2 * Equiv.swap (1:Fin 3) 2) 2 = 1 := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne (show (1:Fin 3) ≠ 0 by decide)
              (show (1:Fin 3) ≠ 2 by decide)]
      rw [hσ]; exact h1
  · -- σ = swap 0 2: σ 0 = 2, σ 1 = 1, σ 2 = 0
    refine lePermK_of_three_lePairNat u v (Equiv.swap 0 2) ?_ ?_ ?_
    · have hσ : (Equiv.swap (0:Fin 3) 2) 0 = 2 := Equiv.swap_apply_left 0 2
      rw [hσ]; exact h2
    · have hσ : (Equiv.swap (0:Fin 3) 2) 1 = 1 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      rw [hσ]; exact h1
    · have hσ : (Equiv.swap (0:Fin 3) 2) 2 = 0 := Equiv.swap_apply_right 0 2
      rw [hσ]; exact h0

/-! ### α-values at the 12 canonical disc FracTuples

For each known disc (in canonical FracTuple form), `alphaK d = α-value`. -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple222 : alphaK triple222 = 8 := by
  rw [alphaK_three]
  change ((fractionGraph 2 1 ⊠ fractionGraph 2 1) ⊠ fractionGraph 2 1).indepNum = 8
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_2_2_2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple223 : alphaK triple223 = 12 := by
  rw [alphaK_three]
  change ((fractionGraph 2 1 ⊠ fractionGraph 2 1) ⊠ fractionGraph 3 1).indepNum = 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_2_2_3

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple233 : alphaK triple233 = 18 := by
  rw [alphaK_three]
  change ((fractionGraph 2 1 ⊠ fractionGraph 3 1) ⊠ fractionGraph 3 1).indepNum = 18
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_2_3_3

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple333 : alphaK triple333 = 27 := by
  rw [alphaK_three]
  change ((fractionGraph 3 1 ⊠ fractionGraph 3 1) ⊠ fractionGraph 3 1).indepNum = 27
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_3_3_3

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple_2_5o2_5o2 : alphaK triple_2_5o2_5o2 = 10 := by
  rw [alphaK_three]
  change ((fractionGraph 2 1 ⊠ fractionGraph 5 2) ⊠ fractionGraph 5 2).indepNum = 10
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_2_5o2_5o2

/-- Disc-list-order canonical: `![(3,1),(5,2),(5,2)]`. Matches the
    `((3,1),(5,2),(5,2))` entry in `knownDiscNatList`; ordered to allow direct
    bridge to `alpha3_5o2_5o2_3`. -/
def triple_3_5o2_5o2 : FracTuple 3 := ![(3, 1), (5, 2), (5, 2)]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple_3_5o2_5o2 : alphaK triple_3_5o2_5o2 = 15 := by
  rw [alphaK_three]
  change ((fractionGraph 3 1 ⊠ fractionGraph 5 2) ⊠ fractionGraph 5 2).indepNum = 15
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_5o2_5o2_3

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple_5o2_5o2_8o3 : alphaK triple_5o2_5o2_8o3 = 11 := by
  rw [alphaK_three]
  change ((fractionGraph 5 2 ⊠ fractionGraph 5 2) ⊠ fractionGraph 8 3).indepNum = 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_5o2_5o2_8o3

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple_8o3_8o3_8o3 : alphaK triple_8o3_8o3_8o3 = 12 := by
  rw [alphaK_three]
  change ((fractionGraph 8 3 ⊠ fractionGraph 8 3) ⊠ fractionGraph 8 3).indepNum = 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_8o3_8o3_8o3

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple_9o4_7o3_5o2 : alphaK triple_9o4_7o3_5o2 = 9 := by
  rw [alphaK_three]
  change ((fractionGraph 9 4 ⊠ fractionGraph 7 3) ⊠ fractionGraph 5 2).indepNum = 9
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_9o4_7o3_5o2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple_11o5_11o4_11o4 : alphaK triple_11o5_11o4_11o4 = 11 := by
  rw [alphaK_three]
  change ((fractionGraph 11 5 ⊠ fractionGraph 11 4) ⊠ fractionGraph 11 4).indepNum = 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_11o5_11o4_11o4

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple_11o4_11o4_11o4 : alphaK triple_11o4_11o4_11o4 = 13 := by
  rw [alphaK_three]
  change ((fractionGraph 11 4 ⊠ fractionGraph 11 4) ⊠ fractionGraph 11 4).indepNum = 13
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_11o4_11o4_11o4

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma alphaK_triple_14o5_14o5_14o5 : alphaK triple_14o5_14o5_14o5 = 14 := by
  rw [alphaK_three]
  change ((fractionGraph 14 5 ⊠ fractionGraph 14 5) ⊠ fractionGraph 14 5).indepNum = 14
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_14o5_14o5_14o5

/-- ValidK at each canonical disc FracTuple. -/
private lemma validK_triple222 : ValidK triple222 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple223 : ValidK triple223 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple233 : ValidK triple233 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple333 : ValidK triple333 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_2_5o2_5o2 : ValidK triple_2_5o2_5o2 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_3_5o2_5o2 : ValidK triple_3_5o2_5o2 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_5o2_5o2_8o3 : ValidK triple_5o2_5o2_8o3 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_8o3_8o3_8o3 : ValidK triple_8o3_8o3_8o3 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_9o4_7o3_5o2 : ValidK triple_9o4_7o3_5o2 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_11o5_11o4_11o4 : ValidK triple_11o5_11o4_11o4 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_11o4_11o4_11o4 : ValidK triple_11o4_11o4_11o4 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_14o5_14o5_14o5 : ValidK triple_14o5_14o5_14o5 := by
  intro i; fin_cases i <;> decide

/-- toNatTriple of each canonical disc. -/
private lemma toNatTriple_triple222 :
    FracTuple.toNatTriple triple222 = ((2,1),(2,1),(2,1)) := rfl
private lemma toNatTriple_triple223 :
    FracTuple.toNatTriple triple223 = ((2,1),(2,1),(3,1)) := rfl
private lemma toNatTriple_triple233 :
    FracTuple.toNatTriple triple233 = ((2,1),(3,1),(3,1)) := rfl
private lemma toNatTriple_triple333 :
    FracTuple.toNatTriple triple333 = ((3,1),(3,1),(3,1)) := rfl
private lemma toNatTriple_triple_2_5o2_5o2 :
    FracTuple.toNatTriple triple_2_5o2_5o2 = ((2,1),(5,2),(5,2)) := rfl
private lemma toNatTriple_triple_3_5o2_5o2 :
    FracTuple.toNatTriple triple_3_5o2_5o2 = ((3,1),(5,2),(5,2)) := rfl
private lemma toNatTriple_triple_5o2_5o2_3 :
    FracTuple.toNatTriple triple_5o2_5o2_3 = ((5,2),(5,2),(3,1)) := rfl
private lemma toNatTriple_triple_5o2_5o2_8o3 :
    FracTuple.toNatTriple triple_5o2_5o2_8o3 = ((5,2),(5,2),(8,3)) := rfl
private lemma toNatTriple_triple_8o3_8o3_8o3 :
    FracTuple.toNatTriple triple_8o3_8o3_8o3 = ((8,3),(8,3),(8,3)) := rfl
private lemma toNatTriple_triple_9o4_7o3_5o2 :
    FracTuple.toNatTriple triple_9o4_7o3_5o2 = ((9,4),(7,3),(5,2)) := rfl
private lemma toNatTriple_triple_11o5_11o4_11o4 :
    FracTuple.toNatTriple triple_11o5_11o4_11o4 = ((11,5),(11,4),(11,4)) := rfl
private lemma toNatTriple_triple_11o4_11o4_11o4 :
    FracTuple.toNatTriple triple_11o4_11o4_11o4 = ((11,4),(11,4),(11,4)) := rfl
private lemma toNatTriple_triple_14o5_14o5_14o5 :
    FracTuple.toNatTriple triple_14o5_14o5_14o5 = ((14,5),(14,5),(14,5)) := rfl

/-! ## Baumert bound bridges: `alphaK v ≤ B` from `matchesMultisetNat` -/

/-- Generic helper: if `v : FracTuple 3` has each slot's `(p, q)` equal to a
    canonical `w`'s slot's `(p, q)` as nat values, then `alphaK v = alphaK w`. -/
private lemma alphaK_eq_of_pq_match {v w : FracTuple 3}
    (h_valid_v : ValidK v) (h_valid_w : ValidK w)
    (h0p : ((v 0).1 : ℕ) = ((w 0).1 : ℕ)) (h0q : ((v 0).2 : ℕ) = ((w 0).2 : ℕ))
    (h1p : ((v 1).1 : ℕ) = ((w 1).1 : ℕ)) (h1q : ((v 1).2 : ℕ) = ((w 1).2 : ℕ))
    (h2p : ((v 2).1 : ℕ) = ((w 2).1 : ℕ)) (h2q : ((v 2).2 : ℕ) = ((w 2).2 : ℕ)) :
    alphaK v = alphaK w := by
  apply alphaK_eq_of_toRat_eq h_valid_v h_valid_w
  intro i
  fin_cases i
  · unfold FracTuple.toRat
    have hp : (((v 0).1 : ℕ) : ℚ) = (((w 0).1 : ℕ) : ℚ) := by exact_mod_cast h0p
    have hq : (((v 0).2 : ℕ) : ℚ) = (((w 0).2 : ℕ) : ℚ) := by exact_mod_cast h0q
    push_cast at hp hq ⊢
    rw [hp, hq]
  · unfold FracTuple.toRat
    have hp : (((v 1).1 : ℕ) : ℚ) = (((w 1).1 : ℕ) : ℚ) := by exact_mod_cast h1p
    have hq : (((v 1).2 : ℕ) : ℚ) = (((w 1).2 : ℕ) : ℚ) := by exact_mod_cast h1q
    push_cast at hp hq ⊢
    rw [hp, hq]
  · unfold FracTuple.toRat
    have hp : (((v 2).1 : ℕ) : ℚ) = (((w 2).1 : ℕ) : ℚ) := by exact_mod_cast h2p
    have hq : (((v 2).2 : ℕ) : ℚ) = (((w 2).2 : ℕ) : ℚ) := by exact_mod_cast h2q
    push_cast at hp hq ⊢
    rw [hp, hq]

/-- Decompose `matchesMultisetNat t m = true` into 6 permutation-disjuncts
    of pair equalities. -/
private lemma matchesMultisetNat_decompose
    (t m : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h : matchesMultisetNat t m = true) :
    (t.1 = m.1 ∧ t.2.1 = m.2.1 ∧ t.2.2 = m.2.2) ∨
    (t.1 = m.1 ∧ t.2.1 = m.2.2 ∧ t.2.2 = m.2.1) ∨
    (t.1 = m.2.1 ∧ t.2.1 = m.1 ∧ t.2.2 = m.2.2) ∨
    (t.1 = m.2.1 ∧ t.2.1 = m.2.2 ∧ t.2.2 = m.1) ∨
    (t.1 = m.2.2 ∧ t.2.1 = m.1 ∧ t.2.2 = m.2.1) ∨
    (t.1 = m.2.2 ∧ t.2.1 = m.2.1 ∧ t.2.2 = m.1) := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨x, y, z⟩ := m
  change ((a == x && b == y && c == z) || (a == x && b == z && c == y) ||
          (a == y && b == x && c == z) || (a == y && b == z && c == x) ||
          (a == z && b == x && c == y) || (a == z && b == y && c == x)) = true at h
  change (a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨
         (a = y ∧ b = x ∧ c = z) ∨ (a = y ∧ b = z ∧ c = x) ∨
         (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x)
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.or_eq_true] at h
        rcases h with h | h
        · rw [Bool.or_eq_true] at h
          rcases h with h | h
          · rw [Bool.and_eq_true, Bool.and_eq_true,
                beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
            exact Or.inl ⟨h.1.1, h.1.2, h.2⟩
          · rw [Bool.and_eq_true, Bool.and_eq_true,
                beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
            exact Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩)
        · rw [Bool.and_eq_true, Bool.and_eq_true,
              beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
          exact Or.inr (Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩))
      · rw [Bool.and_eq_true, Bool.and_eq_true,
            beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩)))
    · rw [Bool.and_eq_true, Bool.and_eq_true,
          beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩))))
  · rw [Bool.and_eq_true, Bool.and_eq_true,
        beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1.1, h.1.2, h.2⟩))))

/-- Generic Baumert bridge: given a canonical FracTuple `w` with `alphaK w ≤ αw`,
    ValidK, and `matchesMultisetNat (toNatTriple v) (toNatTriple w)`, conclude
    `alphaK v ≤ αw`. The match decomposes into 6 permutation cases; in each
    we apply `alphaK_perm` and `alphaK_eq_of_pq_match` to reduce to `w`. -/
private lemma alphaK_le_of_matches_canonical
    {v w : FracTuple 3} (h_valid_v : ValidK v) (h_valid_w : ValidK w)
    {αw : ℕ} (h_alpha_w : alphaK w ≤ αw)
    (h_match : matchesMultisetNat (FracTuple.toNatTriple v) (FracTuple.toNatTriple w) = true) :
    alphaK v ≤ αw := by
  -- Extract per-slot nat equalities from matchesMultisetNat.
  -- toNatTriple v = ((v0p, v0q), (v1p, v1q), (v2p, v2q)); same for w.
  rcases matchesMultisetNat_decompose _ _ h_match with
    h | h | h | h | h | h
  all_goals (
    obtain ⟨h0, h1, h2⟩ := h
    -- Each h_i is a pair-equality. Decompose.
    have e0p := congrArg Prod.fst h0
    have e0q := congrArg Prod.snd h0
    have e1p := congrArg Prod.fst h1
    have e1q := congrArg Prod.snd h1
    have e2p := congrArg Prod.fst h2
    have e2q := congrArg Prod.snd h2
    simp only [FracTuple.toNatTriple] at e0p e0q e1p e1q e2p e2q)
  · -- v σ = id: v slot k matches w slot k.
    have hα : alphaK v = alphaK w := by
      apply alphaK_eq_of_pq_match h_valid_v h_valid_w
      · exact e0p
      · exact e0q
      · exact e1p
      · exact e1q
      · exact e2p
      · exact e2q
    rw [hα]; exact h_alpha_w
  · -- σ swaps slots 1 and 2: v 0 matches w 0; v 1 matches w 2; v 2 matches w 1.
    rw [alphaK_perm v (Equiv.swap 1 2)]
    set u := v ∘ (Equiv.swap (1 : Fin 3) 2) with hu_def
    have hu_valid : ValidK u := fun i => h_valid_v ((Equiv.swap 1 2) i)
    have hu0 : u 0 = v 0 := by
      simp [hu_def,
        Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 3) ≠ 1 by decide)
          (show (0 : Fin 3) ≠ 2 by decide)]
    have hu1 : u 1 = v 2 := by
      simp [hu_def, Equiv.swap_apply_left]
    have hu2 : u 2 = v 1 := by
      simp [hu_def, Equiv.swap_apply_right]
    have hα : alphaK u = alphaK w := by
      apply alphaK_eq_of_pq_match hu_valid h_valid_w
      · rw [hu0]; exact e0p
      · rw [hu0]; exact e0q
      · rw [hu1]; exact e2p
      · rw [hu1]; exact e2q
      · rw [hu2]; exact e1p
      · rw [hu2]; exact e1q
    rw [hα]; exact h_alpha_w
  · -- σ swaps slots 0 and 1: v 0 matches w 1; v 1 matches w 0; v 2 matches w 2.
    rw [alphaK_perm v (Equiv.swap 0 1)]
    set u := v ∘ (Equiv.swap (0 : Fin 3) 1) with hu_def
    have hu_valid : ValidK u := fun i => h_valid_v ((Equiv.swap 0 1) i)
    have hu0 : u 0 = v 1 := by
      simp [hu_def, Equiv.swap_apply_left]
    have hu1 : u 1 = v 0 := by
      simp [hu_def, Equiv.swap_apply_right]
    have hu2 : u 2 = v 2 := by
      simp [hu_def,
        Equiv.swap_apply_of_ne_of_ne (show (2 : Fin 3) ≠ 0 by decide)
          (show (2 : Fin 3) ≠ 1 by decide)]
    have hα : alphaK u = alphaK w := by
      apply alphaK_eq_of_pq_match hu_valid h_valid_w
      · rw [hu0]; exact e1p
      · rw [hu0]; exact e1q
      · rw [hu1]; exact e0p
      · rw [hu1]; exact e0q
      · rw [hu2]; exact e2p
      · rw [hu2]; exact e2q
    rw [hα]; exact h_alpha_w
  · -- 4th disjunct: v 0 matches w 1, v 1 matches w 2, v 2 matches w 0.
    -- Need σ with σ 0 = 2, σ 1 = 0, σ 2 = 1 (so v ∘ σ aligns to w).
    rw [alphaK_perm v (Equiv.swap 0 2 * Equiv.swap 1 2)]
    set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 1 2 with hσ
    have hσ0 : σ 0 = 2 := by
      rw [hσ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 3) ≠ 1 by decide)
          (show (0 : Fin 3) ≠ 2 by decide),
        Equiv.swap_apply_left]
    have hσ1 : σ 1 = 0 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hσ2 : σ 2 = 1 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 3) ≠ 0 by decide)
          (show (1 : Fin 3) ≠ 2 by decide)]
    set u := v ∘ σ with hu_def
    have hu_valid : ValidK u := fun i => h_valid_v (σ i)
    have hu0 : u 0 = v 2 := by simp [hu_def, hσ0]
    have hu1 : u 1 = v 0 := by simp [hu_def, hσ1]
    have hu2 : u 2 = v 1 := by simp [hu_def, hσ2]
    have hα : alphaK u = alphaK w := by
      apply alphaK_eq_of_pq_match hu_valid h_valid_w
      · rw [hu0]; exact e2p
      · rw [hu0]; exact e2q
      · rw [hu1]; exact e0p
      · rw [hu1]; exact e0q
      · rw [hu2]; exact e1p
      · rw [hu2]; exact e1q
    rw [hα]; exact h_alpha_w
  · -- 5th disjunct: v 0 matches w 2, v 1 matches w 0, v 2 matches w 1.
    -- Need σ with σ 0 = 1, σ 1 = 2, σ 2 = 0.
    rw [alphaK_perm v (Equiv.swap 1 2 * Equiv.swap 0 2)]
    set σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 2 with hσ
    have hσ0 : σ 0 = 1 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hσ1 : σ 1 = 2 := by
      rw [hσ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 3) ≠ 0 by decide)
          (show (1 : Fin 3) ≠ 2 by decide),
        Equiv.swap_apply_left]
    have hσ2 : σ 2 = 0 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 3) ≠ 1 by decide)
          (show (0 : Fin 3) ≠ 2 by decide)]
    set u := v ∘ σ with hu_def
    have hu_valid : ValidK u := fun i => h_valid_v (σ i)
    have hu0 : u 0 = v 1 := by simp [hu_def, hσ0]
    have hu1 : u 1 = v 2 := by simp [hu_def, hσ1]
    have hu2 : u 2 = v 0 := by simp [hu_def, hσ2]
    have hα : alphaK u = alphaK w := by
      apply alphaK_eq_of_pq_match hu_valid h_valid_w
      · rw [hu0]; exact e1p
      · rw [hu0]; exact e1q
      · rw [hu1]; exact e2p
      · rw [hu1]; exact e2q
      · rw [hu2]; exact e0p
      · rw [hu2]; exact e0q
    rw [hα]; exact h_alpha_w
  · -- σ swaps slots 0 and 2: v 0 matches w 2, v 1 matches w 1, v 2 matches w 0.
    rw [alphaK_perm v (Equiv.swap 0 2)]
    set u := v ∘ (Equiv.swap (0 : Fin 3) 2) with hu_def
    have hu_valid : ValidK u := fun i => h_valid_v ((Equiv.swap 0 2) i)
    have hu0 : u 0 = v 2 := by
      simp [hu_def, Equiv.swap_apply_left]
    have hu1 : u 1 = v 1 := by
      simp [hu_def,
        Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 3) ≠ 0 by decide)
          (show (1 : Fin 3) ≠ 2 by decide)]
    have hu2 : u 2 = v 0 := by
      simp [hu_def, Equiv.swap_apply_right]
    have hα : alphaK u = alphaK w := by
      apply alphaK_eq_of_pq_match hu_valid h_valid_w
      · rw [hu0]; exact e2p
      · rw [hu0]; exact e2q
      · rw [hu1]; exact e1p
      · rw [hu1]; exact e1q
      · rw [hu2]; exact e0p
      · rw [hu2]; exact e0q
    rw [hα]; exact h_alpha_w

/-! ### Canonical FracTuples for the 15 Baumert multisets

For each Baumert multiset `M`, define a canonical `FracTuple 3` whose
`toNatTriple` equals `M`, and prove its `ValidK` and `alphaK ≤ B`. -/

private def triple_5o2_5o2_5o2 : FracTuple 3 := ![(5, 2), (5, 2), (5, 2)]
private def triple_7o3_7o3_7o3 : FracTuple 3 := ![(7, 3), (7, 3), (7, 3)]
private def triple_5o2_8o3_8o3 : FracTuple 3 := ![(5, 2), (8, 3), (8, 3)]
private def triple_9o4_9o4_5o2 : FracTuple 3 := ![(9, 4), (9, 4), (5, 2)]
private def triple_9o4_9o4_8o3 : FracTuple 3 := ![(9, 4), (9, 4), (8, 3)]
private def triple_8o3_11o4_13o5 : FracTuple 3 := ![(8, 3), (11, 4), (13, 5)]
private def triple_11o4_11o4_13o5 : FracTuple 3 := ![(11, 4), (11, 4), (13, 5)]
private def triple_11o4_13o5_13o5 : FracTuple 3 := ![(11, 4), (13, 5), (13, 5)]
private def triple_8o3_8o3_11o4 : FracTuple 3 := ![(8, 3), (8, 3), (11, 4)]
private def triple_8o3_11o4_11o4 : FracTuple 3 := ![(8, 3), (11, 4), (11, 4)]
private def triple_5o2_5o2_11o4 : FracTuple 3 := ![(5, 2), (5, 2), (11, 4)]
private def triple_5o2_8o3_11o4 : FracTuple 3 := ![(5, 2), (8, 3), (11, 4)]
private def triple_5o2_11o4_11o4 : FracTuple 3 := ![(5, 2), (11, 4), (11, 4)]

private lemma validK_triple_5o2_5o2_5o2 : ValidK triple_5o2_5o2_5o2 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_7o3_7o3_7o3 : ValidK triple_7o3_7o3_7o3 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_5o2_8o3_8o3 : ValidK triple_5o2_8o3_8o3 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_9o4_9o4_5o2 : ValidK triple_9o4_9o4_5o2 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_9o4_9o4_8o3 : ValidK triple_9o4_9o4_8o3 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_8o3_11o4_13o5 : ValidK triple_8o3_11o4_13o5 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_11o4_11o4_13o5 : ValidK triple_11o4_11o4_13o5 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_11o4_13o5_13o5 : ValidK triple_11o4_13o5_13o5 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_8o3_8o3_11o4 : ValidK triple_8o3_8o3_11o4 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_8o3_11o4_11o4 : ValidK triple_8o3_11o4_11o4 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_5o2_5o2_11o4 : ValidK triple_5o2_5o2_11o4 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_5o2_8o3_11o4 : ValidK triple_5o2_8o3_11o4 := by
  intro i; fin_cases i <;> decide
private lemma validK_triple_5o2_11o4_11o4 : ValidK triple_5o2_11o4_11o4 := by
  intro i; fin_cases i <;> decide

private lemma toNatTriple_triple_5o2_5o2_5o2 :
    FracTuple.toNatTriple triple_5o2_5o2_5o2 = ((5,2),(5,2),(5,2)) := rfl
private lemma toNatTriple_triple_7o3_7o3_7o3 :
    FracTuple.toNatTriple triple_7o3_7o3_7o3 = ((7,3),(7,3),(7,3)) := rfl
private lemma toNatTriple_triple_5o2_8o3_8o3 :
    FracTuple.toNatTriple triple_5o2_8o3_8o3 = ((5,2),(8,3),(8,3)) := rfl
private lemma toNatTriple_triple_9o4_9o4_5o2 :
    FracTuple.toNatTriple triple_9o4_9o4_5o2 = ((9,4),(9,4),(5,2)) := rfl
private lemma toNatTriple_triple_9o4_9o4_8o3 :
    FracTuple.toNatTriple triple_9o4_9o4_8o3 = ((9,4),(9,4),(8,3)) := rfl
private lemma toNatTriple_triple_8o3_11o4_13o5 :
    FracTuple.toNatTriple triple_8o3_11o4_13o5 = ((8,3),(11,4),(13,5)) := rfl
private lemma toNatTriple_triple_11o4_11o4_13o5 :
    FracTuple.toNatTriple triple_11o4_11o4_13o5 = ((11,4),(11,4),(13,5)) := rfl
private lemma toNatTriple_triple_11o4_13o5_13o5 :
    FracTuple.toNatTriple triple_11o4_13o5_13o5 = ((11,4),(13,5),(13,5)) := rfl
private lemma toNatTriple_triple_8o3_8o3_11o4 :
    FracTuple.toNatTriple triple_8o3_8o3_11o4 = ((8,3),(8,3),(11,4)) := rfl
private lemma toNatTriple_triple_8o3_11o4_11o4 :
    FracTuple.toNatTriple triple_8o3_11o4_11o4 = ((8,3),(11,4),(11,4)) := rfl
private lemma toNatTriple_triple_5o2_5o2_11o4 :
    FracTuple.toNatTriple triple_5o2_5o2_11o4 = ((5,2),(5,2),(11,4)) := rfl
private lemma toNatTriple_triple_5o2_8o3_11o4 :
    FracTuple.toNatTriple triple_5o2_8o3_11o4 = ((5,2),(8,3),(11,4)) := rfl
private lemma toNatTriple_triple_5o2_11o4_11o4 :
    FracTuple.toNatTriple triple_5o2_11o4_11o4 = ((5,2),(11,4),(11,4)) := rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_5o2_5o2_5o2_le : alphaK triple_5o2_5o2_5o2 ≤ 10 := by
  rw [alphaK_three]
  change ((fractionGraph 5 2 ⊠ fractionGraph 5 2) ⊠ fractionGraph 5 2).indepNum ≤ 10
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_5o2_5o2_5o2_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_7o3_7o3_7o3_le : alphaK triple_7o3_7o3_7o3 ≤ 8 := by
  rw [alphaK_three]
  change ((fractionGraph 7 3 ⊠ fractionGraph 7 3) ⊠ fractionGraph 7 3).indepNum ≤ 8
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_7o3_7o3_7o3_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_5o2_5o2_8o3_le : alphaK triple_5o2_5o2_8o3 ≤ 11 := by
  rw [alphaK_three]
  change ((fractionGraph 5 2 ⊠ fractionGraph 5 2) ⊠ fractionGraph 8 3).indepNum ≤ 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_5o2_5o2_8o3_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_5o2_8o3_8o3_le : alphaK triple_5o2_8o3_8o3 ≤ 11 := by
  rw [alphaK_three]
  change ((fractionGraph 5 2 ⊠ fractionGraph 8 3) ⊠ fractionGraph 8 3).indepNum ≤ 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_5o2_8o3_8o3_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_8o3_8o3_8o3_le : alphaK triple_8o3_8o3_8o3 ≤ 12 := by
  rw [alphaK_three]
  change ((fractionGraph 8 3 ⊠ fractionGraph 8 3) ⊠ fractionGraph 8 3).indepNum ≤ 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_8o3_8o3_8o3_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_9o4_9o4_5o2_le : alphaK triple_9o4_9o4_5o2 ≤ 8 := by
  rw [alphaK_three]
  change ((fractionGraph 9 4 ⊠ fractionGraph 9 4) ⊠ fractionGraph 5 2).indepNum ≤ 8
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_9o4_9o4_5o2_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_9o4_9o4_8o3_le : alphaK triple_9o4_9o4_8o3 ≤ 8 := by
  rw [alphaK_three]
  change ((fractionGraph 9 4 ⊠ fractionGraph 9 4) ⊠ fractionGraph 8 3).indepNum ≤ 8
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_9o4_9o4_8o3_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_8o3_11o4_13o5_le : alphaK triple_8o3_11o4_13o5 ≤ 12 := by
  rw [alphaK_three]
  change ((fractionGraph 8 3 ⊠ fractionGraph 11 4) ⊠ fractionGraph 13 5).indepNum ≤ 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_83_114_135_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_11o4_11o4_13o5_le : alphaK triple_11o4_11o4_13o5 ≤ 12 := by
  rw [alphaK_three]
  change ((fractionGraph 11 4 ⊠ fractionGraph 11 4) ⊠ fractionGraph 13 5).indepNum ≤ 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_114_114_135_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_11o4_13o5_13o5_le : alphaK triple_11o4_13o5_13o5 ≤ 12 := by
  rw [alphaK_three]
  change ((fractionGraph 11 4 ⊠ fractionGraph 13 5) ⊠ fractionGraph 13 5).indepNum ≤ 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_114_135_135_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_8o3_8o3_11o4_le : alphaK triple_8o3_8o3_11o4 ≤ 12 := by
  rw [alphaK_three]
  change ((fractionGraph 8 3 ⊠ fractionGraph 8 3) ⊠ fractionGraph 11 4).indepNum ≤ 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_83_83_114_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_8o3_11o4_11o4_le : alphaK triple_8o3_11o4_11o4 ≤ 12 := by
  rw [alphaK_three]
  change ((fractionGraph 8 3 ⊠ fractionGraph 11 4) ⊠ fractionGraph 11 4).indepNum ≤ 12
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_83_114_114_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_5o2_5o2_11o4_le : alphaK triple_5o2_5o2_11o4 ≤ 11 := by
  rw [alphaK_three]
  change ((fractionGraph 5 2 ⊠ fractionGraph 5 2) ⊠ fractionGraph 11 4).indepNum ≤ 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_52_52_114_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_5o2_8o3_11o4_le : alphaK triple_5o2_8o3_11o4 ≤ 11 := by
  rw [alphaK_three]
  change ((fractionGraph 5 2 ⊠ fractionGraph 8 3) ⊠ fractionGraph 11 4).indepNum ≤ 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_52_83_114_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma alphaK_triple_5o2_11o4_11o4_le : alphaK triple_5o2_11o4_11o4 ≤ 11 := by
  rw [alphaK_three]
  change ((fractionGraph 5 2 ⊠ fractionGraph 11 4) ⊠ fractionGraph 11 4).indepNum ≤ 11
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  exact alpha3_52_114_114_le

/-! ### `alphaK_le_baumertBoundNat`: Baumert match bound on `alphaK v` -/

/-- Per-multiset bridge: for each of the 15 Baumert multisets `m` with bound
    `b`, if `matchesMultisetNat (toNatTriple v) m = true`, then `alphaK v ≤ b`.

    The 15 cases use the 15 canonical FracTuples and their `alphaK_le_*`
    bounds plugged into the generic `alphaK_le_of_matches_canonical`. -/
private lemma alphaK_le_of_baumert_match
    {v : FracTuple 3} (hv : ValidK v)
    (m : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) (b : ℕ)
    (h_in_list : (m, b) ∈
      ([(((5, 2), (5, 2), (8, 3)), 11),
        (((8, 3), (8, 3), (8, 3)), 12),
        (((7, 3), (7, 3), (7, 3)), 8),
        (((5, 2), (5, 2), (5, 2)), 10),
        (((5, 2), (8, 3), (8, 3)), 11),
        (((9, 4), (9, 4), (5, 2)), 8),
        (((9, 4), (9, 4), (8, 3)), 8),
        (((8, 3), (11, 4), (13, 5)), 12),
        (((11, 4), (11, 4), (13, 5)), 12),
        (((11, 4), (13, 5), (13, 5)), 12),
        (((8, 3), (8, 3), (11, 4)), 12),
        (((8, 3), (11, 4), (11, 4)), 12),
        (((5, 2), (5, 2), (11, 4)), 11),
        (((5, 2), (8, 3), (11, 4)), 11),
        (((5, 2), (11, 4), (11, 4)), 11)] : List (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ)))
    (h_match : matchesMultisetNat (FracTuple.toNatTriple v) m = true) :
    alphaK v ≤ b := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h_in_list
  rcases h_in_list with
    ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩ |
    ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩ |
    ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩ | ⟨hm, hb⟩
  all_goals (subst hb; subst hm)
  · -- 5/2, 5/2, 8/3 → 11
    apply alphaK_le_of_matches_canonical hv validK_triple_5o2_5o2_8o3
      alphaK_triple_5o2_5o2_8o3.le
    rw [toNatTriple_triple_5o2_5o2_8o3]; exact h_match
  · -- 8/3, 8/3, 8/3 → 12
    apply alphaK_le_of_matches_canonical hv validK_triple_8o3_8o3_8o3
      alphaK_triple_8o3_8o3_8o3.le
    rw [toNatTriple_triple_8o3_8o3_8o3]; exact h_match
  · -- 7/3, 7/3, 7/3 → 8
    apply alphaK_le_of_matches_canonical hv validK_triple_7o3_7o3_7o3
      alphaK_triple_7o3_7o3_7o3_le
    rw [toNatTriple_triple_7o3_7o3_7o3]; exact h_match
  · -- 5/2, 5/2, 5/2 → 10
    apply alphaK_le_of_matches_canonical hv validK_triple_5o2_5o2_5o2
      alphaK_triple_5o2_5o2_5o2_le
    rw [toNatTriple_triple_5o2_5o2_5o2]; exact h_match
  · -- 5/2, 8/3, 8/3 → 11
    apply alphaK_le_of_matches_canonical hv validK_triple_5o2_8o3_8o3
      alphaK_triple_5o2_8o3_8o3_le
    rw [toNatTriple_triple_5o2_8o3_8o3]; exact h_match
  · -- 9/4, 9/4, 5/2 → 8
    apply alphaK_le_of_matches_canonical hv validK_triple_9o4_9o4_5o2
      alphaK_triple_9o4_9o4_5o2_le
    rw [toNatTriple_triple_9o4_9o4_5o2]; exact h_match
  · -- 9/4, 9/4, 8/3 → 8
    apply alphaK_le_of_matches_canonical hv validK_triple_9o4_9o4_8o3
      alphaK_triple_9o4_9o4_8o3_le
    rw [toNatTriple_triple_9o4_9o4_8o3]; exact h_match
  · -- 8/3, 11/4, 13/5 → 12
    apply alphaK_le_of_matches_canonical hv validK_triple_8o3_11o4_13o5
      alphaK_triple_8o3_11o4_13o5_le
    rw [toNatTriple_triple_8o3_11o4_13o5]; exact h_match
  · -- 11/4, 11/4, 13/5 → 12
    apply alphaK_le_of_matches_canonical hv validK_triple_11o4_11o4_13o5
      alphaK_triple_11o4_11o4_13o5_le
    rw [toNatTriple_triple_11o4_11o4_13o5]; exact h_match
  · -- 11/4, 13/5, 13/5 → 12
    apply alphaK_le_of_matches_canonical hv validK_triple_11o4_13o5_13o5
      alphaK_triple_11o4_13o5_13o5_le
    rw [toNatTriple_triple_11o4_13o5_13o5]; exact h_match
  · -- 8/3, 8/3, 11/4 → 12
    apply alphaK_le_of_matches_canonical hv validK_triple_8o3_8o3_11o4
      alphaK_triple_8o3_8o3_11o4_le
    rw [toNatTriple_triple_8o3_8o3_11o4]; exact h_match
  · -- 8/3, 11/4, 11/4 → 12
    apply alphaK_le_of_matches_canonical hv validK_triple_8o3_11o4_11o4
      alphaK_triple_8o3_11o4_11o4_le
    rw [toNatTriple_triple_8o3_11o4_11o4]; exact h_match
  · -- 5/2, 5/2, 11/4 → 11
    apply alphaK_le_of_matches_canonical hv validK_triple_5o2_5o2_11o4
      alphaK_triple_5o2_5o2_11o4_le
    rw [toNatTriple_triple_5o2_5o2_11o4]; exact h_match
  · -- 5/2, 8/3, 11/4 → 11
    apply alphaK_le_of_matches_canonical hv validK_triple_5o2_8o3_11o4
      alphaK_triple_5o2_8o3_11o4_le
    rw [toNatTriple_triple_5o2_8o3_11o4]; exact h_match
  · -- 5/2, 11/4, 11/4 → 11
    apply alphaK_le_of_matches_canonical hv validK_triple_5o2_11o4_11o4
      alphaK_triple_5o2_11o4_11o4_le
    rw [toNatTriple_triple_5o2_11o4_11o4]; exact h_match

/-- Auxiliary: foldl-min over a filtered list preserves "every element gives an
    upper bound on `alphaK v`" — and the result (if `some B`) is also an upper
    bound. -/
private lemma foldl_min_alpha_le_aux
    {v : FracTuple 3}
    (L : List (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
    (h_each : ∀ p ∈ L, alphaK v ≤ p.2) :
    ∀ (acc : Option ℕ), (∀ a, acc = some a → alphaK v ≤ a) →
    ∀ B, L.foldl (fun acc (p : ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) =>
                    match acc with
                    | none => some p.2
                    | some a => some (min a p.2)) acc = some B →
    alphaK v ≤ B := by
  induction L with
  | nil =>
    intro acc h_acc B h_eq
    simp only [List.foldl] at h_eq
    exact h_acc B h_eq
  | cons head tail ih =>
    intro acc h_acc B h_eq
    have h_head : alphaK v ≤ head.2 := h_each head (by exact List.mem_cons_self)
    have h_tail : ∀ p ∈ tail, alphaK v ≤ p.2 :=
      fun p hp => h_each p (List.mem_cons_of_mem _ hp)
    -- Compute new acc.
    have h_new_acc :
        ∀ a, (match acc with
              | none => some head.2
              | some x => some (min x head.2)) = some a → alphaK v ≤ a := by
      intro a ha
      cases acc with
      | none =>
        simp only [Option.some.injEq] at ha; rw [← ha]; exact h_head
      | some x =>
        simp only [Option.some.injEq] at ha
        rw [← ha]
        exact le_min (h_acc x rfl) h_head
    simp only [List.foldl] at h_eq
    exact ih h_tail _ h_new_acc B h_eq

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Baumert match bound on `alphaK v`.** If `baumertBoundNat (toNatTriple v) = some B`,
    then `alphaK v ≤ B`. -/
theorem alphaK_le_baumertBoundNat
    {v : FracTuple 3} (hv : ValidK v)
    {B : ℕ} (h : baumertBoundNat (FracTuple.toNatTriple v) = some B) :
    alphaK v ≤ B := by
  set t := FracTuple.toNatTriple v with ht_def
  unfold baumertBoundNat at h
  -- The candidates list, then filter, then foldl.
  set candidates :
      List (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) :=
    [ (((5, 2), (5, 2), (8, 3)), 11),
      (((8, 3), (8, 3), (8, 3)), 12),
      (((7, 3), (7, 3), (7, 3)), 8),
      (((5, 2), (5, 2), (5, 2)), 10),
      (((5, 2), (8, 3), (8, 3)), 11),
      (((9, 4), (9, 4), (5, 2)), 8),
      (((9, 4), (9, 4), (8, 3)), 8),
      (((8, 3), (11, 4), (13, 5)), 12),
      (((11, 4), (11, 4), (13, 5)), 12),
      (((11, 4), (13, 5), (13, 5)), 12),
      (((8, 3), (8, 3), (11, 4)), 12),
      (((8, 3), (11, 4), (11, 4)), 12),
      (((5, 2), (5, 2), (11, 4)), 11),
      (((5, 2), (8, 3), (11, 4)), 11),
      (((5, 2), (11, 4), (11, 4)), 11) ] with h_candidates
  -- The matched (filtered) sublist.
  set matched := candidates.filter (fun p => matchesMultisetNat t p.1) with h_matched
  -- Each matched element gives an alpha upper bound.
  have h_each : ∀ p ∈ matched, alphaK v ≤ p.2 := by
    intro p hp
    rw [h_matched] at hp
    rw [List.mem_filter] at hp
    obtain ⟨hp_in, hp_match⟩ := hp
    exact alphaK_le_of_baumert_match hv p.1 p.2 hp_in hp_match
  -- The foldl with starting acc=none, result=some B, gives alphaK v ≤ B.
  apply foldl_min_alpha_le_aux matched h_each none
  · intro a ha
    -- acc = none means ∀ a, none = some a → ⊥.
    cases ha
  · -- Connect h to the foldl.
    -- The h asserts the foldl over `matched` (with init none) equals some B.
    exact h

/-! ### Full upper bound `alphaK_le_existingUpperBoundNat` (with Baumert) -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Full algebraic upper bound on `alphaK`.** For any valid `v : FracTuple 3`,
    `alphaK v ≤ existingUpperBoundNat (toNatTriple v)`. Combines the nested-floor
    bound, the three interval bounds (`< 5/2`, `< 8/3`, `< 11/4`), and the 15
    Baumert multiset-match bounds. -/
theorem alphaK_le_existingUpperBoundNat
    {v : FracTuple 3} (hv : ValidK v) :
    alphaK v ≤ existingUpperBoundNat (FracTuple.toNatTriple v) := by
  set t := FracTuple.toNatTriple v with ht_def
  -- Start from the nested-floor bound.
  have h_nf : alphaK v ≤ nestedFloor3NatMin t :=
    alphaK_le_nestedFloor3NatMin hv
  -- Stage-1 (after `< 5/2`).
  set s1 : ℕ :=
    if allRatiosLtNat 5 2 t = true then min (nestedFloor3NatMin t) 8
    else nestedFloor3NatMin t with hs1
  have h1 : alphaK v ≤ s1 := by
    rw [hs1]
    split_ifs with h
    · exact le_min h_nf (alphaK_le_of_allRatiosLt_5_2 hv h)
    · exact h_nf
  set s2 : ℕ := if allRatiosLtNat 8 3 t = true then min s1 10 else s1 with hs2
  have h2 : alphaK v ≤ s2 := by
    rw [hs2]
    split_ifs with h
    · exact le_min h1 (alphaK_le_of_allRatiosLt_8_3 hv h)
    · exact h1
  set s3 : ℕ := if allRatiosLtNat 11 4 t = true then min s2 12 else s2 with hs3
  have h3 : alphaK v ≤ s3 := by
    rw [hs3]
    split_ifs with h
    · exact le_min h2 (alphaK_le_of_allRatiosLt_11_4 hv h)
    · exact h2
  -- Now goal: alphaK v ≤ existingUpperBoundNat t.
  -- Unfold and case on baumertBoundNat.
  change alphaK v ≤ existingUpperBoundNat t
  unfold existingUpperBoundNat
  -- The let-chain in existingUpperBoundNat reduces via let-beta-equiv.
  -- nf₁ := nestedFloor3NatMin t
  -- nf₂ := if allRatiosLtNat 5 2 t then min nf₁ 8 else nf₁
  -- nf₃ := if allRatiosLtNat 8 3 t then min nf₂ 10 else nf₂
  -- nf₄ := if allRatiosLtNat 11 4 t then min nf₃ 12 else nf₃
  -- match baumertBoundNat t with | none => nf₄ | some b => min nf₄ b
  -- The shape is: `(let-chain).match`. We have alphaK ≤ nf₄ (which equals s3).
  change alphaK v ≤
    (let nf := nestedFloor3NatMin t
     let nf := if allRatiosLtNat 5 2 t then min nf 8 else nf
     let nf := if allRatiosLtNat 8 3 t then min nf 10 else nf
     let nf := if allRatiosLtNat 11 4 t then min nf 12 else nf
     match baumertBoundNat t with
     | none => nf
     | some b => min nf b)
  -- The let-chain reduces; the inner `nf` after all 4 stages equals s3 by definition.
  have h_s3 : alphaK v ≤
      (let nf := nestedFloor3NatMin t
       let nf := if allRatiosLtNat 5 2 t then min nf 8 else nf
       let nf := if allRatiosLtNat 8 3 t then min nf 10 else nf
       if allRatiosLtNat 11 4 t then min nf 12 else nf) := by
    change alphaK v ≤ s3; exact h3
  cases h_baumert : baumertBoundNat t with
  | none =>
    exact h_s3
  | some b =>
    have h_b : alphaK v ≤ b := alphaK_le_baumertBoundNat hv h_baumert
    exact le_min h_s3 h_b

/-! ## Route A (with Baumert): `existingUpperBoundNat t < maxNumeratorNat t` -/

/-- **Route A (full, with Baumert).** If for the reconstructed `fracTupleOf t`,
    the full algebraic upper bound is strictly less than the maximum
    numerator, then `fracTupleOf t` is not an α₃-discontinuity. -/
theorem routeA_not_isDiscontinuityK
    (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (h_route : existingUpperBoundNat t < maxNumeratorNat t)
    (hq_ge2 : ∀ i, 2 ≤ ((fracTupleOf t h0 h1 h2 i).2 : ℕ))
    (hcoprime : ∀ i, Nat.Coprime ((fracTupleOf t h0 h1 h2 i).1 : ℕ)
                                  ((fracTupleOf t h0 h1 h2 i).2 : ℕ)) :
    ¬ IsDiscontinuityK (fracTupleOf t h0 h1 h2) := by
  intro hv_disc
  set v := fracTupleOf t h0 h1 h2 with hv_def
  have hv_valid : ValidK v := fracTupleOf_valid t h0 h1 h2
  have h_t_eq : FracTuple.toNatTriple v = t := fracTupleOf_toNatTriple_eq t h0 h1 h2
  have h_alpha_ub : alphaK v ≤ existingUpperBoundNat t := by
    rw [← h_t_eq]
    exact alphaK_le_existingUpperBoundNat hv_valid
  have h_n0_le : ((v 0).1 : ℕ) ≤ alphaK v :=
    alphaK_ge_num_at_of_isDiscontinuityK hv_valid hv_disc 0 (hq_ge2 0) (hcoprime 0)
  have h_n1_le : ((v 1).1 : ℕ) ≤ alphaK v :=
    alphaK_ge_num_at_of_isDiscontinuityK hv_valid hv_disc 1 (hq_ge2 1) (hcoprime 1)
  have h_n2_le : ((v 2).1 : ℕ) ≤ alphaK v :=
    alphaK_ge_num_at_of_isDiscontinuityK hv_valid hv_disc 2 (hq_ge2 2) (hcoprime 2)
  have h_v0 : ((v 0).1 : ℕ) = t.1.1 := by
    have := congrArg (·.1.1) h_t_eq; simpa [FracTuple.toNatTriple] using this
  have h_v1 : ((v 1).1 : ℕ) = t.2.1.1 := by
    have := congrArg (·.2.1.1) h_t_eq; simpa [FracTuple.toNatTriple] using this
  have h_v2 : ((v 2).1 : ℕ) = t.2.2.1 := by
    have := congrArg (·.2.2.1) h_t_eq; simpa [FracTuple.toNatTriple] using this
  rw [h_v0] at h_n0_le
  rw [h_v1] at h_n1_le
  rw [h_v2] at h_n2_le
  have h_max_le : maxNumeratorNat t ≤ alphaK v := by
    unfold maxNumeratorNat
    exact max_le h_n0_le (max_le h_n1_le h_n2_le)
  have : maxNumeratorNat t ≤ existingUpperBoundNat t :=
    le_trans h_max_le h_alpha_ub
  omega

/-- Bool: Route A (with Baumert) fires on `t`. -/
def decideRouteANat (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (existingUpperBoundNat t < maxNumeratorNat t)

/-- **Route A discharge into `IsClassifiedNat`** (with Baumert). -/
theorem isClassifiedNat_of_routeA
    (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (h_q_ge2 : 2 ≤ t.1.2 ∧ 2 ≤ t.2.1.2 ∧ 2 ≤ t.2.2.2)
    (h_coprime : Nat.Coprime t.1.1 t.1.2 ∧
                 Nat.Coprime t.2.1.1 t.2.1.2 ∧
                 Nat.Coprime t.2.2.1 t.2.2.2)
    (h_route : decideRouteANat t = true) :
    IsClassifiedNat t h0 h1 h2 := by
  right
  unfold decideRouteANat at h_route
  simp only [decide_eq_true_eq] at h_route
  obtain ⟨hq_all, hcop_all⟩ :=
    fracTupleOf_q_coprime_of_q_ge2 t h0 h1 h2 h_q_ge2 h_coprime
  exact routeA_not_isDiscontinuityK t h0 h1 h2 h_route hq_all hcop_all

/-! ## Route B (with Baumert): strict disc-below + full upper bound -/

/-- Per-known-disc Route B helper (with Baumert): given a canonical disc
    `d` (FracTuple) with α-value `αd`, a triple `t` strictly above `d` in the
    multiset-perm order, and the full `existingUpperBoundNat t ≤ αd`, derive
    `¬ IsDiscontinuityK (fracTupleOf t)`. -/
private lemma routeB_via_disc_full
    {d : FracTuple 3} (αd : ℕ)
    (h_valid_d : ValidK d)
    (h_alpha_d : alphaK d = αd)
    {t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)}
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (h_below : lePermNat (FracTuple.toNatTriple d) t = true)
    (h_strict : lePermNat t (FracTuple.toNatTriple d) = false)
    (h_alpha_ub : existingUpperBoundNat t ≤ αd) :
    ¬ IsDiscontinuityK (fracTupleOf t h0 h1 h2) := by
  intro h_disc
  set v := fracTupleOf t h0 h1 h2 with hv_def
  have hv_valid : ValidK v := fracTupleOf_valid t h0 h1 h2
  have h_t_eq : FracTuple.toNatTriple v = t := fracTupleOf_toNatTriple_eq t h0 h1 h2
  have h_le_dv : lePermK d v := by
    apply lePermK_of_lePermNat
    rw [h_t_eq]
    exact h_below
  have h_not_le_vd : ¬ lePermK v d := by
    intro h_vd
    obtain ⟨σ, hσ⟩ := h_vd
    have h_pair_slot : ∀ i, lePairNat (((v (σ i)).1 : ℕ), ((v (σ i)).2 : ℕ))
                                       (((d i).1 : ℕ), ((d i).2 : ℕ)) = true := by
      intro i
      have h_rat := hσ i
      unfold FracTuple.toRat at h_rat
      have hq_v_pos : (0 : ℚ) < (((v (σ i)).2 : ℕ) : ℚ) := by
        have := (v (σ i)).2.pos
        exact_mod_cast this
      have hq_d_pos : (0 : ℚ) < (((d i).2 : ℕ) : ℚ) := by
        have := (d i).2.pos
        exact_mod_cast this
      rw [div_le_div_iff₀ hq_v_pos hq_d_pos] at h_rat
      have h_nat : ((v (σ i)).1 : ℕ) * ((d i).2 : ℕ) ≤
                   ((d i).1 : ℕ) * ((v (σ i)).2 : ℕ) := by exact_mod_cast h_rat
      unfold lePairNat
      simp only [decide_eq_true_eq]
      exact h_nat
    have h_lePermNat_vd : lePermNat (FracTuple.toNatTriple v)
                                     (FracTuple.toNatTriple d) = true := by
      have h_inj : Function.Injective σ := σ.injective
      have hp0 := h_pair_slot 0
      have hp1 := h_pair_slot 1
      have hp2 := h_pair_slot 2
      have hσ0 : σ 0 = 0 ∨ σ 0 = 1 ∨ σ 0 = 2 := by
        match h0' : σ 0 with
        | 0 => exact Or.inl rfl
        | 1 => exact Or.inr (Or.inl rfl)
        | 2 => exact Or.inr (Or.inr rfl)
      have hσ1 : σ 1 = 0 ∨ σ 1 = 1 ∨ σ 1 = 2 := by
        match h1' : σ 1 with
        | 0 => exact Or.inl rfl
        | 1 => exact Or.inr (Or.inl rfl)
        | 2 => exact Or.inr (Or.inr rfl)
      have hσ2 : σ 2 = 0 ∨ σ 2 = 1 ∨ σ 2 = 2 := by
        match h2' : σ 2 with
        | 0 => exact Or.inl rfl
        | 1 => exact Or.inr (Or.inl rfl)
        | 2 => exact Or.inr (Or.inr rfl)
      have h_neq_01 : σ 0 ≠ σ 1 := fun h => absurd (h_inj h) (by decide)
      have h_neq_02 : σ 0 ≠ σ 2 := fun h => absurd (h_inj h) (by decide)
      have h_neq_12 : σ 1 ≠ σ 2 := fun h => absurd (h_inj h) (by decide)
      rcases hσ0 with hσ0 | hσ0 | hσ0 <;>
      rcases hσ1 with hσ1 | hσ1 | hσ1 <;>
      rcases hσ2 with hσ2 | hσ2 | hσ2 <;>
      (try (exfalso; rw [hσ0, hσ1] at h_neq_01; exact h_neq_01 rfl)) <;>
      (try (exfalso; rw [hσ0, hσ2] at h_neq_02; exact h_neq_02 rfl)) <;>
      (try (exfalso; rw [hσ1, hσ2] at h_neq_12; exact h_neq_12 rfl)) <;>
      (rw [hσ0] at hp0; rw [hσ1] at hp1; rw [hσ2] at hp2;
       unfold lePermNat FracTuple.toNatTriple;
       simp only [Bool.or_eq_true, Bool.and_eq_true])
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨hp0, hp1⟩, hp2⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hp0, hp1⟩, hp2⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hp0, hp1⟩, hp2⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨⟨hp0, hp1⟩, hp2⟩))
      · exact Or.inl (Or.inr ⟨⟨hp0, hp1⟩, hp2⟩)
      · exact Or.inr ⟨⟨hp0, hp1⟩, hp2⟩
    rw [h_t_eq] at h_lePermNat_vd
    rw [h_lePermNat_vd] at h_strict
    exact absurd h_strict (by decide)
  have h_lt_dv : ltPermK d v := ⟨h_le_dv, h_not_le_vd⟩
  have h_alpha_lt : alphaK d < alphaK v := h_disc d h_valid_d h_lt_dv
  have h_alpha_v_ub : alphaK v ≤ existingUpperBoundNat t := by
    rw [← h_t_eq]; exact alphaK_le_existingUpperBoundNat hv_valid
  have : alphaK v ≤ alphaK d := by
    rw [h_alpha_d]
    exact le_trans h_alpha_v_ub h_alpha_ub
  omega

/-- Bool: Route B (with Baumert) check via canonical disc `d` (full bound). -/
private def discBelowMatchesNatFull
    (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (d : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) (αd : ℕ) : Bool :=
  lePermNat d t && !lePermNat t d &&
  decide (existingUpperBoundNat t ≤ αd)

/-- Bool: Route B (with Baumert) fires on `t`. -/
def decideRouteBNat (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  knownDiscNatList.any (fun (d, αd) => discBelowMatchesNatFull t d αd)

/-- For each of the 12 disc cases, dispatch via the matching canonical
    `triple*` FracTuple, with the full Baumert-aware upper bound. -/
private theorem routeB_not_isDiscontinuityK_dispatch
    (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (d : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) (αd : ℕ)
    (h_d_in_list : (d, αd) ∈ knownDiscNatList)
    (h_match : discBelowMatchesNatFull t d αd = true) :
    ¬ IsDiscontinuityK (fracTupleOf t h0 h1 h2) := by
  unfold discBelowMatchesNatFull at h_match
  simp only [Bool.and_eq_true, Bool.not_eq_true',
             decide_eq_true_eq] at h_match
  obtain ⟨⟨h_le, h_strict⟩, h_ub⟩ := h_match
  unfold knownDiscNatList at h_d_in_list
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h_d_in_list
  rcases h_d_in_list with
    ⟨hd, hα⟩ | ⟨hd, hα⟩ | ⟨hd, hα⟩ | ⟨hd, hα⟩ | ⟨hd, hα⟩ | ⟨hd, hα⟩ |
    ⟨hd, hα⟩ | ⟨hd, hα⟩ | ⟨hd, hα⟩ | ⟨hd, hα⟩ | ⟨hd, hα⟩ | ⟨hd, hα⟩
  all_goals (subst hd; subst hα)
  · refine routeB_via_disc_full 8 validK_triple222 alphaK_triple222 h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple222]; exact h_le
    · rw [toNatTriple_triple222]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 12 validK_triple223 alphaK_triple223 h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple223]; exact h_le
    · rw [toNatTriple_triple223]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 18 validK_triple233 alphaK_triple233 h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple233]; exact h_le
    · rw [toNatTriple_triple233]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 27 validK_triple333 alphaK_triple333 h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple333]; exact h_le
    · rw [toNatTriple_triple333]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 10 validK_triple_2_5o2_5o2 alphaK_triple_2_5o2_5o2
      h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple_2_5o2_5o2]; exact h_le
    · rw [toNatTriple_triple_2_5o2_5o2]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 15 validK_triple_3_5o2_5o2 alphaK_triple_3_5o2_5o2
      h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple_3_5o2_5o2]; exact h_le
    · rw [toNatTriple_triple_3_5o2_5o2]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 11 validK_triple_5o2_5o2_8o3 alphaK_triple_5o2_5o2_8o3
      h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple_5o2_5o2_8o3]; exact h_le
    · rw [toNatTriple_triple_5o2_5o2_8o3]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 12 validK_triple_8o3_8o3_8o3 alphaK_triple_8o3_8o3_8o3
      h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple_8o3_8o3_8o3]; exact h_le
    · rw [toNatTriple_triple_8o3_8o3_8o3]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 9 validK_triple_9o4_7o3_5o2 alphaK_triple_9o4_7o3_5o2
      h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple_9o4_7o3_5o2]; exact h_le
    · rw [toNatTriple_triple_9o4_7o3_5o2]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 11 validK_triple_11o5_11o4_11o4 alphaK_triple_11o5_11o4_11o4
      h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple_11o5_11o4_11o4]; exact h_le
    · rw [toNatTriple_triple_11o5_11o4_11o4]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 13 validK_triple_11o4_11o4_11o4 alphaK_triple_11o4_11o4_11o4
      h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple_11o4_11o4_11o4]; exact h_le
    · rw [toNatTriple_triple_11o4_11o4_11o4]; exact h_strict
    · exact h_ub
  · refine routeB_via_disc_full 14 validK_triple_14o5_14o5_14o5 alphaK_triple_14o5_14o5_14o5
      h0 h1 h2 ?_ ?_ ?_
    · rw [toNatTriple_triple_14o5_14o5_14o5]; exact h_le
    · rw [toNatTriple_triple_14o5_14o5_14o5]; exact h_strict
    · exact h_ub

/-- **Route B (full, with Baumert).** -/
theorem routeB_not_isDiscontinuityK
    (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (h_route : decideRouteBNat t = true) :
    ¬ IsDiscontinuityK (fracTupleOf t h0 h1 h2) := by
  unfold decideRouteBNat at h_route
  rw [List.any_eq_true] at h_route
  obtain ⟨⟨d, αd⟩, h_mem, h_match⟩ := h_route
  exact routeB_not_isDiscontinuityK_dispatch t h0 h1 h2 d αd h_mem h_match

/-- **Route B discharge into `IsClassifiedNat`** (with Baumert). -/
theorem isClassifiedNat_of_routeB
    (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (h_route : decideRouteBNat t = true) :
    IsClassifiedNat t h0 h1 h2 := by
  right
  exact routeB_not_isDiscontinuityK t h0 h1 h2 h_route

/-! ## Combined classifier wired into `IsClassifiedNat` -/

/-! ### `IsKnownDiscMod` from `matchesMultisetNat` decomposition -/

/-- Helper: pointwise equality of FracTuple slots from per-component nat equalities. -/
private lemma fracTuple_eq_of_pq_match {v w : FracTuple 3}
    (h0p : ((v 0).1 : ℕ) = ((w 0).1 : ℕ)) (h0q : ((v 0).2 : ℕ) = ((w 0).2 : ℕ))
    (h1p : ((v 1).1 : ℕ) = ((w 1).1 : ℕ)) (h1q : ((v 1).2 : ℕ) = ((w 1).2 : ℕ))
    (h2p : ((v 2).1 : ℕ) = ((w 2).1 : ℕ)) (h2q : ((v 2).2 : ℕ) = ((w 2).2 : ℕ)) :
    v = w := by
  funext i
  fin_cases i
  · apply Prod.ext
    · apply PNat.coe_inj.mp; exact h0p
    · apply PNat.coe_inj.mp; exact h0q
  · apply Prod.ext
    · apply PNat.coe_inj.mp; exact h1p
    · apply PNat.coe_inj.mp; exact h1q
  · apply Prod.ext
    · apply PNat.coe_inj.mp; exact h2p
    · apply PNat.coe_inj.mp; exact h2q

/-- Given `matchesMultisetNat (toNatTriple v) (toNatTriple w) = true` and `w ∈ knownDiscList`,
    construct `IsKnownDiscMod v`. The 6-disjunct decomposition gives σ ∈ S₃ with
    `v ∘ σ = w` (after lifting nat-equalities to PNat-equalities). -/
private lemma isKnownDiscMod_of_matchesMultisetNat
    {v : FracTuple 3}
    (w : FracTuple 3) (hw : w ∈ knownDiscList)
    (hm : matchesMultisetNat (FracTuple.toNatTriple v) (FracTuple.toNatTriple w) = true) :
    IsKnownDiscMod v := by
  rcases matchesMultisetNat_decompose _ _ hm with
    h | h | h | h | h | h
  all_goals (
    obtain ⟨h0', h1', h2'⟩ := h
    have e0p := congrArg Prod.fst h0'
    have e0q := congrArg Prod.snd h0'
    have e1p := congrArg Prod.fst h1'
    have e1q := congrArg Prod.snd h1'
    have e2p := congrArg Prod.fst h2'
    have e2q := congrArg Prod.snd h2'
    simp only [FracTuple.toNatTriple] at e0p e0q e1p e1q e2p e2q)
  · -- σ = id: v 0 = w 0, v 1 = w 1, v 2 = w 2.
    refine ⟨1, w, hw, ?_⟩
    funext i
    simp only [Equiv.Perm.coe_one, Function.comp, id_eq]
    have h_eq : v = w := fracTuple_eq_of_pq_match e0p e0q e1p e1q e2p e2q
    rw [h_eq]
  · -- σ = swap 1 2: v 0 = w 0, v 1 = w 2, v 2 = w 1. v ∘ σ = ?
    -- Want (v ∘ σ) k = w k. (v ∘ σ) 0 = v 0 = w 0. ✓
    -- (v ∘ σ) 1 = v 2 = w 1 (e2 says v 2 = w 1). ✓
    -- (v ∘ σ) 2 = v 1 = w 2 (e1 says v 1 = w 2). ✓
    refine ⟨Equiv.swap 1 2, w, hw, ?_⟩
    set u := v ∘ (Equiv.swap (1 : Fin 3) 2) with hu_def
    have hu0 : u 0 = v 0 := by
      simp [hu_def, Equiv.swap_apply_of_ne_of_ne (show (0:Fin 3) ≠ 1 by decide)
        (show (0:Fin 3) ≠ 2 by decide)]
    have hu1 : u 1 = v 2 := by simp [hu_def, Equiv.swap_apply_left]
    have hu2 : u 2 = v 1 := by simp [hu_def, Equiv.swap_apply_right]
    apply fracTuple_eq_of_pq_match
    · rw [hu0]; exact e0p
    · rw [hu0]; exact e0q
    · rw [hu1]; exact e2p
    · rw [hu1]; exact e2q
    · rw [hu2]; exact e1p
    · rw [hu2]; exact e1q
  · -- σ = swap 0 1: v 0 = w 1, v 1 = w 0, v 2 = w 2.
    refine ⟨Equiv.swap 0 1, w, hw, ?_⟩
    set u := v ∘ (Equiv.swap (0 : Fin 3) 1) with hu_def
    have hu0 : u 0 = v 1 := by simp [hu_def, Equiv.swap_apply_left]
    have hu1 : u 1 = v 0 := by simp [hu_def, Equiv.swap_apply_right]
    have hu2 : u 2 = v 2 := by
      simp [hu_def, Equiv.swap_apply_of_ne_of_ne (show (2:Fin 3) ≠ 0 by decide)
        (show (2:Fin 3) ≠ 1 by decide)]
    apply fracTuple_eq_of_pq_match
    · rw [hu0]; exact e1p
    · rw [hu0]; exact e1q
    · rw [hu1]; exact e0p
    · rw [hu1]; exact e0q
    · rw [hu2]; exact e2p
    · rw [hu2]; exact e2q
  · -- 4th disjunct: v 0 = w 1, v 1 = w 2, v 2 = w 0.
    -- Want σ such that (v ∘ σ) k = w k. So σ 0 = ? where v(σ 0) = w 0. v 2 = w 0 → σ 0 = 2.
    -- σ 1 = 0 (v 0 = w 1). σ 2 = 1 (v 1 = w 2).
    refine ⟨Equiv.swap 0 2 * Equiv.swap 1 2, w, hw, ?_⟩
    set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 1 2 with hσ
    have hσ0 : σ 0 = 2 := by
      rw [hσ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (show (0:Fin 3) ≠ 1 by decide)
          (show (0:Fin 3) ≠ 2 by decide),
        Equiv.swap_apply_left]
    have hσ1 : σ 1 = 0 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hσ2 : σ 2 = 1 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (show (1:Fin 3) ≠ 0 by decide)
          (show (1:Fin 3) ≠ 2 by decide)]
    set u := v ∘ σ with hu_def
    have hu0 : u 0 = v 2 := by simp [hu_def, hσ0]
    have hu1 : u 1 = v 0 := by simp [hu_def, hσ1]
    have hu2 : u 2 = v 1 := by simp [hu_def, hσ2]
    apply fracTuple_eq_of_pq_match
    · rw [hu0]; exact e2p
    · rw [hu0]; exact e2q
    · rw [hu1]; exact e0p
    · rw [hu1]; exact e0q
    · rw [hu2]; exact e1p
    · rw [hu2]; exact e1q
  · -- 5th disjunct: v 0 = w 2, v 1 = w 0, v 2 = w 1.
    -- σ 0 = 1 (v 1 = w 0). σ 1 = 2 (v 2 = w 1). σ 2 = 0 (v 0 = w 2).
    refine ⟨Equiv.swap 1 2 * Equiv.swap 0 2, w, hw, ?_⟩
    set σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 2 with hσ
    have hσ0 : σ 0 = 1 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hσ1 : σ 1 = 2 := by
      rw [hσ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (show (1:Fin 3) ≠ 0 by decide)
          (show (1:Fin 3) ≠ 2 by decide),
        Equiv.swap_apply_left]
    have hσ2 : σ 2 = 0 := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (show (0:Fin 3) ≠ 1 by decide)
          (show (0:Fin 3) ≠ 2 by decide)]
    set u := v ∘ σ with hu_def
    have hu0 : u 0 = v 1 := by simp [hu_def, hσ0]
    have hu1 : u 1 = v 2 := by simp [hu_def, hσ1]
    have hu2 : u 2 = v 0 := by simp [hu_def, hσ2]
    apply fracTuple_eq_of_pq_match
    · rw [hu0]; exact e1p
    · rw [hu0]; exact e1q
    · rw [hu1]; exact e2p
    · rw [hu1]; exact e2q
    · rw [hu2]; exact e0p
    · rw [hu2]; exact e0q
  · -- σ = swap 0 2: v 0 = w 2, v 1 = w 1, v 2 = w 0.
    refine ⟨Equiv.swap 0 2, w, hw, ?_⟩
    set u := v ∘ (Equiv.swap (0 : Fin 3) 2) with hu_def
    have hu0 : u 0 = v 2 := by simp [hu_def, Equiv.swap_apply_left]
    have hu1 : u 1 = v 1 := by
      simp [hu_def, Equiv.swap_apply_of_ne_of_ne (show (1:Fin 3) ≠ 0 by decide)
        (show (1:Fin 3) ≠ 2 by decide)]
    have hu2 : u 2 = v 0 := by simp [hu_def, Equiv.swap_apply_right]
    apply fracTuple_eq_of_pq_match
    · rw [hu0]; exact e2p
    · rw [hu0]; exact e2q
    · rw [hu1]; exact e1p
    · rw [hu1]; exact e1q
    · rw [hu2]; exact e0p
    · rw [hu2]; exact e0q

/-- For triples in `BoundedDiscCandidates` with auto-derived q ≥ 2 and
    coprimality, if `decideClassifiedNat t = true`, then `IsClassifiedNat`. -/
theorem isClassifiedNat_of_decideClassifiedNat
    (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ))
    (h0 : t.1 ∈ fracPairCandidates)
    (h1 : t.2.1 ∈ fracPairCandidates)
    (h2 : t.2.2 ∈ fracPairCandidates)
    (h_q_ge2 : 2 ≤ t.1.2 ∧ 2 ≤ t.2.1.2 ∧ 2 ≤ t.2.2.2)
    (h_coprime : Nat.Coprime t.1.1 t.1.2 ∧
                 Nat.Coprime t.2.1.1 t.2.1.2 ∧
                 Nat.Coprime t.2.2.1 t.2.2.2)
    (h_decide : decideClassifiedNat t = true) :
    IsClassifiedNat t h0 h1 h2 := by
  unfold decideClassifiedNat at h_decide
  rw [Bool.or_eq_true, Bool.or_eq_true] at h_decide
  rcases h_decide with (h_known | h_routeA) | h_routeB
  · -- isKnownDiscNat t = true: produce IsKnownDiscMod by matching one of the 12 multisets.
    left
    -- Decode isKnownDiscNat into list-membership.
    unfold isKnownDiscNat at h_known
    rw [List.any_eq_true] at h_known
    obtain ⟨⟨d, αd⟩, h_d_in_list, h_match⟩ := h_known
    -- Now match the 12 cases; in each, produce a permutation σ with v ∘ σ = canonical.
    set v := fracTupleOf t h0 h1 h2 with hv_def
    have h_t_eq : FracTuple.toNatTriple v = t := fracTupleOf_toNatTriple_eq t h0 h1 h2
    have hv_valid : ValidK v := fracTupleOf_valid t h0 h1 h2
    -- The match `h_match : matchesMultisetNat t d = true` along with d's
    -- position in `knownDiscNatList` lets us pick the corresponding canonical
    -- FracTuple `w` and find σ with `v ∘ σ = w`. We use the bridge below.
    -- Decompose `(d, αd) ∈ knownDiscNatList` by 12 cases.
    unfold knownDiscNatList at h_d_in_list
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h_d_in_list
    -- Helper lemma per case: given
    -- `matchesMultisetNat (toNatTriple v) (toNatTriple w_canon) = true`,
    -- with w_canon ∈ knownDiscList, produce IsKnownDiscMod v.
    -- The IsKnownDiscMod predicate: ∃ σ, ∃ w ∈ knownDiscList, v ∘ σ = w.
    -- The matchesMultisetNat decomposition gives the σ.
    have h_extract : ∀ (w : FracTuple 3), w ∈ knownDiscList →
        matchesMultisetNat (FracTuple.toNatTriple v) (FracTuple.toNatTriple w) = true →
        IsKnownDiscMod v :=
      fun w hw hm => isKnownDiscMod_of_matchesMultisetNat w hw hm
    -- Now case-split on the 12 cases of (d, αd) ∈ knownDiscNatList.
    rcases h_d_in_list with
      ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ |
      ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩
    -- For each of the 12 cases, d ∈ knownDiscNatList = toNatTriple-image of knownDiscList.
    -- Strategy: subst hd to make h_match's d concrete, then rewrite goal via toNatTriple_*.
    · -- (2,1),(2,1),(2,1) ↔ triple222
      subst hd
      apply h_extract triple222 (by simp [knownDiscList])
      rw [toNatTriple_triple222, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple223 (by simp [knownDiscList])
      rw [toNatTriple_triple223, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple233 (by simp [knownDiscList])
      rw [toNatTriple_triple233, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple333 (by simp [knownDiscList])
      rw [toNatTriple_triple333, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple_2_5o2_5o2 (by simp [knownDiscList])
      rw [toNatTriple_triple_2_5o2_5o2, h_t_eq]; exact h_match
    · -- d = ((3,1),(5,2),(5,2)). We use canonical `triple_5o2_5o2_3` (which has
      -- toNatTriple = ((5,2),(5,2),(3,1))) — same multiset as d, so matching is equivalent.
      subst hd
      apply h_extract triple_5o2_5o2_3 (by simp [knownDiscList])
      -- Goal: matchesMultisetNat (toNatTriple v) (toNatTriple triple_5o2_5o2_3) = true.
      -- toNatTriple triple_5o2_5o2_3 = ((5,2),(5,2),(3,1)).
      -- We have h_match : matchesMultisetNat t ((3,1),(5,2),(5,2)) = true.
      -- Same multiset; convert via decompose-and-recompose.
      rw [h_t_eq, toNatTriple_triple_5o2_5o2_3]
      -- Now goal: matchesMultisetNat t ((5,2),(5,2),(3,1)) = true.
      -- h_match already gives `((3,1),(5,2),(5,2))`. Same multiset.
      rcases matchesMultisetNat_decompose _ _ h_match with
        hh | hh | hh | hh | hh | hh
      all_goals (
        obtain ⟨hh0, hh1, hh2⟩ := hh
        unfold matchesMultisetNat
        simp only [hh0, hh1, hh2, Bool.or_eq_true, Bool.and_eq_true, beq_self_eq_true,
                   Bool.true_and, Bool.and_true, beq_iff_eq, Prod.mk.injEq, Bool.or_eq_true])
      all_goals tauto
    · subst hd
      apply h_extract triple_5o2_5o2_8o3 (by simp [knownDiscList])
      rw [toNatTriple_triple_5o2_5o2_8o3, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple_8o3_8o3_8o3 (by simp [knownDiscList])
      rw [toNatTriple_triple_8o3_8o3_8o3, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple_9o4_7o3_5o2 (by simp [knownDiscList])
      rw [toNatTriple_triple_9o4_7o3_5o2, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple_11o5_11o4_11o4 (by simp [knownDiscList])
      rw [toNatTriple_triple_11o5_11o4_11o4, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple_11o4_11o4_11o4 (by simp [knownDiscList])
      rw [toNatTriple_triple_11o4_11o4_11o4, h_t_eq]; exact h_match
    · subst hd
      apply h_extract triple_14o5_14o5_14o5 (by simp [knownDiscList])
      rw [toNatTriple_triple_14o5_14o5_14o5, h_t_eq]; exact h_match
  · -- Route A fired.
    exact isClassifiedNat_of_routeA t h0 h1 h2 h_q_ge2 h_coprime h_routeA
  · -- Route B fired (with Baumert).
    right
    rw [List.any_eq_true] at h_routeB
    obtain ⟨⟨d, αd⟩, h_d_in_list, h_match⟩ := h_routeB
    -- h_match has the inlined form; convert to discBelowMatchesNatFull.
    have h_match' : discBelowMatchesNatFull t d αd = true := h_match
    exact routeB_not_isDiscontinuityK_dispatch t h0 h1 h2 d αd h_d_in_list h_match'

/-! ## Refined converse: only require classification for t = toNatTriple v

The standard `theorem_6_9_converse_of_bounded_classification` requires
classification for all `t ∈ BoundedDiscCandidates`. But to actually use it we
need only classification at the specific `t = toNatTriple v` (which has the
strong q≥2 + coprime hypotheses). We provide a refined converse with this
weaker hypothesis. -/

/-- **Theorem 6.9 (converse, refined).** For valid `v` with q ≥ 2 and coprime
    everywhere, `IsClassifiedNat (toNatTriple v) ...` (at the specific tuple)
    suffices to conclude `IsKnownDiscMod v` from `IsDiscontinuityK v`. -/
theorem theorem_6_9_converse_of_classification_at_v
    {v : FracTuple 3} (hv_valid : ValidK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3)
    (hv_coprime : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ))
    (hv_q_ge2 : ∀ i, 2 ≤ ((v i).2 : ℕ))
    (hv_disc : IsDiscontinuityK v)
    (h_class_at_v : ∀ (h0 : (FracTuple.toNatTriple v).1 ∈ fracPairCandidates)
                      (h1 : (FracTuple.toNatTriple v).2.1 ∈ fracPairCandidates)
                      (h2 : (FracTuple.toNatTriple v).2.2 ∈ fracPairCandidates),
        IsClassifiedNat (FracTuple.toNatTriple v) h0 h1 h2) :
    IsKnownDiscMod v := by
  set t := FracTuple.toNatTriple v with ht_def
  have ht_mem : t ∈ BoundedDiscCandidates :=
    isDiscontinuityK_imp_mem_BoundedDiscCandidates hv_valid hv_disc hv_le3
      hv_coprime hv_q_ge2
  have ht_dc : t ∈ discCandidates := (mem_BoundedDiscCandidates.mp ht_mem).1
  unfold discCandidates at ht_dc
  rw [Finset.mem_product, Finset.mem_product] at ht_dc
  obtain ⟨h0, h1, h2⟩ := ht_dc
  have h_class_t := h_class_at_v h0 h1 h2
  have h_v_eq : v = fracTupleOf t h0 h1 h2 :=
    fracTupleOf_eq_of_toNatTriple t h0 h1 h2 ht_def.symm
  rcases h_class_t with h_known | h_not_disc
  · rw [h_v_eq]; exact h_known
  · rw [h_v_eq] at hv_disc
    exact absurd hv_disc h_not_disc

/-! ## The 441-element classification

Verify that every triple in `BoundedDiscCandidates` is classified by
`decideClassifiedNat`. -/

/-- **441-candidate decidability check.** Every triple in `BoundedDiscCandidates`
    has `decideClassifiedNat = true`. Discharged by `native_decide` (the 441
    candidates are enumerable; the classifier uses pure Bool predicates with
    nested-floor + interval + Baumert bounds + disc-multiset matching). -/
theorem decideClassifiedNat_BoundedDiscCandidates :
    ∀ t ∈ BoundedDiscCandidates, decideClassifiedNat t = true := by
  native_decide

/-! ## Theorem 6.9 (full bidirectional, q ≥ 2 hypothesis) -/

/-- **Theorem 6.9 (full bidirectional, `th:discont`)** — for triples with all
    denominators ≥ 2 (no integer slots), the α₃-discontinuities on `(ℚ ∩ [2, 3])³`
    are exactly the 12 listed multisets up to permutation.

    The integer-slot case is handled in `theorem_6_9_forward` (which proves
    forward direction unconditionally for all 12 cases including integer ones).
    The converse is proven by:
    - Membership in `BoundedDiscCandidates` (via `isDiscontinuityK_imp_mem_BoundedDiscCandidates`).
    - Classifier discharge for that one tuple (via `decideClassifiedNat` + `native_decide`). -/
theorem theorem_6_9_full
    (v : FracTuple 3) (hv_valid : ValidK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3)
    (hv_coprime : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ))
    (hv_q_ge2 : ∀ i, 2 ≤ ((v i).2 : ℕ)) :
    IsDiscontinuityK v ↔ IsKnownDiscMod v := by
  refine ⟨?_, theorem_6_9_forward⟩
  intro hv_disc
  apply theorem_6_9_converse_of_classification_at_v hv_valid hv_le3 hv_coprime
    hv_q_ge2 hv_disc
  intro h0 h1 h2
  -- Discharge IsClassifiedNat at t = toNatTriple v.
  set t := FracTuple.toNatTriple v with ht_def
  have ht_mem : t ∈ BoundedDiscCandidates :=
    isDiscontinuityK_imp_mem_BoundedDiscCandidates hv_valid hv_disc hv_le3
      hv_coprime hv_q_ge2
  -- Extract q ≥ 2 and coprime in t-form from v.
  have h_q_ge2_t : 2 ≤ t.1.2 ∧ 2 ≤ t.2.1.2 ∧ 2 ≤ t.2.2.2 :=
    ⟨hv_q_ge2 0, hv_q_ge2 1, hv_q_ge2 2⟩
  have h_cop_t : Nat.Coprime t.1.1 t.1.2 ∧
                 Nat.Coprime t.2.1.1 t.2.1.2 ∧
                 Nat.Coprime t.2.2.1 t.2.2.2 :=
    ⟨hv_coprime 0, hv_coprime 1, hv_coprime 2⟩
  -- Apply decideClassifiedNat at t.
  have h_decide : decideClassifiedNat t = true :=
    decideClassifiedNat_BoundedDiscCandidates t ht_mem
  exact isClassifiedNat_of_decideClassifiedNat t h0 h1 h2 h_q_ge2_t h_cop_t h_decide

/-! ## Unconditional bidirectional Theorem 6.9 (drops `q_i ≥ 2`)

The `q_i ≥ 2` hypothesis in `theorem_6_9_full` rules out the 6 paper cases
with integer slots (`(2,2,2), (2,2,3), (2,3,3), (3,3,3), (2, 5/2, 5/2),
(5/2, 5/2, 3)`). This section drops that hypothesis using
`lem:disc-integer` (`isDiscontinuityK_consInt` /
`isDiscontinuityK_of_consInt_disc`): an α₃-discontinuity with an integer
slot reduces to an α₂-discontinuity on the remaining two slots.

The reduction is fully proven; the residual α₂ classification statement
is taken as a hypothesis (`h_alpha2_classify`) — see
`alpha2_classification` below for the precise form. The full
unconditional theorem `theorem_6_9_unconditional` then drops `hv_q_ge2`.

Once an unconditional α₂ converse classification is supplied, the
parameterized form gives a fully unconditional bidirectional Theorem 6.9. -/

/-- **Bidirectional `lem:disc-integer`.** For `n ≥ 2`, `consInt n v` is an
    α-discontinuity iff `v` is. Combination of `isDiscontinuityK_consInt`
    (forward, `Section6DiscontinuityK.lean`) and
    `isDiscontinuityK_of_consInt_disc` (reverse). -/
theorem consInt_isDiscontinuityK_iff {k : ℕ} (n : ℕ+) (hn : 2 ≤ n)
    {v : FracTuple k} (hv_valid : ValidK v) :
    IsDiscontinuityK (consInt n v) ↔ IsDiscontinuityK v :=
  ⟨isDiscontinuityK_of_consInt_disc n hn,
   isDiscontinuityK_consInt n hn hv_valid⟩

/-! ### Factorization helpers: an integer slot factors `v` as `consInt n v'` -/

/-- Helper: `Fin.tail` for a `FracTuple (k + 1)` is a `FracTuple k`. -/
private def fracTupleTail {k : ℕ} (v : FracTuple (k + 1)) : FracTuple k :=
  fun j => v j.succ

/-- If `v 0 = (n, 1)`, then `v = consInt n (fracTupleTail v)`. -/
private lemma fracTuple_eq_consInt_of_q0_eq_one
    {k : ℕ} {v : FracTuple (k + 1)} (h0q : (v 0).2 = 1) :
    v = consInt (v 0).1 (fracTupleTail v) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    rw [consInt_zero]
    -- Goal: v 0 = ((v 0).1, 1). Use Prod.mk.eta backwards + h0q.
    conv_lhs => rw [show v 0 = ((v 0).1, (v 0).2) from rfl]
    rw [h0q]
  | succ j => simp [consInt_succ, fracTupleTail]

/-- The numerator of an integer slot `(v i).2 = 1` is bounded by 3 when
    `toRat v i ≤ 3`; coupled with `(v i).1 ≥ 2` from validity, it lies in
    `{2, 3}`. -/
private lemma int_slot_num_le_three {v : FracTuple 3} (hv_valid : ValidK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3) (i : Fin 3)
    (hq : ((v i).2 : ℕ) = 1) :
    ((v i).1 : ℕ) ≤ 3 ∧ 2 ≤ ((v i).1 : ℕ) := by
  refine ⟨?_, ?_⟩
  · -- p_i / 1 ≤ 3 → p_i ≤ 3.
    have h := hv_le3 i
    unfold FracTuple.toRat at h
    have hq_q : ((v i).2 : ℚ) = 1 := by exact_mod_cast hq
    rw [hq_q, div_one] at h
    exact_mod_cast h
  · -- 2 * 1 ≤ p_i from validity.
    have h := hv_valid i
    have h_nat : (2 : ℕ) * ((v i).2 : ℕ) ≤ ((v i).1 : ℕ) := by exact_mod_cast h
    omega

/-! ### α₂ classification statement (hypothesis form)

We package the α₂ converse classification as a precise Prop, parameterized
out of the unconditional theorem below. When supplied, it discharges the
integer-slot case by reducing via `consInt_isDiscontinuityK_iff` to a
2-tuple. The 4 α₂-discs in `(ℚ ∩ [2, 3])²` (paper §6 line 2778) are
`(2, 2), (2, 3), (3, 3), (5/2, 5/2)`; only their `consInt n`-extensions
appear among the 6 integer/mixed-integer α₃-discs. -/

/-- The 4 α₂-disc tuples in lowest terms with values in `[2, 3]`. -/
def knownDisc2List : List (FracTuple 2) :=
  [ ![(2, 1), (2, 1)],
    ![(2, 1), (3, 1)],
    ![(3, 1), (3, 1)],
    ![(5, 2), (5, 2)] ]

/-- `v : FracTuple 2` matches one of the 4 paper-canonical α₂-disc tuples
    up to permutation. -/
def IsKnownDisc2Mod (v : FracTuple 2) : Prop :=
  ∃ σ : Equiv.Perm (Fin 2), ∃ w ∈ knownDisc2List, v ∘ σ = w

/-- The α₂ converse classification statement: every α₂-discontinuity
    `v' : FracTuple 2` valid + lowest-terms + `toRat ≤ 3` matches one of
    the 4 paper-canonical α₂-disc multisets up to permutation. This is
    the analog of `theorem_6_9_full` at `k = 2`; supplied as a hypothesis
    to `theorem_6_9_unconditional_of_alpha2_classification` below. -/
def Alpha2Classification : Prop :=
  ∀ v' : FracTuple 2, ValidK v' →
    (∀ i, FracTuple.toRat v' i ≤ 3) →
    (∀ i, Nat.Coprime ((v' i).1 : ℕ) ((v' i).2 : ℕ)) →
    IsDiscontinuityK v' →
    IsKnownDisc2Mod v'

/-! ### Lifting `IsKnownDisc2Mod` to `IsKnownDiscMod` via `consInt n` -/

/-- Helper: `consInt n v ∘ extendPerm σ = consInt n (v ∘ σ)`. -/
private lemma consInt_comp_extendPerm {k : ℕ} (n : ℕ+) (v : FracTuple k)
    (σ : Equiv.Perm (Fin k)) :
    (consInt n v) ∘ extendPerm σ = consInt n (v ∘ σ) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    change (consInt n v) (extendPerm σ 0) = (consInt n (v ∘ σ)) 0
    have : extendPerm σ 0 = (0 : Fin (k + 1)) := by
      simp [extendPerm]
    rw [this, consInt_zero, consInt_zero]
  | succ j =>
    change (consInt n v) (extendPerm σ j.succ) = (consInt n (v ∘ σ)) j.succ
    have : extendPerm σ j.succ = (σ j).succ := by
      simp [extendPerm]
    rw [this, consInt_succ, consInt_succ]
    rfl

/-- For `n : ℕ+` with `(n : ℕ) = m`, equality of `(n, 1) : ℕ+ × ℕ+` with
    `(m, 1) : ℕ+ × ℕ+` (constructor form). -/
private lemma consInt_zero_eq_pnat (n : ℕ+) (m : ℕ+) (h : (n : ℕ) = (m : ℕ)) :
    ((n, 1) : ℕ+ × ℕ+) = ((m, 1) : ℕ+ × ℕ+) := by
  apply Prod.ext
  · exact PNat.coe_inj.mp h
  · rfl

/-- Lift each of the 4 α₂-discs through `consInt n` for `n ∈ {2, 3}` to a
    member of `knownDiscList`. The 8 resulting tuples cover the 6
    integer/mixed-integer paper cases (cases 1–6) up to permutation.

    For each case, we exhibit a permutation σ ∈ S₃ such that
    `(consInt n v') ∘ σ = w` for some `w ∈ knownDiscList`. -/
private lemma isKnownDiscMod_of_consInt_isKnownDisc2Mod
    (n : ℕ+) (hn2 : 2 ≤ (n : ℕ)) (hn3 : (n : ℕ) ≤ 3)
    {v' : FracTuple 2} (h2 : IsKnownDisc2Mod v') :
    IsKnownDiscMod (consInt n v') := by
  -- It suffices to handle the case v' ∈ knownDisc2List directly, then
  -- compose permutations.
  obtain ⟨σ', w', hw'_mem, hw'_eq⟩ := h2
  -- Reduce to: IsKnownDiscMod (consInt n w'), then transfer back via σ'.
  suffices h_target : IsKnownDiscMod (consInt n w') by
    obtain ⟨τ, w_match, hw_match_mem, hw_match_eq⟩ := h_target
    refine ⟨extendPerm σ' * τ, w_match, hw_match_mem, ?_⟩
    rw [show (consInt n v') ∘ (extendPerm σ' * τ) =
          ((consInt n v') ∘ extendPerm σ') ∘ τ from rfl,
        consInt_comp_extendPerm, hw'_eq]
    exact hw_match_eq
  -- n = 2 or n = 3.
  have hn_cases : (n : ℕ) = 2 ∨ (n : ℕ) = 3 := by omega
  -- Case-split on w' ∈ knownDisc2List.
  simp only [knownDisc2List, List.mem_cons, List.not_mem_nil, or_false] at hw'_mem
  -- helper: equality of pnat (n,1) with (2,1) or (3,1).
  rcases hw'_mem with rfl | rfl | rfl | rfl
  · -- w' = (2, 2).
    rcases hn_cases with hn | hn
    · -- consInt 2 (2,2) = triple222.
      refine ⟨1, triple222, by simp [knownDiscList], ?_⟩
      have h_n21 : ((n, 1) : ℕ+ × ℕ+) = ((2, 1) : ℕ+ × ℕ+) :=
        consInt_zero_eq_pnat n 2 hn
      funext i; fin_cases i
      · change consInt n ![(2, 1), (2, 1)] 0 = triple222 0
        rw [consInt_zero]
        change ((n, 1) : ℕ+ × ℕ+) = ((2, 1) : ℕ+ × ℕ+)
        exact consInt_zero_eq_pnat n 2 hn
      · rfl
      · rfl
    · -- consInt 3 (2,2). Swap 0 ↔ 2 gives (2, 2, 3) = triple223.
      refine ⟨Equiv.swap (0 : Fin 3) 2, triple223, by simp [knownDiscList], ?_⟩
      have h_n31 : ((n, 1) : ℕ+ × ℕ+) = ((3, 1) : ℕ+ × ℕ+) :=
        consInt_zero_eq_pnat n 3 hn
      funext i; fin_cases i
      · change (consInt n ![(2, 1), (2, 1)]) ((Equiv.swap (0 : Fin 3) 2) 0) =
              triple223 0
        rw [Equiv.swap_apply_left]
        change ((consInt n ![(2, 1), (2, 1)]) (2 : Fin 3)) = ((2, 1) : ℕ+ × ℕ+)
        rfl
      · change (consInt n ![(2, 1), (2, 1)]) ((Equiv.swap (0 : Fin 3) 2) 1) =
              triple223 1
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        rfl
      · change (consInt n ![(2, 1), (2, 1)]) ((Equiv.swap (0 : Fin 3) 2) 2) =
              triple223 2
        rw [Equiv.swap_apply_right]
        change ((consInt n ![(2, 1), (2, 1)]) 0) = ((3, 1) : ℕ+ × ℕ+)
        rw [consInt_zero]; exact h_n31
  · -- w' = (2, 3).
    rcases hn_cases with hn | hn
    · -- consInt 2 (2,3) = (2, 2, 3) = triple223.
      refine ⟨1, triple223, by simp [knownDiscList], ?_⟩
      have h_n21 : ((n, 1) : ℕ+ × ℕ+) = ((2, 1) : ℕ+ × ℕ+) :=
        consInt_zero_eq_pnat n 2 hn
      funext i; fin_cases i
      · change consInt n ![(2, 1), (3, 1)] 0 = triple223 0
        rw [consInt_zero]
        change ((n, 1) : ℕ+ × ℕ+) = ((2, 1) : ℕ+ × ℕ+)
        exact consInt_zero_eq_pnat n 2 hn
      · rfl
      · rfl
    · -- consInt 3 (2,3) = (3, 2, 3). Swap 0 ↔ 1 gives (2, 3, 3) = triple233.
      refine ⟨Equiv.swap (0 : Fin 3) 1, triple233, by simp [knownDiscList], ?_⟩
      have h_n31 : ((n, 1) : ℕ+ × ℕ+) = ((3, 1) : ℕ+ × ℕ+) :=
        consInt_zero_eq_pnat n 3 hn
      funext i; fin_cases i
      · change (consInt n ![(2, 1), (3, 1)]) ((Equiv.swap (0 : Fin 3) 1) 0) =
              triple233 0
        rw [Equiv.swap_apply_left]
        rfl
      · change (consInt n ![(2, 1), (3, 1)]) ((Equiv.swap (0 : Fin 3) 1) 1) =
              triple233 1
        rw [Equiv.swap_apply_right]
        change ((consInt n ![(2, 1), (3, 1)]) 0) = ((3, 1) : ℕ+ × ℕ+)
        rw [consInt_zero]; exact h_n31
      · change (consInt n ![(2, 1), (3, 1)]) ((Equiv.swap (0 : Fin 3) 1) 2) =
              triple233 2
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        rfl
  · -- w' = (3, 3).
    rcases hn_cases with hn | hn
    · -- consInt 2 (3,3) = (2, 3, 3) = triple233.
      refine ⟨1, triple233, by simp [knownDiscList], ?_⟩
      have h_n21 : ((n, 1) : ℕ+ × ℕ+) = ((2, 1) : ℕ+ × ℕ+) :=
        consInt_zero_eq_pnat n 2 hn
      funext i; fin_cases i
      · change consInt n ![(3, 1), (3, 1)] 0 = triple233 0
        rw [consInt_zero]
        change ((n, 1) : ℕ+ × ℕ+) = ((2, 1) : ℕ+ × ℕ+)
        exact consInt_zero_eq_pnat n 2 hn
      · rfl
      · rfl
    · -- consInt 3 (3,3) = (3, 3, 3) = triple333.
      refine ⟨1, triple333, by simp [knownDiscList], ?_⟩
      have h_n31 : ((n, 1) : ℕ+ × ℕ+) = ((3, 1) : ℕ+ × ℕ+) :=
        consInt_zero_eq_pnat n 3 hn
      funext i; fin_cases i
      · change consInt n ![(3, 1), (3, 1)] 0 = triple333 0
        rw [consInt_zero]
        change ((n, 1) : ℕ+ × ℕ+) = ((3, 1) : ℕ+ × ℕ+)
        exact consInt_zero_eq_pnat n 3 hn
      · rfl
      · rfl
  · -- w' = (5/2, 5/2).
    rcases hn_cases with hn | hn
    · -- consInt 2 (5/2, 5/2) = (2, 5/2, 5/2) = triple_2_5o2_5o2.
      refine ⟨1, triple_2_5o2_5o2, by simp [knownDiscList], ?_⟩
      have h_n21 : ((n, 1) : ℕ+ × ℕ+) = ((2, 1) : ℕ+ × ℕ+) :=
        consInt_zero_eq_pnat n 2 hn
      funext i; fin_cases i
      · change consInt n ![(5, 2), (5, 2)] 0 = triple_2_5o2_5o2 0
        rw [consInt_zero]
        change ((n, 1) : ℕ+ × ℕ+) = ((2, 1) : ℕ+ × ℕ+)
        exact consInt_zero_eq_pnat n 2 hn
      · rfl
      · rfl
    · -- consInt 3 (5/2, 5/2) = (3, 5/2, 5/2). Swap 0 ↔ 2 gives (5/2, 5/2, 3) = triple_5o2_5o2_3.
      refine ⟨Equiv.swap (0 : Fin 3) 2, triple_5o2_5o2_3, by simp [knownDiscList], ?_⟩
      have h_n31 : ((n, 1) : ℕ+ × ℕ+) = ((3, 1) : ℕ+ × ℕ+) :=
        consInt_zero_eq_pnat n 3 hn
      funext i; fin_cases i
      · change (consInt n ![(5, 2), (5, 2)]) ((Equiv.swap (0 : Fin 3) 2) 0) =
              triple_5o2_5o2_3 0
        rw [Equiv.swap_apply_left]
        rfl
      · change (consInt n ![(5, 2), (5, 2)]) ((Equiv.swap (0 : Fin 3) 2) 1) =
              triple_5o2_5o2_3 1
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        rfl
      · change (consInt n ![(5, 2), (5, 2)]) ((Equiv.swap (0 : Fin 3) 2) 2) =
              triple_5o2_5o2_3 2
        rw [Equiv.swap_apply_right]
        change ((consInt n ![(5, 2), (5, 2)]) 0) = ((3, 1) : ℕ+ × ℕ+)
        rw [consInt_zero]; exact h_n31

/-! ### Unconditional `theorem_6_9` parameterized by α₂ classification -/

/-- **Theorem 6.9 (unconditional bidirectional, parameterized by α₂
    classification).** Drops `hv_q_ge2`. The integer-slot case is reduced
    via `lem:disc-integer` to a 2-tuple; the residual α₂ converse
    classification is supplied as `h_alpha2`. -/
theorem theorem_6_9_unconditional_of_alpha2_classification
    (h_alpha2 : Alpha2Classification)
    (v : FracTuple 3) (hv_valid : ValidK v)
    (hv_le3 : ∀ i, FracTuple.toRat v i ≤ 3)
    (hv_coprime : ∀ i, Nat.Coprime ((v i).1 : ℕ) ((v i).2 : ℕ)) :
    IsDiscontinuityK v ↔ IsKnownDiscMod v := by
  refine ⟨?_, theorem_6_9_forward⟩
  intro hv_disc
  -- Case split: all q_i ≥ 2, or some q_i = 1.
  by_cases h_all_q_ge2 : ∀ i, 2 ≤ ((v i).2 : ℕ)
  · -- All q_i ≥ 2: invoke theorem_6_9_full.
    exact (theorem_6_9_full v hv_valid hv_le3 hv_coprime h_all_q_ge2).mp hv_disc
  · -- Some q_i = 1: pick that slot, permute to slot 0, reduce via consInt.
    push_neg at h_all_q_ge2
    obtain ⟨i₀, hi₀⟩ := h_all_q_ge2
    -- (v i₀).2 ≥ 1 (PNat), and < 2 from hi₀, so = 1.
    have hi₀_q : ((v i₀).2 : ℕ) = 1 := by
      have h_pos : (1 : ℕ) ≤ ((v i₀).2 : ℕ) := (v i₀).2.pos
      omega
    -- Permute i₀ to slot 0.
    set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 i₀ with hσ_def
    set w := v ∘ σ with hw_def
    have hw_valid : ValidK w := fun j => hv_valid (σ j)
    have hw_le3 : ∀ i, FracTuple.toRat w i ≤ 3 := fun i => hv_le3 (σ i)
    have hw_coprime : ∀ i, Nat.Coprime ((w i).1 : ℕ) ((w i).2 : ℕ) :=
      fun i => hv_coprime (σ i)
    have hw_disc : IsDiscontinuityK w := (isDiscontinuityK_perm σ).mp hv_disc
    have hw0 : w 0 = v i₀ := by
      change v (σ 0) = v i₀
      rw [hσ_def, Equiv.swap_apply_left]
    have hw0_q : ((w 0).2 : ℕ) = 1 := by rw [hw0]; exact hi₀_q
    -- Bound on (w 0).1: 2 ≤ (w 0).1 ≤ 3.
    have h_n_bd : ((w 0).1 : ℕ) ≤ 3 ∧ 2 ≤ ((w 0).1 : ℕ) := by
      have h := int_slot_num_le_three hw_valid hw_le3 0 hw0_q
      exact h
    -- Factor w as consInt n (fracTupleTail w).
    have hw0_q_pnat : (w 0).2 = 1 := by
      apply PNat.coe_inj.mp; exact hw0_q
    have hw_eq : w = consInt (w 0).1 (fracTupleTail w) :=
      fracTuple_eq_consInt_of_q0_eq_one hw0_q_pnat
    set n := (w 0).1 with hn_def
    set v' : FracTuple 2 := fracTupleTail w with hv'_def
    have hn_ge2 : 2 ≤ n := by
      change (2 : ℕ+) ≤ n
      exact_mod_cast h_n_bd.2
    -- v' is valid: validity transfers via consInt_validK relationship.
    have hv'_valid : ValidK v' := by
      intro j
      have h := hw_valid j.succ
      rw [hw_eq] at h
      simpa [consInt_succ, v'] using h
    have hv'_le3 : ∀ i, FracTuple.toRat v' i ≤ 3 := by
      intro i
      have h := hw_le3 i.succ
      rw [hw_eq] at h
      rwa [consInt_toRat_succ] at h
    have hv'_coprime : ∀ i, Nat.Coprime ((v' i).1 : ℕ) ((v' i).2 : ℕ) := by
      intro i
      have h := hw_coprime i.succ
      rw [hw_eq] at h
      simpa [consInt_succ, v'] using h
    -- IsDiscontinuityK v' from consInt iff.
    have hw_eq_consInt : IsDiscontinuityK (consInt n v') := by
      rw [← hw_eq]; exact hw_disc
    have hv'_disc : IsDiscontinuityK v' :=
      (consInt_isDiscontinuityK_iff n hn_ge2 hv'_valid).mp hw_eq_consInt
    -- Apply α₂ classification to v'.
    have hv'_known : IsKnownDisc2Mod v' :=
      h_alpha2 v' hv'_valid hv'_le3 hv'_coprime hv'_disc
    -- Lift to IsKnownDiscMod (consInt n v') = IsKnownDiscMod w.
    have hw_known : IsKnownDiscMod w := by
      rw [hw_eq]
      exact isKnownDiscMod_of_consInt_isKnownDisc2Mod n h_n_bd.2 h_n_bd.1 hv'_known
    -- Transfer back to v: w = v ∘ σ, so v = w ∘ σ⁻¹.
    obtain ⟨τ, w_match, hw_match_mem, hw_match_eq⟩ := hw_known
    refine ⟨σ * τ, w_match, hw_match_mem, ?_⟩
    rw [show v ∘ (σ * τ) = (v ∘ σ) ∘ τ from rfl, ← hw_def]
    exact hw_match_eq

end Section6
