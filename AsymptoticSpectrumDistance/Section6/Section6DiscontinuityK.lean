/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Discontinuities of `α_k` (unified, all k)

Generalizes `alpha2`/`alpha3` and `IsDiscontinuity₂`/`IsDiscontinuity` to a
single `alphaK : (k : ℕ) → FracTuple k → ℕ` over `Fin k`-indexed tuples.
Targets the paper's `lem:disc-integer` (Section 6, line 2744) at full
generality: prepending an integer `n ≥ 2` to any `α_k`-discontinuity
yields an `α_{k+1}`-discontinuity (and the converse also holds).

Bridges to `alpha2`/`alpha3` are provided so the FracTriple-form
disc statements continue to work without changes to `Main.lean`.

## Main definitions

* `FracTuple k := Fin k → ℕ+ × ℕ+`
* `FracTuple.toRat v i : ℚ`
* `alphaK v : ℕ` — uses `bigStrongProduct` of the corresponding fraction graphs
* `lePermK`, `ltPermK`, `ValidK`, `IsDiscontinuityK`

## Main results

* `alphaK_two` : `alphaK v = alpha2 v` for `v : FracTuple 2` (bridge).
* `alphaK_three` : `alphaK v = alpha3 v` for `v : FracTuple 3` (bridge).
* `alphaK_le_of_lePermK` : monotonicity of `alphaK` under `lePermK`.
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.BigStrongProduct
import AsymptoticSpectrumDistance.Prerequisites.ShannonCapacity
import AsymptoticSpectrumDistance.Section6.Section6IntegerFactor
import AsymptoticSpectrumDistance.Section6.Section6Diagonal

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-- A `Fin k`-indexed tuple of fraction-graph parameters. -/
abbrev FracTuple (k : ℕ) := Fin k → ℕ+ × ℕ+

/-- The `i`-th coordinate of a `FracTuple` viewed as a rational. -/
def FracTuple.toRat {k : ℕ} (v : FracTuple k) (i : Fin k) : ℚ :=
  ((v i).1 : ℚ) / ((v i).2 : ℚ)

/-- `α_k(p₁/q₁, ..., pₖ/qₖ) = α(E_{p₁/q₁} ⊠ ⋯ ⊠ E_{pₖ/qₖ})`,
    realized as the independence number of `bigStrongProduct` of the
    corresponding `fractionGraph`s. -/
noncomputable def alphaK {k : ℕ} (v : FracTuple k) : ℕ :=
  (bigStrongProduct (fun i => fractionGraph (v i).1 (v i).2)).indepNum

/-- Permutation-aware product order on `FracTuple k`s. -/
def lePermK {k : ℕ} (u v : FracTuple k) : Prop :=
  ∃ σ : Equiv.Perm (Fin k),
    ∀ i, FracTuple.toRat u (σ i) ≤ FracTuple.toRat v i

/-- Strict version: `u <ₚ v` iff `lePermK u v ∧ ¬ lePermK v u`. -/
def ltPermK {k : ℕ} (u v : FracTuple k) : Prop := lePermK u v ∧ ¬ lePermK v u

/-- A `FracTuple` is valid iff each coordinate satisfies `2q ≤ p`
    (equivalently, `toRat ≥ 2`). -/
def ValidK {k : ℕ} (v : FracTuple k) : Prop := ∀ i, 2 * (v i).2 ≤ (v i).1

/-- `v` is a discontinuity of `α_k` iff every strictly smaller valid `u`
    has strictly smaller `α_k`. -/
def IsDiscontinuityK {k : ℕ} (v : FracTuple k) : Prop :=
  ∀ u, ValidK u → ltPermK u v → alphaK u < alphaK v

/-! ## Helpers -/

lemma toRatK_ge_two_of_valid {k : ℕ} {u : FracTuple k} (hu : ValidK u) (i : Fin k) :
    (2 : ℚ) ≤ FracTuple.toRat u i := by
  have h := hu i
  unfold FracTuple.toRat
  rw [le_div_iff₀ (by exact_mod_cast (u i).2.pos : (0 : ℚ) < ((u i).2 : ℚ))]
  exact_mod_cast h

lemma toRatK_pos_of_valid {k : ℕ} {u : FracTuple k} (hu : ValidK u) (i : Fin k) :
    (0 : ℚ) < FracTuple.toRat u i :=
  lt_of_lt_of_le (by norm_num) (toRatK_ge_two_of_valid hu i)

/-! ## Integer-prepend `consInt` and value formula -/

/-- Prepend the integer `(n, 1)` at slot 0, shifting `v` to slots 1..k. -/
def consInt {k : ℕ} (n : ℕ+) (v : FracTuple k) : FracTuple (k + 1) :=
  Fin.cons (n, 1) v

@[simp] lemma consInt_zero {k : ℕ} (n : ℕ+) (v : FracTuple k) :
    (consInt n v) 0 = (n, 1) := Fin.cons_zero _ _

@[simp] lemma consInt_succ {k : ℕ} (n : ℕ+) (v : FracTuple k) (i : Fin k) :
    (consInt n v) i.succ = v i := Fin.cons_succ _ _ _

@[simp] lemma consInt_toRat_zero {k : ℕ} (n : ℕ+) (v : FracTuple k) :
    FracTuple.toRat (consInt n v) 0 = (n : ℚ) := by
  simp [FracTuple.toRat]

@[simp] lemma consInt_toRat_succ {k : ℕ} (n : ℕ+) (v : FracTuple k) (i : Fin k) :
    FracTuple.toRat (consInt n v) i.succ = FracTuple.toRat v i := by
  simp [FracTuple.toRat]

/-- `ValidK v + n ≥ 2` lifts to `ValidK (consInt n v)`. -/
lemma consInt_validK {k : ℕ} (n : ℕ+) (hn : 2 ≤ n) {v : FracTuple k}
    (hv : ValidK v) : ValidK (consInt n v) := by
  intro i
  cases i using Fin.cases with
  | zero => change 2 * (1 : ℕ+) ≤ n; exact_mod_cast hn
  | succ j => exact hv j

/-- **Value formula** (paper integer-factor formula generalized):
    `α_{k+1}(consInt n v) = n · α_k(v)` for `n ≥ 2`. -/
theorem alphaK_consInt {k : ℕ} (n : ℕ+) (hn : 2 ≤ n) (v : FracTuple k) :
    alphaK (consInt n v) = n * alphaK v := by
  -- Rewrite using the recursive characterization of bigStrongProduct.
  have h_iso := SimpleGraph.independenceNumber_iso
    (bigStrongProduct_succ_iso
      (fun i : Fin (k + 1) =>
        fractionGraph ((consInt n v) i).1 ((consInt n v) i).2))
  unfold alphaK
  rw [h_iso]
  -- The iso target is: ((G 0) ⊠ bigStrongProduct (G ∘ Fin.succ)).indepNum where
  -- G i := fractionGraph (consInt n v i).1 (consInt n v i).2.
  -- By consInt_zero and consInt_succ:
  --   G 0 = fractionGraph n 1
  --   G ∘ Fin.succ i = fractionGraph (v i).1 (v i).2
  -- These are definitionally equal, so `change` succeeds.
  change (strongProduct (fractionGraph (n : ℕ) (1 : ℕ))
      (bigStrongProduct
        (fun i : Fin k => fractionGraph (v i).1 (v i).2))).indepNum = _
  rw [indepNum_strongProduct_edgeless_fraction (n : ℕ) (by exact_mod_cast hn)]

/-! ## `consInt` preserves order

The integer-prepend extends `lePermK` from `FracTuple k` to `FracTuple (k+1)`.
Strict order (`ltPermK`) extension requires restricting a `Fin (k+1)`-permutation
back to `Fin k` (handled by `restrictPerm` below). -/

/-- Extend a permutation of `Fin k` to a permutation of `Fin (k+1)` by
    fixing the first index. -/
def extendPerm {k : ℕ} (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv := by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp
  right_inv := by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp

@[simp] lemma extendPerm_zero {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    extendPerm σ 0 = 0 := by simp [extendPerm]

@[simp] lemma extendPerm_succ {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    extendPerm σ i.succ = (σ i).succ := by simp [extendPerm]

/-- `consInt` is monotone in the `lePermK` order. -/
lemma consInt_lePermK {k : ℕ} (n : ℕ+) {u v : FracTuple k}
    (h : lePermK u v) : lePermK (consInt n u) (consInt n v) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨extendPerm σ, ?_⟩
  intro i
  cases i using Fin.cases with
  | zero => simp [FracTuple.toRat]
  | succ j =>
    simp only [extendPerm_succ, consInt_toRat_succ]
    exact hσ j

/-- For `τ : Equiv.Perm (Fin (k+1))`, define `σ := swap (τ 0) 0 * τ`. This
    permutation fixes 0 (since `swap (τ 0) 0` sends `τ 0 ↦ 0`). -/
private def σ_fix0 {k : ℕ} (τ : Equiv.Perm (Fin (k + 1))) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.swap (τ 0) 0 * τ

private lemma σ_fix0_zero {k : ℕ} (τ : Equiv.Perm (Fin (k + 1))) :
    σ_fix0 τ 0 = 0 := by
  simp [σ_fix0, Equiv.Perm.mul_apply, Equiv.swap_apply_left]

private lemma σ_fix0_symm_zero {k : ℕ} (τ : Equiv.Perm (Fin (k + 1))) :
    (σ_fix0 τ).symm 0 = 0 := by
  have h := σ_fix0_zero τ
  have := (σ_fix0 τ).symm_apply_apply 0
  rw [h] at this
  exact this

private lemma σ_fix0_succ_ne_zero {k : ℕ} (τ : Equiv.Perm (Fin (k + 1))) (j : Fin k) :
    σ_fix0 τ j.succ ≠ 0 := by
  intro h
  have heq : σ_fix0 τ j.succ = σ_fix0 τ 0 := by rw [h, σ_fix0_zero]
  have : j.succ = (0 : Fin (k + 1)) := (σ_fix0 τ).injective heq
  exact Fin.succ_ne_zero j this

private lemma σ_fix0_symm_succ_ne_zero {k : ℕ} (τ : Equiv.Perm (Fin (k + 1)))
    (j : Fin k) : (σ_fix0 τ).symm j.succ ≠ 0 := by
  intro h
  have heq : (σ_fix0 τ).symm j.succ = (σ_fix0 τ).symm 0 := by rw [h, σ_fix0_symm_zero]
  have : j.succ = (0 : Fin (k + 1)) := (σ_fix0 τ).symm.injective heq
  exact Fin.succ_ne_zero j this

/-- Restrict a `Fin (k+1)`-perm to a `Fin k`-perm by absorbing the action
    on slot 0 via `σ_fix0`, then projecting via `Fin.pred`. -/
private def restrictPerm {k : ℕ} (τ : Equiv.Perm (Fin (k + 1))) : Equiv.Perm (Fin k) where
  toFun := fun j => (σ_fix0 τ j.succ).pred (σ_fix0_succ_ne_zero τ j)
  invFun := fun j => ((σ_fix0 τ).symm j.succ).pred (σ_fix0_symm_succ_ne_zero τ j)
  left_inv := by
    intro j
    apply Fin.succ_injective
    rw [Fin.succ_pred, Fin.succ_pred, (σ_fix0 τ).symm_apply_apply]
  right_inv := by
    intro j
    apply Fin.succ_injective
    rw [Fin.succ_pred, Fin.succ_pred, (σ_fix0 τ).apply_symm_apply]

private lemma restrictPerm_succ {k : ℕ} (τ : Equiv.Perm (Fin (k + 1))) (j : Fin k) :
    (restrictPerm τ j).succ = σ_fix0 τ j.succ := by
  change ((σ_fix0 τ j.succ).pred (σ_fix0_succ_ne_zero τ j)).succ = σ_fix0 τ j.succ
  rw [Fin.succ_pred]

/-- `consInt` is monotone in `ltPermK`. -/
lemma consInt_ltPermK {k : ℕ} (n : ℕ+) {u v : FracTuple k}
    (h : ltPermK u v) : ltPermK (consInt n u) (consInt n v) := by
  refine ⟨consInt_lePermK n h.1, ?_⟩
  intro h_back
  apply h.2
  obtain ⟨τ, hτ⟩ := h_back
  refine ⟨restrictPerm τ, ?_⟩
  intro j
  -- Goal: v.toRat (restrictPerm τ j) ≤ u.toRat j.
  -- (restrictPerm τ j).succ = σ_fix0 τ j.succ = swap (τ 0) 0 (τ j.succ).
  -- Case 1: τ j.succ = 0. Then σ_fix0 τ j.succ = swap (τ 0) 0 0 = τ 0.
  --   τ 0 ≠ 0 (else τ injective gives j.succ = 0).
  --   v.toRat ((τ 0).pred _) follows; combined with hτ 0 and hτ j.succ.
  -- Case 2: τ j.succ ≠ 0. Then either τ j.succ = τ 0 (impossible, τ inj) or
  --   it's neither 0 nor τ 0, so swap fixes it. σ_fix0 τ j.succ = τ j.succ.
  --   Direct from hτ j.succ.
  have h_eq : (restrictPerm τ j).succ = σ_fix0 τ j.succ := restrictPerm_succ τ j
  by_cases hτj : τ j.succ = 0
  · -- Case 1: τ j.succ = 0.
    have h_τ0_ne : τ 0 ≠ 0 := by
      intro h0
      have : τ j.succ = τ 0 := by rw [hτj, h0]
      exact Fin.succ_ne_zero j (τ.injective this)
    have h_σ_eq : σ_fix0 τ j.succ = τ 0 := by
      simp [σ_fix0, Equiv.Perm.mul_apply, hτj, Equiv.swap_apply_right]
    -- (restrictPerm τ j).succ = τ 0
    have h_succ_eq : (restrictPerm τ j).succ = τ 0 := h_eq.trans h_σ_eq
    -- hτ 0: (consInt n v).toRat (τ 0) ≤ n.
    have h_τ0 := hτ 0
    rw [show (consInt n u).toRat 0 = (n : ℚ) from consInt_toRat_zero n u] at h_τ0
    rw [← h_succ_eq, consInt_toRat_succ] at h_τ0
    -- h_τ0: v.toRat (restrictPerm τ j) ≤ n.
    -- hτ j.succ: (consInt n v).toRat 0 = n ≤ u.toRat j.
    have h_jsucc := hτ j.succ
    rw [hτj, consInt_toRat_zero, consInt_toRat_succ] at h_jsucc
    -- h_jsucc: n ≤ u.toRat j.
    linarith
  · -- Case 2: τ j.succ ≠ 0.
    -- τ j.succ ≠ τ 0 either (else τ injective gives j.succ = 0).
    have h_τjsucc_ne_τ0 : τ j.succ ≠ τ 0 := by
      intro heq
      have : j.succ = (0 : Fin (k + 1)) := τ.injective heq
      exact Fin.succ_ne_zero j this
    -- σ_fix0 τ j.succ = swap (τ 0) 0 (τ j.succ) = τ j.succ.
    have h_σ_eq : σ_fix0 τ j.succ = τ j.succ := by
      simp [σ_fix0, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne h_τjsucc_ne_τ0 hτj]
    have h_succ_eq : (restrictPerm τ j).succ = τ j.succ := h_eq.trans h_σ_eq
    have h_jsucc := hτ j.succ
    rw [← h_succ_eq, consInt_toRat_succ, consInt_toRat_succ] at h_jsucc
    exact h_jsucc

/-! ## `lem:disc-integer` (reverse direction)

If `consInt n v` is an `α_{k+1}`-discontinuity, then `v` is an
`α_k`-discontinuity. Proof: pull back via the value formula
`α_{k+1}(consInt n v) = n · αₖ(v)`. -/

/-- **Reverse direction of `lem:disc-integer`.** Given a `(k+1)`-disc
    of the form `consInt n v`, the `k`-tuple `v` is `α_k`-disc. -/
theorem isDiscontinuityK_of_consInt_disc {k : ℕ} (n : ℕ+) (hn : 2 ≤ n)
    {v : FracTuple k}
    (h_disc : IsDiscontinuityK (consInt n v)) :
    IsDiscontinuityK v := by
  intro u hu_valid hlt
  have hu_consInt_valid : ValidK (consInt n u) := consInt_validK n hn hu_valid
  have h_lt_consInt : ltPermK (consInt n u) (consInt n v) :=
    consInt_ltPermK n hlt
  have h := h_disc (consInt n u) hu_consInt_valid h_lt_consInt
  rw [alphaK_consInt n hn, alphaK_consInt n hn] at h
  exact Nat.lt_of_mul_lt_mul_left h

/-! ## Permutation invariance of `αₖ` -/

/-- `αₖ` is invariant under permuting slots: `αₖ v = αₖ (v ∘ σ)`. -/
theorem alphaK_perm {k : ℕ} (v : FracTuple k) (σ : Equiv.Perm (Fin k)) :
    alphaK v = alphaK (v ∘ σ) :=
  indepNum_bigStrongProduct_perm
    (fun i : Fin k => fractionGraph (v i).1 (v i).2) σ

/-- `αₖ v ≥ 1` for any `v : FracTuple k`. The bigStrongProduct has at least
    one vertex (the constant `0` tuple), giving a singleton independent set. -/
private lemma alphaK_pos {k : ℕ} (v : FracTuple k) : 0 < alphaK v := by
  classical
  unfold alphaK
  set G := bigStrongProduct (fun i : Fin k => fractionGraph ((v i).1 : ℕ) ((v i).2 : ℕ))
    with hG
  let x : ∀ i : Fin k, ZMod ((v i).1 : ℕ) := fun _ => 0
  have hsing : G.IsIndepSet (({x} : Finset _) : Set _) := by
    rw [SimpleGraph.IsIndepSet, Set.Pairwise]
    intro a ha b hb _
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
    exact G.loopless.irrefl x
  have hcard : ({x} : Finset _).card = 1 := Finset.card_singleton x
  have hle : ({x} : Finset _).card ≤ G.indepNum := hsing.card_le_indepNum
  omega

/-- `(v ∘ σ).toRat i = v.toRat (σ i)` definitionally. -/
@[simp] lemma FracTuple.toRat_comp {k : ℕ} (v : FracTuple k)
    (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    FracTuple.toRat (v ∘ σ) i = FracTuple.toRat v (σ i) := rfl

/-! ## `lePermK` / `ltPermK` are invariant under perming either side -/

lemma lePermK_perm_right {k : ℕ} {u v : FracTuple k} (σ : Equiv.Perm (Fin k)) :
    lePermK u (v ∘ σ) ↔ lePermK u v := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨τ * σ.symm, fun i => ?_⟩
    have h := hτ (σ.symm i)
    simpa [Equiv.Perm.mul_apply, σ.apply_symm_apply] using h
  · rintro ⟨τ, hτ⟩
    refine ⟨τ * σ, fun i => ?_⟩
    have h := hτ (σ i)
    simpa [Equiv.Perm.mul_apply] using h

lemma lePermK_perm_left {k : ℕ} {u v : FracTuple k} (σ : Equiv.Perm (Fin k)) :
    lePermK (u ∘ σ) v ↔ lePermK u v := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨σ * τ, fun i => ?_⟩
    have h := hτ i
    simpa [Equiv.Perm.mul_apply] using h
  · rintro ⟨τ, hτ⟩
    refine ⟨σ.symm * τ, fun i => ?_⟩
    have h := hτ i
    simpa [Equiv.Perm.mul_apply, σ.apply_symm_apply] using h

lemma ltPermK_perm_right {k : ℕ} {u v : FracTuple k} (σ : Equiv.Perm (Fin k)) :
    ltPermK u (v ∘ σ) ↔ ltPermK u v := by
  unfold ltPermK
  rw [lePermK_perm_right, lePermK_perm_left]

/-- **C3.5: perm symmetry of `IsDiscontinuityK`.** -/
theorem isDiscontinuityK_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) {v : FracTuple k} :
    IsDiscontinuityK v ↔ IsDiscontinuityK (v ∘ σ) := by
  unfold IsDiscontinuityK
  rw [show alphaK v = alphaK (v ∘ σ) from alphaK_perm v σ]
  refine forall_congr' fun u => ?_
  refine imp_congr_right fun _ => ?_
  rw [ltPermK_perm_right]

/-! ## `αₖ` monotonicity under `lePermK` (paper line 2740 implication) -/

/-- Per-slot cohom from rational comparison `(u i).toRat ≤ (v i).toRat`. -/
private lemma cohom_fractionGraph_of_toRat_le {p1 q1 p2 q2 : ℕ+}
    (h2q1 : 2 * q1 ≤ p1) (h2q2 : 2 * q2 ≤ p2)
    (h : ((p1 : ℚ) / q1) ≤ ((p2 : ℚ) / q2)) :
    fractionGraph (p1 : ℕ) (q1 : ℕ) ≤_G fractionGraph (p2 : ℕ) (q2 : ℕ) := by
  have hq1 : (0 : ℚ) < (q1 : ℚ) := by exact_mod_cast q1.pos
  have hq2 : (0 : ℚ) < (q2 : ℚ) := by exact_mod_cast q2.pos
  rw [div_le_div_iff₀ hq1 hq2] at h
  have h_le_nat : (p1 : ℕ) * (q2 : ℕ) ≤ (p2 : ℕ) * (q1 : ℕ) := by exact_mod_cast h
  have h_v1 : 2 * (q1 : ℕ) ≤ (p1 : ℕ) := by exact_mod_cast h2q1
  have h_v2 : 2 * (q2 : ℕ) ≤ (p2 : ℕ) := by exact_mod_cast h2q2
  exact cohom_fractionGraph_monotone _ _ _ _ q1.pos h_v1 q2.pos h_v2 h_le_nat

/-- **αₖ monotonicity** (paper line 2740): `u ≤ₚ v` (with both valid) implies
    `αₖ u ≤ αₖ v`. Reduces to per-slot `fractionGraph` cohom + iterated cohom
    monotonicity + αₖ permutation invariance. -/
theorem alphaK_le_of_lePermK {k : ℕ} {u v : FracTuple k}
    (hu : ValidK u) (hv : ValidK v) (h : lePermK u v) :
    alphaK u ≤ alphaK v := by
  obtain ⟨σ, hσ⟩ := h
  rw [alphaK_perm u σ]
  -- Now goal: alphaK (u ∘ σ) ≤ alphaK v.
  -- u ∘ σ has slot i = u (σ i) with toRat ≤ v(i).toRat.
  unfold alphaK
  -- Per-slot cohom.
  have h_co : ∀ i, fractionGraph ((u ∘ σ) i).1 ((u ∘ σ) i).2 ≤_G
                   fractionGraph (v i).1 (v i).2 := by
    intro i
    have h_rat := hσ i  -- ((u (σ i)).1 : ℚ) / (u (σ i)).2 ≤ ((v i).1 : ℚ) / (v i).2
    unfold FracTuple.toRat at h_rat
    exact cohom_fractionGraph_of_toRat_le (hu (σ i)) (hv i) h_rat
  obtain ⟨F, hF⟩ := bigStrongProduct_cohom_mono h_co
  exact independenceNumber_le_of_cohomomorphism _ _ F hF

/-! ## Representation independence of `αₖ`

`αₖ` depends only on the rational values `FracTuple.toRat`, not on the
specific `(p, q)` representation. Used for "WLOG coprime" reductions. -/

theorem alphaK_eq_of_toRat_eq {k : ℕ} {u v : FracTuple k}
    (hu : ValidK u) (hv : ValidK v)
    (h_eq : ∀ i, FracTuple.toRat u i = FracTuple.toRat v i) :
    alphaK u = alphaK v := by
  have h_le_uv : lePermK u v :=
    ⟨1, fun i => by
      simp only [Equiv.Perm.coe_one, id_eq]
      exact (h_eq i).le⟩
  have h_le_vu : lePermK v u :=
    ⟨1, fun i => by
      simp only [Equiv.Perm.coe_one, id_eq]
      exact (h_eq i).symm.le⟩
  exact le_antisymm
    (alphaK_le_of_lePermK hu hv h_le_uv)
    (alphaK_le_of_lePermK hv hu h_le_vu)

/-- `ValidK` depends only on rational values: if `toRat u = toRat v` pointwise,
    then `ValidK u ↔ ValidK v`. (Validity is `2 * (v i).2 ≤ (v i).1`, which is
    equivalent to `2 ≤ toRat v i`.) -/
theorem validK_iff_of_toRat_eq {k : ℕ} {u v : FracTuple k}
    (h_eq : ∀ i, FracTuple.toRat u i = FracTuple.toRat v i) :
    ValidK u ↔ ValidK v := by
  have aux : ∀ {a b : FracTuple k}, ValidK a →
      (∀ i, FracTuple.toRat a i = FracTuple.toRat b i) → ValidK b := by
    intro a b ha h_ab i
    have hqa : (0 : ℚ) < ((a i).2 : ℚ) := by exact_mod_cast (a i).2.pos
    have hqb : (0 : ℚ) < ((b i).2 : ℚ) := by exact_mod_cast (b i).2.pos
    have h_rat_a : (2 : ℚ) ≤ FracTuple.toRat a i := toRatK_ge_two_of_valid ha i
    have h_ab_unfold : ((a i).1 : ℚ) / ((a i).2 : ℚ) = ((b i).1 : ℚ) / ((b i).2 : ℚ) := by
      have := h_ab i; unfold FracTuple.toRat at this; exact this
    have h_rat_b : (2 : ℚ) ≤ ((b i).1 : ℚ) / ((b i).2 : ℚ) := by
      rw [← h_ab_unfold]; have := h_rat_a; unfold FracTuple.toRat at this; exact this
    rw [le_div_iff₀ hqb] at h_rat_b
    exact_mod_cast h_rat_b
  exact ⟨fun hu => aux hu h_eq, fun hv => aux hv (fun i => (h_eq i).symm)⟩

/-- `lePermK` depends only on rational values: invariance on both sides. -/
theorem lePermK_iff_of_toRat_eq {k : ℕ} {u v u' v' : FracTuple k}
    (h_u : ∀ i, FracTuple.toRat u i = FracTuple.toRat u' i)
    (h_v : ∀ i, FracTuple.toRat v i = FracTuple.toRat v' i) :
    lePermK u v ↔ lePermK u' v' := by
  unfold lePermK
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun i => by rw [← h_u (σ i), ← h_v i]; exact hσ i⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun i => by rw [h_u (σ i), h_v i]; exact hσ i⟩

/-- `IsDiscontinuityK` depends only on rational values: if `toRat u = toRat v`
    pointwise and `u` is valid, then `IsDiscontinuityK u ↔ IsDiscontinuityK v`.
    Used to reduce the general (not-necessarily-coprime) case to the coprime
    case in `theorem_6_9`. -/
theorem isDiscontinuityK_iff_of_toRat_eq {k : ℕ} {u v : FracTuple k}
    (hu : ValidK u)
    (h_eq : ∀ i, FracTuple.toRat u i = FracTuple.toRat v i) :
    IsDiscontinuityK u ↔ IsDiscontinuityK v := by
  have hv : ValidK v := (validK_iff_of_toRat_eq h_eq).mp hu
  unfold IsDiscontinuityK
  refine forall_congr' fun w => ?_
  refine imp_congr Iff.rfl ?_
  have h_lt_iff : ltPermK w u ↔ ltPermK w v := by
    unfold ltPermK
    refine and_congr ?_ (not_congr ?_)
    · exact lePermK_iff_of_toRat_eq (fun _ => rfl) h_eq
    · exact lePermK_iff_of_toRat_eq h_eq (fun _ => rfl)
  refine imp_congr h_lt_iff ?_
  rw [alphaK_eq_of_toRat_eq hu hv h_eq]

/-! ## Hales bound at slot 0 (and at any slot via permutation invariance) -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Hales-at-slot 0: `α_{k+1}(u) ≤ ⌊u(0).toRat * α_k(Fin.tail u)⌋`. -/
private lemma alphaK_le_hales_slot0 {k : ℕ} {u : FracTuple (k + 1)} (hu : ValidK u) :
    alphaK u ≤ ⌊((u 0).1 : ℝ) / ((u 0).2 : ℝ) *
      (alphaK (Fin.tail u) : ℝ)⌋₊ := by
  obtain ⟨cliques, weights, hclique, hpos, hcover, hsum⟩ :=
    fractionalCliqueCover_fractionGraph (u 0).1 (u 0).2 (u 0).2.pos (hu 0)
  unfold alphaK
  rw [SimpleGraph.independenceNumber_iso
    (bigStrongProduct_succ_iso (fun i : Fin (k + 1) => fractionGraph (u i).1 (u i).2))]
  exact hales_inequality (fractionGraph (u 0).1 (u 0).2)
    (bigStrongProduct (fun i : Fin k => fractionGraph (u i.succ).1 (u i.succ).2))
    cliques weights hclique hpos hcover (((u 0).1 : ℝ) / ((u 0).2 : ℝ)) hsum

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Hales bound at slot `σ 0` of `u`, via permutation invariance:
    `α_{k+1}(u) ≤ ⌊u(σ 0).toRat * α_k(fun i => u (σ i.succ))⌋`. -/
private lemma alphaK_le_hales_at_perm {k : ℕ} {u : FracTuple (k + 1)} (hu : ValidK u)
    (σ : Equiv.Perm (Fin (k + 1))) :
    alphaK u ≤ ⌊((u (σ 0)).1 : ℝ) / ((u (σ 0)).2 : ℝ) *
      (alphaK (fun i : Fin k => u (σ i.succ)) : ℝ)⌋₊ := by
  rw [alphaK_perm u σ]
  exact alphaK_le_hales_slot0 (fun i => hu (σ i))

/-! ## Forward direction of `lem:disc-integer`

If `v : FracTuple k` is an `α_k`-discontinuity and `n ∈ ℕ` with `n ≥ 2`, then
`consInt n v : FracTuple (k+1)` is an `α_{k+1}`-discontinuity.

Proof outline (paper §6 line 2759–2766): take any valid `u' <ₚ consInt n v`
with alignment `σ`. Let `v' j := u' (σ j.succ)`; then `u' ≤ₚ consInt n v'` and
`v' ≤ₚ v`. Case-split on whether `v <ₚ v'` (excluded by definition of `lePermK`)
or `v ≤ₚ v'`:
- Case A (`¬ v ≤ₚ v'`): `v' <ₚ v`, so `α_k v' < α_k v` by `hv_disc`. Multiply
  by `n` and use the value formula.
- Case B (`v ≤ₚ v'`): `α_k v' = α_k v`. The strict inequality forces
  `u'(σ 0).toRat < n` (else multiset of `u'` matches `consInt n v`). Apply
  `alphaK_le_hales_at_perm` to get `α_{k+1}(u') ≤ ⌊u'(σ 0).toRat · α_k v⌋`,
  which is `< n · α_k v` since `u'(σ 0).toRat < n` and `α_k v` is integer. -/

/-- Forward direction of `lem:disc-integer`. -/
theorem isDiscontinuityK_consInt {k : ℕ} (n : ℕ+) (hn : 2 ≤ n) {v : FracTuple k}
    (hv_valid : ValidK v) (hv_disc : IsDiscontinuityK v) :
    IsDiscontinuityK (consInt n v) := by
  intro u' hu'_valid h_lt
  obtain ⟨⟨σ, hσ⟩, hno_back⟩ := h_lt
  -- v' j := u'(σ j.succ). Defeq to a `fun` so equalities go through.
  set v' : FracTuple k := fun j => u' (σ j.succ) with hv'_def
  have hv'_valid : ValidK v' := fun j => hu'_valid (σ j.succ)
  -- v' ≤ₚ v via id perm: v'(j).toRat ≤ v(j).toRat from hσ j.succ.
  have hv'_le_v : lePermK v' v := by
    refine ⟨1, fun j => ?_⟩
    have h := hσ j.succ
    rwa [consInt_toRat_succ] at h
  -- u' ≤ₚ consInt n v' via σ.
  have hu'_le_cInv' : lePermK u' (consInt n v') := by
    refine ⟨σ, fun i => ?_⟩
    cases i using Fin.cases with
    | zero =>
      rw [consInt_toRat_zero]
      have h := hσ 0
      rwa [consInt_toRat_zero] at h
    | succ j =>
      rw [consInt_toRat_succ]
      exact le_refl _
  have h_mono : alphaK u' ≤ alphaK (consInt n v') :=
    alphaK_le_of_lePermK hu'_valid (consInt_validK n hn hv'_valid) hu'_le_cInv'
  rw [alphaK_consInt n hn] at h_mono
  rw [alphaK_consInt n hn]
  -- Goal: alphaK u' < n * alphaK v.
  by_cases h_back : lePermK v v'
  · -- Case B: v ≡ₚ v' (multiset-wise). αₖ v = αₖ v'.
    have hv_le_v' : alphaK v ≤ alphaK v' :=
      alphaK_le_of_lePermK hv_valid hv'_valid h_back
    have hv'_le_α : alphaK v' ≤ alphaK v :=
      alphaK_le_of_lePermK hv'_valid hv_valid hv'_le_v
    have hα_eq : alphaK v' = alphaK v := le_antisymm hv'_le_α hv_le_v'
    -- v'(j).toRat = v(j).toRat (pointwise) by sum/multiset argument.
    have hv'_eq_v : ∀ j, FracTuple.toRat v' j = FracTuple.toRat v j := by
      obtain ⟨ρ, hρ⟩ := h_back
      -- h_le : v'(j).toRat ≤ v(j).toRat (direct from hσ at j.succ).
      have h_le : ∀ j, FracTuple.toRat v' j ≤ FracTuple.toRat v j := fun j => by
        have h := hσ j.succ
        rwa [consInt_toRat_succ] at h
      -- h_perm : v(ρ j).toRat ≤ v'(j).toRat.
      have h_perm : ∀ j, FracTuple.toRat v (ρ j) ≤ FracTuple.toRat v' j := hρ
      -- Sum equality: sum_j v(ρ j) = sum_j v(j) (ρ bijection).
      have h_sum_eq : (∑ j, FracTuple.toRat v (ρ j)) = (∑ j, FracTuple.toRat v j) :=
        Finset.sum_equiv ρ (by simp) (fun _ _ => rfl)
      have h_sum_le_v' : (∑ j, FracTuple.toRat v (ρ j)) ≤ (∑ j, FracTuple.toRat v' j) :=
        Finset.sum_le_sum (fun j _ => h_perm j)
      have h_sum_v'_le : (∑ j, FracTuple.toRat v' j) ≤ (∑ j, FracTuple.toRat v j) :=
        Finset.sum_le_sum (fun j _ => h_le j)
      have h_sum_eq_v' : (∑ j, FracTuple.toRat v' j) = (∑ j, FracTuple.toRat v j) := by
        linarith
      intro j
      have hj := h_le j
      by_contra hne
      have hlt : FracTuple.toRat v' j < FracTuple.toRat v j := lt_of_le_of_ne hj hne
      have hsum_lt : (∑ j, FracTuple.toRat v' j) < (∑ j, FracTuple.toRat v j) :=
        Finset.sum_lt_sum (fun j' _ => h_le j') ⟨j, Finset.mem_univ j, hlt⟩
      linarith
    -- u'(σ 0).toRat < n (else multiset of u'(σ ·) matches consInt n v, giving back-perm).
    have hσ0_lt_n : ((u' (σ 0)).1 : ℚ) / ((u' (σ 0)).2 : ℚ) < (n : ℚ) := by
      by_contra h_ge
      push_neg at h_ge
      apply hno_back
      -- For slot 0: u'(σ 0).toRat = n.
      have h_eq_0 : FracTuple.toRat u' (σ 0) = (n : ℚ) := by
        have h := hσ 0
        rw [consInt_toRat_zero] at h
        unfold FracTuple.toRat at h ⊢
        linarith
      -- For all i, u'(σ i).toRat = (consInt n v)(i).toRat.
      have h_eq_all : ∀ i, FracTuple.toRat u' (σ i) = (consInt n v).toRat i := by
        intro i
        cases i using Fin.cases with
        | zero =>
          rw [consInt_toRat_zero]
          exact h_eq_0
        | succ j =>
          rw [consInt_toRat_succ]
          -- v'(j) = u'(σ j.succ) by definition; v'(j).toRat = v(j).toRat by hv'_eq_v.
          change FracTuple.toRat v' j = FracTuple.toRat v j
          exact hv'_eq_v j
      -- Construct (consInt n v) ≤ₚ u' via σ.symm: pointwise equality.
      refine ⟨σ.symm, fun i => ?_⟩
      have h := h_eq_all (σ.symm i)
      rw [σ.apply_symm_apply] at h
      exact h.symm.le
    -- Hales at slot σ 0 + αₖ v' = αₖ v + αₖ v ≥ 1.
    have h_hales := alphaK_le_hales_at_perm hu'_valid σ
    have hα_v' : alphaK (fun i : Fin k => u' (σ i.succ)) = alphaK v := hα_eq
    rw [hα_v'] at h_hales
    -- Floor strict: ⌊u'(σ 0).toRat * αₖ v⌋ < n * αₖ v.
    have hαv_pos : (0 : ℝ) < (alphaK v : ℝ) := by exact_mod_cast alphaK_pos v
    have h_real : ((u' (σ 0)).1 : ℝ) / ((u' (σ 0)).2 : ℝ) < (n : ℝ) := by
      have h2pos_r : (0 : ℝ) < ((u' (σ 0)).2 : ℝ) := by exact_mod_cast (u' (σ 0)).2.pos
      have h2pos_q : (0 : ℚ) < ((u' (σ 0)).2 : ℚ) := by exact_mod_cast (u' (σ 0)).2.pos
      rw [div_lt_iff₀ h2pos_r]
      have h := hσ0_lt_n
      rw [div_lt_iff₀ h2pos_q] at h
      exact_mod_cast h
    have h_lt_real : ((u' (σ 0)).1 : ℝ) / ((u' (σ 0)).2 : ℝ) * (alphaK v : ℝ) <
        ((n : ℕ) * alphaK v : ℕ) := by
      push_cast
      exact mul_lt_mul_of_pos_right h_real hαv_pos
    have h_floor_lt : ⌊((u' (σ 0)).1 : ℝ) / ((u' (σ 0)).2 : ℝ) * (alphaK v : ℝ)⌋₊ <
        (n : ℕ) * alphaK v := by
      have hne : (n : ℕ) * alphaK v ≠ 0 :=
        Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp n.pos) (Nat.pos_iff_ne_zero.mp (alphaK_pos v))
      exact (Nat.floor_lt' hne).mpr h_lt_real
    omega
  · -- Case A: ¬ lePermK v v', so v' <ₚ v.
    have hv'_lt_v : ltPermK v' v := ⟨hv'_le_v, h_back⟩
    have h_v'_lt : alphaK v' < alphaK v := hv_disc v' hv'_valid hv'_lt_v
    have hn_pos : 0 < (n : ℕ) := n.pos
    calc alphaK u' ≤ (n : ℕ) * alphaK v' := h_mono
      _ < (n : ℕ) * alphaK v := Nat.mul_lt_mul_of_pos_left h_v'_lt hn_pos

/-! ## Reducing a valid `FracTuple 3` to its coprime representation -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Every valid `u : FracTuple 3` admits a coprime `u₀` with the same per-slot
    `toRat`. Shared helper for the per-case `Section6DiscontinuityK_*` files. -/
lemma exists_coprime_form (u : FracTuple 3) (hu : ValidK u) :
    ∃ u₀ : FracTuple 3, ValidK u₀ ∧
      (∀ i, FracTuple.toRat u₀ i = FracTuple.toRat u i) ∧
      (∀ i, Nat.Coprime ((u₀ i).1 : ℕ) ((u₀ i).2 : ℕ)) := by
  refine ⟨fun i =>
    let g : ℕ := Nat.gcd ((u i).1 : ℕ) ((u i).2 : ℕ);
    let p' : ℕ+ := ⟨((u i).1 : ℕ) / g,
      Nat.div_pos (Nat.le_of_dvd (u i).1.pos (Nat.gcd_dvd_left _ _))
        (Nat.gcd_pos_of_pos_left _ (u i).1.pos)⟩;
    let q' : ℕ+ := ⟨((u i).2 : ℕ) / g,
      Nat.div_pos (Nat.le_of_dvd (u i).2.pos (Nat.gcd_dvd_right _ _))
        (Nat.gcd_pos_of_pos_right _ (u i).2.pos)⟩;
    (p', q'), ?_, ?_, ?_⟩
  all_goals (intro i)
  · -- ValidK at slot i.
    set g : ℕ := Nat.gcd ((u i).1 : ℕ) ((u i).2 : ℕ) with hg_def
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (u i).1.pos
    have hg_dvd_p : g ∣ ((u i).1 : ℕ) := Nat.gcd_dvd_left _ _
    have hg_dvd_q : g ∣ ((u i).2 : ℕ) := Nat.gcd_dvd_right _ _
    have h_p_eq : ((u i).1 : ℕ) / g * g = ((u i).1 : ℕ) := Nat.div_mul_cancel hg_dvd_p
    have h_q_eq : ((u i).2 : ℕ) / g * g = ((u i).2 : ℕ) := Nat.div_mul_cancel hg_dvd_q
    have h2q : 2 * ((u i).2 : ℕ) ≤ ((u i).1 : ℕ) := by exact_mod_cast hu i
    change 2 * (((u i).2 : ℕ) / g) ≤ ((u i).1 : ℕ) / g
    have key : (2 * (((u i).2 : ℕ) / g)) * g ≤ (((u i).1 : ℕ) / g) * g := by
      rw [mul_assoc, h_p_eq, h_q_eq]; exact h2q
    exact Nat.le_of_mul_le_mul_right key hg_pos
  · -- toRat preserved.
    set g : ℕ := Nat.gcd ((u i).1 : ℕ) ((u i).2 : ℕ) with hg_def
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (u i).1.pos
    have hg_dvd_p : g ∣ ((u i).1 : ℕ) := Nat.gcd_dvd_left _ _
    have hg_dvd_q : g ∣ ((u i).2 : ℕ) := Nat.gcd_dvd_right _ _
    have h_p_eq : ((u i).1 : ℕ) / g * g = ((u i).1 : ℕ) := Nat.div_mul_cancel hg_dvd_p
    have h_q_eq : ((u i).2 : ℕ) / g * g = ((u i).2 : ℕ) := Nat.div_mul_cancel hg_dvd_q
    change ((((u i).1 : ℕ) / g : ℕ) : ℚ) / ((((u i).2 : ℕ) / g : ℕ) : ℚ) =
            ((u i).1 : ℚ) / ((u i).2 : ℚ)
    have hg_q : (g : ℚ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hg_pos
    have hq_pos_q : (((u i).2 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp (u i).2.pos
    have hq_div_pos : ((((u i).2 : ℕ) / g : ℕ) : ℚ) ≠ 0 := by
      have : 0 < ((u i).2 : ℕ) / g :=
        Nat.div_pos (Nat.le_of_dvd (u i).2.pos hg_dvd_q) hg_pos
      exact_mod_cast Nat.pos_iff_ne_zero.mp this
    rw [div_eq_div_iff hq_div_pos hq_pos_q]
    have h_p_eq_q : ((((u i).1 : ℕ) / g : ℕ) : ℚ) * g = (((u i).1 : ℕ) : ℚ) := by
      have h := h_p_eq; exact_mod_cast h
    have h_q_eq_q : ((((u i).2 : ℕ) / g : ℕ) : ℚ) * g = (((u i).2 : ℕ) : ℚ) := by
      have h := h_q_eq; exact_mod_cast h
    have hg_pos_q : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg_pos
    have hg_ne : (g : ℚ) ≠ 0 := ne_of_gt hg_pos_q
    field_simp
    have lhs_eq :
        ((((u i).1 : ℕ) / g : ℕ) : ℚ) * (((u i).2 : ℕ) : ℚ) =
        ((((u i).1 : ℕ) / g : ℕ) : ℚ) * ((((u i).2 : ℕ) / g : ℕ) : ℚ) * g := by
      rw [mul_assoc]; rw [h_q_eq_q]
    have rhs_eq :
        ((((u i).2 : ℕ) / g : ℕ) : ℚ) * (((u i).1 : ℕ) : ℚ) =
        ((((u i).2 : ℕ) / g : ℕ) : ℚ) * ((((u i).1 : ℕ) / g : ℕ) : ℚ) * g := by
      rw [mul_assoc]; rw [h_p_eq_q]
    linarith [lhs_eq, rhs_eq]
  · -- Coprime.
    change Nat.Coprime (((u i).1 : ℕ) / Nat.gcd ((u i).1 : ℕ) ((u i).2 : ℕ))
                        (((u i).2 : ℕ) / Nat.gcd ((u i).1 : ℕ) ((u i).2 : ℕ))
    exact Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left _ (u i).1.pos)

end Section6
