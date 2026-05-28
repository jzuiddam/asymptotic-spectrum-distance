/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.PSDCone

set_option linter.style.longLine false

/-!
# Semidefinite Programming on Symmetric Matrices

This file provides the SDP structure on symmetric matrices and strong duality,
following Chapter 4 of Gärtner-Matoušek "Approximation Algorithms and Semidefinite Programming".

## Main definitions

* `SDPSym` : A semidefinite program on symmetric matrices
* `SDPSym.toConeProgram` : Embedding SDP into cone program framework

## Main results

* `SDPSym.strong_duality_exists` : Strong duality for SDP
-/

namespace ConeProgramming

open scoped InnerProductSpace RealInnerProductSpace
open ContinuousLinearMap

/-! ## SDP on Symmetric Matrices (Following Gärtner-Matoušek)

This section provides the mathematically correct SDP formulation using the symmetric matrix
subspace `SymMatrix n` as defined in the book. The key advantage is that
`interior_psdSym_eq_posDef` is now a correct mathematical statement.
-/

section SDPSymmetric

open Matrix

variable (n : ℕ)

-- Use Frobenius norm and inner product for matrices
open scoped Matrix.Norms.Frobenius MatrixFrobenius


/-- A semidefinite program on symmetric matrices (following Gärtner-Matoušek).
This is the mathematically correct formulation where V = SYMn. -/
structure SDPSym (n m : ℕ) where
  /-- Constraint matrices A₁, ..., Aₘ (symmetric by construction) -/
  A : Fin m → SymMatrix n
  /-- Right-hand side b -/
  b : Fin m → ℝ
  /-- Objective matrix C (symmetric by construction) -/
  C : SymMatrix n

namespace SDPSym

/-- The Frobenius inner product on symmetric matrices: Tr(XᵀY) = Tr(XY). -/
def frobeniusInnerSym {n : ℕ} (X Y : SymMatrix n) : ℝ :=
  Matrix.trace (X.val.transpose * Y.val)

/-- The linear operator A: SYMₙ → ℝᵐ defined by A(X)ᵢ = Tr(AᵢᵀX). -/
def linearOp {n m : ℕ} (P : SDPSym n m) (X : SymMatrix n) : Fin m → ℝ :=
  fun i => frobeniusInnerSym (P.A i) X

/-- Sum of symmetric matrices is symmetric. -/
private theorem isSymm_sum {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (hA : ∀ i, (A i).IsSymm) : (∑ i, c i • A i).IsSymm := by
  apply Finset.sum_induction
  · intro a b ha hb
    exact ha.add hb
  · exact Matrix.isSymm_zero
  · intro i _
    exact Matrix.IsSymm.smul (hA i) (c i)

/-- The adjoint of the linear operator: Aᵀ(y) = Σᵢ yᵢAᵢ. -/
def adjointOp {n m : ℕ} (P : SDPSym n m) (y : Fin m → ℝ) : SymMatrix n :=
  ⟨∑ i, y i • (P.A i).val, isSymm_sum (fun i => (P.A i).val) y (fun i => (P.A i).prop)⟩

/-- Feasibility: X ⪰ 0 and A(X) = b. -/
def isFeasible {n m : ℕ} (P : SDPSym n m) (X : SymMatrix n) : Prop :=
  X.val.PosSemidef ∧ P.linearOp X = P.b

/-- Strict feasibility (interior point): X ≻ 0 and A(X) = b. -/
def isStrictlyFeasible {n m : ℕ} (P : SDPSym n m) (X : SymMatrix n) : Prop :=
  X.val.PosDef ∧ P.linearOp X = P.b

/-- The objective value Tr(CᵀX). -/
def objective {n m : ℕ} (P : SDPSym n m) (X : SymMatrix n) : ℝ :=
  frobeniusInnerSym P.C X

/-- Dual feasibility: y ∈ ℝᵐ with Σᵢ yᵢAᵢ - C ⪰ 0. -/
def isDualFeasible {n m : ℕ} (P : SDPSym n m) (y : Fin m → ℝ) : Prop :=
  ((P.adjointOp y).val - P.C.val).PosSemidef

/-- Dual objective value bᵀy. -/
def dualObjective {n m : ℕ} (P : SDPSym n m) (y : Fin m → ℝ) : ℝ :=
  ∑ i, P.b i * y i

/-! ### SDPSym to ConeProgram Translation -/

/-- The linear operator A as a LinearMap on SymMatrix. -/
def linearOpAsLinearMap {n m : ℕ} (P : SDPSym n m) :
    SymMatrix n →ₗ[ℝ] (Fin m → ℝ) where
  toFun := P.linearOp
  map_add' := fun X Y => by
    ext i
    simp only [linearOp, frobeniusInnerSym, Pi.add_apply]
    have h : (X + Y : SymMatrix n).val = X.val + Y.val := rfl
    rw [h, Matrix.mul_add, Matrix.trace_add]
  map_smul' := fun c X => by
    ext i
    simp only [linearOp, frobeniusInnerSym, Pi.smul_apply, RingHom.id_apply]
    have h : (c • X : SymMatrix n).val = c • X.val := rfl
    rw [h, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- The linear operator A as a ContinuousLinearMap (automatic in finite dimensions). -/
noncomputable def toCLM {n m : ℕ} (P : SDPSym n m) :
    SymMatrix n →L[ℝ] (Fin m → ℝ) :=
  P.linearOpAsLinearMap.toContinuousLinearMap

/-- The PiLp equivalence. -/
noncomputable def piLpEquivSym (m : ℕ) :
    (Fin m → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm

/-- The linear operator A as a ContinuousLinearMap to EuclideanSpace. -/
noncomputable def toCLM' {n m : ℕ} (P : SDPSym n m) :
    SymMatrix n →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (piLpEquivSym m).toContinuousLinearMap.comp P.toCLM

/-- The adjoint of `toCLM'` as a continuous linear map.

v4.29 update: `(P.toCLM').adjoint` (i.e. `ContinuousLinearMap.adjoint`) cannot have its
`CompleteSpace ↥(SymMatrix n)` instance synthesized in typeclass elaboration here, because the
topology Lean picks for `↥(SymMatrix n)` (the `Subtype` topology `instTopologicalSpaceSubtype`)
does not unify with the topology that `adjoint` expects (the norm-derived
`PseudoMetricSpace.toUniformSpace.toTopologicalSpace`). These two topologies are definitionally
equal but no longer syntactically reconciled by v4.29's stricter instance unification.

We route through `LinearMap.adjoint` (which only needs `FiniteDimensional`, not `CompleteSpace`,
and so is unaffected) and lift back to a `ContinuousLinearMap`. -/
noncomputable def adjointCLM {n m : ℕ} (P : SDPSym n m) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] SymMatrix n :=
  P.toCLM'.toLinearMap.adjoint.toContinuousLinearMap

/-- Convert an SDPSym to a ConeProgram on SymMatrix.

This is the mathematically correct reduction:
- V = SymMatrix n (symmetric matrices with Frobenius inner product)
- W = EuclideanSpace ℝ (Fin m)
- K = psdConeSym n (PSD cone on symmetric matrices)
- L = trivialCone
- interior(K) = {X | X.val.PosDef} (CORRECT!)
-/
noncomputable def toConeProgram {n m : ℕ} (P : SDPSym n m) :
    ConeProgramming.ConeProgram (V := SymMatrix n) (W := EuclideanSpace ℝ (Fin m)) where
  K := psdConeSym n
  L := trivialCone (W := EuclideanSpace ℝ (Fin m))
  A := P.toCLM'
  b := piLpEquivSym m P.b
  c := P.C

/-! ### SDPSym Translation Lemmas -/

theorem toCLM'_eq {n m : ℕ} (P : SDPSym n m) (X : SymMatrix n) :
    P.toCLM' X = piLpEquivSym m (P.linearOp X) := rfl

/-- SDPSym feasibility translates to ConeProgram feasibility. -/
theorem toConeProgram_isFeasible {n m : ℕ} (P : SDPSym n m) (X : SymMatrix n) :
    P.toConeProgram.isFeasible X ↔ P.isFeasible X := by
  simp only [ConeProgram.isFeasible, toConeProgram, isFeasible]
  constructor
  · intro ⟨hX_psd, hconstr⟩
    constructor
    · exact hX_psd
    · rw [mem_trivialCone] at hconstr
      have h : P.toCLM' X = piLpEquivSym m P.b := eq_of_sub_eq_zero hconstr |>.symm
      rw [toCLM'_eq] at h
      exact (piLpEquivSym m).injective h
  · intro ⟨hX_psd, hconstr⟩
    constructor
    · exact hX_psd
    · rw [mem_trivialCone, sub_eq_zero]
      change (piLpEquivSym m) P.b = piLpEquivSym m (P.linearOp X)
      rw [hconstr]

/-- SDPSym strict feasibility gives a Slater point for the ConeProgram.
This uses the CORRECT interior characterization `interior_psdSym_eq_posDef`. -/
theorem toConeProgram_isSlaterPointEq {n m : ℕ} (P : SDPSym n m)
    (X : SymMatrix n) (h : P.isStrictlyFeasible X) :
    P.toConeProgram.isSlaterPointEq X := by
  simp only [ConeProgram.isSlaterPointEq, toConeProgram]
  constructor
  · -- X ∈ interior (psdConeSym n) - this is now CORRECT!
    exact @PosDef.mem_interior_psdSym n X h.1
  · -- A X = b
    change piLpEquivSym m (P.linearOp X) = piLpEquivSym m P.b
    rw [h.2]

/-- SDPSym objective equals ConeProgram objective. -/
theorem toConeProgram_objective {n m : ℕ} (P : SDPSym n m) (X : SymMatrix n) :
    P.toConeProgram.objective X = P.objective X := rfl

/-- The dual cone of the trivial cone is the whole space. -/
theorem toConeProgram_dualCone_L_univ {n m : ℕ} (P : SDPSym n m) :
    ∀ y : EuclideanSpace ℝ (Fin m),
      y ∈ (dualCone (P.toConeProgram.L : Set (EuclideanSpace ℝ (Fin m))) : Set _) := by
  intro y
  simp only [toConeProgram]
  exact mem_dualCone_trivialCone y

/-- SDP has a feasible point implies ConeProgram has a feasible point. -/
theorem toConeProgram_hasFeasible {n m : ℕ} (P : SDPSym n m)
    (hfeas : ∃ X, P.isFeasible X) :
    ∃ x, P.toConeProgram.isFeasible x := by
  obtain ⟨X, hX⟩ := hfeas
  exact ⟨X, (toConeProgram_isFeasible P X).mpr hX⟩

/-- Bounded objective translates between SDPSym and ConeProgram. -/
theorem toConeProgram_bddAbove {n m : ℕ} (P : SDPSym n m)
    (hFinite : BddAbove (Set.range fun (X : {X // P.isFeasible X}) => P.objective X.val)) :
    BddAbove (Set.range fun (X : {X // P.toConeProgram.isFeasible X}) =>
      P.toConeProgram.objective X.val) := by
  obtain ⟨M, hM⟩ := hFinite
  use M
  intro v ⟨⟨X, hX_feas⟩, hv⟩
  simp only at hv
  rw [← hv, toConeProgram_objective]
  apply hM
  use ⟨X, (toConeProgram_isFeasible P X).mp hX_feas⟩

/-! ### SDPSym Dual Translation Lemmas -/

/-- The adjoint formula for SDPSym: Σᵢ yᵢ * ⟨Aᵢ, X⟩ = ⟨Σᵢ yᵢAᵢ, X⟩ for Frobenius inner product. -/
theorem adjoint_eqSym {n m : ℕ} (P : SDPSym n m) (y : Fin m → ℝ) (X : SymMatrix n) :
    ∑ i, y i * frobeniusInnerSym (P.A i) X = frobeniusInnerSym (P.adjointOp y) X := by
  simp only [adjointOp, frobeniusInnerSym]
  rw [Matrix.transpose_sum, Finset.sum_mul]
  simp only [Matrix.transpose_smul, Matrix.smul_mul]
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul]

/-- The adjoint of toCLM' equals adjointOp after piLpEquiv translation.
This is the key formula: A*(y') = Σᵢ yᵢAᵢ where y = piLpEquivSym.symm y'.

v4.29: we state this for `P.adjointCLM` (the LinearMap-based wrapper) instead of
`(P.toCLM').adjoint`. See the docstring on `adjointCLM` for why. -/
theorem toCLM'_adjoint_apply {n m : ℕ} (P : SDPSym n m)
    (y' : EuclideanSpace ℝ (Fin m)) :
    P.adjointCLM y' = P.adjointOp ((piLpEquivSym m).symm y') := by
  apply ext_inner_right ℝ
  intro X
  -- adjointCLM unfolds to (LinearMap.adjoint ...) so we use LinearMap.adjoint_inner_left
  show ⟪P.toCLM'.toLinearMap.adjoint y', X⟫_ℝ = _
  rw [LinearMap.adjoint_inner_left]
  show ⟪y', P.toCLM' X⟫_ℝ = _
  rw [toCLM'_eq, PiLp.inner_apply]
  have h1 : ∀ i, (piLpEquivSym m (P.linearOp X)).ofLp i = P.linearOp X i := fun _ => rfl
  -- v4.29: `RCLike.inner_apply` no longer reduces real ⟪·, ·⟫_ℝ; reduce by hand to a product.
  simp_rw [h1, show ∀ (a b : ℝ), ⟪a, b⟫_ℝ = a * b from fun _ _ => mul_comm _ _]
  -- Goal: ∑ x, y'.ofLp x * P.linearOp X x = ⟪P.adjointOp ((piLpEquivSym m).symm y'), X⟫
  have hsum : (∑ i, y'.ofLp i * P.linearOp X i) =
          ∑ i, ((piLpEquivSym m).symm y') i * frobeniusInnerSym (P.A i) X := by
    apply Finset.sum_congr rfl; intro i _
    simp only [linearOp, frobeniusInnerSym]; rfl
  rw [hsum]
  exact P.adjoint_eqSym ((piLpEquivSym m).symm y') X

/-- Helper: vecMulVec v v is PSD for real vectors. -/
private theorem posSemidef_vecMulVec_self (v : Fin n → ℝ) : (Matrix.vecMulVec v v).PosSemidef := by
  have h : Star.star v = v := by ext i; simp [Star.star]
  rw [← h]
  exact Matrix.posSemidef_vecMulVec_star_self v

/-- The trace formula: Tr(vvᵀ · X) = vᵀXv = dotProduct v (X.mulVec v). -/
private theorem trace_vecMulVec_mul (v : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace ((Matrix.vecMulVec v v)ᵀ * X) = dotProduct v (X.mulVec v) := by
  simp only [Matrix.vecMulVec, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Self-duality of psdConeSym (membership characterization).
This follows from the self-duality of the PSD cone on full matrices.

v4.29: stated as a membership iff (rather than the ProperCone-valued equality
`dualCone (psdConeSym n : Set _) = psdConeSym n`) because the latter triggers
the v4.29 `CompleteSpace ↥(SymMatrix n)` synthesis failure documented on
`adjointCLM`. The proof content is unchanged.

**Proof (Gärtner-Matoušek Lemma 4.7.5):**
- (⊇) If X ⪰ 0 and Y ⪰ 0, then ⟨Y, X⟩ = Tr(YᵀX) ≥ 0 (inner product of PSD matrices is nonneg)
- (⊆) If ⟨Y, X⟩ ≥ 0 for all Y ⪰ 0, take Y = vvᵀ (rank-1 PSD matrix) to show ⟨v, Xv⟩ ≥ 0 for all v -/
theorem psdConeSym_self_dual_mem (X : SymMatrix n) :
    (∀ Y ∈ (psdConeSym n : Set (SymMatrix n)), 0 ≤ ⟪Y, X⟫_ℝ) ↔ X ∈ psdConeSym n := by
  simp only [SetLike.mem_coe, mem_psdConeSym]
  constructor
  · -- dualCone ⊆ psdConeSym: X ∈ dual means ⟪Y, X⟫ ≥ 0 for all Y ⪰ 0 implies X ⪰ 0
    intro hX
    -- Use rank-1 test matrices vvᵀ to show ⟨v, Xv⟩ ≥ 0 for all v
    rw [Matrix.PosSemidef]
    constructor
    · exact X.prop
    · intro v
      -- Use the coerced function w = ⇑v : Fin n → ℝ
      let w : Fin n → ℝ := ⇑v
      -- Build rank-1 matrix Y = wwᵀ which is PSD
      let Y : SymMatrix n := ⟨vecMulVec w w, isSymm_vecMulVec (n := n) w⟩
      have hY : Y ∈ psdConeSym n := by
        rw [mem_psdConeSym]
        exact posSemidef_vecMulVec_self (n := n) w
      -- Apply hX to get ⟪Y, X⟫ ≥ 0
      have h := hX Y hY
      -- Use trace_vecMulVec_mul: ⟪Y, X⟫ = Tr(Yᵀ * X.val) = w ⬝ᵥ (X.val *ᵥ w)
      simp only [inner, Y, MatrixFrobenius.traceInnerDef, Submodule.coe_subtype] at h
      rw [trace_vecMulVec_mul (n := n)] at h
      -- h : 0 ≤ w ⬝ᵥ (X.val *ᵥ w)
      -- Convert dotProduct to Finsupp.sum form
      have hconv : w ⬝ᵥ (X.val *ᵥ w) = v.sum fun i xi => v.sum fun j xj => star xi * X.val i j * xj := by
        simp only [dotProduct, mulVec, star_trivial, w]
        rw [Finsupp.sum_fintype v _ (by intro i; simp)]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finsupp.sum_fintype v _ (by intro j; simp)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [← hconv]
      exact h
  · -- psdConeSym ⊆ dualCone: X ⪰ 0 means ⟪Y, X⟫ ≥ 0 for all Y ⪰ 0
    intro hX Y hY
    simp only [inner]
    exact psd_inner_nonneg hY hX

/-- ConeProgram dual feasibility translates to SDPSym dual feasibility.

Uses `psdConeSym_self_dual_mem` and `toCLM'_adjoint_apply` to translate between formulations. -/
theorem toConeProgram_isDualFeasible {n m : ℕ} (P : SDPSym n m)
    (y' : EuclideanSpace ℝ (Fin m)) (h : P.toConeProgram.isDualFeasible y') :
    P.isDualFeasible ((piLpEquivSym m).symm y') := by
  unfold ConeProgram.isDualFeasible at h
  obtain ⟨_, h_dual⟩ := h
  simp only [toConeProgram] at h_dual
  unfold isDualFeasible
  -- Use the adjoint formula
  have hadj := toCLM'_adjoint_apply P y'
  -- h_dual : (adjoint P.toCLM') y' - P.C ∈ dualCone(psdConeSym n)
  -- We need: P.adjointOp ((piLpEquivSym m).symm y') - P.C is PSD
  -- Use psdConeSym_self_dual_mem to convert membership in dualCone ↔ PSD-ness
  have h_in_psd : P.adjointOp ((piLpEquivSym m).symm y') - P.C ∈
      (psdConeSym n : Set (SymMatrix n)) := by
    apply (psdConeSym_self_dual_mem n _).mp
    intro Y hY
    -- h_dual via `mem_dualCone` gives ⟪Y, (P.toCLM').adjoint y' - P.C⟫ ≥ 0 ;
    -- rewrite (P.toCLM').adjoint y' = P.adjointCLM y' = P.adjointOp ((piLpEquivSym m).symm y')
    have := (mem_dualCone (K := (psdConeSym n : Set (SymMatrix n))) (y := _)).mp h_dual Y hY
    -- `this : 0 ≤ ⟪Y, (P.toCLM').adjoint y' - P.C⟫_ℝ`
    -- substitute via toCLM'_adjoint_apply
    rwa [show (P.toCLM').adjoint y' = P.adjointCLM y' from rfl, hadj] at this
  simp only [SetLike.mem_coe, mem_psdConeSym] at h_in_psd
  exact h_in_psd

/-- ConeProgram dual objective equals SDPSym dual objective after translation. -/
theorem toConeProgram_dualObjective {n m : ℕ} (P : SDPSym n m)
    (y' : EuclideanSpace ℝ (Fin m)) :
    P.toConeProgram.dualObjective y' = P.dualObjective ((piLpEquivSym m).symm y') := by
  simp only [ConeProgram.dualObjective, toConeProgram, SDPSym.dualObjective]
  -- Goal: ⟪piLpEquivSym m P.b, y'⟫_ℝ = ∑ i, P.b i * (piLpEquivSym m).symm y' i
  rw [PiLp.inner_apply]
  congr 1
  ext i
  -- v4.29: `RCLike.inner_apply` no longer reduces real ⟪·, ·⟫_ℝ; reduce by hand.
  rw [show ∀ (a b : ℝ), ⟪(a:ℝ), b⟫_ℝ = a * b from fun _ _ => mul_comm _ _]
  -- The key is that piLpEquivSym and its inverse preserve values
  simp only [piLpEquivSym]
  -- ((equiv).symm P.b) i = P.b i for WithLp equivalence
  -- y' i = (equiv.symm.symm y') i for WithLp equivalence
  have h1 : ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm P.b) i = P.b i := rfl
  have h2 : ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.symm y') i = y' i := rfl
  rw [h1, h2]

/-- SDPSym dual feasibility translates to ConeProgram dual feasibility.

Uses `psdConeSym_self_dual_mem` and `toCLM'_adjoint_apply` to translate between formulations. -/
theorem toConeProgram_isDualFeasible_rev {n m : ℕ} (P : SDPSym n m)
    (y : Fin m → ℝ) (h : P.isDualFeasible y) :
    P.toConeProgram.isDualFeasible (piLpEquivSym m y) := by
  unfold ConeProgram.isDualFeasible
  constructor
  · -- piLpEquivSym m y ∈ dualCone(trivialCone) = Set.univ
    exact mem_dualCone_trivialCone _
  · -- P.toCLM'.adjoint (piLpEquivSym m y) - P.C ∈ dualCone(psdConeSym)
    simp only [toConeProgram]
    -- Use the adjoint formula with round-trip through piLpEquivSym
    have hadj : (P.toCLM').adjoint (piLpEquivSym m y) = P.adjointOp y := by
      have h1 := toCLM'_adjoint_apply P (piLpEquivSym m y)
      simp only [piLpEquivSym, ContinuousLinearEquiv.symm_apply_apply] at h1
      -- h1 has adjointCLM (= toLinearMap.adjoint.toContinuousLinearMap) on LHS;
      -- `(P.toCLM').adjoint` is the CLM-adjoint, defeq to the LM-adjoint lifted back.
      exact h1
    rw [hadj]
    -- Need: adjointOp y - P.C ∈ dualCone(psdConeSym).
    -- By psdConeSym_self_dual_mem: equivalent to "⟪Y, _⟫ ≥ 0 for all Y ⪰ 0".
    rw [SetLike.mem_coe, mem_dualCone]
    intro Y hY
    -- ⟪Y, adjointOp y - P.C⟫ ≥ 0 by psd_inner_nonneg
    exact psd_inner_nonneg
      ((mem_psdConeSym (n := n) (A := Y)).mp hY) h

/-! ### SDPSym Strong Duality -/

/-- Strong duality for SDPSym.

This is the mathematically correct formulation using SymMatrix.
The key insight is that `toConeProgram_isSlaterPointEq` now uses the
CORRECT interior characterization `interior_psdSym_eq_posDef`. -/
theorem strong_duality_exists {n m : ℕ} (P : SDPSym n m)
    (hfeas : ∃ X, P.isFeasible X)
    (hstrict : ∃ X_int, P.isStrictlyFeasible X_int)
    (hFinite : BddAbove (Set.range fun (X : {X // P.isFeasible X}) => P.objective X.val)) :
    ∃ y, P.isDualFeasible y ∧
      ⨆ X : {X // P.isFeasible X}, P.objective X.val =
      ⨅ y : {y // P.isDualFeasible y}, P.dualObjective y.val := by
  -- Setup: Get the ConeProgram translation
  let Q := P.toConeProgram
  -- Finite dimensionality of SymMatrix
  haveI : FiniteDimensional ℝ (SymMatrix n) := inferInstance
  -- Step 1: Get Slater point from strict feasibility
  obtain ⟨X_int, hX_int⟩ := hstrict
  have hSlater : ∃ x₀, Q.isSlaterPointEq x₀ :=
    ⟨X_int, toConeProgram_isSlaterPointEq P X_int hX_int⟩
  -- Step 2: Apply ConeProgram.strong_duality_exists
  have hQ_feas : ∃ X, Q.isFeasible X := toConeProgram_hasFeasible P hfeas
  have hQ_finite : BddAbove (Set.range fun (X : {X // Q.isFeasible X}) => Q.objective X.val) :=
    toConeProgram_bddAbove P hFinite
  obtain ⟨y', hy'_dual, hy'_eq⟩ := ConeProgram.strong_duality_exists Q hQ_feas
    (toConeProgram_dualCone_L_univ P) hSlater hQ_finite
  -- Step 3: Translate dual feasibility back to SDPSym
  let y := (piLpEquivSym m).symm y'
  have hy_dual : P.isDualFeasible y := toConeProgram_isDualFeasible P y' hy'_dual
  use y, hy_dual
  -- Step 4: Show equality of values
  -- Get Nonempty instances
  obtain ⟨X₀, hX₀⟩ := hfeas
  haveI hNE_sdp : Nonempty {X // P.isFeasible X} := ⟨⟨X₀, hX₀⟩⟩
  haveI hNE_cone : Nonempty {X // Q.isFeasible X} :=
    ⟨⟨X₀, (toConeProgram_isFeasible P X₀).mpr hX₀⟩⟩
  haveI hNE_dual_sdp : Nonempty {y // P.isDualFeasible y} := ⟨⟨y, hy_dual⟩⟩
  haveI hNE_dual_cone : Nonempty {y' // Q.isDualFeasible y'} := ⟨⟨y', hy'_dual⟩⟩
  -- LHS: ⨆ over SDPSym feasible = ⨆ over ConeProgram feasible (by objective translation)
  have hprimal_eq : (⨆ X : {X // P.isFeasible X}, P.objective X.val) =
      ⨆ X : {X // Q.isFeasible X}, Q.objective X.val := by
    apply le_antisymm
    · apply ciSup_le; intro ⟨X, hX⟩
      rw [← toConeProgram_objective]
      exact le_ciSup hQ_finite ⟨X, (toConeProgram_isFeasible P X).mpr hX⟩
    · apply ciSup_le; intro ⟨X, hX⟩
      rw [toConeProgram_objective]
      exact le_ciSup hFinite ⟨X, (toConeProgram_isFeasible P X).mp hX⟩
  rw [hprimal_eq, hy'_eq]
  -- RHS: The ConeProgram dual infimum equals SDPSym dual infimum
  -- We have a bijection between dual feasible sets via piLpEquivSym
  -- Dual objective is bounded below by any primal feasible point (weak duality)
  have hQ_bddBelow : BddBelow (Set.range fun y' : {y' // Q.isDualFeasible y'} =>
      Q.dualObjective y'.val) := by
    use Q.objective X₀
    intro v ⟨⟨y'', hy''⟩, hv⟩
    rw [← hv]
    exact ConeProgram.weak_duality Q X₀ y'' ((toConeProgram_isFeasible P X₀).mpr hX₀) hy''
  have hP_bddBelow : BddBelow (Set.range fun y : {y // P.isDualFeasible y} =>
      P.dualObjective y.val) := by
    use P.objective X₀
    intro v ⟨⟨y'', hy''⟩, hv⟩
    rw [← hv]
    -- Use ConeProgram weak duality via translation
    have hQ_feas_X₀ := (toConeProgram_isFeasible P X₀).mpr hX₀
    have hQ_dual_y'' := toConeProgram_isDualFeasible_rev P y'' hy''
    have hQ_wd := ConeProgram.weak_duality Q X₀ (piLpEquivSym m y'') hQ_feas_X₀ hQ_dual_y''
    have h1 : Q.objective X₀ = P.objective X₀ := toConeProgram_objective P X₀
    have h2 : Q.dualObjective (piLpEquivSym m y'') = P.dualObjective y'' := by
      rw [toConeProgram_dualObjective]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
    rw [h1, h2] at hQ_wd
    exact hQ_wd
  have hdual_eq : (⨅ y' : {y' // Q.isDualFeasible y'}, Q.dualObjective y'.val) =
      ⨅ y : {y // P.isDualFeasible y}, P.dualObjective y.val := by
    apply le_antisymm
    · -- ConeProgram dual infimum ≤ SDPSym dual infimum
      apply le_ciInf; intro ⟨y_sdp, hy_sdp⟩
      have h_cone : Q.isDualFeasible (piLpEquivSym m y_sdp) :=
        toConeProgram_isDualFeasible_rev P y_sdp hy_sdp
      calc (⨅ y' : {y' // Q.isDualFeasible y'}, Q.dualObjective y'.val)
          ≤ Q.dualObjective (piLpEquivSym m y_sdp) :=
              ciInf_le hQ_bddBelow ⟨piLpEquivSym m y_sdp, h_cone⟩
        _ = P.dualObjective ((piLpEquivSym m).symm (piLpEquivSym m y_sdp)) :=
              toConeProgram_dualObjective P (piLpEquivSym m y_sdp)
        _ = P.dualObjective y_sdp := by simp
    · -- SDPSym dual infimum ≤ ConeProgram dual infimum
      apply le_ciInf; intro ⟨y'_cone, hy'_cone⟩
      have h_sdp : P.isDualFeasible ((piLpEquivSym m).symm y'_cone) :=
        toConeProgram_isDualFeasible P y'_cone hy'_cone
      calc (⨅ y : {y // P.isDualFeasible y}, P.dualObjective y.val)
          ≤ P.dualObjective ((piLpEquivSym m).symm y'_cone) :=
              ciInf_le hP_bddBelow ⟨(piLpEquivSym m).symm y'_cone, h_sdp⟩
        _ = Q.dualObjective y'_cone := (toConeProgram_dualObjective P y'_cone).symm
  exact hdual_eq

end SDPSym

end SDPSymmetric

end ConeProgramming
