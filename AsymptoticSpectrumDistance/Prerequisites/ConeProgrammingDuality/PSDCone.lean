/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.Duality
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order

set_option linter.style.longLine false

/-!
# PSD Cones and Self-Duality

This file provides the positive semidefinite cone structure and its self-duality,
following Chapter 4 of Gärtner-Matoušek "Approximation Algorithms and Semidefinite Programming".

## Main definitions

* `SymMatrix` : The subspace of symmetric n×n real matrices
* `psdConeSym` : The PSD cone as a proper cone on symmetric matrices
* `trivialCone` : The trivial cone {0} for equational form constraints

## Main results

* `psd_inner_nonneg` : ⟨X, Y⟩ ≥ 0 for X, Y ⪰ 0
* `psd_cone_self_dual` : (PSD)* = PSD under trace inner product
* `psdConeSym_self_dual` : Self-duality for symmetric PSD cone
* `interior_psdSym_eq_posDef` : interior(PSD) = {X ≻ 0}
-/

namespace ConeProgramming

open scoped InnerProductSpace RealInnerProductSpace
open ContinuousLinearMap

/-! ## Application: Self-Duality of PSD Cone

Lemma 4.7.5: (PSDₙ)* = PSDₙ

The positive semidefinite cone is self-dual, which is used for
SDP duality (Theorem 4.1.1).

The proof uses:
- ⟨X, Y⟩ := Tr(XY) = Tr(XᵀY) (Frobenius inner product)
- For X, Y ⪰ 0: ⟨X, Y⟩ = Tr(XY) ≥ 0 since eigenvalues are nonnegative
- If Tr(XY) ≥ 0 for all Y ⪰ 0, then X ⪰ 0 (take Y = vvᵀ for eigenvectors)
-/

section PSDCone

open Matrix

/-- The trace inner product on matrices: ⟨X, Y⟩ := Tr(XᵀY). -/
def traceInner {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (X.transpose * Y)

/-- For positive semidefinite matrices, the trace inner product is nonnegative.
    This is one direction of PSD cone self-duality.

    Proof: X = BᵀB for some B (factorization), so Tr(XᵀY) = Tr(BᵀBY) = Tr(BYBᵀ).
    Since Y ⪰ 0, we have BYBᵀ ⪰ 0, so Tr(BYBᵀ) ≥ 0. -/
theorem psd_inner_nonneg {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : Matrix.PosSemidef X) (hY : Matrix.PosSemidef Y) : 0 ≤ traceInner X Y := by
  -- X = Bᴴ B for some B
  obtain ⟨B, hXB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ, X = B.conjTranspose * B := by
    open scoped MatrixOrder in
    obtain ⟨B, hXB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
    exact ⟨B, by rw [hXB]; rfl⟩
  simp only [traceInner]
  -- For real matrices, Aᴴ = Aᵀ
  have conjT_eq' : ∀ (A : Matrix (Fin n) (Fin n) ℝ), A.conjTranspose = A.transpose := fun A => by
    ext i j; simp only [conjTranspose_apply, transpose_apply, RCLike.star_def, RCLike.conj_to_real]
  rw [hXB, conjT_eq']
  -- (Bᵀ B)ᵀ = Bᵀ B by symmetry
  have hsym : (B.transpose * B).transpose = B.transpose * B := by
    simp only [transpose_mul, transpose_transpose]
  rw [hsym]
  -- Tr(Bᵀ B Y) = Tr(B Y Bᵀ) by cyclic property
  rw [show (B.transpose * B * Y).trace = (Y * B.transpose * B).trace from trace_mul_cycle _ _ _]
  rw [show (Y * B.transpose * B).trace = (B * Y * B.transpose).trace from trace_mul_cycle _ _ _]
  -- B Y Bᵀ is PSD (using mul_mul_conjTranspose_same)
  have hpsd : (B * Y * B.transpose).PosSemidef := by
    have h := Matrix.PosSemidef.mul_mul_conjTranspose_same hY B
    -- For real matrices, Aᴴ = Aᵀ
    have conjT_eq : ∀ (A : Matrix (Fin n) (Fin n) ℝ), A.conjTranspose = A.transpose := fun A => by
      ext i j; simp only [conjTranspose_apply, transpose_apply, RCLike.star_def, RCLike.conj_to_real]
    rw [conjT_eq] at h
    exact h
  -- Tr of PSD matrix is nonneg
  exact hpsd.trace_nonneg

/-- Trace of Xᵀ * vecMulVec v w. -/
private lemma trace_transpose_mul_vecMulVec {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    (X.transpose * vecMulVec v w).trace = w ⬝ᵥ (X.transpose *ᵥ v) := by
  simp only [trace, diag_apply, Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct,
    transpose_apply]
  congr 1
  funext i
  rw [Finset.mul_sum]
  congr 1
  funext j
  ring

/-- For real vectors, star v = v. -/
private lemma star_real_eq {n : ℕ} (v : Fin n → ℝ) : star v = v := by
  ext i; simp [Pi.star_apply]

/-- IsHermitian for symmetric real matrices. -/
private lemma isHermitian_of_isSymm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) :
    X.IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, RCLike.star_def, RCLike.conj_to_real]
  exact hX.apply i j

/-- Self-duality of PSD cone: (PSDₙ)* = PSDₙ (Lemma 4.7.5).
    Under the Frobenius inner product ⟨X,Y⟩ = Tr(XᵀY), the dual of
    the PSD cone is itself.

    Note: For the reverse direction (dual membership → PSD), X must be symmetric.
    This is natural since PSD matrices are always Hermitian. -/
-- Helper to get IsSymm from IsHermitian for real matrices
private lemma isSymm_of_isHermitian {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (h : X.IsHermitian) :
    X.IsSymm := by
  ext i j
  have hh : X.conjTranspose i j = X i j := by rw [h]
  simp only [conjTranspose_apply, RCLike.star_def, RCLike.conj_to_real] at hh
  simp only [transpose_apply]
  exact hh

theorem psd_cone_self_dual (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.PosSemidef X ↔
      X.IsSymm ∧ (∀ Y, Matrix.PosSemidef Y → 0 ≤ traceInner X Y) := by
  constructor
  · -- If X ⪰ 0, then X is symmetric and Tr(XᵀY) ≥ 0 for all Y ⪰ 0
    intro hX
    constructor
    · exact isSymm_of_isHermitian X hX.isHermitian
    · intro Y hY
      exact psd_inner_nonneg hX hY
  · -- If X is symmetric and Tr(XᵀY) ≥ 0 for all Y ⪰ 0, then X ⪰ 0
    intro ⟨hX_sym, h⟩
    rw [posSemidef_iff_dotProduct_mulVec]
    constructor
    · exact isHermitian_of_isSymm X hX_sym
    · intro v
      haveI : StarOrderedRing ℝ := inferInstance
      have hY : (vecMulVec v (star v)).PosSemidef := posSemidef_vecMulVec_self_star v
      specialize h _ hY
      simp only [traceInner] at h
      rw [trace_transpose_mul_vecMulVec] at h
      rw [star_real_eq] at h
      -- Now h : 0 ≤ v ⬝ᵥ (Xᵀ *ᵥ v)
      -- For symmetric X, Xᵀ = X
      have hXt : X.transpose = X := hX_sym.eq
      rw [hXt] at h
      rw [star_real_eq]
      exact h

end PSDCone

/-! ## SDP Infrastructure: Proper Cones and Interior Characterization

This section provides the infrastructure needed to reduce SDP duality to the
general `ConeProgram.strong_duality` theorem.
-/

section SDPInfrastructure

open Matrix
open scoped Matrix.Norms.Frobenius

variable (n : ℕ)

/-! ### Quadratic Form Continuity -/

/-- The quadratic form v ↦ vᵀXv is continuous in X. -/
lemma quadForm_continuous (v : Fin n → ℝ) :
    Continuous (fun X : Matrix (Fin n) (Fin n) ℝ => v ⬝ᵥ (X *ᵥ v)) := by
  apply Continuous.dotProduct continuous_const
  apply Continuous.matrix_mulVec continuous_id continuous_const

/-- The quadratic form constraint {X | 0 ≤ vᵀXv} is closed. -/
lemma isClosed_nonneg_quadform (v : Fin n → ℝ) :
    IsClosed {X : Matrix (Fin n) (Fin n) ℝ | 0 ≤ v ⬝ᵥ (X *ᵥ v)} :=
  isClosed_le continuous_const (quadForm_continuous n v)

/-! ### Quadratic Form Bounds for Interior Characterization -/

/-- Convert double sum to sum over pairs. -/
private lemma double_sum_to_pair (f : Fin n → Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, f i j = ∑ p : Fin n × Fin n, f p.1 p.2 := by
  have h : (Finset.univ : Finset (Fin n)) ×ˢ Finset.univ =
           (Finset.univ : Finset (Fin n × Fin n)) := by ext p; simp
  rw [← h, Finset.sum_product']

/-- Sum of squared products equals square of sums. -/
private lemma sum_sq_prod_eq (v : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, (v i * v j) ^ 2 = (∑ i : Fin n, v i ^ 2) ^ 2 := by
  calc ∑ i : Fin n, ∑ j : Fin n, (v i * v j) ^ 2
      = ∑ i : Fin n, ∑ j : Fin n, v i ^ 2 * v j ^ 2 := by
        congr 1; ext i; congr 1; ext j; ring
    _ = ∑ i : Fin n, v i ^ 2 * (∑ j : Fin n, v j ^ 2) := by
        congr 1; ext i; rw [Finset.mul_sum]
    _ = (∑ j : Fin n, v j ^ 2) * (∑ i : Fin n, v i ^ 2) := by
        rw [Finset.sum_mul]
    _ = (∑ i : Fin n, v i ^ 2) ^ 2 := by ring

/-- Cauchy-Schwarz for the quadratic form (squared version). -/
private lemma quadForm_bound_sq (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (v ⬝ᵥ (M *ᵥ v)) ^ 2 ≤
    (∑ i : Fin n, v i ^ 2) ^ 2 * ∑ i : Fin n, ∑ j : Fin n, M i j ^ 2 := by
  have h1 : v ⬝ᵥ (M *ᵥ v) = ∑ i : Fin n, ∑ j : Fin n, (v i * v j) * M i j := by
    simp only [dotProduct, mulVec]
    congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
  rw [h1]
  rw [double_sum_to_pair n (fun i j => (v i * v j) * M i j)]
  rw [← sum_sq_prod_eq n v, double_sum_to_pair n (fun i j => (v i * v j) ^ 2)]
  rw [double_sum_to_pair n (fun i j => M i j ^ 2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun (p : Fin n × Fin n) => v p.1 * v p.2)
    (fun (p : Fin n × Fin n) => M p.1 p.2)

/-- Frobenius norm squared equals sum of squared entries. -/
lemma norm_sq_eq_sum_sq (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖M‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, M i j ^ 2 := by
  simp only [Matrix.frobenius_norm_def, Real.norm_eq_abs]
  -- We have ((∑ ∑ |M i j|^(2:ℝ))^(1/2))^2
  have habs_sq : ∀ i j, |M i j| ^ (2 : ℝ) = (M i j) ^ 2 := fun i j => by
    rw [Real.rpow_two, sq_abs]
  have hsum_eq : (∑ i : Fin n, ∑ j : Fin n, |M i j| ^ (2 : ℝ)) =
                 (∑ i : Fin n, ∑ j : Fin n, M i j ^ 2) := by
    congr 1; ext i; congr 1; ext j; exact habs_sq i j
  rw [hsum_eq]
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, M i j ^ 2 := by
    apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
    exact sq_nonneg _
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsum_nonneg]

/-- The key bound: |v ⬝ᵥ (M *ᵥ v)| ≤ (v ⬝ᵥ v) * ‖M‖.
This bounds the quadratic form perturbation by the Frobenius norm. -/
lemma quadForm_abs_bound (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    |v ⬝ᵥ (M *ᵥ v)| ≤ (v ⬝ᵥ v) * ‖M‖ := by
  have hsq := quadForm_bound_sq n M v
  have hdot_eq : v ⬝ᵥ v = ∑ i : Fin n, v i ^ 2 := by
    simp only [dotProduct]; congr 1; ext i; ring
  -- Rewrite hsq using norm_sq_eq_sum_sq: ‖M‖^2 = ∑∑ M i j ^2
  rw [← norm_sq_eq_sum_sq] at hsq
  -- Now hsq : (v ⬝ᵥ (M *ᵥ v)) ^ 2 ≤ (∑ i, v i ^ 2) ^ 2 * ‖M‖ ^ 2
  have ha : 0 ≤ ∑ i : Fin n, v i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : 0 ≤ ‖M‖ := norm_nonneg M
  have hsq' : (v ⬝ᵥ (M *ᵥ v)) ^ 2 ≤ ((∑ i : Fin n, v i ^ 2) * ‖M‖) ^ 2 := by
    calc (v ⬝ᵥ (M *ᵥ v)) ^ 2
        ≤ (∑ i : Fin n, v i ^ 2) ^ 2 * ‖M‖ ^ 2 := hsq
      _ = ((∑ i : Fin n, v i ^ 2) * ‖M‖) ^ 2 := by ring
  -- From hsq' : a² ≤ b² with b ≥ 0, we get |a| ≤ b
  have hprod_nonneg : 0 ≤ (∑ i : Fin n, v i ^ 2) * ‖M‖ := mul_nonneg ha hb
  have h : |v ⬝ᵥ (M *ᵥ v)| ≤ (∑ i : Fin n, v i ^ 2) * ‖M‖ := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hprod_nonneg]
    exact Real.sqrt_le_sqrt hsq'
  rw [hdot_eq]
  exact h

/-! ### Transpose Continuity (for IsHermitian closedness) -/

/-- Transpose is continuous for real matrices (equals conjTranspose = star). -/
private lemma continuous_transpose_via_star :
    Continuous (transpose : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
  have h : (transpose : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) = conjTranspose := by
    ext X i j
    simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, RCLike.conj_to_real]
  rw [h]
  have : (conjTranspose : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) = star := rfl
  rw [this]
  exact continuous_star

/-- The pairing X ↦ (X, Xᵀ) is continuous. -/
private lemma continuous_pair_transpose :
    Continuous (fun X : Matrix (Fin n) (Fin n) ℝ => (X, X.transpose)) :=
  continuous_id.prodMk (continuous_transpose_via_star n)

/-- The set of Hermitian (= symmetric for real) matrices is closed. -/
lemma isClosed_isHermitian :
    IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.IsHermitian} := by
  have hconjT_eq : ∀ (X : Matrix (Fin n) (Fin n) ℝ), X.conjTranspose = X.transpose := fun X => by
    ext i j
    simp only [conjTranspose_apply, transpose_apply, RCLike.star_def, RCLike.conj_to_real]
  have heq : {X : Matrix (Fin n) (Fin n) ℝ | X.IsHermitian} = {X | X.transpose = X} := by
    ext X
    simp only [Matrix.IsHermitian, Set.mem_setOf_eq, hconjT_eq]
  rw [heq]
  have : {X : Matrix (Fin n) (Fin n) ℝ | X.transpose = X} =
      (fun X => (X, X.transpose))⁻¹' {p | p.1 = p.2} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    exact Eq.comm
  rw [this]
  apply IsClosed.preimage (continuous_pair_transpose n) isClosed_diagonal

/-! ### PSD Cone Closedness (Lemma 4.2.2) -/

/-- The positive semidefinite cone is closed (Lemma 4.2.2 from Gärtner-Matoušek).

**Proof**: The set {X | X.PosSemidef} = {X | X.IsHermitian} ∩ ⋂_v {X | vᵀXv ≥ 0}.
Both sets are closed (IsHermitian by diagonal preimage, quadform by continuity). -/
theorem posSemidef_isClosed :
    IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
  have heq : {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} =
      {X | X.IsHermitian} ∩ ⋂ (v : Fin n → ℝ), {X | 0 ≤ star v ⬝ᵥ (X *ᵥ v)} := by
    ext X
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [posSemidef_iff_dotProduct_mulVec]
  rw [heq]
  apply IsClosed.inter (isClosed_isHermitian n)
  apply isClosed_iInter
  intro v
  rw [star_real_eq]
  exact isClosed_nonneg_quadform n v

/-! ### PSD Proper Cone -/

/-- The positive semidefinite cone as a proper cone. -/
def psdCone : ProperCone ℝ (Matrix (Fin n) (Fin n) ℝ) where
  toSubmodule := {
    carrier := {X | X.PosSemidef}
    add_mem' := fun hX hY => hX.add hY
    zero_mem' := PosSemidef.zero
    smul_mem' := fun ⟨_, hc⟩ _ hX => hX.smul hc
  }
  isClosed' := posSemidef_isClosed n

@[simp]
theorem mem_psdCone {X : Matrix (Fin n) (Fin n) ℝ} :
    X ∈ psdCone n ↔ X.PosSemidef := Iff.rfl

/-! ### Symmetric Matrix Subspace (following Gärtner-Matoušek)

The book defines V = SYMn (symmetric n×n matrices) with Frobenius inner product.
Working in this subspace ensures that `interior(PSD) = PosDef` is mathematically correct,
because we compute the interior relative to the symmetric matrix space.
-/

-- Use Frobenius norm for topology on matrices
open scoped Matrix.Norms.Frobenius in
/-- The submodule of symmetric n×n real matrices.
Following Gärtner-Matoušek: V = SYMn is the ambient space for SDP formulation. -/
def SymMatrixSubmodule : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | A.IsSymm}
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := isSymm_zero
  smul_mem' := fun c _ ha => ha.smul c

/-- Abbreviation for the symmetric matrix type. -/
abbrev SymMatrix (n : ℕ) := SymMatrixSubmodule n

-- SymMatrix inherits normed structure from the ambient Matrix space
/-- SymMatrix is a complete (finite-dimensional) space.
This instance targets the *default* `UniformSpace ↥(SymMatrix n)`, which Lean
elaborates as the `Subtype` uniform space `instUniformSpaceSubtype`. -/
instance symMatrix_completeSpace : CompleteSpace (SymMatrix n) := by
  haveI : FiniteDimensional ℝ (SymMatrix n) := inferInstance
  haveI : IsUniformAddGroup (SymMatrix n) :=
    (SymMatrixSubmodule n).toAddSubgroup.isUniformAddGroup
  exact FiniteDimensional.complete ℝ _

-- v4.29: `ContinuousLinearMap.adjoint`, `ProperCone.innerDual`, and
-- `ConeProgram.isDualFeasible` all force typeclass elaboration to look for
-- `CompleteSpace ↥(SymMatrix n)` under the uniform space derived from
-- `Submodule.normedAddCommGroup → SeminormedAddCommGroup.toPseudoMetricSpace →
-- PseudoMetricSpace.toUniformSpace`, *not* the bare `instUniformSpaceSubtype` that
-- the previous `symMatrix_completeSpace` targets. These two uniform structures are
-- propositionally equal but no longer reconciled by v4.29's stricter unifier, so we
-- provide this second instance to satisfy that synthesis path explicitly.
open scoped Matrix.Norms.Frobenius in
/-- Companion `CompleteSpace` instance targeting the norm-derived `UniformSpace` on
`↥(SymMatrix n)` (the one v4.29 elaboration paths through
`Submodule.normedAddCommGroup` require). -/
instance symMatrix_completeSpace_norm :
    @CompleteSpace (SymMatrix n) ((Submodule.normedAddCommGroup _).toUniformSpace) :=
  ⟨(Submodule.complete_of_finiteDimensional
      (SymMatrixSubmodule n)).completeSpace_coe.complete⟩

/-- PSD is closed in the symmetric matrix subspace (preimage of closed set). -/
theorem psdConeSym_isClosed :
    IsClosed {A : SymMatrix n | A.val.PosSemidef} := by
  have h : {A : SymMatrix n | A.val.PosSemidef} =
      Subtype.val ⁻¹' {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
    ext A; simp
  rw [h]
  exact (posSemidef_isClosed n).preimage continuous_subtype_val

/-- The positive semidefinite cone on symmetric matrices.
This is the mathematically correct formulation following Gärtner-Matoušek. -/
def psdConeSym : ProperCone ℝ (SymMatrix n) where
  toSubmodule := {
    carrier := {A : SymMatrix n | A.val.PosSemidef}
    add_mem' := fun hX hY => hX.add hY
    zero_mem' := PosSemidef.zero
    smul_mem' := fun ⟨_, hc⟩ _ hA => hA.smul hc
  }
  isClosed' := psdConeSym_isClosed n

@[simp]
theorem mem_psdConeSym {A : SymMatrix n} :
    A ∈ psdConeSym n ↔ A.val.PosSemidef := Iff.rfl

/-- Helper: vecMulVec v v subtracted from A decreases the quadratic form on v. -/
private lemma quadForm_sub_vecMulVec (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (ε : ℝ) :
    v ⬝ᵥ ((A - ε • vecMulVec v v) *ᵥ v) = v ⬝ᵥ (A *ᵥ v) - ε * (v ⬝ᵥ v) ^ 2 := by
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]
  congr 1
  -- Need: v ⬝ᵥ ((vecMulVec v v) *ᵥ v) = (v ⬝ᵥ v)^2
  simp only [vecMulVec, mulVec, dotProduct]
  rw [sq]
  simp only [smul_eq_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [of_apply]
  ring

/-- Helper: if A is PSD but not PD, there exists v ≠ 0 with ⟨v, Av⟩ = 0. -/
private lemma exists_zero_quadForm_of_not_posDef {A : Matrix (Fin n) (Fin n) ℝ}
    (hpsd : A.PosSemidef) (hnotpd : ¬A.PosDef) : ∃ v ≠ 0, v ⬝ᵥ (A *ᵥ v) = 0 := by
  rw [Matrix.PosDef] at hnotpd
  push_neg at hnotpd
  obtain ⟨v, hv_ne, hv_le⟩ := hnotpd hpsd.isHermitian
  -- v is a Finsupp, convert to regular function ⇑v
  refine ⟨⇑v, ?_, ?_⟩
  · -- ⇑v ≠ 0
    intro h
    apply hv_ne
    ext i
    exact congr_fun h i
  · -- dotProduct ⇑v (A.mulVec ⇑v) = 0
    -- Convert between Finsupp.sum and dotProduct
    have hconv : (⇑v) ⬝ᵥ (A *ᵥ (⇑v)) = v.sum fun i xi => v.sum fun j xj => star xi * A i j * xj := by
      simp only [dotProduct, mulVec, star_trivial]
      rw [Finsupp.sum_fintype v _ (by intro i; simp)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finsupp.sum_fintype v _ (by intro j; simp)]
      simp only [mul_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hconv]
    apply le_antisymm hv_le
    -- For the lower bound, use hpsd.dotProduct_mulVec_nonneg and convert back
    have h1 : 0 ≤ star (⇑v) ⬝ᵥ (A *ᵥ ⇑v) := hpsd.dotProduct_mulVec_nonneg ⇑v
    simp only [star_trivial] at h1
    rw [hconv] at h1
    exact h1

/-- Helper: vvᵀ is symmetric. -/
theorem isSymm_vecMulVec (v : Fin n → ℝ) : (vecMulVec v v).IsSymm := by
  rw [Matrix.IsSymm, transpose_vecMulVec]

/-- Rayleigh quotient lower bound: For a Hermitian matrix A with minimum eigenvalue λ_min,
the quadratic form satisfies v ⬝ᵥ (A *ᵥ v) ≥ λ_min * (v ⬝ᵥ v) for all v.

This follows from the spectral decomposition: if {u_i} is an orthonormal eigenbasis with
eigenvalues {λ_i}, then v ⬝ᵥ (A *ᵥ v) = ∑_i λ_i |⟨v, u_i⟩|² ≥ λ_min * ∑_i |⟨v, u_i⟩|² = λ_min * ‖v‖².

The proof uses the spectral theorem A = U * diag(λ) * Uᵀ where U is orthogonal.
Setting w = Uᵀv, we get v ⬝ᵥ (A *ᵥ v) = ∑ᵢ λᵢwᵢ² ≥ λ_min * ∑ᵢ wᵢ² = λ_min * (v ⬝ᵥ v). -/
lemma IsHermitian.rayleigh_lower_bound [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (v : Fin n → ℝ) :
    (Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
  -- Use spectral theorem: A = U * diagonal(eigvals) * Uᵀ
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  let eigvals := hA.eigenvalues
  have hUstar : star U = Uᵀ := by
    ext i j; simp only [Matrix.star_apply, Matrix.transpose_apply, RCLike.star_def,
      RCLike.conj_to_real]
  have hspec' : A = U * Matrix.diagonal eigvals * Uᵀ := by
    rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, hUstar]
    -- Goal: U * diagonal (ofReal ∘ hA.eigenvalues) * Uᵀ = U * diagonal eigvals * Uᵀ
    -- These are defeq since ofReal for ℝ → ℝ is id
    rfl
  let w := mulVec Uᵀ v
  have hUUT : U * Uᵀ = 1 := by
    rw [← hUstar]; exact Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).prop
  -- v ⬝ᵥ v = w ⬝ᵥ w (unitary preserves dot product)
  have hdot : dotProduct v v = dotProduct w w := by
    have h1 : dotProduct v v = dotProduct v (mulVec 1 v) := by rw [one_mulVec]
    have h2 : dotProduct v (mulVec 1 v) = dotProduct v (mulVec (U * Uᵀ) v) := by rw [hUUT]
    have h3 : dotProduct v (mulVec (U * Uᵀ) v) = dotProduct v (mulVec U (mulVec Uᵀ v)) := by
      rw [mulVec_mulVec]
    have h4 : dotProduct v (mulVec U (mulVec Uᵀ v)) = dotProduct (mulVec Uᵀ v) (mulVec Uᵀ v) := by
      rw [dotProduct_mulVec, ← mulVec_transpose]
    rw [h1, h2, h3, h4]
  -- v ⬝ᵥ (A *ᵥ v) = ∑ i, eigvals i * w i ^ 2
  have hquad : dotProduct v (mulVec A v) = ∑ i, eigvals i * (w i) ^ 2 := by
    have h1 : dotProduct v (mulVec A v) =
              dotProduct v (mulVec (U * diagonal eigvals * Uᵀ) v) := by rw [hspec']
    have h2 : dotProduct v (mulVec (U * diagonal eigvals * Uᵀ) v) =
              dotProduct v (mulVec U (mulVec (diagonal eigvals) (mulVec Uᵀ v))) := by
      rw [mulVec_mulVec, mulVec_mulVec]
    have h3 : dotProduct v (mulVec U (mulVec (diagonal eigvals) (mulVec Uᵀ v))) =
              dotProduct (mulVec Uᵀ v) (mulVec (diagonal eigvals) (mulVec Uᵀ v)) := by
      rw [dotProduct_mulVec, ← mulVec_transpose]
    have h4 : dotProduct w (mulVec (diagonal eigvals) w) = ∑ i, w i * (eigvals i * w i) := by
      simp only [dotProduct, mulVec, diagonal, of_apply]
      congr 1; funext i; congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [hji.symm]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have h5 : (∑ i, w i * (eigvals i * w i)) = ∑ i, eigvals i * (w i) ^ 2 := by
      congr 1; funext i; ring
    rw [h1, h2, h3, h4, h5]
  -- ∑ i, eigvals i * w i ^ 2 ≥ eigvals_min * ∑ i, w i ^ 2
  have hbound : (Finset.univ.inf' Finset.univ_nonempty eigvals) * (∑ i, (w i) ^ 2) ≤
      ∑ i, eigvals i * (w i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : Finset.univ.inf' Finset.univ_nonempty eigvals ≤ eigvals i :=
      Finset.inf'_le _ (Finset.mem_univ i)
    nlinarith [sq_nonneg (w i)]
  have hdotsum : dotProduct w w = ∑ i, (w i) ^ 2 := by simp only [dotProduct, sq]
  rw [hdot, hdotsum, hquad]
  exact hbound

/-- Interior of PSD cone in symmetric matrices equals positive definite matrices.
This is the mathematically correct characterization (Gärtner-Matoušek page 47).

**Proof:**
- (⊆) If A ∈ interior(PSD) but not PosDef, there exists v ≠ 0 with ⟨v, Av⟩ = 0.
  Then A - ε·vvᵀ is symmetric and has ⟨v, (A - ε·vvᵀ)v⟩ = -ε‖v‖⁴ < 0,
  so A - ε·vvᵀ ∉ PSD for any ε > 0, contradicting A being in the interior.
- (⊇) If A ≻ 0, the function X ↦ ⟨v, Xv⟩ is continuous for each v, and by compactness
  of the unit sphere, the minimum eigenvalue depends continuously on A.
  So there's a neighborhood of A where all matrices are PosDef, hence PSD. -/
theorem interior_psdSym_eq_posDef :
    interior {A : SymMatrix n | A.val.PosSemidef} = {A : SymMatrix n | A.val.PosDef} := by
  ext A
  constructor
  · -- (⊆) interior(PSD) ⊆ PosDef
    intro hA_int
    by_contra hA_not_pd
    -- A is PSD (since interior ⊆ set)
    have hA_psd : A.val.PosSemidef := by
      have h := @interior_subset (SymMatrix n) _ {B | B.val.PosSemidef} A hA_int
      exact h
    -- Get v ≠ 0 with ⟨v, Av⟩ = 0
    have hA_not_pd' : ¬A.val.PosDef := by simpa using hA_not_pd
    obtain ⟨v, hv_ne, hv_zero⟩ := exists_zero_quadForm_of_not_posDef (n := n) (A := A.val) hA_psd hA_not_pd'
    -- Perturbation argument: construct B = A - ε·vvᵀ which is close to A but not PSD
    -- Get ball around A that stays in PSD
    rw [mem_interior_iff_mem_nhds] at hA_int
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp hA_int
    -- Construct the perturbation vvᵀ as a SymMatrix
    let vvT : SymMatrix n := ⟨vecMulVec v v, isSymm_vecMulVec (n := n) v⟩
    -- Choose ε small enough that ε·‖vvᵀ‖ < δ
    have hvvT_ne : vvT.val ≠ 0 := by
      intro h
      apply hv_ne
      -- If vvᵀ = 0, then v = 0
      have hdiag : ∀ i, vecMulVec v v i i = 0 := fun i => by
        have := congrFun (congrFun h i) i
        exact this
      simp only [vecMulVec, of_apply] at hdiag
      ext i
      have := hdiag i
      simp only [Pi.zero_apply, mul_self_eq_zero] at this ⊢
      exact this
    have hvvT_norm_pos : 0 < ‖vvT‖ := by
      rw [norm_pos_iff]
      simp only [ne_eq, Subtype.ext_iff]
      exact hvvT_ne
    -- Choose ε = δ / (2 * ‖vvᵀ‖)
    set ε := δ / (2 * ‖vvT‖) with hε_def
    have hε_pos : 0 < ε := div_pos hδ_pos (by linarith)
    -- Construct B = A - ε·vvᵀ
    let B : SymMatrix n := A - ε • vvT
    -- Show ‖B - A‖ < δ
    have hB_close : dist B A < δ := by
      show ‖B - A‖ < δ
      simp only [B, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_pos hε_pos]
      calc ε * ‖vvT‖ = (δ / (2 * ‖vvT‖)) * ‖vvT‖ := by rw [hε_def]
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
    -- B is in the ball, so should be PSD
    have hB_in_ball : B ∈ Metric.ball A δ := by
      rw [Metric.mem_ball]
      exact hB_close
    have hB_psd : B.val.PosSemidef := hball hB_in_ball
    -- But ⟨v, Bv⟩ < 0
    have hquad : v ⬝ᵥ (B.val *ᵥ v) = v ⬝ᵥ (A.val *ᵥ v) - ε * (v ⬝ᵥ v) ^ 2 := by
      simp only [B, Submodule.coe_sub, Submodule.coe_smul_of_tower]
      exact quadForm_sub_vecMulVec (n := n) A.val v ε
    have hvdotv_pos : 0 < v ⬝ᵥ v := by
      have h := dotProduct_star_self_pos_iff (v := v)
      simp only [star_trivial] at h
      exact h.mpr hv_ne
    have hquad_neg : v ⬝ᵥ (B.val *ᵥ v) < 0 := by
      rw [hquad, hv_zero]
      simp only [zero_sub]
      apply neg_neg_of_pos
      apply mul_pos hε_pos
      apply sq_pos_of_pos hvdotv_pos
    -- Contradiction: B is PSD but ⟨v, Bv⟩ < 0
    have hquad_nonneg := hB_psd.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at hquad_nonneg
    linarith
  · -- (⊇) PosDef ⊆ interior(PSD)
    intro hA_pd
    -- Strategy: Use the quadratic form characterization of PSD.
    -- For PosDef A with minimum eigenvalue lmin > 0:
    -- - For any v, v ⬝ᵥ (A *ᵥ v) ≥ lmin * (v ⬝ᵥ v)
    -- - For B close to A: v ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ ((B-A) *ᵥ v)
    -- - By quadForm_abs_bound: |v ⬝ᵥ ((B-A) *ᵥ v)| ≤ (v ⬝ᵥ v) * ‖B-A‖
    -- - If ‖B-A‖ < lmin, then v ⬝ᵥ (B *ᵥ v) > 0 for all v ≠ 0
    -- This proves B is PSD.
    rw [mem_interior_iff_mem_nhds]
    refine Metric.mem_nhds_iff.mpr ?_
    -- Handle case n = 0 separately (all 0x0 matrices are vacuously PSD)
    by_cases hn : n = 0
    · subst hn
      refine ⟨1, one_pos, fun B _ => ?_⟩
      simp only [Set.mem_setOf_eq]
      -- For 0x0 matrix, PosSemidef is vacuously true (no vectors exist)
      rw [posSemidef_iff_dotProduct_mulVec]
      exact ⟨isHermitian_of_isSymm B.val B.prop, fun v => by simp [Subsingleton.elim v 0]⟩
    · have hne : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
      have hA_herm : A.val.IsHermitian := hA_pd.isHermitian
      -- The minimum eigenvalue provides the radius
      set lmin := Finset.univ.inf' (Finset.univ_nonempty_iff.mpr hne)
          (hA_herm.eigenvalues) with hlmin_def
      have hmin_pos : 0 < lmin := by
        rw [Finset.lt_inf'_iff]
        intro i _
        exact hA_pd.eigenvalues_pos i
      -- Use lmin / 2 as the radius
      refine ⟨lmin / 2, by linarith, ?_⟩
      intro B hB_close
      -- B is symmetric and close to A
      have hB_herm : B.val.IsHermitian := isHermitian_of_isSymm B.val B.prop
      -- Use quadratic form characterization: PSD iff ∀ v, 0 ≤ v ⬝ᵥ (B *ᵥ v)
      simp only [Set.mem_setOf_eq]
      rw [posSemidef_iff_dotProduct_mulVec]
      refine ⟨hB_herm, ?_⟩
      intro v
      simp only [star_trivial]
      -- Case: v = 0
      by_cases hv : v = 0
      · simp [hv]
      -- Case: v ≠ 0
      -- Bound: v ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ ((B-A) *ᵥ v)
      have hdiff : B.val - A.val = (B - A).val := rfl
      have hB_eq : v ⬝ᵥ (B.val *ᵥ v) = v ⬝ᵥ (A.val *ᵥ v) + v ⬝ᵥ ((B.val - A.val) *ᵥ v) := by
        simp only [Matrix.sub_mulVec]
        rw [dotProduct_sub]
        ring
      rw [hB_eq]
      -- Helper: v ⬝ᵥ v ≥ 0 for real vectors
      have hvdotv_nonneg' : 0 ≤ v ⬝ᵥ v := by
        simp only [dotProduct]
        exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
      -- PosDef A gives: v ⬝ᵥ (A *ᵥ v) ≥ lmin * (v ⬝ᵥ v)
      -- This is the Rayleigh quotient lower bound from spectral theory:
      -- For Hermitian A with eigenvalues λ_i and orthonormal eigenbasis {u_i},
      -- v ⬝ᵥ (A *ᵥ v) = ∑_i λ_i |⟨v, u_i⟩|² ≥ lmin * ∑_i |⟨v, u_i⟩|² = lmin * (v ⬝ᵥ v)
      have hA_lower : lmin * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A.val *ᵥ v) := by
        -- Use the Rayleigh quotient lower bound
        haveI : Nonempty (Fin n) := hne
        exact @IsHermitian.rayleigh_lower_bound n _ A.val hA_herm v
      -- Perturbation bound: |v ⬝ᵥ ((B-A) *ᵥ v)| ≤ (v ⬝ᵥ v) * ‖B - A‖
      have hdist : ‖B - A‖ < lmin / 2 := by
        have : dist B A < lmin / 2 := hB_close
        rwa [show dist B A = ‖B - A‖ from rfl] at this
      have hpert := quadForm_abs_bound n (B.val - A.val) v
      have hpert' : |v ⬝ᵥ ((B.val - A.val) *ᵥ v)| ≤ (v ⬝ᵥ v) * (lmin / 2) := by
        have hnorm_sub : ‖B.val - A.val‖ = ‖B - A‖ := rfl
        calc |v ⬝ᵥ ((B.val - A.val) *ᵥ v)|
            ≤ (v ⬝ᵥ v) * ‖B.val - A.val‖ := hpert
          _ = (v ⬝ᵥ v) * ‖B - A‖ := by rw [hnorm_sub]
          _ ≤ (v ⬝ᵥ v) * (lmin / 2) := by
              apply mul_le_mul_of_nonneg_left (le_of_lt hdist)
              exact hvdotv_nonneg'
      have hvdotv_nonneg : 0 ≤ v ⬝ᵥ v := hvdotv_nonneg'
      -- Combine: v ⬝ᵥ (B *ᵥ v) ≥ lmin*(v ⬝ᵥ v) - (lmin/2)*(v ⬝ᵥ v) = (lmin/2)*(v ⬝ᵥ v) ≥ 0
      have hfinal : (lmin / 2) * (v ⬝ᵥ v) ≤
          v ⬝ᵥ (A.val *ᵥ v) + v ⬝ᵥ ((B.val - A.val) *ᵥ v) := by
        have h1 : v ⬝ᵥ ((B.val - A.val) *ᵥ v) ≥ -(lmin / 2) * (v ⬝ᵥ v) := by
          have := neg_abs_le (v ⬝ᵥ ((B.val - A.val) *ᵥ v))
          calc v ⬝ᵥ ((B.val - A.val) *ᵥ v)
              ≥ -|v ⬝ᵥ ((B.val - A.val) *ᵥ v)| := this
            _ ≥ -((v ⬝ᵥ v) * (lmin / 2)) := by linarith [hpert']
            _ = -(lmin / 2) * (v ⬝ᵥ v) := by ring
        calc (lmin / 2) * (v ⬝ᵥ v)
            = lmin * (v ⬝ᵥ v) - (lmin / 2) * (v ⬝ᵥ v) := by ring
          _ ≤ v ⬝ᵥ (A.val *ᵥ v) - (lmin / 2) * (v ⬝ᵥ v) := by linarith [hA_lower]
          _ = v ⬝ᵥ (A.val *ᵥ v) + (-(lmin / 2) * (v ⬝ᵥ v)) := by ring
          _ ≤ v ⬝ᵥ (A.val *ᵥ v) + v ⬝ᵥ ((B.val - A.val) *ᵥ v) := by linarith [h1]
      linarith [mul_nonneg (by linarith : 0 ≤ lmin / 2) hvdotv_nonneg]

/-- A positive definite matrix is in the interior of psdConeSym.
This is the correct Slater condition for SDP. -/
theorem PosDef.mem_interior_psdSym {A : SymMatrix n} (hA : A.val.PosDef) :
    A ∈ interior (psdConeSym n : Set (SymMatrix n)) := by
  have h : (psdConeSym n : Set (SymMatrix n)) = {A : SymMatrix n | A.val.PosSemidef} := rfl
  rw [h, interior_psdSym_eq_posDef]
  exact hA

/-! ### Interior Characterization -/

/-! ### Trivial Cone {0} -/

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The trivial cone {0} as a proper cone. -/
def trivialCone : ProperCone ℝ W where
  toSubmodule := {
    carrier := {0}
    add_mem' := fun {a b} ha hb => by simp_all
    zero_mem' := Set.mem_singleton 0
    smul_mem' := fun ⟨c, hc⟩ x hx => by simp [Set.mem_singleton_iff.mp hx]
  }
  isClosed' := isClosed_singleton

theorem mem_trivialCone {w : W} : w ∈ (trivialCone (W := W) : Set W) ↔ w = 0 := by
  simp only [SetLike.mem_coe, trivialCone]
  rfl

/-- Every element is in the dual of the trivial cone {0}. -/
theorem mem_dualCone_trivialCone [CompleteSpace W] (y : W) :
    y ∈ dualCone (trivialCone (W := W) : Set W) := by
  rw [mem_dualCone]
  intro x hx
  rw [mem_trivialCone] at hx
  rw [hx, inner_zero_left]

/-- The dual of the trivial cone {0} is the whole space (as sets). -/
theorem dualCone_trivialCone_eq_univ [CompleteSpace W] :
    (dualCone (trivialCone (W := W) : Set W) : Set W) = Set.univ := by
  ext y
  simp only [SetLike.mem_coe, Set.mem_univ, iff_true]
  exact mem_dualCone_trivialCone y

end SDPInfrastructure

/-! ## Matrix Frobenius Inner Product Space

This section defines an `InnerProductSpace` instance for matrices using the
Frobenius (trace) inner product ⟨X, Y⟩ = Tr(XᵀY).
-/

namespace MatrixFrobenius

open scoped Matrix.Norms.Frobenius

variable (n : ℕ)

/-- The Frobenius/trace inner product: ⟨X, Y⟩ = Tr(XᵀY). -/
def traceInnerDef (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (X.transpose * Y).trace

/-- Scoped Inner instance for matrices using trace inner product. -/
noncomputable scoped instance : Inner ℝ (Matrix (Fin n) (Fin n) ℝ) where
  inner := traceInnerDef n

/-- Scoped InnerProductSpace instance for matrices using Frobenius inner product.
    This is compatible with the Frobenius norm from Matrix.Norms.Frobenius. -/
noncomputable scoped instance : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  refine InnerProductSpace.mk ?_ ?_ ?_ ?_
  · -- norm_sq_eq_re_inner
    intro A
    simp only [RCLike.re_to_real]
    have h : ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ)) ^ (1 / 2 : ℝ) := Matrix.frobenius_norm_def A
    have hnn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ (2:ℝ) := by
      apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro j _
      exact Real.rpow_nonneg (norm_nonneg _) _
    have h1 : ‖A‖ ^ (2:ℕ) = ((∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ)) ^ (1 / 2 : ℝ)) ^ (2:ℕ) := by rw [h]
    have h2 : ((∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ)) ^ (1 / 2 : ℝ)) ^ (2:ℕ) =
              (∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ)) ^ ((1/2 : ℝ) * (2:ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
    have h3 : (∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ)) ^ ((1/2 : ℝ) * (2:ℕ)) = ∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ) := by
      simp only [Nat.cast_ofNat, one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, IsUnit.inv_mul_cancel]
      exact Real.rpow_one _
    have h4 : ∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ) = ∑ i, ∑ j, (A i j)^2 := by
      congr 1; ext i; congr 1; ext j
      simp only [Real.norm_eq_abs, sq_abs, Real.rpow_two]
    have key2 : @inner ℝ (Matrix (Fin n) (Fin n) ℝ) _ A A = ∑ i, ∑ j, (A i j)^2 := by
      change (A.transpose * A).trace = _
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Finset.sum_comm]; congr 1; ext i; congr 1; ext j; ring
    rw [h1, h2, h3, h4, key2]
  · -- conj_inner_symm
    intro A B
    simp only [RCLike.conj_to_real]
    change (B.transpose * A).trace = (A.transpose * B).trace
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    congr 1; ext i; congr 1; ext j; ring
  · -- add_left
    intro A B C
    change ((A+B).transpose * C).trace = (A.transpose * C).trace + (B.transpose * C).trace
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]
  · -- smul_left
    intro A B r
    simp only [RCLike.conj_to_real]
    change ((r • A).transpose * B).trace = r * (A.transpose * B).trace
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end MatrixFrobenius

end ConeProgramming
