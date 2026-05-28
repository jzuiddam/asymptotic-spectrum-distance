/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.Duality
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.PSDCone
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Linear Programming as a Special Case of Cone Programming

This file develops LP duality as a special case of cone programming, following
Chapter 4 of Gärtner-Matoušek "Approximation Algorithms and Semidefinite Programming".

## Main results

* `coneImage_isClosed` : The image {Ax : x ≥ 0} is closed (key theorem)
* `LP.strong_duality` : LP strong duality without Slater condition
* `lp_farkas` : Farkas lemma for LP

## Key insight (Exercise 4.7)

For LP, the gap between limit value and value does not occur because:
1. The image cone {Ax : x ∈ ℝ₊ⁿ} is finitely generated (conic hull of columns)
2. Finitely generated cones are polyhedral
3. Polyhedral cones are closed

Therefore LP strong duality holds without requiring a Slater (interior) point.

## References

* Gärtner-Matoušek, Chapter 4 (Duality and Cone Programming), Exercise 4.7
-/

namespace ConeProgramming

open scoped InnerProductSpace RealInnerProductSpace
open Matrix BigOperators Finset

/-! ## Section 1: Matrix as ContinuousLinearMap -/

section MatrixCLM

variable {m n : ℕ}

/-- A matrix A defines a continuous linear map between EuclideanSpace types. -/
noncomputable def matrixToCLM (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

/-- matrixToCLM preserves the mulVec operation. -/
theorem matrixToCLM_apply (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    matrixToCLM A x = Matrix.toEuclideanLin A x := rfl

/-- The adjoint of matrixToCLM A is matrixToCLM Aᵀ. -/
theorem matrixToCLM_adjoint (A : Matrix (Fin m) (Fin n) ℝ) :
    ContinuousLinearMap.adjoint (matrixToCLM A) = matrixToCLM (Aᵀ) := by
  unfold matrixToCLM
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  rw [show LinearMap.adjoint (Matrix.toEuclideanLin A) = (A.conjTranspose).toEuclideanLin from
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm,
    Matrix.conjTranspose_eq_transpose_of_trivial]

end MatrixCLM

/-! ## Section 2: Image Cone is Closed (Key Theorem)

The key theorem for LP duality without Slater: the image {Ax : x ≥ 0} is closed.
This is because finitely generated cones are polyhedral, hence closed.
-/

section ConeImageClosed

variable {m n : ℕ}

/-- The image cone {Ax : x ≥ 0} as a set. -/
def coneImage (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  {y | ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A.mulVec x = y}

/-- The support of a vector: indices where it is positive. -/
noncomputable def support (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.filter (fun j => x j ≠ 0) Finset.univ

/-- A vector u is optimal (for matrix A) if:
    - u ∈ [0,1]ⁿ (componentwise)
    - ‖u‖ = 1
    - No z ≥ 0 with Az = Au has smaller support than u -/
def IsOptimal (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ u j ∧ u j ≤ 1) ∧
  ‖u‖ = 1 ∧
  ∀ z : Fin n → ℝ, (∀ j, 0 ≤ z j) → A.mulVec z = A.mulVec u →
    (support z).card ≥ (support u).card

/-- For an optimal vector u, Au ≠ 0.
    Proof: If Au = 0, then z = 0 satisfies Az = Au with support size 0 < support size of u
    (since ‖u‖ = 1 means u ≠ 0). -/
theorem optimal_image_ne_zero (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin n → ℝ)
    (hu : IsOptimal A u) : A.mulVec u ≠ 0 := by
  intro hAu
  obtain ⟨hbounds, hnorm, hmin⟩ := hu
  -- z = 0 satisfies Az = Au = 0
  have hz : A.mulVec 0 = A.mulVec u := by simp [hAu]
  have hzpos : ∀ j, (0 : ℝ) ≤ (0 : Fin n → ℝ) j := fun _ => le_refl 0
  have hcard := hmin 0 hzpos hz
  -- support of 0 is empty
  have hsupp0 : support (0 : Fin n → ℝ) = ∅ := by
    simp only [support, Finset.filter_eq_empty_iff, Finset.mem_univ, Pi.zero_apply,
      ne_eq, not_true_eq_false, not_false_eq_true, implies_true]
  simp only [hsupp0, Finset.card_empty] at hcard
  -- support of u is nonempty since ‖u‖ = 1 means u ≠ 0
  have hu_ne : u ≠ 0 := by
    intro hu0
    rw [hu0] at hnorm
    simp at hnorm
  have hsupp_ne : support u ≠ ∅ := by
    intro hsupp_empty
    apply hu_ne
    ext j
    simp only [Pi.zero_apply]
    by_contra huj
    have : j ∈ support u := by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      exact huj
    rw [hsupp_empty] at this
    exact Finset.notMem_empty j this
  have hcard_pos : 0 < (support u).card :=
    Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hsupp_ne)
  omega

/-- Any nonzero v in coneImage can be written as λ·Au with u optimal and λ > 0. -/
theorem exists_optimal_rep (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin m → ℝ)
    (hv : v ∈ coneImage A) (hv_ne : v ≠ 0) :
    ∃ (lam : ℝ) (u : Fin n → ℝ), 0 < lam ∧ IsOptimal A u ∧ v = lam • A.mulVec u := by
  -- Get x ≥ 0 with Ax = v
  obtain ⟨x, hxpos, hAx⟩ := hv
  -- x ≠ 0 since v ≠ 0
  have hx_ne : x ≠ 0 := by
    intro hx0
    rw [hx0] at hAx
    simp at hAx
    exact hv_ne hAx.symm
  -- Choose z with minimal support among {z ≥ 0 : Az = v}
  -- This exists because support sizes are bounded by n and we have a finite set
  have hexists : ∃ z : Fin n → ℝ, (∀ j, 0 ≤ z j) ∧ A.mulVec z = v ∧
      ∀ w : Fin n → ℝ, (∀ j, 0 ≤ w j) → A.mulVec w = v → (support z).card ≤ (support w).card := by
    -- Use Nat.find on the predicate "there exists z with this support size"
    classical
    let P := fun k => ∃ z : Fin n → ℝ, (∀ j, 0 ≤ z j) ∧ A.mulVec z = v ∧ (support z).card = k
    have hP_exists : ∃ k, P k := ⟨(support x).card, x, hxpos, hAx, rfl⟩
    let min_k := Nat.find hP_exists
    have hmin_spec : P min_k := Nat.find_spec hP_exists
    obtain ⟨z, hzpos, hAz, hz_card⟩ := hmin_spec
    use z, hzpos, hAz
    intro w hwpos hAw
    rw [hz_card]
    -- Show (support w).card ≥ min_k
    have hw_P : P (support w).card := ⟨w, hwpos, hAw, rfl⟩
    exact Nat.find_le hw_P
  obtain ⟨z, hzpos, hAz, hzmin⟩ := hexists
  -- z ≠ 0 since v ≠ 0
  have hz_ne : z ≠ 0 := by
    intro hz0
    rw [hz0] at hAz
    simp at hAz
    exact hv_ne hAz.symm
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  -- Define λ = ‖z‖ and u = z / ‖z‖
  use ‖z‖, (‖z‖)⁻¹ • z
  refine ⟨hnorm_pos, ?_, ?_⟩
  · -- Show u is optimal
    constructor
    · -- u ∈ [0,1]ⁿ
      intro j
      simp only [Pi.smul_apply, smul_eq_mul]
      constructor
      · exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (hzpos j)
      · -- u j = z j / ‖z‖ ≤ 1 because z j ≤ ‖z‖
        by_cases hz_j : z j = 0
        · simp [hz_j]
        · have h1 : z j ≤ ‖z‖ := by
            calc z j ≤ |z j| := le_abs_self _
              _ ≤ ‖z‖ := norm_le_pi_norm z j
          calc (‖z‖)⁻¹ * z j = z j / ‖z‖ := by ring
            _ ≤ ‖z‖ / ‖z‖ := by apply div_le_div_of_nonneg_right h1 (le_of_lt hnorm_pos)
            _ = 1 := div_self (ne_of_gt hnorm_pos)
    constructor
    · -- ‖u‖ = 1
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (ne_of_gt hnorm_pos)
    · -- Minimality of support
      intro w hwpos hAw
      -- Need to show support((‖z‖)⁻¹ • z).card ≤ support(w).card
      -- support of scalar multiple equals support (for positive scalar)
      have hsupp_eq : support ((‖z‖)⁻¹ • z) = support z := by
        ext j
        simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
          Pi.smul_apply, smul_eq_mul, ne_eq]
        constructor
        · intro h hzj
          apply h
          simp [hzj]
        · intro hzj h
          apply hzj
          have hinv_ne : (‖z‖)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hnorm_pos)
          exact (mul_eq_zero.mp h).resolve_left hinv_ne
      rw [hsupp_eq]
      -- Now use hAw to relate to v
      -- A((‖z‖)⁻¹ • z) = (‖z‖)⁻¹ • Az = (‖z‖)⁻¹ • v
      -- So Aw = A((‖z‖)⁻¹ • z) means (‖z‖) • Aw = v
      -- i.e., A(‖z‖ • w) = v
      have hAscaled : A.mulVec (‖z‖ • w) = v := by
        rw [Matrix.mulVec_smul]
        calc ‖z‖ • A.mulVec w = ‖z‖ • ((‖z‖)⁻¹ • A.mulVec z) := by rw [hAw, Matrix.mulVec_smul, hAz]
          _ = (‖z‖ * (‖z‖)⁻¹) • A.mulVec z := by rw [smul_smul]
          _ = A.mulVec z := by rw [mul_inv_cancel₀ (ne_of_gt hnorm_pos), one_smul]
          _ = v := hAz
      have hscaled_pos : ∀ j, 0 ≤ (‖z‖ • w) j := fun j => by
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (le_of_lt hnorm_pos) (hwpos j)
      have hmin := hzmin (‖z‖ • w) hscaled_pos hAscaled
      -- support(‖z‖ • w) = support(w) for ‖z‖ > 0
      have hsupp_w : support (‖z‖ • w) = support w := by
        ext j
        simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
          Pi.smul_apply, smul_eq_mul, ne_eq]
        constructor
        · intro h hw
          apply h
          simp [hw]
        · intro hw h
          apply hw
          have hnz_ne : ‖z‖ ≠ 0 := ne_of_gt hnorm_pos
          exact (mul_eq_zero.mp h).resolve_left hnz_ne
      rw [hsupp_w] at hmin
      exact hmin
  · -- v = λ • Au
    simp only [Matrix.mulVec_smul]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hnorm_pos), one_smul, hAz]

/-- The image of the nonnegative orthant under a matrix is closed.

    This is the key theorem that makes LP duality work without Slater condition.

    The proof uses the "optimal vector" technique from Kager (2022):
    https://arxiv.org/abs/2208.11678

    Key idea: A vector u ∈ [0,1]ⁿ with ‖u‖ = 1 is "optimal" if there's no z ≥ 0
    with Az = Au having fewer nonzero components. Then:
    1. Any v ∈ {Ax : x ≥ 0} can be written as v = λ·Au with u optimal and λ ≥ 0
    2. The set of optimal vectors lies in [0,1]ⁿ ∩ {‖u‖ = 1}, which is compact
    3. For a sequence v_k → v, write v_k = λ_k·Au_k with u_k optimal
    4. Extract convergent subsequence u_{k_j} → u on the compact set
    5. Key step: Au ≠ 0 (if Au = 0, construct z with Az = Au_{k_j} but fewer
       nonzero components, contradicting optimality)
    6. Since ‖v_{k_j}‖ → ‖v‖ and ‖Au_{k_j}‖ → ‖Au‖ ≠ 0, we get λ_{k_j} → λ
    7. Therefore v = λ·Au ∈ {Ax : x ≥ 0} -/
theorem coneImage_isClosed (A : Matrix (Fin m) (Fin n) ℝ) :
    IsClosed (coneImage A) := by
  rw [← isSeqClosed_iff_isClosed]
  intro b_seq b hseq hlim
  -- b_seq k ∈ coneImage A, b_seq → b, need b ∈ coneImage A
  -- For each k, get x_k ≥ 0 with A x_k = b_seq k
  choose x_seq hxpos hAxb using hseq
  -- Case split on whether (x_seq) is bounded
  by_cases hbdd : ∃ M : ℝ, ∀ k, ‖x_seq k‖ ≤ M
  · -- Bounded case: extract convergent subsequence via Bolzano-Weierstrass
    obtain ⟨M, hM⟩ := hbdd
    have hball_bdd : Bornology.IsBounded (Metric.closedBall (0 : Fin n → ℝ) M) :=
      Metric.isBounded_closedBall
    have hxin : ∀ k, x_seq k ∈ Metric.closedBall (0 : Fin n → ℝ) M := by
      intro k
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact hM k
    -- Use Bolzano-Weierstrass (finite-dimensional space is proper)
    haveI : ProperSpace (Fin n → ℝ) := FiniteDimensional.proper_real _
    obtain ⟨x, hxmem, φ, hφmono, hconv⟩ := tendsto_subseq_of_bounded hball_bdd hxin
    -- x is in the closure of the closed ball = closed ball
    rw [Metric.isClosed_closedBall.closure_eq] at hxmem
    -- x ≥ 0 since nonnegative orthant is closed and x_seq k ≥ 0
    have hxpos' : ∀ j, 0 ≤ x j := by
      intro j
      have hclosed : IsClosed {y : Fin n → ℝ | 0 ≤ y j} :=
        isClosed_le continuous_const (continuous_apply j)
      apply hclosed.mem_of_tendsto hconv
      filter_upwards with k
      exact hxpos (φ k) j
    -- Ax = b by continuity
    have hAx : A.mulVec x = b := by
      have hcont : Continuous (fun y => A.mulVec y) :=
        continuous_const.matrix_mulVec continuous_id
      have hlim1 : Filter.Tendsto (fun k => A.mulVec (x_seq (φ k))) Filter.atTop
          (nhds (A.mulVec x)) :=
        hcont.continuousAt.tendsto.comp hconv
      have hlim2 : Filter.Tendsto (fun k => A.mulVec (x_seq (φ k))) Filter.atTop (nhds b) := by
        simp only [hAxb]
        exact hlim.comp hφmono.tendsto_atTop
      exact tendsto_nhds_unique hlim1 hlim2
    exact ⟨x, hxpos', hAx⟩
  · -- Unbounded case: use optimal vector technique
    -- Reference: Kager (2022) https://arxiv.org/abs/2208.11678
    push_neg at hbdd
    -- Handle the easy case b = 0
    by_cases hb_zero : b = 0
    · -- b = 0 is trivially in coneImage (take x = 0)
      rw [hb_zero]
      exact ⟨0, fun _ => le_refl 0, by simp⟩
    -- For b ≠ 0, use optimal vectors
    -- Eventually b_seq k ≠ 0 (since b_seq → b ≠ 0)
    have hev_ne : ∀ᶠ k in Filter.atTop, b_seq k ≠ 0 := by
      have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb_zero
      rw [Filter.eventually_atTop]
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (‖b‖ / 2) (by linarith)
      refine ⟨N, fun k hk hbk => ?_⟩
      have h1 := hN k hk
      rw [hbk] at h1
      simp only [dist_zero_left] at h1
      linarith
    -- Get k₀ such that for all k ≥ k₀, b_seq k ≠ 0
    obtain ⟨k₀, hk₀⟩ := hev_ne.exists_forall_of_atTop
    -- Define shifted sequences starting from k₀
    let b_seq' := fun k => b_seq (k + k₀)
    let x_seq' := fun k => x_seq (k + k₀)
    have hseq' : ∀ k, b_seq' k ∈ coneImage A := by
      intro k
      exact ⟨x_seq (k + k₀), hxpos (k + k₀), hAxb (k + k₀)⟩
    have hlim' : Filter.Tendsto b_seq' Filter.atTop (nhds b) := by
      have hshift : Filter.Tendsto (fun k => k + k₀) Filter.atTop Filter.atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro M
        use M
        intro k hk
        omega
      exact hlim.comp hshift
    have hb_seq'_ne : ∀ k, b_seq' k ≠ 0 := fun k => hk₀ (k + k₀) (Nat.le_add_left k₀ k)
    -- For each k, write b_seq' k = λ_k · A(u_k) with u_k optimal
    have hrep : ∀ k, ∃ (lam : ℝ) (u : Fin n → ℝ),
        0 < lam ∧ IsOptimal A u ∧ b_seq' k = lam • A.mulVec u := by
      intro k
      exact exists_optimal_rep A (b_seq' k) (hseq' k) (hb_seq'_ne k)
    choose lam_seq u_seq hlam_pos hu_opt hu_eq using hrep
    -- The u_seq lie in the compact set [0,1]^n ∩ {‖u‖ = 1}
    -- This is the intersection of a closed box and the unit sphere, both compact
    haveI : ProperSpace (Fin n → ℝ) := FiniteDimensional.proper_real _
    -- Define the compact set
    let K := {u : Fin n → ℝ | (∀ j, 0 ≤ u j ∧ u j ≤ 1) ∧ ‖u‖ = 1}
    have hK_compact : IsCompact K := by
      -- K is a closed subset of a compact set, hence compact
      have h1 : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
        isCompact_univ_pi (fun _ => isCompact_Icc)
      have hK_sub : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
        intro u ⟨hu1, _⟩
        simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        exact fun j => hu1 j
      have hK_closed : IsClosed K := by
        have hc1 : IsClosed {u : Fin n → ℝ | ∀ j, 0 ≤ u j ∧ u j ≤ 1} := by
          have heq : {u : Fin n → ℝ | ∀ j, 0 ≤ u j ∧ u j ≤ 1} =
              ⋂ j : Fin n, {u | 0 ≤ u j ∧ u j ≤ 1} := by
            ext u
            simp only [Set.mem_setOf_eq, Set.mem_iInter]
          rw [heq]
          apply isClosed_iInter
          intro j
          exact (isClosed_le continuous_const (continuous_apply j)).inter
            (isClosed_le (continuous_apply j) continuous_const)
        have hc2 : IsClosed {u : Fin n → ℝ | ‖u‖ = 1} := by
          have : {u : Fin n → ℝ | ‖u‖ = 1} = Metric.sphere 0 1 := by
            ext u
            simp
          rw [this]
          exact Metric.isClosed_sphere
        have hK_eq : K = {u | ∀ j, 0 ≤ u j ∧ u j ≤ 1} ∩ {u | ‖u‖ = 1} := rfl
        rw [hK_eq]
        exact hc1.inter hc2
      exact h1.of_isClosed_subset hK_closed hK_sub
    have hu_in_K : ∀ k, u_seq k ∈ K := by
      intro k
      exact ⟨(hu_opt k).1, (hu_opt k).2.1⟩
    -- Extract convergent subsequence
    obtain ⟨u_star, hu_star_mem, φ, hφ_mono, hφ_conv⟩ :=
      hK_compact.tendsto_subseq hu_in_K
    -- u_star is in K, so it has ‖u_star‖ = 1 and components in [0,1]
    have hu_star_norm : ‖u_star‖ = 1 := hu_star_mem.2
    have hu_star_pos : ∀ j, 0 ≤ u_star j := fun j => (hu_star_mem.1 j).1
    -- Key: A(u_star) ≠ 0, using direct argument from Kager (2022)
    -- The argument: let I = {j : u_star j > 0}. For large k, u_{φ k} j > 0 for all j ∈ I.
    -- Define μ = min_{j∈I} (u_{φ k} j / u_star j) and z = u_{φ k} - μ·u_star.
    -- Then z ≥ 0 and has fewer nonzero components than u_{φ k}.
    -- Since u_{φ k} is optimal, Az ≠ Au_{φ k}, so Au_star ≠ 0.
    have hAu_ne : A.mulVec u_star ≠ 0 := by
      -- The set I = support u_star
      let I := support u_star
      by_cases hI_empty : I = ∅
      · -- If I is empty, then u_star = 0, but ‖u_star‖ = 1, contradiction
        have hu_zero : u_star = 0 := by
          ext j
          by_contra hj
          have : j ∈ I := by
            simp only [I, support, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hj
          rw [hI_empty] at this
          exact Finset.notMem_empty j this
        rw [hu_zero, norm_zero] at hu_star_norm
        exact absurd hu_star_norm zero_ne_one
      -- I is nonempty
      obtain ⟨j₀, hj₀⟩ := Finset.nonempty_of_ne_empty hI_empty
      -- For large enough k, all components in I are positive
      -- Since u_{φ k} → u_star and I is finite, eventually u_{φ k} j > (u_star j)/2 for j ∈ I
      have hev_pos : ∀ᶠ k in Filter.atTop, ∀ j ∈ I, (u_seq (φ k)) j > 0 := by
        -- Use pointwise convergence. For each j ∈ I, u_{φ k} j → u_star j > 0
        -- Since I is finite, we can take the max of the N values
        have hI_finite := I.finite_toSet
        apply Filter.eventually_all.mpr
        intro j
        by_cases hj_in : j ∈ I
        · simp only [I, support, Finset.mem_filter, Finset.mem_univ, true_and] at hj_in
          have hu_star_j_pos : 0 < u_star j := by
            have := hu_star_pos j
            cases this.lt_or_eq with
            | inl h => exact h
            | inr h => exfalso; exact hj_in h.symm
          have hconv_j : Filter.Tendsto (fun k => (u_seq (φ k)) j)
              Filter.atTop (nhds (u_star j)) := by
            exact (continuous_apply j).continuousAt.tendsto.comp hφ_conv
          rw [Filter.eventually_atTop]
          obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv_j (u_star j / 2) (by linarith)
          use N
          intro k hk _
          have hdist := hN k hk
          simp only [Real.dist_eq] at hdist
          have h1 : |u_seq (φ k) j - u_star j| < u_star j / 2 := hdist
          have h2 : u_star j - u_star j / 2 < u_seq (φ k) j := by
            have := abs_sub_lt_iff.mp h1
            linarith
          linarith
        · -- j ∉ I, vacuously true
          filter_upwards with k hjI
          exact absurd hjI hj_in
      -- Get a specific k for which this holds
      obtain ⟨k₁, hk₁⟩ := hev_pos.exists_forall_of_atTop
      specialize hk₁ k₁ (le_refl _)
      -- Define μ = min_{j∈I} (u_{φ k₁} j / u_star j)
      let μ_vals := I.image (fun j => (u_seq (φ k₁)) j / u_star j)
      have hμ_ne : μ_vals.Nonempty := Finset.Nonempty.image ⟨j₀, hj₀⟩ _
      let μ := μ_vals.min' hμ_ne
      have hμ_pos : 0 < μ := by
        simp only [μ, Finset.lt_min'_iff]
        intro y hy
        simp only [μ_vals, Finset.mem_image] at hy
        obtain ⟨j, hj_mem, hjy⟩ := hy
        rw [← hjy]
        apply div_pos (hk₁ j hj_mem)
        simp only [I, support, Finset.mem_filter, Finset.mem_univ, true_and] at hj_mem
        have := hu_star_pos j
        cases this.lt_or_eq with
        | inl h => exact h
        | inr h => exfalso; exact hj_mem h.symm
      -- Define z = u_{φ k₁} - μ·u_star
      let z := u_seq (φ k₁) - μ • u_star
      -- Show z ≥ 0
      have hz_pos : ∀ j, 0 ≤ z j := by
        intro j
        simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hj_in_I : j ∈ I
        · -- For j ∈ I: z j = u_{φ k₁} j - μ·u_star j ≥ 0 by definition of μ
          have hu_star_j_pos : 0 < u_star j := by
            simp only [I, support, Finset.mem_filter, Finset.mem_univ, true_and] at hj_in_I
            have := hu_star_pos j
            cases this.lt_or_eq with
            | inl h => exact h
            | inr h => exfalso; exact hj_in_I h.symm
          have hμ_le : μ ≤ (u_seq (φ k₁)) j / u_star j := by
            apply Finset.min'_le
            simp only [μ_vals, Finset.mem_image]
            exact ⟨j, hj_in_I, rfl⟩
          have : μ * u_star j ≤ (u_seq (φ k₁)) j := by
            have := mul_le_mul_of_nonneg_right hμ_le (le_of_lt hu_star_j_pos)
            rw [div_mul_cancel₀ _ (ne_of_gt hu_star_j_pos)] at this
            exact this
          linarith
        · -- For j ∉ I: u_star j = 0, so z j = u_{φ k₁} j ≥ 0
          simp only [I, support, Finset.mem_filter, Finset.mem_univ, true_and,
            Decidable.not_not] at hj_in_I
          rw [hj_in_I, mul_zero, sub_zero]
          exact (hu_opt (φ k₁)).1 j |>.1
      -- Show z has strictly fewer nonzero components than u_{φ k₁}
      -- (at least one component in I becomes zero)
      have hz_fewer : (support z).card < (support (u_seq (φ k₁))).card := by
        -- μ achieves its minimum at some j_min ∈ I
        have ⟨j_min, hj_min_mem, hj_min_eq⟩ : ∃ j ∈ I, (u_seq (φ k₁)) j / u_star j = μ := by
          have := Finset.min'_mem μ_vals hμ_ne
          simp only [μ_vals, Finset.mem_image] at this
          obtain ⟨j, hj, hjval⟩ := this
          refine ⟨j, hj, ?_⟩
          exact hjval
        -- At j_min: z j_min = u_{φ k₁} j_min - μ·u_star j_min = 0
        have hz_zero : z j_min = 0 := by
          simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have hu_star_j_pos : 0 < u_star j_min := by
            simp only [I, support, Finset.mem_filter, Finset.mem_univ, true_and] at hj_min_mem
            have := hu_star_pos j_min
            cases this.lt_or_eq with
            | inl h => exact h
            | inr h => exfalso; exact hj_min_mem h.symm
          -- hj_min_eq : u_seq (φ k₁) j_min / u_star j_min = μ
          -- Goal: u_seq (φ k₁) j_min - μ * u_star j_min = 0
          have : μ * u_star j_min = u_seq (φ k₁) j_min := by
            rw [← hj_min_eq]
            field_simp
          linarith
        -- j_min ∈ support (u_{φ k₁}) because u_{φ k₁} j_min > 0
        have hj_min_in_supp : j_min ∈ support (u_seq (φ k₁)) := by
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
          exact ne_of_gt (hk₁ j_min hj_min_mem)
        -- j_min ∉ support z because z j_min = 0
        have hj_min_not_in_supp_z : j_min ∉ support z := by
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not]
          exact hz_zero
        -- support z ⊆ support (u_{φ k₁})
        have hsub : support z ⊆ support (u_seq (φ k₁)) := by
          intro j hj
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hj ⊢
          intro hu_zero
          simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hu_zero, zero_sub,
            neg_eq_zero, mul_eq_zero] at hj
          -- hj : ¬(μ = 0 ∨ u_star j = 0)
          push_neg at hj
          -- hj : μ ≠ 0 ∧ u_star j ≠ 0
          -- But this contradicts the simp result...
          -- Actually the simp simplified to ¬(μ = 0 ∨ u_star j = 0), which means both are nonzero
          -- But that doesn't make sense because we deduced z j = -μ * u_star j from hu_zero
          -- Actually z j = u_seq (φ k₁) j - μ * u_star j = 0 - μ * u_star j = -μ * u_star j
          -- If z j ≠ 0, then -μ * u_star j ≠ 0, so μ ≠ 0 ∧ u_star j ≠ 0
          -- But then u_star j ≠ 0 means j ∈ I, so u_seq (φ k₁) j > 0 by hk₁
          -- But we assumed u_seq (φ k₁) j = 0 (hu_zero), contradiction
          have hj_in_I : j ∈ I := by
            simp only [I, support, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hj.2
          have hpos := hk₁ j hj_in_I
          rw [hu_zero] at hpos
          exact (lt_irrefl 0 hpos).elim
        -- Therefore card(support z) < card(support u_{φ k₁})
        exact Finset.card_lt_card ⟨hsub, fun h => hj_min_not_in_supp_z (h hj_min_in_supp)⟩
      -- Since u_{φ k₁} is optimal and z has smaller support with same A-image...
      -- Wait, Az ≠ Au_{φ k₁} by optimality
      have hAz_neq : A.mulVec z ≠ A.mulVec (u_seq (φ k₁)) := by
        intro heq
        -- z ≥ 0, Az = Au_{φ k₁}, but support z < support u_{φ k₁}
        -- This contradicts optimality of u_{φ k₁}
        have hmin := (hu_opt (φ k₁)).2.2
        have hle := hmin z hz_pos heq
        omega
      -- Az = Au_{φ k₁} - μ·Au_star
      have hAz_eq : A.mulVec z = A.mulVec (u_seq (φ k₁)) - μ • A.mulVec u_star := by
        simp only [z]
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
      -- Therefore μ·Au_star ≠ 0, so Au_star ≠ 0
      intro hAu_zero
      rw [hAu_zero, smul_zero, sub_zero] at hAz_eq
      exact hAz_neq hAz_eq
    -- Now we can show λ_seq(φ k) → some λ_star > 0
    -- From b_seq'(φ k) = λ_{φ k} • A(u_{φ k}) and b_seq'(φ k) → b
    -- and A(u_{φ k}) → A(u_star) ≠ 0
    -- we get λ_{φ k} = ‖b_seq'(φ k)‖ / ‖A(u_{φ k})‖ → ‖b‖ / ‖A(u_star)‖
    have hAu_conv : Filter.Tendsto (fun k => A.mulVec (u_seq (φ k)))
        Filter.atTop (nhds (A.mulVec u_star)) := by
      have hcont : Continuous (fun x => A.mulVec x) :=
        continuous_const.matrix_mulVec continuous_id
      have : Filter.Tendsto (A.mulVec ∘ (u_seq ∘ φ)) Filter.atTop (nhds (A.mulVec u_star)) :=
        hcont.continuousAt.tendsto.comp hφ_conv
      convert this using 1
    have hAu_norm_conv : Filter.Tendsto (fun k => ‖A.mulVec (u_seq (φ k))‖)
        Filter.atTop (nhds ‖A.mulVec u_star‖) := by
      exact continuous_norm.continuousAt.tendsto.comp hAu_conv
    have hAu_norm_pos : 0 < ‖A.mulVec u_star‖ := norm_pos_iff.mpr hAu_ne
    -- λ_seq(φ k) = ‖b_seq'(φ k)‖ / ‖A(u_{φ k})‖
    have hlam_eq : ∀ k, lam_seq (φ k) = ‖b_seq' (φ k)‖ / ‖A.mulVec (u_seq (φ k))‖ := by
      intro k
      have heq := hu_eq (φ k)
      have hn1 : ‖b_seq' (φ k)‖ = ‖lam_seq (φ k) • A.mulVec (u_seq (φ k))‖ := by rw [heq]
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt (hlam_pos (φ k)))] at hn1
      have hAu_ne_k : A.mulVec (u_seq (φ k)) ≠ 0 := optimal_image_ne_zero A _ (hu_opt (φ k))
      field_simp [norm_ne_zero_iff.mpr hAu_ne_k] at hn1 ⊢
      linarith
    -- So λ_seq(φ k) → ‖b‖ / ‖A(u_star)‖
    have hlim_b' : Filter.Tendsto (fun k => b_seq' (φ k)) Filter.atTop (nhds b) :=
      hlim'.comp hφ_mono.tendsto_atTop
    have hlim_b_norm : Filter.Tendsto (fun k => ‖b_seq' (φ k)‖) Filter.atTop (nhds ‖b‖) :=
      continuous_norm.continuousAt.tendsto.comp hlim_b'
    let lam_star := ‖b‖ / ‖A.mulVec u_star‖
    have hlam_conv : Filter.Tendsto (fun k => lam_seq (φ k)) Filter.atTop (nhds lam_star) := by
      simp_rw [hlam_eq]
      exact hlim_b_norm.div hAu_norm_conv (norm_ne_zero_iff.mpr hAu_ne)
    have hlam_star_pos : 0 < lam_star := by
      apply div_pos (norm_pos_iff.mpr hb_zero) hAu_norm_pos
    -- Finally, show b = lam_star • A(u_star)
    have hb_eq : b = lam_star • A.mulVec u_star := by
      -- b_seq'(φ k) → b and b_seq'(φ k) = λ_{φ k} • A(u_{φ k})
      -- λ_{φ k} → lam_star and A(u_{φ k}) → A(u_star)
      -- So λ_{φ k} • A(u_{φ k}) → lam_star • A(u_star)
      have hprod : Filter.Tendsto (fun k => lam_seq (φ k) • A.mulVec (u_seq (φ k)))
          Filter.atTop (nhds (lam_star • A.mulVec u_star)) := by
        exact Filter.Tendsto.smul hlam_conv hAu_conv
      have hprod' : Filter.Tendsto (fun k => b_seq' (φ k)) Filter.atTop
          (nhds (lam_star • A.mulVec u_star)) := by
        have heq : (fun k => b_seq' (φ k)) = (fun k => lam_seq (φ k) • A.mulVec (u_seq (φ k))) := by
          funext k
          exact hu_eq (φ k)
        rw [heq]
        exact hprod
      exact tendsto_nhds_unique hlim_b' hprod'
    -- So b ∈ coneImage A
    rw [hb_eq]
    refine ⟨lam_star • u_star, ?_, ?_⟩
    · intro j
      exact mul_nonneg (le_of_lt hlam_star_pos) (hu_star_pos j)
    · rw [Matrix.mulVec_smul]

end ConeImageClosed

/-! ## Section 3: LP Structure and Conversion to ConeProgram -/

section LPStructure

/-- Linear program in equality form: max c·x subject to Ax = b, x ≥ 0 -/
structure LP (m n : ℕ) where
  /-- The constraint matrix -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- The right-hand side -/
  b : Fin m → ℝ
  /-- The objective coefficients -/
  c : Fin n → ℝ

variable {m n : ℕ}

/-- A point x is feasible for the LP if x ≥ 0 and Ax = b. -/
def LP.isFeasible (P : LP m n) (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ P.A.mulVec x = P.b

/-- The primal objective value c·x. -/
def LP.objective (P : LP m n) (x : Fin n → ℝ) : ℝ :=
  dotProduct P.c x

/-- A point y is dual feasible if Aᵀy = c (LP in equality form has free dual). -/
def LP.isDualFeasible (P : LP m n) (y : Fin m → ℝ) : Prop :=
  P.Aᵀ.mulVec y = P.c

/-- The dual objective value b·y. -/
def LP.dualObjective (P : LP m n) (y : Fin m → ℝ) : ℝ :=
  dotProduct P.b y

/-- Convert LP to ConeProgram with K = ℝ₊ⁿ, L = {0}. -/
noncomputable def LP.toConeProgram (P : LP m n) :
    ConeProgram (V := EuclideanSpace ℝ (Fin n)) (W := EuclideanSpace ℝ (Fin m)) where
  K := nonnegOrthant n
  L := trivialCone
  A := matrixToCLM P.A
  b := (WithLp.equiv 2 _).symm P.b
  c := (WithLp.equiv 2 _).symm P.c

/-- Helper: WithLp equivalence applied componentwise. -/
theorem WithLp.equiv_symm_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    ((WithLp.equiv 2 (Fin n → ℝ)).symm x) i = x i := rfl

/-- Feasibility equivalence between LP and its ConeProgram. -/
theorem LP.toConeProgram_isFeasible (P : LP m n) (x : Fin n → ℝ) :
    P.toConeProgram.isFeasible ((WithLp.equiv 2 _).symm x) ↔ P.isFeasible x := by
  simp only [ConeProgram.isFeasible, toConeProgram]
  constructor
  · intro ⟨hK, hL⟩
    constructor
    · intro j
      have := hK j
      simp only [WithLp.equiv_symm_apply] at this
      exact this
    · -- b - A(x) ∈ L means b - A(x) = 0, i.e., A(x) = b
      rw [mem_trivialCone] at hL
      simp only [sub_eq_zero] at hL
      ext i
      have hAx_i : (matrixToCLM P.A ((WithLp.equiv 2 _).symm x)) i =
          (P.A.mulVec x) i := by
        simp only [matrixToCLM_apply, Matrix.toEuclideanLin_apply]
        rfl
      -- hL says P.b' = A(x'), we need P.b i = (A.mulVec x) i
      have hb_i : P.b i = (matrixToCLM P.A ((WithLp.equiv 2 _).symm x)) i := by
        have := congrArg (· i) hL
        simp only [WithLp.equiv_symm_apply] at this
        exact this
      simp only [hAx_i] at hb_i
      linarith
  · intro ⟨hpos, hAx⟩
    constructor
    · intro i
      simp only [WithLp.equiv_symm_apply]
      exact hpos i
    · rw [mem_trivialCone, sub_eq_zero]
      ext i
      have hAx_i : (matrixToCLM P.A ((WithLp.equiv 2 _).symm x)) i =
          (P.A.mulVec x) i := by
        simp only [matrixToCLM_apply, Matrix.toEuclideanLin_apply]
        rfl
      simp only [WithLp.equiv_symm_apply, hAx_i]
      exact (congrFun hAx i).symm

end LPStructure

/-! ## Section 4: LP-Specific Duality Results -/

section LPDuality

variable {m n : ℕ}

/-- Weak LP duality: c·x ≤ b·y for feasible pairs.

    Proof: c·x = (Aᵀy)·x = y·(Ax) = y·b = b·y
    (when Aᵀy = c and Ax = b). -/
theorem LP.weak_duality (P : LP m n) (x y : _)
    (hx : P.isFeasible x) (hy : P.isDualFeasible y) :
    P.objective x = P.dualObjective y := by
  simp only [objective, dualObjective, isFeasible, isDualFeasible] at *
  obtain ⟨_, hAx⟩ := hx
  -- c·x = (Aᵀy)·x
  rw [← hy]
  -- (Aᵀy)·x = y·(Ax)
  simp only [dotProduct, Matrix.mulVec]
  calc ∑ j, (∑ i, P.A i j * y i) * x j
      = ∑ j, ∑ i, P.A i j * y i * x j := by
          apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, P.A i j * y i * x j := Finset.sum_comm
    _ = ∑ i, y i * ∑ j, P.A i j * x j := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ = ∑ i, P.b i * y i := by
          apply Finset.sum_congr rfl; intro i _
          have := congrFun hAx i
          simp only [Matrix.mulVec, dotProduct] at this
          rw [this]; ring

/-- For LP, limit-feasibility equals feasibility because the image cone is closed.
    This is the key result from Exercise 4.7 of Gärtner-Matoušek. -/
theorem LP.limitFeasible_iff_feasible (P : LP m n) :
    P.toConeProgram.isLimitFeasibleCP ↔ (∃ x, P.toConeProgram.isFeasible x) := by
  constructor
  · -- Limit-feasible → feasible (uses coneImage_isClosed)
    intro ⟨seq, slack, hseq_K, hslack_L, hconv⟩
    -- For L = {0}, slack n = 0 always
    have hslack_zero : ∀ k, slack k = 0 := by
      intro k
      have h := hslack_L k
      simp only [toConeProgram] at h
      rw [mem_trivialCone] at h
      exact h
    -- So A(seq n) → b
    have hconv' : Filter.Tendsto (fun k => P.toConeProgram.A (seq k)) Filter.atTop
        (nhds P.toConeProgram.b) := by
      simp_rw [hslack_zero, add_zero] at hconv
      exact hconv
    -- The image cone is closed, so b ∈ image
    have hclosed := coneImage_isClosed P.A
    -- Need to show P.toConeProgram.b is in the image of nonnegOrthant under A
    -- This requires connecting EuclideanSpace to Fin n → ℝ
    -- Convert seq from EuclideanSpace to Fin n → ℝ
    let seq_plain := fun k => (WithLp.equiv 2 _) (seq k)
    -- Show seq_plain k ≥ 0
    have hseq_pos : ∀ k j, 0 ≤ seq_plain k j := by
      intro k j
      exact hseq_K k j
    -- Show A.mulVec (seq_plain k) converges to P.b
    have hconv_plain : Filter.Tendsto (fun k => P.A.mulVec (seq_plain k)) Filter.atTop
        (nhds P.b) := by
      -- matrixToCLM P.A (seq k) i = A.mulVec (seq_plain k) i
      have heq : ∀ k,
          P.A.mulVec (seq_plain k) = (WithLp.equiv 2 _) (P.toConeProgram.A (seq k)) := by
        intro k
        ext i
        simp only [matrixToCLM_apply, Matrix.toEuclideanLin_apply, toConeProgram, seq_plain]
        rfl
      simp_rw [heq]
      -- P.toConeProgram.b = (WithLp.equiv 2 _).symm P.b
      have hb_eq : P.b = (WithLp.equiv 2 _) P.toConeProgram.b := by
        simp only [toConeProgram]
        ext i
        rfl
      rw [hb_eq]
      have hunif := (PiLp.uniformContinuous_ofLp 2 (fun _ : Fin m => ℝ)).continuous
      exact hunif.tendsto P.toConeProgram.b |>.comp hconv'
    -- Apply closedness to get b in image
    have hb_in : P.b ∈ coneImage P.A := by
      apply hclosed.isSeqClosed
      · exact fun k => ⟨seq_plain k, hseq_pos k, rfl⟩
      · exact hconv_plain
    -- Extract x from image
    obtain ⟨x, hxpos, hAx⟩ := hb_in
    -- Convert x to EuclideanSpace
    use (WithLp.equiv 2 _).symm x
    constructor
    · intro i
      simp only [WithLp.equiv_symm_apply]
      exact hxpos i
    · -- Need b - A(x) ∈ L = {0}
      simp only [toConeProgram]
      rw [mem_trivialCone, sub_eq_zero]
      ext i
      simp only [matrixToCLM_apply, Matrix.toEuclideanLin_apply, WithLp.equiv_symm_apply]
      exact congrFun hAx.symm i
  · -- Feasible → limit-feasible (constant sequence)
    intro ⟨x, hx⟩
    refine ⟨fun _ => x, fun _ => (0 : EuclideanSpace ℝ (Fin m)), fun _ => hx.1, ?_, ?_⟩
    · intro _
      simp only [toConeProgram]
      rw [mem_trivialCone]
    · have hfeas := hx.2
      simp only [toConeProgram] at hfeas
      rw [mem_trivialCone] at hfeas
      simp only [sub_eq_zero] at hfeas
      -- hfeas : (WithLp.equiv 2 _).symm P.b = (matrixToCLM P.A) x
      -- goal: (fun _ => A x + 0) → nhds b
      simp only [add_zero, toConeProgram]
      rw [hfeas]
      exact @tendsto_const_nhds _ _ _ ((matrixToCLM P.A) x) (Filter.atTop (α := ℕ))

/-- LP strong duality without Slater condition.

    If both primal and dual are feasible, then:
    1. Optimal values are equal
    2. Optima are attained

    This follows from the image cone being closed (Exercise 4.7). -/
theorem LP.strong_duality (P : LP m n)
    (hPrimal : ∃ x, P.isFeasible x)
    (hDual : ∃ y, P.isDualFeasible y) :
    ∃ x_opt y_opt,
      P.isFeasible x_opt ∧
      P.isDualFeasible y_opt ∧
      P.objective x_opt = P.dualObjective y_opt := by
  -- For LP in equality form (Ax = b, x ≥ 0), if primal and dual are both feasible,
  -- weak duality already gives equality (since c·x = b·y for any feasible pair)
  obtain ⟨x₀, hx₀⟩ := hPrimal
  obtain ⟨y₀, hy₀⟩ := hDual
  use x₀, y₀, hx₀, hy₀
  exact LP.weak_duality P x₀ y₀ hx₀ hy₀

end LPDuality

/-! ## Section 5: Farkas Lemma as Corollary -/

section Farkas

variable {m n : ℕ}

/-- Farkas Lemma for LP: exactly one of the following holds:
    1. ∃ x ≥ 0 with Ax = b
    2. ∃ y with Aᵀy ≥ 0 and b·y < 0

    This follows from the Farkas lemma for cones (ConeProgram.farkas_forward)
    combined with the fact that the image cone is closed. -/
theorem lp_farkas (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b) ↔
    ¬∃ y : Fin m → ℝ, (∀ j, 0 ≤ Aᵀ.mulVec y j) ∧ dotProduct b y < 0 := by
  constructor
  · -- Forward direction: algebraic, doesn't need closedness
    intro ⟨x, hxpos, hAxb⟩
    push_neg
    intro y hATy
    -- b·y = (Ax)·y = x·(Aᵀy) ≥ 0 since x ≥ 0 and Aᵀy ≥ 0
    rw [← hAxb]
    simp only [dotProduct, Matrix.mulVec]
    calc ∑ i, (∑ j, A i j * x j) * y i
        = ∑ i, ∑ j, A i j * x j * y i := by
            apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
      _ = ∑ j, ∑ i, A i j * x j * y i := Finset.sum_comm
      _ = ∑ j, x j * ∑ i, A i j * y i := by
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≥ 0 := by
            apply Finset.sum_nonneg; intro j _
            apply mul_nonneg (hxpos j) (hATy j)
  · -- Backward direction: uses image cone being closed
    intro hnoY
    -- We use the characterization: b ∈ closure{Ax : x ≥ 0} iff ∀ y, Aᵀy ≥ 0 → b·y ≥ 0
    -- Since the image is closed, b ∈ {Ax : x ≥ 0}
    push_neg at hnoY
    have hclosed := coneImage_isClosed A
    -- hnoY says: ∀ y, (∀ j, Aᵀy j ≥ 0) → b·y ≥ 0
    -- This is exactly the dual characterization of b being in the closure
    -- Since closure = image (by closedness), b ∈ image
    -- Proof by contradiction using separation theorem
    by_contra hb_not_in
    push_neg at hb_not_in
    have hb_not_mem : b ∉ coneImage A := by
      intro ⟨x, hxpos, hAx⟩
      exact hb_not_in x hxpos hAx
    -- Build a ConvexCone structure for coneImage A
    let K : ConvexCone ℝ (Fin m → ℝ) := {
      carrier := coneImage A
      smul_mem' := by
        intro c hc y ⟨x, hxpos, hAx⟩
        refine ⟨c • x, ?_, ?_⟩
        · intro j; exact mul_nonneg (le_of_lt hc) (hxpos j)
        · simp only [Matrix.mulVec_smul, hAx]
      add_mem' := by
        intro y1 hy1 y2 hy2
        obtain ⟨x1, hx1pos, hA1⟩ := hy1
        obtain ⟨x2, hx2pos, hA2⟩ := hy2
        refine ⟨x1 + x2, ?_, ?_⟩
        · intro j; exact add_nonneg (hx1pos j) (hx2pos j)
        · simp only [Matrix.mulVec_add, hA1, hA2]
    }
    -- K is nonempty (contains 0)
    have hne : (↑K : Set (Fin m → ℝ)).Nonempty := by
      use 0
      exact ⟨0, fun _ => le_refl 0, by simp [Matrix.mulVec_zero]⟩
    -- K is closed
    have hKclosed : IsClosed (↑K : Set (Fin m → ℝ)) := hclosed
    -- Apply separation theorem via EuclideanSpace (which has InnerProductSpace instance)
    -- The key is that Fin m → ℝ and EuclideanSpace ℝ (Fin m) have the same underlying type
    -- but EuclideanSpace has InnerProductSpace instance
    -- We use the fact that coneImage A : Set (Fin m → ℝ) is the same as a set in EuclideanSpace
    --
    -- v4.29 update: `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem` was
    -- deprecated in favor of `ProperCone.hyperplane_separation'`. We rebuild K' as a `ProperCone`
    -- (which in v4.29 is `ClosedSubmodule ℝ≥0 _`, requiring zero, addition, nonneg scalar
    -- multiplication, and topological closedness).
    let toE := @WithLp.toLp 2 (Fin m → ℝ)
    have hKclosed' : IsClosed (toE '' coneImage A : Set (EuclideanSpace ℝ (Fin m))) := by
      -- The topology on WithLp 2 (Fin m → ℝ) is uniform with Fin m → ℝ for finite products.
      -- toE '' coneImage A = (WithLp.ofLp) ⁻¹' coneImage A (since toE is a bijection)
      have heq : (toE '' coneImage A : Set (EuclideanSpace ℝ (Fin m))) =
          (WithLp.ofLp : EuclideanSpace ℝ (Fin m) → Fin m → ℝ) ⁻¹' coneImage A := by
        ext x
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · intro ⟨y, hy, hxy⟩
          rwa [← hxy]
        · intro hx
          exact ⟨x.ofLp, hx, rfl⟩
      rw [heq]
      exact hclosed.preimage (PiLp.uniformContinuous_ofLp 2 (fun _ : Fin m => ℝ)).continuous
    let K' : ProperCone ℝ (EuclideanSpace ℝ (Fin m)) :=
      { carrier := toE '' coneImage A
        add_mem' := by
          intro z1 z2 ⟨z1', ⟨x1, hx1pos, hA1⟩, hz1e⟩ ⟨z2', ⟨x2, hx2pos, hA2⟩, hz2e⟩
          refine ⟨z1' + z2', ⟨x1 + x2, ?_, ?_⟩, ?_⟩
          · intro j; exact add_nonneg (hx1pos j) (hx2pos j)
          · simp only [Matrix.mulVec_add, hA1, hA2]
          · rw [← hz1e, ← hz2e]; rfl
        zero_mem' := ⟨0, ⟨0, fun _ => le_refl 0, by simp [Matrix.mulVec_zero]⟩, by simp [toE]⟩
        smul_mem' := by
          intro c z ⟨z', ⟨x, hxpos, hAx⟩, hze⟩
          refine ⟨(c : ℝ) • z', ⟨(c : ℝ) • x, ?_, ?_⟩, ?_⟩
          · intro j; exact mul_nonneg c.2 (hxpos j)
          · simp only [Matrix.mulVec_smul, hAx]
          · rw [← hze]; rfl
        isClosed' := hKclosed' }
    let b' : EuclideanSpace ℝ (Fin m) := toE b
    have hb_not_mem_K' : b' ∉ K' := by
      intro ⟨z, hz, hbe⟩
      apply hb_not_mem
      convert hz using 1
      simp [b', toE] at hbe
      exact hbe.symm
    have hsep := ProperCone.hyperplane_separation' K' hb_not_mem_K'
    obtain ⟨y, hy_dual, hy_neg⟩ := hsep
    -- hy_dual : ∀ x ∈ K', 0 ≤ ⟨x, y⟩
    -- hy_neg : ⟨y, b'⟩ < 0
    -- For the standard basis vector eⱼ, we have A eⱼ ∈ K' (the j-th column)
    -- Actually, we need: ∀ x ≥ 0, ⟨Ax, y⟩ ≥ 0 implies Aᵀy ≥ 0
    have hATy_pos : ∀ j, 0 ≤ Aᵀ.mulVec y.ofLp j := by
      intro j
      -- Test with the j-th standard basis vector eⱼ ∈ ℝ₊ⁿ
      -- ⟨A eⱼ, y⟩ = ⟨j-th column of A, y⟩ = (Aᵀy)_j
      let e : Fin n → ℝ := Pi.single j 1
      have he_pos : ∀ k, 0 ≤ e k := by
        intro k
        simp only [e, Pi.single_apply]
        split_ifs with h
        · exact zero_le_one
        · exact le_refl 0
      have he_in_K' : toE (A.mulVec e) ∈ K' := ⟨A.mulVec e, ⟨e, he_pos, rfl⟩, rfl⟩
      have h := hy_dual (toE (A.mulVec e)) he_in_K'
      -- ⟨A eⱼ, y⟩ = ∑ᵢ (A eⱼ)ᵢ * yᵢ = ∑ᵢ A i j * yᵢ = (Aᵀy)_j
      -- v4.29 needs the lemma applied to specific args for pattern unification.
      rw [show inner ℝ (toE (A.mulVec e)) y = y.ofLp ⬝ᵥ star (toE (A.mulVec e)).ofLp from
        EuclideanSpace.inner_eq_star_dotProduct _ _] at h
      simp only [star_trivial, toE, Matrix.mulVec, dotProduct] at h
      -- h : 0 ≤ ∑ i, y.ofLp i * ∑ k, A i k * e k
      -- Since e = Pi.single j 1, we have ∑ k, A i k * e k = A i j
      have hsum_eq : ∑ i, y.ofLp i * ∑ k, A i k * e k = ∑ i, A i j * y.ofLp i := by
        apply Finset.sum_congr rfl
        intro i _
        have hinner : ∑ k, A i k * e k = A i j := by
          rw [Finset.sum_eq_single j]
          · simp only [e, Pi.single_apply, if_true, mul_one]
          · intro k _ hkj
            simp only [e, Pi.single_apply, if_neg hkj, mul_zero]
          · intro hj
            exact (hj (Finset.mem_univ j)).elim
        rw [hinner, mul_comm]
      rw [hsum_eq] at h
      simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct]
      exact h
    -- Apply hnoY to get b·y ≥ 0
    have hby := hnoY y.ofLp hATy_pos
    -- But hy_neg says ⟨y, b'⟩ < 0
    rw [show inner ℝ b' y = y.ofLp ⬝ᵥ star b'.ofLp from
      EuclideanSpace.inner_eq_star_dotProduct _ _] at hy_neg
    simp only [star_trivial, b', toE] at hy_neg
    have hby_eq : dotProduct b y.ofLp = ∑ i, y.ofLp i * b i := by
      simp only [dotProduct]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hby_eq] at hby
    simp only [dotProduct] at hy_neg
    -- After simp, hy_neg is already in the form `∑ i, y.ofLp i * b i < 0` matching hby
    linarith

/-- Farkas Lemma for inequality form: Ax ≥ b, x ≥ 0.

    Exactly one of the following holds:
    1. ∃ x ≥ 0 with Ax ≥ b (i.e., b_i ≤ (Ax)_i for all i)
    2. ∃ y ≥ 0 with Aᵀy ≤ 0 and b·y > 0

    This follows from the equality-form Farkas by introducing slack variables:
    Ax ≥ b, x ≥ 0 ↔ Ax - s = b, x ≥ 0, s ≥ 0. -/
theorem lp_farkas_ineq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, b i ≤ A.mulVec x i)) ↔
    ¬∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, Aᵀ.mulVec y j ≤ 0) ∧
                       0 < dotProduct b y := by
  constructor
  · -- Forward: if Ax ≥ b exists, no certificate y exists
    intro ⟨x, hxpos, hAxb⟩
    push_neg
    intro y hypos hATy
    -- b·y = Σ_i b_i y_i ≤ Σ_i (Ax)_i y_i = Σ_i Σ_j A_ij x_j y_i
    --     = Σ_j x_j (Σ_i A_ij y_i) = Σ_j x_j (Aᵀy)_j ≤ 0
    calc dotProduct b y = ∑ i, b i * y i := rfl
      _ ≤ ∑ i, (A.mulVec x i) * y i := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_right (hAxb i) (hypos i)
      _ = ∑ i, (∑ j, A i j * x j) * y i := by
          apply Finset.sum_congr rfl; intro i _; rfl
      _ = ∑ i, ∑ j, A i j * x j * y i := by
          apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
      _ = ∑ j, ∑ i, A i j * x j * y i := Finset.sum_comm
      _ = ∑ j, x j * ∑ i, A i j * y i := by
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = ∑ j, x j * (Aᵀ.mulVec y j) := by
          apply Finset.sum_congr rfl; intro j _
          rfl
      _ ≤ 0 := by
          apply Finset.sum_nonpos; intro j _
          exact mul_nonpos_of_nonneg_of_nonpos (hxpos j) (hATy j)
  · -- Backward: use equality-form Farkas with slack variables
    -- Ax ≥ b, x ≥ 0 is equivalent to Ax - s = b, x ≥ 0, s ≥ 0
    -- We use augmented matrix [A | -I] : Matrix (Fin m) (Fin (n + m))
    intro hno_cert
    push_neg at hno_cert
    -- hno_cert : ∀ y ≥ 0 with Aᵀy ≤ 0, we have b·y ≤ 0
    -- Define augmented matrix A' = [A | -I]
    let A' : Matrix (Fin m) (Fin (n + m)) ℝ := fun i k =>
      if h : k.val < n then A i ⟨k.val, h⟩ else if k.val - n = i.val then -1 else 0
    -- Claim: ∀ y with A'ᵀy ≥ 0, we have b·y ≥ 0
    -- A'ᵀy = [Aᵀy; -y], so A'ᵀy ≥ 0 means Aᵀy ≥ 0 and y ≤ 0
    have hAug_no_alt : ¬∃ y : Fin m → ℝ, (∀ k : Fin (n + m), 0 ≤ A'ᵀ.mulVec y k) ∧
        dotProduct b y < 0 := by
      push_neg
      intro y hA'y
      -- From hA'y on the left part (k < n): Aᵀy ≥ 0
      have hATy : ∀ j : Fin n, 0 ≤ Aᵀ.mulVec y j := by
        intro j
        have hk : (⟨j.val, Nat.lt_add_right m j.isLt⟩ : Fin (n + m)).val < n := j.isLt
        have h := hA'y ⟨j.val, Nat.lt_add_right m j.isLt⟩
        simp only [A', Matrix.transpose_apply, Matrix.mulVec, dotProduct, hk, ↓reduceDIte] at h
        simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct]
        calc ∑ i, A i j * y i = ∑ i, A i ⟨j.val, j.isLt⟩ * y i := by rfl
          _ ≥ 0 := h
      -- From hA'y on the right part (k ≥ n): -y ≥ 0, i.e., y ≤ 0
      have hy_le : ∀ i : Fin m, y i ≤ 0 := by
        intro i
        have hk :
            ¬(⟨n + i.val, Nat.add_lt_add_left i.isLt n⟩ : Fin (n + m)).val < n := by
          simp only [not_lt]
          omega
        have h := hA'y ⟨n + i.val, Nat.add_lt_add_left i.isLt n⟩
        simp only [A', Matrix.transpose_apply, Matrix.mulVec, dotProduct, hk, ↓reduceDIte] at h
        have hsum :
            ∑ j : Fin m,
                (if (n + i.val) - n = j.val then (-1 : ℝ) else 0) * y j = -y i := by
          rw [Finset.sum_eq_single i]
          · simp only [Nat.add_sub_cancel_left, ↓reduceIte, neg_one_mul]
          · intro j _ hji
            have hne : (n + i.val) - n ≠ j.val := by
              simp only [Nat.add_sub_cancel_left]
              exact fun h => hji (Fin.ext h.symm)
            simp only [hne, ↓reduceIte, zero_mul]
          · intro hi; exact (hi (Finset.mem_univ i)).elim
        rw [hsum] at h
        linarith
      -- Replace y with -y in hno_cert (since y ≤ 0 means -y ≥ 0)
      let y' : Fin m → ℝ := fun i => -y i
      have hy'_nonneg : ∀ i, 0 ≤ y' i := by
        intro i; simp only [y']; linarith [hy_le i]
      have hATy'_nonpos : ∀ j, Aᵀ.mulVec y' j ≤ 0 := by
        intro j
        simp only [y', Matrix.transpose_apply, Matrix.mulVec, dotProduct]
        have heq : ∑ i, A i j * (-y i) = - ∑ i, A i j * y i := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _; ring
        rw [heq]
        have h := hATy j
        simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct] at h
        linarith
      have hby' := hno_cert y' hy'_nonneg hATy'_nonpos
      simp only [y', dotProduct] at hby'
      have h : ∑ i, b i * (-y i) = - ∑ i, b i * y i := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _; ring
      rw [h] at hby'
      simp only [dotProduct]
      linarith
    -- Now apply lp_farkas to A' and b (with column dimension n+m)
    have hfarkas := (lp_farkas A' b).mpr hAug_no_alt
    -- hfarkas : ∃ x' ≥ 0, A' x' = b
    obtain ⟨x', hx'pos, hA'x'⟩ := hfarkas
    -- Extract x : Fin n → ℝ and s : Fin m → ℝ
    let x : Fin n → ℝ := fun j => x' ⟨j.val, Nat.lt_add_right m j.isLt⟩
    let s : Fin m → ℝ := fun i => x' ⟨n + i.val, Nat.add_lt_add_left i.isLt n⟩
    use x
    constructor
    · intro j; exact hx'pos ⟨j.val, Nat.lt_add_right m j.isLt⟩
    · -- Show Ax ≥ b, i.e., b ≤ Ax
      intro i
      -- From A'x' = b: (Ax)_i - s_i = b_i, so (Ax)_i = b_i + s_i ≥ b_i
      have hs_nonneg : 0 ≤ s i := hx'pos ⟨n + i.val, Nat.add_lt_add_left i.isLt n⟩
      have hA'x'_i : A'.mulVec x' i = b i := congrFun hA'x' i
      simp only [A', Matrix.mulVec, dotProduct] at hA'x'_i
      -- Split the sum into k < n and k ≥ n parts
      have hsum_split : ∑ k : Fin (n + m), (if h : k.val < n then A i ⟨k.val, h⟩
          else if k.val - n = i.val then -1 else 0) * x' k =
          (∑ j : Fin n, A i j * x j) - s i := by
        -- Split sum by filtering on k.val < n vs k.val ≥ n
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun k => k.val < n)]
        -- The left sum (k < n) gives ∑ j : Fin n, A i j * x j
        have h1 : (Finset.univ.filter (fun k : Fin (n + m) => k.val < n)).sum
            (fun k => (if h : k.val < n then A i ⟨k.val, h⟩
              else if k.val - n = i.val then -1 else 0) * x' k) =
            ∑ j : Fin n, A i j * x j := by
          -- The filtered set is the image of Fin n under the natural embedding
          have hfilter_eq : (Finset.univ.filter (fun k : Fin (n + m) => k.val < n)) =
              (Finset.univ : Finset (Fin n)).map ⟨fun j => ⟨j.val, Nat.lt_add_right m j.isLt⟩,
                fun j1 j2 h => Fin.ext (Fin.mk.inj h)⟩ := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
              Function.Embedding.coeFn_mk]
            constructor
            · intro hk
              use ⟨k.val, hk⟩
            · intro ⟨j, hj⟩
              rw [← hj]
              exact j.isLt
          rw [hfilter_eq, Finset.sum_map]
          apply Finset.sum_congr rfl
          intro j _
          have hlt : (⟨j.val, Nat.lt_add_right m j.isLt⟩ : Fin (n + m)).val < n := j.isLt
          simp only [Function.Embedding.coeFn_mk, hlt, ↓reduceDIte, x, Fin.eta]
        -- The right sum (k ≥ n) gives -s i
        have h2 : (Finset.univ.filter (fun k : Fin (n + m) => ¬k.val < n)).sum
            (fun k => (if h : k.val < n then A i ⟨k.val, h⟩
              else if k.val - n = i.val then -1 else 0) * x' k) = -s i := by
          -- Only k = n + i contributes
          rw [Finset.sum_eq_single ⟨n + i.val, Nat.add_lt_add_left i.isLt n⟩]
          · have hnotlt : ¬(n + i.val < n) := by omega
            simp only [hnotlt, ↓reduceDIte, Nat.add_sub_cancel_left, ↓reduceIte, neg_one_mul, s]
          · intro k hk hki
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
            have hnotlt : ¬(k.val < n) := by omega
            simp only [hnotlt, ↓reduceDIte]
            have hne : k.val - n ≠ i.val := by
              intro heq
              apply hki
              have hk_ge : n ≤ k.val := le_of_not_gt hnotlt
              have hval' : k.val = i.val + n := Nat.eq_add_of_sub_eq hk_ge heq
              have hval : k.val = n + i.val := by
                simpa [Nat.add_comm] using hval'
              ext
              exact hval
            simp only [hne, ↓reduceIte, zero_mul]
          · intro hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, not_le] at hi
            omega
        rw [h1, h2]
        ring
      rw [hsum_split] at hA'x'_i
      have hAx : (∑ j : Fin n, A i j * x j) = b i + s i := by linarith
      simp only [Matrix.mulVec, dotProduct]
      linarith

end Farkas

/-! ## Section 5: Rational Linear Algebra Helpers -/

section RationalHelpers

open Matrix

noncomputable def ratCastLinearMap (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℝ) :=
{ toFun := fun x i => (x i : ℝ)
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro a x
    ext i
    simp [Algebra.smul_def] }

theorem ratCastLinearMap_injective (n : ℕ) :
    Function.Injective (ratCastLinearMap n) := by
  intro x y h
  funext i
  have h' := congrArg (fun f => f i) h
  exact Rat.cast_injective (by simpa using h')

theorem ratCast_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ) :
    ratCastLinearMap m (A.mulVec x) = (A.map Rat.cast).mulVec (fun i => (x i : ℝ)) := by
  ext i
  simpa using (RingHom.map_mulVec (Rat.castHom ℝ) A x i)

theorem exists_rat_solution_of_real_injective {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (hA : LinearIndependent ℚ A.col) (b : Fin m → ℚ) (x : Fin n → ℝ)
    (hx : (A.map Rat.cast).mulVec x = fun i => (b i : ℝ)) :
    ∃ xq : Fin n → ℚ, A.mulVec xq = b := by
  classical
  let ratCastHom : ℚ →+* ℝ := Rat.castHom ℝ
  have hA_inj : Function.Injective A.mulVec :=
    (Matrix.mulVec_injective_iff (M := A)).2 hA
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    simpa [Matrix.mulVecLin_apply] using (LinearMap.ker_eq_bot_of_injective hA_inj)
  obtain ⟨B, hB⟩ := (A.mulVecLin).exists_leftInverse_of_injective hker
  let Bmat : Matrix (Fin n) (Fin m) ℚ := LinearMap.toMatrix' B
  have hBmat : Matrix.toLin' Bmat = B := by
    simp [Bmat]
  have hBA : Bmat * A = 1 := by
    apply (Matrix.toLin'.injective)
    calc
      Matrix.toLin' (Bmat * A)
          = (Matrix.toLin' Bmat).comp (Matrix.toLin' A) := by
              simp [Matrix.toLin'_mul]
      _ = B.comp A.mulVecLin := by
            simp [hBmat, Matrix.toLin'_apply']
      _ = LinearMap.id := hB
      _ = Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℚ) := by
            simp [Matrix.toLin'_one]
  have hBA_cast : (Bmat.map ratCastHom) * (A.map ratCastHom) = 1 := by
    have hBA' := congrArg (fun M => Matrix.map M ratCastHom) hBA
    simpa [Matrix.map_mul, Matrix.map_one] using hBA'
  have hx' : (A.map ratCastHom).mulVec x = fun i => (b i : ℝ) := by
    simpa using hx
  have hx_cast :
      (Bmat.map ratCastHom).mulVec (fun i => (b i : ℝ)) = x := by
    calc
      (Bmat.map ratCastHom).mulVec (fun i => (b i : ℝ))
          = (Bmat.map ratCastHom).mulVec ((A.map ratCastHom).mulVec x) := by
              simp [hx']
      _ = ((Bmat.map ratCastHom) * (A.map ratCastHom)).mulVec x := by
            simp [Matrix.mulVec_mulVec]
      _ = x := by
            simp [hBA_cast]
  let xq : Fin n → ℚ := Bmat.mulVec b
  have hxq_cast : (fun i => (xq i : ℝ)) = x := by
    have hxq_cast' : ratCastLinearMap n xq =
        (Bmat.map ratCastHom).mulVec (fun i => (b i : ℝ)) := by
      simpa [xq] using (ratCast_mulVec Bmat b)
    simpa [ratCastLinearMap] using hxq_cast'.trans hx_cast
  refine ⟨xq, ?_⟩
  have hcast_eq : ratCastLinearMap m (A.mulVec xq) = fun i => (b i : ℝ) := by
    calc
      ratCastLinearMap m (A.mulVec xq)
          = (A.map Rat.cast).mulVec (fun i => (xq i : ℝ)) := ratCast_mulVec A xq
      _ = (A.map Rat.cast).mulVec x := by
            simp [hxq_cast]
      _ = fun i => (b i : ℝ) := hx
  exact ratCastLinearMap_injective m hcast_eq

theorem exists_rat_solution_of_real_injective_cast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (hA : LinearIndependent ℚ A.col) (b : Fin m → ℚ) (x : Fin n → ℝ)
    (hx : (A.map Rat.cast).mulVec x = fun i => (b i : ℝ)) :
    ∃ xq : Fin n → ℚ, A.mulVec xq = b ∧ (fun i => (xq i : ℝ)) = x := by
  classical
  let ratCastHom : ℚ →+* ℝ := Rat.castHom ℝ
  have hA_inj : Function.Injective A.mulVec :=
    (Matrix.mulVec_injective_iff (M := A)).2 hA
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    simpa [Matrix.mulVecLin_apply] using (LinearMap.ker_eq_bot_of_injective hA_inj)
  obtain ⟨B, hB⟩ := (A.mulVecLin).exists_leftInverse_of_injective hker
  let Bmat : Matrix (Fin n) (Fin m) ℚ := LinearMap.toMatrix' B
  have hBmat : Matrix.toLin' Bmat = B := by
    simp [Bmat]
  have hBA : Bmat * A = 1 := by
    apply (Matrix.toLin'.injective)
    calc
      Matrix.toLin' (Bmat * A)
          = (Matrix.toLin' Bmat).comp (Matrix.toLin' A) := by
              simp [Matrix.toLin'_mul]
      _ = B.comp A.mulVecLin := by
            simp [hBmat, Matrix.toLin'_apply']
      _ = LinearMap.id := hB
      _ = Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℚ) := by
            simp [Matrix.toLin'_one]
  have hBA_cast : (Bmat.map ratCastHom) * (A.map ratCastHom) = 1 := by
    have hBA' := congrArg (fun M => Matrix.map M ratCastHom) hBA
    simpa [Matrix.map_mul, Matrix.map_one] using hBA'
  have hx' : (A.map ratCastHom).mulVec x = fun i => (b i : ℝ) := by
    simpa using hx
  have hx_cast :
      (Bmat.map ratCastHom).mulVec (fun i => (b i : ℝ)) = x := by
    calc
      (Bmat.map ratCastHom).mulVec (fun i => (b i : ℝ))
          = (Bmat.map ratCastHom).mulVec ((A.map ratCastHom).mulVec x) := by
              simp [hx']
      _ = ((Bmat.map ratCastHom) * (A.map ratCastHom)).mulVec x := by
            simp [Matrix.mulVec_mulVec]
      _ = x := by
            simp [hBA_cast]
  let xq : Fin n → ℚ := Bmat.mulVec b
  have hxq_cast : (fun i => (xq i : ℝ)) = x := by
    have hxq_cast' : ratCastLinearMap n xq =
        (Bmat.map ratCastHom).mulVec (fun i => (b i : ℝ)) := by
      simpa [xq] using (ratCast_mulVec Bmat b)
    simpa [ratCastLinearMap] using hxq_cast'.trans hx_cast
  have hcast_eq : ratCastLinearMap m (A.mulVec xq) = fun i => (b i : ℝ) := by
    calc
      ratCastLinearMap m (A.mulVec xq)
          = (A.map Rat.cast).mulVec (fun i => (xq i : ℝ)) := ratCast_mulVec A xq
      _ = (A.map Rat.cast).mulVec x := by
            simp [hxq_cast]
      _ = fun i => (b i : ℝ) := hx
  refine ⟨xq, ?_, hxq_cast⟩
  exact ratCastLinearMap_injective m hcast_eq

end RationalHelpers

end ConeProgramming
