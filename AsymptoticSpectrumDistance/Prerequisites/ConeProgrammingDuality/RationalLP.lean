/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.LP

/-!
# Rational LP setup

Rational LP data, basic helper lemmas, and the main rational-optimality
theorem `RationalLP.exists_rat_optimal`.
-/

namespace ConeProgramming

section RationalLP

variable {m n : ℕ}

/-- Rational LP data: max c·x subject to Ax = b, x ≥ 0. -/
structure RationalLP (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℚ
  b : Fin m → ℚ
  c : Fin n → ℚ

/-- Cast a rational LP to a real LP. -/
def RationalLP.toLP (P : RationalLP m n) : LP m n :=
  { A := P.A.map Rat.cast
    b := fun i => (P.b i : ℝ)
    c := fun j => (P.c j : ℝ) }

def RationalLP.isFeasible (P : RationalLP m n) (x : Fin n → ℚ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ P.A.mulVec x = P.b

private lemma RationalLP.feasible_cast {P : RationalLP m n} (x : Fin n → ℚ)
    (hx : P.isFeasible x) : P.toLP.isFeasible (fun j => (x j : ℝ)) := by
  constructor
  · intro j
    exact Rat.cast_nonneg.mpr (hx.1 j)
  · have hmul := ratCast_mulVec (A := P.A) (x := x)
    have hmul' :
        (P.A.map Rat.cast).mulVec (fun j => (x j : ℝ)) =
          fun i => ((P.A.mulVec x) i : ℝ) := by
      simpa [ratCastLinearMap] using hmul.symm
    simpa [RationalLP.toLP, hx.2] using hmul'

noncomputable def restrictSupport {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → ℝ) : Fin S.card → ℝ :=
  fun j => x ((Finset.equivFin S).symm j)

noncomputable def extendSupport {n : ℕ} (S : Finset (Fin n))
    (u : Fin S.card → ℝ) : Fin n → ℝ :=
  fun j => if h : j ∈ S then u (Finset.equivFin S ⟨j, h⟩) else 0

private lemma restrict_extend_support {n : ℕ} (S : Finset (Fin n))
    (u : Fin S.card → ℝ) :
    restrictSupport S (extendSupport S u) = u := by
  classical
  ext j
  simp [restrictSupport, extendSupport]

private lemma extend_support_eq_zero {n : ℕ} (S : Finset (Fin n))
    (u : Fin S.card → ℝ) (j : Fin n) (hj : j ∉ S) :
    extendSupport S u j = 0 := by
  simp [extendSupport, hj]

noncomputable def submatrixSupport (A : Matrix (Fin m) (Fin n) ℚ)
    (S : Finset (Fin n)) : Matrix (Fin m) (Fin S.card) ℚ :=
  fun i j => A i ((Finset.equivFin S).symm j)

private lemma submatrixSupport_mulVec_eq {A : Matrix (Fin m) (Fin n) ℚ}
    (S : Finset (Fin n)) (u : Fin S.card → ℝ) :
    ((submatrixSupport A S).map Rat.cast).mulVec u =
      (A.map Rat.cast).mulVec (extendSupport S u) := by
  classical
  ext i
  have hsum_univ :
      (A.map Rat.cast).mulVec (extendSupport S u) i =
        S.sum (fun j => (A.map Rat.cast) i j * extendSupport S u j) := by
    have hsum :
        (∑ j ∈ S, (A.map Rat.cast) i j * extendSupport S u j) =
          ∑ j ∈ (Finset.univ : Finset (Fin n)),
            (A.map Rat.cast) i j * extendSupport S u j := by
      refine Finset.sum_subset ?_ ?_
      · intro j _
        exact Finset.mem_univ j
      · intro j _ hjnot
        simp [extend_support_eq_zero (S := S) (u := u) (j := j) hjnot]
    simpa [Matrix.mulVec, dotProduct] using hsum.symm
  have hsum_attach' :
      (S.attach).sum (fun j => (A.map Rat.cast) i j * extendSupport S u j) =
        S.sum (fun j => (A.map Rat.cast) i j * extendSupport S u j) := by
    simpa using (Finset.sum_attach (s := S)
      (f := fun j => (A.map Rat.cast) i j * extendSupport S u j))
  have hsum_attach :
      (S.attach).sum (fun j => (A.map Rat.cast) i j * extendSupport S u j) =
        (S.attach).sum (fun j => (A.map Rat.cast) i j * u ((Finset.equivFin S) j)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [extendSupport, j.property]
  have hsum_equiv :
      (S.attach).sum (fun j => (A.map Rat.cast) i j * u ((Finset.equivFin S) j)) =
        ∑ j : Fin S.card,
          (A.map Rat.cast) i ((Finset.equivFin S).symm j) * u j := by
    simpa using
      (Finset.sum_equiv (Finset.equivFin S)
        (s := S.attach)
        (t := (Finset.univ : Finset (Fin S.card)))
        (f := fun j =>
          (A.map Rat.cast) i j * u ((Finset.equivFin S) j))
        (g := fun j =>
          (A.map Rat.cast) i ((Finset.equivFin S).symm j) * u j)
        (by intro j; simp)
        (by intro j _; simp))
  calc
    ((submatrixSupport A S).map Rat.cast).mulVec u i
        = ∑ j : Fin S.card,
            (A.map Rat.cast) i ((Finset.equivFin S).symm j) * u j := by
              simp [submatrixSupport, Matrix.mulVec, dotProduct]
    _ =
        (S.attach).sum
          (fun j => (A.map Rat.cast) i j * u ((Finset.equivFin S) j)) := by
          simpa using hsum_equiv.symm
    _ = S.sum (fun j => (A.map Rat.cast) i j * extendSupport S u j) := by
          exact (hsum_attach'.symm.trans hsum_attach).symm
    _ = (A.map Rat.cast).mulVec (extendSupport S u) i := hsum_univ.symm

noncomputable def posIndexSet {n : ℕ} (y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.filter (fun j => 0 < y j) Finset.univ

noncomputable def minPosRatio {n : ℕ} (x y : Fin n → ℝ)
    (hpos : (posIndexSet y).Nonempty) : ℝ :=
  ((posIndexSet y).image (fun j => x j / y j)).min'
    (Finset.Nonempty.image hpos _)

private lemma minPosRatio_le {n : ℕ} (x y : Fin n → ℝ)
    (hpos : (posIndexSet y).Nonempty) {j : Fin n} (hj : j ∈ posIndexSet y) :
    minPosRatio x y hpos ≤ x j / y j := by
  classical
  have hj' : x j / y j ∈ (posIndexSet y).image (fun j => x j / y j) := by
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  exact Finset.min'_le _ _ hj'

private lemma minPosRatio_pos {n : ℕ} (x y : Fin n → ℝ)
    (hpos : (posIndexSet y).Nonempty) (hxpos : ∀ j ∈ posIndexSet y, 0 < x j) :
    0 < minPosRatio x y hpos := by
  classical
  have hmem :
      minPosRatio x y hpos ∈ (posIndexSet y).image (fun j => x j / y j) := by
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨j, hj, hj_eq⟩
  have hy : 0 < y j := by
    simpa [posIndexSet] using hj
  have hx : 0 < x j := hxpos j hj
  have hratio : 0 < x j / y j := div_pos hx hy
  simpa [hj_eq] using hratio

private lemma support_pos {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) {j : Fin n} (hj : j ∈ support x) : 0 < x j := by
  have hnonneg : 0 ≤ x j := hx j
  have hne : x j ≠ 0 := (Finset.mem_filter.mp hj).2
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

private lemma exists_pos_or_neg {n : ℕ} (y : Fin n → ℝ) (hne : y ≠ 0) :
    ∃ j, 0 < y j ∨ y j < 0 := by
  classical
  by_contra h
  have hzero : ∀ j, y j = 0 := by
    intro j
    have h' : ¬ (0 < y j ∨ y j < 0) := by
      intro hj
      exact h ⟨j, hj⟩
    have hle : y j ≤ 0 := by
      by_contra hj
      exact h' (Or.inl (lt_of_not_ge hj))
    have hge : 0 ≤ y j := by
      by_contra hj
      exact h' (Or.inr (lt_of_not_ge hj))
    exact le_antisymm hle hge
  exact hne (by funext j; exact hzero j)

private lemma extendSupport_eq_sum_support {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → ℝ) (hS : ∀ j, j ∉ S → x j = 0) :
    extendSupport S (restrictSupport S x) = x := by
  classical
  funext j
  by_cases hj : j ∈ S
  · simp [extendSupport, restrictSupport, hj]
  · simp [extendSupport, hj, hS j hj]

private lemma support_extend_subset {n : ℕ} (S : Finset (Fin n))
    (u : Fin S.card → ℝ) :
    support (extendSupport S u) ⊆ S := by
  classical
  intro j hj
  have hj' : extendSupport S u j ≠ 0 := by
    simpa [support] using (Finset.mem_filter.mp hj).2
  by_contra hmem
  exact hj' (extend_support_eq_zero (S := S) (u := u) (j := j) hmem)

private lemma mulVec_extend_eq_zero_of_submatrix_eq_zero
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (S : Finset (Fin n))
    (y : Fin S.card → ℚ)
    (hy : (submatrixSupport A S).mulVec y = 0) :
    (A.map Rat.cast).mulVec (extendSupport S (fun j => (y j : ℝ))) = 0 := by
  classical
  have hy' : ((submatrixSupport A S).map Rat.cast).mulVec (fun j => (y j : ℝ)) = 0 := by
    have hcast := ratCast_mulVec (A := submatrixSupport A S) (x := y)
    simpa [hy] using hcast.symm
  have hsum :=
    submatrixSupport_mulVec_eq (A := A) (S := S) (u := fun j => (y j : ℝ))
  simpa [hsum] using hy'

def RationalLP.isOptimalReal (P : RationalLP m n) (x : Fin n → ℝ) : Prop :=
  P.toLP.isFeasible x ∧
    ∀ z, P.toLP.isFeasible z → P.toLP.objective z ≤ P.toLP.objective x

private lemma objective_add_smul (P : RationalLP m n) (x y : Fin n → ℝ) (t : ℝ) :
    P.toLP.objective (x + t • y) =
      P.toLP.objective x + t * P.toLP.objective y := by
  simp [LP.objective, dotProduct_add, dotProduct_smul]

private lemma extendSupport_ne_zero {n : ℕ} (S : Finset (Fin n))
    (u : Fin S.card → ℝ) (hu : u ≠ 0) :
    extendSupport S u ≠ 0 := by
  intro hzero
  have : restrictSupport S (extendSupport S u) = (0 : Fin S.card → ℝ) := by
    ext j
    simp [hzero, restrictSupport]
  have hru : restrictSupport S (extendSupport S u) = u :=
    restrict_extend_support (S := S) (u := u)
  exact hu (by simpa [hru] using this)

theorem RationalLP.exists_rat_optimal {P : RationalLP m n} (x : Fin n → ℝ)
    (hxopt : P.isOptimalReal x) :
    ∃ xq : Fin n → ℚ,
      P.isFeasible xq ∧
      P.toLP.objective (fun j => (xq j : ℝ)) = P.toLP.objective x := by
  classical
  let optVal := P.toLP.objective x
  have hx_feas : P.toLP.isFeasible x := hxopt.1
  let p : ℕ → Prop :=
    fun k => ∃ z, P.toLP.isFeasible z ∧ P.toLP.objective z = optVal ∧ (support z).card = k
  have hp : ∃ k, p k := by
    refine ⟨(support x).card, x, hx_feas, rfl, rfl⟩
  let kmin := Nat.find hp
  have hkmin : p kmin := Nat.find_spec hp
  obtain ⟨x_min, hx_min_feas, hx_min_obj, hx_min_card⟩ := hkmin
  have hx_min_opt : P.isOptimalReal x_min := by
    refine ⟨hx_min_feas, ?_⟩
    intro z hz
    have hz_le := hxopt.2 z hz
    simpa [optVal, hx_min_obj] using hz_le
  let S := support x_min
  have hx_min_pos : ∀ j ∈ S, 0 < x_min j := by
    intro j hj
    have hx_nonneg : ∀ j, 0 ≤ x_min j := hx_min_feas.1
    exact support_pos x_min hx_nonneg (by simpa [S] using hj)
  have hmin_support :
      ∀ z, P.toLP.isFeasible z → P.toLP.objective z = optVal →
        kmin ≤ (support z).card := by
    intro z hz hobj
    have : p (support z).card := ⟨z, hz, hobj, rfl⟩
    exact Nat.find_min' hp this
  have hmin_support' :
      ∀ z, P.isOptimalReal z → (support z).card ≥ (support x_min).card := by
    intro z hz
    have hobj : P.toLP.objective z = optVal := by
      have hz_le := hxopt.2 z hz.1
      have hx_le := hz.2 x hx_feas
      have := le_antisymm hz_le hx_le
      simpa [optVal] using this
    have hle := hmin_support z hz.1 hobj
    simpa [S, hx_min_card, kmin] using hle
  have hker :
      ∀ y : Fin S.card → ℚ, (submatrixSupport P.A S).mulVec y = 0 → y = 0 := by
    intro y hy
    by_contra hyne
    let yR : Fin S.card → ℝ := fun j => (y j : ℝ)
    have hyR_ne : yR ≠ 0 := by
      intro hzero
      apply hyne
      funext j
      have hj := congrArg (fun f => f j) hzero
      exact Rat.cast_injective (by simpa using hj)
    let yExt : Fin n → ℝ := extendSupport S yR
    have hyExt_ne : yExt ≠ 0 := by
      simpa [yExt] using extendSupport_ne_zero (S := S) (u := yR) hyR_ne
    have hAyExt : (P.A.map Rat.cast).mulVec yExt = 0 := by
      simpa [yExt] using
        mulVec_extend_eq_zero_of_submatrix_eq_zero (A := P.A) (S := S) (y := y) hy
    let yabs : Fin n → ℝ := fun j => |yExt j|
    have hyabs_pos : (posIndexSet yabs).Nonempty := by
      obtain ⟨j, hj⟩ := exists_pos_or_neg yExt hyExt_ne
      cases hj with
      | inl hjpos =>
          exact ⟨j, by simpa [posIndexSet, yabs] using abs_pos.mpr (ne_of_gt hjpos)⟩
      | inr hjneg =>
          have : 0 < |yExt j| := by
            exact abs_pos.mpr (ne_of_lt hjneg)
          exact ⟨j, by simpa [posIndexSet, yabs] using this⟩
    have hx_min_pos_abs : ∀ j ∈ posIndexSet yabs, 0 < x_min j := by
      intro j hj
      have hj' : yExt j ≠ 0 := by
        have hjpos : 0 < yabs j := (Finset.mem_filter.mp hj).2
        have hne : |yExt j| ≠ 0 := by
          exact ne_of_gt (by simpa [yabs] using hjpos)
        intro hz
        exact hne (by simp [hz])
      have hjS : j ∈ S := by
        have : j ∈ support yExt := by
          simpa [support] using hj'
        simpa [yExt] using (support_extend_subset (S := S) (u := yR) this)
      exact hx_min_pos j hjS
    let t := minPosRatio x_min yabs hyabs_pos
    have htpos : 0 < t := minPosRatio_pos x_min yabs hyabs_pos hx_min_pos_abs
    have hnonneg_abs : ∀ j, 0 ≤ x_min j - t * yabs j := by
      intro j
      by_cases hjpos : 0 < yabs j
      · have hle := minPosRatio_le x_min yabs hyabs_pos (j := j)
          (by simpa [posIndexSet] using hjpos)
        have hle' : t * yabs j ≤ x_min j := by
          have := (mul_le_mul_of_nonneg_right hle (le_of_lt hjpos))
          field_simp at this
          simpa [t] using this
        linarith
      · have hzero : yabs j = 0 := by
          have hle : yabs j ≤ 0 := le_of_not_gt hjpos
          exact le_antisymm hle (abs_nonneg _)
        have hx_nonneg : 0 ≤ x_min j := hx_min_feas.1 j
        simp [hzero, hx_nonneg]
    have hfeas_add : P.toLP.isFeasible (x_min + t • yExt) := by
      refine ⟨?_, ?_⟩
      · intro j
        have hnn := hnonneg_abs j
        have hbound :
            x_min j - t * yabs j ≤ x_min j + t * yExt j := by
          have hbound' : -|yExt j| ≤ yExt j :=
            (abs_le.mp (le_rfl : |yExt j| ≤ |yExt j|)).1
          have hmul := mul_le_mul_of_nonneg_left hbound' (le_of_lt htpos)
          have hmul' : -t * |yExt j| ≤ t * yExt j := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          have := add_le_add_left hmul' (x_min j)
          simpa [yabs, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, mul_comm,
            mul_left_comm, mul_assoc] using this
        exact le_trans hnn hbound
      · have hAx := hx_min_feas.2
        have hAy : (P.A.map Rat.cast).mulVec yExt = 0 := hAyExt
        calc
          (P.A.map Rat.cast).mulVec (x_min + t • yExt)
              = (P.A.map Rat.cast).mulVec x_min + t • (P.A.map Rat.cast).mulVec yExt := by
                  simp [Matrix.mulVec_add, Matrix.mulVec_smul]
          _ = fun i => (P.b i : ℝ) := by
                  simpa [hAx, hAy]
    have hfeas_sub : P.toLP.isFeasible (x_min - t • yExt) := by
      refine ⟨?_, ?_⟩
      · intro j
        have hnn := hnonneg_abs j
        have hbound :
            x_min j - t * yabs j ≤ x_min j - t * yExt j := by
          have hbound' : yExt j ≤ |yExt j| :=
            (abs_le.mp (le_rfl : |yExt j| ≤ |yExt j|)).2
          have hmul := mul_le_mul_of_nonneg_left hbound' (le_of_lt htpos)
          have hmul' : t * yExt j ≤ t * |yExt j| := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          have := sub_le_sub_left hmul' (x_min j)
          simpa [yabs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
            mul_left_comm, mul_assoc] using this
        exact le_trans hnn hbound
      · have hAx := hx_min_feas.2
        have hAy : (P.A.map Rat.cast).mulVec yExt = 0 := hAyExt
        calc
          (P.A.map Rat.cast).mulVec (x_min - t • yExt)
              = (P.A.map Rat.cast).mulVec x_min +
                  (P.A.map Rat.cast).mulVec (-(t • yExt)) := by
                  simpa [sub_eq_add_neg] using
                    (Matrix.mulVec_add (P.A.map Rat.cast) x_min (-(t • yExt)))
          _ = (P.A.map Rat.cast).mulVec x_min - t • (P.A.map Rat.cast).mulVec yExt := by
                  simp [Matrix.mulVec_neg, Matrix.mulVec_smul, sub_eq_add_neg]
          _ = fun i => (P.b i : ℝ) := by
                  simpa [hAx, hAy]
    have hobj_add := hx_min_opt.2 _ hfeas_add
    have hobj_sub := hx_min_opt.2 _ hfeas_sub
    have hobj_add' :
        P.toLP.objective (x_min + t • yExt) =
          P.toLP.objective x_min + t * P.toLP.objective yExt := by
      simpa using objective_add_smul P x_min yExt t
    have hobj_sub' :
        P.toLP.objective (x_min - t • yExt) =
          P.toLP.objective x_min - t * P.toLP.objective yExt := by
      have := objective_add_smul P x_min yExt (-t)
      simpa [sub_eq_add_neg, smul_neg] using this
    have hle1 : t * P.toLP.objective yExt ≤ 0 := by
      have : P.toLP.objective x_min + t * P.toLP.objective yExt ≤ P.toLP.objective x_min := by
        simpa [hobj_add'] using hobj_add
      linarith
    have hle2 : -t * P.toLP.objective yExt ≤ 0 := by
      have : P.toLP.objective x_min - t * P.toLP.objective yExt ≤ P.toLP.objective x_min := by
        simpa [hobj_sub'] using hobj_sub
      linarith
    have hcy_zero : P.toLP.objective yExt = 0 := by
      nlinarith [htpos, hle1, hle2]
    have hy_pos_or_neg :
        (posIndexSet yExt).Nonempty ∨ (posIndexSet (-yExt)).Nonempty := by
      obtain ⟨j, hj⟩ := exists_pos_or_neg yExt hyExt_ne
      cases hj with
      | inl hjpos =>
          left
          exact ⟨j, by simpa [posIndexSet] using hjpos⟩
      | inr hjneg =>
          right
          have : 0 < (-yExt) j := by
            simpa using (neg_pos.mpr hjneg)
          exact ⟨j, by simpa [posIndexSet] using this⟩
    -- Objective direction is zero: reduce support.
    rcases hy_pos_or_neg with hpos | hpos
    · let t := minPosRatio x_min (extendSupport S yR) hpos
      have htpos : 0 < t := by
        refine minPosRatio_pos x_min (extendSupport S yR) hpos ?_
        intro j hj
        have hj' : j ∈ support (extendSupport S yR) := by
          have : (extendSupport S yR) j ≠ 0 := by
            exact ne_of_gt (Finset.mem_filter.mp hj).2
          simpa [support] using this
        have hjS : j ∈ S := support_extend_subset (S := S) (u := yR) hj'
        exact hx_min_pos j hjS
      have hnonneg : ∀ j, 0 ≤ x_min j - t * (extendSupport S yR) j := by
        intro j
        by_cases hjpos : 0 < (extendSupport S yR) j
        · have hle := minPosRatio_le x_min (extendSupport S yR) hpos
            (j := j) (by simpa [posIndexSet] using hjpos)
          have hle' : t * (extendSupport S yR) j ≤ x_min j := by
            have := (mul_le_mul_of_nonneg_right hle (le_of_lt hjpos))
            have hxy : x_min j / (extendSupport S yR) j * (extendSupport S yR) j = x_min j := by
              field_simp [hjpos.ne']
            simpa [hxy] using this
          linarith [hle']
        · have hle : (extendSupport S yR) j ≤ 0 := by
            exact le_of_not_gt hjpos
          have : 0 ≤ -t * (extendSupport S yR) j := by
            have : 0 ≤ t * (-extendSupport S yR j) :=
              mul_nonneg (le_of_lt htpos) (neg_nonneg.mpr hle)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
          have hxnonneg : 0 ≤ x_min j := hx_min_feas.1 j
          have hsum : 0 ≤ x_min j + (-t * (extendSupport S yR) j) :=
            add_nonneg hxnonneg this
          simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hsum
      have hfeas : P.toLP.isFeasible (x_min - t • extendSupport S yR) := by
        refine ⟨?_, ?_⟩
        · intro j
          specialize hnonneg j
          simpa [Pi.sub_apply, Pi.smul_apply] using hnonneg
        · have hAx := hx_min_feas.2
          have hAy : (P.A.map Rat.cast).mulVec (extendSupport S yR) = 0 := by
            simpa [yExt] using hAyExt
          calc
            (P.A.map Rat.cast).mulVec (x_min - t • extendSupport S yR)
                = (P.A.map Rat.cast).mulVec x_min +
                    (P.A.map Rat.cast).mulVec (-(t • extendSupport S yR)) := by
                      simpa [sub_eq_add_neg] using
                        (Matrix.mulVec_add (P.A.map Rat.cast) x_min (-(t • extendSupport S yR)))
            _ = (P.A.map Rat.cast).mulVec x_min
                    - t • (P.A.map Rat.cast).mulVec (extendSupport S yR) := by
                      simp [Matrix.mulVec_neg, Matrix.mulVec_smul, sub_eq_add_neg]
            _ = fun i => (P.b i : ℝ) := by
                      simpa [hAx, hAy]
      have hobj' :
          P.toLP.objective (x_min - t • extendSupport S yR) = P.toLP.objective x_min := by
        have hobj :=
          objective_add_smul P x_min (extendSupport S yR) (-t)
        have hobj' :
            P.toLP.objective (x_min - t • extendSupport S yR) =
              P.toLP.objective x_min + (-t) * P.toLP.objective (extendSupport S yR) := by
          simpa [sub_eq_add_neg, smul_neg] using hobj
        simpa [yExt, hcy_zero] using hobj'
      have hsupport_lt :
          (support (x_min - t • extendSupport S yR)).card < (support x_min).card := by
        have hmem :=
          Finset.min'_mem
            ((posIndexSet (extendSupport S yR)).image
              (fun j => x_min j / (extendSupport S yR) j))
            (Finset.Nonempty.image hpos _)
        rcases Finset.mem_image.mp hmem with ⟨j, hj, hj_eq⟩
        have hjpos : 0 < (extendSupport S yR) j := by
          simpa [posIndexSet] using hj
        have ht : t = x_min j / (extendSupport S yR) j := by
          simpa [minPosRatio] using hj_eq.symm
        have hjmin : x_min j - t * (extendSupport S yR) j = 0 := by
          have hjpos_ne : (extendSupport S yR) j ≠ 0 := ne_of_gt hjpos
          calc
            x_min j - t * (extendSupport S yR) j
                = x_min j - (x_min j / (extendSupport S yR) j) *
                    (extendSupport S yR) j := by
                    simp [ht]
            _ = x_min j - x_min j := by
                    field_simp [hjpos_ne]
            _ = 0 := by
                    ring
        have hjmem : j ∈ support x_min := by
          have : (extendSupport S yR) j ≠ 0 := ne_of_gt hjpos
          have : j ∈ support (extendSupport S yR) := by
            simpa [support] using this
          exact support_extend_subset (S := S) (u := yR) this
        have hjzero : (x_min - t • extendSupport S yR) j = 0 := by
          simp [Pi.sub_apply, Pi.smul_apply, hjmin]
        have hsubset :
            support (x_min - t • extendSupport S yR) ⊆ support x_min := by
          intro j hj
          have : (x_min - t • extendSupport S yR) j ≠ 0 := by
            simpa [support] using (Finset.mem_filter.mp hj).2
          have hjy : extendSupport S yR j = 0 → x_min j ≠ 0 := by
            intro hzero
            have hEq : x_min j = (x_min - t • extendSupport S yR) j := by
              simp [Pi.sub_apply, Pi.smul_apply, hzero]
            exact hEq ▸ this
          have hj' : j ∈ S := by
            by_cases hmem : j ∈ S
            · exact hmem
            · have hz := extend_support_eq_zero (S := S) (u := yR) (j := j) hmem
              have hxzero : x_min j = 0 := by
                simpa [S, support] using hmem
              exact False.elim ((hjy hz) hxzero)
          simpa [S] using hj'
        have hnotmem : j ∉ support (x_min - t • extendSupport S yR) := by
          intro hmem
          have hmem' := (Finset.mem_filter.mp hmem).2
          exact hmem' hjzero
        have hssub : support (x_min - t • extendSupport S yR) ⊂ support x_min := by
          refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
          exact ⟨j, hjmem, hnotmem⟩
        exact Finset.card_lt_card hssub
      have hopt' : P.isOptimalReal (x_min - t • extendSupport S yR) := by
        refine ⟨hfeas, ?_⟩
        intro z hz
        have hz_le := hx_min_opt.2 z hz
        simpa [hobj'] using hz_le
      have hcard_le := hmin_support' (x_min - t • extendSupport S yR) hopt'
      exact lt_irrefl _ (lt_of_lt_of_le hsupport_lt hcard_le)
    · -- Use y' = -yExt when no positive entries.
      let y' := -extendSupport S yR
      let t := minPosRatio x_min y' hpos
      have htpos : 0 < t := by
        refine minPosRatio_pos x_min y' hpos ?_
        intro j hj
        have hj' : j ∈ support y' := by
          have : y' j ≠ 0 := by
            exact ne_of_gt (Finset.mem_filter.mp hj).2
          simpa [support, y'] using this
        have hjS : j ∈ S := by
          have hj'' : j ∈ support (extendSupport S yR) := by
            simpa [support, y'] using hj'
          have := support_extend_subset (S := S) (u := yR) hj''
          simpa using this
        exact hx_min_pos j hjS
      have hnonneg : ∀ j, 0 ≤ x_min j - t * y' j := by
        intro j
        by_cases hjpos : 0 < y' j
        · have hle := minPosRatio_le x_min y' hpos
            (j := j) (by simpa [posIndexSet] using hjpos)
          have hle' : t * y' j ≤ x_min j := by
            have := (mul_le_mul_of_nonneg_right hle (le_of_lt hjpos))
            have hxy : x_min j / y' j * y' j = x_min j := by
              field_simp [hjpos.ne']
            simpa [hxy] using this
          linarith [hle']
        · have hle : y' j ≤ 0 := by
            exact le_of_not_gt hjpos
          have : 0 ≤ -t * y' j := by
            have : 0 ≤ t * (-y' j) :=
              mul_nonneg (le_of_lt htpos) (neg_nonneg.mpr hle)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
          have hxnonneg : 0 ≤ x_min j := hx_min_feas.1 j
          have hsum : 0 ≤ x_min j + (-t * y' j) := add_nonneg hxnonneg this
          simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hsum
      have hfeas : P.toLP.isFeasible (x_min - t • y') := by
        refine ⟨?_, ?_⟩
        · intro j
          specialize hnonneg j
          simpa [Pi.sub_apply, Pi.smul_apply] using hnonneg
        · have hAx := hx_min_feas.2
          have hAy' : (P.A.map Rat.cast).mulVec y' = 0 := by
            simpa [y', Matrix.mulVec_neg] using hAyExt
          calc
            (P.A.map Rat.cast).mulVec (x_min - t • y')
                = (P.A.map Rat.cast).mulVec x_min +
                    (P.A.map Rat.cast).mulVec (-(t • y')) := by
                      simpa [sub_eq_add_neg] using
                        (Matrix.mulVec_add (P.A.map Rat.cast) x_min (-(t • y')))
            _ = (P.A.map Rat.cast).mulVec x_min - t • (P.A.map Rat.cast).mulVec y' := by
                      simp [Matrix.mulVec_neg, Matrix.mulVec_smul, sub_eq_add_neg]
            _ = fun i => (P.b i : ℝ) := by
                      simpa [hAx, hAy']
      have hobj' :
          P.toLP.objective (x_min - t • y') = P.toLP.objective x_min := by
        have hobj := objective_add_smul P x_min y' (-t)
        have hcy_zero' : P.toLP.objective y' = 0 := by
          have hcy' : P.toLP.objective y' = (-1) * P.toLP.objective yExt := by
            simp [y', yExt, LP.objective]
          simpa [hcy_zero] using hcy'
        have hobj' :
            P.toLP.objective (x_min - t • y') =
              P.toLP.objective x_min + (-t) * P.toLP.objective y' := by
          simpa [sub_eq_add_neg, smul_neg] using hobj
        simpa [hcy_zero'] using hobj'
      have hsupport_lt :
          (support (x_min - t • y')).card < (support x_min).card := by
        have hmem := Finset.min'_mem
          ((posIndexSet y').image (fun j => x_min j / y' j))
          (Finset.Nonempty.image hpos _)
        rcases Finset.mem_image.mp hmem with ⟨j, hj, hj_eq⟩
        have hjpos : 0 < y' j := by
          simpa [posIndexSet] using hj
        have ht : t = x_min j / y' j := by
          simpa [minPosRatio] using hj_eq.symm
        have hjmin : x_min j - t * y' j = 0 := by
          have hjpos_ne : y' j ≠ 0 := ne_of_gt hjpos
          calc
            x_min j - t * y' j = x_min j - (x_min j / y' j) * y' j := by
              simp [ht]
            _ = x_min j - x_min j := by
              field_simp [hjpos_ne]
            _ = 0 := by
              ring
        have hjmem : j ∈ support x_min := by
          have : y' j ≠ 0 := ne_of_gt hjpos
          have : j ∈ support y' := by
            simpa [support, y'] using this
          have : j ∈ support (extendSupport S yR) := by
            simpa [support, y'] using this
          exact support_extend_subset (S := S) (u := yR) this
        have hjzero : (x_min - t • y') j = 0 := by
          simp [Pi.sub_apply, Pi.smul_apply, hjmin]
        have hsubset : support (x_min - t • y') ⊆ support x_min := by
          intro j hj
          have : (x_min - t • y') j ≠ 0 := by
            simpa [support] using (Finset.mem_filter.mp hj).2
          have hjy : y' j = 0 → x_min j ≠ 0 := by
            intro hzero
            have hEq : x_min j = (x_min - t • y') j := by
              simp [Pi.sub_apply, Pi.smul_apply, hzero]
            exact hEq ▸ this
          have hj' : j ∈ S := by
            by_cases hmem : j ∈ S
            · exact hmem
            · have hz : y' j = 0 := by
                have hz' := extend_support_eq_zero (S := S) (u := yR) (j := j) hmem
                simpa [y'] using hz'
              have hxzero : x_min j = 0 := by
                simpa [S, support] using hmem
              exact False.elim ((hjy hz) hxzero)
          simpa [S] using hj'
        have hnotmem : j ∉ support (x_min - t • y') := by
          intro hmem
          have hmem' := (Finset.mem_filter.mp hmem).2
          exact hmem' hjzero
        have hssub : support (x_min - t • y') ⊂ support x_min := by
          refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
          exact ⟨j, hjmem, hnotmem⟩
        exact Finset.card_lt_card hssub
      have hopt' : P.isOptimalReal (x_min - t • y') := by
        refine ⟨hfeas, ?_⟩
        intro z hz
        have hz_le := hx_min_opt.2 z hz
        simpa [hobj'] using hz_le
      have hcard_le := hmin_support' (x_min - t • y') hopt'
      exact lt_irrefl _ (lt_of_lt_of_le hsupport_lt hcard_le)
    -- unreachable
  have hA_inj : Function.Injective (submatrixSupport P.A S).mulVec := by
    intro y1 y2 h
    have hdiff : (submatrixSupport P.A S).mulVec (y1 - y2) = 0 := by
      calc
        (submatrixSupport P.A S).mulVec (y1 - y2)
            = (submatrixSupport P.A S).mulVec y1 -
                (submatrixSupport P.A S).mulVec y2 := by
                  simp [Matrix.mulVec_sub]
        _ = 0 := by
                  simp [h]
    have hzero : y1 - y2 = 0 := hker _ hdiff
    simpa [sub_eq_zero] using hzero
  have hA_lin : LinearIndependent ℚ (submatrixSupport P.A S).col := by
    exact (Matrix.mulVec_injective_iff).1 hA_inj
  have hAx : ((submatrixSupport P.A S).map Rat.cast).mulVec (restrictSupport S x_min) =
      (P.A.map Rat.cast).mulVec x_min := by
    ext i
    have h := submatrixSupport_mulVec_eq (A := P.A) (S := S) (u := restrictSupport S x_min)
    have h' : extendSupport S (restrictSupport S x_min) = x_min := by
      refine extendSupport_eq_sum_support (S := S) (x := x_min) ?_
      intro j hj
      by_contra hzero
      have : j ∈ support x_min := by
        simp [support, hzero]
      exact hj (by simpa [S] using this)
    simpa [h'] using congrArg (fun f => f i) h
  have hAx' :
      ((submatrixSupport P.A S).map Rat.cast).mulVec (restrictSupport S x_min) =
        fun i => (P.b i : ℝ) := by
    have hAx_min := hx_min_feas.2
    ext i
    have hAx_i := congrArg (fun f => f i) hAx
    have hAx_min_i := congrArg (fun f => f i) hAx_min
    exact hAx_i.trans hAx_min_i
  obtain ⟨xqS, hxqS, hxqS_cast⟩ :=
    exists_rat_solution_of_real_injective_cast (A := submatrixSupport P.A S) hA_lin (b := P.b)
      (x := restrictSupport S x_min)
      (by
        ext i
        simpa using (congrArg (fun f => f i) hAx'))
  let xq : Fin n → ℚ :=
    fun j => if h : j ∈ S then xqS (Finset.equivFin S ⟨j, h⟩) else 0
  have hxq_eq : (fun j => (xq j : ℝ)) = extendSupport S (fun j => (xqS j : ℝ)) := by
    funext j
    by_cases hj : j ∈ S
    · simp [xq, extendSupport, hj]
    · simp [xq, extendSupport, hj]
  have hxq_feas : P.isFeasible xq := by
    constructor
    · intro j
      by_cases hj : j ∈ S
      · have hxqS_nonneg : 0 ≤ xqS (Finset.equivFin S ⟨j, hj⟩) := by
          have hxmin_nonneg :
              0 ≤ restrictSupport S x_min (Finset.equivFin S ⟨j, hj⟩) := by
            have hmin := hx_min_feas.1 j
            simpa [restrictSupport] using hmin
          have hxqS_cast_j :
              (xqS (Finset.equivFin S ⟨j, hj⟩) : ℝ) =
                restrictSupport S x_min (Finset.equivFin S ⟨j, hj⟩) := by
            simpa using congrArg (fun f => f (Finset.equivFin S ⟨j, hj⟩)) hxqS_cast
          exact Rat.cast_nonneg.mp (by simpa [hxqS_cast_j.symm] using hxmin_nonneg)
        simpa [xq, hj] using hxqS_nonneg
      · simp [xq, hj]
    · ext i
      have hAxq_cast :
          ratCastLinearMap m (P.A.mulVec xq) =
            ratCastLinearMap m ((submatrixSupport P.A S).mulVec xqS) := by
        calc
          ratCastLinearMap m (P.A.mulVec xq)
              = (P.A.map Rat.cast).mulVec (fun j => (xq j : ℝ)) := by
                  simpa using (ratCast_mulVec (A := P.A) (x := xq))
          _ = (P.A.map Rat.cast).mulVec (extendSupport S (fun j => (xqS j : ℝ))) := by
                  simp [hxq_eq]
          _ = ((submatrixSupport P.A S).map Rat.cast).mulVec (fun j => (xqS j : ℝ)) := by
                  symm
                  simpa using (submatrixSupport_mulVec_eq (A := P.A) (S := S)
                    (u := fun j => (xqS j : ℝ)))
          _ = ratCastLinearMap m ((submatrixSupport P.A S).mulVec xqS) := by
                  symm
                  simpa using (ratCast_mulVec (A := submatrixSupport P.A S) (x := xqS))
      have hAxq_cast_b :
          ratCastLinearMap m ((submatrixSupport P.A S).mulVec xqS) =
            fun i => (P.b i : ℝ) := by
        simpa [ratCastLinearMap] using congrArg (fun f => ratCastLinearMap m f) hxqS
      have hAxq_cast_b' :
          ratCastLinearMap m (P.A.mulVec xq) = fun i => (P.b i : ℝ) :=
        hAxq_cast.trans hAxq_cast_b
      have hAxq : P.A.mulVec xq = P.b :=
        ratCastLinearMap_injective m hAxq_cast_b'
      exact congrArg (fun f => f i) hAxq
  refine ⟨xq, hxq_feas, ?_⟩
  have hx_min_eq :
      extendSupport S (restrictSupport S x_min) = x_min := by
    refine extendSupport_eq_sum_support (S := S) (x := x_min) ?_
    intro j hj
    by_contra hzero
    have : j ∈ support x_min := by
      simp [support, hzero]
    exact hj (by simpa [S] using this)
  have hxqS_eq : (fun j => (xqS j : ℝ)) = restrictSupport S x_min := by
    simpa using hxqS_cast
  have hobj :
      P.toLP.objective (fun j => (xq j : ℝ)) =
        P.toLP.objective x_min := by
    have hxq_cast : (fun j => (xq j : ℝ)) = x_min := by
      calc
        (fun j => (xq j : ℝ)) =
            extendSupport S (fun j => (xqS j : ℝ)) := hxq_eq
        _ = extendSupport S (restrictSupport S x_min) := by
            simp [hxqS_eq]
        _ = x_min := hx_min_eq
    simpa [LP.objective] using congrArg (fun f => dotProduct P.toLP.c f) hxq_cast
  simpa [hx_min_obj] using hobj

end RationalLP

end ConeProgramming
