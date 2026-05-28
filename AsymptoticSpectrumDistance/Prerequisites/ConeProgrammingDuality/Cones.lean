/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.LocallyConvex.Separation

set_option linter.style.emptyLine false

/-!
# Closed Convex Cones and Dual Cones

This file provides basic definitions and properties of closed convex cones,
product cones, lifted cones, and dual cones, following Chapter 4 of
Gärtner-Matoušek "Approximation Algorithms and Semidefinite Programming".

## Main definitions

* `ClosedConvexCone` : Abbreviation for Mathlib's `ProperCone`
* `nonnegOrthant` : The nonnegative orthant ℝ₊ⁿ
* `nonnegHalfLine` : The nonnegative half-line ℝ₊
* `productCone` : Product of two proper cones
* `liftedCone` : The cone K × ℝ₊ used in regular duality
* `liftedConeL2` : Lifted cone in L2 product space
* `dualCone` : The dual cone K*
* `objectiveImageCone` : The image cone {(Ax, ⟨c,x⟩) : x ∈ K}

## Main results

* `nonnegOrthant_self_dual` : (ℝ₊ⁿ)* = ℝ₊ⁿ
* `nonnegHalfLine_self_dual` : (ℝ₊)* = ℝ₊
* `separation_theorem` : Separation for closed convex cones (Theorem 4.4.2)
* `double_dual_eq_self` : (K*)* = K (Lemma 4.4.1)
-/

namespace ConeProgramming

open scoped InnerProductSpace RealInnerProductSpace
open ContinuousLinearMap

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-! ## Section 4.2: Closed Convex Cones

Definition 4.2.1: A closed convex cone K ⊆ V satisfies:
(i) For all x ∈ K and λ ≥ 0, we have λx ∈ K
(ii) For all x, y ∈ K, we have x + y ∈ K

In Mathlib, this is `ProperCone` (a pointed, closed cone).
-/

section ClosedConvexCones

/-- A closed convex cone in the sense of Gärtner-Matoušek Definition 4.2.1.
    We use Mathlib's ProperCone which captures closed pointed cones. -/
abbrev ClosedConvexCone (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] := ProperCone ℝ V

/-- The nonnegative orthant ℝ₊ⁿ is a closed convex cone. -/
def nonnegOrthant (n : ℕ) : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) where
  toSubmodule := {
    carrier := {x | ∀ i, 0 ≤ x i}
    add_mem' := fun ha hb i => add_nonneg (ha i) (hb i)
    zero_mem' := fun _ => le_refl 0
    smul_mem' := fun ⟨c, hc⟩ x hx i => mul_nonneg hc (hx i)
  }
  isClosed' := by
    have : {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} = ⋂ i : Fin n, {x | 0 ≤ x i} := by
      ext x; simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (EuclideanSpace.proj i).continuous

theorem mem_nonnegOrthant {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ nonnegOrthant n ↔ ∀ i, 0 ≤ x i := Iff.rfl

/-- The nonnegative half-line ℝ₊ = {x ∈ ℝ : x ≥ 0} as a proper cone in ℝ. -/
def nonnegHalfLine : ProperCone ℝ ℝ where
  toSubmodule := {
    carrier := Set.Ici 0
    add_mem' := fun {a b} (ha : 0 ≤ a) (hb : 0 ≤ b) => add_nonneg ha hb
    zero_mem' := Set.self_mem_Ici
    smul_mem' := fun ⟨_, hc⟩ _ hx => mul_nonneg hc hx
  }
  isClosed' := isClosed_Ici

@[simp]
theorem mem_nonnegHalfLine {x : ℝ} : x ∈ nonnegHalfLine ↔ 0 ≤ x := by rfl

end ClosedConvexCones

/-! ## Product Cones

For the lifted cone construction in regular duality, we need to work with
product cones K × ℝ₊ in V × ℝ.
-/

section ProductCones

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Product of two proper cones is a proper cone.
    This uses Submodule.prod for the submodule structure and IsClosed.prod for closedness. -/
def productCone (K₁ : ProperCone ℝ V) (K₂ : ProperCone ℝ ℝ) : ProperCone ℝ (V × ℝ) :=
  ClosedSubmodule.mk
    (Submodule.prod K₁.toSubmodule K₂.toSubmodule)
    (IsClosed.prod K₁.isClosed K₂.isClosed)

omit [CompleteSpace V] in
theorem mem_productCone {K₁ : ProperCone ℝ V} {K₂ : ProperCone ℝ ℝ} {p : V × ℝ} :
    p ∈ productCone K₁ K₂ ↔ p.1 ∈ (K₁ : Set V) ∧ p.2 ∈ (K₂ : Set ℝ) := by
  simp only [productCone, ClosedSubmodule.mem_mk, Submodule.mem_prod, SetLike.mem_coe]
  rfl

/-- The lifted cone K × ℝ₊ used in regular duality. -/
noncomputable def liftedCone (K : ProperCone ℝ V) : ProperCone ℝ (V × ℝ) :=
  productCone K nonnegHalfLine

omit [CompleteSpace V] in
theorem mem_liftedCone {K : ProperCone ℝ V} {p : V × ℝ} :
    p ∈ liftedCone K ↔ p.1 ∈ (K : Set V) ∧ 0 ≤ p.2 := by
  rw [liftedCone, mem_productCone]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, mem_nonnegHalfLine.mp h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1, mem_nonnegHalfLine.mpr h2⟩

end ProductCones

/-! ## Lifted Cone for Regular Duality

The key construction for regular duality (Theorem 4.7.3) uses a lifted cone
in V × ℝ and a lifted map L : V × ℝ → W × ℝ.

We use `WithLp 2 (W × ℝ)` for the codomain to get the product inner product:
⟪(w₁, t₁), (w₂, t₂)⟫ = ⟪w₁, w₂⟫ + t₁ * t₂
-/

section LiftedConeConstruction

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- The lifted cone K × ℝ≥0 in the L2 product space WithLp 2 (V × ℝ).
    This uses the L2 norm on the product, giving the correct inner product structure
    for duality theory: ⟪(v₁, r₁), (v₂, r₂)⟫ = ⟪v₁, v₂⟫ + r₁ * r₂. -/
def liftedConeL2 (K : ProperCone ℝ V) : ProperCone ℝ (WithLp 2 (V × ℝ)) where
  toSubmodule := {
    carrier := {p | p.ofLp.1 ∈ (K : Set V) ∧ 0 ≤ p.ofLp.2}
    add_mem' := fun {a b} ha hb => by
      constructor
      · simp only [WithLp.ofLp_add, Prod.fst_add]
        exact K.add_mem ha.1 hb.1
      · simp only [WithLp.ofLp_add, Prod.snd_add]
        exact add_nonneg ha.2 hb.2
    zero_mem' := by
      constructor
      · simp [WithLp.ofLp_zero, Prod.fst_zero]
      · simp [WithLp.ofLp_zero, Prod.snd_zero]
    smul_mem' := fun c x hx => by
      constructor
      · exact K.smul_mem hx.1 c.2
      · exact mul_nonneg c.2 hx.2
  }
  isClosed' := by
    have h1 : ∀ p : WithLp 2 (V × ℝ), (WithLp.fstL 2 ℝ V ℝ) p = p.ofLp.1 := by
      intro p; simp [WithLp.fstL]
    have h2 : ∀ p : WithLp 2 (V × ℝ), (WithLp.sndL 2 ℝ V ℝ) p = p.ofLp.2 := by
      intro p; simp [WithLp.sndL]
    have hset : {p : WithLp 2 (V × ℝ) | p.ofLp.1 ∈ (K : Set V) ∧ 0 ≤ p.ofLp.2} =
                ((WithLp.fstL 2 ℝ V ℝ) ⁻¹' (K : Set V)) ∩
                ((WithLp.sndL 2 ℝ V ℝ) ⁻¹' Set.Ici 0) := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ici, h1, h2]
    rw [hset]
    exact IsClosed.inter
      (K.isClosed.preimage (WithLp.fstL 2 ℝ V ℝ).continuous)
      (isClosed_Ici.preimage (WithLp.sndL 2 ℝ V ℝ).continuous)

omit [CompleteSpace V] in
theorem mem_liftedConeL2 {K : ProperCone ℝ V} {p : WithLp 2 (V × ℝ)} :
    p ∈ liftedConeL2 K ↔ p.ofLp.1 ∈ (K : Set V) ∧ 0 ≤ p.ofLp.2 := by
  rfl

omit [CompleteSpace W] in
/-- Inner product on WithLp 2 (W × ℝ) decomposes as sum of component inner products.
    For vectors (w₁, t₁) and (w₂, t₂), we have ⟪(w₁,t₁), (w₂,t₂)⟫ = ⟪w₁,w₂⟫ + t₁*t₂.
    This is standard from the L2 product structure. -/
theorem WithLp2_inner_decomp {w₁ w₂ : W} {t₁ t₂ : ℝ} :
    ⟪(WithLp.equiv 2 (W × ℝ)).symm (w₁, t₁), (WithLp.equiv 2 (W × ℝ)).symm (w₂, t₂)⟫_ℝ =
    ⟪w₁, w₂⟫_ℝ + t₁ * t₂ := by
  rw [WithLp.prod_inner_apply]
  simp only [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
  simp [inner, mul_comm]

/-- The objective image cone: {(Ax, ⟪c, x⟫) : x ∈ K}.
    This IS a proper cone:
    - 0 = (A(0), ⟨c,0⟩) ∈ cone
    - λ ≥ 0: λ(A(x), ⟨c,x⟩) = (A(λx), ⟨c,λx⟩) ∈ cone

    Used in the Farkas-based proof of regular duality. -/
def objectiveImageCone (A : V →L[ℝ] W) (c : V) (K : ProperCone ℝ V) :
    Set (WithLp 2 (W × ℝ)) :=
  {q | ∃ x ∈ (K : Set V),
    q.ofLp.1 = A x ∧
    q.ofLp.2 = ⟪c, x⟫_ℝ}

omit [CompleteSpace V] [CompleteSpace W] in
/-- The objective image cone is closed under nonnegative scaling. -/
theorem objectiveImageCone_cone (A : V →L[ℝ] W) (c : V) (K : ProperCone ℝ V) :
    ∀ (sc : ℝ), sc ≥ 0 → ∀ q ∈ objectiveImageCone A c K, sc • q ∈ objectiveImageCone A c K := by
  intro sc hsc q ⟨x, hxK, hq1, hq2⟩
  use sc • x
  refine ⟨K.smul_mem hxK hsc, ?_, ?_⟩
  · -- First component: (sc • q).1 = A(sc • x)
    have h1 : (sc • q).ofLp.1 = sc • q.ofLp.1 := by
      simp [WithLp.ofLp_smul, Prod.smul_fst]
    rw [h1, hq1, ContinuousLinearMap.map_smul]
  · -- Second component: (sc • q).2 = ⟨c, sc • x⟩
    have h2 : (sc • q).ofLp.2 = sc * q.ofLp.2 := by
      simp [WithLp.ofLp_smul, Prod.smul_snd, smul_eq_mul]
    rw [h2, hq2, inner_smul_right]

omit [CompleteSpace V] [CompleteSpace W] in
/-- Key lemma for Farkas-based regular duality:
    If all sequences approaching b have objective limit ≤ γ, then (b, γ+ε) is NOT in
    the closure of the objective image cone for any ε > 0.

    The proof is direct: if (b, γ+ε) were in closure, there would be a sequence
    with A(x_n) → b and ⟨c, x_n⟩ → γ+ε > γ, contradicting the bound.
-/
theorem not_in_closure_objectiveImageCone_if_bound
    (A : V →L[ℝ] W) (c : V) (γ : ℝ) (K : ProperCone ℝ V) (b : W) (ε : ℝ)
    (hε : 0 < ε)
    (hγ_bound : ∀ (seq : ℕ → V),
      (∀ n, seq n ∈ (K : Set V)) →
      Filter.Tendsto (fun n => A (seq n)) Filter.atTop (nhds b) →
      ∀ v, Filter.Tendsto (fun n => ⟪c, seq n⟫_ℝ) Filter.atTop (nhds v) → v ≤ γ) :
    (WithLp.equiv 2 (W × ℝ)).symm (b, γ + ε) ∉ closure (objectiveImageCone A c K) := by
  intro hmem
  -- Extract a sequence from closure membership
  rw [mem_closure_iff_seq_limit] at hmem
  obtain ⟨q, hq_in, hq_lim⟩ := hmem
  -- Each q n is in objectiveImageCone, extract witnesses
  choose x hxK hq1 hq2 using hq_in
  -- Get component convergence
  have hq_prod_lim : Filter.Tendsto (fun n => WithLp.equiv 2 (W × ℝ) (q n))
      Filter.atTop (nhds (b, γ + ε)) := by
    have heq : (b, γ + ε) = WithLp.equiv 2 (W × ℝ) ((WithLp.equiv 2 (W × ℝ)).symm (b, γ + ε)) := by
      simp only [Equiv.apply_symm_apply]
    rw [heq]
    exact (WithLp.homeomorphProd 2 W ℝ).continuous.continuousAt.tendsto.comp hq_lim
  rw [Prod.tendsto_iff] at hq_prod_lim
  obtain ⟨hq_lim1, hq_lim2⟩ := hq_prod_lim
  -- A(x n) → b
  have hA : Filter.Tendsto (fun n => A (x n)) Filter.atTop (nhds b) := by
    have heq : (fun n => A (x n)) = (fun n => (WithLp.equiv 2 (W × ℝ) (q n)).1) := by
      ext n; exact (hq1 n).symm
    rw [heq]; exact hq_lim1
  -- ⟨c, x n⟩ → γ + ε
  have hobj : Filter.Tendsto (fun n => ⟪c, x n⟫_ℝ) Filter.atTop (nhds (γ + ε)) := by
    have heq : (fun n => ⟪c, x n⟫_ℝ) = (fun n => (WithLp.equiv 2 (W × ℝ) (q n)).2) := by
      ext n; exact (hq2 n).symm
    rw [heq]; exact hq_lim2
  -- Apply the bound: γ + ε ≤ γ
  have hcontra : γ + ε ≤ γ := hγ_bound x hxK hA (γ + ε) hobj
  -- But ε > 0, so γ + ε > γ. Contradiction!
  linarith

end LiftedConeConstruction

/-! ### Separation from objective image cone

The following lemma allows applying Farkas separation using `objectiveImageCone`.
This is the key step for regular duality.
-/

section ObjectiveConeSeparation

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace V] [CompleteSpace W] in
/-- The objective image cone is convex. -/
theorem objectiveImageCone_convex (A : V →L[ℝ] W) (c : V) (K : ProperCone ℝ V) :
    Convex ℝ (objectiveImageCone A c K) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨x, hxK, hp1, hp2⟩ := hp
  obtain ⟨z, hzK, hq1, hq2⟩ := hq
  use a • x + b • z
  refine ⟨K.convex hxK hzK ha hb hab, ?_, ?_⟩
  · -- First component
    have h1 : (a • p + b • q).ofLp.1 = a • p.ofLp.1 + b • q.ofLp.1 := by
      simp [WithLp.ofLp_add, WithLp.ofLp_smul, Prod.fst_add, Prod.smul_fst]
    rw [h1, hp1, hq1]
    simp only [← A.map_smul, ← A.map_add]
  · -- Second component
    have h2 : (a • p + b • q).ofLp.2 = a • p.ofLp.2 + b • q.ofLp.2 := by
      simp [WithLp.ofLp_add, WithLp.ofLp_smul, Prod.snd_add, Prod.smul_snd]
    rw [h2, hp2, hq2]
    simp only [smul_eq_mul, inner_add_right, inner_smul_right]

omit [CompleteSpace V] [CompleteSpace W] in
/-- Zero is in the objective image cone. -/
theorem zero_mem_objectiveImageCone (A : V →L[ℝ] W) (c : V) (K : ProperCone ℝ V) :
    0 ∈ objectiveImageCone A c K := by
  use 0, K.zero_mem
  constructor
  · simp only [map_zero]; rfl
  · simp only [inner_zero_right]; rfl

omit [CompleteSpace V] in
/-- Separation from the objective image cone gives a dual-like functional.
    If (b, γ+ε) is not in closure(objectiveImageCone), then there exists (y, τ) such that
    ⟪A(x), y⟫ + ⟪c, x⟫ * τ ≥ 0 for all x ∈ K, and ⟪b, y⟫ + (γ+ε) * τ < 0. -/
theorem separation_from_objectiveImageCone
    (A : V →L[ℝ] W) (c : V) (γ : ℝ) (K : ProperCone ℝ V) (b : W) (ε : ℝ)
    (_ : 0 < ε)
    (hnotmem : (WithLp.equiv 2 (W × ℝ)).symm (b, γ + ε) ∉ closure (objectiveImageCone A c K)) :
    ∃ y : W, ∃ τ : ℝ,
      (∀ x ∈ (K : Set V), 0 ≤ ⟪A x, y⟫_ℝ + ⟪c, x⟫_ℝ * τ) ∧
      ⟪b, y⟫_ℝ + (γ + ε) * τ < 0 := by
  -- The closure of objectiveImageCone is closed and convex
  have hclosed : IsClosed (closure (objectiveImageCone A c K)) := isClosed_closure
  have hconvex : Convex ℝ (closure (objectiveImageCone A c K)) :=
    (objectiveImageCone_convex A c K).closure

  -- Apply geometric Hahn-Banach separation
  obtain ⟨f, u, hf_pt, hf_set⟩ := geometric_hahn_banach_point_closed hconvex hclosed hnotmem

  -- Use Riesz representation: f = ⟪v, ·⟫ for some v
  let v := (InnerProductSpace.toDual ℝ (WithLp 2 (W × ℝ))).symm f
  have hv_eq : ∀ z, f z = ⟪v, z⟫_ℝ := by
    intro z
    rw [InnerProductSpace.toDual_symm_apply]

  -- Extract components: v = (y, τ) in W × ℝ
  let v' := WithLp.equiv 2 (W × ℝ) v
  let y := v'.1
  let τ := v'.2
  use y, τ

  -- 0 ∈ objectiveImageCone implies u < f(0)
  have h0_mem : (0 : WithLp 2 (W × ℝ)) ∈ objectiveImageCone A c K :=
    zero_mem_objectiveImageCone A c K
  have h0_closure : (0 : WithLp 2 (W × ℝ)) ∈ closure (objectiveImageCone A c K) :=
    subset_closure h0_mem
  have hu_lt_0 : u < f 0 := hf_set 0 h0_closure
  simp only [hv_eq, inner_zero_right] at hu_lt_0

  -- f(b, γ+ε) < u < 0
  have hf_neg : f ((WithLp.equiv 2 (W × ℝ)).symm (b, γ + ε)) < 0 := by
    calc f ((WithLp.equiv 2 (W × ℝ)).symm (b, γ + ε)) < u := hf_pt
      _ < 0 := hu_lt_0

  -- Key observation: v = (WithLp.equiv 2 (W × ℝ)).symm v'
  have hv_decomp : v = (WithLp.equiv 2 (W × ℝ)).symm v' := by
    simp only [v', Equiv.symm_apply_apply]

  -- Helper: express f in terms of v'
  have hf_inner : ∀ w t, f ((WithLp.equiv 2 (W × ℝ)).symm (w, t)) = ⟪y, w⟫_ℝ + τ * t := by
    intro w t
    calc f ((WithLp.equiv 2 (W × ℝ)).symm (w, t))
        = ⟪v, (WithLp.equiv 2 (W × ℝ)).symm (w, t)⟫_ℝ := hv_eq _
      _ = ⟪(WithLp.equiv 2 (W × ℝ)).symm v', (WithLp.equiv 2 (W × ℝ)).symm (w, t)⟫_ℝ := by
            rw [← hv_decomp]
      _ = ⟪v'.1, w⟫_ℝ + v'.2 * t := WithLp2_inner_decomp
      _ = ⟪y, w⟫_ℝ + τ * t := rfl

  constructor
  · -- For all x ∈ K: ⟪A(x), y⟫ + ⟪c, x⟫ * τ ≥ 0
    intro x hxK
    -- Use cone homogeneity: for all s > 0, s•x ∈ K, so (A(sx), ⟪c,sx⟫) is in cone
    -- We prove by contradiction: if ⟪A(x), y⟫ + ⟪c,x⟫*τ < 0, then f is unbounded below on cone
    by_contra hcontra
    push_neg at hcontra
    -- hcontra : ⟪A x, y⟫ + ⟪c, x⟫ * τ < 0
    -- For s > 0, f(s•point) = s * f(point) → -∞
    -- But we have u < f(point) for all points in cone, contradiction
    have hval_neg : ⟪y, A x⟫_ℝ + τ * ⟪c, x⟫_ℝ < 0 := by
      rw [real_inner_comm, mul_comm]; exact hcontra
    -- For any s > 0, s•x ∈ K
    have hmem_scaled : ∀ s : ℝ, 0 < s → s • x ∈ (K : Set V) :=
      fun s hs => K.smul_mem hxK (le_of_lt hs)
    -- The scaled point is in the closure
    have hclosure_scaled : ∀ s : ℝ, 0 < s →
        (WithLp.equiv 2 (W × ℝ)).symm (A (s • x), ⟪c, s • x⟫_ℝ) ∈
          closure (objectiveImageCone A c K) := by
      intro s hs
      apply subset_closure
      refine ⟨s • x, hmem_scaled s hs, ?_, ?_⟩
      · simp [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
      · simp [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
    -- f on scaled point
    have hf_scaled : ∀ s : ℝ, 0 < s →
        f ((WithLp.equiv 2 (W × ℝ)).symm (A (s • x), ⟪c, s • x⟫_ℝ)) =
          s * (⟪y, A x⟫_ℝ + τ * ⟪c, x⟫_ℝ) := by
      intro s _
      rw [hf_inner]
      simp only [map_smul, inner_smul_right]
      ring
    -- For large s, this becomes very negative
    have hbad : ∀ s : ℝ, 0 < s → u < s * (⟪y, A x⟫_ℝ + τ * ⟪c, x⟫_ℝ) := by
      intro s hs
      have := hf_set _ (hclosure_scaled s hs)
      rw [hf_scaled s hs] at this
      exact this
    -- But this contradicts u being fixed while s * negative → -∞
    set val := ⟪y, A x⟫_ℝ + τ * ⟪c, x⟫_ℝ
    have hval_neg' : val < 0 := hval_neg
    -- Take s large enough that s * val < u
    -- Since val < 0, we need s > u / val, i.e., s > (a negative number)
    -- We use s = (1 - u) / (-val), noting -val > 0
    have hneg_val_pos : 0 < -val := by linarith
    have : ∃ s : ℝ, 0 < s ∧ s * val < u := by
      use (1 - u) / (-val)
      constructor
      · apply div_pos
        · linarith
        · exact hneg_val_pos
      · rw [div_mul_eq_mul_div]
        have hval_ne : val ≠ 0 := ne_of_lt hval_neg'
        have heq : (1 - u) * val / (-val) = -(1 - u) := by
          rw [div_neg, neg_eq_iff_eq_neg, neg_neg]
          rw [mul_div_assoc, div_self hval_ne, mul_one]
        rw [heq]
        linarith
    obtain ⟨s, hspos, hsbad⟩ := this
    have := hbad s hspos
    linarith

  · -- ⟪b, y⟫ + (γ+ε) * τ < 0
    have := hf_inner b (γ + ε)
    rw [this] at hf_neg
    rw [real_inner_comm, mul_comm]
    exact hf_neg

end ObjectiveConeSeparation

/-! ## Section 4.3: Dual Cones

Definition 4.3.1: The dual cone of K is
  K* := {y ∈ V : ⟨y, x⟩ ≥ 0 for all x ∈ K}

Key examples:
- (ℝ₊ⁿ)* = ℝ₊ⁿ (self-dual)
- ({0})* = V
- V* = {0}
-/

section DualCones

/-- The dual cone K* = {y : ⟨y, x⟩ ≥ 0 for all x ∈ K}.
    This is `ProperCone.innerDual` in Mathlib. -/
noncomputable abbrev dualCone (K : Set V) : ProperCone ℝ V := ProperCone.innerDual K

/-- Membership in the dual cone. -/
theorem mem_dualCone {K : Set V} {y : V} :
    y ∈ dualCone K ↔ ∀ x ∈ K, 0 ≤ ⟪x, y⟫_ℝ :=
  ProperCone.mem_innerDual

/-- The nonnegative orthant is self-dual: (ℝ₊ⁿ)* = ℝ₊ⁿ.

    Proof sketch:
    - (⊆) If y ∈ (ℝ₊ⁿ)*, take x = eᵢ (standard basis). Then ⟨eᵢ, y⟩ = yᵢ ≥ 0.
    - (⊇) If y ≥ 0 and x ≥ 0, then ⟨x, y⟩ = Σ xᵢyᵢ ≥ 0. -/
theorem nonnegOrthant_self_dual (n : ℕ) :
    dualCone (nonnegOrthant n : Set _) = nonnegOrthant n := by
  ext y
  simp only [mem_dualCone, SetLike.mem_coe]
  constructor
  · -- If y ∈ dual cone, then y ≥ 0
    intro hy i
    -- Take x = eᵢ, the i-th standard basis vector
    have hei : EuclideanSpace.single i (1 : ℝ) ∈ (nonnegOrthant n : Set _) := by
      simp only [SetLike.mem_coe, mem_nonnegOrthant]
      intro j
      simp only [EuclideanSpace.single_apply]
      split_ifs <;> linarith
    specialize hy _ hei
    rw [show ⟪EuclideanSpace.single i 1, y⟫_ℝ = y.ofLp i from
      by simpa using EuclideanSpace.inner_single_left i (1:ℝ) y] at hy
    exact hy
  · -- If y ≥ 0, then y ∈ dual cone
    intro hy x hx
    -- ⟨x, y⟩ = Σ xᵢyᵢ ≥ 0 since xᵢ, yᵢ ≥ 0
    simp only [mem_nonnegOrthant] at hx hy
    rw [PiLp.inner_apply]
    apply Finset.sum_nonneg
    intro i _
    simp [inner]
    exact mul_nonneg (hy i) (hx i)

/-- The nonnegative half-line is self-dual: (ℝ₊)* = ℝ₊.
    This follows from the fact that for t, s ≥ 0, we have t * s ≥ 0. -/
theorem nonnegHalfLine_self_dual :
    dualCone (nonnegHalfLine : Set ℝ) = nonnegHalfLine := by
  ext s
  simp only [SetLike.mem_coe, mem_dualCone, mem_nonnegHalfLine]
  constructor
  · intro h
    -- Take t = 1 ∈ ℝ₊, get ⟪1, s⟫ = s ≥ 0
    have h1 : (1 : ℝ) ∈ (nonnegHalfLine : Set ℝ) := by simp [mem_nonnegHalfLine]
    specialize h 1 h1
    -- ⟪1, s⟫ = s for real numbers
    have : ⟪(1 : ℝ), s⟫_ℝ = s := by simp [inner]
    linarith
  · intro hs t ht
    -- ⟪t, s⟫ = t * s ≥ 0 since t, s ≥ 0
    have : ⟪t, s⟫_ℝ = t * s := by simp [inner]; ring
    rw [this]
    exact mul_nonneg ht hs

end DualCones

/-! ## Section 4.4: Separation Theorem

Theorem 4.4.2: Let K ⊆ V be a closed convex cone, and b ∉ K.
Then there exists y ∈ V such that ⟨y, x⟩ ≥ 0 for all x ∈ K, and ⟨y, b⟩ < 0.

Lemma 4.4.1: (K*)* = K for closed convex cones.

These are available in Mathlib as:
- `ProperCone.hyperplane_separation'`
- `ProperCone.innerDual_innerDual`
-/

section Separation

/-- Separation theorem for closed convex cones (Theorem 4.4.2).
    If b ∉ K, there exists y with ⟨y, x⟩ ≥ 0 for all x ∈ K and ⟨y, b⟩ < 0. -/
theorem separation_theorem (K : ProperCone ℝ V) (b : V) (hb : b ∉ K) :
    ∃ y : V, (∀ x ∈ (K : Set V), 0 ≤ ⟪x, y⟫_ℝ) ∧ ⟪b, y⟫_ℝ < 0 :=
  ProperCone.hyperplane_separation' K hb

/-- The double dual equals the original cone: (K*)* = K (Lemma 4.4.1). -/
theorem double_dual_eq_self (K : ProperCone ℝ V) :
    dualCone (dualCone (K : Set V) : Set V) = K :=
  ProperCone.innerDual_innerDual K

end Separation

end ConeProgramming
