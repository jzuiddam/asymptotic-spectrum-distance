/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.ConeProgrammingDuality.Cones

/-!
# Cone Programs and Farkas Lemma

This file defines the cone program structure and related feasibility notions,
following Chapter 4 of Gärtner-Matoušek "Approximation Algorithms and Semidefinite Programming".

## Main definitions

* `ConeProgram` : A general cone program: maximize ⟨c, x⟩ subject to b - A(x) ∈ L, x ∈ K
* `ConeProgramEq` : A cone program in equational form (L = {0})
* `ConeProgram.isFeasible` : Feasibility of a cone program
* `ConeProgram.isDualFeasible` : Dual feasibility
* `ConeProgram.isInteriorPoint` : Slater's constraint qualification
* `ConeProgram.limitValue` : The limit value (supremum over feasible sequences)
* `ConeProgram.value` : The value (supremum over feasible points)

## Main results

* `farkas_forward` : Forward direction of Farkas lemma
* `farkas_lemma_cone` : Full Farkas lemma characterization
-/

namespace ConeProgramming

open scoped InnerProductSpace RealInnerProductSpace
open ContinuousLinearMap

/-! ## Section 4.5: Farkas Lemma for Cones

Definition 4.5.5: The system A(x) = b, x ∈ K is limit-feasible if there exists
a sequence (xₖ) with xₖ ∈ K and lim A(xₖ) = b.

Lemma 4.5.6 (Farkas Lemma for Cones): Let K ⊆ V be a closed convex cone.
Either:
- The system A(x) = b, x ∈ K is limit-feasible, OR
- The system Aᵀ(y) ∈ K*, ⟨b, y⟩ < 0 has a solution.
But not both.

This is related to `ProperCone.relative_hyperplane_separation` in Mathlib.
-/

section FarkasLemma

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable (A : V →L[ℝ] W)

/-- The image cone {A(x) : x ∈ K}. -/
def imageCone (K : ProperCone ℝ V) : Set W :=
  {y | ∃ x ∈ (K : Set V), A x = y}

/-- The system A(x) = b, x ∈ K is limit-feasible if b is in the closure of {A(x) : x ∈ K}. -/
def isLimitFeasible (K : ProperCone ℝ V) (b : W) : Prop :=
  b ∈ closure (imageCone A K)

/-- Forward direction of Farkas: If limit-feasible, then no separating witness.

    Proof: If limit-feasible, b is in the closure of {A(x) : x ∈ K}.
    If Aᵀy ∈ K* and y ∈ W, then ⟨y, A(x)⟩ = ⟨Aᵀy, x⟩ ≥ 0 for all x ∈ K.
    So the image cone is contained in the closed half-space {z : ⟨y, z⟩ ≥ 0}.
    By closure, b also satisfies ⟨y, b⟩ ≥ 0.
    But ⟨b, y⟩ = ⟨y, b⟩ (real inner product), contradicting ⟨b, y⟩ < 0. -/
theorem farkas_forward (K : ProperCone ℝ V) (b : W) (hlf : isLimitFeasible A K b) :
    ¬∃ y : W, A.adjoint y ∈ dualCone (K : Set V) ∧ ⟪b, y⟫_ℝ < 0 := by
  intro ⟨y, hAdj, hby⟩
  -- The set {z | 0 ≤ ⟪y, z⟫} is closed
  have hclosed : IsClosed {z : W | 0 ≤ ⟪y, z⟫_ℝ} := by
    have : {z : W | 0 ≤ ⟪y, z⟫_ℝ} = (fun z => ⟪y, z⟫_ℝ) ⁻¹' Set.Ici 0 := by ext z; simp
    rw [this]
    exact IsClosed.preimage (continuous_const.inner continuous_id) isClosed_Ici
  -- The image cone is contained in this set
  have hsubset : imageCone A K ⊆ {z : W | 0 ≤ ⟪y, z⟫_ℝ} := by
    intro z ⟨x, hxK, hAxz⟩
    simp only [Set.mem_setOf_eq]
    rw [← hAxz, ← adjoint_inner_left]
    rw [real_inner_comm]
    exact mem_dualCone.mp hAdj x hxK
  -- So b is also in this set (by closure)
  have hb : b ∈ {z : W | 0 ≤ ⟪y, z⟫_ℝ} :=
    hclosed.closure_subset_iff.mpr hsubset hlf
  -- This means ⟪y, b⟫ ≥ 0, but ⟪b, y⟫ = ⟪y, b⟫ and hby says ⟪b, y⟫ < 0
  simp only [Set.mem_setOf_eq] at hb
  rw [real_inner_comm] at hb
  linarith

/-- The Farkas Lemma for cones (Lemma 4.5.6) stated using ProperCone.map.

    This uses the fact that ProperCone.map takes the closure automatically.
    The characterization is:
    b ∈ closure{A(x) : x ∈ K} ↔ ∀ y, Aᵀ(y) ∈ K* → ⟨b, y⟩ ≥ 0
-/
theorem farkas_lemma_cone (K : ProperCone ℝ V) (b : W) :
    b ∈ ProperCone.map A K ↔ ∀ y : W, A.adjoint y ∈ dualCone (K : Set V) → 0 ≤ ⟪b, y⟫_ℝ :=
  ProperCone.relative_hyperplane_separation

end FarkasLemma

/-! ## Section 4.6: Cone Programs

Definition 4.6.1: A cone program is
  (P) Maximize ⟨c, x⟩
      subject to b - A(x) ∈ L
                 x ∈ K

Definition 4.6.4: An interior point (Slater point) is x with:
- x ∈ K, b - A(x) ∈ L
- x ∈ int(K) if L = {0}, or b - A(x) ∈ int(L) otherwise
-/

section ConePrograms

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- A cone program in equational form (L = {0}):
    maximize ⟨c, x⟩ subject to A(x) = b, x ∈ K -/
structure ConeProgramEq where
  /-- The cone constraint -/
  K : ProperCone ℝ V
  /-- The linear operator in the equality constraint -/
  A : V →L[ℝ] W
  /-- The right-hand side of A(x) = b -/
  b : W
  /-- The objective function coefficient -/
  c : V

/-- A general cone program:
    maximize ⟨c, x⟩ subject to b - A(x) ∈ L, x ∈ K -/
structure ConeProgram where
  /-- The primal cone K ⊆ V -/
  K : ProperCone ℝ V
  /-- The constraint cone L ⊆ W -/
  L : ProperCone ℝ W
  /-- The linear operator -/
  A : V →L[ℝ] W
  /-- The right-hand side -/
  b : W
  /-- The objective coefficient -/
  c : V

namespace ConeProgram

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- A point x is feasible for the cone program if x ∈ K and b - A(x) ∈ L. -/
def isFeasible (P : ConeProgram (V := V) (W := W)) (x : V) : Prop :=
  x ∈ (P.K : Set V) ∧ P.b - P.A x ∈ (P.L : Set W)

/-- The primal objective value ⟨c, x⟩. -/
def objective (P : ConeProgram (V := V) (W := W)) (x : V) : ℝ := ⟪P.c, x⟫_ℝ

/-- The dual cone program:
    (D) minimize ⟨b, y⟩
        subject to Aᵀ(y) - c ∈ K*
                   y ∈ L*
-/
noncomputable def dual (P : ConeProgram (V := V) (W := W)) : ConeProgram (V := W) (W := V) where
  K := dualCone (P.L : Set W)
  L := dualCone (P.K : Set V)
  A := P.A.adjoint
  b := P.c
  c := P.b

/-- A point y is dual feasible if y ∈ L* and Aᵀ(y) - c ∈ K*. -/
def isDualFeasible (P : ConeProgram (V := V) (W := W)) (y : W) : Prop :=
  y ∈ (dualCone (P.L : Set W) : Set W) ∧
  P.A.adjoint y - P.c ∈ (dualCone (P.K : Set V) : Set V)

/-- The dual objective value ⟨b, y⟩. -/
def dualObjective (P : ConeProgram (V := V) (W := W)) (y : W) : ℝ := ⟪P.b, y⟫_ℝ

/-- An interior point satisfies Slater's constraint qualification. -/
def isInteriorPoint (P : ConeProgram (V := V) (W := W)) (x : V) : Prop :=
  P.isFeasible x ∧ P.b - P.A x ∈ interior (P.L : Set W)

/-- For equational form (L = {0}), interior point means x ∈ int(K). -/
def isInteriorPointEq (P : ConeProgramEq (V := V) (W := W)) (x : V) : Prop :=
  P.A x = P.b ∧ x ∈ interior (P.K : Set V)

/-! ### Limit-feasibility and Limit Values (Definition 4.6.2, 4.6.3)

Following Gärtner-Matoušek Definition 4.6.2 and 4.6.3:
- A feasible sequence is a pair (x_k), (x'_k) with x_k ∈ K, x'_k ∈ L, and A(x_k) + x'_k → b
- The value of a feasible sequence is limsup⟨c, x_k⟩
- The limit value is the supremum of values over all feasible sequences
-/

/-- A feasible sequence for the cone program (Definition 4.6.2).
    A pair of sequences (seq, slack) is feasible if:
    - seq n ∈ K for all n
    - slack n ∈ L for all n
    - A(seq n) + slack n → b -/
def isFeasibleSeq (P : ConeProgram (V := V) (W := W)) (seq : ℕ → V) (slack : ℕ → W) : Prop :=
  (∀ n, seq n ∈ (P.K : Set V)) ∧
  (∀ n, slack n ∈ (P.L : Set W)) ∧
  Filter.Tendsto (fun n => P.A (seq n) + slack n) Filter.atTop (nhds P.b)

/-- A feasible sequence for equational form (L = {0}): just seq with A(seq n) → b. -/
def isFeasibleSeqEq (P : ConeProgram (V := V) (W := W)) (seq : ℕ → V) : Prop :=
  (∀ n, seq n ∈ (P.K : Set V)) ∧
  Filter.Tendsto (fun n => P.A (seq n)) Filter.atTop (nhds P.b)

/-- The cone program is limit-feasible if there exists a feasible sequence (Definition 4.5.5). -/
def isLimitFeasibleCP (P : ConeProgram (V := V) (W := W)) : Prop :=
  ∃ seq slack, P.isFeasibleSeq seq slack

/-- The value of a feasible sequence is limsup⟨c, x_k⟩ (Definition 4.6.3).
    We use Filter.limsup which returns an element of EReal. -/
noncomputable def feasibleSeqValue (P : ConeProgram (V := V) (W := W)) (seq : ℕ → V) : EReal :=
  Filter.limsup (fun n => (P.objective (seq n) : EReal)) Filter.atTop

/-- The limit value of a cone program: supremum over all feasible sequences (Definition 4.6.3). -/
noncomputable def limitValue (P : ConeProgram (V := V) (W := W)) : EReal :=
  ⨆ (seq : ℕ → V) (slack : ℕ → W) (_ : P.isFeasibleSeq seq slack), P.feasibleSeqValue seq

/-- The (exact) value of a cone program: supremum over feasible points. -/
noncomputable def value (P : ConeProgram (V := V) (W := W)) : EReal :=
  ⨆ (x : V) (_ : P.isFeasible x), (P.objective x : EReal)

/-- The dual value: infimum over dual feasible points. -/
noncomputable def dualValue (P : ConeProgram (V := V) (W := W)) : EReal :=
  ⨅ (y : W) (_ : P.isDualFeasible y), (P.dualObjective y : EReal)

omit [CompleteSpace V] [CompleteSpace W] in
/-- Every feasible point gives a constant feasible sequence. -/
theorem isFeasible_gives_feasibleSeq (P : ConeProgram (V := V) (W := W)) (x : V)
    (hx : P.isFeasible x) : P.isFeasibleSeq (fun _ => x) (fun _ => P.b - P.A x) := by
  obtain ⟨hxK, hbAx⟩ := hx
  refine ⟨fun _ => hxK, fun _ => hbAx, ?_⟩
  simp only [add_sub_cancel]
  exact tendsto_const_nhds

omit [CompleteSpace V] [CompleteSpace W] in
/-- Value is bounded above by limit value: val(P) ≤ limval(P).
    This is because every feasible point gives a constant feasible sequence
    with limsup equal to the objective value. -/
theorem value_le_limitValue (P : ConeProgram (V := V) (W := W)) :
    P.value ≤ P.limitValue := by
  unfold value limitValue
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  -- x feasible gives constant sequence with value = objective(x)
  have hseq := P.isFeasible_gives_feasibleSeq x hx
  have hval : P.feasibleSeqValue (fun _ => x) = (P.objective x : EReal) := by
    simp only [feasibleSeqValue, Filter.limsup_const]
  calc (P.objective x : EReal) = P.feasibleSeqValue (fun _ => x) := hval.symm
    _ ≤ ⨆ seq, ⨆ slack, ⨆ (_ : P.isFeasibleSeq seq slack), P.feasibleSeqValue seq := by
        apply le_iSup_of_le (fun _ => x)
        apply le_iSup_of_le (fun _ => P.b - P.A x)
        apply le_iSup_of_le hseq
        rfl

/-! ### Slater Points (Interior Points)

A Slater point (Definition 4.6.4) is an interior point for Slater's constraint
qualification. For equational form, this means x ∈ int(K) with A(x) = b.
-/

/-- A Slater point for equational form: x ∈ int(K) and A(x) = b. -/
def isSlaterPointEq (P : ConeProgram (V := V) (W := W)) (x : V) : Prop :=
  x ∈ interior (P.K : Set V) ∧ P.A x = P.b

end ConeProgram

end ConePrograms

end ConeProgramming
