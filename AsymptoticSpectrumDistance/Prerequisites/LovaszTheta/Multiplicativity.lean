/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Lovász θ multiplicativity (≤ direction)

Proves `lovaszTheta (G ⊠ H) ≤ lovaszTheta G * lovaszTheta H` (the inequality
direction of Lovász's multiplicativity theorem) on top of `Tensor.lean`.

The reverse direction `θ(G ⊠ H) ≥ θ(G) · θ(H)` requires SDP strong duality,
which we do not need here — for the disc-check application we only need the
upper bound on `α`.

## Main results

* `iSup_prod_factor` : `(⨆ vw, f vw.1 * g vw.2) = (⨆ v, f v) * (⨆ w, g w)`
  for nonneg `f`, `g` over Fintype × Fintype.
* `thetaRepValue_nonneg`, `repValueSet_nonempty`, `repValueSet_bddBelow`,
  `lovaszTheta_nonneg`.
* `thetaRepValue_thetaRep_tensor` : `thetaRepValue` of a tensor rep factors.
* `lovaszTheta_strongProduct_le` : `θ(G ⊠ H) ≤ θ(G) · θ(H)`.
-/

import AsymptoticSpectrumDistance.Prerequisites.LovaszTheta.Tensor
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import Mathlib.Data.Real.Pointwise

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Universality

open scoped BigOperators
open SimpleGraph ShannonCapacity

/-! ## sSup over Cartesian product factors as a product (nonneg case) -/

lemma iSup_prod_factor {V W : Type*} [Fintype V] [Fintype W] [Nonempty V] [Nonempty W]
    (f : V → ℝ) (g : W → ℝ) (hf : ∀ v, 0 ≤ f v) (hg : ∀ w, 0 ≤ g w) :
    (⨆ vw : V × W, f vw.1 * g vw.2) = (⨆ v, f v) * (⨆ w, g w) := by
  classical
  apply le_antisymm
  · apply ciSup_le
    intro vw
    have h1 : f vw.1 ≤ ⨆ v, f v := le_ciSup (Finite.bddAbove_range f) vw.1
    have h2 : g vw.2 ≤ ⨆ w, g w := le_ciSup (Finite.bddAbove_range g) vw.2
    have hfv_nn : 0 ≤ f vw.1 := hf _
    have hsupg_nn : 0 ≤ ⨆ w, g w := Real.iSup_nonneg hg
    nlinarith
  · have hsupg_nn : 0 ≤ ⨆ w, g w := Real.iSup_nonneg hg
    rw [Real.iSup_mul_of_nonneg hsupg_nn]
    apply ciSup_le; intro v
    rw [Real.mul_iSup_of_nonneg (hf v)]
    apply ciSup_le; intro w
    exact le_ciSup (Finite.bddAbove_range (fun (vw : V × W) => f vw.1 * g vw.2)) (v, w)

/-! ## Nonneg, nonempty, bddBelow for the rep-value set -/

variable {V : Type*} [Fintype V]

lemma thetaRepValue_nonneg {n : ℕ} {G : SimpleGraph V} (rep : ThetaOrthonormalRep G n) :
    0 ≤ thetaRepValue G rep := by
  unfold thetaRepValue
  apply Real.sSup_nonneg
  rintro x ⟨v, rfl⟩
  positivity

lemma repValueSet_bddBelow (G : SimpleGraph V) :
    BddBelow {t : ℝ | ∃ n, ∃ rep : ThetaOrthonormalRep (Gᶜ) n, t = thetaRepValue (Gᶜ) rep} := by
  refine ⟨0, ?_⟩
  rintro x ⟨_, rep, rfl⟩
  exact thetaRepValue_nonneg rep

lemma repValueSet_nonempty (G : SimpleGraph V) :
    {t : ℝ | ∃ n, ∃ rep : ThetaOrthonormalRep (Gᶜ) n, t = thetaRepValue (Gᶜ) rep}.Nonempty := by
  classical
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    refine ⟨0, 1, ?_, ?_⟩
    · exact { vec := fun v => (IsEmpty.elim ‹IsEmpty V› v)
              handle := EuclideanSpace.single 0 (1 : ℝ)
              vec_norm := fun v => (IsEmpty.elim ‹IsEmpty V› v)
              handle_norm := by simp
              inner_ne_zero := fun v => (IsEmpty.elim ‹IsEmpty V› v)
              orthogonal := fun {v} => (IsEmpty.elim ‹IsEmpty V› v) }
    · simp only [thetaRepValue]
      have hempty : Set.range (fun v : V =>
          (1 : ℝ) / ‖@inner ℝ _ _ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
            (IsEmpty.elim ‹IsEmpty V› v)‖ ^ 2) = ∅ := by
        rw [Set.range_eq_empty_iff]; exact ‹IsEmpty V›
      rw [hempty, Real.sSup_empty]
  · have hV' : 0 < Fintype.card V := Nat.pos_of_ne_zero hV
    haveI : Nonempty V := Fintype.card_pos_iff.mp hV'
    let m := Fintype.card V
    let e : V ≃ Fin m := Fintype.equivFin V
    let baseHandle : EuclideanSpace ℝ (Fin m) :=
      ∑ i : Fin m, (1 : ℝ) • EuclideanSpace.single i (1 : ℝ)
    have hnorm0 : ‖baseHandle‖ ≠ 0 := by
      obtain ⟨v0⟩ : Nonempty V := inferInstance
      intro h
      have hz : baseHandle = 0 := norm_eq_zero.mp h
      have h1 : @inner ℝ _ _ baseHandle (EuclideanSpace.single (e v0) (1 : ℝ)) = 0 := by
        simp [hz]
      have h2 : @inner ℝ _ _ baseHandle (EuclideanSpace.single (e v0) (1 : ℝ)) = 1 := by
        simpa [baseHandle] using (EuclideanSpace.orthonormal_single (𝕜 := ℝ)
          |>.inner_left_fintype (l := fun _ => (1 : ℝ)) (i := e v0))
      linarith
    exact ⟨thetaRepValue (Gᶜ)
      { vec := fun v => EuclideanSpace.single (e v) (1 : ℝ)
        handle := (1 / ‖baseHandle‖) • baseHandle
        vec_norm := by intro v; simp
        handle_norm := by
          have hn : 0 ≤ (1 / ‖baseHandle‖ : ℝ) := one_div_nonneg.mpr (norm_nonneg _)
          calc ‖(1 / ‖baseHandle‖ : ℝ) • baseHandle‖
              = |(1 / ‖baseHandle‖ : ℝ)| * ‖baseHandle‖ := by simp [norm_smul]
            _ = (1 / ‖baseHandle‖ : ℝ) * ‖baseHandle‖ := by rw [abs_of_nonneg hn]
            _ = 1 := by field_simp [hnorm0]
        inner_ne_zero := by
          intro v
          have hi : @inner ℝ _ _ ((1 / ‖baseHandle‖ : ℝ) • baseHandle)
              (EuclideanSpace.single (e v) (1 : ℝ))
              = (1 / ‖baseHandle‖ : ℝ) * @inner ℝ _ _ baseHandle
                (EuclideanSpace.single (e v) (1 : ℝ)) := by
            simp [inner_smul_left]
          have ho : @inner ℝ _ _ baseHandle
              (EuclideanSpace.single (e v) (1 : ℝ)) = 1 := by
            simpa [baseHandle] using (EuclideanSpace.orthonormal_single (𝕜 := ℝ)
              |>.inner_left_fintype (l := fun _ => (1 : ℝ)) (i := e v))
          rw [hi, ho, mul_one]; exact one_div_ne_zero hnorm0
        orthogonal := by
          intro v w hvw
          have hne : v ≠ w := (Gᶜ).ne_of_adj hvw
          simpa using EuclideanSpace.orthonormal_single (𝕜 := ℝ)
            |>.inner_eq_zero (fun h => hne (e.injective h)) },
      ⟨m, _, rfl⟩⟩

lemma lovaszTheta_nonneg (G : SimpleGraph V) : 0 ≤ lovaszTheta G := by
  unfold lovaszTheta
  apply le_csInf (repValueSet_nonempty G)
  intro t ht
  obtain ⟨_, rep, rfl⟩ := ht
  exact thetaRepValue_nonneg rep

/-! ## `thetaRepValue` factors over the tensor product -/

variable {W : Type*} [Fintype W] [DecidableEq W]
variable [Nonempty V] [Nonempty W] [DecidableEq V]
variable {G : SimpleGraph V} {H : SimpleGraph W}

theorem thetaRepValue_thetaRep_tensor {n m : ℕ}
    (f : ThetaOrthonormalRep (Gᶜ) n) (g : ThetaOrthonormalRep (Hᶜ) m) :
    thetaRepValue ((strongProduct G H)ᶜ) (thetaRep_tensor f g) =
      thetaRepValue (Gᶜ) f * thetaRepValue (Hᶜ) g := by
  unfold thetaRepValue
  rw [show sSup (Set.range fun (vw : V × W) =>
        (1 : ℝ) / ‖@inner ℝ _ _ (thetaRep_tensor f g).handle ((thetaRep_tensor f g).vec vw)‖ ^ 2) =
      ⨆ vw : V × W,
        (1 : ℝ) / ‖@inner ℝ _ _ (thetaRep_tensor f g).handle ((thetaRep_tensor f g).vec vw)‖ ^ 2
      from rfl]
  rw [show sSup (Set.range fun v =>
        (1 : ℝ) / ‖@inner ℝ _ _ f.handle (f.vec v)‖ ^ 2) =
      ⨆ v : V,
        (1 : ℝ) / ‖@inner ℝ _ _ f.handle (f.vec v)‖ ^ 2 from rfl]
  rw [show sSup (Set.range fun w =>
        (1 : ℝ) / ‖@inner ℝ _ _ g.handle (g.vec w)‖ ^ 2) =
      ⨆ w : W,
        (1 : ℝ) / ‖@inner ℝ _ _ g.handle (g.vec w)‖ ^ 2 from rfl]
  have h_simp : ∀ vw : V × W,
      (1 : ℝ) / ‖@inner ℝ _ _ (thetaRep_tensor f g).handle ((thetaRep_tensor f g).vec vw)‖ ^ 2 =
        (1 / ‖@inner ℝ _ _ f.handle (f.vec vw.1)‖ ^ 2) *
          (1 / ‖@inner ℝ _ _ g.handle (g.vec vw.2)‖ ^ 2) := by
    intro vw
    change (1 : ℝ) / ‖@inner ℝ _ _ (kronecker f.handle g.handle)
                    (kronecker (f.vec vw.1) (g.vec vw.2))‖ ^ 2 = _
    rw [kronecker_inner]
    rw [show ‖(@inner ℝ _ _ f.handle (f.vec vw.1)) * (@inner ℝ _ _ g.handle (g.vec vw.2))‖ =
         ‖@inner ℝ _ _ f.handle (f.vec vw.1)‖ * ‖@inner ℝ _ _ g.handle (g.vec vw.2)‖ from
       norm_mul _ _]
    rw [mul_pow, one_div, mul_inv]
    ring
  rw [show (⨆ vw : V × W,
        (1 : ℝ) / ‖@inner ℝ _ _ (thetaRep_tensor f g).handle ((thetaRep_tensor f g).vec vw)‖ ^ 2) =
      ⨆ vw : V × W,
        (1 / ‖@inner ℝ _ _ f.handle (f.vec vw.1)‖ ^ 2) *
          (1 / ‖@inner ℝ _ _ g.handle (g.vec vw.2)‖ ^ 2) from
    iSup_congr h_simp]
  exact iSup_prod_factor (fun v => 1 / ‖@inner ℝ _ _ f.handle (f.vec v)‖ ^ 2)
    (fun w => 1 / ‖@inner ℝ _ _ g.handle (g.vec w)‖ ^ 2)
    (fun _ => by positivity) (fun _ => by positivity)

/-! ## Lovász θ multiplicativity (≤ direction)

Given any reps `f, g` of `Gᶜ, Hᶜ`, the tensor rep gives an upper bound on
`lovaszTheta (G ⊠ H)` of `thetaRepValue f * thetaRepValue g`. Using
`Real.sInf_smul_of_nonneg` to factor `sInf` over multiplication by a nonneg
constant, we can take `sInf` over `f` and `g` separately. -/

/-- For `c ≥ 0` and a set `S ⊆ ℝ`, `c * sInf S = sInf ((c * ·) '' S)`. -/
private lemma mul_csInf_eq {c : ℝ} (hc : 0 ≤ c) (s : Set ℝ) :
    c * sInf s = sInf ((fun x => c * x) '' s) := by
  have h := Real.sInf_smul_of_nonneg hc s
  -- h : sInf (c • s) = c • sInf s. For ℝ, smul = mul.
  simp only [smul_eq_mul] at h
  -- h : sInf ((c * ·) '' s) = c * sInf s, modulo c • s vs (c * ·) '' s.
  rw [← h]
  rfl

/-- **Lovász multiplicativity (≤ direction).** -/
theorem lovaszTheta_strongProduct_le (G : SimpleGraph V) (H : SimpleGraph W) :
    lovaszTheta (strongProduct G H) ≤ lovaszTheta G * lovaszTheta H := by
  classical
  -- Step 1: For each (n, f, m, g), lovaszTheta (G⊠H) ≤ thetaRepValue f * thetaRepValue g.
  have h_per_rep : ∀ {n m : ℕ} (f : ThetaOrthonormalRep (Gᶜ) n)
      (g : ThetaOrthonormalRep (Hᶜ) m),
      lovaszTheta (strongProduct G H) ≤ thetaRepValue (Gᶜ) f * thetaRepValue (Hᶜ) g := by
    intro n m f g
    have h_in : thetaRepValue ((strongProduct G H)ᶜ) (thetaRep_tensor f g) ∈
        {t : ℝ | ∃ n, ∃ rep : ThetaOrthonormalRep ((strongProduct G H)ᶜ) n,
          t = thetaRepValue ((strongProduct G H)ᶜ) rep} :=
      ⟨n * m, thetaRep_tensor f g, rfl⟩
    have h_le : lovaszTheta (strongProduct G H) ≤
        thetaRepValue ((strongProduct G H)ᶜ) (thetaRep_tensor f g) := by
      unfold lovaszTheta
      exact csInf_le (repValueSet_bddBelow _) h_in
    rwa [thetaRepValue_thetaRep_tensor] at h_le
  -- Step 2: Fix g, take sInf over f.
  -- For each tg = thetaRepValue Hᶜ g, lovaszTheta (G⊠H) ≤ lovaszTheta G * tg.
  have h_per_g : ∀ {m : ℕ} (g : ThetaOrthonormalRep (Hᶜ) m),
      lovaszTheta (strongProduct G H) ≤ lovaszTheta G * thetaRepValue (Hᶜ) g := by
    intro m g
    have h_θg_nn : 0 ≤ thetaRepValue (Hᶜ) g := thetaRepValue_nonneg g
    rw [mul_comm]
    unfold lovaszTheta
    rw [mul_csInf_eq h_θg_nn]
    apply le_csInf
    · -- nonempty
      obtain ⟨tf, n, f, rfl⟩ := repValueSet_nonempty G
      exact ⟨thetaRepValue (Hᶜ) g * thetaRepValue (Gᶜ) f,
        ⟨thetaRepValue (Gᶜ) f, ⟨n, f, rfl⟩, rfl⟩⟩
    · rintro x ⟨_, ⟨n, f, rfl⟩, rfl⟩
      simp only
      rw [mul_comm]
      exact h_per_rep f g
  -- Step 3: Take sInf over g.
  -- lovaszTheta G * lovaszTheta H = sInf (Set.image (lovaszTheta G * ·) S_H) for lovaszTheta G ≥ 0.
  have h_θG_nn : 0 ≤ lovaszTheta G := lovaszTheta_nonneg G
  have h_eq2 : lovaszTheta G * lovaszTheta H =
      sInf ((fun x => lovaszTheta G * x) ''
        {t : ℝ | ∃ m, ∃ g : ThetaOrthonormalRep (Hᶜ) m, t = thetaRepValue (Hᶜ) g}) := by
    unfold lovaszTheta
    exact mul_csInf_eq h_θG_nn _
  rw [h_eq2]
  apply le_csInf
  · obtain ⟨tg, m, g, rfl⟩ := repValueSet_nonempty H
    exact ⟨lovaszTheta G * thetaRepValue (Hᶜ) g, ⟨thetaRepValue (Hᶜ) g, ⟨m, g, rfl⟩, rfl⟩⟩
  · rintro x ⟨_, ⟨m, g, rfl⟩, rfl⟩
    simp only
    exact h_per_g g

/-! ## Monotonicity: `Gᶜ →g Hᶜ → θ(G) ≤ θ(H)` -/

/-- Pull back a `ThetaOrthonormalRep` along a graph hom `Gᶜ →g Hᶜ`. -/
noncomputable def pullbackRep {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : Gᶜ →g Hᶜ) {n : ℕ} (rep : ThetaOrthonormalRep (Hᶜ) n) :
    ThetaOrthonormalRep (Gᶜ) n where
  vec := fun v => rep.vec (f v)
  handle := rep.handle
  vec_norm := fun v => rep.vec_norm (f v)
  handle_norm := rep.handle_norm
  inner_ne_zero := fun v => rep.inner_ne_zero (f v)
  orthogonal := fun {_v _w} hvw => rep.orthogonal (f.map_adj hvw)

lemma pullbackRep_value_le {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : Gᶜ →g Hᶜ) {n : ℕ} (rep : ThetaOrthonormalRep (Hᶜ) n) :
    thetaRepValue (Gᶜ) (pullbackRep f rep) ≤ thetaRepValue (Hᶜ) rep := by
  unfold thetaRepValue pullbackRep
  simp only
  by_cases hV : IsEmpty V
  · rw [Set.range_eq_empty_iff.mpr hV]
    simp only [Real.sSup_empty]
    exact Real.sSup_nonneg (fun x hx => by obtain ⟨w, rfl⟩ := hx; positivity)
  · rw [not_isEmpty_iff] at hV
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨v, rfl⟩ := hx
    exact le_csSup (Set.finite_range _).bddAbove ⟨f v, rfl⟩

/-- **Lovász θ monotonicity:** if there's a hom `Gᶜ →g Hᶜ` then `θ(G) ≤ θ(H)`. -/
theorem lovaszTheta_mono_of_complHom {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : Gᶜ →g Hᶜ) : lovaszTheta G ≤ lovaszTheta H := by
  unfold lovaszTheta
  apply le_csInf (repValueSet_nonempty H)
  intro t ht
  obtain ⟨n, rep, rfl⟩ := ht
  have h1 : sInf {t | ∃ n, ∃ rep : ThetaOrthonormalRep (Gᶜ) n,
      t = thetaRepValue (Gᶜ) rep} ≤ thetaRepValue (Gᶜ) (pullbackRep f rep) := by
    apply csInf_le (repValueSet_bddBelow G)
    exact ⟨n, pullbackRep f rep, rfl⟩
  exact le_trans h1 (pullbackRep_value_le f rep)

/-- `θ` monotone under cohom (`G ≤_G H → θ(G) ≤ θ(H)`). The cohom in our codebase
    is `Cohom G H = ∃ f : V → W, IsCohom G H f`, which (via `cohomLE_to_cohom` /
    its converse) is equivalent to a hom `Gᶜ →g Hᶜ`. -/
theorem lovaszTheta_mono_of_cohom {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (h : G ≤_G H) :
    lovaszTheta G ≤ lovaszTheta H := by
  obtain ⟨φ, hφ⟩ := h
  -- IsCohom: ∀ u v, u ≠ v → ¬G.Adj u v → φ u ≠ φ v ∧ ¬H.Adj (φ u) (φ v).
  -- Equivalently: a hom Gᶜ →g Hᶜ since Gᶜ.Adj iff (u ≠ v ∧ ¬G.Adj u v).
  have h_hom : Gᶜ →g Hᶜ := {
    toFun := φ
    map_rel' := fun {u v} hAdj => by
      rw [SimpleGraph.compl_adj] at hAdj
      obtain ⟨hne, hnAdj⟩ := hAdj
      have ⟨h1, h2⟩ := hφ u v hne hnAdj
      rw [SimpleGraph.compl_adj]
      exact ⟨h1, h2⟩ }
  exact lovaszTheta_mono_of_complHom h_hom

/-! ## Bridge to `α(G ⊠ H) ≤ θ(G) · θ(H)`

The Shannon-capacity application. `α(G) = ω(Gᶜ) ≤ θ(G)` (clique number bound,
already in `Defs.lean`), so `α(G ⊠ H) ≤ θ(G ⊠ H) ≤ θ(G) · θ(H)`. -/

omit [Nonempty V] [DecidableEq V] in
/-- `α(G) ≤ θ(G)` for any finite graph: independence number bounded by Lovász theta. -/
lemma indepNum_le_lovaszTheta (G : SimpleGraph V) : (G.indepNum : ℝ) ≤ lovaszTheta G := by
  -- α(G) = ω(Gᶜ) by SimpleGraph.cliqueNum_compl.
  rw [show ((G.indepNum : ℕ) : ℝ) = ((Gᶜ).cliqueNum : ℝ) by
    exact_mod_cast (SimpleGraph.cliqueNum_compl (G := G)).symm]
  exact cliqueNum_compl_le_lovaszTheta G

/-- `α(G ⊠ H) ≤ θ(G) · θ(H)`: tightest spectral upper bound on indepNum of strongProduct. -/
theorem indepNum_strongProduct_le_lovaszTheta_mul (G : SimpleGraph V) (H : SimpleGraph W) :
    ((strongProduct G H).indepNum : ℝ) ≤ lovaszTheta G * lovaszTheta H :=
  (indepNum_le_lovaszTheta _).trans (lovaszTheta_strongProduct_le G H)

end Universality
