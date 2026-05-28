/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.BigOperators

/-!
# Lovász theta function

Defines the Lovász theta function via the orthonormal-representation form
(`lovaszTheta` = `1 / sSup (handle ⬝ u_v)²` over valid orthonormal handles
and vector assignments). The SDP form is defined elsewhere; this file
contains the definitions used by Tensor multiplicativity and monotonicity
(see `LovaszTheta/Tensor.lean` and `LovaszTheta/Multiplicativity.lean`).
-/

namespace Universality

open scoped BigOperators
open SimpleGraph

/-! ## Orthonormal representation definition -/

structure ThetaOrthonormalRep {V : Type*} (G : SimpleGraph V) (n : ℕ) where
  vec : V → EuclideanSpace ℝ (Fin n)
  handle : EuclideanSpace ℝ (Fin n)
  vec_norm : ∀ v, ‖vec v‖ = 1
  handle_norm : ‖handle‖ = 1
  inner_ne_zero : ∀ v, inner (𝕜 := ℝ) handle (vec v) ≠ 0
  orthogonal : ∀ {v w}, G.Adj v w → inner (𝕜 := ℝ) (vec v) (vec w) = 0

noncomputable def thetaRepValue {V : Type*} [Fintype V] {n : ℕ}
    (G : SimpleGraph V) (rep : ThetaOrthonormalRep G n) : ℝ :=
  sSup (Set.range fun v : V =>
    (1 : ℝ) / ‖inner (𝕜 := ℝ) rep.handle (rep.vec v)‖ ^ 2)

noncomputable def lovaszTheta {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf {t : ℝ | ∃ n, ∃ rep : ThetaOrthonormalRep (Gᶜ) n,
    t = thetaRepValue (Gᶜ) rep}

/-! ### Clique bound -/

section CliqueBound

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}

lemma clique_card_le_thetaRepValue (rep : ThetaOrthonormalRep (Gᶜ) n) (s : Finset V)
    (hs : (Gᶜ).IsClique s) : (s.card : ℝ) ≤ thetaRepValue (Gᶜ) rep := by
  classical
  by_cases hsne : s.Nonempty
  · have hs_pair : (s : Set V).Pairwise (Gᶜ).Adj := by
      simpa [SimpleGraph.isClique_iff] using hs
    let u : {v // v ∈ s} → EuclideanSpace ℝ (Fin n) := fun v => rep.vec v
    have hu : Orthonormal ℝ u := by
      refine ⟨?_, ?_⟩
      · intro v
        simpa using rep.vec_norm v
      · intro v w hne
        have hne' : (v : V) ≠ w := by
          exact Subtype.coe_ne_coe.mpr hne
        have hAdj : (Gᶜ).Adj (v : V) (w : V) :=
          hs_pair v.property w.property hne'
        simpa [u] using rep.orthogonal hAdj
    have hBessel :=
      (Orthonormal.sum_inner_products_le (𝕜 := ℝ) (v := u)
        (s := (Finset.univ : Finset {v // v ∈ s})) (x := rep.handle) hu)
    have hBessel' :
        Finset.sum s.attach (fun v =>
          inner (𝕜 := ℝ) (rep.vec v) rep.handle ^ 2) ≤ ‖rep.handle‖ ^ 2 := by
      simpa [Finset.univ_eq_attach, u, Real.norm_eq_abs, sq_abs] using hBessel
    have hsum' :
        Finset.sum s (fun v =>
          inner (𝕜 := ℝ) (rep.vec v) rep.handle ^ 2) ≤ ‖rep.handle‖ ^ 2 := by
      have hsum_eq :
          Finset.sum s.attach (fun v =>
            inner (𝕜 := ℝ) (rep.vec v) rep.handle ^ 2) =
            Finset.sum s (fun v =>
              inner (𝕜 := ℝ) (rep.vec v) rep.handle ^ 2) := by
        exact (Finset.sum_attach (s := s)
          (f := fun v : V => inner (𝕜 := ℝ) (rep.vec v) rep.handle ^ 2))
      rw [← hsum_eq]
      exact hBessel'
    have hnorm : ‖rep.handle‖ ^ 2 = (1 : ℝ) := by
      simp [rep.handle_norm]
    have hsum'' :
        Finset.sum s (fun v =>
          inner (𝕜 := ℝ) rep.handle (rep.vec v) ^ 2) ≤ ‖rep.handle‖ ^ 2 := by
      simpa [real_inner_comm] using hsum'
    have hsum :
        Finset.sum s (fun v =>
          inner (𝕜 := ℝ) rep.handle (rep.vec v) ^ 2) ≤ 1 := by
      simpa [hnorm] using hsum''
    have hkpos : 0 < (s.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr hsne)
    have hexists :
        ∃ v ∈ s, inner (𝕜 := ℝ) rep.handle (rep.vec v) ^ 2 ≤
          (1 : ℝ) / (s.card : ℝ) := by
      by_contra h
      push_neg at h
      have hsum_lt :
          Finset.sum s (fun _ => (1 : ℝ) / (s.card : ℝ)) <
            Finset.sum s (fun v =>
              inner (𝕜 := ℝ) rep.handle (rep.vec v) ^ 2) := by
        exact Finset.sum_lt_sum_of_nonempty hsne h
      have hsum_one :
          (1 : ℝ) <
            Finset.sum s (fun v =>
              inner (𝕜 := ℝ) rep.handle (rep.vec v) ^ 2) := by
        have hk : (s.card : ℝ) ≠ 0 := by
          exact_mod_cast (Finset.card_ne_zero.mpr hsne)
        have hconst :
            Finset.sum s (fun _ => (1 : ℝ) / (s.card : ℝ)) =
              (s.card : ℝ) * (s.card : ℝ)⁻¹ := by
          simp [one_div]
        have hmul : (s.card : ℝ) * (s.card : ℝ)⁻¹ = 1 := by
          field_simp [hk]
        have hsum_lt' :
            (s.card : ℝ) * (s.card : ℝ)⁻¹ <
              Finset.sum s (fun v =>
                inner (𝕜 := ℝ) rep.handle (rep.vec v) ^ 2) := by
          simpa [hconst] using hsum_lt
        simpa [hmul] using hsum_lt'
      exact (lt_of_lt_of_le hsum_one hsum).false
    rcases hexists with ⟨v, hv, hbound⟩
    have hpos : 0 < inner (𝕜 := ℝ) rep.handle (rep.vec v) ^ 2 := by
      have hne : inner (𝕜 := ℝ) rep.handle (rep.vec v) ≠ 0 :=
        rep.inner_ne_zero v
      exact sq_pos_of_ne_zero hne
    have hge :
        (s.card : ℝ) ≤ (1 : ℝ) / inner (𝕜 := ℝ) rep.handle (rep.vec v) ^ 2 := by
      have hpos' : 0 < (1 : ℝ) / (s.card : ℝ) := by
        nlinarith [hkpos]
      have hinv := one_div_le_one_div_of_le hpos hbound
      have hmul : (1 : ℝ) / ((1 : ℝ) / (s.card : ℝ)) = (s.card : ℝ) := by
        field_simp [hkpos.ne']
      simpa [one_div, hmul] using hinv
    have hge' :
        (s.card : ℝ) ≤ (1 : ℝ) / ‖inner (𝕜 := ℝ) rep.handle (rep.vec v)‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using hge
    have hbdd : BddAbove (Set.range fun v : V =>
        (1 : ℝ) / ‖inner (𝕜 := ℝ) rep.handle (rep.vec v)‖ ^ 2) := by
      exact (Set.finite_range _).bddAbove
    have hmem :
        (1 : ℝ) / ‖inner (𝕜 := ℝ) rep.handle (rep.vec v)‖ ^ 2 ∈
          Set.range fun v : V =>
            (1 : ℝ) / ‖inner (𝕜 := ℝ) rep.handle (rep.vec v)‖ ^ 2 := by
      exact ⟨v, rfl⟩
    have hsup :
        (1 : ℝ) / ‖inner (𝕜 := ℝ) rep.handle (rep.vec v)‖ ^ 2 ≤
          sSup (Set.range fun v : V =>
            (1 : ℝ) / ‖inner (𝕜 := ℝ) rep.handle (rep.vec v)‖ ^ 2) :=
      le_csSup hbdd hmem
    exact le_trans hge' hsup
  · have hcard : (s.card : ℝ) = 0 := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hsne
    have hnonneg : 0 ≤ thetaRepValue (Gᶜ) rep := by
      refine Real.sSup_nonneg ?_
      intro x hx
      rcases hx with ⟨v, rfl⟩
      have hsq : 0 ≤ ‖inner (𝕜 := ℝ) rep.handle (rep.vec v)‖ ^ 2 := by
        nlinarith
      exact one_div_nonneg.mpr hsq
    simpa [hcard] using hnonneg

theorem cliqueNum_compl_le_lovaszTheta (G : SimpleGraph V) :
    ((Gᶜ).cliqueNum : ℝ) ≤ lovaszTheta G := by
  classical
  obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
  have hs' : (Gᶜ).IsClique s := by
    exact (SimpleGraph.isNClique_iff (G := Gᶜ) (n := (Gᶜ).cliqueNum) (s := s)).1 hs |>.1
  have hcard : (s.card : ℝ) = (Gᶜ).cliqueNum := by
    have hcard_nat :
        s.card = (Gᶜ).cliqueNum :=
      (SimpleGraph.isNClique_iff (G := Gᶜ) (n := (Gᶜ).cliqueNum) (s := s)).1 hs |>.2
    exact_mod_cast hcard_nat
  have hne :
      ({t : ℝ | ∃ n, ∃ rep : ThetaOrthonormalRep (Gᶜ) n,
        t = thetaRepValue (Gᶜ) rep}).Nonempty := by
    classical
    by_cases hV : (Fintype.card V = 0)
    · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      have hVempty : IsEmpty V := inferInstance
      let rep : ThetaOrthonormalRep (Gᶜ) 1 :=
        { vec := fun v => (IsEmpty.elim hVempty v)
          handle := EuclideanSpace.single 0 (1 : ℝ)
          vec_norm := by intro v; exact (IsEmpty.elim hVempty v)
          handle_norm := by simp
          inner_ne_zero := by intro v; exact (IsEmpty.elim hVempty v)
          orthogonal := by intro v w h; exact (IsEmpty.elim hVempty v) }
      exact ⟨thetaRepValue (Gᶜ) rep, ⟨1, rep, rfl⟩⟩
    · let n := Fintype.card V
      let e : V ≃ Fin n := Fintype.equivFin V
      let baseHandle : EuclideanSpace ℝ (Fin n) :=
        ∑ i : Fin n, (1 : ℝ) • EuclideanSpace.single i (1 : ℝ)
      let handle : EuclideanSpace ℝ (Fin n) := (1 / ‖baseHandle‖) • baseHandle
      let vec : V → EuclideanSpace ℝ (Fin n) :=
        fun v => EuclideanSpace.single (e v) (1 : ℝ)
      have horth : Orthonormal ℝ (fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) :=
        EuclideanSpace.orthonormal_single
      have hinner_base (v : V) :
          inner (𝕜 := ℝ) baseHandle (vec v) = 1 := by
        simpa [baseHandle, vec] using
          (Orthonormal.inner_left_fintype (𝕜 := ℝ) (v := fun i : Fin n =>
            EuclideanSpace.single i (1 : ℝ)) horth (l := fun _ => (1 : ℝ)) (i := e v))
      have hnorm0 : ‖baseHandle‖ ≠ 0 := by
        have hpos : 0 < Fintype.card V := Nat.pos_of_ne_zero hV
        obtain ⟨v0⟩ : Nonempty V := (Fintype.card_pos_iff.mp hpos)
        intro hnorm
        have hzero : baseHandle = 0 := by
          simpa [norm_eq_zero] using hnorm
        have hinner_zero : inner (𝕜 := ℝ) baseHandle (vec v0) = 0 := by
          simp [hzero]
        have hinner_one : inner (𝕜 := ℝ) baseHandle (vec v0) = 1 := hinner_base v0
        have : (1 : ℝ) = 0 := by
          exact hinner_one.symm.trans hinner_zero
        exact one_ne_zero this
      let rep : ThetaOrthonormalRep (Gᶜ) n :=
        { vec := vec
          handle := handle
          vec_norm := by intro v; simp [vec]
          handle_norm := by
            have hnonneg : 0 ≤ (1 / ‖baseHandle‖ : ℝ) := by
              exact one_div_nonneg.mpr (norm_nonneg _)
            have habs : |(1 / ‖baseHandle‖ : ℝ)| = (1 / ‖baseHandle‖ : ℝ) :=
              abs_of_nonneg hnonneg
            calc
              ‖handle‖ = ‖(1 / ‖baseHandle‖ : ℝ)‖ * ‖baseHandle‖ := by
                simp [handle, norm_smul]
              _ = |(1 / ‖baseHandle‖ : ℝ)| * ‖baseHandle‖ := by
                rfl
              _ = (1 / ‖baseHandle‖ : ℝ) * ‖baseHandle‖ := by
                rw [habs]
              _ = 1 := by
                field_simp [hnorm0]
          inner_ne_zero := by
            intro v
            have hinner :
                inner (𝕜 := ℝ) handle (vec v) =
                  (1 / ‖baseHandle‖ : ℝ) * inner (𝕜 := ℝ) baseHandle (vec v) := by
              simp [handle, inner_smul_left]
            have hinner' :
                inner (𝕜 := ℝ) handle (vec v) = (1 / ‖baseHandle‖ : ℝ) := by
              simpa [hinner_base v] using hinner
            have hneq : (1 / ‖baseHandle‖ : ℝ) ≠ 0 := one_div_ne_zero hnorm0
            simpa [hinner'] using hneq
          orthogonal := by
            intro v w hvw
            have hne : v ≠ w := (Gᶜ).ne_of_adj hvw
            have hne' : e v ≠ e w := by
              exact fun h => hne (e.injective h)
            simpa [vec] using (Orthonormal.inner_eq_zero horth hne') }
      exact ⟨thetaRepValue (Gᶜ) rep, ⟨n, rep, rfl⟩⟩
  have hbound :
      (s.card : ℝ) ≤
        sInf {t : ℝ | ∃ n, ∃ rep : ThetaOrthonormalRep (Gᶜ) n,
          t = thetaRepValue (Gᶜ) rep} := by
    refine le_csInf hne ?_
    intro t ht
    rcases ht with ⟨n, rep, rfl⟩
    exact clique_card_le_thetaRepValue rep s hs'
  simpa [lovaszTheta, hcard] using hbound

end CliqueBound

/-! ## SDP formulation -/

def thetaSDPMatrixSum {V : Type*} [Fintype V] (M : Matrix V V ℝ) : ℝ :=
  ∑ i, ∑ j, M i j

structure ThetaSDPFeasible {V : Type*} [Fintype V] (G : SimpleGraph V) where
  M : Matrix V V ℝ
  symm : M.IsSymm
  psd : M.PosSemidef
  trace_one : Matrix.trace M = 1
  edge_zero : ∀ {v w}, G.Adj v w → M v w = 0

noncomputable def thetaSDP {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup {t : ℝ | ∃ rep : ThetaSDPFeasible G, t = thetaSDPMatrixSum rep.M}

end Universality
