/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Kronecker product of `ThetaOrthonormalRep`s

Builds the tensor (Kronecker) product of two orthonormal reps, producing a rep
of `(G ⊠ H)ᶜ` from reps of `Gᶜ` and `Hᶜ`. The key step toward
`θ(G ⊠ H) ≤ θ(G) · θ(H)` (the easy direction of multiplicativity), without
needing the full SDP-strong-duality stack (only required for the reverse
direction, which we do not use here).

## Main results

* `kronecker` : `EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (n*m))`.
* `kronecker_apply_equiv` : `kronecker a b (finProdFinEquiv (i, j)) = a i * b j`.
* `kronecker_inner` : `⟨a ⊗ b, c ⊗ d⟩ = ⟨a, c⟩ · ⟨b, d⟩`.
* `kronecker_norm_sq`, `kronecker_norm` : norm² and norm factor.
* `thetaRep_tensor` : tensor product of reps, lands in `((G ⊠ H)ᶜ).ThetaOrthonormalRep (n*m)`.
-/

import AsymptoticSpectrumDistance.Prerequisites.LovaszTheta.Defs
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.StrongProduct

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Universality

open scoped BigOperators
open SimpleGraph ShannonCapacity

/-! ## Kronecker product of Euclidean vectors -/

/-- Kronecker (tensor) product of two Euclidean vectors, indexed via
    `finProdFinEquiv : Fin n × Fin m ≃ Fin (n*m)`. -/
noncomputable def kronecker {n m : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin (n * m)) :=
  WithLp.toLp 2 (fun k : Fin (n * m) =>
    let ij := finProdFinEquiv.symm k; a ij.1 * b ij.2)

private lemma fin_div_mod {n m : ℕ} (i : Fin n) (j : Fin m) :
    finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
  finProdFinEquiv.symm_apply_apply _

theorem kronecker_apply_equiv {n m : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin m)) (i : Fin n) (j : Fin m) :
    (kronecker a b).ofLp (finProdFinEquiv (i, j)) = a.ofLp i * b.ofLp j := by
  unfold kronecker
  simp only [fin_div_mod]

private lemma h_inner_real {p : ℕ} (x y : EuclideanSpace ℝ (Fin p)) :
    @inner ℝ _ _ x y = ∑ i, x.ofLp i * y.ofLp i := by
  rw [PiLp.inner_apply]; simp [inner, mul_comm]

/-- Inner product of Kronecker products factors over the components. -/
theorem kronecker_inner {n m : ℕ}
    (a c : EuclideanSpace ℝ (Fin n)) (b d : EuclideanSpace ℝ (Fin m)) :
    @inner ℝ _ _ (kronecker a b) (kronecker c d) =
      (@inner ℝ _ _ a c) * (@inner ℝ _ _ b d) := by
  rw [h_inner_real, h_inner_real, h_inner_real]
  rw [← Fintype.sum_equiv finProdFinEquiv
        (fun ij : Fin n × Fin m => (a.ofLp ij.1 * c.ofLp ij.1) * (b.ofLp ij.2 * d.ofLp ij.2))
        (fun k => (kronecker a b).ofLp k * (kronecker c d).ofLp k) ?_]
  · rw [show (∑ ij : Fin n × Fin m,
              (a.ofLp ij.1 * c.ofLp ij.1) * (b.ofLp ij.2 * d.ofLp ij.2)) =
            ∑ i : Fin n, ∑ j : Fin m,
              (a.ofLp i * c.ofLp i) * (b.ofLp j * d.ofLp j) from
      Fintype.sum_prod_type _]
    rw [← Finset.sum_mul_sum]
  · rintro ⟨i, j⟩
    change (a.ofLp i * c.ofLp i) * (b.ofLp j * d.ofLp j) =
      (kronecker a b).ofLp (finProdFinEquiv (i, j)) *
      (kronecker c d).ofLp (finProdFinEquiv (i, j))
    rw [kronecker_apply_equiv, kronecker_apply_equiv]; ring

/-- Norm-squared of Kronecker product factors. -/
theorem kronecker_norm_sq {n m : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖kronecker a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  rw [@EuclideanSpace.norm_sq_eq, @EuclideanSpace.norm_sq_eq, @EuclideanSpace.norm_sq_eq]
  rw [← Fintype.sum_equiv finProdFinEquiv
        (fun ij : Fin n × Fin m => ‖a.ofLp ij.1‖ ^ 2 * ‖b.ofLp ij.2‖ ^ 2)
        (fun k => ‖(kronecker a b).ofLp k‖ ^ 2) ?_]
  · rw [show (∑ ij : Fin n × Fin m, ‖a.ofLp ij.1‖ ^ 2 * ‖b.ofLp ij.2‖ ^ 2) =
            ∑ i : Fin n, ∑ j : Fin m, ‖a.ofLp i‖ ^ 2 * ‖b.ofLp j‖ ^ 2 from
      Fintype.sum_prod_type _]
    rw [← Finset.sum_mul_sum]
  · rintro ⟨i, j⟩
    change ‖a.ofLp i‖ ^ 2 * ‖b.ofLp j‖ ^ 2 =
      ‖(kronecker a b).ofLp (finProdFinEquiv (i, j))‖ ^ 2
    rw [kronecker_apply_equiv, norm_mul]; ring

/-- Norm of Kronecker product factors. -/
theorem kronecker_norm {n m : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖kronecker a b‖ = ‖a‖ * ‖b‖ := by
  have h_sq := kronecker_norm_sq a b
  have h_nonneg : (0 : ℝ) ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (kronecker a b), sq_nonneg (‖kronecker a b‖ - ‖a‖ * ‖b‖)]

/-! ## Tensor product of orthonormal representations -/

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Tensor product of orthonormal reps of `Gᶜ` and `Hᶜ` is a rep of `(G ⊠ H)ᶜ`,
    with vectors `(v, w) ↦ kronecker (f.vec v) (g.vec w)`. -/
noncomputable def thetaRep_tensor {n m : ℕ}
    (f : ThetaOrthonormalRep (Gᶜ) n) (g : ThetaOrthonormalRep (Hᶜ) m) :
    ThetaOrthonormalRep ((strongProduct G H)ᶜ) (n * m) where
  vec := fun vw => kronecker (f.vec vw.1) (g.vec vw.2)
  handle := kronecker f.handle g.handle
  vec_norm := fun vw => by rw [kronecker_norm, f.vec_norm, g.vec_norm]; ring
  handle_norm := by rw [kronecker_norm, f.handle_norm, g.handle_norm]; ring
  inner_ne_zero := fun vw => by
    rw [kronecker_inner]
    exact mul_ne_zero (f.inner_ne_zero vw.1) (g.inner_ne_zero vw.2)
  orthogonal := fun {vw vw'} hAdj => by
    rw [kronecker_inner]
    -- (G ⊠ H)ᶜ.Adj vw vw' implies Gᶜ.Adj vw.1 vw'.1 ∨ Hᶜ.Adj vw.2 vw'.2.
    have key : (Gᶜ).Adj vw.1 vw'.1 ∨ (Hᶜ).Adj vw.2 vw'.2 := by
      rw [SimpleGraph.compl_adj] at hAdj
      obtain ⟨hne, hnAdj⟩ := hAdj
      by_contra hcontra
      push_neg at hcontra
      obtain ⟨hnG, hnH⟩ := hcontra
      rw [SimpleGraph.compl_adj] at hnG hnH
      push_neg at hnG hnH
      apply hnAdj
      refine ⟨hne, ?_, ?_⟩
      · by_cases h : vw.1 = vw'.1
        · exact Or.inl h
        · exact Or.inr (hnG h)
      · by_cases h : vw.2 = vw'.2
        · exact Or.inl h
        · exact Or.inr (hnH h)
    rcases key with hG | hH
    · rw [f.orthogonal hG]; ring
    · rw [g.orthogonal hH]; ring

end Universality
