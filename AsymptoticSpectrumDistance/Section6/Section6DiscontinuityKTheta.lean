/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Bridge `lovaszTheta_strongProduct_le` to `α₃` / `alphaK`

Connects the Lovász theta multiplicativity bound (`Multiplicativity.lean`) to
the disc-check problem on `FracTriple`/`FracTuple 3`. Provides:

* `alpha3_le_lovaszTheta_prod` : `α₃(v) ≤ θ(E_{p₀/q₀}) · θ(E_{p₁/q₁}) · θ(E_{p₂/q₂})`.
* `alphaK_three_le_lovaszTheta_prod` : same on `FracTuple 3`.

These are the entry points for the per-pair `θ`-bound machinery used by the
per-disc α₃ proofs.

## Usage

For each non-integer disc point `v`, given a candidate `u <ₚ v` in
`discCandidates`, if there exist concrete `θ`-bounds `θ(E_{(u i).1/(u i).2}) ≤ ti`
with `t₀ · t₁ · t₂ < α₃(v)`, then `α₃(u) ≤ ⌊t₀ · t₁ · t₂⌋ < α₃(v)`, ruling out
`u` as a counterexample.

In the final converse-direction proof of Theorem 6.9 the θ-product bound
turned out to be dominated by the nested-floor + Baumert combination,
so the disc-by-disc Lovász θ machinery here is not used; it is retained
as standalone infrastructure since it is correct and may be useful for
future extensions.
-/

import AsymptoticSpectrumDistance.Prerequisites.LovaszTheta.Multiplicativity
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKBridge

open Universality

namespace Section6

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- `α₃` upper-bounded by the product of three `lovaszTheta` values. -/
theorem alpha3_le_lovaszTheta_prod (v : FracTriple) :
    (alpha3 v : ℝ) ≤
      lovaszTheta (ShannonCapacity.fractionGraph (v 0).1 (v 0).2) *
      lovaszTheta (ShannonCapacity.fractionGraph (v 1).1 (v 1).2) *
      lovaszTheta (ShannonCapacity.fractionGraph (v 2).1 (v 2).2) := by
  unfold alpha3
  rw [ShannonCapacity.indepNum_strongProduct_assoc]
  calc ((ShannonCapacity.fractionGraph (v 0).1 (v 0).2 ⊠
          (ShannonCapacity.fractionGraph (v 1).1 (v 1).2 ⊠
          ShannonCapacity.fractionGraph (v 2).1 (v 2).2)).indepNum : ℝ)
      ≤ lovaszTheta (ShannonCapacity.fractionGraph (v 0).1 (v 0).2) *
        lovaszTheta (ShannonCapacity.fractionGraph (v 1).1 (v 1).2 ⊠
          ShannonCapacity.fractionGraph (v 2).1 (v 2).2) :=
          indepNum_strongProduct_le_lovaszTheta_mul _ _
    _ ≤ lovaszTheta (ShannonCapacity.fractionGraph (v 0).1 (v 0).2) *
        (lovaszTheta (ShannonCapacity.fractionGraph (v 1).1 (v 1).2) *
         lovaszTheta (ShannonCapacity.fractionGraph (v 2).1 (v 2).2)) := by
          apply mul_le_mul_of_nonneg_left
          · exact lovaszTheta_strongProduct_le _ _
          · exact lovaszTheta_nonneg _
    _ = lovaszTheta (ShannonCapacity.fractionGraph (v 0).1 (v 0).2) *
        lovaszTheta (ShannonCapacity.fractionGraph (v 1).1 (v 1).2) *
        lovaszTheta (ShannonCapacity.fractionGraph (v 2).1 (v 2).2) := by ring

/-- `alphaK` (k = 3) upper-bounded by the product of three `lovaszTheta` values. -/
theorem alphaK_three_le_lovaszTheta_prod (v : FracTuple 3) :
    (alphaK v : ℝ) ≤
      lovaszTheta (ShannonCapacity.fractionGraph (v 0).1 (v 0).2) *
      lovaszTheta (ShannonCapacity.fractionGraph (v 1).1 (v 1).2) *
      lovaszTheta (ShannonCapacity.fractionGraph (v 2).1 (v 2).2) := by
  rw [show (alphaK v : ℝ) = (alpha3 v : ℝ) by exact_mod_cast alphaK_three v]
  exact alpha3_le_lovaszTheta_prod v

/-! ## θ monotonicity for fraction graphs

If `p/q ≤ p'/q'` (both `Valid`, i.e., ≥ 2), then `θ(E_{p/q}) ≤ θ(E_{p'/q'})`.
This is the key bound that lets us replace per-pair `θ` certificates with a
single bound at the disc point's slot maxima. -/

/-- `θ(E_{p/q})` is monotone in `p/q`. -/
theorem lovaszTheta_fractionGraph_monotone (p₁ q₁ p₂ q₂ : ℕ) [NeZero p₁] [NeZero p₂]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁) (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂)
    (hle : (p₁ : ℚ) / q₁ ≤ (p₂ : ℚ) / q₂) :
    lovaszTheta (ShannonCapacity.fractionGraph p₁ q₁) ≤
      lovaszTheta (ShannonCapacity.fractionGraph p₂ q₂) := by
  -- E_{p₁/q₁} ≤_G E_{p₂/q₂} via cohom_fractionGraph_monotone, then θ-mono.
  have h_le_nat : p₁ * q₂ ≤ p₂ * q₁ := by
    have hq₁_q : (0 : ℚ) < (q₁ : ℚ) := by exact_mod_cast hq₁
    have hq₂_q : (0 : ℚ) < (q₂ : ℚ) := by exact_mod_cast hq₂
    rw [div_le_div_iff₀ hq₁_q hq₂_q] at hle
    exact_mod_cast hle
  have h_cohom : ShannonCapacity.fractionGraph p₁ q₁ ≤_G
      ShannonCapacity.fractionGraph p₂ q₂ :=
    cohom_fractionGraph_monotone p₁ q₁ p₂ q₂ hq₁ h2q₁ hq₂ h2q₂ h_le_nat
  exact lovaszTheta_mono_of_cohom h_cohom

/-! ## Main result: `α₃(u) ≤ θ(E_v0) · θ(E_v1) · θ(E_v2)` for `u ≤ₚ v`

Combines `alpha3_le_lovaszTheta_prod` with `θ` monotonicity to give a *single*
upper bound on `α₃` for all candidates `u ≤ₚ v`. Eliminates the need for
per-candidate `θ`-prod computation: the disc-point `v` itself supplies the
bound.

This is the missing piece the user pointed out: `θ(E_{p/q})` monotonicity
in `p/q` lets us replace the candidate-set-wide enumeration with a single
real-arithmetic check at the disc point. -/

/-- For `u ≤ₚ v` (both valid `FracTriple`s), `α₃(u)` is bounded by the
    `θ`-product at the **disc point** `v`. Chains `alphaK_le_of_lePermK`
    (monotonicity of α₃ under `lePerm`) with `alpha3_le_lovaszTheta_prod` at `v`. -/
theorem alpha3_le_lovaszTheta_prod_at_v {u v : FracTriple}
    (hu : Valid u) (hv : Valid v) (h_le : lePerm u v) :
    (alpha3 u : ℝ) ≤
      lovaszTheta (ShannonCapacity.fractionGraph (v 0).1 (v 0).2) *
      lovaszTheta (ShannonCapacity.fractionGraph (v 1).1 (v 1).2) *
      lovaszTheta (ShannonCapacity.fractionGraph (v 2).1 (v 2).2) := by
  -- α₃(u) ≤ α₃(v) via lePerm + αₖ monotonicity (through the bridges).
  have h_α_le : alpha3 u ≤ alpha3 v := by
    rw [show alpha3 u = alphaK u from (alphaK_three u).symm,
        show alpha3 v = alphaK v from (alphaK_three v).symm]
    -- ValidK = Valid (defeq for FracTriple/FracTuple 3).
    -- lePermK = lePerm (defeq).
    exact alphaK_le_of_lePermK hu hv h_le
  -- α₃(v) ≤ θ-prod(v) via the existing bound.
  have h_α_θ : (alpha3 v : ℝ) ≤
      lovaszTheta (ShannonCapacity.fractionGraph (v 0).1 (v 0).2) *
      lovaszTheta (ShannonCapacity.fractionGraph (v 1).1 (v 1).2) *
      lovaszTheta (ShannonCapacity.fractionGraph (v 2).1 (v 2).2) :=
    alpha3_le_lovaszTheta_prod v
  exact (Nat.cast_le.mpr h_α_le).trans h_α_θ

end Section6
