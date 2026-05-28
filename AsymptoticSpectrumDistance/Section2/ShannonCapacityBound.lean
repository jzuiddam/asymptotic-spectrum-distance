/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems
import AsymptoticSpectrumDistance.Section2.Basic

/-!
# Shannon Capacity Bounds via Asymptotic Spectrum Distance

This file proves that Shannon capacity difference is bounded by asymptotic spectrum distance,
using the spectral characterization of Shannon capacity from AsymptoticSpectrumGraphs.

## Main Results

* `shannonCapacity_dist_le` - |Θ(G) - Θ(H)| ≤ d(G, H)

## References

* [de Boer, Buys, Zuiddam] The asymptotic spectrum distance, graph limits, and Shannon capacity
-/

set_option linter.style.longLine false

namespace AsymptoticSpectrumDistance

open AsymptoticSpectrumGraphs

/-- Shannon capacity difference is bounded by asymptotic spectrum distance.

    This follows from:
    - Θ(G) = min_{φ ∈ X} φ(G) (Shannon capacity is minimum of spectral values)
    - |Θ(G) - Θ(H)| ≤ sup_{φ ∈ X} |φ(G) - φ(H)| = d(G, H) -/
theorem shannonCapacity_dist_le (G H : Graph) :
    |shannonCapacity G - shannonCapacity H| ≤ asympSpecDistance G H := by
  -- Get spectral points achieving the minima
  obtain ⟨φG, hφG⟩ := shannonCapacity_eq_min_spectrum G
  obtain ⟨φH, hφH⟩ := shannonCapacity_eq_min_spectrum H
  -- Convert abstract spectral points to graph spectral points
  -- AsymptoticSpectrum graphStrassenPreorder = SpectralPoint graphStrassenPreorder
  let φG' : SpectralPoint := abstractToGraphSpectralPoint φG
  let φH' : SpectralPoint := abstractToGraphSpectralPoint φH
  -- Key: the evaluations match
  have hevalG_G : φG'.eval G = AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder (GraphClass.mk G) φG := rfl
  have hevalG_H : φG'.eval H = AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder (GraphClass.mk H) φG := rfl
  have hevalH_G : φH'.eval G = AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder (GraphClass.mk G) φH := rfl
  have hevalH_H : φH'.eval H = AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder (GraphClass.mk H) φH := rfl
  -- Shannon capacity = min over spectral points
  -- We have: Θ(G) = φG(G), Θ(H) = φH(H)
  rw [hφG, hφH]
  -- Rewrite using graph spectral points
  rw [← hevalG_G, ← hevalH_H]
  -- Key inequalities from minimality:
  -- φG achieves min at G, so φG(G) ≤ φH(G)
  have hφG_min : φG'.eval G ≤ φH'.eval G := by
    rw [hevalG_G, hevalH_G, ← hφG, shannonCapacity_eq_iInf_spectrum]
    exact ciInf_le ⟨0, fun x ⟨ψ, hψ⟩ => hψ ▸ AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_nonneg _ ψ _⟩ φH
  -- φH achieves min at H, so φH(H) ≤ φG(H)
  have hφH_min : φH'.eval H ≤ φG'.eval H := by
    rw [hevalH_H, hevalG_H, ← hφH, shannonCapacity_eq_iInf_spectrum]
    exact ciInf_le ⟨0, fun x ⟨ψ, hψ⟩ => hψ ▸ AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_nonneg _ ψ _⟩ φG
  -- Case analysis: either φG'(G) ≥ φH'(H) or φG'(G) < φH'(H)
  by_cases h : φG'.eval G ≥ φH'.eval H
  · -- Case: φG(G) ≥ φH(H)
    -- Use: φG(G) - φH(H) = (φG(G) - φH(G)) + (φH(G) - φH(H)) ≤ 0 + |φH(G) - φH(H)|
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have key : φG'.eval G - φH'.eval H ≤ φH'.eval G - φH'.eval H := by linarith
    calc φG'.eval G - φH'.eval H
        ≤ φH'.eval G - φH'.eval H := key
      _ ≤ |φH'.eval G - φH'.eval H| := le_abs_self _
      _ ≤ asympSpecDistance G H := spectralPoint_dist_le G H φH'
  · -- Case: φG(G) < φH(H)
    push_neg at h
    -- Use: φH(H) - φG(G) = (φH(H) - φG(H)) + (φG(H) - φG(G)) ≤ 0 + |φG(G) - φG(H)|
    rw [abs_of_neg (sub_neg.mpr h)]
    have key : φH'.eval H - φG'.eval G ≤ φG'.eval H - φG'.eval G := by linarith
    calc -(φG'.eval G - φH'.eval H)
        = φH'.eval H - φG'.eval G := by ring
      _ ≤ φG'.eval H - φG'.eval G := key
      _ ≤ |φG'.eval H - φG'.eval G| := le_abs_self _
      _ = |φG'.eval G - φG'.eval H| := abs_sub_comm _ _
      _ ≤ asympSpecDistance G H := spectralPoint_dist_le G H φG'

end AsymptoticSpectrumDistance
