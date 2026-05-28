/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.AsymptoticSpectrum
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.FractionalCliqueCover
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems
import AsymptoticSpectrumDistance.Prerequisites.FractionGraph
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.UniformSpace.Dini

/-!
# Asymptotic Spectrum Distance

This file defines the asymptotic spectrum distance on graphs and proves its basic properties.

## Main definitions

* `asympSpecDistance G H` : The asymptotic spectrum distance d(G,H) = sup_{F ∈ X} |F(G) - F(H)|
* `evalGraph G` : The evaluation function Ĝ : X → ℝ given by Ĝ(F) = F(G)

## Main results

* `asympSpecDistance_self` : d(G, G) = 0
* `asympSpecDistance_symm` : d(G, H) = d(H, G)
* `asympSpecDistance_triangle` : d(G, K) ≤ d(G, H) + d(H, K)
* `asympSpecDistance_alt_char` : d(G, H) ≤ a/b ↔ asymptotic bounds hold

## References

* [de Boer, Buys, Zuiddam] The asymptotic spectrum distance, graph limits, and Shannon capacity
* [Strassen 1988] Asymptotic deformation of tensor structures
-/

namespace AsymptoticSpectrumDistance

open AsymptoticSpectrumGraphs SimpleGraph

abbrev SpectralPoint := AsymptoticSpectrumGraphs.SpectralPoint

/-- The asymptotic spectrum is nonempty.
    This follows from the existence of the fractional clique covering number χ̄_f. -/
theorem spectralPoint_nonempty : Nonempty SpectralPoint :=
  ⟨AsymptoticSpectrumGraphs.chibar_spectralPoint⟩

/-! ### Asymptotic Spectrum Distance -/

/-- The set of spectral distances between G and H. -/
def spectralDistanceSet (G H : Graph) : Set ℝ :=
  {x | ∃ φ : SpectralPoint, x = |φ.eval G - φ.eval H|}

/-- The asymptotic spectrum distance between two graphs.
    Definition 2.4: d(G, H) = sup_{F ∈ X} |F(G) - F(H)| -/
noncomputable def asympSpecDistance (G H : Graph) : ℝ :=
  sSup (spectralDistanceSet G H)

/-! ### Basic Properties of the Distance -/

/-- The distance from a graph to itself is zero. -/
theorem asympSpecDistance_self (G : Graph) : asympSpecDistance G G = 0 := by
  simp only [asympSpecDistance, spectralDistanceSet]
  have h : {x | ∃ φ : SpectralPoint, x = |φ.eval G - φ.eval G|} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, sub_self, abs_zero, Set.mem_singleton_iff]
    constructor
    · intro ⟨_, hx⟩; exact hx
    · intro hx; exact ⟨spectralPoint_nonempty.some, hx⟩
  simp only [h]
  exact csSup_singleton 0

/-- The distance is symmetric. -/
theorem asympSpecDistance_symm (G H : Graph) : asympSpecDistance G H = asympSpecDistance H G := by
  simp only [asympSpecDistance, spectralDistanceSet]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨φ, hφ⟩; exact ⟨φ, by rw [abs_sub_comm]; exact hφ⟩
  · intro ⟨φ, hφ⟩; exact ⟨φ, by rw [abs_sub_comm]; exact hφ⟩

/-- The distance is non-negative. -/
theorem asympSpecDistance_nonneg (G H : Graph) : 0 ≤ asympSpecDistance G H := by
  simp only [asympSpecDistance, spectralDistanceSet]
  apply Real.sSup_nonneg
  intro x ⟨φ, hφ⟩
  rw [hφ]
  exact abs_nonneg _

/-- The set of spectral values is bounded above by the number of vertices.
    For any graph G, {F(G) : F ∈ X} ⊆ [α(G), χ̄(G)] ⊆ [1, n]. -/
theorem spectralPoint_bdd_above (G : Graph) :
    BddAbove {x | ∃ φ : SpectralPoint, x = φ.eval G} := by
  -- Every spectral point is bounded by the number of vertices
  use Fintype.card G.V
  intro x ⟨φ, hφ⟩
  rw [hφ]
  -- φ(G) ≤ φ(E_n) = n since G ≤_G E_n
  have hcohom := cohom_to_edgeless G
  have hmono := φ.mono_cohom G (EdgelessGraph (Fintype.card G.V)) hcohom
  calc φ.eval G ≤ φ.eval (EdgelessGraph (Fintype.card G.V)) := hmono
    _ = Fintype.card G.V := φ.normalized (Fintype.card G.V)

/-- The distance set is bounded above. -/
theorem asympSpecDistance_bdd_above (G H : Graph) :
    BddAbove (spectralDistanceSet G H) := by
  -- Use boundedness of spectral values
  obtain ⟨MG, hMG⟩ := spectralPoint_bdd_above G
  obtain ⟨MH, hMH⟩ := spectralPoint_bdd_above H
  use MG + MH
  intro x ⟨φ, hφ⟩
  rw [hφ]
  calc |φ.eval G - φ.eval H|
      ≤ |φ.eval G| + |φ.eval H| := abs_sub _ _
    _ = φ.eval G + φ.eval H := by
        rw [abs_of_nonneg (φ.nonneg G), abs_of_nonneg (φ.nonneg H)]
    _ ≤ MG + MH := by
        apply add_le_add
        · exact hMG ⟨φ, rfl⟩
        · exact hMH ⟨φ, rfl⟩

/-- Triangle inequality for the asymptotic spectrum distance. -/
theorem asympSpecDistance_triangle (G H K : Graph) :
    asympSpecDistance G K ≤ asympSpecDistance G H + asympSpecDistance H K := by
  simp only [asympSpecDistance, spectralDistanceSet]
  apply csSup_le
  · -- Nonemptiness
    obtain ⟨φ₀⟩ := spectralPoint_nonempty
    exact ⟨|φ₀.eval G - φ₀.eval K|, φ₀, rfl⟩
  · -- Upper bound
    intro x ⟨φ, hφ⟩
    rw [hφ]
    calc |φ.eval G - φ.eval K|
        = |(φ.eval G - φ.eval H) + (φ.eval H - φ.eval K)| := by ring_nf
      _ ≤ |φ.eval G - φ.eval H| + |φ.eval H - φ.eval K| :=
          abs_add_le (φ.eval G - φ.eval H) (φ.eval H - φ.eval K)
      _ ≤ sSup {x | ∃ ψ : SpectralPoint, x = |ψ.eval G - ψ.eval H|} +
          sSup {x | ∃ ψ : SpectralPoint, x = |ψ.eval H - ψ.eval K|} := by
          apply add_le_add
          · apply le_csSup (asympSpecDistance_bdd_above G H)
            exact ⟨φ, rfl⟩
          · apply le_csSup (asympSpecDistance_bdd_above H K)
            exact ⟨φ, rfl⟩

/-! ### The Evaluation Map -/

/-- The evaluation function Ĝ : SpectralPoint → ℝ given by Ĝ(F) = F(G).
    This identifies graphs with continuous functions on the asymptotic spectrum. -/
def evalGraph (G : Graph) : SpectralPoint → ℝ := fun φ => φ.eval G

notation:max "Ĝ[" G "]" => evalGraph G

/-- The evaluation map is multiplicative under strong product. -/
theorem evalGraph_strongProduct (G H : Graph) :
    Ĝ[G ⊠ H] = Ĝ[G] * Ĝ[H] := by
  ext φ
  simp only [evalGraph, Pi.mul_apply]
  exact φ.mul_strongProduct G H

/-- The evaluation map is additive under disjoint union. -/
theorem evalGraph_disjointUnion (G H : Graph) :
    Ĝ[G ⊔ᴳ H] = Ĝ[G] + Ĝ[H] := by
  ext φ
  simp only [evalGraph, Pi.add_apply]
  exact φ.add_disjointUnion G H

/-- Monotonicity of evaluation under cohomomorphism. -/
theorem evalGraph_mono_cohom {G H : Graph} (hGH : G.graph ≤_G H.graph) :
    ∀ φ : SpectralPoint, Ĝ[G] φ ≤ Ĝ[H] φ := by
  intro φ
  simp only [evalGraph]
  exact φ.mono_cohom G H hGH

/-! ### Convergence and Shannon Capacity -/

/-- A sequence of graphs converges to H if their distance to H goes to 0. -/
def ConvergesTo (Gs : ℕ → Graph) (H : Graph) : Prop :=
  Filter.Tendsto (fun n => asympSpecDistance (Gs n) H) Filter.atTop (nhds 0)

/-- Any spectral value difference is bounded by the asymptotic spectrum distance. -/
theorem spectralPoint_dist_le (G H : Graph) (φ : SpectralPoint) :
    |φ.eval G - φ.eval H| ≤ asympSpecDistance G H := by
  apply le_csSup (asympSpecDistance_bdd_above G H)
  exact ⟨φ, rfl⟩

/-! ### Alternative Characterization of Distance -/

/-- Helper: spectral value of edgeless graph times any graph. -/
theorem spectralPoint_edgeless_strongProduct (φ : SpectralPoint) (n : ℕ) (G : Graph) :
    φ.eval (EdgelessGraph n ⊠ G) = n * φ.eval G := by
  rw [φ.mul_strongProduct, φ.normalized]

/-- Helper: spectral value of disjoint union with edgeless graph. -/
theorem spectralPoint_disjointUnion_edgeless (φ : SpectralPoint) (G : Graph) (n : ℕ) :
    φ.eval (G ⊔ᴳ EdgelessGraph n) = φ.eval G + n := by
  rw [φ.add_disjointUnion, φ.normalized]

/-- Lemma 2.8: Alternative characterization of asymptotic spectrum distance.
    d(G, H) ≤ a/b ↔ E_b ⊠ G ≲ (E_b ⊠ H) ⊔ E_a and E_b ⊠ H ≲ (E_b ⊠ G) ⊔ E_a -/
theorem asympSpecDistance_alt_char (G H : Graph) (a b : ℕ) (hb : 0 < b) :
    asympSpecDistance G H ≤ (a : ℝ) / b ↔
      (((EdgelessGraph b ⊠ G) ≲ ((EdgelessGraph b ⊠ H) ⊔ᴳ EdgelessGraph a)) ∧
       ((EdgelessGraph b ⊠ H) ≲ ((EdgelessGraph b ⊠ G) ⊔ᴳ EdgelessGraph a))) := by
  -- The proof uses spectral duality: H ≲ G ↔ ∀ φ, φ(H) ≤ φ(G)
  -- d(G,H) ≤ a/b means ∀ φ, |φ(G) - φ(H)| ≤ a/b
  -- Using φ(E_b ⊠ G) = b·φ(G) and φ(X ⊔ E_a) = φ(X) + a:
  -- E_b ⊠ G ≲ (E_b ⊠ H) ⊔ E_a ↔ ∀ φ, b·φ(G) ≤ b·φ(H) + a ↔ φ(G) - φ(H) ≤ a/b
  constructor
  · -- Forward direction: d(G,H) ≤ a/b → cohomomorphism conditions
    intro hdist
    constructor
    · -- E_b ⊠ G ≲ (E_b ⊠ H) ⊔ E_a
      rw [asympCohom_iff_forall_spectralPoint]
      intro φ
      -- φ(E_b ⊠ G) = b·φ(G) ≤ b·φ(H) + a = φ((E_b ⊠ H) ⊔ E_a)
      rw [spectralPoint_edgeless_strongProduct, spectralPoint_disjointUnion_edgeless,
          spectralPoint_edgeless_strongProduct]
      have hφ : φ.eval G - φ.eval H ≤ (a : ℝ) / b := by
        have hbound := spectralPoint_dist_le G H φ
        have hab : |φ.eval G - φ.eval H| ≤ (a : ℝ) / b := le_trans hbound hdist
        exact (abs_le.mp hab).2
      have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
      -- Need: b * φ.eval G ≤ b * φ.eval H + a
      -- From hφ: φ.eval G - φ.eval H ≤ a/b
      -- Multiply by b: b * (φ.eval G - φ.eval H) ≤ a
      have hmul : b * (φ.eval G - φ.eval H) ≤ a := by
        calc (b : ℝ) * (φ.eval G - φ.eval H)
            ≤ b * (a / b) := by apply mul_le_mul_of_nonneg_left hφ (le_of_lt hb_pos)
          _ = a := by field_simp
      linarith
    · -- E_b ⊠ H ≲ (E_b ⊠ G) ⊔ E_a
      rw [asympCohom_iff_forall_spectralPoint]
      intro φ
      rw [spectralPoint_edgeless_strongProduct, spectralPoint_disjointUnion_edgeless,
          spectralPoint_edgeless_strongProduct]
      have hφ : φ.eval H - φ.eval G ≤ (a : ℝ) / b := by
        have hbound := spectralPoint_dist_le G H φ
        have hab : |φ.eval G - φ.eval H| ≤ (a : ℝ) / b := le_trans hbound hdist
        have hab' := (abs_le.mp hab).1
        linarith
      have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
      -- Need: b * φ.eval H ≤ b * φ.eval G + a
      -- From hφ: φ.eval H - φ.eval G ≤ a/b
      -- Multiply by b: b * (φ.eval H - φ.eval G) ≤ a
      have hmul : b * (φ.eval H - φ.eval G) ≤ a := by
        calc (b : ℝ) * (φ.eval H - φ.eval G)
            ≤ b * (a / b) := by apply mul_le_mul_of_nonneg_left hφ (le_of_lt hb_pos)
          _ = a := by field_simp
      linarith
  · -- Reverse direction: cohomomorphism conditions → d(G,H) ≤ a/b
    intro ⟨h1, h2⟩
    -- For all φ, we have both φ(G) - φ(H) ≤ a/b and φ(H) - φ(G) ≤ a/b
    -- This means |φ(G) - φ(H)| ≤ a/b for all φ
    -- Hence d(G,H) = sup_φ |φ(G) - φ(H)| ≤ a/b
    apply csSup_le
    · -- Nonemptiness
      obtain ⟨φ₀⟩ := spectralPoint_nonempty
      exact ⟨|φ₀.eval G - φ₀.eval H|, φ₀, rfl⟩
    · intro x ⟨φ, hφ⟩
      rw [hφ]
      rw [asympCohom_iff_forall_spectralPoint] at h1 h2
      have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
      have h1' := h1 φ
      have h2' := h2 φ
      rw [spectralPoint_edgeless_strongProduct, spectralPoint_disjointUnion_edgeless,
          spectralPoint_edgeless_strongProduct] at h1' h2'
      -- From h1': b * φ(G) ≤ b * φ(H) + a, so φ(G) - φ(H) ≤ a/b
      -- From h2': b * φ(H) ≤ b * φ(G) + a, so φ(H) - φ(G) ≤ a/b
      have hGH : φ.eval G - φ.eval H ≤ (a : ℝ) / b := by
        -- From h1': b * φ(G) ≤ b * φ(H) + a
        -- So b * (φ(G) - φ(H)) ≤ a
        -- So φ(G) - φ(H) ≤ a/b
        have hmul : (b : ℝ) * (φ.eval G - φ.eval H) ≤ a := by linarith
        rw [le_div_iff₀ hb_pos]
        linarith
      have hHG : φ.eval H - φ.eval G ≤ (a : ℝ) / b := by
        -- From h2': b * φ(H) ≤ b * φ(G) + a
        -- So b * (φ(H) - φ(G)) ≤ a
        -- So φ(H) - φ(G) ≤ a/b
        have hmul : (b : ℝ) * (φ.eval H - φ.eval G) ≤ a := by linarith
        rw [le_div_iff₀ hb_pos]
        linarith
      rw [abs_le]
      constructor <;> linarith

/-! ### Dini's Theorem Application -/

/-- Lemma 2.13 (Dini): If F(G_n) is uniformly monotone (or uniformly antitone) for
    all spectral points F ∈ X and converges pointwise to F(H), then G_n converges uniformly to H.

    This is Dini's theorem applied to the spectral functions on the asymptotic
    spectrum X. The key insight is that X is compact and the spectral functions
    are continuous, so monotone pointwise convergence implies uniform convergence.

    The hypothesis requires uniform behavior: either ALL spectral points have monotone
    sequences F(G_n), or ALL have antitone sequences.

    Proof outline:
    1. The abstract spectrum X is compact (AsymptoticSpectrum.isCompact)
    2. Evaluation maps are continuous (AsymptoticSpectrum.continuous_eval)
    3. Apply Dini's theorem to get uniform convergence
    4. Uniform convergence on compact set gives asympSpecDistance → 0 -/
theorem dini_convergence (Gs : ℕ → Graph) (H : Graph)
    (hmono : (∀ F : SpectralPoint, Monotone (fun n => F.eval (Gs n))) ∨
             (∀ F : SpectralPoint, Antitone (fun n => F.eval (Gs n))))
    (hptwise : ∀ F : SpectralPoint,
      Filter.Tendsto (fun n => F.eval (Gs n)) Filter.atTop (nhds (F.eval H))) :
    ConvergesTo Gs H := by
  -- Work with the abstract spectrum
  let p := AsymptoticSpectrumGraphs.graphStrassenPreorder
  let X := AsymptoticSpectrumDuality.AsymptoticSpectrum p
  -- Define the evaluation functions on the abstract spectrum
  let F : ℕ → X → ℝ := fun n ψ => ψ.toFun (AsymptoticSpectrumGraphs.GraphClass.mk (Gs n))
  let f : X → ℝ := fun ψ => ψ.toFun (AsymptoticSpectrumGraphs.GraphClass.mk H)
  -- The abstract spectrum is compact
  have hcompact : IsCompact (Set.univ : Set X) :=
    AsymptoticSpectrumDuality.AsymptoticSpectrum.isCompact p
  -- Evaluation is continuous
  have hF_cont : ∀ n, Continuous (F n) := fun n =>
    AsymptoticSpectrumDuality.AsymptoticSpectrum.continuous_eval p _
  have hf_cont : Continuous f := AsymptoticSpectrumDuality.AsymptoticSpectrum.continuous_eval p _
  -- Convert monotonicity hypothesis: graph SpectralPoints ↔ abstract SpectralPoints
  have hmono_abstract :
      (∀ ψ : X, Monotone (fun n => F n ψ)) ∨ (∀ ψ : X, Antitone (fun n => F n ψ)) := by
    rcases hmono with hmono_inc | hmono_dec
    · left
      intro ψ
      -- Convert ψ to graph SpectralPoint via abstractToGraphSpectralPoint
      let φ := AsymptoticSpectrumGraphs.abstractToGraphSpectralPoint ψ
      have heq : ∀ n, F n ψ = φ.eval (Gs n) := fun n => rfl
      have hφ := hmono_inc φ
      intro m n hmn
      simp only [heq]
      exact hφ hmn
    · right
      intro ψ
      let φ := AsymptoticSpectrumGraphs.abstractToGraphSpectralPoint ψ
      have heq : ∀ n, F n ψ = φ.eval (Gs n) := fun n => rfl
      have hφ := hmono_dec φ
      intro m n hmn
      simp only [heq]
      exact hφ hmn
  -- Convert pointwise convergence hypothesis
  have hptwise_abstract : ∀ ψ : X, Filter.Tendsto (fun n => F n ψ) Filter.atTop (nhds (f ψ)) := by
    intro ψ
    let φ := AsymptoticSpectrumGraphs.abstractToGraphSpectralPoint ψ
    have heq : ∀ n, F n ψ = φ.eval (Gs n) := fun n => rfl
    have hlim : f ψ = φ.eval H := rfl
    simp only [heq, hlim]
    exact hptwise φ
  -- Apply Dini's theorem
  have hunif : TendstoUniformlyOn F f Filter.atTop Set.univ := by
    rcases hmono_abstract with hmono_abs | hanti_abs
    · -- Monotone case
      exact Monotone.tendstoUniformlyOn_of_forall_tendsto hcompact
        (fun n => (hF_cont n).continuousOn) (fun x _ => hmono_abs x)
        hf_cont.continuousOn (fun x _ => hptwise_abstract x)
    · -- Antitone case
      exact Antitone.tendstoUniformlyOn_of_forall_tendsto hcompact
        (fun n => (hF_cont n).continuousOn) (fun x _ => hanti_abs x)
        hf_cont.continuousOn (fun x _ => hptwise_abstract x)
  -- Convert uniform convergence to ConvergesTo (asympSpecDistance → 0)
  -- TendstoUniformlyOn F f atTop univ means:
  --   ∀ ε > 0, ∀ᶠ n, ∀ ψ ∈ univ, |F n ψ - f ψ| < ε
  -- We need: ∀ ε > 0, ∃ N, ∀ n ≥ N, asympSpecDistance (Gs n) H < ε
  unfold ConvergesTo
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get N from uniform convergence with ε/2 (to convert ≤ to <)
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  have hε2 : ε / 2 > 0 := half_pos hε
  have hunif_ε := hunif (ε / 2) hε2
  -- Convert "∀ᶠ n in atTop" to "∃ N, ∀ n ≥ N"
  obtain ⟨N, hN⟩ := hunif_ε.exists_forall_of_atTop
  use N
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (asympSpecDistance_nonneg _ _)]
  -- Show asympSpecDistance (Gs n) H < ε
  -- asympSpecDistance (Gs n) H = sSup {|φ.eval (Gs n) - φ.eval H| : φ : SpectralPoint}
  -- Each |φ.eval (Gs n) - φ.eval H| < ε/2 by the uniform bound, so sSup ≤ ε/2 < ε
  have hN' := hN n hn
  have hbdd := asympSpecDistance_bdd_above (Gs n) H
  calc asympSpecDistance (Gs n) H
      = sSup (spectralDistanceSet (Gs n) H) := rfl
    _ ≤ ε / 2 := by
        apply csSup_le
        · -- Nonempty
          obtain ⟨φ₀⟩ := spectralPoint_nonempty
          exact ⟨|φ₀.eval (Gs n) - φ₀.eval H|, φ₀, rfl⟩
        · -- Upper bound: each element ≤ ε/2
          intro x ⟨φ, hφ⟩
          rw [hφ]
          -- Convert φ to abstract SpectralPoint
          let ψ := AsymptoticSpectrumGraphs.graphSpectralPointToAbstract φ
          -- φ.eval G = ψ.toFun (GraphClass.mk G) by definition of graphSpectralPointToAbstract
          have heval_n : φ.eval (Gs n) = F n ψ := rfl
          have heval_H : φ.eval H = f ψ := rfl
          rw [heval_n, heval_H]
          -- Use the uniform bound (strict < ε/2, hence ≤ ε/2)
          have hspec := hN' ψ (Set.mem_univ _)
          rw [Real.dist_eq, abs_sub_comm] at hspec
          exact le_of_lt hspec
    _ < ε := half_lt_self hε

end AsymptoticSpectrumDistance
