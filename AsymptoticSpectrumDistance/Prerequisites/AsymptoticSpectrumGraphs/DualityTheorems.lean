/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.Specialization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Graph Spectral Duality Theorems

This file connects the abstract spectral duality theorems to the graph setting.

## Main Results

* `graphAsympRel_iff_forall_abstractSpectrum` - Abstract spectral duality for graphs
* `spectral_implies_asymp` - If φ(H) ≤ φ(G) for all abstract φ, then AsympRel holds

## Discussion

The abstract theory provides:
  `AsympRel p a b ↔ ∀ φ : AsymptoticSpectrum p, φ(a) ≤ φ(b)`

For graphs, we have two asymptotic relations:
1. `AsympCohom H G` (graph-specific): ∃f little-o, ∀n, H^⊠n →_G G^⊠(n+f(n))
2. `AsympRel graphStrassenPreorder` (abstract): ∃x, ∀n, a^n ≤_P b^n * x(n)

These are related but not identical:
- In (1): G^(n+f(n)) = n+f(n) strong products of G
- In (2): G^n * x(n) = G^n ⊠ E_{x(n)} = n products of G plus x(n) isolated vertices

The graph-specific `spectral_duality` theorem (proved below) states:
  `AsympCohom H G ↔ ∀ φ : SpectralPoint, φ(H) ≤ φ(G)`

This is a theorem due to Strassen that requires additional work beyond what the
abstract Strassen preorder theory provides.

## References

* Strassen (1988), The asymptotic spectrum of tensors
* Vrana (2015), Probabilistic refinement of the asymptotic spectrum of graphs
-/

namespace AsymptoticSpectrumGraphs

open SimpleGraph
open AsymptoticSpectrumDuality

-- Abbreviation to avoid notation conflicts with Δ(G)
abbrev AbstractSpectrum := AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder

/-! ### Abstract Spectral Duality for Graphs -/

/-- The asymptotic relation on GraphClass using the abstract definition.
    This is AsympRel for graphStrassenPreorder. -/
def GraphAsympRel (a b : GraphClass) : Prop :=
  AsympRel graphStrassenPreorder a b

notation:50 a " ≲ᴬ " b => GraphAsympRel a b

/-- Abstract spectral duality for graphs:
    a ≲ᴬ b ↔ ∀ φ : AsymptoticSpectrum, φ(a) ≤ φ(b)

    This follows directly from the abstract asympRel_iff_forall_spectrum. -/
theorem graphAsympRel_iff_forall_abstractSpectrum (a b : GraphClass) :
    (a ≲ᴬ b) ↔ ∀ φ : AbstractSpectrum,
              AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder a φ ≤
              AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder b φ := by
  exact graphStrassenPreorder.asympRel_iff_forall_spectrum a b

/-- If the spectral condition holds for all abstract spectral points,
    then the abstract asymptotic relation holds. -/
theorem spectral_implies_graphAsympRel (a b : GraphClass)
    (h : ∀ φ : AbstractSpectrum,
         AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder a φ ≤
         AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder b φ) :
    a ≲ᴬ b :=
  (graphAsympRel_iff_forall_abstractSpectrum a b).mpr h

/-! ### Connection to Graph SpectralPoint -/

/-- If the abstract asymptotic relation holds, then any graph SpectralPoint
    respects it: φ(G) ≤ φ(H).

    Note: This requires showing that graphSpectralPointToAbstract lands in
    the AsymptoticSpectrum, which requires additional bounds on φ.

    The key issue: graph SpectralPoint has axioms:
    - φ(E_n) = n (normalized)
    - φ(G ⊠ H) = φ(G) * φ(H)
    - φ(G ⊔ H) = φ(G) + φ(H)
    - φ(G) ≤ φ(H) if G ≤_G H

    Abstract AsymptoticSpectrum requires:
    - 1 ≤ φ(a) ≤ rank(a) for all a (bounded)
    - Same algebraic properties

    The boundedness condition φ(a) ≤ rank(a) is the key gap. -/
theorem graphSpectralPoint_respects_asympRel (φ : SpectralPoint) (G H : Graph)
    (hasym : GraphClass.mk G ≲ᴬ GraphClass.mk H) :
    φ.eval G ≤ φ.eval H := by
  -- Convert graph SpectralPoint to abstract SpectralPoint
  -- Note: AsymptoticSpectrum p = SpectralPoint p in the abstract theory
  let ψ : AbstractSpectrum := graphSpectralPointToAbstract φ
  -- Use abstract duality: AsympRel implies all spectral points respect the order
  have hspec := (graphAsympRel_iff_forall_abstractSpectrum
                   (GraphClass.mk G) (GraphClass.mk H)).mp hasym ψ
  -- This gives us ψ(G) ≤ ψ(H), which equals φ.eval G ≤ φ.eval H
  simp only [AsymptoticSpectrumDuality.AsymptoticSpectrum.eval] at hspec
  exact hspec

/-! ### The Graph Spectral Duality Theorem

The spectral duality theorem characterizes the abstract asymptotic relation
`GraphAsympRel` (i.e., G^n ≤ E_2^{o(n)} · H^n) in terms of spectral points:

  `GraphAsympRel G H ↔ ∀ φ : SpectralPoint, φ(G) ≤ φ(H)`

This follows directly from the abstract `spectral_duality_abstract` theorem
via the equivalence between graph SpectralPoints and abstract SpectralPoints.

The connection between `AsympCohom` (G^n ≤ H^{n+o(n)}) and `GraphAsympRel`
(G^n ≤ E_2^{o(n)} · H^n) is a separate theorem that holds for all graphs.
-/

/-- Spectral duality theorem for graphs (abstract form):
    G^n ≤ E_2^{o(n)} · H^n iff for all spectral points φ, φ(G) ≤ φ(H).

    This is Strassen's duality theorem specialized to graphs. -/
theorem spectral_duality (G H : Graph) :
    (GraphClass.mk G ≲ᴬ GraphClass.mk H) ↔ ∀ φ : SpectralPoint, φ.eval G ≤ φ.eval H := by
  constructor
  · -- Forward: GraphAsympRel → spectral points agree
    intro hasym φ
    exact graphSpectralPoint_respects_asympRel φ G H hasym
  · -- Backward: spectral points agree → GraphAsympRel
    intro hspec
    apply spectral_implies_graphAsympRel
    intro ψ
    -- Convert abstract spectral point to graph spectral point
    let φ := abstractToGraphSpectralPoint ψ
    -- hspec gives φ.eval G ≤ φ.eval H
    have hφ := hspec φ
    -- Need to show ψ(G) ≤ ψ(H)
    -- By abstractSpectralPoint_roundtrip, ψ = graphSpectralPointToAbstract φ
    have hround := abstractSpectralPoint_roundtrip ψ
    simp only [AsymptoticSpectrumDuality.AsymptoticSpectrum.eval]
    -- φ.eval G = ψ.toFun (GraphClass.mk G) by definition of abstractToGraphSpectralPoint
    exact hφ

/-! ### Bridge Lemma: SimpleGraph.strongPower ↔ Semiring Power -/

-- Note: recStrongPowerGraph, recStrongPowerGraph_iso, strongPowerGraph,
-- cohom_to_edgeless, and cohomLE_to_cohom are now in Universality namespace

/-! ### Analysis lemma for little-o functions -/

/-- When f is little-o and V ≥ 1, the sInf of V^{f(n)/n} over n ≥ 1 equals 1.

    Since V is constant:
    - V = 1: all terms are 1, so sInf = 1
    - V ≥ 2: f(n)/n → 0 by little-o, so V^{f(n)/n} → 1, and all terms ≥ 1 -/
theorem littleO_implies_sInf_pow_eq_one (f : ℕ → ℕ) (hf : IsLittleO f) (V : ℕ) (hV : 1 ≤ V) :
    sInf ((fun n => (V ^ f n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) = 1 := by
  -- Case V = 1: all terms are 1^{f(n)/n} = 1
  by_cases hV1 : V = 1
  · simp only [hV1, Nat.cast_one, one_pow, Real.one_rpow]
    have himg : (fun _ : ℕ => (1 : ℝ)) '' {n : ℕ | 1 ≤ n} = {1} := by
      ext x; simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, _, rfl⟩; rfl
      · intro hx; exact ⟨1, le_refl 1, hx.symm⟩
    rw [himg, csInf_singleton]
  -- Case V ≥ 2: use that f(n)/n → 0
  have hV2 : 2 ≤ V := by omega
  have hV_ge1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
  let S := (fun n => ((V : ℝ) ^ f n) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}
  -- All terms ≥ 1
  have hge1 : ∀ x ∈ S, 1 ≤ x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := hx
    apply Real.one_le_rpow _ (by positivity : 0 ≤ 1 / (n : ℝ))
    calc (1 : ℝ) = V ^ (0 : ℕ) := by simp
         _ ≤ V ^ f n := by exact_mod_cast Nat.pow_le_pow_right hV (Nat.zero_le _)
  have hnonempty : S.Nonempty := ⟨_, ⟨1, le_refl 1, rfl⟩⟩
  have hbdd : BddBelow S := ⟨1, hge1⟩
  -- sInf ≥ 1 (all terms ≥ 1)
  have hsInf_ge1 : 1 ≤ sInf S := le_csInf hnonempty hge1
  -- sInf ≤ 1: by little-o, for ε = 1, ∃N, ∀n ≥ N, f(n) < n, so f(n)/n < 1
  -- Thus V^{f(n)/n} < V^1 = V. But we need V^{f(n)/n} → 1.
  -- Key: (V^{f(n)})^{1/n} = V^{f(n)/n}, and f(n)/n → 0, so this → V^0 = 1.
  have hsInf_le1 : sInf S ≤ 1 := by
    -- For any δ > 0, we find an element < 1 + δ, showing sInf ≤ 1
    by_contra h_neg
    push_neg at h_neg  -- h_neg : 1 < sInf S
    set δ := sInf S - 1 with hδ_def
    have hδ_pos : 0 < δ := by linarith
    -- Use little-o: for ε = log(1 + δ/2)/log(V), eventually f(n)/n < ε
    have hV_gt1 : (1 : ℝ) < V := by exact_mod_cast hV2
    have hlogV_pos : 0 < Real.log V := Real.log_pos hV_gt1
    have h1δ2_gt1 : 1 < 1 + δ/2 := by linarith
    have hlog1δ_pos : 0 < Real.log (1 + δ/2) := Real.log_pos h1δ2_gt1
    set ε := Real.log (1 + δ/2) / Real.log V with hε_def
    have hε_pos : 0 < ε := div_pos hlog1δ_pos hlogV_pos
    obtain ⟨N, hN⟩ := hf ε hε_pos
    -- For n = max(N, 1), we have f(n)/n < ε
    set n := max N 1 with hn_def
    have hn_ge1 : 1 ≤ n := le_max_right _ _
    have hn_geN : N ≤ n := le_max_left _ _
    have hfn_bound : (f n : ℝ) < ε * n := hN n hn_geN
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn_ge1)
    have hfn_div : (f n : ℝ) / n < ε := by
      have : (f n : ℝ) < n * ε := by linarith
      calc (f n : ℝ) / n < (n * ε) / n := by apply div_lt_div_of_pos_right this hn_pos
                       _ = ε := by field_simp
    -- V^{f(n)/n} < V^ε = 1 + δ/2 < sInf S
    have hV_pos : (0 : ℝ) < V := by positivity
    have hVε : (V : ℝ) ^ ε = 1 + δ/2 := by
      rw [hε_def]
      rw [Real.rpow_def_of_pos hV_pos, mul_div_assoc']
      rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hlogV_pos), mul_one]
      exact Real.exp_log (by linarith : 0 < 1 + δ/2)
    have hVfn : ((V : ℝ) ^ f n) ^ (1 / n : ℝ) < sInf S := by
      have heq : ((V : ℝ) ^ f n) ^ (1 / n : ℝ) = V ^ ((f n : ℝ) / n) := by
        rw [← Real.rpow_natCast V (f n)]
        rw [← Real.rpow_mul (le_of_lt hV_pos)]
        congr 1
        field_simp
      rw [heq]
      calc (V : ℝ) ^ ((f n : ℝ) / n)
          < V ^ ε := Real.rpow_lt_rpow_of_exponent_lt hV_gt1 hfn_div
        _ = 1 + δ/2 := hVε
        _ < sInf S := by linarith
    -- But V^{f(n)/n} ∈ S, so sInf S ≤ V^{f(n)/n} < sInf S, contradiction
    have hVfn_mem : ((V : ℝ) ^ f n) ^ (1 / n : ℝ) ∈ S := ⟨n, hn_ge1, rfl⟩
    linarith [csInf_le hbdd hVfn_mem]
  exact le_antisymm hsInf_le1 hsInf_ge1

/-- GraphClass semiring power equals the quotient of recStrongPowerGraph. -/
theorem graphClass_pow_eq_mk_recStrongPowerGraph (G : Graph) (n : ℕ) :
    (GraphClass.mk G) ^ n = GraphClass.mk (recStrongPowerGraph G n) := by
  induction n with
  | zero =>
    simp only [pow_zero, recStrongPowerGraph]
    rfl  -- Both are mk (EdgelessGraph 1)
  | succ k ih =>
    -- pow_succ: a^(k+1) = a^k * a
    -- recStrongPowerGraph: rec (k+1) = G ⊠ rec k
    simp only [pow_succ, recStrongPowerGraph, ih]
    -- Need: mk (rec k) * mk G = mk (G ⊠ rec k)
    -- Use commutativity: mk A * mk B = mk (A ⊠ B) = mk (B ⊠ A) via Quotient.sound
    rw [mul_comm]
    rfl  -- mk G * mk (rec k) = mk (G ⊠ rec k)

/-- The key bridge: Cohom on SimpleGraph.strongPower corresponds to
    graphCohom on semiring powers in GraphClass.

    This is the ONLY bridge lemma needed - everything else follows from the
    Strassen preorder structure (pow_mono, mul_mono, transitivity). -/
theorem cohom_strongPower_iff_graphCohom_pow (G H : Graph) (n m : ℕ) :
    Cohom (SimpleGraph.strongPower G.graph n) (SimpleGraph.strongPower H.graph m) ↔
    graphCohom ((GraphClass.mk G) ^ n) ((GraphClass.mk H) ^ m) := by
  -- Rewrite both sides to use recStrongPowerGraph via isomorphisms
  rw [graphClass_pow_eq_mk_recStrongPowerGraph, graphClass_pow_eq_mk_recStrongPowerGraph]
  rw [graphCohom_mk]
  -- Now we need: Cohom (strongPower G n) (strongPower H m) ↔
  --              Cohom (recStrongPowerGraph G n).graph (recStrongPowerGraph H m).graph
  -- strongPower G n = (strongPowerGraph G n).graph ≃g (recStrongPowerGraph G n).graph
  let isoG := recStrongPowerGraph_iso G n
  let isoH := recStrongPowerGraph_iso H m
  constructor
  · intro hcoh
    -- Cohom (strongPower G n) (strongPower H m)
    -- strongPower G n = (strongPowerGraph G n).graph
    -- (strongPowerGraph G n).graph ≃g (recStrongPowerGraph G n).graph via isoG.symm
    -- So compose: recStrongPowerGraph G n →_G strongPowerGraph G n →_G strongPowerGraph H m
    --           →_G recStrongPowerGraph H m
    have h1 : Cohom (recStrongPowerGraph G n).graph (strongPowerGraph G n).graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoG)
    have h2 : Cohom (strongPowerGraph H m).graph (recStrongPowerGraph H m).graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoH.symm)
    exact Cohom.trans (Cohom.trans h1 hcoh) h2
  · intro hcoh
    -- Reverse: compose with isoG and isoH.symm
    have h1 : Cohom (strongPowerGraph G n).graph (recStrongPowerGraph G n).graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoG.symm)
    have h2 : Cohom (recStrongPowerGraph H m).graph (strongPowerGraph H m).graph :=
      cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE isoH)
    exact Cohom.trans (Cohom.trans h1 hcoh) h2

/-- Connection between AsympCohom and GraphAsympRel.

    The proof uses:
    1. cohom_strongPower_iff_graphCohom_pow to convert the cohomomorphism
    2. pow_add to split G^{n+f(n)} = G^n * G^{f(n)}
    3. pow_mono from StrassenPreorder: G ≤_G |V| implies G^k ≤_G |V|^k
    4. mul_mono to get (mk H)^n ≤_G (mk G)^n * |V|^{f(n)}

    This approach uses the Strassen preorder structure directly,
    avoiding ad-hoc lemmas about edgeless graphs. -/
theorem asympCohom_implies_graphAsympRel (H G : Graph)
    (h : AsympCohom H G) : GraphClass.mk H ≲ᴬ GraphClass.mk G := by
  obtain ⟨f, hf_littleO, hcohom_n⟩ := h
  let V := Fintype.card G.V
  -- Handle the edge case V = 0 separately
  by_cases hV_pos : 1 ≤ V
  · -- Main case: V ≥ 1 (G has at least one vertex)
    use fun n => V ^ (f n)
    constructor
    · -- Part 1: ∀n≥1, (mk H)^n ≤_P (mk G)^n * V^{f(n)}
      intro n hn
      -- Step 1: Convert Cohom to graphCohom using bridge lemma
      have hcoh := hcohom_n n hn
      have hcoh' : graphCohom ((GraphClass.mk H) ^ n) ((GraphClass.mk G) ^ (n + f n)) :=
        (cohom_strongPower_iff_graphCohom_pow H G n (n + f n)).mp hcoh
      -- Step 2: Split the power using pow_add
      rw [pow_add] at hcoh'
      -- hcoh' : graphCohom (mk H)^n ((mk G)^n * (mk G)^{f n})
      -- Step 3: Use pow_mono: G ≤_G |V| implies G^{f n} ≤_G |V|^{f n}
      have hG_le_V : graphStrassenPreorder.rel (GraphClass.mk G) (V : GraphClass) := by
        rw [natCast_graphClass_eq]
        change Cohom G.graph (edgelessGraph V)
        exact cohom_to_edgeless G
      have hpow : graphStrassenPreorder.rel
          ((GraphClass.mk G) ^ (f n)) ((V : GraphClass) ^ (f n)) :=
        graphStrassenPreorder.pow_mono (f n) hG_le_V
      -- Step 4: Use mul_mono: (mk G)^{f n} * (mk G)^n ≤_G V^{f n} * (mk G)^n
      have hmul := graphStrassenPreorder.mul_mono _ _ ((GraphClass.mk G) ^ n) hpow
      -- Convert (V : GraphClass)^{f n} to ↑(V^{f n})
      have hV_pow : (V : GraphClass) ^ (f n) = ↑(V ^ f n) := by
        simp only [← Nat.cast_pow]
      rw [hV_pow] at hmul
      -- Use commutativity and transitivity
      -- hcoh' : rel (mk H)^n ((mk G)^n * (mk G)^{f n})
      -- hmul : rel ((mk G)^{f n} * (mk G)^n) (↑(V^{f n}) * (mk G)^n)
      -- Goal: rel (mk H)^n ((mk G)^n * ↑(V^{f n}))
      have hcoh'' : graphStrassenPreorder.rel ((GraphClass.mk H) ^ n)
          ((GraphClass.mk G) ^ (f n) * (GraphClass.mk G) ^ n) := by
        rw [mul_comm] at hcoh'; exact hcoh'
      have hmul' : graphStrassenPreorder.rel
          ((GraphClass.mk G) ^ (f n) * (GraphClass.mk G) ^ n)
          ((GraphClass.mk G) ^ n * ↑(V ^ f n)) := by
        have heq : ↑(V ^ f n) * (GraphClass.mk G) ^ n = (GraphClass.mk G) ^ n * ↑(V ^ f n) :=
          mul_comm _ _
        rw [heq] at hmul
        exact hmul
      exact graphStrassenPreorder.trans _ _ _ hcoh'' hmul'
    · -- Part 2: sInf({V^{f(n)/n} : n ≥ 1}) = 1
      -- This follows from: f is little-o implies f(n)/n → 0, so V^{f(n)/n} → 1
      -- Convert (V ^ f n : ℕ) to (V : ℝ) ^ f n
      have heq : (fun n => (↑(V ^ f n) : ℝ) ^ (1 / n : ℝ)) =
                 (fun n => ((V : ℝ) ^ f n) ^ (1 / n : ℝ)) := by
        ext n
        simp only [Nat.cast_pow]
      rw [heq]
      exact littleO_implies_sInf_pow_eq_one f hf_littleO V hV_pos
  · -- Edge case: V = 0 (G has no vertices)
    -- If G has no vertices, then G^(n+f(n)) has no vertices for all n ≥ 1.
    -- Cohom H^n (empty graph) requires H^n to be empty, so H has no vertices.
    -- Thus both mk H = 0 and mk G = 0, and we prove 0 ≲ᴬ 0 using witness 1.
    have hV_zero : V = 0 := by omega
    -- Show G has no vertices
    have hG_empty : IsEmpty G.V := Fintype.card_eq_zero_iff.mp hV_zero
    -- G with no vertices is isomorphic to EdgelessGraph 0, so mk G = 0
    have hG_zero : GraphClass.mk G = 0 := by
      rw [GraphClass.zero_def]
      apply Quotient.sound
      refine ⟨⟨⟨fun v => hG_empty.false v |>.elim, fun v => Fin.elim0 v, ?_, ?_⟩, ?_⟩⟩
      · intro v; exact (hG_empty.false v).elim
      · intro v; exact Fin.elim0 v
      · intro v _; exact (hG_empty.false v).elim
    -- Use n = 1 to show H also has no vertices
    have hcoh1 := hcohom_n 1 (Nat.le_refl 1)
    -- The vertex type of strongPower G k is (Fin k → G.V), which is empty when G.V is empty
    have hG_pow_empty : IsEmpty (Fin (1 + f 1) → G.V) := inferInstance
    -- Cohom X Y requires a function from vertices of X to vertices of Y
    -- If Y's vertex type is empty, X's must be too
    have hH_empty : IsEmpty (Fin 1 → H.V) := by
      obtain ⟨φ, _hφ⟩ := hcoh1
      -- φ : (Fin 1 → H.V) → (Fin (1 + f 1) → G.V)
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨x⟩ := hne
      exact hG_pow_empty.false (φ x)
    -- Fin 1 → H.V is empty iff H.V is empty
    have hH_V_empty : IsEmpty H.V := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      apply hH_empty.false
      exact fun _ => Classical.choice hne
    -- H with no vertices means mk H = 0
    have hH_zero : GraphClass.mk H = 0 := by
      rw [GraphClass.zero_def]
      apply Quotient.sound
      refine ⟨⟨⟨fun v => hH_V_empty.false v |>.elim, fun v => Fin.elim0 v, ?_, ?_⟩, ?_⟩⟩
      · intro v; exact (hH_V_empty.false v).elim
      · intro v; exact Fin.elim0 v
      · intro v _; exact (hH_V_empty.false v).elim
    -- Now we need to show 0 ≲ᴬ 0, which is reflexive
    rw [hH_zero, hG_zero]
    -- Use witness 1: ∀n, 0^n ≤ 0^n * 1 and sInf({1^{1/n}}) = 1
    use fun _ => 1
    constructor
    · intro n hn
      simp only [zero_pow (Nat.one_le_iff_ne_zero.mp hn), zero_mul]
      exact graphStrassenPreorder.refl 0
    · -- sInf({1^{1/n} : n ≥ 1}) = sInf({1}) = 1
      -- The function is n ↦ ↑1 ^ (1/n) = 1 for all n, so the set is {1}
      have himg : (fun n : ℕ => ((1 : ℕ) : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n} = {1} := by
        ext x
        simp only [Nat.cast_one, Set.mem_image, Set.mem_setOf_eq, Real.one_rpow,
                   Set.mem_singleton_iff]
        constructor
        · rintro ⟨_, _, rfl⟩; rfl
        · intro hx; exact ⟨1, Nat.le_refl 1, hx.symm⟩
      rw [himg, csInf_singleton]

/-! ### Reverse Direction: GraphAsympRel → AsympCohom -/

/-- An independent set in a graph is a set of pairwise non-adjacent vertices. -/
def HasIndepSetOfSize (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ S : Finset V, S.card = n ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/-- Edgeless graph E_m has a cohomomorphism to a graph Y iff Y has an independent set of size m. -/
theorem edgeless_cohom_iff_has_indep_set (m : ℕ) (Y : Graph) :
    Cohom (edgelessGraph m) Y.graph ↔ HasIndepSetOfSize Y.graph m := by
  constructor
  · -- Forward: cohom gives us an independent set (the image)
    intro ⟨f, hf⟩
    use Finset.image f Finset.univ
    constructor
    · -- Card: f is injective on Fin m
      rw [Finset.card_image_of_injective]
      · exact Finset.card_fin m
      · intro u v huv
        by_contra hne
        have hnadj : ¬(edgelessGraph m).Adj u v := by simp [edgelessGraph]
        have ⟨hfne, _⟩ := hf u v hne hnadj
        exact hfne huv
    · -- Independent: images of distinct non-adjacent pairs are non-adjacent
      intro u hu v hv huv
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      have hne' : u' ≠ v' := by
        intro heq; subst heq; exact huv rfl
      have hnadj : ¬(edgelessGraph m).Adj u' v' := by simp [edgelessGraph]
      exact (hf u' v' hne' hnadj).2
  · -- Backward: independent set gives us a cohom
    intro ⟨S, hcard, hindep⟩
    -- Get an equivalence S ≃ Fin m and use its inverse
    have hS : Fintype.card ↥S = m := by rw [Fintype.card_coe]; exact hcard
    let e : S ≃ Fin m := Fintype.equivFinOfCardEq hS
    use fun i => (e.symm i : Y.V)
    intro u v huv hnadj
    constructor
    · -- Injectivity
      intro heq
      apply huv
      have := Subtype.coe_injective heq
      exact e.symm.injective this
    · -- Non-adjacency: S is independent
      have hu_mem : (e.symm u : Y.V) ∈ S := (e.symm u).2
      have hv_mem : (e.symm v : Y.V) ∈ S := (e.symm v).2
      have hne : (e.symm u : Y.V) ≠ (e.symm v : Y.V) := by
        intro heq
        apply huv
        exact e.symm.injective (Subtype.coe_injective heq)
      exact hindep _ hu_mem _ hv_mem hne

/-- If G has an independent set of size α, then G^k has an independent set of size α^k.
    More precisely, the k-fold Cartesian product of an independent set is independent in G^k. -/
theorem hasIndepSet_strongPower (G : Graph) (α : ℕ) (k : ℕ)
    (hα : HasIndepSetOfSize G.graph α) :
    HasIndepSetOfSize (recStrongPowerGraph G k).graph (α ^ k) := by
  obtain ⟨S, hcard, hindep⟩ := hα
  induction k with
  | zero =>
    -- G^0 = E_1, and E_1 has independent set of size 1 = α^0
    simp only [pow_zero, recStrongPowerGraph]
    use {⟨0, by decide⟩}
    constructor
    · simp only [Finset.card_singleton]
    · intro u hu v hv huv
      simp only [Finset.mem_singleton] at hu hv
      exact (huv (hu.trans hv.symm)).elim
  | succ n ih =>
    -- G^{n+1} = G ⊠ G^n
    simp only [pow_succ, recStrongPowerGraph]
    obtain ⟨T, hTcard, hTindep⟩ := ih
    -- Use S × T as the independent set
    use S ×ˢ T
    constructor
    · -- v4.29: bare `rw [Finset.card_product]` no longer unifies its `(?s ×ˢ ?t).card`
      -- pattern with the goal's `(S ×ˢ T).card`, because the latter sits at the
      -- `Finset (Graph.strongProduct G _).V` type rather than the expected
      -- `Finset (G.V × _.V)` (the structure-projection coercion blocks `rw`).
      -- Chain the equality through `Finset.card_product S T` explicitly instead.
      exact (Finset.card_product S T).trans (by rw [hcard, hTcard, mul_comm])
    · intro ⟨u, t⟩ hp ⟨v, s⟩ hq hpq
      -- v4.29: same `Finset.mem_product` pattern issue as above; apply the helper directly.
      obtain ⟨hu, ht⟩ := (Finset.mem_product (p := (u, t))).mp hp
      obtain ⟨hv, hs⟩ := (Finset.mem_product (p := (v, s))).mp hq
      simp only [Graph.strongProduct]
      intro ⟨_, h1, h2⟩
      -- Either u ≠ v and they're non-adjacent in G, or t ≠ s and they're non-adjacent in G^n
      by_cases huv : u = v
      · -- u = v, so t ≠ s (by hpq)
        have hts : t ≠ s := by
          intro hts_eq
          apply hpq
          exact Prod.ext huv hts_eq
        -- t and s are in the independent set T of G^n, so they're non-adjacent
        have := hTindep t ht s hs hts
        cases h2 with
        | inl heq => exact hts heq
        | inr hadj => exact this hadj
      · -- u ≠ v, so they're non-adjacent in G (by hindep)
        have := hindep u hu v hv huv
        cases h1 with
        | inl heq => exact huv heq
        | inr hadj => exact this hadj

/-- The vertex count of recStrongPowerGraph is |V(G)|^n. -/
theorem recStrongPowerGraph_card (G : Graph) (n : ℕ) :
    Fintype.card (recStrongPowerGraph G n).V = Fintype.card G.V ^ n := by
  induction n with
  | zero =>
    simp only [recStrongPowerGraph, pow_zero]
    rfl
  | succ k ih =>
    simp only [recStrongPowerGraph, pow_succ]
    -- recStrongPowerGraph G (k+1) = G ⊠ recStrongPowerGraph G k
    -- Vertex set is G.V × (recStrongPowerGraph G k).V
    simp only [Graph.strongProduct]
    -- v4.29: bare `rw [Fintype.card_prod]` no longer unifies its `Fintype.card (?α × ?β)`
    -- pattern with the goal's `Fintype.card (G.V × _.V)`. Chain via explicit `.trans`.
    exact (Fintype.card_prod G.V (recStrongPowerGraph G k).V).trans (by rw [ih, mul_comm])

/-- A cohomomorphism on the second factor of a strong product.
    If f : H → H' is a cohomomorphism, then (id × f) : G ⊠ H → G ⊠ H' is too. -/
theorem _root_.IsCohom.strongProduct_map_snd {V W W' : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {H' : SimpleGraph W'}
    {f : W → W'} (hf : IsCohom H H' f) :
    IsCohom (ShannonCapacity.strongProduct G H)
            (ShannonCapacity.strongProduct G H')
            (Prod.map _root_.id f) := by
  intro ⟨a, x⟩ ⟨b, y⟩ hne hnadj
  simp only [ShannonCapacity.strongProduct, Prod.map_apply] at hnadj ⊢
  -- hnadj: ¬((a,x) ≠ (b,y) ∧ (a=b ∨ G.Adj a b) ∧ (x=y ∨ H.Adj x y))
  have hnadj' : ¬((a = b ∨ G.Adj a b) ∧ (x = y ∨ H.Adj x y)) := by
    intro ⟨h1, h2⟩
    exact hnadj ⟨hne, h1, h2⟩
  -- Split cases based on whether x = y
  by_cases hxy : x = y
  · -- x = y, so from hnadj', we get ¬(a = b ∨ G.Adj a b)
    have hab_stuff : ¬(a = b ∨ G.Adj a b) := fun h => hnadj' ⟨h, Or.inl hxy⟩
    push_neg at hab_stuff
    have ⟨hab, hnadj_G⟩ := hab_stuff
    constructor
    · intro heq; exact hab (Prod.mk.inj heq).1
    · intro ⟨_, hG, _⟩; exact hG.elim hab hnadj_G
  · -- x ≠ y
    by_cases hH : H.Adj x y
    · -- H.Adj x y, so from hnadj' we get ¬(a = b ∨ G.Adj a b)
      have hab_stuff : ¬(a = b ∨ G.Adj a b) := fun h => hnadj' ⟨h, Or.inr hH⟩
      push_neg at hab_stuff
      have ⟨hab, hnadj_G⟩ := hab_stuff
      constructor
      · intro heq; exact hab (Prod.mk.inj heq).1
      · intro ⟨_, hG, _⟩; exact hG.elim hab hnadj_G
    · -- ¬H.Adj x y, so we can use hf
      have ⟨hfne, hfnadj⟩ := hf x y hxy hH
      constructor
      · intro heq; exact hfne (Prod.mk.inj heq).2
      · intro ⟨_, _, hH'⟩; exact hH'.elim hfne hfnadj

/-- Cohom is preserved by strong product on the second factor. -/
theorem _root_.Cohom.strongProduct_right {V W W' : Type*}
    {H : SimpleGraph W} {H' : SimpleGraph W'} (G : SimpleGraph V)
    (hHH' : H ≤_G H') :
    ShannonCapacity.strongProduct G H ≤_G ShannonCapacity.strongProduct G H' := by
  obtain ⟨f, hf⟩ := hHH'
  exact ⟨Prod.map _root_.id f, hf.strongProduct_map_snd⟩

/-- recStrongPowerGraph G (n + m) is isomorphic to
    recStrongPowerGraph G n ⊠ recStrongPowerGraph G m.

    This follows from the semiring structure: (mk G)^{n+m} = (mk G)^n * (mk G)^m. -/
theorem recStrongPowerGraph_add_iso (G : Graph) (n m : ℕ) :
    Nonempty ((recStrongPowerGraph G (n + m)).graph ≃g
              (recStrongPowerGraph G n ⊠ recStrongPowerGraph G m).graph) := by
  -- Key: mk (recG (n+m)) = mk (recG n ⊠ recG m) in GraphClass
  have heq : GraphClass.mk (recStrongPowerGraph G (n + m)) =
             GraphClass.mk (recStrongPowerGraph G n ⊠ recStrongPowerGraph G m) := by
    -- Use pow_add: (mk G)^{n+m} = (mk G)^n * (mk G)^m
    have h1 := graphClass_pow_eq_mk_recStrongPowerGraph G (n + m)
    have h2 := graphClass_pow_eq_mk_recStrongPowerGraph G n
    have h3 := graphClass_pow_eq_mk_recStrongPowerGraph G m
    calc GraphClass.mk (recStrongPowerGraph G (n + m))
        = (GraphClass.mk G) ^ (n + m) := h1.symm
      _ = (GraphClass.mk G) ^ n * (GraphClass.mk G) ^ m := pow_add _ _ _
      _ = GraphClass.mk (recStrongPowerGraph G n) * GraphClass.mk (recStrongPowerGraph G m) := by
          rw [h2, h3]
      _ = GraphClass.mk (recStrongPowerGraph G n ⊠ recStrongPowerGraph G m) := rfl
  -- Quotient equality implies isomorphism
  exact Quotient.exact heq

/-- Cohom from recStrongPowerGraph G n ⊠ recStrongPowerGraph G m
    to recStrongPowerGraph G (n + m). -/
theorem cohom_recStrongPowerGraph_add (G : Graph) (n m : ℕ) :
    Cohom (recStrongPowerGraph G n ⊠ recStrongPowerGraph G m).graph
             (recStrongPowerGraph G (n + m)).graph := by
  obtain ⟨iso⟩ := recStrongPowerGraph_add_iso G n m
  exact cohomLE_to_cohom (SimpleGraph.Iso.toCohomLE iso.symm)

/-- The log₂ bound function: ⌈log₂(x)⌉ = smallest k such that 2^k ≥ x.
    For x = 0 or x = 1, returns 0. -/
noncomputable def logBound (x : ℕ) : ℕ :=
  if x ≤ 1 then 0 else Nat.clog 2 x

/-- 2^{logBound x} ≥ x for all x. -/
theorem two_pow_logBound_ge (x : ℕ) : 2 ^ logBound x ≥ x := by
  simp only [logBound]
  by_cases hx : x ≤ 1
  · simp only [hx, ↓reduceIte]
    omega
  · simp only [hx, ↓reduceIte]
    push_neg at hx
    have h2 : 1 < 2 := by omega
    exact Nat.le_pow_clog h2 x

/-- If y(n)^{1/n} → 1 (as a limit), then logBound(y(n)) is little-o.
    For any ε > 0, eventually y(n) < (1+ε)^n, so log(y(n)) < n*log(1+ε) < ε*n. -/
theorem logBound_littleO_of_tendsto (y : ℕ → ℕ)
    (htendsto : Filter.Tendsto (fun n => (y n : ℝ) ^ (1 / n : ℝ)) Filter.atTop (nhds 1)) :
    IsLittleO (fun n => logBound (y n)) := by
  intro ε hε
  -- From Tendsto, get N such that for n ≥ N, y(n)^{1/n} < 1 + ε/4
  rw [Metric.tendsto_atTop] at htendsto
  set δ := min (ε / 4) 1 with hδ_def
  have hδ_pos : 0 < δ := by simp only [hδ_def, lt_min_iff]; constructor <;> linarith
  have hδ_le1 : δ ≤ 1 := min_le_right _ _
  obtain ⟨N₀, hN₀⟩ := htendsto δ hδ_pos
  -- For large n: y(n) < (1 + δ)^n ≤ 2^n, so clog 2 (y n) ≤ n < ε * n
  use max N₀ (Nat.ceil (2 / ε) + 1)
  intro n hn
  have hn_geN₀ : n ≥ N₀ := le_of_max_le_left hn
  have hn_large : n ≥ Nat.ceil (2 / ε) + 1 := le_of_max_le_right hn
  have hn_pos : 0 < n := by omega
  have hdist := hN₀ n hn_geN₀
  rw [Real.dist_eq] at hdist
  have hyn_lt : (y n : ℝ) ^ (1 / n : ℝ) < 1 + δ := by
    have := abs_lt.mp hdist; linarith [this.2]
  -- Step 1: Show y n < (1 + δ)^n from (y n)^{1/n} < 1 + δ
  have hyn_pos : (0 : ℝ) ≤ y n := Nat.cast_nonneg _
  have h1δ_pos : (0 : ℝ) < 1 + δ := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := by simp [hn_pos.ne']
  have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  -- Raise both sides to the n-th power
  have hyn_lt_pow : (y n : ℝ) < (1 + δ) ^ (n : ℕ) := by
    have hbase_pos : 0 ≤ (y n : ℝ) ^ (1 / n : ℝ) := Real.rpow_nonneg hyn_pos _
    have h1 : ((y n : ℝ) ^ (1 / n : ℝ)) ^ (n : ℕ) < (1 + δ) ^ (n : ℕ) :=
      pow_lt_pow_left₀ hyn_lt hbase_pos hn_pos.ne'
    have h2 : ((y n : ℝ) ^ (1 / n : ℝ)) ^ (n : ℕ) = y n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hyn_pos]
      simp only [one_div, inv_mul_cancel₀ hn_ne, Real.rpow_one]
    rw [h2] at h1
    exact h1
  -- Step 2: Since δ ≤ 1, we have 1 + δ ≤ 2, so (1+δ)^n ≤ 2^n
  have h1δ_le2 : 1 + δ ≤ 2 := by linarith
  have hpow_le : (1 + δ) ^ (n : ℕ) ≤ 2 ^ n := by
    exact pow_le_pow_left₀ (by linarith : 0 ≤ 1 + δ) h1δ_le2 n
  -- Step 3: y n ≤ 2^n - 1 < 2^n (as naturals), so clog 2 (y n) ≤ n
  have hyn_lt_2n : y n < 2 ^ n := by
    have h1 : (y n : ℝ) < 2 ^ n := lt_of_lt_of_le hyn_lt_pow hpow_le
    have h2 : (y n : ℝ) < ((2 : ℕ) ^ n : ℕ) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat] at h1 ⊢; exact h1
    exact Nat.cast_lt.mp h2
  have hclog_le : Nat.clog 2 (y n) ≤ n := by
    apply Nat.clog_le_of_le_pow
    omega
  -- Step 4: Handle the if-then-else in logBound
  simp only [logBound]
  -- Split on whether y n ≤ 1
  split_ifs with hyn_le1
  · -- Case y n ≤ 1: logBound = 0 < ε * n
    simp only [Nat.cast_zero]
    have : ε * n > 0 := by nlinarith
    linarith
  · -- Case y n > 1: need to show Nat.clog 2 (y n) < ε * n
    push_neg at hyn_le1
    -- For ε > 1, we have clog 2 (y n) ≤ n < ε * n, so we're done
    -- For ε ≤ 1, use the tighter bound with δ = ε/4
    by_cases hε_gt1 : ε > 1
    · -- Case ε > 1: clog 2 (y n) ≤ n < ε * n
      calc (Nat.clog 2 (y n) : ℝ) ≤ n := Nat.cast_le.mpr hclog_le
        _ < ε * n := by nlinarith [hn_pos]
    · -- Case ε ≤ 1: Need tighter analysis using δ = ε/4
      push_neg at hε_gt1
      -- δ = min(ε/4, 1) = ε/4 since ε < 1 implies ε/4 < 1
      have hδ_eq : δ = ε / 4 := by
        simp only [hδ_def]; exact min_eq_left (by linarith)
      -- log_2(1+δ) ≤ 2δ for δ ≤ 1 (standard bound)
      -- So (1+δ)^n ≤ 2^(n * 2δ) = 2^(nε/2)
      -- Thus clog 2 (y n) ≤ ⌈nε/2⌉ ≤ nε/2 + 1 < εn (for n > 2/ε)
      -- Use the fact that n ≥ ⌈2/ε⌉ + 1 > 2/ε
      have hn_ge : (n : ℝ) > 2 / ε := by
        have hle : n ≥ Nat.ceil (2 / ε) + 1 := hn_large
        calc (n : ℝ) ≥ Nat.ceil (2 / ε) + 1 := by exact_mod_cast hle
          _ > Nat.ceil (2 / ε) := by linarith
          _ ≥ 2 / ε := Nat.le_ceil _
      -- Key: (1+δ)^n < 2^{2δn} when δ ≤ 1 (since log(1+x) ≤ x and log 2 > 0.5)
      -- For δ = ε/4, this gives (1+ε/4)^n < 2^{εn/2}
      -- So clog 2 (y n) < εn/2 + 1 < εn for n > 2/ε
      -- First, show (1+δ) < 2^{2δ} when 0 < δ ≤ 1
      have hlog_bound : Real.log (1 + δ) ≤ δ := by
        have h1δ_pos' : 0 < 1 + δ := by linarith
        have h := Real.log_le_sub_one_of_pos h1δ_pos'
        linarith
      -- log 2 > 0.693 > 0.5
      have hlog2_pos : (0.5 : ℝ) < Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      -- So log_2(1+δ) = log(1+δ)/log(2) < δ/0.5 = 2δ
      have hlog2_bound : Real.log (1 + δ) / Real.log 2 < 2 * δ := by
        have hlog2_pos' : 0 < Real.log 2 := by linarith
        rw [div_lt_iff₀ hlog2_pos']
        calc Real.log (1 + δ) ≤ δ := hlog_bound
          _ = δ * 1 := by ring
          _ < δ * (2 * Real.log 2) := by nlinarith
          _ = 2 * δ * Real.log 2 := by ring
      -- For δ = ε/4, log_2(1+ε/4) < 2*(ε/4) = ε/2
      rw [hδ_eq] at hlog2_bound
      have hlog2_lt_eps2 : Real.log (1 + ε / 4) / Real.log 2 < ε / 2 := by linarith
      -- So (1+ε/4)^n < 2^{(ε/2)*n}
      -- First: (1+ε/4)^n = 2^{n * log_2(1+ε/4)}
      -- Then: n * log_2(1+ε/4) < n * (ε/2) = εn/2
      -- So (1+ε/4)^n < 2^{εn/2}
      have hδ_eq' : δ = ε / 4 := hδ_eq
      rw [hδ_eq'] at hyn_lt_pow h1δ_pos h1δ_le2 hpow_le
      -- y n < (1 + ε/4)^n < 2^{εn/2}
      -- Since y n is a natural, y n ≤ 2^{⌊εn/2⌋} or y n < 2^{⌈εn/2⌉}
      -- For natural k, y n < 2^k implies clog 2 (y n) ≤ k
      -- We need to find k ≈ εn/2 with y n < 2^k
      -- Key insight: Since n > 2/ε, we have εn > 2, so εn/2 > 1
      have hεn_gt2 : ε * n > 2 := by
        have hε_ne : ε ≠ 0 := by linarith
        have h1 : ε * n > ε * (2 / ε) := mul_lt_mul_of_pos_left hn_ge hε
        have h2 : ε * (2 / ε) = 2 := by field_simp
        linarith
      have hεn2_gt1 : ε * n / 2 > 1 := by linarith
      -- Formalize: y n < 2^{⌈nε/2⌉}, so clog 2 (y n) ≤ ⌈nε/2⌉
      -- And ⌈nε/2⌉ ≤ nε/2 + 1 < nε
      have h_target : (Nat.clog 2 (y n) : ℝ) < ε * n := by
        -- The key step is: (1 + ε/4)^n < 2^{nε/2}
        have h1eps4_lt_2eps2 : (1 + ε / 4) < (2 : ℝ) ^ (ε / 2) := by
          -- Convert to exp form: 1 + ε/4 = exp(log(1+ε/4)), 2^(ε/2) = exp(ε/2 * log 2)
          rw [← Real.exp_log (by linarith : 0 < 1 + ε / 4)]
          rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
          apply Real.exp_strictMono
          calc Real.log (1 + ε / 4) ≤ ε / 4 := by
                have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ε / 4)
                linarith
            _ < Real.log 2 * (ε / 2) := by nlinarith [Real.log_two_gt_d9]
        -- So (1 + ε/4)^n < (2^{ε/2})^n = 2^{nε/2}
        have hpow_lt : (1 + ε / 4) ^ (n : ℕ) < (2 : ℝ) ^ (ε / 2 * n) := by
          have h_eq : ((2 : ℝ) ^ (ε / 2)) ^ (n : ℕ) = (2 : ℝ) ^ (ε / 2 * n) := by
            exact (Real.rpow_mul_natCast (by linarith : (0:ℝ) ≤ 2) (ε / 2) n).symm
          rw [← h_eq]
          exact pow_lt_pow_left₀ h1eps4_lt_2eps2 (by linarith : 0 ≤ 1 + ε / 4) hn_pos.ne'
        -- y n < (1+ε/4)^n < 2^{nε/2}
        have hyn_lt_2eps : (y n : ℝ) < (2 : ℝ) ^ (ε / 2 * n) := by
          calc (y n : ℝ) < (1 + ε / 4) ^ (n : ℕ) := hyn_lt_pow
            _ < (2 : ℝ) ^ (ε / 2 * n) := hpow_lt
        -- Convert to integer bound
        let k := Nat.ceil (ε * n / 2)
        have hk_bound : (k : ℝ) ≤ ε * n / 2 + 1 := by
          have := Nat.le_ceil (ε * n / 2)
          linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ ε * n / 2)]
        have hk_lt_εn : (k : ℝ) < ε * n := by
          calc (k : ℝ) ≤ ε * n / 2 + 1 := hk_bound
            _ < ε * n := by linarith
        -- y n < 2^k (need to show 2^{εn/2} ≤ 2^k, i.e., εn/2 ≤ k)
        have heps2_le_k : ε / 2 * n ≤ k := by
          have := Nat.le_ceil (ε * n / 2)
          simp only [k]
          have h1 : ε * n / 2 = ε / 2 * n := by ring
          rw [← h1]
          exact Nat.le_ceil (ε * n / 2)
        have h2k_ge : (2 : ℝ) ^ (ε / 2 * n) ≤ 2 ^ (k : ℕ) := by
          rw [← Real.rpow_natCast 2 k]
          exact Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr heps2_le_k
        have hyn_lt_2k : (y n : ℝ) < 2 ^ (k : ℕ) := lt_of_lt_of_le hyn_lt_2eps h2k_ge
        have hyn_le_2k : y n ≤ 2 ^ k := by
          have : (y n : ℝ) < (2 ^ k : ℕ) := by
            convert hyn_lt_2k using 1
            simp only [Nat.cast_pow, Nat.cast_ofNat]
          exact le_of_lt (Nat.cast_lt.mp this)
        have hclog_le_k : Nat.clog 2 (y n) ≤ k := by
          apply Nat.clog_le_of_le_pow
          exact hyn_le_2k
        calc (Nat.clog 2 (y n) : ℝ) ≤ k := Nat.cast_le.mpr hclog_le_k
          _ < ε * n := hk_lt_εn
      exact h_target

/-- If G has an independent pair (α(G) ≥ 2), then E_m has a cohomomorphism to G^k when 2^k ≥ m.
    This uses the fact that G^k has an independent set of size 2^k
    (the k-fold product of the pair). -/
theorem edgeless_cohom_to_strongPower (G : Graph) (m k : ℕ)
    (hG_indep : ∃ v₀ v₁ : G.V, v₀ ≠ v₁ ∧ ¬G.graph.Adj v₀ v₁)
    (hmk : m ≤ 2 ^ k) :
    Cohom (edgelessGraph m) (recStrongPowerGraph G k).graph := by
  -- G has an independent set of size 2
  obtain ⟨v₀, v₁, hne, hnadj⟩ := hG_indep
  have hG_indep2 : HasIndepSetOfSize G.graph 2 := by
    use {v₀, v₁}
    constructor
    · simp only [Finset.card_insert_of_notMem (by simp [hne] : v₀ ∉ ({v₁} : Finset G.V)),
                 Finset.card_singleton]
    · intro u hu v hv huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      cases hu with
      | inl h1 => cases hv with
        | inl h2 => exact (huv (h1.trans h2.symm)).elim
        | inr h2 => subst h1 h2; exact hnadj
      | inr h1 => cases hv with
        | inl h2 => subst h1 h2; exact fun h => hnadj (G.graph.symm h)
        | inr h2 => exact (huv (h1.trans h2.symm)).elim
  -- G^k has an independent set of size 2^k
  have hGk_indep := hasIndepSet_strongPower G 2 k hG_indep2
  -- E_m ≤_G E_{2^k} (by size)
  have h1 : Cohom (edgelessGraph m) (edgelessGraph (2 ^ k)) := by
    rw [edgelessGraph_cohom_iff]
    exact hmk
  -- E_{2^k} ≤_G G^k (by independent set)
  have h2 : Cohom (edgelessGraph (2 ^ k)) (recStrongPowerGraph G k).graph :=
    (edgeless_cohom_iff_has_indep_set (2^k) (recStrongPowerGraph G k)).mpr hGk_indep
  -- Compose
  exact Cohom.trans h1 h2

/-- Main theorem: GraphAsympRel implies AsympCohom (for graphs with α(G) ≥ 2).

    The key insight is that if G has at least 2 non-adjacent vertices (α(G) ≥ 2),
    then G^k has an independent set of size 2^k, which is enough to "absorb"
    the edgeless graph factor from the abstract asymptotic relation. -/
theorem graphAsympRel_implies_asympCohom_gapped (H G : Graph)
    (hG_gapped : ∃ v₀ v₁ : G.V, v₀ ≠ v₁ ∧ ¬G.graph.Adj v₀ v₁)
    (hasym : GraphClass.mk H ≲ᴬ GraphClass.mk G) : AsympCohom H G := by
  -- From hasym, we get: ∃ x, (∀n≥1, (mk H)^n ≤_P (mk G)^n * x(n)) ∧ sInf(...) = 1
  obtain ⟨x, hrel, hsInf⟩ := hasym
  -- Use the submultiplicative closure y = submultClosure x
  -- This gives: (1) The bound still holds: H^n ≤ G^n * y(n)
  --             (2) y has Tendsto property (by Fekete), not just sInf = 1
  let y := AsymptoticSpectrumDuality.submultClosure x
  -- First, establish x n ≥ 1 for n ≥ 1 (from sInf = 1)
  have hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1 := by
    intro n hn
    by_contra hlt
    push_neg at hlt
    have hxn0 : x n = 0 := Nat.lt_one_iff.mp hlt
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
    have h1n_ne : (1 : ℝ) / n ≠ 0 := one_div_ne_zero hn_ne
    have hval : (x n : ℝ) ^ ((1 : ℝ) / n) = 0 := by
      simp only [hxn0, Nat.cast_zero, Real.zero_rpow h1n_ne]
    have hmem : (0 : ℝ) ∈ (fun m => (x m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m} := ⟨n, hn, hval⟩
    have hbdd : BddBelow ((fun m => (x m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m}) := by
      use 0; intro z hz; obtain ⟨m, _, rfl⟩ := hz
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hle := csInf_le hbdd hmem
    rw [hsInf] at hle; linarith
  -- y satisfies Tendsto by Fekete's lemma
  have hy_tendsto : Filter.Tendsto (fun n => (y n : ℝ) ^ (1 / n : ℝ)) Filter.atTop (nhds 1) := by
    have hy_ge1 := AsymptoticSpectrumDuality.submultClosure_ge_one x hx_ge1
    have hy_submult := AsymptoticSpectrumDuality.submultClosure_submult x
    have hy_sInf : sInf ((fun n => (y n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) = 1 :=
      AsymptoticSpectrumDuality.submultClosure_sInf_eq_one_of x hx_ge1 hsInf
    -- Apply Fekete: for submultiplicative sequences, Tendsto = sInf
    have hy_ge1_all : ∀ n, 1 ≤ (y n : ℝ) := fun n => by
      by_cases hn : n = 0
      · subst hn; simp [y, AsymptoticSpectrumDuality.submultClosure_zero]
      · exact Nat.one_le_cast.mpr (hy_ge1 n (Nat.one_le_iff_ne_zero.mpr hn))
    have hy_submult_cast : ∀ n m, (y (n + m) : ℝ) ≤ (y n : ℝ) * (y m : ℝ) := fun n m => by
      by_cases hn : n = 0
      · subst hn
        simp only [y, zero_add, AsymptoticSpectrumDuality.submultClosure_zero, Nat.cast_one,
                   one_mul, le_refl]
      · by_cases hm : m = 0
        · subst hm
          simp only [y, add_zero, AsymptoticSpectrumDuality.submultClosure_zero, Nat.cast_one,
                     mul_one, le_refl]
        · have := Nat.cast_le (α := ℝ).mpr (hy_submult n m
            (Nat.one_le_iff_ne_zero.mpr hn) (Nat.one_le_iff_ne_zero.mpr hm))
          simp only [Nat.cast_mul] at this; exact this
    have hfekete := AsymptoticSpectrumDuality.fekete_multiplicative hy_ge1_all hy_submult_cast
    rw [hy_sInf] at hfekete
    exact hfekete
  -- The bound holds for y: submultClosure_bound
  have hy_bound := AsymptoticSpectrumDuality.submultClosure_bound
    graphStrassenPreorder (GraphClass.mk H) (GraphClass.mk G) x hrel
  -- Define f(n) = logBound(y(n))
  use fun n => logBound (y n)
  constructor
  · -- f is little-o: use logBound_littleO_of_tendsto
    exact logBound_littleO_of_tendsto y hy_tendsto
  · -- ∀n≥1, H^⊠n ≤_G G^⊠(n + f(n))
    intro n hn
    -- Get the bound for this n
    have hrel_n := hy_bound n hn
    -- Convert to Cohom
    have hrel_n' : Cohom (recStrongPowerGraph H n).graph
                           (recStrongPowerGraph G n ⊠ EdgelessGraph (y n)).graph := by
      change graphCohom _ _ at hrel_n
      rw [graphClass_pow_eq_mk_recStrongPowerGraph,
          graphClass_pow_eq_mk_recStrongPowerGraph,
          natCast_graphClass_eq,
          GraphClass.mul_def,
          graphCohom_mk] at hrel_n
      exact hrel_n
    -- E_{y(n)} ≤_G G^{logBound(y(n))} because 2^{logBound(y n)} ≥ y n
    have hE_to_Gf : Cohom (edgelessGraph (y n))
        (recStrongPowerGraph G (logBound (y n))).graph :=
      edgeless_cohom_to_strongPower G (y n) (logBound (y n)) hG_gapped (two_pow_logBound_ge (y n))
    -- G^n ⊠ E_{y(n)} ≤_G G^n ⊠ G^{f(n)}
    have hprod : Cohom ((recStrongPowerGraph G n) ⊠ EdgelessGraph (y n)).graph
        ((recStrongPowerGraph G n) ⊠ recStrongPowerGraph G (logBound (y n))).graph := by
      simp only [Graph.strongProduct]
      exact Cohom.strongProduct_right _ hE_to_Gf
    -- Compose: H^n ≤_G G^n ⊠ E_{y(n)} ≤_G G^n ⊠ G^{f(n)}
    have hcomp := Cohom.trans hrel_n' hprod
    -- G^n ⊠ G^{f(n)} → G^{n+f(n)}
    have hfinal := Cohom.trans hcomp (cohom_recStrongPowerGraph_add G n (logBound (y n)))
    -- Convert to the target format
    rw [cohom_strongPower_iff_graphCohom_pow]
    rw [graphClass_pow_eq_mk_recStrongPowerGraph,
        graphClass_pow_eq_mk_recStrongPowerGraph,
        graphCohom_mk]
    exact hfinal

/-- AsympCohom holds when H ≤ 0 in the cohom preorder (H is empty). -/
private lemma asympCohom_of_H_le_zero (H G : Graph)
    (hH_le_zero : graphCohom (GraphClass.mk H) 0) : AsympCohom H G := by
  -- H ≤ 0 means H has a cohom to the empty graph, so H must be empty
  rw [GraphClass.zero_def, graphCohom_mk] at hH_le_zero
  obtain ⟨f, _⟩ := hH_le_zero
  have hH_empty : IsEmpty H.V := by
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨v⟩ := hne
    exact Fin.elim0 (f v)
  -- H is empty, so AsympCohom holds with f = 0
  use fun _ => 0
  constructor
  · intro ε hε; use 1; intro n hn
    simp only [Nat.cast_zero]
    exact mul_pos hε (Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
  · intro n hn
    have hFin_nonempty : Nonempty (Fin n) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩⟩
    have hHn_empty : IsEmpty (Fin n → H.V) := isEmpty_fun.mpr ⟨hFin_nonempty, hH_empty⟩
    exact ⟨fun v => (hHn_empty.false v).elim, fun v _ _ _ => (hHn_empty.false v).elim⟩

/-- AsympCohom holds when H ≤ G in the cohom preorder. -/
private lemma asympCohom_of_H_le_G (H G : Graph)
    (hH_le_G : graphCohom (GraphClass.mk H) (GraphClass.mk G)) : AsympCohom H G := by
  -- H ≤ G implies H^n ≤ G^n for all n, so AsympCohom holds with f = 0
  rw [graphCohom_mk] at hH_le_G
  obtain ⟨f, hf⟩ := hH_le_G
  use fun _ => 0
  constructor
  · intro ε hε; use 1; intro n hn
    simp only [Nat.cast_zero]
    exact mul_pos hε (Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
  · intro n hn
    -- Build cohom from H^n to G^n by applying f componentwise
    refine ⟨fun v => fun i => f (v i), ?_⟩
    intro u v huv hnadj
    -- Strong power adjacency: u ~ v iff u ≠ v ∧ ∀ i, u(i) = v(i) ∨ H.Adj (u i) (v i)
    -- hnadj : ¬Adj u v means: u = v ∨ ∃ i, u(i) ≠ v(i) ∧ ¬H.Adj (u i) (v i)
    -- Since huv : u ≠ v, we get ∃ i, u(i) ≠ v(i) ∧ ¬H.Adj (u i) (v i)
    simp only [SimpleGraph.strongPower, not_and, not_forall] at hnadj
    have ⟨i, hcond⟩ := hnadj huv
    rw [not_or] at hcond
    obtain ⟨hneq, hnadj_i⟩ := hcond
    -- Apply cohomomorphism property of f
    have ⟨hfneq, hfnadj⟩ := hf (u i) (v i) hneq hnadj_i
    constructor
    · intro heq; apply hfneq; exact congr_fun heq i
    · simp only [SimpleGraph.strongPower, not_and, not_forall]
      intro _
      exact ⟨i, by rw [not_or]; exact ⟨hfneq, hfnadj⟩⟩

/-- H ≤ 1 ∧ 2 ≤ H^k leads to 2 ≤ 1, contradiction. -/
private lemma strictlyGapped_contradicts_le_one (H : GraphClass)
    (hH_le_1 : graphCohom H 1)
    (hstrict : ∃ k : ℕ, 0 < k ∧ graphStrassenPreorder.rel 2 (H ^ k)) : False := by
  obtain ⟨k, hk_pos, h2_le_Hk⟩ := hstrict
  -- H ≤ 1 implies H^k ≤ 1^k = 1 (by submultiplicativity of rank)
  have hHk_le_1 : graphCohom (H ^ k) 1 := by
    -- H ≤ 1 implies H^k ≤ 1^k = 1 by pow_mono
    have hpow := graphStrassenPreorder.pow_mono k hH_le_1
    simp only [one_pow] at hpow
    exact hpow
  -- 2 ≤ H^k ≤ 1, so 2 ≤ 1 by transitivity
  have h2_le_1 : graphCohom (2 : GraphClass) 1 :=
    graphStrassenPreorder.trans 2 (H ^ k) 1 h2_le_Hk hHk_le_1
  -- But E_2 doesn't have cohom to E_1
  have h2eq : (2 : GraphClass) = GraphClass.mk (EdgelessGraph 2) := natCast_graphClass_eq 2
  rw [h2eq, GraphClass.one_def, graphCohom_mk] at h2_le_1
  obtain ⟨f, hf⟩ := h2_le_1
  -- Use explicit Fin 2 elements (EdgelessGraph 2).V = Fin 2 definitionally
  have h01 : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := by simp only [ne_eq, Fin.mk.injEq]; omega
  have hnadj : ¬(edgelessGraph 2).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by simp [edgelessGraph]
  have ⟨hfne, _⟩ := hf ⟨0, by omega⟩ ⟨1, by omega⟩ h01 hnadj
  -- f : Fin 2 → Fin 1, and Fin 1 is a subsingleton
  have hsub : Subsingleton (Fin 1) := inferInstance
  exact hfne (@Subsingleton.elim (Fin 1) hsub (f ⟨0, by omega⟩) (f ⟨1, by omega⟩))

/-- Strictly gapped graphs have an independent pair. -/
private lemma strictlyGapped_has_independent_pair (G : Graph)
    (hstrict : ∃ k : ℕ, 0 < k ∧ graphStrassenPreorder.rel 2 ((GraphClass.mk G) ^ k)) :
    ∃ v₀ v₁ : G.V, v₀ ≠ v₁ ∧ ¬G.graph.Adj v₀ v₁ := by
  -- If G had no independent pair, G would be complete, hence G ≤ 1
  -- But strictly gapped contradicts ≤ 1
  by_contra hno_indep
  push_neg at hno_indep
  -- hno_indep : ∀ v₀ v₁, v₀ ≠ v₁ → G.graph.Adj v₀ v₁ (G is complete)
  -- G complete means G ≤ 1
  have hG_le_1 : graphCohom (GraphClass.mk G) 1 := by
    rw [GraphClass.one_def, graphCohom_mk]
    -- Map all vertices to the single vertex
    refine ⟨fun _ => ⟨0, by omega⟩, ?_⟩
    intro u v huv hnadj
    -- If u ≠ v and ¬Adj u v, contradiction with hno_indep
    exact (hnadj (hno_indep u v huv)).elim
  -- Apply strictlyGapped_contradicts_le_one
  exact strictlyGapped_contradicts_le_one (GraphClass.mk G) hG_le_1 hstrict

/-- GraphAsympRel implies AsympCohom for ALL graphs.

    Uses the trichotomy from graph_isGapped:
    1. Strictly gapped (has independent pair): use graphAsympRel_implies_asympCohom_gapped
    2. G ≤ 0 (empty): deduce H ≤ 0, then AsympCohom holds
    3. G ≃ 1 (complete): deduce H ≤ 1, combined with H being gapped gives H ≤ 0 or H ≃ 1 -/
theorem graphAsympRel_implies_asympCohom (H G : Graph) :
    (GraphClass.mk H ≲ᴬ GraphClass.mk G) → AsympCohom H G := by
  intro hasym
  -- Use the trichotomy: every graph is strictly gapped, ≤ 0, or ≃ 1
  rcases graph_isGapped (GraphClass.mk G) with hG_strict | hG_zero | ⟨hG_le_1, h1_le_G⟩
  · -- Case 1: G is strictly gapped (has independent pair)
    have hG_gapped := strictlyGapped_has_independent_pair G hG_strict
    exact graphAsympRel_implies_asympCohom_gapped H G hG_gapped hasym
  · -- Case 2: G ≤ 0 (G is empty)
    -- From H ≲ᴬ G and G = 0, deduce H ≤ 0
    have hH_le_zero : graphCohom (GraphClass.mk H) 0 := by
      -- G ≤ 0 means G has cohom to empty, so G is empty, so G = 0
      -- First extract the cohomomorphism
      change graphCohom (GraphClass.mk G) (GraphClass.mk (EdgelessGraph 0)) at hG_zero
      rw [graphCohom_mk] at hG_zero
      obtain ⟨f, _⟩ := hG_zero
      have hG_empty : IsEmpty G.V := by
        by_contra hne; rw [not_isEmpty_iff] at hne
        obtain ⟨v⟩ := hne; exact Fin.elim0 (f v)
      -- G is empty, so G is isomorphic to EdgelessGraph 0
      have hG_eq_zero : GraphClass.mk G = 0 := by
        rw [GraphClass.zero_def]; apply Quotient.sound; constructor
        refine ⟨⟨fun v => (hG_empty.false v).elim, fun i => Fin.elim0 i, ?_, ?_⟩, ?_⟩
        · intro v; exact (hG_empty.false v).elim
        · intro i; exact Fin.elim0 i
        · intro v _; exact (hG_empty.false v).elim
      -- H ≲ᴬ 0 implies H ≤ 0
      obtain ⟨x, hrel, _⟩ := hasym
      have hrel1 := hrel 1 (Nat.le_refl 1)
      rw [pow_one, hG_eq_zero, zero_pow (by omega : 1 ≠ 0), zero_mul] at hrel1
      change graphCohom (GraphClass.mk H) 0 at hrel1
      exact hrel1
    exact asympCohom_of_H_le_zero H G hH_le_zero
  · -- Case 3: G ≃ 1 (G is complete)
    -- From H ≲ᴬ G and G ≃ 1, deduce H ≤ 1
    have hH_le_1 : graphCohom (GraphClass.mk H) 1 := by
      -- Use trichotomy on H: strictly gapped, ≤ 0, or ≃ 1
      rcases graph_isGapped (GraphClass.mk H) with hH_strict | hH_zero | ⟨hH_le_1', _⟩
      · -- H strictly gapped (∃ k > 0, 2 ≤ H^k) leads to contradiction
        -- From H ≲ᴬ G, extract witness x with H^n ≤ G^n * x(n) and sInf{x(n)^{1/n}} = 1
        obtain ⟨x, hbound, hxinf⟩ := hasym
        -- From G ≤ 1, G^n ≤ 1 for all n, so H^n ≤ x(n)
        have hHn_le_xn : ∀ n, n ≥ 1 → graphCohom ((GraphClass.mk H) ^ n) (x n) := by
          intro n hn
          have hbn := hbound n hn
          -- G^n ≤ 1^n = 1
          have hGn_le_1 : graphCohom ((GraphClass.mk G) ^ n) 1 := by
            have := graphStrassenPreorder.pow_mono n hG_le_1
            simp only [one_pow] at this
            exact this
          -- G^n * x(n) ≤ 1 * x(n) = x(n)
          have hGnx_le_xn : graphCohom ((GraphClass.mk G) ^ n * (x n : GraphClass)) (x n) := by
            have h1 : graphStrassenPreorder.rel ((GraphClass.mk G) ^ n * (x n : GraphClass))
                                                ((1 : GraphClass) * (x n : GraphClass)) :=
              graphStrassenPreorder.mul_mono_left (x n : GraphClass) hGn_le_1
            simp only [one_mul, graphStrassenPreorder] at h1
            exact h1
          exact graphStrassenPreorder.trans _ _ _ hbn hGnx_le_xn
        -- H strictly gapped: ∃ k > 0, 2 ≤ H^k
        obtain ⟨k, hk_pos, h2_le_Hk⟩ := hH_strict
        -- If subrank(H) ≤ 1 (α(H) ≤ 1), then H is empty or clique, so H ≤ 1
        -- Then H^k ≤ 1 by pow_mono, but 2 ≤ H^k contradicts H^k ≤ 1
        -- So subrank(H) ≥ 2
        have hsubrank_H_ge_2 : graphStrassenPreorder.subrank (GraphClass.mk H) ≥ 2 := by
          by_contra hlt
          push_neg at hlt
          have hsub_le_1 : graphStrassenPreorder.subrank (GraphClass.mk H) ≤ 1 :=
            Nat.lt_succ_iff.mp hlt
          -- subrank(H) ≤ 1 means H has no independent pair of size 2, so H ≤ 1
          -- (If H had two non-adjacent vertices, subrank would be ≥ 2)
          have hH_le_1_local : graphStrassenPreorder.rel (GraphClass.mk H) 1 := by
            -- Construct a cohom from H to K_1: map all vertices to 0
            simp only [graphStrassenPreorder, GraphClass.one_def, graphCohom_mk]
            refine ⟨fun _ => ⟨0, by omega⟩, ?_⟩
            intro u v huv hnadj
            -- If u ≠ v and ¬Adj(u, v), then {u, v} is an independent set of size 2
            -- So subrank(H) ≥ 2, contradicting hsub_le_1
            exfalso
            have hindep2 : 2 ≤ graphStrassenPreorder.subrank (GraphClass.mk H) := by
              rw [graphStrassenPreorder.le_subrank_iff]
              -- 2 ≤_P H means E_2 has cohom to H, i.e., H has 2 non-adjacent vertices
              simp only [graphStrassenPreorder]
              rw [natCast_graphClass_eq, graphCohom_mk, EdgelessGraph]
              -- f : Fin 2 → H.V with f(0) = u, f(1) = v is a cohom
              refine ⟨fun i => if i = ⟨0, by omega⟩ then u else v, ?_⟩
              intro x y hxy hnadj_e
              simp only [edgelessGraph] at hnadj_e
              -- x ≠ y in Fin 2 means {x, y} = {0, 1} (or {1, 0})
              fin_cases x <;> fin_cases y
              · exact (hxy rfl).elim
              · simp only [↓reduceIte]
                exact ⟨huv, hnadj⟩
              · simp only [↓reduceIte]
                exact ⟨Ne.symm huv, fun hadj => hnadj (SimpleGraph.Adj.symm hadj)⟩
              · exact (hxy rfl).elim
            omega
          -- H ≤ 1 implies H^k ≤ 1
          have hHk_le_1 : graphStrassenPreorder.rel ((GraphClass.mk H) ^ k) 1 := by
            have := graphStrassenPreorder.pow_mono k hH_le_1_local
            simp only [one_pow] at this
            exact this
          -- 2 ≤ H^k and H^k ≤ 1 gives 2 ≤ 1, contradiction
          exact strictlyGapped_contradicts_le_one (GraphClass.mk H)
            hH_le_1_local ⟨k, hk_pos, h2_le_Hk⟩
        -- From subrank(H) ≥ 2 and supermultiplicativity, subrank(H^n) ≥ 2^n
        have hsubrank_Hn_ge :
            ∀ n, n ≥ 1 → graphStrassenPreorder.subrank ((GraphClass.mk H) ^ n) ≥ 2 ^ n := by
          intro n _
          have hpow := graphStrassenPreorder.le_subrank_pow (a := GraphClass.mk H) n
          calc 2 ^ n ≤ graphStrassenPreorder.subrank (GraphClass.mk H) ^ n :=
                Nat.pow_le_pow_left hsubrank_H_ge_2 n
            _ ≤ graphStrassenPreorder.subrank ((GraphClass.mk H) ^ n) := hpow
        -- From H^n ≤ x(n), subrank(H^n) ≤ subrank(x(n)) = x(n)
        have hsubrank_Hn_le :
            ∀ n, n ≥ 1 → graphStrassenPreorder.subrank ((GraphClass.mk H) ^ n) ≤ x n := by
          intro n hn
          have hHn := hHn_le_xn n hn
          have hsub := graphStrassenPreorder.subrank_mono hHn
          rw [graphStrassenPreorder.subrank_natCast'] at hsub
          exact hsub
        -- So 2^n ≤ x(n), hence x(n)^{1/n} ≥ 2 for all n ≥ 1
        have hxn_ge : ∀ n, n ≥ 1 → x n ≥ 2 ^ n := by
          intro n hn
          exact le_trans (hsubrank_Hn_ge n hn) (hsubrank_Hn_le n hn)
        have hxn_root_ge : ∀ n, n ≥ 1 → (x n : ℝ) ^ (1 / (n : ℝ)) ≥ 2 := by
          intro n hn
          have hn_pos : (0 : ℝ) < n :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
          have hexp_pos : 0 < 1 / (n : ℝ) := div_pos one_pos hn_pos
          have h2n : (2 : ℝ) ^ n ≤ x n := by
            calc (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by simp
              _ ≤ (x n : ℝ) := Nat.cast_le.mpr (hxn_ge n hn)
          calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
            _ = 2 ^ ((n : ℝ) * (1 / (n : ℝ))) := by rw [mul_one_div_cancel (ne_of_gt hn_pos)]
            _ = (2 ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            _ = ((2 : ℝ) ^ n) ^ (1 / (n : ℝ)) := by rw [Real.rpow_natCast]
            _ ≤ (x n : ℝ) ^ (1 / (n : ℝ)) :=
                Real.rpow_le_rpow (by positivity) h2n (le_of_lt hexp_pos)
        -- But sInf{x(n)^{1/n}} = 1 < 2, contradiction since all elements are ≥ 2
        have hbdd : BddBelow ((fun m => (x m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m}) := by
          use 2; intro z hz; obtain ⟨m, hm, rfl⟩ := hz
          exact hxn_root_ge m hm
        have hinf_ge :
            sInf ((fun m => (x m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m}) ≥ 2 := by
          apply le_csInf
          · -- Set is nonempty
            refine ⟨(x 1 : ℝ) ^ (1 / (1 : ℝ)), ?_⟩
            simp only [Set.mem_image, Set.mem_setOf_eq]
            exact ⟨1, Nat.le_refl 1, by norm_num⟩
          · intro z hz; obtain ⟨m, hm, rfl⟩ := hz; exact hxn_root_ge m hm
        rw [hxinf] at hinf_ge
        linarith
      · -- H ≤ 0 implies H ≤ 1 (since 0 ≤ 1)
        have h0_le_1 : graphStrassenPreorder.rel (0 : GraphClass) 1 :=
          graphStrassenPreorder.zero_le 1
        exact graphStrassenPreorder.trans _ _ _ hH_zero h0_le_1
      · -- H ≤ 1
        exact hH_le_1'
    -- Use trichotomy on H: strictly gapped, ≤ 0, or ≃ 1
    rcases graph_isGapped (GraphClass.mk H) with hH_strict | hH_zero | ⟨hH_le_1', h1_le_H⟩
    · -- H strictly gapped contradicts H ≤ 1
      exact (strictlyGapped_contradicts_le_one (GraphClass.mk H) hH_le_1 hH_strict).elim
    · -- H ≤ 0
      exact asympCohom_of_H_le_zero H G hH_zero
    · -- H ≃ 1 and G ≃ 1: H ≤ 1 ≤ G, so H ≤ G
      have hH_le_G : graphCohom (GraphClass.mk H) (GraphClass.mk G) :=
        graphStrassenPreorder.trans (GraphClass.mk H) 1 (GraphClass.mk G) hH_le_1' h1_le_G
      exact asympCohom_of_H_le_G H G hH_le_G

/-! ### The equivalence theorems (moved here after dependencies are defined) -/

/-- The two asymptotic relations on graphs are equivalent:
    - AsympCohom H G: H^n ≤_G G^{n+o(n)} (concrete form)
    - GraphAsympRel H G: H^n ≤ E_2^{o(n)} · G^n (abstract form)

    This equivalence holds for all graphs. -/
theorem asympCohom_iff_graphAsympRel (H G : Graph) :
    AsympCohom H G ↔ GraphClass.mk H ≲ᴬ GraphClass.mk G := by
  constructor
  · exact asympCohom_implies_graphAsympRel H G
  · exact graphAsympRel_implies_asympCohom H G

/-- Combined spectral duality: AsympCohom H G iff all spectral points agree.
    This combines `spectral_duality` and `asympCohom_iff_graphAsympRel`. -/
theorem asympCohom_iff_forall_spectralPoint (H G : Graph) :
    AsympCohom H G ↔ ∀ φ : SpectralPoint, φ.eval H ≤ φ.eval G := by
  rw [asympCohom_iff_graphAsympRel, spectral_duality]

/-! ### Asymptotic Rank equals Fractional Clique Cover -/

/-- (1 + n * c)^{1/n} → 1 as n → ∞ for c ≥ 0.
    This is used in the proof that graphAsympRank = χ̄_f. -/
private lemma tendsto_one_add_mul_rpow_one_div (c : ℝ) (hc : 0 ≤ c) :
    Filter.Tendsto (fun n : ℕ => (1 + n * c) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
  by_cases hc0 : c = 0
  · simp only [hc0, mul_zero, add_zero]
    have : (fun n : ℕ => (1 : ℝ) ^ (1 / (n : ℝ))) = fun _ => 1 := by
      ext n; exact Real.one_rpow _
    rw [this]; exact tendsto_const_nhds
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have h1 : Filter.Tendsto (fun n : ℕ => (1 + (n : ℝ) * c)) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_atTop_of_monotone
      · intro x y hxy
        have : (x : ℝ) * c ≤ (y : ℝ) * c := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hxy) hc
        linarith
      · intro b
        use Nat.ceil (max 0 ((b - 1) / c))
        have hceil : (Nat.ceil (max 0 ((b - 1) / c)) : ℝ) ≥ max 0 ((b - 1) / c) := Nat.le_ceil _
        have : (Nat.ceil (max 0 ((b - 1) / c)) : ℝ) * c ≥ ((b - 1) / c) * c := by
          apply mul_le_mul_of_nonneg_right _ hc; linarith [le_max_right (0 : ℝ) ((b - 1) / c)]
        calc 1 + (Nat.ceil (max 0 ((b - 1) / c)) : ℝ) * c
            ≥ 1 + ((b - 1) / c) * c := by linarith
          _ = 1 + (b - 1) := by field_simp
          _ = b := by ring
    have h2 : Filter.Tendsto (fun n : ℕ => (1 + n * c) ^ (1 / (1 + n * c)))
        Filter.atTop (nhds 1) := tendsto_rpow_div.comp h1
    have h3 : Filter.Tendsto (fun n : ℕ => (1 + n * c) / n) Filter.atTop (nhds c) := by
      have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have h4 : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ + c) Filter.atTop (nhds (0 + c)) :=
        Filter.Tendsto.add hinv tendsto_const_nhds
      rw [zero_add] at h4
      have heq : (fun n : ℕ => (1 + n * c) / n) =ᶠ[Filter.atTop] (fun n : ℕ => (n : ℝ)⁻¹ + c) := by
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        field_simp
      exact h4.congr' heq.symm
    have h4 : Filter.Tendsto (fun n : ℕ => ((1 + n * c) ^ (1 / (1 + n * c))) ^ ((1 + n * c) / n))
        Filter.atTop (nhds (1 ^ c)) := Filter.Tendsto.rpow h2 h3 (by left; norm_num)
    rw [Real.one_rpow] at h4
    have heq : (fun n : ℕ => (1 + n * c) ^ (1 / (n : ℝ))) =ᶠ[Filter.atTop]
        (fun n : ℕ => ((1 + n * c) ^ (1 / (1 + n * c))) ^ ((1 + n * c) / n)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
      have hpos : 0 < 1 + n * c := by positivity
      rw [← Real.rpow_mul (le_of_lt hpos)]
      congr 1; field_simp
    exact h4.congr' heq.symm

/-- χ̄_f is nonnegative. -/
private lemma chibar_nonneg (G : Graph) : 0 ≤ χ̄_f G := by
  unfold fractionalCliqueCovering_finite fractionalCliqueCoverNumber_finite
    fractionalCliqueCoverNumber
  apply le_ciInf
  intro cover
  exact cover.totalWeight_nonneg

set_option linter.unusedFintypeInType false in
/-- If cliqueNum = 0, then V is empty (since each vertex forms a clique of size 1). -/
private lemma isEmpty_of_cliqueNum_eq_zero {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : G.cliqueNum = 0) : IsEmpty V := by
  classical
  by_contra hne
  rw [not_isEmpty_iff] at hne
  obtain ⟨v⟩ := hne
  -- {v} is a clique of size 1
  have h1 : G.IsNClique 1 {v} := SimpleGraph.isNClique_singleton.mpr rfl
  have hisClique := h1.isClique
  have hcard := h1.card_eq
  have hle := hisClique.card_le_cliqueNum
  rw [hcard, h] at hle
  omega

/-- χ̄_f of an empty graph is 0. -/
private lemma chibar_empty (G : Graph) (hempty : IsEmpty G.V) : χ̄_f G = 0 := by
  unfold fractionalCliqueCovering_finite fractionalCliqueCoverNumber_finite
    fractionalCliqueCoverNumber
  -- The infimum over covers is 0 when there's nothing to cover
  apply le_antisymm
  · -- Show χ̄_f ≤ 0 via the zero cover
    -- Construct the empty cover directly
    let cover : FractionalCliqueCover G.graph := {
      cliques := ∅
      weights := fun _ => 0
      isClique := fun C hC => (Finset.notMem_empty C hC).elim
      nonneg := fun C hC => (Finset.notMem_empty C hC).elim
      covers := fun v => hempty.elim v
    }
    have hzero : cover.totalWeight = 0 := by
      simp only [FractionalCliqueCover.totalWeight]
      rfl
    have hbdd : BddBelow (Set.range fun c : FractionalCliqueCover G.graph =>
        c.totalWeight) := by
      use 0
      intro x hx
      obtain ⟨c, rfl⟩ := hx
      exact c.totalWeight_nonneg
    calc ⨅ c : FractionalCliqueCover G.graph, c.totalWeight
        ≤ cover.totalWeight := ciInf_le hbdd cover
      _ = 0 := hzero
  · -- Show 0 ≤ χ̄_f
    apply le_ciInf
    intro cover
    exact cover.totalWeight_nonneg

/-- graphRank of a graph power equals graphRank applied to the power in GraphClass. -/
private lemma graphRank_recStrongPowerGraph (G : Graph) (n : ℕ) :
    graphRank (GraphClass.mk (recStrongPowerGraph G n)) =
    graphRank ((GraphClass.mk G) ^ n) := by
  rw [graphClass_pow_eq_mk_recStrongPowerGraph]

/-- graphAsympRank equals fractional clique cover number: graphAsympRank(G) = χ̄_f(G).

    Proof outline:
    - Lower bound (χ̄_f ≤ graphAsympRank): proved via chibar_le_graphAsympRank
    - Upper bound (graphAsympRank ≤ χ̄_f): Use logarithmic_bound on G^n:
      χ̄(G^n) ≤ (1 + n·ln(ω(G))) · χ̄_f(G)^n
      Taking n-th roots: χ̄(G^n)^{1/n} ≤ (1 + n·ln(ω(G)))^{1/n} · χ̄_f(G)
      As n → ∞, the first factor → 1, so inf_n χ̄(G^n)^{1/n} ≤ χ̄_f(G)
-/
theorem graphAsympRank_eq_chibar (G : Graph) :
    graphAsympRank (GraphClass.mk G) = χ̄_f G := by
  apply le_antisymm
  · -- Upper bound: graphAsympRank ≤ χ̄_f
    -- graphAsympRank = sInf { graphRank((mk G)^n)^{1/n} : n ≥ 1 }
    -- Strategy: show that elements of the set are bounded above by a sequence
    -- converging to χ̄_f(G), then use ge_of_tendsto to conclude sInf ≤ χ̄_f
    simp only [graphAsympRank, StrassenPreorder.asympRank]
    -- Handle degenerate case: empty graph has ω = 0
    by_cases hω : G.graph.cliqueNum = 0
    · -- Empty graph: rank = 0, χ̄_f = 0
      have hempty : IsEmpty G.V := isEmpty_of_cliqueNum_eq_zero G.graph hω
      have hrank0 : ∀ n : ℕ, 0 < n →
          graphStrassenPreorder.rank ((GraphClass.mk G) ^ n) = 0 := by
        intro n hn
        rw [graphClass_pow_eq_mk_recStrongPowerGraph]
        -- Now goal is: graphStrassenPreorder.rank (GraphClass.mk (recStrongPowerGraph G n)) = 0
        -- graphRank = graphStrassenPreorder.rank by definition
        change graphRank (GraphClass.mk (recStrongPowerGraph G n)) = 0
        -- ω(G^n) = ω(G)^n = 0^n = 0 for n > 0, so G^n is empty
        have hωn : (recStrongPowerGraph G n).graph.cliqueNum = 0 := by
          rw [cliqueNum_recStrongPowerGraph, hω, zero_pow (Nat.pos_iff_ne_zero.mp hn)]
        have hempty_n : IsEmpty (recStrongPowerGraph G n).V :=
          isEmpty_of_cliqueNum_eq_zero (recStrongPowerGraph G n).graph hωn
        -- Empty graph has rank 0
        rw [graphRank_eq_chromaticNumber_toNat (recStrongPowerGraph G n)]
        -- χ(Gᶜ) = 0 for empty G (no vertices to color)
        haveI : IsEmpty (recStrongPowerGraph G n).V := hempty_n
        simp only [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty, ENat.toNat_zero]
      have hχ0 : χ̄_f G = 0 := chibar_empty G hempty
      rw [hχ0]
      -- sInf { 0^{1/n} : n ≥ 1 } = 0
      -- All elements of S are 0, so sInf S = 0
      have hall_zero : ∀ x ∈ graphStrassenPreorder.asympRankSet (GraphClass.mk G), x = 0 := by
        intro x hx
        simp only [StrassenPreorder.asympRankSet, Set.mem_image, Set.mem_Ici] at hx
        obtain ⟨n, hn, rfl⟩ := hx
        have hn_pos : 0 < n := Nat.one_le_iff_ne_zero.mp hn |> Nat.pos_of_ne_zero
        rw [hrank0 n hn_pos]
        simp only [Nat.cast_zero]
        have hn_ne : (1 : ℝ) / n ≠ 0 := one_div_ne_zero (Nat.cast_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp hn_pos))
        rw [Real.zero_rpow hn_ne]
      -- Since all elements are 0 and set is nonempty, sInf = 0
      have hnonempty := graphStrassenPreorder.asympRankSet_nonempty (GraphClass.mk G)
      obtain ⟨y, hy⟩ := hnonempty
      have hy0 : y = 0 := hall_zero y hy
      rw [← hy0]
      exact csInf_le (graphStrassenPreorder.asympRankSet_bddBelow (GraphClass.mk G)) hy
    · -- Non-empty graph: ω ≥ 1
      have hω_pos : 0 < G.graph.cliqueNum := Nat.pos_of_ne_zero hω
      have hω_ge1 : 1 ≤ G.graph.cliqueNum := hω_pos
      let c := Real.log G.graph.cliqueNum
      have hc_nn : 0 ≤ c := Real.log_nonneg (Nat.one_le_cast.mpr hω_ge1)
      -- Upper bound on each term: graphRank(G^n)^{1/n} ≤ (1 + n*c)^{1/n} * χ̄_f(G)
      have hbound : ∀ n : ℕ, 1 ≤ n →
          (graphStrassenPreorder.rank ((GraphClass.mk G) ^ n) : ℝ) ^ (1 / (n : ℝ)) ≤
          (1 + n * c) ^ (1 / (n : ℝ)) * χ̄_f G := by
        intro n hn
        have hn_pos' : 0 < n := Nat.one_le_iff_ne_zero.mp hn |> Nat.pos_of_ne_zero
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos'
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        -- Apply logarithmic_bound to G^n
        have hω_n : 1 ≤ (recStrongPowerGraph G n).graph.cliqueNum := by
          rw [cliqueNum_recStrongPowerGraph]
          exact Nat.one_le_pow n _ hω_pos
        have hlog := logarithmic_bound (recStrongPowerGraph G n) hω_n
        simp only [graphRank] at hlog
        -- Use power lemmas
        rw [cliqueNum_recStrongPowerGraph, chibar_recStrongPowerGraph] at hlog
        have hlog_pow : Real.log (G.graph.cliqueNum ^ n : ℕ) = n * c := by
          rw [Nat.cast_pow, Real.log_pow]
        rw [hlog_pow] at hlog
        -- hlog : graphStrassenPreorder.rank(mk(G^n)) ≤ (1 + n*c) * χ̄_f(G)^n
        -- Convert to graphStrassenPreorder.rank((mk G)^n)
        rw [← graphClass_pow_eq_mk_recStrongPowerGraph] at hlog
        -- Now take n-th roots
        have hrank_nn : (0 : ℝ) ≤ graphStrassenPreorder.rank ((GraphClass.mk G) ^ n) :=
          Nat.cast_nonneg _
        have hχ_nn : 0 ≤ χ̄_f G := chibar_nonneg G
        have hcoeff_pos : 0 < 1 + n * c := by
          calc 1 + n * c ≥ 1 + 0 := by linarith [mul_nonneg (Nat.cast_nonneg n) hc_nn]
            _ = 1 := by ring
            _ > 0 := by norm_num
        have hχ_pow_nn : 0 ≤ (χ̄_f G) ^ n := pow_nonneg hχ_nn n
        have hrhs_nn : 0 ≤ (1 + n * c) * (χ̄_f G) ^ n := mul_nonneg (le_of_lt hcoeff_pos) hχ_pow_nn
        have hroot := Real.rpow_le_rpow hrank_nn hlog (one_div_nonneg.mpr (le_of_lt hn_pos))
        calc (graphStrassenPreorder.rank ((GraphClass.mk G) ^ n) : ℝ) ^
              (1 / (n : ℝ))
            ≤ ((1 + n * c) * (χ̄_f G) ^ n) ^ (1 / (n : ℝ)) := hroot
          _ = (1 + n * c) ^ (1 / (n : ℝ)) * ((χ̄_f G) ^ n) ^ (1 / (n : ℝ)) := by
              rw [Real.mul_rpow (le_of_lt hcoeff_pos) hχ_pow_nn]
          _ = (1 + n * c) ^ (1 / (n : ℝ)) * (χ̄_f G) ^ (n * (1 / (n : ℝ))) := by
              rw [← Real.rpow_natCast (χ̄_f G) n, ← Real.rpow_mul hχ_nn]
          _ = (1 + n * c) ^ (1 / (n : ℝ)) * (χ̄_f G) ^ (1 : ℝ) := by
              congr 1; field_simp
          _ = (1 + n * c) ^ (1 / (n : ℝ)) * χ̄_f G := by rw [Real.rpow_one]
      -- The sequence (1 + n*c)^{1/n} * χ̄_f(G) → χ̄_f(G)
      have hconv : Filter.Tendsto
          (fun n : ℕ => (1 + n * c) ^ (1 / (n : ℝ)) * χ̄_f G)
          Filter.atTop (nhds (χ̄_f G)) := by
        have h1 := tendsto_one_add_mul_rpow_one_div c hc_nn
        have h2 := Filter.Tendsto.mul h1 (@tendsto_const_nhds _ _ _ (χ̄_f G) _)
        simp only [one_mul] at h2
        exact h2
      -- Use ge_of_tendsto: sInf ≤ limit of upper bounds
      apply ge_of_tendsto hconv
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      -- Show sInf S ≤ (1 + n*c)^{1/n} * χ̄_f
      -- This follows from: f(n) ∈ S, sInf S ≤ f(n), f(n) ≤ upper_bound
      have hmem : (graphStrassenPreorder.rank ((GraphClass.mk G) ^ n) : ℝ) ^ (1 / (n : ℝ)) ∈
          graphStrassenPreorder.asympRankSet (GraphClass.mk G) := by
        simp only [StrassenPreorder.asympRankSet, Set.mem_image, Set.mem_Ici]
        exact ⟨n, hn, rfl⟩
      calc sInf (graphStrassenPreorder.asympRankSet (GraphClass.mk G))
          ≤ (graphStrassenPreorder.rank ((GraphClass.mk G) ^ n) : ℝ) ^ (1 / (n : ℝ)) :=
            csInf_le (graphStrassenPreorder.asympRankSet_bddBelow (GraphClass.mk G)) hmem
        _ ≤ (1 + n * c) ^ (1 / (n : ℝ)) * χ̄_f G := hbound n hn
  · -- Lower bound: χ̄_f ≤ graphAsympRank
    exact chibar_le_graphAsympRank G

/-- χ̄_f is the maximum spectral point: for all φ and G, φ(G) ≤ χ̄_f(G).

    This follows from:
    1. graphSpectralPointToAbstract φ is an abstract spectral point
    2. spectralPoint_le_asympRank: abstract spectral point ≤ asympRank
    3. graphAsympRank_eq_chibar: asympRank = χ̄_f
    4. graphSpectralPointToAbstract φ evaluated at G equals φ.eval G -/
theorem chibar_is_max (G : Graph) (φ : SpectralPoint) :
    φ.eval G ≤ χ̄_f G := by
  -- Convert graph SpectralPoint to abstract SpectralPoint
  let ψ : AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder :=
    graphSpectralPointToAbstract φ
  -- ψ(mk G) ≤ graphAsympRank(mk G) by spectralPoint_le_asympRank
  have h1 : AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder
      (GraphClass.mk G) ψ ≤ graphAsympRank (GraphClass.mk G) :=
    graphStrassenPreorder.spectralPoint_le_asympRank ψ (GraphClass.mk G)
  -- graphAsympRank(mk G) = χ̄_f G
  rw [graphAsympRank_eq_chibar] at h1
  -- ψ(mk G) = φ.eval G by definition
  simp only [AsymptoticSpectrumDuality.AsymptoticSpectrum.eval] at h1
  exact h1

/-! ### Shannon Capacity -/

/-- The Shannon capacity Θ(G) of a graph, defined as the asymptotic subrank.
    This equals sup_{n≥1} α(G^⊠n)^{1/n} = lim_{n→∞} α(G^⊠n)^{1/n} = min_{φ} φ(G). -/
noncomputable def shannonCapacity (G : Graph) : ℝ :=
  graphAsympSubrank (GraphClass.mk G)

/-- Independence number of recStrongPowerGraph equals that of strongPowerGraph. -/
theorem indepNum_recStrongPowerGraph_eq_strongPower (G : Graph) (n : ℕ) :
    (recStrongPowerGraph G n).graph.indepNum =
    (SimpleGraph.strongPower G.graph n).indepNum := by
  -- They are isomorphic, so have the same independence number
  have hiso := recStrongPowerGraph_iso G n
  -- strongPowerGraph G n has the same graph as SimpleGraph.strongPower
  have heq : (strongPowerGraph G n).graph = SimpleGraph.strongPower G.graph n := rfl
  rw [← heq]
  exact SimpleGraph.independenceNumber_iso hiso

/-- The subrank of a graph power equals the independence number of the strong power. -/
theorem graphSubrank_pow_eq_indepNum (G : Graph) (n : ℕ) :
    graphStrassenPreorder.subrank ((GraphClass.mk G) ^ n) =
    (SimpleGraph.strongPower G.graph n).indepNum := by
  rw [graphClass_pow_eq_mk_recStrongPowerGraph]
  -- Now: graphStrassenPreorder.subrank (GraphClass.mk (recStrongPowerGraph G n)) = ...
  -- graphStrassenPreorder.subrank = graphSubrank by definition
  change graphSubrank (GraphClass.mk (recStrongPowerGraph G n)) = _
  rw [graphSubrank_eq_indepNum]
  exact indepNum_recStrongPowerGraph_eq_strongPower G n

/-- Shannon capacity equals the supremum over α(G^⊠n)^{1/n} for n ≥ 1. -/
theorem shannonCapacity_eq_iSup (G : Graph) :
    shannonCapacity G = sSup ((fun n : ℕ =>
      ((SimpleGraph.strongPower G.graph n).indepNum : ℝ) ^ (1 / (n : ℝ))) '' Set.Ici 1) := by
  unfold shannonCapacity graphAsympSubrank
  rw [graphStrassenPreorder.asympSubrank_eq_iSup]
  -- asympSubrankSet uses subrank((GraphClass.mk G)^n)^{1/n}
  -- We need to show this equals indepNum(strongPower G n)^{1/n}
  congr 1
  ext x
  simp only [StrassenPreorder.asympSubrankSet, Set.mem_image, Set.mem_Ici]
  constructor
  · intro ⟨n, hn, hx⟩
    use n, hn
    rw [← hx, graphSubrank_pow_eq_indepNum]
  · intro ⟨n, hn, hx⟩
    use n, hn
    rw [← hx, graphSubrank_pow_eq_indepNum]

/-- Shannon capacity equals the limit of α(G^⊠n)^{1/n} as n → ∞.
    This requires that 1 ≤_coh G (i.e., G has at least one vertex). -/
theorem shannonCapacity_eq_tendsto (G : Graph)
    (hG : graphStrassenPreorder.rel 1 (GraphClass.mk G)) :
    Filter.Tendsto (fun n : ℕ =>
      ((SimpleGraph.strongPower G.graph n).indepNum : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds (shannonCapacity G)) := by
  unfold shannonCapacity graphAsympSubrank
  -- Use the abstract Fekete lemma result
  have htend := graphStrassenPreorder.asympSubrank_eq_tendsto hG
  -- Convert from subrank to indepNum
  convert htend using 1
  ext n
  rw [graphSubrank_pow_eq_indepNum]

/-- Shannon capacity equals the infimum over all spectral points.
    Θ(G) = ⨅ φ, φ(G) -/
theorem shannonCapacity_eq_iInf_spectrum (G : Graph) :
    shannonCapacity G =
      ⨅ φ : AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder,
        AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder
          (GraphClass.mk G) φ := by
  unfold shannonCapacity
  exact graphAsympSubrank_eq_iInf_spectrum (GraphClass.mk G)

/-- Shannon capacity is achieved by some spectral point.
    ∃ φ, Θ(G) = φ(G) -/
theorem shannonCapacity_eq_min_spectrum (G : Graph) :
    ∃ φ : AsymptoticSpectrumDuality.AsymptoticSpectrum graphStrassenPreorder,
      shannonCapacity G =
        AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder
          (GraphClass.mk G) φ := by
  unfold shannonCapacity
  exact graphAsympSubrank_eq_min_spectrum (GraphClass.mk G)

end AsymptoticSpectrumGraphs
