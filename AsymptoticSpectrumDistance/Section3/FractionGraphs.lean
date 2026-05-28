/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section3.VertexRemoval
import AsymptoticSpectrumDistance.Section2.CoveringLemma
import AsymptoticSpectrumDistance.Prerequisites.InducedSubgraphBound

/-!
# Fraction Graphs: Main Theorems

This file contains the main theorems about fraction graphs E_{p/q} for the
asymptotic spectrum distance paper.

The basic definitions are in `FractionGraphsDefs.lean`, and the core lemmas
are in `VertexRemoval.lean` (ceiling-based clean implementation).

## Main results

* `fractionGraph_remove_vertex_equiv` : E_{p/q} - v ≃ E_{p'/q'} where pq' - qp' = 1
* `fractionGraph_spectral_bounds` : F(E_{p'/q'}) ≤ F(E_{p/q}) ≤ (p/(p-1)) F(E_{p'/q'})

## References

* [Hell-Nešetřil] Graphs and Homomorphisms, Section 6
* [de Boer, Buys, Zuiddam] Section 3.1
-/

namespace AsymptoticSpectrumDistance

open Universality AsymptoticSpectrumGraphs SimpleGraph FractionGraphBasic

/-- The induced subgraph E_{p/q}[V - {v}] (removing any vertex) is equivalent
    to E_{p'/q'} where 0 < p' < p, 0 < q' < q, and pq' - qp' = 1.

    Lemma 6.6 (Hell-Nešetřil): Removing any vertex from E_{p/q} gives a graph
    that is graph-homomorphism equivalent to E_{p'/q'}.

    Note: "Equivalent" means there exist homomorphisms in both directions.
    This is NOT isomorphism (the graphs have different numbers of vertices).

    Note: Requires q ≥ 2 for the Stern-Brocot predecessor to exist
    (since we need 0 < q' < q).

    Proof outline (from Hell-Nešetřil):
    1. Define the winding subset X = {0, q+1, 2q+1, ..., (p'-1)q+1} mod p
    2. Show X has p' elements and E_{p/q}[X] ≃ E_{p'/q'}
    3. Show q ∉ X (so X ⊆ V \ {q})
    4. Define a retraction f: V \ {q} → X that preserves adjacency
    5. Conclude E_{p/q} - q ~ E_{p'/q'} (bidirectional homomorphisms)
    6. By vertex-transitivity, E_{p/q} - v ~ E_{p'/q'} for any v -/
theorem fractionGraph_remove_vertex_equiv (p q : ℕ) [hp : NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (v : ZMod p) :
    -- E_{p/q}[V \ {v}] ~ E_{p'/q'} (homomorphism equivalent)
    ∃ (p' q' : ℕ) (hp' : 0 < p') (_hq' : 0 < q'),
      p' < p ∧ q' < q ∧ p * q' - q * p' = 1 ∧
      haveI : NeZero p' := ⟨Nat.pos_iff_ne_zero.mp hp'⟩
      -- Bidirectional homomorphisms (graph equivalence)
      Cohom ((fractionGraph p q).induce {x : ZMod p | x ≠ v}) (fractionGraph p' q') ∧
      Cohom (fractionGraph p' q') ((fractionGraph p q).induce {x : ZMod p | x ≠ v}) := by
  -- Get p', q' from the Stern-Brocot predecessor
  have hp_pos : 0 < p := NeZero.pos p
  have hq_pos : 0 < q := by omega
  have hpq : q < p := Nat.lt_of_lt_of_le (by omega : q < 2 * q) h2q
  obtain ⟨p', q', hp'_pos, hp'_lt, hq'_pos, hq'_lt, hbezout⟩ :=
    sternBrocotPredecessor_exists p q hp_pos hq hcoprime hpq
  use p', q', hp'_pos, hq'_pos, hp'_lt, hq'_lt, hbezout
  haveI hp'_ne : NeZero p' := ⟨Nat.pos_iff_ne_zero.mp hp'_pos⟩
  -- Use the clean Lemma 6.6 from VertexRemoval.lean
  -- This gives us bidirectional K-adjacency preservation via the ceiling-based approach
  -- K-adjacency preservation implies cohomomorphism for fractionGraph (which is the complement)
  have hp_pos' : 0 < p := NeZero.pos p
  obtain ⟨f, g, hf_Kadj, hg_Kadj⟩ :=
    Lemma66.lemma_6_6 hp'_pos hp'_lt hp_pos' hq'_pos hq'_lt hq h2q hcoprime hbezout v
  constructor
  · -- Forward: E_{p/q}[V\{v}] → E_{p'/q'}
    -- Use f from Lemma 6.6
    let forwardMap : {x : ZMod p | x ≠ v} → ZMod p' := fun x => f x.val
    refine ⟨forwardMap, fun u w huw hnadj => ?_⟩
    -- Extract adjacency in base graph from induced adjacency
    have hnadj_base : ¬(fractionGraph p q).Adj u.val w.val := by
      simp only [SimpleGraph.induce_adj, Set.mem_setOf_eq, ne_eq] at hnadj
      exact fun hadj => hnadj hadj
    have hu_ne_v : u.val ≠ v := u.property
    have hw_ne_v : w.val ≠ v := w.property
    have huv_ne : u.val ≠ w.val := by
      intro heq
      exact huw (Subtype.val_injective heq)
    -- Non-adjacent in fractionGraph = adjacent in Kpq (complement)
    have hKpq_adj : (Lemma66.Kpq p q).Adj u.val w.val := by
      rw [Kpq_adj_iff_not_fractionGraph_adj u.val w.val huv_ne]
      exact hnadj_base
    -- f preserves Kpq adjacency
    have hf_adj := hf_Kadj u.val w.val hu_ne_v hw_ne_v hKpq_adj
    constructor
    · -- f u ≠ f w: Kpq-adjacency requires distinctness
      exact hf_adj.1
    · -- ¬fractionGraph.Adj (f u) (f w): Kpq-adjacency in target = non-adjacency in fractionGraph
      -- hf_adj : Kpq.Adj (f u.val) (f w.val)
      -- Need: ¬fractionGraph.Adj (f u.val) (f w.val)
      rw [← Kpq_adj_iff_not_fractionGraph_adj (f u.val) (f w.val) hf_adj.1]
      exact hf_adj
  · -- Backward: E_{p'/q'} → E_{p/q}[V\{v}]
    -- Use g from Lemma 6.6, which maps into {x | x ≠ v}
    -- First extract the property that g avoids v
    have hg_avoids_v : ∀ i : ZMod p', g i ≠ v := by
      intro i
      -- Find an adjacent pair involving i
      -- Since 2*q' ≤ p', every vertex i has a Kpq'-neighbor j = i + q'.
      -- From hg_Kadj applied to this adjacent pair, g i ≠ v.
      have hp'_ge2 : 2 ≤ p' := by
        -- p' ≥ 2 follows from the Bezout constraints
        by_contra hp'_lt2
        push_neg at hp'_lt2
        have hp'_eq_1 : p' = 1 := by omega
        -- If p' = 1, then p * q' - q = 1, so p * q' = q + 1
        rw [hp'_eq_1] at hbezout
        have hpq' : p * q' = q + 1 := by omega
        have hp_ge4 : p ≥ 4 := by omega
        -- From p * q' = q + 1 and p ≥ 4, q' ≤ (q+1)/4 < q (when q ≥ 2)
        have hq'_eq_1 : q' = 1 := by
          have : q' ≤ 1 := by
            have hle : p * q' ≤ p * 1 := by
              calc p * q' = q + 1 := hpq'
                _ ≤ q + q := by omega
                _ = 2 * q := by ring
                _ ≤ p := h2q
                _ = p * 1 := by ring
            exact Nat.le_of_mul_le_mul_left hle (by omega : 0 < p)
          omega
        have hp_eq : p = q + 1 := by
          rw [hq'_eq_1] at hpq'
          omega
        -- But p ≥ 2q and p = q + 1 gives q + 1 ≥ 2q, i.e., 1 ≥ q
        omega
      have hq'_lt_p' : q' < p' :=
        Lemma66.q'_lt_p'_of_bezout hp'_pos hp'_ge2 hq'_pos hq'_lt hq hpq hbezout
      -- Pick j = i + q'
      let j : ZMod p' := i + q'
      have hij : i ≠ j := by
        intro heq
        have : (q' : ZMod p') = 0 := by
          calc (q' : ZMod p') = (i + q') - i := by ring
            _ = j - i := rfl
            _ = i - i := by rw [← heq]
            _ = 0 := by ring
        have hdvd : p' ∣ q' := CharP.cast_eq_zero_iff (ZMod p') p' q' |>.mp this
        have : q' ≥ p' := Nat.le_of_dvd hq'_pos hdvd
        omega
      have hKpq'_adj : (Lemma66.Kpq p' q').Adj i j := by
        unfold Lemma66.Kpq
        constructor
        · exact hij
        · unfold Lemma66.circDist
          have hj_sub_i : (j - i).val = q' := by
            simp only [j]
            have : (i + q' - i : ZMod p') = q' := by ring
            rw [this]
            exact ZMod.val_natCast_of_lt hq'_lt_p'
          have h2q'_le_p' : 2 * q' ≤ p' :=
            Lemma66.two_q'_le_p'_of_bezout hp'_pos hp'_ge2 hq'_pos hq'_lt hq h2q hbezout
          have hi_sub_j : (i - j).val = p' - q' := by
            simp only [j]
            have heq : i - (i + ↑q') = (-(q' : ZMod p')) := by ring
            rw [heq]
            have hq'_ne_zero : (q' : ZMod p') ≠ 0 := by
              intro h
              have hdvd : p' ∣ q' := CharP.cast_eq_zero_iff (ZMod p') p' q' |>.mp h
              have : q' ≥ p' := Nat.le_of_dvd hq'_pos hdvd
              omega
            rw [ZMod.neg_val]
            simp only [hq'_ne_zero, ↓reduceIte]
            rw [ZMod.val_natCast_of_lt hq'_lt_p']
          simp only [hj_sub_i, hi_sub_j]
          exact Nat.le_min.mpr ⟨le_refl q', by omega⟩
      obtain ⟨_, hgi_ne_v, _⟩ := hg_Kadj i j hKpq'_adj
      exact hgi_ne_v
    let backwardMap : ZMod p' → {x : ZMod p | x ≠ v} := fun i => ⟨g i, hg_avoids_v i⟩
    refine ⟨backwardMap, fun u w huw hnadj => ?_⟩
    -- Non-adjacent in fractionGraph = adjacent in Kpq (complement)
    have hKpq_adj : (Lemma66.Kpq p' q').Adj u w := by
      rw [Kpq_adj_iff_not_fractionGraph_adj u w huw]
      exact hnadj
    -- g preserves Kpq adjacency
    obtain ⟨hg_adj, _, _⟩ := hg_Kadj u w hKpq_adj
    constructor
    · -- g u ≠ g w: Kpq-adjacency requires distinctness
      intro heq
      have h1 : (backwardMap u).val = (backwardMap w).val := congrArg Subtype.val heq
      simp only [backwardMap] at h1
      exact hg_adj.1 h1
    · -- ¬Adj in induced subgraph
      simp only [SimpleGraph.induce_adj, Set.mem_setOf_eq, ne_eq]
      intro hadj
      -- hadj : fractionGraph.Adj (g u) (g w)
      -- But hg_adj : Kpq.Adj (g u) (g w), which means ¬fractionGraph.Adj (g u) (g w)
      have hne : g u ≠ g w := hg_adj.1
      have hnadj_fg := (Kpq_adj_iff_not_fractionGraph_adj (g u) (g w) hne).mp hg_adj
      exact hnadj_fg hadj

/-! ### Spectral Bounds from Vertex Removal -/

/-- The Stern-Brocot successor e/f of a/b satisfies e*b - f*a = 1 and e/f > a/b.

    The successor is constructed using the multiplicative inverse: since gcd(a,b) = 1,
    the element b has a multiplicative inverse in ZMod a. Set e to be this inverse,
    then f = (e*b - 1)/a.

    This gives the sequence p_n = e + n*a, q_n = f + n*b that converges to a/b from above,
    with each p_n/q_n being a Stern-Brocot neighbor of a/b (p_n*b - q_n*a = 1). -/
theorem sternBrocotSuccessor_exists (a b : ℕ) (ha : 2 ≤ a) (hb : 0 < b)
    (hcoprime : Nat.Coprime a b) :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧ e * b - f * a = 1 ∧ (a : ℚ) / b < (e : ℚ) / f := by
  haveI hane : NeZero a := ⟨by omega⟩
  haveI : Fact (1 < a) := ⟨by omega⟩
  have ha_pos : 0 < a := by omega
  -- Define e as the multiplicative inverse of b mod a
  set e := ((b : ZMod a)⁻¹).val with he_def
  -- Since gcd(a,b) = gcd(b,a) = 1, b is a unit in ZMod a
  have hcoprime' : Nat.Coprime b a := hcoprime.symm
  -- Key property: b * e ≡ 1 (mod a) from ZMod.val_mul_inv
  have hmul : (b : ZMod a) * e = 1 := ZMod.mul_val_inv hcoprime'
  -- Convert to: (b * e) % a = 1
  have hbe_mod : (b * e) % a = 1 := by
    have h : ((b * e : ℕ) : ZMod a) = 1 := by simp only [Nat.cast_mul, hmul]
    have hval : ((b * e : ℕ) : ZMod a).val = (1 : ZMod a).val := congrArg ZMod.val h
    rw [ZMod.val_natCast] at hval
    have hone : (1 : ZMod a).val = 1 := ZMod.val_one (n := a)
    rw [hone] at hval
    exact hval
  -- e is positive since (b : ZMod a) is a unit (by coprimality)
  have he_pos : 0 < e := by
    by_contra he_zero
    push_neg at he_zero
    have he_eq : e = 0 := Nat.le_zero.mp he_zero
    have hcontra : (b : ZMod a) * e = 0 := by simp [he_eq]
    rw [hmul] at hcontra
    exact one_ne_zero hcontra
  -- e < a from ZMod.val_lt
  have he_lt : e < a := ZMod.val_lt _
  -- b * e ≥ 1
  have hbe_ge_1 : b * e ≥ 1 := Nat.mul_pos hb he_pos
  -- a ∣ (b * e - 1)
  have hdiv : a ∣ b * e - 1 := by
    have hone_lt_a : 1 < a := by omega
    have hone_mod : 1 % a = 1 := Nat.mod_eq_of_lt hone_lt_a
    rw [Nat.dvd_iff_mod_eq_zero]
    have : b * e % a = 1 % a := by rw [hbe_mod, hone_mod]
    exact Nat.sub_mod_eq_zero_of_mod_eq this
  -- Define f = (b * e - 1) / a
  set f := (b * e - 1) / a with hf_def
  -- When b ≥ 2, f = (b*e - 1)/a > 0 and e/f is the Stern-Brocot right successor of a/b.
  -- When b = 1, the formula gives f = 0, so we use (a+1)/1 directly instead.
  by_cases hb_eq_1 : b = 1
  · -- Case b = 1: Use e = a + 1, f = 1
    use a + 1, 1
    refine ⟨by omega, by omega, ?_, ?_⟩
    · -- (a + 1) * 1 - 1 * a = a + 1 - a = 1
      subst hb_eq_1
      simp only [mul_one, one_mul]
      omega
    · -- a / 1 < (a + 1) / 1
      simp only [hb_eq_1, Nat.cast_add, Nat.cast_one, div_one]
      have ha_pos' : (0 : ℚ) < a := Nat.cast_pos.mpr ha_pos
      linarith
  · -- Case b ≥ 2
    have hb_ge_2 : 2 ≤ b := by omega
    -- b * e ≥ 2 * 1 = 2 since b ≥ 2 and e ≥ 1
    have hbe_ge_2 : b * e ≥ 2 := by
      calc b * e ≥ 2 * 1 := Nat.mul_le_mul hb_ge_2 he_pos
        _ = 2 := by ring
    -- Since b * e ≡ 1 (mod a) and b * e ≥ 2, and 1 < a (since a ≥ 2),
    -- we have b * e ≠ 1, so b * e ≥ a + 1
    have hbe_gt_1 : b * e ≠ 1 := by omega
    have hbe_ge_a1 : b * e ≥ a + 1 := by
      -- b * e ≡ 1 (mod a) means b * e = k * a + 1 for some k ≥ 0
      -- Since b * e ≠ 1, we have k ≥ 1, so b * e ≥ a + 1
      have hmod := hbe_mod
      -- From (b * e) % a = 1, we have b * e = (b * e / a) * a + 1
      have hdiv_mod_orig := Nat.div_add_mod (b * e) a
      -- hdiv_mod_orig : a * (b * e / a) + b * e % a = b * e
      have hdiv_mod : b * e = (b * e) / a * a + (b * e) % a := by
        have : a * (b * e / a) = (b * e) / a * a := by ring
        rw [this] at hdiv_mod_orig
        omega
      rw [hmod] at hdiv_mod
      set k := (b * e) / a with hk_def
      -- b * e = k * a + 1
      have hbe_eq : b * e = k * a + 1 := hdiv_mod
      -- Since b * e ≥ 2 and 1 < a, we have k ≥ 1
      rcases Nat.eq_zero_or_pos k with hk_zero | hk_pos
      · -- k = 0 case: b * e = 1, contradiction
        rw [hk_zero] at hbe_eq
        simp at hbe_eq
        omega
      · -- k ≥ 1 case: b * e = k * a + 1 ≥ a + 1
        have : k * a ≥ a := Nat.le_mul_of_pos_left a hk_pos
        omega
    -- b * e - 1 ≥ a
    have hbe_sub_ge : b * e - 1 ≥ a := by omega
    -- f > 0
    have hf_pos : 0 < f := Nat.div_pos hbe_sub_ge ha_pos
    use e, f
    constructor
    · exact he_pos
    constructor
    · exact hf_pos
    constructor
    · -- e * b - f * a = 1
      -- From hdiv: a ∣ b * e - 1, so b * e - 1 = f * a
      have h3 : b * e - 1 = f * a := (Nat.div_mul_cancel hdiv).symm
      -- So e * b - f * a = 1
      have hmul_comm : e * b = b * e := Nat.mul_comm e b
      rw [hmul_comm]
      omega
    · -- a / b < e / f
      -- From e * b - f * a = 1: e * b = f * a + 1 > f * a
      -- So e / f > a / b
      have heq : e * b = f * a + 1 := by
        have h3 : b * e - 1 = f * a := (Nat.div_mul_cancel hdiv).symm
        have hmul_comm : e * b = b * e := Nat.mul_comm e b
        omega
      have hlt : a * f < e * b := by
        calc a * f = f * a := Nat.mul_comm a f
          _ < f * a + 1 := Nat.lt_succ_self _
          _ = e * b := heq.symm
      have hb_pos' : (0 : ℚ) < b := Nat.cast_pos.mpr hb
      have hf_pos' : (0 : ℚ) < f := Nat.cast_pos.mpr hf_pos
      rw [div_lt_div_iff₀ hb_pos' hf_pos']
      calc (a : ℚ) * f = ↑(a * f) := by push_cast; ring
        _ < ↑(e * b) := by exact_mod_cast hlt
        _ = e * b := by push_cast; ring

/-- p₂/q₂ < p/q when pq₂ - qp₂ = 1 (and p₂ < p, q₂ < q). -/
theorem sternBrocot_predecessor_lt (p q p₂ q₂ : ℕ)
    (_hp₂_lt : p₂ < p) (hq₂_lt : q₂ < q) (hq₂ : 0 < q₂)
    (heq : p * q₂ - q * p₂ = 1) :
    (p₂ : ℚ) / q₂ < (p : ℚ) / q := by
  -- Derive 0 < q from q₂ < q and 0 < q₂
  have hq : 0 < q := Nat.lt_trans hq₂ hq₂_lt
  -- pq₂ - qp₂ = 1 means pq₂ = qp₂ + 1
  have h : p * q₂ = q * p₂ + 1 := by omega
  -- p₂ * q = q * p₂ < q * p₂ + 1 = p * q₂
  have hlt : p₂ * q < p * q₂ := by
    calc p₂ * q = q * p₂ := Nat.mul_comm p₂ q
      _ < q * p₂ + 1 := Nat.lt_succ_self _
      _ = p * q₂ := h.symm
  rw [div_lt_div_iff₀ (by positivity : (0 : ℚ) < q₂) (by positivity : (0 : ℚ) < q)]
  calc (p₂ : ℚ) * q = ↑(p₂ * q) := by push_cast; ring
    _ < ↑(p * q₂) := by exact_mod_cast hlt
    _ = p * q₂ := by push_cast; ring

/-- Spectral value of fraction graph is bounded by number of vertices.
    This follows from: E_{p/q} ≤_G E_{p/1} (edgeless graph on p vertices),
    so φ(E_{p/q}) ≤ φ(E_{p/1}) = p by monotonicity and normalization. -/
theorem fractionGraph_spectral_le_vertices (p q : ℕ) [NeZero p]
    (hq : 0 < q) (φ : SpectralPoint) :
    φ.eval (FractionGraph' p q) ≤ p := by
  -- E_{p/q} has a cohomomorphism to E_{p/1} since p/q ≤ p/1 = p
  have h_ratio_le : (p : ℚ) / q ≤ (p : ℚ) / 1 := by
    rw [div_one]
    have hq_ge_1 : (1 : ℚ) ≤ q := by exact_mod_cast hq
    exact div_le_self (Nat.cast_nonneg p) hq_ge_1
  have h_cohom := fractionGraph_cohomomorphism p q p 1 hq h_ratio_le
  have h_mono := φ.mono_cohom (FractionGraph' p q) (FractionGraph' p 1) h_cohom
  -- E_{p/1} is the edgeless graph
  have h_edgeless : fractionGraph p 1 = ⊥ := fractionGraph_one_edgeless p
  -- φ(E_{p/1}) = p via isomorphism to EdgelessGraph p
  have h_eval_edgeless : φ.eval (FractionGraph' p 1) = p := by
    calc φ.eval (FractionGraph' p 1)
        = φ.eval { V := ZMod p, graph := ⊥ } := by
          change φ.eval { V := ZMod p, graph := fractionGraph p 1 } = _
          rw [h_edgeless]
      _ = φ.eval { V := Fin p, graph := ⊥ } := by
          exact (Universality.SpectralPoint.eval_iso φ (Universality.edgelessIsoZMod p)).symm
      _ = φ.eval (EdgelessGraph p) := rfl
      _ = p := φ.normalized p
  linarith

/-- Lemma 2.15: For vertex-transitive graphs, the spectral value is bounded
    by the ratio |V|/|S| times the spectral value of the induced subgraph.

    For fraction graphs: E_{p/q} has p vertices, and removing one vertex gives p-1 vertices,
    so the ratio is p/(p-1).

    Proof strategy:
    1. Use spectral_vertexTransitive_upper to get bound with induced subgraph
    2. Use fractionGraph_remove_vertex_equiv to identify induced subgraph with E_{p'/q'}
    3. Use sternBrocotPredecessor_unique to match the given p', q' with those from removal
    4. Use eval_iso to transfer the spectral evaluation -/
theorem spectral_transitive_bound_fractionGraph (p q p' q' : ℕ) [NeZero p] [NeZero p']
    (hq : 0 < q) (hq' : 0 < q') (h2q : 2 * q ≤ p) (_h2q' : 2 * q' ≤ p')
    (hp'_lt : p' < p) (hq'_lt : q' < q)
    (heq : p * q' - q * p' = 1)
    (φ : SpectralPoint) :
    φ.eval (FractionGraph' p q) ≤ (p : ℝ) / (p - 1) * φ.eval (FractionGraph' p' q') := by
  -- Step 1: Derive coprimality from the Stern-Brocot equation
  -- From p * q' - q * p' = 1, any common factor of p and q must divide 1
  have hcoprime : Nat.Coprime p q := by
    rw [Nat.Coprime]
    by_contra h
    have hgcd_gt : 1 < p.gcd q := by
      have hgcd_pos : 0 < p.gcd q := Nat.gcd_pos_of_pos_left q (NeZero.pos p)
      omega
    have hdiv_p : p.gcd q ∣ p := Nat.gcd_dvd_left p q
    have hdiv_q : p.gcd q ∣ q := Nat.gcd_dvd_right p q
    have hdiv : p.gcd q ∣ p * q' - q * p' := by
      have hdiv1 : p.gcd q ∣ p * q' := Nat.dvd_trans hdiv_p (dvd_mul_right p q')
      have hdiv2 : p.gcd q ∣ q * p' := Nat.dvd_trans hdiv_q (dvd_mul_right q p')
      exact Nat.dvd_sub hdiv1 hdiv2
    rw [heq] at hdiv
    have : p.gcd q ≤ 1 := Nat.le_of_dvd Nat.one_pos hdiv
    omega
  -- Step 2: p > 1 follows from p' < p and p' > 0
  have hp_gt_1 : 1 < p := by
    have hp'_pos : 0 < p' := NeZero.pos p'
    omega
  -- Step 3: Use the vertex-transitive upper bound from CoveringLemma
  -- Set up the induced subgraph S = {x : ZMod p | x ≠ 0}
  set G := FractionGraph' p q with hG_def
  set S : Set (ZMod p) := {x | x ≠ 0} with hS_def
  -- S is nonempty since p > 1
  have hS_nonempty : S.Nonempty := by
    use 1
    intro h
    have hdvd : p ∣ 1 := by rw [← ZMod.natCast_eq_zero_iff]; simpa using h
    have : p ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd
    omega
  -- Fraction graphs are vertex-transitive
  have hT : ProbabilisticRefinement.IsVertexTransitive G.graph :=
    FractionGraphBasic.fractionGraph_vertexTransitive p q
  -- Fintype.card S = p - 1
  have hcard_S : Fintype.card S = p - 1 := by
    have : Fintype.card S = (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).card := by
      rw [Fintype.card_subtype]; rfl
    rw [this, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp only [Finset.card_univ, ZMod.card]
  have hcard_pos : 0 < Fintype.card S := by rw [hcard_S]; omega
  have hcard_V : Fintype.card G.V = p := ZMod.card p
  -- Apply spectral_vertexTransitive_upper
  -- v4.29: instance synthesis is stricter; specify all Fintype instances explicitly so the
  -- subsequent `rw` of `hcard_V`/`hcard_S` can find matching subterms.
  have h_upper : φ.eval G ≤
      (Fintype.card G.V : ℝ) / @Fintype.card ↑S (Subtype.fintype (Membership.mem S)) *
        φ.eval (@inducedGraph G.V G.graph S G.fintype G.deceq
                  (Subtype.fintype (Membership.mem S))) :=
    @spectral_vertexTransitive_upper G S (Subtype.fintype (Membership.mem S))
      hS_nonempty hT hcard_pos φ
  rw [hcard_V, hcard_S] at h_upper
  -- Convert (p - 1 : ℕ) to (p : ℝ) - 1
  have hconv : (p : ℝ) / (p - 1 : ℕ) = (p : ℝ) / ((p : ℝ) - 1) := by
    congr 1
    have hp_ge_1 : 1 ≤ p := by omega
    simp only [Nat.cast_sub hp_ge_1, Nat.cast_one]
  rw [hconv] at h_upper
  -- Step 4: Use fractionGraph_remove_vertex_equiv to identify induced subgraph with E_{p₁/q₁}
  -- From hq'_lt : q' < q and hq' : 0 < q', we get q ≥ 2
  have hq2 : 2 ≤ q := by omega
  have h_remove := fractionGraph_remove_vertex_equiv p q hq2 h2q hcoprime (0 : ZMod p)
  obtain ⟨p₁, q₁, hp₁_pos, hq₁_pos, hp₁_lt, hq₁_lt, heq₁, hcohom_fwd, hcohom_bwd⟩ := h_remove
  -- Step 5: Use uniqueness to show p₁ = p' and q₁ = q'
  have huniq := sternBrocotPredecessor_unique p q p₁ q₁ p' q' hcoprime
    hp₁_pos hp₁_lt hq₁_pos hq₁_lt (NeZero.pos p') hp'_lt hq' hq'_lt heq₁ heq
  obtain ⟨hp_eq, hq_eq⟩ := huniq
  -- Step 6: The induced subgraph is equivalent to E_{p'/q'} (bidirectional cohoms)
  haveI : NeZero p₁ := ⟨Nat.pos_iff_ne_zero.mp hp₁_pos⟩
  -- Use bidirectional cohomomorphisms to get spectral equality
  -- φ.eval (induced) ≤ φ.eval (E_{p₁/q₁}) by hcohom_fwd
  -- φ.eval (E_{p₁/q₁}) ≤ φ.eval (induced) by hcohom_bwd
  have h_eval_eq : φ.eval (inducedGraph (fractionGraph p q) S) =
      φ.eval (FractionGraph' p₁ q₁) := by
    apply le_antisymm
    · exact φ.mono_cohom (inducedGraph (fractionGraph p q) S) (FractionGraph' p₁ q₁) hcohom_fwd
    · exact φ.mono_cohom (FractionGraph' p₁ q₁) (inducedGraph (fractionGraph p q) S) hcohom_bwd
  -- Substitute p₁ = p' and q₁ = q' into the goal
  -- Since hp_eq : p₁ = p' and hq_eq : q₁ = q', we have
  -- FractionGraph' p₁ q₁ = FractionGraph' p' q'
  have h_graph_eq : FractionGraph' p₁ q₁ = FractionGraph' p' q' := by
    simp only [hp_eq, hq_eq]
  rw [h_graph_eq] at h_eval_eq
  -- Now h_eval_eq : φ.eval (inducedGraph (fractionGraph p q) S) = φ.eval (FractionGraph' p' q')
  -- h_upper : φ.eval G ≤ (p : ℝ) / (p - 1) * φ.eval (inducedGraph G.graph S)
  -- G = FractionGraph' p q, and G.graph = fractionGraph p q
  -- So inducedGraph G.graph S = inducedGraph (fractionGraph p q) S
  have h_induced_eq :
      @inducedGraph G.V G.graph S G.fintype G.deceq (Subtype.fintype (Membership.mem S)) =
        inducedGraph (fractionGraph p q) S := rfl
  rw [h_induced_eq, h_eval_eq] at h_upper
  exact h_upper

/-- Theorem 3.6: For F ∈ X ∪ {α, Θ} and fraction graphs with pq₂ - qp₂ = 1:
    F(E_{p₂/q₂}) ≤ F(E_{p/q}) ≤ (p/(p-1)) · F(E_{p₂/q₂})

    This follows from:
    1. E_{p₂/q₂} ≤ E_{p/q} (induced subgraph)
    2. E_{p/q} is vertex-transitive with |V|/|S| = p/(p-1)
    3. Vrana's bound for vertex-transitive graphs -/
theorem fractionGraph_spectral_bounds (p q p₂ q₂ : ℕ) [NeZero p] [NeZero p₂]
    (hq : 0 < q) (hq₂ : 0 < q₂) (h2q : 2 * q ≤ p) (h2q₂ : 2 * q₂ ≤ p₂)
    (hp₂_lt : p₂ < p) (hq₂_lt : q₂ < q)
    (heq : p * q₂ - q * p₂ = 1)
    (φ : SpectralPoint) :
    φ.eval (FractionGraph' p₂ q₂) ≤ φ.eval (FractionGraph' p q) ∧
    φ.eval (FractionGraph' p q) ≤ (p : ℝ) / (p - 1) *
      φ.eval (FractionGraph' p₂ q₂) := by
  constructor
  · -- Lower bound: E_{p₂/q₂} ≤ E_{p/q} under cohomomorphism
    apply φ.mono_cohom
    -- Need: E_{p₂/q₂} ≤_G E_{p/q}
    -- This follows from p₂/q₂ < p/q and the ordering theorem
    have hlt := sternBrocot_predecessor_lt p q p₂ q₂ hp₂_lt hq₂_lt hq₂ heq
    have hle : (p₂ : ℚ) / q₂ ≤ (p : ℚ) / q := le_of_lt hlt
    exact (fractionGraph_ordering p₂ q₂ p q hq₂ hq h2q₂ h2q).mp hle
  · -- Upper bound: Uses vertex transitivity and Vrana's bound
    -- E_{p/q} is vertex-transitive, removing a vertex gives E_{p₂/q₂}
    -- By Lemma 2.15: F(E_{p/q}) ≤ (p/(p-1)) F(E_{p₂/q₂})
    exact spectral_transitive_bound_fractionGraph p q p₂ q₂ hq hq₂ h2q h2q₂ hp₂_lt hq₂_lt heq φ

/-- Corollary: Distance bound between consecutive Stern-Brocot fractions. -/
theorem fractionGraph_distance_bound (p q p₂ q₂ : ℕ) [NeZero p] [NeZero p₂]
    (hq : 0 < q) (hq₂ : 0 < q₂) (h2q : 2 * q ≤ p) (h2q₂ : 2 * q₂ ≤ p₂)
    (hp₂_lt : p₂ < p) (hq₂_lt : q₂ < q)
    (heq : p * q₂ - q * p₂ = 1) :
    asympSpecDistance (FractionGraph' p q) (FractionGraph' p₂ q₂) ≤
      (p₂ : ℝ) / (p - 1) := by
  -- From the spectral bounds:
  -- 0 ≤ F(E_{p/q}) - F(E_{p₂/q₂}) ≤ (1/(p-1)) F(E_{p₂/q₂}) ≤ p₂/(p-1)
  simp only [asympSpecDistance, spectralDistanceSet]
  apply csSup_le
  · -- Nonemptiness
    obtain ⟨φ₀⟩ := spectralPoint_nonempty
    exact ⟨|φ₀.eval (FractionGraph' p q) - φ₀.eval (FractionGraph' p₂ q₂)|, φ₀, rfl⟩
  · -- Upper bound for each spectral point
    intro x ⟨φ, hφ⟩
    rw [hφ]
    -- Get bounds from fractionGraph_spectral_bounds
    have ⟨hlo, hhi⟩ := fractionGraph_spectral_bounds p q p₂ q₂ hq hq₂ h2q h2q₂ hp₂_lt hq₂_lt heq φ
    -- Since φ(E_{p₂/q₂}) ≤ φ(E_{p/q}), the difference is non-negative
    have hdiff_nonneg : 0 ≤ φ.eval (FractionGraph' p q) -
        φ.eval (FractionGraph' p₂ q₂) := by linarith
    rw [abs_of_nonneg hdiff_nonneg]
    -- From hhi: φ(E_{p/q}) ≤ (p/(p-1)) * φ(E_{p₂/q₂})
    -- So: φ(E_{p/q}) - φ(E_{p₂/q₂}) ≤ (p/(p-1) - 1) * φ(E_{p₂/q₂}) = (1/(p-1)) * φ(E_{p₂/q₂})
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
    have hp1_pos : (0 : ℝ) < p - 1 := by
      have hp₂_pos : 0 < p₂ := NeZero.pos p₂
      have hp_ge_2 : 2 ≤ p := by omega
      have : (1 : ℝ) < p := by exact_mod_cast hp_ge_2
      linarith
    have hdiff_bound : φ.eval (FractionGraph' p q) - φ.eval (FractionGraph' p₂ q₂) ≤
        (1 : ℝ) / (p - 1) * φ.eval (FractionGraph' p₂ q₂) := by
      have : (p : ℝ) / (p - 1) - 1 = 1 / (p - 1) := by field_simp; ring
      calc φ.eval (FractionGraph' p q) - φ.eval (FractionGraph' p₂ q₂)
          ≤ (p : ℝ) / (p - 1) * φ.eval (FractionGraph' p₂ q₂) -
            φ.eval (FractionGraph' p₂ q₂) := by linarith
        _ = ((p : ℝ) / (p - 1) - 1) * φ.eval (FractionGraph' p₂ q₂) := by ring
        _ = (1 : ℝ) / (p - 1) * φ.eval (FractionGraph' p₂ q₂) := by rw [this]
    -- Now bound φ(E_{p₂/q₂}) ≤ p₂ using cohomomorphism to edgeless graph
    have heval_bound : φ.eval (FractionGraph' p₂ q₂) ≤ p₂ := by
      -- E_{p₂/q₂} has cohomomorphism to EdgelessGraph p₂
      -- by monotonicity: φ(E_{p₂/q₂}) ≤ φ(EdgelessGraph p₂) = p₂
      exact fractionGraph_spectral_le_vertices p₂ q₂ hq₂ φ
    calc φ.eval (FractionGraph' p q) - φ.eval (FractionGraph' p₂ q₂)
        ≤ (1 : ℝ) / (p - 1) * φ.eval (FractionGraph' p₂ q₂) := hdiff_bound
      _ ≤ (1 : ℝ) / (p - 1) * p₂ := by
          apply mul_le_mul_of_nonneg_left heval_bound
          exact le_of_lt (one_div_pos.mpr hp1_pos)
      _ = (p₂ : ℝ) / (p - 1) := by ring

/-! ### Fraction Graph Independence Number -/

/-- The independence number of E_{p/q} is ⌊p/q⌋.

    Proof: The set {0, q, 2q, ..., (p/q - 1)*q} is independent (elements are q apart),
    giving the lower bound. The upper bound uses the fractional clique cover. -/
theorem fractionGraph_independenceNumber (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    (fractionGraph p q).indepNum = p / q := by
  apply le_antisymm
  · -- Upper bound: α ≤ p/q using fractional clique cover
    obtain ⟨cliques, weights, hcliq, hpos, hcover, hweight⟩ := fractionGraph_chiBar_f p q hq h2q
    have hbound := SimpleGraph.independenceNumber_le_of_clique_cover
      (fractionGraph p q) cliques weights hcliq hpos hcover
    have hle : ((fractionGraph p q).indepNum : ℝ) ≤ (p : ℝ) / q :=
      le_trans (hbound ((p : ℝ) / q) hweight) (le_refl _)
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    rw [Nat.le_div_iff_mul_le hq]
    have hle' : ((fractionGraph p q).indepNum : ℝ) * q ≤ p := by
      calc ((fractionGraph p q).indepNum : ℝ) * q
          ≤ ((p : ℝ) / q) * q := by apply mul_le_mul_of_nonneg_right hle (le_of_lt hq_pos)
        _ = p := by field_simp
    exact_mod_cast hle'
  · -- Lower bound: α ≥ p/q by constructing explicit independent set {0, q, 2q, ...}
    let m := p / q
    have hm_bound : m * q ≤ p := Nat.div_mul_le_self p q
    have hq_le_p : q ≤ p := le_trans (Nat.le_mul_of_pos_left q (by omega : 0 < 2)) h2q
    have hm_ge_1 : m ≥ 1 := (Nat.one_le_div_iff hq).mpr hq_le_p
    -- Define the set {0, q, 2q, ..., (m-1)*q} as elements of ZMod p
    -- Use explicit Nat.cast to ensure Nat multiplication, not ZMod multiplication
    let S : Finset (ZMod p) := Finset.image
      (fun k : Fin m => (Nat.cast (k.val * q) : ZMod p)) Finset.univ
    have hS_card : S.card = m := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_fin m
      · intro k₁ k₂ heq
        have hk₁q_lt : k₁.val * q < p := Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_pos_right k₁.isLt hq) hm_bound
        have hk₂q_lt : k₂.val * q < p := Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_pos_right k₂.isLt hq) hm_bound
        -- If (k₁*q : ZMod p) = (k₂*q : ZMod p), and both k_i*q < p, they're equal as ℕ
        have h1 : (Nat.cast (k₁.val * q) : ZMod p).val = k₁.val * q :=
          ZMod.val_natCast_of_lt hk₁q_lt
        have h2 : (Nat.cast (k₂.val * q) : ZMod p).val = k₂.val * q :=
          ZMod.val_natCast_of_lt hk₂q_lt
        have heq_nat : k₁.val * q = k₂.val * q := by
          have heq' : (Nat.cast (k₁.val * q) : ZMod p).val =
              (Nat.cast (k₂.val * q) : ZMod p).val := congrArg ZMod.val heq
          rw [h1, h2] at heq'
          exact heq'
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right hq heq_nat)
    have hS_indep : (fractionGraph p q).IsIndepSet (S : Set (ZMod p)) := by
      apply (SimpleGraph.isIndepSet_iff _).2
      intro u hu v hv huv
      have hu' : u ∈ S := by simpa using hu
      have hv' : v ∈ S := by simpa using hv
      simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hu' hv'
      obtain ⟨ku, rfl⟩ := hu'
      obtain ⟨kv, rfl⟩ := hv'
      simp only [fractionGraph, ne_eq]
      intro ⟨hne, hdist⟩
      have hku_ne_kv : ku ≠ kv := by
        intro heq
        apply huv
        simp only [heq]
      have hne_val : ku.val ≠ kv.val := fun h => hku_ne_kv (Fin.ext h)
      -- Key bounds
      have hku_q_lt : ku.val * q < p := Nat.lt_of_lt_of_le
        (Nat.mul_lt_mul_of_pos_right ku.isLt hq) hm_bound
      have hkv_q_lt : kv.val * q < p := Nat.lt_of_lt_of_le
        (Nat.mul_lt_mul_of_pos_right kv.isLt hq) hm_bound
      -- Simplify hdist
      have hval_ku : (Nat.cast (ku.val * q) : ZMod p).val = ku.val * q :=
        ZMod.val_natCast_of_lt hku_q_lt
      have hval_kv : (Nat.cast (kv.val * q) : ZMod p).val = kv.val * q :=
        ZMod.val_natCast_of_lt hkv_q_lt
      -- Use symmetry WLOG: consider ku > kv case (symmetric)
      by_cases hlt : ku.val < kv.val
      · -- ku < kv case: use symmetry of distMod
        have hdiff_ge : kv.val - ku.val ≥ 1 := by
          exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hlt)
        have hdiff_lt_m : kv.val - ku.val < m := by
          have : kv.val - ku.val ≤ kv.val := Nat.sub_le _ _
          omega
        have hdiff_q_lt : (kv.val - ku.val) * q < p := Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_pos_right hdiff_lt_m hq) hm_bound
        -- Use symmetry: (kv*q - ku*q).val = (kv - ku)*q
        have hkv_ge_ku : (Nat.cast (ku.val * q) : ZMod p).val ≤
            (Nat.cast (kv.val * q) : ZMod p).val := by
          rw [hval_ku, hval_kv]
          exact Nat.mul_le_mul_right q (le_of_lt hlt)
        have hval_sub_rev : ((Nat.cast (kv.val * q) : ZMod p) -
            (Nat.cast (ku.val * q) : ZMod p)).val = (kv.val - ku.val) * q := by
          rw [ZMod.val_sub hkv_ge_ku, hval_kv, hval_ku, Nat.sub_mul]
        -- distMod is symmetric, apply before unfolding
        rw [FractionGraphBasic.distMod_comm] at hdist
        unfold FractionGraphBasic.distMod at hdist
        rw [hval_sub_rev] at hdist
        -- Now hdist says: min ((kv - ku)*q) (p - (kv - ku)*q) < q
        -- But (kv - ku)*q ≥ q and p - (kv - ku)*q ≥ q
        have hge_q : (kv.val - ku.val) * q ≥ q := Nat.le_mul_of_pos_left q hdiff_ge
        have hdiff_le_m1 : kv.val - ku.val ≤ m - 1 := by omega
        have hp_sub_ge : p - (kv.val - ku.val) * q ≥ q := by
          have hbound' : (kv.val - ku.val) * q ≤ (m - 1) * q := Nat.mul_le_mul_right q hdiff_le_m1
          have hm1_eq : (m - 1) * q = m * q - q := by rw [Nat.sub_mul, Nat.one_mul]
          omega
        have hmin_ge : min ((kv.val - ku.val) * q) (p - (kv.val - ku.val) * q) ≥ q :=
          le_min hge_q hp_sub_ge
        exact absurd hdist (not_lt.mpr hmin_ge)
      · -- ku ≥ kv case (and ku ≠ kv, so ku > kv)
        push_neg at hlt
        have hgt : ku.val > kv.val := Nat.lt_of_le_of_ne hlt (Ne.symm hne_val)
        have hdiff_ge : ku.val - kv.val ≥ 1 := by
          exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hgt)
        have hdiff_lt_m : ku.val - kv.val < m := by
          have : ku.val - kv.val ≤ ku.val := Nat.sub_le _ _
          omega
        have hdiff_q_lt : (ku.val - kv.val) * q < p := Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_pos_right hdiff_lt_m hq) hm_bound
        -- (ku*q - kv*q).val = (ku - kv)*q when ku > kv
        have hku_ge_kv : (Nat.cast (kv.val * q) : ZMod p).val ≤
            (Nat.cast (ku.val * q) : ZMod p).val := by
          rw [hval_kv, hval_ku]
          exact Nat.mul_le_mul_right q (le_of_lt hgt)
        have hval_sub : ((Nat.cast (ku.val * q) : ZMod p) -
            (Nat.cast (kv.val * q) : ZMod p)).val = (ku.val - kv.val) * q := by
          rw [ZMod.val_sub hku_ge_kv, hval_ku, hval_kv, Nat.sub_mul]
        unfold FractionGraphBasic.distMod at hdist
        rw [hval_sub] at hdist
        have hge_q : (ku.val - kv.val) * q ≥ q := Nat.le_mul_of_pos_left q hdiff_ge
        have hdiff_le_m1 : ku.val - kv.val ≤ m - 1 := by omega
        have hp_sub_ge : p - (ku.val - kv.val) * q ≥ q := by
          have hbound' : (ku.val - kv.val) * q ≤ (m - 1) * q := Nat.mul_le_mul_right q hdiff_le_m1
          have hm1_eq : (m - 1) * q = m * q - q := by rw [Nat.sub_mul, Nat.one_mul]
          omega
        have hmin_ge : min ((ku.val - kv.val) * q) (p - (ku.val - kv.val) * q) ≥ q :=
          le_min hge_q hp_sub_ge
        exact absurd hdist (not_lt.mpr hmin_ge)
    calc (fractionGraph p q).indepNum
        ≥ S.card := SimpleGraph.IsIndepSet.card_le_indepNum hS_indep
      _ = m := hS_card

/-! ### α version of Theorem 3.6 (Stern–Brocot neighbour invariance of ⌊p/q⌋)

For Stern–Brocot neighbours `p₂/q₂ < p/q` with `p·q₂ − q·p₂ = 1`, the integer
floor `⌊p/q⌋` is invariant: `⌊p/q⌋ = ⌊p₂/q₂⌋`. Combined with
`fractionGraph_independenceNumber`, this proves the α version of Theorem 3.6. -/

/-- Stern–Brocot neighbours `p₂/q₂ < p/q` satisfying `p·q₂ − q·p₂ = 1`,
    `2q ≤ p`, `2q₂ ≤ p₂`, and `q₂ < q`, have the same integer floor:
    `⌊p/q⌋ = ⌊p₂/q₂⌋` (as natural numbers, where `/` denotes `Nat.div`).

    Proof: the Stern–Brocot relation gives `p/q − p₂/q₂ = 1/(q·q₂) < 1`,
    so the floors differ by at most 1. If they differed by exactly 1 we
    would need `p₂` very close to an integer multiple of `q₂` and `q ≤ 1`,
    contradicting `q ≥ q₂ + 1 ≥ 2`. -/
theorem fractionGraph_floor_eq_of_sternBrocot
    (p q p₂ q₂ : ℕ) (hq : 0 < q) (hq₂ : 0 < q₂)
    (hq₂_lt : q₂ < q) (heq : p * q₂ - q * p₂ = 1) :
    p / q = p₂ / q₂ := by
  -- From `heq` (Nat subtraction), `q * p₂ ≤ p * q₂` and
  -- `p * q₂ = q * p₂ + 1`.
  have hle : q * p₂ ≤ p * q₂ := by
    by_contra hgt
    push_neg at hgt
    have : p * q₂ - q * p₂ = 0 := Nat.sub_eq_zero_of_le (le_of_lt hgt)
    omega
  have hpq₂ : p * q₂ = q * p₂ + 1 := by omega
  -- `q ≥ 2`: from `q₂ ≥ 1` and `q₂ < q`.
  have hq_ge_2 : 2 ≤ q := by omega
  -- Let `m = p₂ / q₂`, so `m * q₂ ≤ p₂ < (m+1) * q₂`.
  set m := p₂ / q₂ with hm_def
  have hm_lo : m * q₂ ≤ p₂ := Nat.div_mul_le_self p₂ q₂
  have hm_hi : p₂ < (m + 1) * q₂ := by
    have h := Nat.lt_div_mul_add (a := p₂) hq₂
    -- h : p₂ < p₂ / q₂ * q₂ + q₂
    have heq' : (m + 1) * q₂ = p₂ / q₂ * q₂ + q₂ := by
      rw [hm_def]; ring
    rw [heq']
    exact h
  -- Lower bound: m ≤ p / q. From m * q₂ ≤ p₂,
  -- multiply by q: m * q * q₂ ≤ q * p₂ = p * q₂ - 1 < p * q₂.
  -- Cancel q₂: m * q < p, hence m * q ≤ p, so m ≤ p / q.
  have hmq_lt : m * q < p := by
    have h1 : m * q * q₂ < p * q₂ := by
      calc m * q * q₂ = q * (m * q₂) := by ring
        _ ≤ q * p₂ := Nat.mul_le_mul_left q hm_lo
        _ < q * p₂ + 1 := Nat.lt_succ_self _
        _ = p * q₂ := hpq₂.symm
    exact Nat.lt_of_mul_lt_mul_right h1
  have hm_le : m ≤ p / q :=
    (Nat.le_div_iff_mul_le hq).mpr (Nat.le_of_lt hmq_lt)
  -- Upper bound: p / q ≤ m. From p₂ < (m+1) * q₂,
  -- so p₂ + 1 ≤ (m+1) * q₂. Multiply by q: q*p₂ + q ≤ q*(m+1)*q₂.
  -- Use q*p₂ = p*q₂ - 1: p*q₂ - 1 + q ≤ q*(m+1)*q₂, so p*q₂ + q - 1 ≤ q*(m+1)*q₂.
  -- Since q ≥ 2, q - 1 ≥ 1 > 0, so p*q₂ < q*(m+1)*q₂.
  -- Cancel q₂: p < q*(m+1), so p/q ≤ m.
  have hp_lt : p < q * (m + 1) := by
    have h1 : p₂ + 1 ≤ (m + 1) * q₂ := hm_hi
    have h2 : q * (p₂ + 1) ≤ q * ((m + 1) * q₂) := Nat.mul_le_mul_left q h1
    have h3 : q * p₂ + q ≤ q * (m + 1) * q₂ := by
      have hreassoc : q * ((m + 1) * q₂) = q * (m + 1) * q₂ := by ring
      have : q * (p₂ + 1) = q * p₂ + q := by ring
      omega
    -- p * q₂ + q - 1 = q * p₂ + q ≤ q*(m+1)*q₂, so p*q₂ < q*(m+1)*q₂
    have h4 : p * q₂ < q * (m + 1) * q₂ := by omega
    exact Nat.lt_of_mul_lt_mul_right h4
  have hp_div_le : p / q ≤ m := by
    have hp_lt' : p < (m + 1) * q := by
      have : q * (m + 1) = (m + 1) * q := by ring
      omega
    have := (Nat.div_lt_iff_lt_mul hq).mpr hp_lt'
    omega
  exact le_antisymm hp_div_le hm_le

/-- α version of Theorem 3.6 (`th:vrm`): for Stern–Brocot neighbours
    `p₂/q₂ < p/q` with `p·q₂ − q·p₂ = 1` and `2q ≤ p`, `2q₂ ≤ p₂`,
    the independence numbers are equal:
    `α(E_{p₂/q₂}) = α(E_{p/q})`.

    This is the α-analogue of `fractionGraph_spectral_bounds`. Combined with
    `fractionGraph_independenceNumber`, both inequalities of Theorem 3.6
    reduce to this equality. -/
theorem fractionGraph_indepNum_eq_of_sternBrocot
    (p q p₂ q₂ : ℕ) [NeZero p] [NeZero p₂]
    (hq : 0 < q) (hq₂ : 0 < q₂) (h2q : 2 * q ≤ p) (h2q₂ : 2 * q₂ ≤ p₂)
    (hq₂_lt : q₂ < q) (heq : p * q₂ - q * p₂ = 1) :
    (fractionGraph p q).indepNum = (fractionGraph p₂ q₂).indepNum := by
  rw [fractionGraph_independenceNumber p q hq h2q,
      fractionGraph_independenceNumber p₂ q₂ hq₂ h2q₂]
  exact fractionGraph_floor_eq_of_sternBrocot p q p₂ q₂ hq hq₂ hq₂_lt heq

/-! ### Theorem 3.6 wrappers (paper-facing `ℕ+` form)

The following theorems package `fractionGraph_spectral_bounds` (and its α / Θ
analogues) using `ℕ+` arguments and the bundled `FractionGraph p q`, matching
the form used in `Main.lean`. -/

/-- Proof of `main_vertex_removal_bounds`: Theorem 3.6 wrapper for `ℕ+`
    arguments. Derives the redundant `h2q : 2*q ≤ p` and `hp₂_lt : p₂ < p`
    from `h2q₂`, `hq₂_lt`, and `heq` internally. -/
theorem vertex_removal_bounds (p q p₂ q₂ : ℕ+)
    (h2q₂ : 2 * q₂ ≤ p₂) (hq₂_lt : q₂ < q)
    (heq : (p : ℕ) * q₂ - q * p₂ = 1)
    (φ : SpectralPoint) :
    φ (FractionGraph p₂ q₂) ≤ φ (FractionGraph p q) ∧
    φ (FractionGraph p q) ≤ (p : ℝ) / (p - 1) *
      φ (FractionGraph p₂ q₂) := by
  -- Derive `h2q : 2*q ≤ p` and `hp₂_lt : p₂ < p` from `h2q₂`, `hq₂_lt`, `heq`:
  -- from `heq` we have `p*q₂ ≥ q*p₂ + 1 ≥ q*(2*q₂) + 1 = 2*q*q₂ + 1`,
  -- so `p > 2*q`. Similarly `p₂ < p` since `p ≤ p₂` would give `p*q₂ ≤ p₂*q`.
  have h2q₂_nat : 2 * (q₂ : ℕ) ≤ (p₂ : ℕ) := by exact_mod_cast h2q₂
  have hq₂_lt_nat : (q₂ : ℕ) < (q : ℕ) := by exact_mod_cast hq₂_lt
  have hq₂_pos : 0 < (q₂ : ℕ) := q₂.pos
  have hp₂_pos : 0 < (p₂ : ℕ) := p₂.pos
  -- Convert `heq` (using ℕ subtraction) to the additive form `p*q₂ = q*p₂ + 1`.
  have hpq₂_eq : (p : ℕ) * (q₂ : ℕ) = (q : ℕ) * (p₂ : ℕ) + 1 := by
    have hge : (q : ℕ) * (p₂ : ℕ) ≤ (p : ℕ) * (q₂ : ℕ) := by
      by_contra hlt
      push_neg at hlt
      have : (p : ℕ) * (q₂ : ℕ) - (q : ℕ) * (p₂ : ℕ) = 0 :=
        Nat.sub_eq_zero_of_le hlt.le
      omega
    omega
  have h2q : 2 * q ≤ p := by
    have hkey : 2 * (q : ℕ) * (q₂ : ℕ) + 1 ≤ (p : ℕ) * (q₂ : ℕ) := by
      have h1 : (q : ℕ) * (2 * (q₂ : ℕ)) ≤ (q : ℕ) * (p₂ : ℕ) :=
        Nat.mul_le_mul_left _ h2q₂_nat
      nlinarith [hpq₂_eq]
    have hp_ge : 2 * (q : ℕ) < (p : ℕ) := by
      have hlt' : 2 * (q : ℕ) * (q₂ : ℕ) < (p : ℕ) * (q₂ : ℕ) := by omega
      exact Nat.lt_of_mul_lt_mul_right hlt'
    exact_mod_cast hp_ge.le
  have hp₂_lt : p₂ < p := by
    have hp₂_lt_nat : (p₂ : ℕ) < (p : ℕ) := by
      by_contra hle
      push_neg at hle
      have h1 : (p : ℕ) * (q₂ : ℕ) ≤ (p₂ : ℕ) * (q₂ : ℕ) :=
        Nat.mul_le_mul_right _ hle
      have h2 : (p₂ : ℕ) * (q₂ : ℕ) < (p₂ : ℕ) * (q : ℕ) :=
        (Nat.mul_lt_mul_left hp₂_pos).mpr hq₂_lt_nat
      nlinarith [hpq₂_eq]
    exact_mod_cast hp₂_lt_nat
  exact fractionGraph_spectral_bounds (p : ℕ) q p₂ q₂ q.pos q₂.pos h2q h2q₂
    hp₂_lt hq₂_lt heq φ

/-- Proof of `main_vertex_removal_bounds_alpha`: α-analogue of Theorem 3.6
    for Stern–Brocot–neighbour fraction graphs. Both inequalities follow from
    the equality `α(E_{p/q}) = α(E_{p₂/q₂})` together with `1 ≤ p/(p − 1)`. -/
theorem vertex_removal_bounds_alpha (p q p₂ q₂ : ℕ+)
    (h2q₂ : 2 * q₂ ≤ p₂)
    (hq₂_lt : q₂ < q)
    (heq : (p : ℕ) * q₂ - q * p₂ = 1) :
    ((fractionGraph p₂ q₂).indepNum : ℝ) ≤ (fractionGraph p q).indepNum ∧
    ((fractionGraph p q).indepNum : ℝ) ≤
      (p : ℝ) / (p - 1) * (fractionGraph p₂ q₂).indepNum := by
  -- Derive `h2q : 2*q ≤ p` from `h2q₂`, `hq₂_lt`, `heq`.
  have h2q₂_nat : 2 * (q₂ : ℕ) ≤ (p₂ : ℕ) := by exact_mod_cast h2q₂
  have hq₂_lt_nat : (q₂ : ℕ) < (q : ℕ) := by exact_mod_cast hq₂_lt
  have hq₂_pos : 0 < (q₂ : ℕ) := q₂.pos
  have hpq₂_eq : (p : ℕ) * (q₂ : ℕ) = (q : ℕ) * (p₂ : ℕ) + 1 := by
    have hge : (q : ℕ) * (p₂ : ℕ) ≤ (p : ℕ) * (q₂ : ℕ) := by
      by_contra hlt
      push_neg at hlt
      have : (p : ℕ) * (q₂ : ℕ) - (q : ℕ) * (p₂ : ℕ) = 0 :=
        Nat.sub_eq_zero_of_le hlt.le
      omega
    omega
  have h2q : 2 * q ≤ p := by
    have hkey : 2 * (q : ℕ) * (q₂ : ℕ) + 1 ≤ (p : ℕ) * (q₂ : ℕ) := by
      have h1 : (q : ℕ) * (2 * (q₂ : ℕ)) ≤ (q : ℕ) * (p₂ : ℕ) :=
        Nat.mul_le_mul_left _ h2q₂_nat
      nlinarith [hpq₂_eq]
    have hp_ge : 2 * (q : ℕ) < (p : ℕ) := by
      have hlt' : 2 * (q : ℕ) * (q₂ : ℕ) < (p : ℕ) * (q₂ : ℕ) := by omega
      exact Nat.lt_of_mul_lt_mul_right hlt'
    exact_mod_cast hp_ge.le
  -- Both inequalities follow from the equality
  -- `α(E_{p/q}) = α(E_{p₂/q₂}) = ⌊p₂/q₂⌋`.
  have hα_eq : (fractionGraph p q).indepNum = (fractionGraph p₂ q₂).indepNum :=
    fractionGraph_indepNum_eq_of_sternBrocot
      (p : ℕ) q p₂ q₂ q.pos q₂.pos h2q h2q₂ hq₂_lt heq
  have hα_pos : (0 : ℝ) ≤ ((fractionGraph p₂ q₂).indepNum : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hp_ge_2 : (2 : ℕ) ≤ (p : ℕ) := by
    have hq₂_pos : 1 ≤ (q₂ : ℕ) := q₂.pos
    have h2q_nat : 2 * (q : ℕ) ≤ (p : ℕ) := by exact_mod_cast h2q
    have hq_ge_2 : 2 ≤ (q : ℕ) := by
      have hq₂_lt_nat : (q₂ : ℕ) < (q : ℕ) := by exact_mod_cast hq₂_lt
      omega
    omega
  have hp_minus_1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge_2
    linarith
  have hratio_ge_one : (1 : ℝ) ≤ (p : ℝ) / (p - 1) := by
    rw [le_div_iff₀ hp_minus_1_pos]; linarith
  refine ⟨?_, ?_⟩
  · -- α(E_{p₂/q₂}) ≤ α(E_{p/q}) since they are equal.
    rw [hα_eq]
  · -- α(E_{p/q}) ≤ p/(p−1) · α(E_{p₂/q₂}) since
    -- α(E_{p/q}) = α(E_{p₂/q₂}) ≤ p/(p−1) · α(E_{p₂/q₂}).
    rw [hα_eq]
    calc ((fractionGraph p₂ q₂).indepNum : ℝ)
        = 1 * ((fractionGraph p₂ q₂).indepNum : ℝ) := (one_mul _).symm
      _ ≤ (p : ℝ) / (p - 1) * ((fractionGraph p₂ q₂).indepNum : ℝ) :=
            mul_le_mul_of_nonneg_right hratio_ge_one hα_pos

/-- Proof of `main_vertex_removal_bounds_shannonCapacity`: Θ-analogue of
    Theorem 3.6 for Stern–Brocot–neighbour fraction graphs (`p₂ < p`, `q₂ < q`,
    `p·q₂ − q·p₂ = 1`), `Θ(E_{p₂/q₂}) ≤ Θ(E_{p/q}) ≤ p/(p − 1) · Θ(E_{p₂/q₂})`.

    Strategy (Path B, via duality, avoids re-formalising Lemma 2.16):
    * Lower bound: by `shannonCapacity_eq_iInf_spectrum` Θ is an infimum over
      `AsymptoticSpectrum graphStrassenPreorder`; each such φ is monotone under
      cohomomorphism (`AsymptoticSpectrum.eval_mono`), and we have a
      cohomomorphism `E_{p₂/q₂} → E_{p/q}` from `fractionGraph_ordering`
      applied to the Stern–Brocot ordering `p₂/q₂ ≤ p/q`.
    * Upper bound: choose `φ₀` achieving `Θ(E_{p₂/q₂}) = φ₀(E_{p₂/q₂})` by
      `shannonCapacity_eq_min_spectrum`; apply the spectral 3.6
      (`fractionGraph_spectral_bounds`) at the corresponding graph
      `SpectralPoint` (via `abstractToGraphSpectralPoint`) to get
      `φ₀(E_{p/q}) ≤ p/(p−1) · φ₀(E_{p₂/q₂})`; conclude
      `Θ(E_{p/q}) ≤ φ₀(E_{p/q})` by `shannonCapacity_eq_iInf_spectrum`. -/
theorem vertex_removal_bounds_shannonCapacity (p q p₂ q₂ : ℕ+)
    (h2q₂ : 2 * q₂ ≤ p₂) (hq₂_lt : q₂ < q)
    (heq : (p : ℕ) * q₂ - q * p₂ = 1) :
    shannonCapacity (FractionGraph p₂ q₂) ≤ shannonCapacity (FractionGraph p q) ∧
    shannonCapacity (FractionGraph p q) ≤ (p : ℝ) / (p - 1) *
      shannonCapacity (FractionGraph p₂ q₂) := by
  -- Derive `h2q : 2*q ≤ p` and `hp₂_lt : p₂ < p` from `h2q₂`, `hq₂_lt`, `heq`.
  have h2q₂_nat : 2 * (q₂ : ℕ) ≤ (p₂ : ℕ) := by exact_mod_cast h2q₂
  have hq₂_lt_nat : (q₂ : ℕ) < (q : ℕ) := by exact_mod_cast hq₂_lt
  have hq₂_pos : 0 < (q₂ : ℕ) := q₂.pos
  have hp₂_pos : 0 < (p₂ : ℕ) := p₂.pos
  have hpq₂_eq : (p : ℕ) * (q₂ : ℕ) = (q : ℕ) * (p₂ : ℕ) + 1 := by
    have hge : (q : ℕ) * (p₂ : ℕ) ≤ (p : ℕ) * (q₂ : ℕ) := by
      by_contra hlt
      push_neg at hlt
      have : (p : ℕ) * (q₂ : ℕ) - (q : ℕ) * (p₂ : ℕ) = 0 :=
        Nat.sub_eq_zero_of_le hlt.le
      omega
    omega
  have h2q : 2 * q ≤ p := by
    have hkey : 2 * (q : ℕ) * (q₂ : ℕ) + 1 ≤ (p : ℕ) * (q₂ : ℕ) := by
      have h1 : (q : ℕ) * (2 * (q₂ : ℕ)) ≤ (q : ℕ) * (p₂ : ℕ) :=
        Nat.mul_le_mul_left _ h2q₂_nat
      nlinarith [hpq₂_eq]
    have hp_ge : 2 * (q : ℕ) < (p : ℕ) := by
      have hlt' : 2 * (q : ℕ) * (q₂ : ℕ) < (p : ℕ) * (q₂ : ℕ) := by omega
      exact Nat.lt_of_mul_lt_mul_right hlt'
    exact_mod_cast hp_ge.le
  have hp₂_lt : p₂ < p := by
    have hp₂_lt_nat : (p₂ : ℕ) < (p : ℕ) := by
      by_contra hle
      push_neg at hle
      have h1 : (p : ℕ) * (q₂ : ℕ) ≤ (p₂ : ℕ) * (q₂ : ℕ) :=
        Nat.mul_le_mul_right _ hle
      have h2 : (p₂ : ℕ) * (q₂ : ℕ) < (p₂ : ℕ) * (q : ℕ) :=
        (Nat.mul_lt_mul_left hp₂_pos).mpr hq₂_lt_nat
      nlinarith [hpq₂_eq]
    exact_mod_cast hp₂_lt_nat
  -- Helpful arithmetic: p ≥ 2 hence p − 1 > 0.
  have hp_ge_2 : (2 : ℕ) ≤ (p : ℕ) := by
    have h2q_nat : 2 * (q : ℕ) ≤ (p : ℕ) := by exact_mod_cast h2q
    have hq_ge_2 : 2 ≤ (q : ℕ) := by
      omega
    omega
  have hp_minus_1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge_2
    linarith
  -- Cohomomorphism E_{p₂/q₂} → E_{p/q} from the Stern–Brocot ordering.
  have hp₂_ne : NeZero (p₂ : ℕ) := ⟨p₂.pos.ne'⟩
  have hp_ne : NeZero (p : ℕ) := ⟨p.pos.ne'⟩
  have h2q_nat : 2 * (q : ℕ) ≤ (p : ℕ) := by exact_mod_cast h2q
  have hlt_rat : ((p₂ : ℕ) : ℚ) / (q₂ : ℕ) < ((p : ℕ) : ℚ) / (q : ℕ) :=
    sternBrocot_predecessor_lt (p : ℕ) q p₂ q₂ hp₂_lt hq₂_lt q₂.pos heq
  have hle_rat : ((p₂ : ℕ) : ℚ) / (q₂ : ℕ) ≤ ((p : ℕ) : ℚ) / (q : ℕ) := le_of_lt hlt_rat
  have hcohom : Cohom (fractionGraph (p₂ : ℕ) q₂) (fractionGraph (p : ℕ) q) :=
    (fractionGraph_ordering (p₂ : ℕ) q₂ (p : ℕ) q q₂.pos q.pos h2q₂_nat h2q_nat).mp hle_rat
  -- Translate to the abstract preorder relation.
  have hrel : graphStrassenPreorder.rel
      (GraphClass.mk (FractionGraph p₂ q₂)) (GraphClass.mk (FractionGraph p q)) := by
    change Cohom (FractionGraph p₂ q₂).graph (FractionGraph p q).graph
    exact hcohom
  refine ⟨?_, ?_⟩
  · -- Lower bound: Θ(E_{p₂/q₂}) ≤ Θ(E_{p/q}) via iInf-monotonicity.
    rw [shannonCapacity_eq_iInf_spectrum (FractionGraph p₂ q₂),
        shannonCapacity_eq_iInf_spectrum (FractionGraph p q)]
    refine ciInf_mono ?_ ?_
    · -- BddBelow: every spectral evaluation is ≥ 0.
      refine ⟨0, ?_⟩
      rintro x ⟨ψ, rfl⟩
      exact AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_nonneg
        graphStrassenPreorder ψ _
    · intro ψ
      exact AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_mono
        graphStrassenPreorder ψ hrel
  · -- Upper bound: route through a minimising φ₀ on E_{p₂/q₂}.
    obtain ⟨φ₀, hφ₀⟩ := shannonCapacity_eq_min_spectrum (FractionGraph p₂ q₂)
    -- Translate φ₀ into a graph SpectralPoint and apply the spectral 3.6 bound.
    set φ : SpectralPoint := abstractToGraphSpectralPoint φ₀ with hφ_def
    have heval_p₂ : φ.eval (FractionGraph p₂ q₂) =
        AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder
          (GraphClass.mk (FractionGraph p₂ q₂)) φ₀ := rfl
    have heval_p : φ.eval (FractionGraph p q) =
        AsymptoticSpectrumDuality.AsymptoticSpectrum.eval graphStrassenPreorder
          (GraphClass.mk (FractionGraph p q)) φ₀ := rfl
    -- Spectral 3.6 at φ.
    have hbounds := fractionGraph_spectral_bounds (p : ℕ) q p₂ q₂
      q.pos q₂.pos h2q h2q₂ hp₂_lt hq₂_lt heq φ
    obtain ⟨_, hhi⟩ := hbounds
    -- `FractionGraph' p q = FractionGraph p q` definitionally (modulo NeZero packaging).
    have hF_p : (FractionGraph' (p : ℕ) q : Graph) = FractionGraph p q := rfl
    have hF_p₂ : (FractionGraph' (p₂ : ℕ) q₂ : Graph) = FractionGraph p₂ q₂ := rfl
    -- Θ(E_{p/q}) ≤ φ(E_{p/q}) by iInf characterisation.
    have hTheta_le_phi_p : shannonCapacity (FractionGraph p q) ≤ φ.eval (FractionGraph p q) := by
      rw [shannonCapacity_eq_iInf_spectrum (FractionGraph p q), heval_p]
      refine ciInf_le ?_ φ₀
      refine ⟨0, ?_⟩
      rintro x ⟨ψ, rfl⟩
      exact AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_nonneg
        graphStrassenPreorder ψ _
    -- Chain: Θ(E_{p/q}) ≤ φ(E_{p/q}) ≤ p/(p-1) · φ(E_{p₂/q₂}) = p/(p-1) · Θ(E_{p₂/q₂}).
    have hratio_nonneg : (0 : ℝ) ≤ (p : ℝ) / (p - 1) := by
      apply div_nonneg
      · exact_mod_cast p.pos.le
      · linarith
    have hphi_eq_theta : φ.eval (FractionGraph p₂ q₂) =
        shannonCapacity (FractionGraph p₂ q₂) := by
      rw [heval_p₂, ← hφ₀]
    calc shannonCapacity (FractionGraph p q)
        ≤ φ.eval (FractionGraph p q) := hTheta_le_phi_p
      _ ≤ (p : ℝ) / (p - 1) * φ.eval (FractionGraph p₂ q₂) := by
            -- Unfold FractionGraph' to FractionGraph in hhi.
            simpa [hF_p, hF_p₂] using hhi
      _ = (p : ℝ) / (p - 1) * shannonCapacity (FractionGraph p₂ q₂) := by
            rw [hphi_eq_theta]

end AsymptoticSpectrumDistance
