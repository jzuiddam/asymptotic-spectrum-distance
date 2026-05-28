/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Shannon Capacity of Graphs via Lattices

Basic definitions and properties.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.ZMod.ValMinAbs
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.GraphOperations
import AsymptoticSpectrumDistance.Prerequisites.FractionGraph

namespace ShannonCapacity

open SimpleGraph FractionGraphBasic

-- Re-export `SimpleGraph.strongPower` and the cohomomorphism-extension lemma
-- as `ShannonCapacity.*` so callers that `open ShannonCapacity` get them
-- under the short names.  `independenceNumber_le_of_clique_cover` is a fully
-- generic `SimpleGraph` lemma (lives in `GraphOperations.lean`) and is
-- re-exported here too.
export SimpleGraph (strongPower strongPower_cohomomorphism_of_cohomomorphism
  independenceNumber_le_of_cohomomorphism independenceNumber_iso
  independenceNumber_le_of_clique_cover)

-- Re-export the `distMod` / `fractionGraph` families from `FractionGraphBasic`
-- so callers that `open ShannonCapacity` keep getting these names under the
-- short form.  The clique-number / clique-cover lemmas (consolidated into
-- `Prerequisites/FractionGraph.lean`) are also re-exported here for the same
-- reason.
export FractionGraphBasic (distMod distMod_eq_valMinAbs_natAbs distMod_comm
  distMod_add_left min_span_ge_q_of_in_range fractionGraph
  fractionGraph_adj_add_left fractionGraph_scalingMap
  fractionGraph_scalingMap_isCohom fractionGraph_cohomomorphism
  distMod_ge_q_of_val_diff_in_range finset_card_le_of_pairwise_dist_lt
  cliqueNum_fractionGraph_le isClique_range_fractionGraph isClique_arc
  cliqueNum_fractionGraph_ge cliqueNum_fractionGraph_eq
  fractionalCliqueCover_fractionGraph)

-- Re-export the canonical `fractionGraph` decidability instance.
export FractionGraphBasic (fractionGraph_adj_decidable)

/-- Canonical decidability instance for `(strongPower G n).Adj` whenever the
base graph's adjacency is decidable and the vertex type has decidable equality.

Adjacency in `strongPower G n` is
`f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj (f i) (g i)`,
which is decidable componentwise. -/
instance strongPower_adj_decidable {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    DecidableRel (SimpleGraph.strongPower G n).Adj := fun f g => by
  change Decidable (f ≠ g ∧ ∀ i : Fin n, f i = g i ∨ G.Adj (f i) (g i))
  exact instDecidableAnd

/-! ## Section 1: Graph Theory Basics -/

/-- Strong power preserves graph isomorphism. -/
def strongPower_iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (n : ℕ) : strongPower G n ≃g strongPower H n where
  toEquiv := Equiv.piCongrRight (fun _ => f.toEquiv)
  map_rel_iff' := by
    intro x y
    simp only [strongPower, Equiv.piCongrRight_apply, Pi.map_apply]
    constructor
    · intro ⟨hne, h⟩
      refine ⟨?_, fun i => ?_⟩
      · intro heq; exact hne (by simp only [heq])
      · cases h i with
        | inl heq => left; exact f.toEquiv.injective heq
        | inr hadj => right; exact f.map_rel_iff'.mp hadj
    · intro ⟨hne, h⟩
      refine ⟨?_, fun i => ?_⟩
      · intro heq
        apply hne
        have : ∀ i, f.toEquiv (x i) = f.toEquiv (y i) := congr_fun heq
        funext i
        exact f.toEquiv.injective (this i)
      · cases h i with
        | inl heq => left; exact congr_arg f.toEquiv heq
        | inr hadj => right; exact f.map_rel_iff'.mpr hadj

/-- Product of cliques is a clique in the strong power.
    If each `sets i` is a clique in G, then their product is a clique in G^⊠n. -/
theorem strongPower_isClique_piFinset (G : SimpleGraph V) (n : ℕ)
    (sets : Fin n → Finset V) (hclique : ∀ i, G.IsClique (sets i)) :
    (strongPower G n).IsClique (Fintype.piFinset sets) := by
  classical
  rw [SimpleGraph.isClique_iff]
  intro f hf g hg hfg
  have hf' := Fintype.mem_piFinset.mp hf
  have hg' := Fintype.mem_piFinset.mp hg
  simp only [strongPower]
  constructor
  · exact hfg
  · intro i
    by_cases heq : f i = g i
    · left; exact heq
    · right
      have hclique_i := hclique i
      rw [SimpleGraph.isClique_iff] at hclique_i
      exact hclique_i (hf' i) (hg' i) heq

/-- The Shannon capacity Θ(G) = sup_{n≥1} α(G^⊠n)^(1/n) -/
noncomputable def shannonCapacity (G : SimpleGraph V) [Fintype V] : ℝ :=
  ⨆ n : ℕ, ((strongPower G (n + 1)).indepNum : ℝ) ^ (1 / (n + 1 : ℝ))

/-- Shannon capacity is preserved under graph isomorphism. -/
theorem shannonCapacity_iso {W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    shannonCapacity G = shannonCapacity H := by
  unfold shannonCapacity
  congr 1
  ext n
  congr 1
  exact_mod_cast independenceNumber_iso (strongPower_iso f (n + 1))

/-! ## Section 2: Fraction Graphs

The `distMod` family, the `fractionGraph` definition, and the scaling-map
cohomomorphism live in `Prerequisites/DistMod.lean` and
`Prerequisites/FractionGraph.lean` (namespace `FractionGraphBasic`) and are
re-exported via the `export` statements at the top of this file. -/

/-- The equivalence between Fin n and ZMod n -/
def finEquivZMod (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun := fun i => i.val
  invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
  left_inv := fun i => by simp [ZMod.val_natCast_of_lt i.isLt]
  right_inv := fun z => by simp

/-- distMod p u v = 1 iff u - v = 1 or u - v = -1 -/
lemma distMod_eq_one_iff (p : ℕ) [hp : NeZero p] (hp3 : 3 ≤ p) (u v : ZMod p) (hne : u ≠ v) :
    distMod p u v = 1 ↔ (u - v = 1 ∨ u - v = -1) := by
  have hp1 : p ≠ 1 := by omega
  have hone : (1 : ZMod p).val = 1 := ZMod.val_one'' hp1
  have hone_ne : (1 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.val_eq_zero _).mpr h
    rw [hone] at this
    omega
  have hneg_one : (-(1 : ZMod p)).val = p - 1 := by
    rw [ZMod.neg_val (1 : ZMod p)]
    simp [hone_ne, hone]
  simp only [distMod]
  have hd_pos : 0 < (u - v).val := by
    by_contra h
    push_neg at h
    have hzero : (u - v).val = 0 := Nat.le_zero.mp h
    have := (ZMod.val_eq_zero _).mp hzero
    exact hne (sub_eq_zero.mp this)
  have hd_lt : (u - v).val < p := (u - v).val_lt
  constructor
  · intro h
    have hmin : min (u - v).val (p - (u - v).val) = 1 := h
    -- Case split: either (u-v).val = 1 or (p - (u-v).val) = 1
    by_cases hcase : (u - v).val ≤ p - (u - v).val
    · -- min is (u - v).val
      have heq : (u - v).val = 1 := by
        rw [min_eq_left hcase] at hmin
        exact hmin
      left
      exact ZMod.val_injective p (heq.trans hone.symm)
    · -- min is (p - (u - v).val)
      push_neg at hcase
      have heq : p - (u - v).val = 1 := by
        rw [min_eq_right (le_of_lt hcase)] at hmin
        exact hmin
      right
      have hval : (u - v).val = p - 1 := by omega
      exact ZMod.val_injective p (hval.trans hneg_one.symm)
  · intro h
    cases h with
    | inl h1 =>
      rw [h1, hone]; omega
    | inr h1 =>
      rw [h1, hneg_one]; omega

/-- fractionGraph p 2 equals the circulant graph with connection set {1} -/
theorem fractionGraph_two_eq_circulant (p : ℕ) [hp : NeZero p] (hp3 : 3 ≤ p) :
    fractionGraph p 2 = SimpleGraph.circulantGraph {(1 : ZMod p)} := by
  ext u v
  simp only [fractionGraph, distMod, SimpleGraph.circulantGraph_adj, Set.mem_singleton_iff]
  constructor
  · intro ⟨hne, hdist⟩
    constructor
    · exact hne
    · have hd_pos : 0 < (u - v).val := by
        by_contra h; push_neg at h
        have hzero : (u - v).val = 0 := Nat.le_zero.mp h
        have := (ZMod.val_eq_zero _).mp hzero
        exact hne (sub_eq_zero.mp this)
      have hd_lt : (u - v).val < p := (u - v).val_lt
      have hmin_pos : 0 < min (u - v).val (p - (u - v).val) := by
        simp only [lt_min_iff]; exact ⟨hd_pos, by omega⟩
      have hmin_eq_one : min (u - v).val (p - (u - v).val) = 1 := by omega
      have hdist' : distMod p u v = 1 := hmin_eq_one
      rw [distMod_eq_one_iff p hp3 u v hne] at hdist'
      cases hdist' with
      | inl h1 => left; exact h1
      | inr h1 =>
        right
        have : v - u = -(u - v) := by ring
        rw [this, h1]; ring
  · intro ⟨hne, h⟩
    constructor
    · exact hne
    · have hdist' : distMod p u v = 1 := by
        rw [distMod_eq_one_iff p hp3 u v hne]
        cases h with
        | inl h1 => left; exact h1
        | inr h1 =>
          right
          calc u - v = -(v - u) := by ring
            _ = -1 := by rw [h1]
      simp only [distMod] at hdist'; omega

/-- Helper: Fin p subtraction value equals ZMod p subtraction value -/
lemma fin_sub_val_eq_zmod_sub_val (p : ℕ) [NeZero p] (a b : Fin p) :
    (a - b).val = ((a.val : ZMod p) - (b.val : ZMod p)).val := by
  have hp : 0 < p := NeZero.pos p
  have ha_lt : a.val < p := a.isLt
  have hb_lt : b.val < p := b.isLt
  simp only [Fin.sub_def, Fin.val_mk]
  by_cases hle : b.val ≤ a.val
  · -- Case: a.val ≥ b.val, so (p - b + a) % p = a - b
    have heq : (p - b.val + a.val) % p = a.val - b.val := by
      have h1 : p - b.val + a.val = a.val - b.val + p := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a.val - b.val < p)]
    rw [heq]
    have hsub : (a.val : ZMod p) - (b.val : ZMod p) = ((a.val - b.val : ℕ) : ZMod p) := by
      rw [← Nat.cast_sub hle]
    rw [hsub, ZMod.val_natCast_of_lt (by omega : a.val - b.val < p)]
  · -- Case: a.val < b.val, so (p - b + a) % p = p - (b - a)
    push_neg at hle
    have heq : (p - b.val + a.val) % p = p - (b.val - a.val) := by
      have h1 : p - b.val + a.val = p - (b.val - a.val) := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega : p - (b.val - a.val) < p)]
    rw [heq]
    -- Need: (a.val : ZMod p) - (b.val : ZMod p) has value p - (b.val - a.val)
    have hlt' : b.val - a.val < p := by omega
    have hne_zmod : ((b.val - a.val : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have := (ZMod.val_eq_zero _).mpr h
      rw [ZMod.val_natCast_of_lt hlt'] at this
      omega
    have hsub : (a.val : ZMod p) - (b.val : ZMod p) = -((b.val - a.val : ℕ) : ZMod p) := by
      have h1 : ((b.val - a.val : ℕ) : ZMod p) = (b.val : ZMod p) - (a.val : ZMod p) := by
        rw [Nat.cast_sub (le_of_lt hle)]
      rw [h1]; ring
    rw [hsub, ZMod.neg_val, if_neg hne_zmod, ZMod.val_natCast_of_lt hlt']

/-- Helper: ZMod subtraction = 1 implies Fin subtraction = 1 -/
private lemma fin_sub_eq_one_of_zmod_sub_eq_one (p : ℕ) [NeZero p] (hp1 : 1 < p) (a b : Fin p)
    (h : (a.val : ZMod p) - (b.val : ZMod p) = 1) : a - b = 1 := by
  have hzmod_val : ((a.val : ZMod p) - (b.val : ZMod p)).val = 1 := by
    rw [h, ZMod.val_one'' (by omega : p ≠ 1)]
  rw [← fin_sub_val_eq_zmod_sub_val] at hzmod_val
  have h1 : (1 : Fin p).val = 1 := Nat.mod_eq_of_lt hp1
  exact Fin.ext (hzmod_val.trans h1.symm)

/-- Helper: Fin subtraction = 1 implies ZMod subtraction = 1 -/
private lemma zmod_sub_eq_one_of_fin_sub_eq_one (p : ℕ) [NeZero p] (hp1 : 1 < p) (a b : Fin p)
    (h : a - b = 1) : (a.val : ZMod p) - (b.val : ZMod p) = 1 := by
  have hfin_val : (a - b).val = 1 := by rw [h]; exact Nat.mod_eq_of_lt hp1
  rw [fin_sub_val_eq_zmod_sub_val] at hfin_val
  exact (ZMod.val_eq_one hp1 _).mp hfin_val

/-- The cycle graph C_p is isomorphic to the fraction graph E_{p/2} -/
def cycleGraph_iso_fractionGraph_two (p : ℕ) [hp : NeZero p] (hp2 : 2 ≤ p) :
    SimpleGraph.cycleGraph p ≃g fractionGraph p 2 := by
  -- Case split: p = 2 vs p ≥ 3
  by_cases heq : p = 2
  · -- p = 2: both graphs are complete on 2 vertices
    subst heq
    refine ⟨finEquivZMod 2, ?_⟩
    intro a b
    -- Both graphs on 2 vertices: adjacency iff distinct
    simp only [SimpleGraph.cycleGraph_adj, finEquivZMod, Equiv.coe_fn_mk, fractionGraph, distMod]
    revert a b
    decide
  · -- p ≥ 3: use circulant characterization
    have hp3 : 2 < p := Nat.lt_of_le_of_ne hp2 (Ne.symm heq)
    have hp3' : 3 ≤ p := hp3
    have hcycle : SimpleGraph.cycleGraph p = SimpleGraph.circulantGraph {(1 : Fin p)} := by
      obtain _ | n := p
      · exact (NeZero.ne 0 rfl).elim
      · exact SimpleGraph.cycleGraph_eq_circulantGraph n
    have hfrac : fractionGraph p 2 = SimpleGraph.circulantGraph {(1 : ZMod p)} :=
      fractionGraph_two_eq_circulant p hp3'
    rw [hcycle, hfrac]
    refine ⟨finEquivZMod p, ?_⟩
    intro a b
    simp only [SimpleGraph.circulantGraph_adj, Set.mem_singleton_iff, finEquivZMod, Equiv.coe_fn_mk]
    have hp1 : 1 < p := by omega
    have ha_lt : a.val < p := a.isLt
    have hb_lt : b.val < p := b.isLt
    constructor
    · intro ⟨hne_zmod, h_zmod⟩
      constructor
      · intro heq_fin; rw [heq_fin] at hne_zmod; exact hne_zmod rfl
      · cases h_zmod with
        | inl hab_zmod => exact Or.inl (fin_sub_eq_one_of_zmod_sub_eq_one p hp1 a b hab_zmod)
        | inr hba_zmod => exact Or.inr (fin_sub_eq_one_of_zmod_sub_eq_one p hp1 b a hba_zmod)
    · intro ⟨hne_fin, h_fin⟩
      constructor
      · intro heq_zmod
        have ha_eq : (a.val : ZMod p).val = a.val := ZMod.val_natCast_of_lt ha_lt
        have hb_eq : (b.val : ZMod p).val = b.val := ZMod.val_natCast_of_lt hb_lt
        exact hne_fin (Fin.ext (by rw [← ha_eq, ← hb_eq, heq_zmod]))
      · cases h_fin with
        | inl hab_fin => exact Or.inl (zmod_sub_eq_one_of_fin_sub_eq_one p hp1 a b hab_fin)
        | inr hba_fin => exact Or.inr (zmod_sub_eq_one_of_fin_sub_eq_one p hp1 b a hba_fin)

/-! ## Section 3: Subgroup Independence -/

/-- The subgroup independence number α_grp(Γ): the maximum cardinality of a subgroup
    that is an independent set in Γ -/
@[to_additive /-- The additive subgroup independence number α_grp(Γ): the maximum cardinality of
    an AddSubgroup that is an independent set in Γ -/]
noncomputable def subgroupIndependenceNumber {G : Type*} [Group G] [Fintype G]
    (Γ : SimpleGraph G) : ℕ := by
  classical
  exact sSup { n : ℕ | ∃ H : Subgroup G, Γ.IsIndepSet (H : Set G) ∧ Nat.card H = n }

/-- The subgroup Shannon capacity Θ_grp(Γ) = sup_{n≥1} α_grp(Γ^⊠n)^(1/n) -/
@[to_additive /-- The additive subgroup Shannon capacity Θ_grp(Γ) = sup_{n≥1} α_grp(Γ^⊠n)^(1/n)
    for Cayley graphs over additive groups -/]
noncomputable def subgroupShannonCapacity {G : Type*} [Group G] [Fintype G]
    (Γ : SimpleGraph G) : ℝ :=
  ⨆ n : ℕ, (subgroupIndependenceNumber (strongPower Γ (n + 1)) : ℝ) ^ (1 / (n + 1 : ℝ))

/-! ## Shannon Capacity Bounds -/

set_option linter.unusedFintypeInType false in
/-- If S is an independent Set, then G.indepNum ≥ |S|. -/
theorem independenceNumber_ge_natCard_of_independent (G : SimpleGraph V) [Fintype V]
    (S : Set V) (hS : G.IsIndepSet S) :
    G.indepNum ≥ Nat.card S := by
  classical
  have hfin : S.Finite := Set.toFinite S
  have hS' : G.IsIndepSet ((hfin.toFinset) : Set V) := by
    apply (SimpleGraph.isIndepSet_iff G).2
    intro u hu v hv huv
    have hu' : u ∈ S := by simpa [Set.Finite.mem_toFinset] using hu
    have hv' : v ∈ S := by simpa [Set.Finite.mem_toFinset] using hv
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS
    exact hpair hu' hv' huv
  have h := SimpleGraph.IsIndepSet.card_le_indepNum hS'
  simp only [Set.Finite.card_toFinset] at h
  have hcard : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
  rw [hcard]
  exact h

/-- The independence number is bounded by the number of vertices. -/
theorem independenceNumber_le_card (G : SimpleGraph V) [Fintype V] :
    G.indepNum ≤ Fintype.card V := by
  classical
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_card : S.card = G.indepNum := by
    simpa using
      (SimpleGraph.maximumIndepSet_card_eq_indepNum (G := G) S hSmax)
  have hle : S.card ≤ Fintype.card V := by
    simpa using (Finset.card_le_univ (s := S))
  simpa [hS_card] using hle

set_option linter.unusedFintypeInType false in
/-- The Shannon capacity sequence is bounded above by the cardinality of the vertex set. -/
lemma shannonCapacity_bddAbove (G : SimpleGraph V) [Fintype V] :
    BddAbove (Set.range fun m =>
      ((strongPower G (m + 1)).indepNum : ℝ) ^ (1 / (m + 1 : ℝ))) := by
  use (Fintype.card V : ℝ)
  intro x ⟨m, hm⟩
  rw [← hm]
  have hexp_pos : (0 : ℝ) ≤ 1 / (m + 1) := by positivity
  have hcard_pos : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hindep_le : ((strongPower G (m + 1)).indepNum : ℝ) ≤
      (Fintype.card (Fin (m + 1) → V) : ℝ) := by
    exact_mod_cast independenceNumber_le_card (strongPower G (m + 1))
  have hcard_eq : Fintype.card (Fin (m + 1) → V) = (Fintype.card V) ^ (m + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
  calc ((strongPower G (m + 1)).indepNum : ℝ) ^ (1 / (m + 1 : ℝ))
      ≤ (Fintype.card (Fin (m + 1) → V) : ℝ) ^ (1 / (m + 1 : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) hindep_le hexp_pos
    _ = ((Fintype.card V : ℝ) ^ (m + 1 : ℕ)) ^ (1 / (m + 1 : ℝ)) := by
        rw [hcard_eq]; norm_cast
    _ = (Fintype.card V : ℝ) ^ ((m + 1 : ℕ) * (1 / (m + 1 : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hcard_pos]
    _ = (Fintype.card V : ℝ) ^ (1 : ℝ) := by
        congr 1; push_cast; field_simp
    _ = Fintype.card V := Real.rpow_one _

/-- Lower bound: Shannon capacity is at least α(G^⊠n)^(1/n) for any n ≥ 1.
This follows directly from the definition of Shannon capacity as a supremum. -/
theorem shannonCapacity_ge_root (G : SimpleGraph V) [Fintype V] (n : ℕ) (hn : n ≥ 1) :
    shannonCapacity G ≥ ((strongPower G n).indepNum : ℝ) ^ (1 / (n : ℝ)) := by
  simp only [shannonCapacity]
  apply le_ciSup_of_le (shannonCapacity_bddAbove G) (n - 1)
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [h]
  simp only [← Nat.cast_add_one, h, le_refl]

end ShannonCapacity
