/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.Embedding
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.Specialization
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphOperations
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphSemiring
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumInfiniteGraphs.InfiniteGraphStrassenPreorder
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.FractionalCliqueCover
import AsymptoticSpectrumDistance.Prerequisites.AsymptoticSpectrumGraphs.DualityTheorems
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Asymptotic Spectrum Distance and Limit Infrastructure for Infinite Graphs

This file collects the generic infinite-graph infrastructure that is
independent of any particular family of graphs (circle graphs, fraction
graphs, etc.).  It was previously located in `Section4/CircleGraphLimits.lean`
but is reused throughout the development.

## Main definitions

* `asympSpecDistanceInf`, `ConvergesToInf` - distance and convergence for
  infinite graphs in terms of `SpectralPointInf`.
* `recInfProduct` - iterated strong product (left-recursive) of an infinite
  graph, matching the `npowRec` convention of `InfiniteGraphClass`.
* `recInfProduct_iso_strongPower` - graph isomorphism between `recInfProduct`
  and `strongPower`.
* `AsympCohomInf`, `AsympCohomEquivInf` - asymptotic order/equivalence in the
  infinite-graph Strassen preorder.

## Main theorems

* `convergesToInf_of_uniform_bound` - uniform spectral bound implies convergence.
* `spectral_duality_inf` - infinite-graph version of asymptotic spectrum duality.
* `infClass_pow_eq_mk`, `infCohom_mk_iff`, `recInfProduct_mono` - bridging
  lemmas between `recInfProduct` and `InfiniteGraphClass` operations.
* `cohom_of_relIso`, `strongProduct_cohom_both`, `strongPower_product_merge` -
  small generic helpers about `Cohom` and strong products / powers.
-/

set_option linter.style.longLine false

namespace AsymptoticSpectrumDistance

open AsymptoticSpectrumGraphs SimpleGraph ShannonCapacity
open AsymptoticSpectrumInfiniteGraphs

/-! ### Asymptotic Spectrum Distance for Infinite Graphs -/

/-- The asymptotic spectrum distance between two infinite graphs.
    d(G, H) = sup_{ψ ∈ X_∞} |ψ(G) - ψ(H)| -/
noncomputable def asympSpecDistanceInf (G H : InfiniteGraph) : ℝ :=
  sSup {x | ∃ ψ : SpectralPointInf, x = |ψ.eval G - ψ.eval H|}

/-- A sequence of infinite graphs converges to H if their distance to H goes to 0. -/
def ConvergesToInf (Gs : ℕ → InfiniteGraph) (H : InfiniteGraph) : Prop :=
  Filter.Tendsto (fun n => asympSpecDistanceInf (Gs n) H) Filter.atTop (nhds 0)

/-- Uniform pointwise bound implies ConvergesToInf. -/
theorem convergesToInf_of_uniform_bound
    (Gs : ℕ → InfiniteGraph) (H : InfiniteGraph)
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ ψ : SpectralPointInf,
      |ψ.eval (Gs n) - ψ.eval H| < ε) :
    ConvergesToInf Gs H := by
  unfold ConvergesToInf
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)
  use N
  intro n hn
  rw [Real.dist_eq, sub_zero]
  have hne : {x | ∃ ψ : SpectralPointInf, x = |ψ.eval (Gs n) - ψ.eval H|}.Nonempty := by
    obtain ⟨ψ, _⟩ := restriction_surjective chibar_spectralPoint
    exact ⟨_, ψ, rfl⟩
  have hbdd : BddAbove {x | ∃ ψ : SpectralPointInf, x = |ψ.eval (Gs n) - ψ.eval H|} :=
    ⟨ε / 2, fun x ⟨ψ, hx⟩ => hx ▸ le_of_lt (hN n hn ψ)⟩
  have hle : sSup {x | ∃ ψ : SpectralPointInf, x = |ψ.eval (Gs n) - ψ.eval H|} ≤ ε / 2 :=
    csSup_le hne (fun x ⟨ψ, hx⟩ => hx ▸ le_of_lt (hN n hn ψ))
  have hnn : 0 ≤ sSup {x | ∃ ψ : SpectralPointInf, x = |ψ.eval (Gs n) - ψ.eval H|} := by
    obtain ⟨x, ψ, hx⟩ := hne
    exact le_trans (hx ▸ abs_nonneg _) (le_csSup hbdd ⟨ψ, hx⟩)
  unfold asympSpecDistanceInf at hnn ⊢
  rw [abs_of_nonneg hnn]
  linarith

/-! ### Spectral Duality and Iterated Strong Product -/

/-- Spectral duality for infinite graphs: `AsympRel` in the infinite graph Strassen
    preorder is equivalent to all `SpectralPointInf` agreeing on the ordering.
    Specializes `asympRel_iff_forall_spectrum` via the round-trip between
    `SpectralPointInf` and abstract `SpectralPoint`. -/
theorem spectral_duality_inf (G H : InfiniteGraph) :
    AsymptoticSpectrumDuality.AsympRel infiniteGraphStrassenPreorder
      (InfiniteGraphClass.mk G) (InfiniteGraphClass.mk H) ↔
    ∀ ψ : SpectralPointInf, ψ.eval G ≤ ψ.eval H := by
  rw [infiniteGraphStrassenPreorder.asympRel_iff_forall_spectrum]
  exact ⟨fun h ψ => h (infGraphSpectralPointToAbstract ψ),
         fun h φ => h (abstractToInfGraphSpectralPoint φ)⟩

/-- Iterated strong product of infinite graphs, matching the `npowRec` convention. -/
def recInfProduct (G : InfiniteGraph) : ℕ → InfiniteGraph
  | 0 => InfiniteGraph.edgeless 1
  | n + 1 => (recInfProduct G n) ⊠∞ G

/-- Power in `InfiniteGraphClass` equals `mk` of the iterated strong product. -/
theorem infClass_pow_eq_mk (G : InfiniteGraph) (n : ℕ) :
    (InfiniteGraphClass.mk G) ^ n = InfiniteGraphClass.mk (recInfProduct G n) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, InfiniteGraphClass.mul_def]; rfl

/-- `infiniteGraphCohom` on `mk` terms equals `Cohom` on graphs. -/
theorem infCohom_mk_iff (A B : InfiniteGraph) :
    infiniteGraphCohom (InfiniteGraphClass.mk A) (InfiniteGraphClass.mk B) ↔
    Cohom A.graph B.graph :=
  Iff.of_eq (infiniteGraphCohom_mk A B)

/-- `Cohom` is preserved under iterated strong product of infinite graphs. -/
theorem recInfProduct_mono {G H : InfiniteGraph} (hGH : Cohom G.graph H.graph) (n : ℕ) :
    Cohom (recInfProduct G n).graph (recInfProduct H n).graph := by
  induction n with
  | zero => exact ⟨id, fun _ _ hne hnadj => ⟨hne, hnadj⟩⟩
  | succ k ih =>
    exact Cohom.trans
      (InfiniteGraph.cohom_strongProduct_left (H := G) ih)
      (by obtain ⟨f, hf⟩ := hGH; exact ⟨Prod.map id f, hf.strongProduct_map_snd⟩)

/-! ### Bridge: recInfProduct ≃g strongPower -/

/-- Vertex equivalence between recInfProduct (left-recursive nested products)
    and strongPower (function type Fin n → V).
    Uses `Fin.snoc` to append new coordinates on the right. -/
def recInfProduct_vertex_equiv (G : InfiniteGraph) : (m : ℕ) →
    (recInfProduct G m).V ≃ (Fin m → G.V)
  | 0 => {
      toFun := fun _ => Fin.elim0
      invFun := fun _ => ⟨0, Nat.zero_lt_one⟩
      left_inv := fun x => Fin.ext (Nat.lt_one_iff.mp x.isLt).symm
      right_inv := fun f => funext (fun i => i.elim0)
    }
  | m + 1 =>
      let e := recInfProduct_vertex_equiv G m
      { toFun := fun ⟨rest, v⟩ => Fin.snoc (e rest) v
        invFun := fun f => (e.symm (Fin.init f), f (Fin.last m))
        left_inv := fun ⟨rest, v⟩ => by simp [e.symm_apply_apply]
        right_inv := fun f => by
          funext i
          cases i using Fin.lastCases with
          | last => simp
          | cast j => simp [e.apply_symm_apply, Fin.init]
      }

/-- Adjacency in recInfProduct corresponds to adjacency in strongPower under the
    vertex equivalence. The key insight is that the left-recursive strong product
    decomposes into "all-but-last" and "last" coordinates via Fin.snoc. -/
theorem recInfProduct_adj_iff (G : InfiniteGraph) (m : ℕ)
    (x y : (recInfProduct G m).V) :
    (recInfProduct G m).graph.Adj x y ↔
    (strongPower G.graph m).Adj
      (recInfProduct_vertex_equiv G m x)
      (recInfProduct_vertex_equiv G m y) := by
  induction m with
  | zero =>
    constructor
    · intro h; exact h.elim
    · intro ⟨hne, _⟩; exfalso; apply hne; funext i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨r₁, v₁⟩ := x
    obtain ⟨r₂, v₂⟩ := y
    let e := recInfProduct_vertex_equiv G n
    change (ShannonCapacity.strongProduct (recInfProduct G n).graph G.graph).Adj (r₁, v₁) (r₂, v₂) ↔
      (strongPower G.graph (n + 1)).Adj (Fin.snoc (e r₁) v₁) (Fin.snoc (e r₂) v₂)
    simp only [ShannonCapacity.strongProduct, SimpleGraph.strongPower]
    constructor
    · intro ⟨hne, hrest, hv⟩
      refine ⟨?_, fun i => ?_⟩
      · intro heq
        apply hne
        have h_init := congr_arg Fin.init heq
        rw [Fin.init_snoc, Fin.init_snoc] at h_init
        have h_last : v₁ = v₂ := by
          have := congr_fun heq (Fin.last n); rwa [Fin.snoc_last, Fin.snoc_last] at this
        exact Prod.ext (e.injective h_init) h_last
      · exact Fin.lastCases
          (by rw [Fin.snoc_last, Fin.snoc_last]; exact hv)
          (fun j => by
            rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            cases hrest with
            | inl heq => left; exact congrArg (fun r => e r j) heq
            | inr hadj => exact ((ih r₁ r₂).mp hadj).2 j) i
    · intro ⟨hne, hall⟩
      refine ⟨fun heq => hne (by cases heq; rfl), ?_, ?_⟩
      · by_cases heq : r₁ = r₂
        · exact Or.inl heq
        · exact Or.inr ((ih r₁ r₂).mpr ⟨fun h => heq (e.injective h),
            fun j => by
              have := hall (Fin.castSucc j); rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at this⟩)
      · have := hall (Fin.last n); rwa [Fin.snoc_last, Fin.snoc_last] at this

/-- Graph isomorphism between recInfProduct and strongPower.
    This bridges the left-recursive nested product representation used by
    `InfiniteGraphClass.npowRec` with the function-type representation. -/
def recInfProduct_iso_strongPower (G : InfiniteGraph) (m : ℕ) :
    (recInfProduct G m).graph ≃g strongPower G.graph m where
  toEquiv := recInfProduct_vertex_equiv G m
  map_rel_iff' := (recInfProduct_adj_iff G m _ _).symm

/-! ### Generic Cohom helpers

These are generic graph-cohom helpers (not infinite-graph-specific) but they
use `IsCohom.strongProduct_map_fst`/`_snd` which are declared downstream of
`Prerequisites/Cohomomorphism.lean` (in `AsymptoticSpectrum.lean`), so they
can't be moved further upstream without restructuring the IsCohom extension
theorems too. Kept here. -/

/-- Extract `Cohom` from a graph isomorphism (forward direction). -/
theorem cohom_of_relIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (iso : G ≃g H) : Cohom G H :=
  ⟨iso, fun _ _ hne hnadj =>
    ⟨iso.injective.ne hne, fun hadj => hnadj (iso.map_rel_iff'.mp hadj)⟩⟩

/-- Product of two cohomomorphisms on strong products. -/
theorem strongProduct_cohom_both {V₁ V₂ W₁ W₂ : Type*}
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h₁ : Cohom G₁ H₁) (h₂ : Cohom G₂ H₂) :
    Cohom (ShannonCapacity.strongProduct G₁ G₂)
      (ShannonCapacity.strongProduct H₁ H₂) := by
  obtain ⟨f₁, hf₁⟩ := h₁; obtain ⟨f₂, hf₂⟩ := h₂
  exact Cohom.trans
    ⟨Prod.map f₁ id, hf₁.strongProduct_map_fst⟩
    ⟨Prod.map id f₂, hf₂.strongProduct_map_snd⟩

set_option linter.flexible false in
/-- Merge two strong powers: G^n ⊠ G^m → G^(n+m) via `Fin.append`.
    Proof by contrapositive: adj in G^(n+m) ⟹ adj in G^n ⊠ G^m. -/
theorem strongPower_product_merge {V : Type*} (G : SimpleGraph V) (n m : ℕ) :
    Cohom (ShannonCapacity.strongProduct (strongPower G n) (strongPower G m))
      (strongPower G (n + m)) := by
  refine ⟨fun ⟨f, g⟩ => Fin.append f g, fun ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ hne hnadj => ?_⟩
  constructor
  · intro heq; apply hne; exact Prod.ext
      (funext fun i => by
        have := congr_fun heq (Fin.castAdd m i); simp [Fin.append] at this; exact this)
      (funext fun j => by
        have := congr_fun heq (Fin.natAdd n j); simp [Fin.append] at this; exact this)
  · intro ⟨_, hall⟩
    apply hnadj
    refine ⟨hne, ?_, ?_⟩
    · by_cases hf : f₁ = f₂
      · exact Or.inl hf
      · exact Or.inr ⟨hf, fun i => by
          have := hall (Fin.castAdd m i); simp [Fin.append] at this; exact this⟩
    · by_cases hg : g₁ = g₂
      · exact Or.inl hg
      · exact Or.inr ⟨hg, fun j => by
          have := hall (Fin.natAdd n j); simp [Fin.append] at this; exact this⟩

/-! ### Asymptotic Cohom for Infinite Graphs -/

/-- G ≲ H in the asymptotic preorder for infinite graphs. -/
def AsympCohomInf (G H : InfiniteGraph) : Prop :=
  AsymptoticSpectrumDuality.AsympRel infiniteGraphStrassenPreorder
    (InfiniteGraphClass.mk G) (InfiniteGraphClass.mk H)

/-- G and H are asymptotically equivalent: G ≲ H and H ≲ G. -/
def AsympCohomEquivInf (G H : InfiniteGraph) : Prop :=
  AsympCohomInf G H ∧ AsympCohomInf H G

end AsymptoticSpectrumDistance
