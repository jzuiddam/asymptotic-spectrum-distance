/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Cyclic distance modulo p

This module defines the `distMod` family — the cyclic ("shortest-arc") distance
between two elements of `ZMod p` — and proves the basic properties used by the
fraction-graph constructions in `Prerequisites/FractionGraph.lean` (and
re-exported via `Prerequisites/ShannonCapacity.lean`).

The definitions live in `namespace FractionGraphBasic` so that downstream
modules can either `open FractionGraphBasic` or pick up the names through the
existing `export` re-routes in those files.
-/

namespace FractionGraphBasic

/-- Distance modulo p between two elements of ZMod p -/
def distMod (p : ℕ) [NeZero p] (u v : ZMod p) : ℕ :=
  let d := ((u - v).val : ℕ)
  min d (p - d)

/-- distMod equals valMinAbs.natAbs from Mathlib.Data.ZMod.ValMinAbs -/
theorem distMod_eq_valMinAbs_natAbs (p : ℕ) [NeZero p] (u v : ZMod p) :
    distMod p u v = (u - v).valMinAbs.natAbs :=
  (ZMod.valMinAbs_natAbs_eq_min (u - v)).symm

/-- distMod is symmetric -/
theorem distMod_comm (p : ℕ) [NeZero p] (u v : ZMod p) : distMod p u v = distMod p v u := by
  simp only [distMod_eq_valMinAbs_natAbs, show v - u = -(u - v) by ring]
  exact (ZMod.natAbs_valMinAbs_neg (u - v)).symm

/-- distMod is translation invariant -/
lemma distMod_add_left (p : ℕ) [NeZero p] (c u v : ZMod p) :
    distMod p (c + u) (c + v) = distMod p u v := by
  simp only [distMod]
  have h : (c + u) - (c + v) = u - v := by ring
  rw [h]

/-- Helper: if span ∈ [q, p - q], then min(span, p - span) ≥ q -/
lemma min_span_ge_q_of_in_range (p q span : ℕ) (hq_le : q ≤ span) (hspan_le : span ≤ p - q) :
    min span (p - span) ≥ q := by
  have hp_sub : p - span ≥ q := by omega
  exact le_min hq_le hp_sub

end FractionGraphBasic
