/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Per-candidate `α₃` bounds (Nat-arithmetic forms)

For the `native_decide` enumeration in `Section6DiscontinuityKConverse`, we
need `α₃` bounds expressed in `ℕ` arithmetic. This file provides
`nestedFloor3Nat` — the nested-floor upper bound for `α₃` in pure `ℕ` form —
and proves it equals the `ℝ`-valued nested floor from
`Section6NestedFloor.lean`, hence is a valid α₃ upper bound.

`nestedFloor3Nat` is **tight** for 4 of the 6 non-integer disc cases:
* `(9/4, 7/3, 5/2)` — `nestedFloor3Nat = 9`.
* `(11/5, 11/4, 11/4)` — `nestedFloor3Nat = 11`.
* `(11/4, 11/4, 11/4)` — `nestedFloor3Nat = 13`.
* `(14/5, 14/5, 14/5)` — `nestedFloor3Nat = 14`.

For the 2 non-tight cases (`(5/2, 5/2, 8/3)` and `(8/3, 8/3, 8/3)`), the
existing chain-search bounds in `Section6UpperBoundsCase7.lean` and
`Section6UpperBoundsCase8.lean` give the
tight values (11 and 12); the bridge to this enumeration framework is
provided by the bridge files `Section6UpperBoundsBridge*.lean`.

## Main results

* `nestedFloor3Nat (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ) : ℕ` — pure ℕ-arithmetic.
* `nestedFloor3Nat_eq` — equals the ℝ-valued nested floor.
* `alpha3_le_nestedFloor3Nat` — α₃ upper bound in ℕ.
-/

import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityKCandidates
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor
import Mathlib.Algebra.Order.Floor.Semifield

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## ℕ-arithmetic nested floor for `α₃` -/

/-- `α₃` upper bound in pure ℕ arithmetic: `⌊⌊⌊p₃/q₃⌋ p₂/q₂⌋ p₁/q₁⌋`. -/
def nestedFloor3Nat (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ) : ℕ :=
  (p₁ * ((p₂ * (p₃ / q₃)) / q₂)) / q₁

/-- The ℕ-arithmetic nested floor equals the ℝ-valued one. -/
theorem nestedFloor3Nat_eq (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ) :
    nestedFloor3Nat p₁ q₁ p₂ q₂ p₃ q₃ =
      ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂ * ⌊(p₃ : ℝ) / q₃⌋₊⌋₊⌋₊ := by
  unfold nestedFloor3Nat
  rw [Nat.floor_div_eq_div]
  rw [show ((p₂ : ℝ) / q₂ * (p₃ / q₃ : ℕ) : ℝ) =
       ((p₂ * (p₃ / q₃) : ℕ) : ℝ) / q₂ from by push_cast; ring]
  rw [Nat.floor_div_eq_div]
  rw [show ((p₁ : ℝ) / q₁ * (p₂ * (p₃ / q₃) / q₂ : ℕ) : ℝ) =
       ((p₁ * (p₂ * (p₃ / q₃) / q₂) : ℕ) : ℝ) / q₁ from by push_cast; ring]
  rw [Nat.floor_div_eq_div]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α₃ upper bound in ℕ: the right-associated strong product's indepNum is at
    most the ℕ-arithmetic nested floor. Direct corollary of `nested_floor_three`
    + `nestedFloor3Nat_eq`. -/
theorem alpha3_le_nestedFloor3Nat
    (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ) [NeZero p₁] [NeZero p₂] [NeZero p₃]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂)
    (hq₃ : 0 < q₃) (h2q₃ : 2 * q₃ ≤ p₃) :
    (strongProduct (fractionGraph p₁ q₁)
        (strongProduct (fractionGraph p₂ q₂) (fractionGraph p₃ q₃))).indepNum ≤
      nestedFloor3Nat p₁ q₁ p₂ q₂ p₃ q₃ := by
  rw [nestedFloor3Nat_eq]
  exact nested_floor_three p₁ q₁ p₂ q₂ p₃ q₃ hq₁ h2q₁ hq₂ h2q₂ hq₃ h2q₃

/-! ## D3b: comparison and min-over-perms — Bool predicates for `native_decide`. -/

/-- `(p₁, q₁) ≤ (p₂, q₂)` as rationals, computed in `ℕ`. -/
def lePairNat (a b : ℕ × ℕ) : Bool := a.1 * b.2 ≤ b.1 * a.2

/-- Multiset-`≤` on `(ℕ × ℕ)` triples: some perm of `u` is pointwise `≤ v`. -/
def lePermNat (u v : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  let ⟨a, b, c⟩ := u
  let ⟨x, y, z⟩ := v
  (lePairNat a x && lePairNat b y && lePairNat c z) ||
  (lePairNat a x && lePairNat c y && lePairNat b z) ||
  (lePairNat b x && lePairNat a y && lePairNat c z) ||
  (lePairNat b x && lePairNat c y && lePairNat a z) ||
  (lePairNat c x && lePairNat a y && lePairNat b z) ||
  (lePairNat c x && lePairNat b y && lePairNat a z)

/-- Strict multiset-`<`: `lePermNat` and not the reverse. -/
def ltPermNat (u v : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  lePermNat u v && !lePermNat v u

/-- Min over the 6 permutations of `nestedFloor3Nat`. Tightest nested-floor
    upper bound on `α₃(p₁/q₁, p₂/q₂, p₃/q₃)`. -/
def nestedFloor3NatMin (u : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  let ⟨a, b, c⟩ := u
  min (min (min (nestedFloor3Nat a.1 a.2 b.1 b.2 c.1 c.2)
                (nestedFloor3Nat a.1 a.2 c.1 c.2 b.1 b.2))
            (min (nestedFloor3Nat b.1 b.2 a.1 a.2 c.1 c.2)
                (nestedFloor3Nat b.1 b.2 c.1 c.2 a.1 a.2)))
       (min (nestedFloor3Nat c.1 c.2 a.1 a.2 b.1 b.2)
            (nestedFloor3Nat c.1 c.2 b.1 b.2 a.1 a.2))

end Section6
