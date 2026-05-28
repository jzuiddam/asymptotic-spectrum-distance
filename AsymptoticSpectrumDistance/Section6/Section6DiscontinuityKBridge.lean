/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Bridges between `FracPair`/`FracTriple` and `FracTuple` infrastructures

Bridges `alpha2`/`alpha3` to `alphaK` and `IsDiscontinuity₂`/`IsDiscontinuity`
to `IsDiscontinuityK`. Then collapses 6 of the 12 paper cases
(`th:discont`, paper line 2806) into one-line corollaries of
`isDiscontinuityK_consInt` (the forward direction of `lem:disc-integer`).

## Bridges

* `alphaK_two` : `alphaK v = alpha2 v` for `v : FracTuple 2`.
* `alphaK_three` : `alphaK v = alpha3 v` for `v : FracTuple 3`.
* `isDiscontinuity₂_iff_isDiscontinuityK`, `isDiscontinuity_iff_isDiscontinuityK`.

## Case collapse (Theorem 6.9, integer-extension cases)

Cases 1–4 (all-integer): `(2, 2, 2), (2, 2, 3), (2, 3, 3), (3, 3, 3)` —
built from the empty tuple via three `consInt` applications.

Cases 5–6 (one-`5/2`-extension): `(2, 5/2, 5/2), (5/2, 5/2, 3)` — built
from `α₂(5/2, 5/2)` disc via one `consInt` (+ `isDiscontinuityK_perm` for
the second case).
-/
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityK
import AsymptoticSpectrumDistance.Section6.Section6Discontinuity

open ShannonCapacity AsymptoticSpectrumGraphs

namespace Section6

/-! ## C2.2: bridges `alphaK_two` / `alphaK_three` -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK v = alpha2 v` for `v : FracTuple 2`. Chains `bigStrongProduct_succ_iso`
    twice + `bigStrongProduct_zero_iso` + `strongProduct_botPUnit_right_iso`. -/
theorem alphaK_two (v : FracTuple 2) : alphaK v = alpha2 v := by
  unfold alphaK alpha2
  rw [SimpleGraph.independenceNumber_iso
    (bigStrongProduct_succ_iso (fun i : Fin 2 => fractionGraph (v i).1 (v i).2))]
  rw [indepNum_strongProduct_right_iso _
    (bigStrongProduct_succ_iso (fun i : Fin 1 => fractionGraph (v i.succ).1 (v i.succ).2))]
  rw [indepNum_strongProduct_right_iso _ (strongProduct_right_iso _
    (bigStrongProduct_zero_iso.{0,0}
      (fun i : Fin 0 => fractionGraph (v i.succ.succ).1 (v i.succ.succ).2)))]
  rw [indepNum_strongProduct_right_iso _ (strongProduct_botPUnit_right_iso.{0,0} _)]
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- `alphaK v = alpha3 v` for `v : FracTuple 3`. Chains as in `alphaK_two` plus
    one more `succ_iso` peeling, finishing with `← indepNum_strongProduct_assoc`
    to convert the right-associated form to the left-associated form used by
    `alpha3`. -/
theorem alphaK_three (v : FracTuple 3) : alphaK v = alpha3 v := by
  unfold alphaK alpha3
  rw [SimpleGraph.independenceNumber_iso
    (bigStrongProduct_succ_iso (fun i : Fin 3 => fractionGraph (v i).1 (v i).2))]
  rw [indepNum_strongProduct_right_iso _
    (bigStrongProduct_succ_iso (fun i : Fin 2 => fractionGraph (v i.succ).1 (v i.succ).2))]
  rw [indepNum_strongProduct_right_iso _ (strongProduct_right_iso _
    (bigStrongProduct_succ_iso
      (fun i : Fin 1 => fractionGraph (v i.succ.succ).1 (v i.succ.succ).2)))]
  rw [indepNum_strongProduct_right_iso _ (strongProduct_right_iso _
    (strongProduct_right_iso _ (bigStrongProduct_zero_iso.{0,0}
      (fun i : Fin 0 => fractionGraph (v i.succ.succ.succ).1 (v i.succ.succ.succ).2))))]
  rw [indepNum_strongProduct_right_iso _ (strongProduct_right_iso _
    (strongProduct_botPUnit_right_iso.{0,0} _))]
  rw [← indepNum_strongProduct_assoc]
  rfl

/-! ## Bridges between `IsDiscontinuity₂`/`IsDiscontinuity` and `IsDiscontinuityK`

`Valid₂` ↔ `ValidK`, `ltPerm₂` ↔ `ltPermK`, `Valid` ↔ `ValidK`, `ltPerm` ↔
`ltPermK` are all definitionally equal (both unfold to the same expressions
in their respective namespaces). The only non-trivial step is the bridge
`alpha2`/`alpha3` ↔ `alphaK` from above. -/

theorem isDiscontinuity₂_iff_isDiscontinuityK (v : FracPair) :
    IsDiscontinuity₂ v ↔ IsDiscontinuityK v := by
  constructor
  · intro h u hu_valid hlt
    have h_alpha := h u hu_valid hlt
    rwa [← alphaK_two u, ← alphaK_two v] at h_alpha
  · intro h u hu_valid hlt
    have h_alpha := h u hu_valid hlt
    rwa [alphaK_two u, alphaK_two v] at h_alpha

theorem isDiscontinuity_iff_isDiscontinuityK (v : FracTriple) :
    IsDiscontinuity v ↔ IsDiscontinuityK v := by
  constructor
  · intro h u hu_valid hlt
    have h_alpha := h u hu_valid hlt
    rwa [← alphaK_three u, ← alphaK_three v] at h_alpha
  · intro h u hu_valid hlt
    have h_alpha := h u hu_valid hlt
    rwa [alphaK_three u, alphaK_three v] at h_alpha

/-! ## C4: Theorem 6.9 cases 1–6 from `lem:disc-integer`

The six "integer-extension" cases of paper Theorem 6.9 (line 2806) are now
one-line corollaries of `isDiscontinuityK_consInt` applied to either:
* the vacuous α_0-disc (cases 1–4: pure integer tuples);
* α₂(5/2, 5/2)-disc (cases 5–6, the latter via `isDiscontinuityK_perm`).

This demonstrates the value of formalizing `lem:disc-integer` at full `k`-generality:
the case analysis the paper distributes across §6 collapses into chained `consInt`. -/

/-- α_0 is vacuously a discontinuity (the only `FracTuple 0` is empty). -/
theorem isDiscontinuityK_empty : IsDiscontinuityK (![] : FracTuple 0) := by
  intro u _ hlt
  exact absurd ⟨1, fun i => i.elim0⟩ hlt.2

/-- α₁(n) = n is a discontinuity for any integer `n ≥ 2`.
    Derived as `consInt n` of the vacuous α_0-disc. -/
theorem alphaK_one_n_isDiscontinuity (n : ℕ+) (hn : 2 ≤ n) :
    IsDiscontinuityK (consInt n (![] : FracTuple 0)) :=
  isDiscontinuityK_consInt n hn (fun i => i.elim0) isDiscontinuityK_empty

/-! ### Cases 1–4: pure integer triples -/

/-- Case 1 (paper line 2821): `α₃(2, 2, 2) = 8` is a discontinuity. -/
theorem alphaK_222_isDiscontinuityK :
    IsDiscontinuityK (consInt 2 (consInt 2 (consInt 2 (![] : FracTuple 0)))) := by
  refine isDiscontinuityK_consInt 2 (by decide) ?_ ?_
  · exact consInt_validK 2 (by decide) (consInt_validK 2 (by decide) (fun i => i.elim0))
  · exact isDiscontinuityK_consInt 2 (by decide)
      (consInt_validK 2 (by decide) (fun i => i.elim0))
      (isDiscontinuityK_consInt 2 (by decide) (fun i => i.elim0) isDiscontinuityK_empty)

/-- Case 2 (paper line 2822): `α₃(2, 2, 3) = 12` is a discontinuity. -/
theorem alphaK_223_isDiscontinuityK :
    IsDiscontinuityK (consInt 2 (consInt 2 (consInt 3 (![] : FracTuple 0)))) := by
  refine isDiscontinuityK_consInt 2 (by decide) ?_ ?_
  · exact consInt_validK 2 (by decide) (consInt_validK 3 (by decide) (fun i => i.elim0))
  · exact isDiscontinuityK_consInt 2 (by decide)
      (consInt_validK 3 (by decide) (fun i => i.elim0))
      (isDiscontinuityK_consInt 3 (by decide) (fun i => i.elim0) isDiscontinuityK_empty)

/-- Case 3 (paper line 2823): `α₃(2, 3, 3) = 18` is a discontinuity. -/
theorem alphaK_233_isDiscontinuityK :
    IsDiscontinuityK (consInt 2 (consInt 3 (consInt 3 (![] : FracTuple 0)))) := by
  refine isDiscontinuityK_consInt 2 (by decide) ?_ ?_
  · exact consInt_validK 3 (by decide) (consInt_validK 3 (by decide) (fun i => i.elim0))
  · exact isDiscontinuityK_consInt 3 (by decide)
      (consInt_validK 3 (by decide) (fun i => i.elim0))
      (isDiscontinuityK_consInt 3 (by decide) (fun i => i.elim0) isDiscontinuityK_empty)

/-- Case 4 (paper line 2826): `α₃(3, 3, 3) = 27` is a discontinuity. -/
theorem alphaK_333_isDiscontinuityK :
    IsDiscontinuityK (consInt 3 (consInt 3 (consInt 3 (![] : FracTuple 0)))) := by
  refine isDiscontinuityK_consInt 3 (by decide) ?_ ?_
  · exact consInt_validK 3 (by decide) (consInt_validK 3 (by decide) (fun i => i.elim0))
  · exact isDiscontinuityK_consInt 3 (by decide)
      (consInt_validK 3 (by decide) (fun i => i.elim0))
      (isDiscontinuityK_consInt 3 (by decide) (fun i => i.elim0) isDiscontinuityK_empty)

/-! ### Cases 5–6: one-`5/2`-extension via α₂(5/2, 5/2) -/

/-- Bridge `alpha2(5/2, 5/2)`-disc to `IsDiscontinuityK` form. -/
theorem alphaK_pair5o2_5o2_isDiscontinuityK : IsDiscontinuityK pair5o2_5o2 :=
  (isDiscontinuity₂_iff_isDiscontinuityK pair5o2_5o2).mp alpha2_5o2_5o2_isDiscontinuity

/-- ValidK for `pair5o2_5o2`. -/
private lemma validK_pair5o2_5o2 : ValidK pair5o2_5o2 := by
  intro i; fin_cases i <;> decide

/-- Case 5 (paper line 2824): `α₃(2, 5/2, 5/2) = 10` is a discontinuity. -/
theorem alphaK_2_5o2_5o2_isDiscontinuityK :
    IsDiscontinuityK (consInt 2 pair5o2_5o2) :=
  isDiscontinuityK_consInt 2 (by decide) validK_pair5o2_5o2
    alphaK_pair5o2_5o2_isDiscontinuityK

/-- `α₃(3, 5/2, 5/2)` is a discontinuity (intermediate). -/
private theorem alphaK_3_5o2_5o2_isDiscontinuityK :
    IsDiscontinuityK (consInt 3 pair5o2_5o2) :=
  isDiscontinuityK_consInt 3 (by decide) validK_pair5o2_5o2
    alphaK_pair5o2_5o2_isDiscontinuityK

/-- Case 6 (paper line 2825): `α₃(5/2, 5/2, 3) = 15` is a discontinuity.
    Derived from `α₃(3, 5/2, 5/2)` by swapping slots 0 and 2. -/
theorem alphaK_5o2_5o2_3_isDiscontinuityK :
    IsDiscontinuityK ((consInt 3 pair5o2_5o2) ∘ Equiv.swap (0 : Fin 3) 2) :=
  (isDiscontinuityK_perm (Equiv.swap (0 : Fin 3) 2)).mp alphaK_3_5o2_5o2_isDiscontinuityK

/-! ### α₂-disc cases (paper §6 line 2778)

The α₂ disc tuples `(2, 2), (2, 3), (3, 3)` are integer-extensions of α₁.
They collapse via `consInt` from the vacuous α₀-disc. -/

theorem alphaK_22_isDiscontinuityK :
    IsDiscontinuityK (consInt 2 (consInt 2 (![] : FracTuple 0))) :=
  isDiscontinuityK_consInt 2 (by decide)
    (consInt_validK 2 (by decide) (fun i => i.elim0))
    (alphaK_one_n_isDiscontinuity 2 (by decide))

theorem alphaK_23_isDiscontinuityK :
    IsDiscontinuityK (consInt 2 (consInt 3 (![] : FracTuple 0))) :=
  isDiscontinuityK_consInt 2 (by decide)
    (consInt_validK 3 (by decide) (fun i => i.elim0))
    (alphaK_one_n_isDiscontinuity 3 (by decide))

theorem alphaK_33_isDiscontinuityK :
    IsDiscontinuityK (consInt 3 (consInt 3 (![] : FracTuple 0))) :=
  isDiscontinuityK_consInt 3 (by decide)
    (consInt_validK 3 (by decide) (fun i => i.elim0))
    (alphaK_one_n_isDiscontinuity 3 (by decide))

/-! ### Existing α₂-disc theorems on `FracPair` rederived from K-form -/

theorem alpha2_22_isDiscontinuity : IsDiscontinuity₂ pair22 :=
  (isDiscontinuity₂_iff_isDiscontinuityK pair22).mpr alphaK_22_isDiscontinuityK

theorem alpha2_23_isDiscontinuity : IsDiscontinuity₂ pair23 :=
  (isDiscontinuity₂_iff_isDiscontinuityK pair23).mpr alphaK_23_isDiscontinuityK

theorem alpha2_33_isDiscontinuity : IsDiscontinuity₂ pair33 :=
  (isDiscontinuity₂_iff_isDiscontinuityK pair33).mpr alphaK_33_isDiscontinuityK

/-! ## C4 (continued): the existing α₃-disc theorems on `FracTriple` rederived

The 6 paper cases above give `IsDiscontinuityK` on `consInt`-built tuples;
here we re-state them on the existing `triple222`-style `FracTriple` values
(via the `IsDiscontinuity ↔ IsDiscontinuityK` bridge). The defeq
`triple222 = consInt 2 (consInt 2 (consInt 2 (![] : FracTuple 0)))` etc.
makes these one-liners. -/

theorem alpha3_222_isDiscontinuity : IsDiscontinuity triple222 :=
  (isDiscontinuity_iff_isDiscontinuityK triple222).mpr alphaK_222_isDiscontinuityK

theorem alpha3_223_isDiscontinuity : IsDiscontinuity triple223 :=
  (isDiscontinuity_iff_isDiscontinuityK triple223).mpr alphaK_223_isDiscontinuityK

theorem alpha3_233_isDiscontinuity : IsDiscontinuity triple233 :=
  (isDiscontinuity_iff_isDiscontinuityK triple233).mpr alphaK_233_isDiscontinuityK

theorem alpha3_333_isDiscontinuity : IsDiscontinuity triple333 :=
  (isDiscontinuity_iff_isDiscontinuityK triple333).mpr alphaK_333_isDiscontinuityK

theorem alpha3_2_5o2_5o2_isDiscontinuity : IsDiscontinuity triple_2_5o2_5o2 :=
  (isDiscontinuity_iff_isDiscontinuityK triple_2_5o2_5o2).mpr
    alphaK_2_5o2_5o2_isDiscontinuityK

theorem alpha3_5o2_5o2_3_isDiscontinuity : IsDiscontinuity triple_5o2_5o2_3 := by
  have heq : triple_5o2_5o2_3 = (consInt 3 pair5o2_5o2) ∘ Equiv.swap (0 : Fin 3) 2 := by
    funext i
    fin_cases i <;> decide
  rw [isDiscontinuity_iff_isDiscontinuityK, heq]
  exact alphaK_5o2_5o2_3_isDiscontinuityK

end Section6
