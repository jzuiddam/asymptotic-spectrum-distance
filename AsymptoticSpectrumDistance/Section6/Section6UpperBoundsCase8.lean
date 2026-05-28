/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Case 8 Computational Check: α(E_{8/3}³) ≠ 13

Exhaustive layer search verifying that no valid 8-layer configuration with
sizes (1,2,1,2,2,1,2,2) exists in E_{8/3}². This rules out α = 13
(the nested floor bound), establishing α ≤ 12.

This is directly analogous to the proof of [BMRRS, Lemma 3] (α(C₁₃³) ≤ 252),
which slices into 13 layers, derives forced packing sizes, and obtains a
structural contradiction.

[BMRRS] L. D. Baumert, R. J. McEliece, E. Rodemich, H. C. Rumsey, R. Stanley,
        H. Taylor, "A Combinatorial Packing Problem", 1971.

See `Section6UpperBounds.lean` for the full method description and how this
computational check fits into the overall proof.

## Architecture: 4-way chunked native_decide

The single `native_decide` over the 8-layer search runs ~26 min wall on a
fast machine. We split the outer `v0` loop into four chunks across companion
files `Section6UpperBoundsCase8_Chunk{1,2,3,4}.lean`, each carrying its own
`native_decide`. Lake compiles them in parallel; this file aggregates the four
chunk lemmas into the original `case8_check_true`. Shared helpers
(graph predicates, `innerSearch_v0_case8`, chunk lists, partition proof)
live in `Section6UpperBoundsCase8_Common.lean`.

## Main result

- `case8_check_true`: the case 8 Baumert layer search returns `true`
-/

import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase8_Common
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase8_Chunk1
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase8_Chunk2
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase8_Chunk3
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCase8_Chunk4

set_option linter.style.nativeDecide false

namespace Section6

/-! ## Case 8: α(E_{8/3}³) ≤ 12

**Context**: The nested floor bound (iterated [BMRRS, Lemma 2]) gives α ≤ 13.
We rule out α = 13 by the slicing technique of [BMRRS, Lemma 3].

**Graph**: E_{8/3}³ has 8³ = 512 vertices. Slicing by the first E_{8/3} coordinate
gives 8 layers in E_{8/3}² (64 vertices each). Since α(E_{8/3}²) = 5 (from
`theorem_6_5`), and each 3-clique {i,i+1,i+2} of E_{8/3} gives a fiber constraint
|Sᵢ| + |Sᵢ₊₁| + |Sᵢ₊₂| ≤ 5, the integer program with total 13 and 8 clique
constraints (sum 3·13 = 39 ≤ 8·5 = 40, slack 1) forces the unique solution
(1,2,1,2,2,1,2,2) up to rotation of Z₈.

By vertex-transitivity of E_{8/3} (the cyclic group Z₈ acts by translation),
WLOG the sizes are exactly (1,2,1,2,2,1,2,2).

**Exhaustive search**: We verify by backtracking that no valid assignment of
vertices to layers exists with these sizes, checking cross-layer non-adjacency
for all pairs in adjacent layers (distance 1 or 2 in E_{8/3}).

This is directly analogous to [BMRRS, Lemma 3]: "Any packing of the 13³-torus
may be considered to be the juxtaposition of 13 packings of the 13²-torus.
Since at most 39 2²-cubes fit in the 13²-torus, this implies that 253 can only
be achieved by using twelve packings of size 39 together with one of size 38." -/

/-- Case 8 Baumert layer search: no valid 8-layer configuration with sizes
    (1,2,1,2,2,1,2,2) exists in E_{8/3}².

    The variables v0,...,v71 represent vertices assigned to layers 0-7 with
    sizes (1,2,1,2,2,1,2,2). For size-2 layers, `enc83` ordering breaks
    symmetry. The `compatWith83` checks enforce that every vertex is
    non-adjacent (in E_{8/3}²) to all vertices in layers at E_{8/3}-distance
    1 or 2. For example, layer 7 (size 2) must be compatible with layers
    5,6,0,1 (at distance 1 or 2 in Z₈ mod 8).

    This is the computational heart of the argument, analogous to the exhaustive
    search in [BMRRS, Computation] and the structural contradiction in
    [BMRRS, Lemma 3].

    Implementation note: defined as `!(verts83.any innerSearch_v0_case8)`
    rather than an inline nested-`vs.any` closure, so the chunked combining
    proof does not need to perform deep defeq on the full 13-level nesting.
    Downstream callers that previously did `unfold case8_check` now need an
    additional `unfold innerSearch_v0_case8` step. -/
def case8_check : Bool :=
  !(verts83.any innerSearch_v0_case8)

theorem case8_check_true : case8_check = true := by
  have h1 : vs_chunk1_case8.any innerSearch_v0_case8 = false := by
    have := case8_chunk1_true
    simpa [case8_chunk1, Bool.not_eq_true'] using this
  have h2 : vs_chunk2_case8.any innerSearch_v0_case8 = false := by
    have := case8_chunk2_true
    simpa [case8_chunk2, Bool.not_eq_true'] using this
  have h3 : vs_chunk3_case8.any innerSearch_v0_case8 = false := by
    have := case8_chunk3_true
    simpa [case8_chunk3, Bool.not_eq_true'] using this
  have h4 : vs_chunk4_case8.any innerSearch_v0_case8 = false := by
    have := case8_chunk4_true
    simpa [case8_chunk4, Bool.not_eq_true'] using this
  unfold case8_check
  rw [← chunks_partition_case8, List.any_append, List.any_append,
      List.any_append, h1, h2, h3, h4]
  rfl

end Section6
