/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Upper Bounds via the Baumert Slicing Technique

This file is a thin umbrella module that re-exports the per-bridge files. It used
to contain `fiber_bound_clique`, the shared helpers, and all eleven Baumert
bridges in one 7858-line file; the bridges have been split out for faster
incremental builds.

## File structure

* `Section6UpperBoundsCommon` — shared infrastructure: `fiber_bound_clique`,
  `floor_val`, `fractionGraph_adj_translate`, the `alpha_*` lemmas, the
  `*_clique_E*` lemmas, `five_distinct_zmod13`, `ip_uniform13`.
* Each bridge file contains the bespoke helpers (`*_baumert_contradiction`,
  `layerFiber*`, `translate*`, `extract_*`, `crossNonAdj*_spec`, etc.) plus the
  public `alpha3_*_le` theorem for that bridge.

The chain-search files (`Section6UpperBoundsCase7`, `Section6UpperBoundsCase8`,
`Section6UpperBoundsInterval1`, `Section6UpperBoundsInterval2`,
`Section6UpperBoundsMixed*`) hold the `case*_check_true` `native_decide`
verifications and are imported by the corresponding bridge file.

## Method (recap)

The Baumert slicing technique proceeds:

1. Assume `α = α_nested_floor`.
2. Slice the IS into layers indexed by the first coordinate.
3. Derive layer-size constraints from `fiber_bound_clique`.
4. Solve the integer program to force specific layer sizes.
5. Enumerate max ISs of the layer graph and exhaustively search for valid chains.
6. Conclude no valid chain exists (verified by `native_decide`).

## References

[BMRRS] L. D. Baumert, R. J. McEliece, E. Rodemich, H. C. Rumsey, R. Stanley,
        H. Taylor, "A Combinatorial Packing Problem", 1971.

## Public theorems re-exported

* `Section6.fiber_bound_clique` — from `Section6UpperBoundsCommon`.
* `Section6.alpha3_5o2_5o2_8o3_le` — from `Section6UpperBoundsBridge5o2_5o2_8o3`.
* `Section6.alpha3_8o3_8o3_8o3_le` — from `Section6UpperBoundsBridge8o3_8o3_8o3`.
* `Section6.alpha3_7o3_7o3_7o3_le` — from `Section6UpperBoundsBridge73_73_73`.
* `Section6.alpha3_5o2_5o2_5o2_le` — from `Section6UpperBoundsBridge52_52_52`.
* `Section6.alpha3_5o2_8o3_8o3_le` — from `Section6UpperBoundsBridge52_83_83`.
* `Section6.alpha3_9o4_9o4_5o2_le` — from `Section6UpperBoundsBridge94_94_52`.
* `Section6.alpha3_9o4_9o4_8o3_le` — from `Section6UpperBoundsBridge94_94_83`.
* `Section6.alpha3_83_114_135_le` — from `Section6UpperBoundsBridge83_114_135`.
* `Section6.alpha3_114_114_135_le` — from `Section6UpperBoundsBridge114_114_135`.
* `Section6.alpha3_114_135_135_le` — from `Section6UpperBoundsBridge114_135_135`.
* `Section6.alpha3_83_83_114_le` — from `Section6UpperBoundsBridge83_83_114`.
* `Section6.alpha3_83_114_114_le` — from `Section6UpperBoundsBridge83_114_114`.
* `Section6.alpha3_52_52_114_le` — from `Section6UpperBoundsBridge52_52_114`.
* `Section6.alpha3_52_83_114_le` — from `Section6UpperBoundsBridge52_83_114`.
* `Section6.alpha3_52_114_114_le` — from `Section6UpperBoundsBridge52_114_114`.
-/
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsCommon
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge5o2_5o2_8o3
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge8o3_8o3_8o3
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge73_73_73
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge52_52_52
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge52_83_83
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge94_94_52
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge94_94_83
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge83_114_135
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge114_114_135
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge114_135_135
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge83_83_114
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge83_114_114
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge52_52_114
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge52_83_114
import AsymptoticSpectrumDistance.Section6.Section6UpperBoundsBridge52_114_114
