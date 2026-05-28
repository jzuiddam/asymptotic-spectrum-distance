# Asymptotic Spectrum Distance

Lean 4 formalization of **"The asymptotic spectrum distance, graph limits, and the Shannon capacity"** by David de Boer, Pjotr Buys and Jeroen Zuiddam, 
[arXiv:2404.16763](https://arxiv.org/abs/2404.16763)

## Main results

The paper's main results are stated as 60 `main_*` theorems in
[`AsymptoticSpectrumDistance/Main.lean`](AsymptoticSpectrumDistance/Main.lean).

## Formalised bounds

As part of the formalisation, we formalised the currently best lower bounds on the Shannon capacity of small odd cycles, including our new lower bound for the fifteen-cycle.

| `n` | `Θ(C_n) ≥` | Reference | Theorem |
|---:|---|---|---|
| 5  | `√5` ≈ 2.236              | Shannon 1956 (matched by Lovász 1979)           | `main_shannon_C5`  |
| 7  | `367^{1/5}` ≈ 3.252       | Polak–Schrijver 2019                            | `main_shannon_C7`  |
| 9  | `81^{1/3}` ≈ 4.327        | Baumert, McEliece, Rodemich, Rumsey, Stanley, Taylor (1971) | `main_shannon_C9`  |
| 11 | `148^{1/3}` ≈ 5.290       | Baumert et al. 1971                             | `main_shannon_C11` |
| 13 | `247^{1/3}` ≈ 6.274       | Baumert et al. 1971                             | `main_shannon_C13` |
| 15 | `2842^{1/4}` ≈ 7.301       | **this paper** (de Boer–Buys–Zuiddam, Theorem 6.2) | `main_indepNum_C15_fourth` |

The C₁₅ bound is the new best-known result from the paper being
formalized; it improves on the prior `382^{1/3}` ≈ 7.256
(Codenotti–Gerace–Resta; Polak–Schrijver), also formalized here
(`main_indepNum_C15_cube`).

We also formaly verify our results on the discontinuity points of the independence number on products of fraction graphs, which in the paper rely on optimization software. We formalised:

**Theorem 6.9.** Let `α₃(r₁, r₂, r₃) := α(E_{r₁} ⊠ E_{r₂} ⊠ E_{r₃})` be
the independence number of the strong product of three fraction graphs.
On rational triples in `[2, 3]³`, the discontinuities of `α₃` are exactly
the following 12 triples (up to permutation of slots):

| # | Tuple | α₃ |   | # | Tuple | α₃ |
|---|---|---:|---|---|---|---:|
| 1 | (2, 2, 2)         |  8 |   |  7 | (5/2, 5/2, 8/3)    | 11 |
| 2 | (2, 2, 3)         | 12 |   |  8 | (8/3, 8/3, 8/3)    | 12 |
| 3 | (2, 3, 3)         | 18 |   |  9 | (9/4, 7/3, 5/2)    |  9 |
| 4 | (3, 3, 3)         | 27 |   | 10 | (11/5, 11/4, 11/4) | 11 |
| 5 | (2, 5/2, 5/2)     | 10 |   | 11 | (11/4, 11/4, 11/4) | 13 |
| 6 | (5/2, 5/2, 3)     | 15 |   | 12 | (14/5, 14/5, 14/5) | 14 |

Theorem: `main_theorem_6_9` in `Main.lean`.

## Building

Requires Lean 4 (toolchain version pinned in `lean-toolchain`).

```bash
lake exe cache get   # download Mathlib cache
lake build           # build all modules
```

**Build time.** A clean build (`lake clean && lake exe cache get && lake build`)
takes ~40 minutes wall time on a 16-core machine. Time is dominated by
~75 `native_decide` checks in `Section6/` for independence-number
computations on 64–135-vertex graphs; the largest are split into parallel
chunks. Memory peak ~3.5 GB.

## Module overview

All paths below are under the `AsymptoticSpectrumDistance/` Lean package.

### Core (paper results)

| Directory | Contents |
|---|---|
| `Section2/` | Asymptotic spectrum distance definition, metric properties, Shannon capacity bound, vertex-transitive covering lemma |
| `Section3/` | Fraction graphs, vertex removal, convergence theorems |
| `Section4/` | Circle graphs as infinite limit points |
| `Section5/` | Convex-round graphs, self-cohomomorphisms, non-equivalence of open/closed circle graphs |
| `Section6/` | Independent sets in products of fraction graphs, Theorem 6.9, upper bound computations |
| `CycleGraphBounds/` | Concrete Shannon capacity lower bounds for C₅, C₇, C₉, C₁₁, C₁₃, C₁₅ |

### Prerequisites

| Path | Contents |
|---|---|
| `Prerequisites/AsymptoticSpectrumDuality/` | Asymptotic spectra and duality theory |
| `Prerequisites/AsymptoticSpectrumGraphs/` | Graph semiring, Strassen preorder, specialization to graphs |
| `Prerequisites/AsymptoticSpectrumInfiniteGraphs/` | Extension to infinite graphs |
| `Prerequisites/ConeProgrammingDuality/` | Cone programming, LP duality, SDP duality |
| `Prerequisites/FractionGraph.lean` | Fraction graph definitions used in the prerequisites |
| `Prerequisites/InducedSubgraphBound.lean` | Bound on spectral values of induced subgraphs |
| `Prerequisites/LovaszTheta/` | Lovász theta function: orthonormal-rep definition, Kronecker tensor product, multiplicativity (≤ direction), monotonicity |
| `Prerequisites/ShannonCapacity.lean` | Shannon capacity basics |

## License

Apache 2.0

## Acknowledgements

This formalization was developed with the assistance of [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp).
