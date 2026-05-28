/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticSpectrumDistance.Section5.SelfCohomContinuity
import AsymptoticSpectrumDistance.Section6.Section6DiscontinuityAlpha2Converse
import AsymptoticSpectrumDistance.CycleGraphBounds.C5Bound
import AsymptoticSpectrumDistance.CycleGraphBounds.C7Bound
import AsymptoticSpectrumDistance.CycleGraphBounds.C9Bound
import AsymptoticSpectrumDistance.CycleGraphBounds.C11Bound
import AsymptoticSpectrumDistance.CycleGraphBounds.C13Bound
import AsymptoticSpectrumDistance.CycleGraphBounds.C15ThirdPower
import AsymptoticSpectrumDistance.CycleGraphBounds.C15IndependentSetFast

/-!
# The Asymptotic Spectrum Distance, Graph Limits, and the Shannon Capacity

Formalization of the paper by de Boer, Buys, and Zuiddam (arXiv:2404.16763).
-/

/-! ## Section 2: The asymptotic spectrum distance -/

namespace AsymptoticSpectrumDistance

open AsymptoticSpectrumGraphs AsymptoticSpectrumInfiniteGraphs SimpleGraph FractionGraphBasic
  Filter Topology

/-- **Definition 2.4 + Remark 2.5** (`def:dist`): the asymptotic spectrum
    distance is a pseudometric. -/
theorem main_asympSpecDistance_pseudometric :
    (∀ G : Graph, asympSpecDistance G G = 0) ∧
    (∀ G H : Graph, asympSpecDistance G H = asympSpecDistance H G) ∧
    (∀ G H K : Graph,
      asympSpecDistance G K ≤ asympSpecDistance G H + asympSpecDistance H K) :=
  ⟨asympSpecDistance_self,
   asympSpecDistance_symm,
   asympSpecDistance_triangle⟩

/-- **Lemma 2.7** (`lem:Theta-conv`): Shannon capacity is 1-Lipschitz in the
    asymptotic spectrum distance. -/
theorem main_shannonCapacity_lipschitz (G H : Graph) :
    |shannonCapacity G - shannonCapacity H| ≤ asympSpecDistance G H :=
  shannonCapacity_dist_le G H

/-- **Lemma 2.8** (`lem:alt-charac`): characterization of `d(G, H) ≤ a/b` by
    the existence of cohomomorphisms `E_b ⊠ G ≲ (E_b ⊠ H) ⊔ E_a` and
    `E_b ⊠ H ≲ (E_b ⊠ G) ⊔ E_a` (with `E_n` the edgeless graph on `n` vertices). -/
theorem main_alt_characterization (G H : Graph) (a : ℕ) (b : ℕ+) :
    asympSpecDistance G H ≤ (a : ℝ) / b ↔
    ((EdgelessGraph b ⊠ G) ≲ ((EdgelessGraph b ⊠ H) ⊔ᴳ EdgelessGraph a)) ∧
    ((EdgelessGraph b ⊠ H) ≲ ((EdgelessGraph b ⊠ G) ⊔ᴳ EdgelessGraph a)) :=
  asympSpecDistance_alt_char G H a b b.pos

/-! ## Section 3: Fraction graphs and convergence -/

/-- **Theorem 3.6** (`th:vrm`): vertex-removal bounds
    `φ(E_{p₂/q₂}) ≤ φ(E_{p/q}) ≤ p/(p−1) · φ(E_{p₂/q₂})` for `φ ∈ X`. -/
theorem main_vertex_removal_bounds (p q p₂ q₂ : ℕ+)
    (h2q₂ : 2 * q₂ ≤ p₂) (hq₂_lt : q₂ < q)
    (heq : (p : ℕ) * q₂ - q * p₂ = 1)
    (φ : SpectralPoint) :
    φ (FractionGraph p₂ q₂) ≤ φ (FractionGraph p q) ∧
    φ (FractionGraph p q) ≤ (p : ℝ) / (p - 1) *
      φ (FractionGraph p₂ q₂) :=
  vertex_removal_bounds p q p₂ q₂ h2q₂ hq₂_lt heq φ

/-- **Theorem 3.6 for α** (`th:vrm`): vertex-removal bounds
    `α(E_{p₂/q₂}) ≤ α(E_{p/q}) ≤ p/(p−1) · α(E_{p₂/q₂})`. -/
theorem main_vertex_removal_bounds_alpha (p q p₂ q₂ : ℕ+)
    (h2q₂ : 2 * q₂ ≤ p₂) (hq₂_lt : q₂ < q)
    (heq : (p : ℕ) * q₂ - q * p₂ = 1) :
    ((FractionGraph p₂ q₂).indepNum : ℝ) ≤ (FractionGraph p q).indepNum ∧
    ((FractionGraph p q).indepNum : ℝ) ≤
      (p : ℝ) / (p - 1) * (FractionGraph p₂ q₂).indepNum :=
  vertex_removal_bounds_alpha p q p₂ q₂ h2q₂ hq₂_lt heq

/-- **Theorem 3.6 for Θ** (`th:vrm`): vertex-removal bounds
    `Θ(E_{p₂/q₂}) ≤ Θ(E_{p/q}) ≤ p/(p−1) · Θ(E_{p₂/q₂})`. -/
theorem main_vertex_removal_bounds_shannonCapacity (p q p₂ q₂ : ℕ+)
    (h2q₂ : 2 * q₂ ≤ p₂) (hq₂_lt : q₂ < q)
    (heq : (p : ℕ) * q₂ - q * p₂ = 1) :
    shannonCapacity (FractionGraph p₂ q₂) ≤ shannonCapacity (FractionGraph p q) ∧
    shannonCapacity (FractionGraph p q) ≤ (p : ℝ) / (p - 1) *
      shannonCapacity (FractionGraph p₂ q₂) :=
  vertex_removal_bounds_shannonCapacity p q p₂ q₂
    h2q₂ hq₂_lt heq

/-- **Theorem 3.7(a)** (`th:rational-right-cont`, item `item:rational-right-cont:a`):
    `p/q ↦ φ(E_{p/q})` is right-continuous at every `a/b ∈ ℚ_{≥2}` for `φ ∈ X`. -/
theorem main_right_continuous (a b : ℕ+) (h2b : 2 * b ≤ a) (φ : SpectralPoint) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ+),
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      |φ (FractionGraph p q) - φ (FractionGraph a b)| < ε :=
  right_continuous a b h2b φ

/-- **Theorem 3.7(a) for α** (`th:rational-right-cont`, item `item:rational-right-cont:a`):
    `p/q ↦ α(E_{p/q})` is right-continuous at every `a/b ∈ ℚ_{≥2}`. -/
theorem main_right_continuous_alpha (a b : ℕ+) (h2b : 2 * b ≤ a) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ+),
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      |((FractionGraph p q).indepNum : ℝ) -
        ((FractionGraph a b).indepNum : ℝ)| < ε :=
  right_continuous_alpha a b h2b

/-- **Theorem 3.7(a) for Θ** (`th:rational-right-cont`, item `item:rational-right-cont:a`):
    `p/q ↦ Θ(E_{p/q})` is right-continuous at every `a/b ∈ ℚ_{≥2}`. -/
theorem main_right_continuous_shannonCapacity (a b : ℕ+) (h2b : 2 * b ≤ a) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ+),
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      |shannonCapacity (FractionGraph p q) - shannonCapacity (FractionGraph a b)| < ε :=
  right_continuous_shannonCapacity a b h2b

/-- **Theorem 3.7(b)** (`th:rational-right-cont`, second item): right-continuity is
    uniform over `φ ∈ X`, i.e. `d(E_{p/q}, E_{a/b}) < ε` when `0 ≤ p/q − a/b < δ`. -/
theorem main_right_continuous_uniform (a b : ℕ+) (h2b : 2 * b ≤ a) :
    ∀ ε > 0, ∃ δ > 0, ∀ (p q : ℕ+),
      ((a : ℚ) / b ≤ (p : ℚ) / q) → ((p : ℚ) / q - (a : ℚ) / b < δ) →
      asympSpecDistance (FractionGraph p q) (FractionGraph a b) < ε :=
  right_continuous_uniform a b h2b

/-- **Theorem 3.7(c)** (`th:rational-right-cont`, third item): if `p_n/q_n → a/b`
    from above (with `a/b ≥ 2`, `p_n/q_n ≥ 2`), then `E_{p_n/q_n} → E_{a/b}`. -/
theorem main_convergence_from_above (a b : ℕ+)
    (h2b : 2 * b ≤ a)
    (ps : ℕ → ℕ+) (qs : ℕ → ℕ+)
    (hfrom_above : ∀ n, (a : ℚ) / b ≤ (ps n : ℚ) / qs n)
    (hconv : Tendsto (fun n => (ps n : ℚ) / qs n) atTop (𝓝 ((a : ℚ) / b))) :
    ConvergesTo (fun n => FractionGraph (ps n) (qs n))
      (FractionGraph a b) :=
  convergence_from_above a b h2b ps qs hfrom_above hconv

/-- **Theorem 3.14(a)** (`thm: continuous at irrationals`, item `item:irr:a`):
    for irrational `r ≥ 2` and `φ ∈ X`,
    `sup_{a/b < r} φ(E_{a/b}) = inf_{a/b > r} φ(E_{a/b})`. -/
theorem main_sup_eq_inf_irrational (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (φ : SpectralPoint) :
    sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
        x = φ (FractionGraph a b)} =
    sInf {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
        x = φ (FractionGraph a b)} :=
  fractionGraph_sup_eq_inf_irrational_pnat r hr hirr φ

/-- **Theorem 3.14(a) for α** (`thm: continuous at irrationals`, item `item:irr:a`):
    for irrational `r ≥ 2`,
    `sup_{a/b < r} α(E_{a/b}) = inf_{a/b > r} α(E_{a/b})`. -/
theorem main_sup_eq_inf_irrational_alpha (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r) :
    sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
        x = ((FractionGraph a b).indepNum : ℝ)} =
    sInf {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
        x = ((FractionGraph a b).indepNum : ℝ)} :=
  sup_eq_inf_irrational_alpha r hr hirr

/-- **Theorem 3.14(a) for Θ** (`thm: continuous at irrationals`, item `item:irr:a`):
    for irrational `r ≥ 2`,
    `sup_{a/b < r} Θ(E_{a/b}) = inf_{a/b > r} Θ(E_{a/b})`. -/
theorem main_sup_eq_inf_irrational_shannonCapacity (r : ℝ) (hr : 2 ≤ r)
    (hirr : Irrational r) :
    sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
        x = shannonCapacity (FractionGraph a b)} =
    sInf {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b > r ∧
        x = shannonCapacity (FractionGraph a b)} :=
  sup_eq_inf_irrational_shannonCapacity r hr hirr

/-- **Theorem 3.14(b)** (`thm: continuous at irrationals`, item `item:irr:b`):
    uniformly in `φ ∈ X`, `|sup_{a/b<r} φ(E_{a/b}) − φ(E_{p/q})| < ε` when
    `|p/q − r| < δ`. -/
theorem main_distance_to_limit_irrational (r : ℝ) (hr : 2 ≤ r)
    (hirr : Irrational r) :
    ∀ ε > 0, ∃ δ > 0, ∀ (φ : SpectralPoint) (p q : ℕ+),
      2 * q ≤ p →
      |(p : ℝ) / q - r| < δ →
      |sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧ (a : ℝ) / b < r ∧
                  x = φ (FractionGraph a b)}
       - φ (FractionGraph p q)| < ε :=
  distance_to_limit_irrational r hr hirr

/-- **Theorem 3.14(c)** (`thm: continuous at irrationals`, item `item:irr:c`):
    for irrational `r ≥ 2`, any sequence `E_{p_n/q_n}` with `p_n/q_n → r`
    is Cauchy in the asymptotic spectrum distance. -/
theorem main_cauchy_irrational (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ps : ℕ → ℕ+) (qs : ℕ → ℕ+)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hconv : Tendsto (fun n => (ps n : ℝ) / qs n) atTop (𝓝 r)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      asympSpecDistance (FractionGraph (ps n) (qs n))
        (FractionGraph (ps m) (qs m)) < ε :=
  cauchy_irrational r hr hirr ps qs h2qs hconv

/-- **Corollary 3.16** (`th:not-complete2`): there is a Cauchy sequence of
    fraction graphs not converging to any finite graph. -/
theorem main_no_finite_limit_existential :
    ∃ (ps : ℕ → ℕ+) (qs : ℕ → ℕ+),
      (∀ n, 2 * qs n ≤ ps n) ∧
      (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        asympSpecDistance (FractionGraph (ps n) (qs n))
          (FractionGraph (ps m) (qs m)) < ε) ∧
      ¬ ∃ G : Graph, ConvergesTo
        (fun n => FractionGraph (ps n) (qs n)) G :=
  no_finite_limit_existential

/-! ## Section 4: Circle graphs as limit points -/

/-- **Theorem 4.8** (`th:restr`): the restriction `X_∞ → X` is surjective —
    every `φ ∈ X` extends to some `ψ ∈ X_∞`. -/
theorem main_restriction_surjective :
    ∀ φ : SpectralPoint, ∃ ψ : SpectralPointInf, ∀ G : Graph,
      ψ (graphToInfiniteGraph G) = φ G :=
  restriction_surjective

/-- **Theorem 4.11(a)** (`th:irr-closed-open-equiv`): for irrational `r ≥ 2` and every
    `F ∈ X_∞`, `F(E_r^c) = F(E_r^o) = sup_{a/b<r} F(E_{a/b}) = inf_{c/d>r} F(E_{c/d})`. -/
theorem main_circleGraph_four_way_infinite (r : ℝ) (hr : 2 ≤ r)
    (hirr : Irrational r) (ψ : SpectralPointInf) :
    let S_below := sSup {x | ∃ (a b : ℕ+),
      2 * b ≤ a ∧ (a : ℝ) / b < r ∧
      x = ψ (graphToInfiniteGraph (FractionGraph a b))}
    let S_above := sInf {x | ∃ (a b : ℕ+),
      2 * b ≤ a ∧ (a : ℝ) / b > r ∧
      x = ψ (graphToInfiniteGraph (FractionGraph a b))}
    ψ (circleGraphClosedInf r hr) = S_below ∧
    ψ (circleGraphOpenInf r hr) = S_below ∧
    S_below = S_above :=
  circleGraph_four_way_pnat r hr hirr ψ

/-- **Theorem 4.11(b)** (`th:irr-closed-open-equiv`): for irrational `r ≥ 2`,
    if `p_n/q_n → r` then `E_{p_n/q_n} → E_r^o` in `d_∞`. -/
theorem main_converges_to_circleGraph (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (ps : ℕ → ℕ+) (qs : ℕ → ℕ+)
    (h2qs : ∀ n, 2 * qs n ≤ ps n)
    (hconv : Tendsto (fun n => (ps n : ℝ) / qs n) atTop (𝓝 r)) :
    ConvergesToInf
      (fun n => graphToInfiniteGraph (FractionGraph (ps n) (qs n)))
      (circleGraphOpenInf r hr) :=
  converges_to_circleGraph r hr hirr ps qs h2qs hconv

/-! ### Theorem 4.12: Five equivalent conditions for left-continuity -/

/-- `G ≲∞ H`: asymptotic cohomomorphism preorder on infinite graphs
    (the infinite-graph version of paper's `\asympleq`). -/
infix:50 " ≲∞ " => AsympCohomInf

/-- `G ≃∞ H`: asymptotic equivalence of infinite graphs (paper's
    "asymptotically equivalent", no dedicated symbol), i.e. `G ≲∞ H` and
    `H ≲∞ G`. Defeq to `AsympCohomEquivInf G H`. -/
notation:50 G " ≃∞ " H => AsympCohomInf G H ∧ AsympCohomInf H G

/-- `f : ℕ → ℕ` is `o(n)`: `f(n) / n → 0` as `n → ∞`. Equivalently, for every
    `ε > 0`, eventually `f n < ε · n`. -/
abbrev IsLittleO (f : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, (f n : ℝ) < ε * n

/-- **Theorem 4.12** (`th:op-cl-left`): for rational `r = p/q > 2`, the five
    conditions (i) `E_r^c ≃ E_r^o`, (ii) strong-power `o(n)`-error bound,
    (iii) uniform left-continuity, (iv) sequential left-convergence,
    (v) `sup_{a/b<r} φ(E_{a/b}) = φ(E_{p/q})` are TFAE. -/
theorem main_theorem_4_12 (r : ℝ) (hr : 2 < r) (p q : ℕ+) (hr_eq : r = (p : ℝ) / q) :
    List.TFAE [
      circleGraphClosedInf r (le_of_lt hr) ≃∞ circleGraphOpenInf r (le_of_lt hr),
      ∃ f : ℕ → ℕ, IsLittleO f ∧ ∀ n, n ≥ 1 →
        ∃ (a b : ℕ+), 2 * b ≤ a ∧
          (a : ℝ) / b < r ∧
          Graph.Cohom (strongPowerGraph (FractionGraph p q) n)
            (strongPowerGraph (FractionGraph a b) (n + f n)),
      ∀ ε > 0, ∃ δ > 0, ∀ (a b : ℕ+),
        2 * b ≤ a →
        0 < r - (a : ℝ) / b →
        r - (a : ℝ) / b < δ →
        ∀ φ : SpectralPoint,
          φ (FractionGraph p q) - φ (FractionGraph a b) < ε,
      ∀ (as bs : ℕ → ℕ+),
        (∀ n, 2 * bs n ≤ as n) →
        Tendsto (fun n => (as n : ℝ) / bs n) atTop (𝓝 r) →
        (∀ n, (as n : ℝ) / bs n < r) →
        ConvergesTo (fun n => FractionGraph (as n) (bs n)) (FractionGraph p q),
      ∀ φ : SpectralPoint,
        sSup {x | ∃ (a b : ℕ+), 2 * b ≤ a ∧
          (a : ℝ) / b < r ∧
          x = φ (FractionGraph a b)} =
        φ (FractionGraph p q) ] :=
  theorem_4_12_tfae_with_r r hr p q hr_eq

/-- **Spectral companion to Theorem 4.15** (the literal Theorem 4.15 is
    `main_circleGraph_closure_equality` below): if every `ψ ∈ X_∞` agrees
    on `E_r^c` and `E_r^o` at every rational `r > 2`, then the same holds
    at every real `r > 2`. -/
theorem main_circleGraph_conditional_closure
    (hhyp : ∀ (r : ℝ) (hr : 2 < r), ¬ Irrational r → ∀ ψ : SpectralPointInf,
      ψ (circleGraphClosedInf r (le_of_lt hr)) =
        ψ (circleGraphOpenInf r (le_of_lt hr))) :
    ∀ (r : ℝ) (hr : 2 < r) (ψ : SpectralPointInf),
      ψ (circleGraphClosedInf r (le_of_lt hr)) =
        ψ (circleGraphOpenInf r (le_of_lt hr)) :=
  circleGraph_asymp_equiv_conditional hhyp

/-! ### Section 4.4: Sequential closure of fraction graphs -/

/-- **Theorem 4.15** (⊇ direction, unconditional): every open circle graph
    lies in the sequential closure of the fraction graphs (under `d_∞`). The
    matching ⊆ direction (conditional on Theorem 4.12 (i) at every rational
    `r > 2`) appears in `main_circleGraph_closure_equality` below. -/
theorem main_circleGraph_closure_theorem :
    openCircleGraphSet ⊆ seqClosure fractionGraphSet :=
  openCircleGraphSet_subset_seqClosure_fractionGraphSet

/-- **Theorem 4.15** (sequential-closure ingredient, conditional on Theorem 4.12 (i)
    at every rational `r > 2`): the open circle graphs are sequentially closed,
    i.e. `r_n → r` (with `r_n, r ≥ 2`) gives `E_{r_n}^o → E_r^o` in `d_∞`. -/
theorem main_circleGraphOpen_closed_under_limits
    (hhyp : ∀ (p q : ℕ+) (h2q : 2 * q < p),
      circleGraphClosedInfPNat p q h2q ≃∞ circleGraphOpenInfPNat p q h2q)
    (rs : ℕ → ℝ) (h_rs : ∀ n, 2 ≤ rs n)
    (r : ℝ) (hr : 2 ≤ r) (hrconv : Tendsto rs atTop (𝓝 r)) :
    ConvergesToInf (fun n => circleGraphOpenInf (rs n) (h_rs n))
                   (circleGraphOpenInf r hr) :=
  circleGraphOpen_closed_under_limits hhyp rs h_rs r hr hrconv

/-- Infinite graphs asymptotically equivalent to some open circle graph
    `E_r^o` (`r ≥ 2`): there is `H` and `r ≥ 2` with `F(H) = F(E_r^o)` for
    every `F ∈ X_∞`. -/
abbrev openCircleGraphsAsymp : Set InfiniteGraphClass :=
  { c | ∃ (H : InfiniteGraph) (r : ℝ) (hr : 2 ≤ r),
        c = InfiniteGraphClass.mk H ∧
        ∀ F : SpectralPointInf, F.eval H = F.eval (circleGraphOpenInf r hr) }

/-- **Theorem 4.15**: under Theorem 4.12 (i) at every rational `r > 2`, the
    open circle graphs (up to asymptotic equivalence) are the sequential
    closure of the fraction graphs (under `d_∞`). -/
theorem main_circleGraph_closure_equality
    (hhyp : ∀ (p q : ℕ+) (h2q : 2 * q < p),
      circleGraphClosedInfPNat p q h2q ≃∞ circleGraphOpenInfPNat p q h2q) :
    openCircleGraphsAsymp = seqClosure fractionGraphSet :=
  openCircleGraphSet_specEq_eq_seqClosure_fractionGraphSet hhyp

/-! ## Section 5: Self-cohomomorphisms and open ≠ closed -/

/-- **Lemma 5.1** (`rem: core`): every self-cohomomorphism `f : ZMod p → ZMod p`
    of `E_{p/q}` (coprime `p, q` with `p/q ≥ 2`) is bijective (and hence a
    graph automorphism, since the domain and codomain are the same graph). -/
theorem main_selfCohom_isIso (p q : ℕ+)
    (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : Graph.IsCohom (FractionGraph p q) (FractionGraph p q) f) :
    Function.Bijective f :=
  fractionGraph_selfCohom_isIso_pnat p q h2q hcoprime f hf

/-- **Lemma 5.2** (`lem: self_co_imp_auto_finite`): every self-cohomomorphism
    of `E_{p/q}` (coprime `p, q`, `q ≥ 2`, `p/q ≥ 2`) has the form
    `x ↦ a + x` or `x ↦ a − x`. -/
theorem main_selfCohom_form (p q : ℕ+)
    (hq_ge_2 : 2 ≤ q) (h2q : 2 * q ≤ p) (hcoprime : Nat.Coprime p q)
    (f : ZMod p → ZMod p)
    (hf : Graph.IsCohom (FractionGraph p q) (FractionGraph p q) f) :
    ∃ a : ZMod p, (∀ x, f x = a + x) ∨ (∀ x, f x = a - x) :=
  fractionGraph_selfCohom_form_pnat p q hq_ge_2 h2q hcoprime f hf

/-- **Theorem 5.6** (`lem:rotation-reflection`): for irrational `r ≥ 2`, every
    self-cohomomorphism of `E_r^o` or `E_r^c` is a rotation, possibly with a
    reflection. -/
theorem main_circleSelfCohom_form (r : ℝ) (hr : 2 ≤ r) (hirr : Irrational r)
    (f : Circle → Circle)
    (hf : IsCohom (circleGraphOpen r hr) (circleGraphOpen r hr) f ∨
          IsCohom (circleGraphClosed r hr) (circleGraphClosed r hr) f) :
    ∃ (a : Circle) (sgn : Bool),
      if sgn then ∀ x, f x = a + x else ∀ x, f x = a - x :=
  circleGraph_selfCohom_form r hr hirr f hf

/-- **Theorems 5.7** (`th:rat-inequiv`) **and 5.8** (`th:open-closed-noneq`):
    for every `r ≥ 2`, `E_r^o` and `E_r^c` are not cohomomorphically equivalent —
    there is no pair `(f, g)` of cohomomorphisms `f : E_r^o → E_r^c` and
    `g : E_r^c → E_r^o`. -/
theorem main_open_closed_not_equiv (r : ℝ) (hr : 2 ≤ r) :
    ¬ CohomEquiv (circleGraphOpen r hr) (circleGraphClosed r hr) :=
  circleGraph_open_closed_not_equiv r hr

end AsymptoticSpectrumDistance

/-! ## Section 6: Independent sets in products of fraction graphs

The `main_*` theorems below live in the **root** namespace (not in
`AsymptoticSpectrumDistance`). Opens:
- `ShannonCapacity` for short names like `strongPower`, `bigStrongProduct`,
  and the raw `fractionGraph` (used internally inside upstream lemmas).
- `AsymptoticSpectrumDistance` for the bundled `FractionGraph` (paper's `E_{p/q}`).
- `AsymptoticSpectrumGraphs` for `Graph` and the bundled `Graph.*` operations
  (`Graph.indepNum`, `Graph.bigStrongProduct`, `Graph.Cohom`, `Graph.IsCohom`).

All theorem statements use bundled `FractionGraph` + `Graph.*` operations
for consistency with Sections 2–5. -/

section IndependentSetResults

open ShannonCapacity AsymptoticSpectrumDistance AsymptoticSpectrumGraphs

/-! ### Theorems 6.1, 6.2: explicit C₁₅ strong-power bounds -/

/-- **Theorem 6.1** (`th:C15-3`): `α(C₁₅^{⊠3}) ≥ 382` (Codenotti–Gerace–
    Resta; Polak–Schrijver). -/
theorem main_indepNum_C15_cube :
    (strongPower (SimpleGraph.cycleGraph 15) 3).indepNum ≥ 382 :=
  C15ThirdPower.C15_3_indepNum_bound_cycle

/-- **Theorem 6.2** (`th:C15-4`): `α(C₁₅^{⊠4}) ≥ 2842`. -/
theorem main_indepNum_C15_fourth :
    (strongPower (SimpleGraph.cycleGraph 15) 4).indepNum ≥ 2842 :=
  C15_4_indepNum_bound_cycle

/-! ### Theorem 6.4 (`th:nested-floor`) -/

/-- **Theorem 6.4** (`th:nested-floor`, induction step, single-factor form):
    `α(E_{p/q} ⊠ G) ≤ ⌊(p/q) · α(G)⌋`. The paper's k-fold nested-floor form
    is `main_nested_floor_list` below. -/
theorem main_nested_floor (p q : ℕ+) (h2q : 2 * q ≤ p) (G : Graph) :
    (FractionGraph p q ⊠ G).indepNum ≤ ⌊(p : ℝ) / q * G.indepNum⌋₊ :=
  Section6.nested_floor p q h2q G.graph

/-- **Theorem 6.4** (`th:nested-floor`, two-factor, right-nested form):
    `α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) ≤ ⌊(p₁/q₁) · ⌊p₂/q₂⌋⌋`.

    Note: the paper writes the bound in left-nested form `⌊⌊p₁/q₁⌋ · p₂/q₂⌋`;
    this Lean statement uses the equivalent right-nested form (interchangeable
    by reversing the factor list, since the LHS is permutation-invariant). -/
theorem main_nested_floor_two (p₁ q₁ p₂ q₂ : ℕ+)
    (h2q₁ : 2 * q₁ ≤ p₁) (h2q₂ : 2 * q₂ ≤ p₂) :
    (FractionGraph p₁ q₁ ⊠ FractionGraph p₂ q₂).indepNum ≤
    ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂⌋₊⌋₊ :=
  Section6.nested_floor_two p₁ q₁ p₂ q₂ q₁.pos h2q₁ q₂.pos h2q₂

/-- **Theorem 6.4** (`th:nested-floor`, three-factor, right-nested form):
    `α(E_{p₁/q₁} ⊠ E_{p₂/q₂} ⊠ E_{p₃/q₃}) ≤ ⌊(p₁/q₁) · ⌊(p₂/q₂) · ⌊p₃/q₃⌋⌋⌋`.

    Note: the paper writes the bound in left-nested form
    `⌊⌊⌊p₁/q₁⌋ · p₂/q₂⌋ · p₃/q₃⌋`; this Lean statement uses the equivalent
    right-nested form. -/
theorem main_nested_floor_three (p₁ q₁ p₂ q₂ p₃ q₃ : ℕ+)
    (h2q₁ : 2 * q₁ ≤ p₁) (h2q₂ : 2 * q₂ ≤ p₂) (h2q₃ : 2 * q₃ ≤ p₃) :
    (FractionGraph p₁ q₁ ⊠ FractionGraph p₂ q₂ ⊠ FractionGraph p₃ q₃).indepNum ≤
    ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂ * ⌊(p₃ : ℝ) / q₃⌋₊⌋₊⌋₊ :=
  Section6.nested_floor_three_main p₁ q₁ p₂ q₂ p₃ q₃ h2q₁ h2q₂ h2q₃

/-- The nested-floor expression on a list of fractions:
    `nestedFloorList [(p₁,q₁), …, (pₖ,qₖ)] = ⌊(p₁/q₁)·⌊(p₂/q₂)·⌊…·⌊pₖ/qₖ⌋⌋⌋⌋`. -/
noncomputable def nestedFloorList : List (ℕ+ × ℕ+) → ℕ
  | [] => 1
  | (p, q) :: rest => ⌊(p : ℝ) / q * nestedFloorList rest⌋₊

/-- **Theorem 6.4** (`th:nested-floor`, k-fold, right-nested form):
    `α(E_{p₁/q₁} ⊠ ⋯ ⊠ E_{pₖ/qₖ}) ≤ nestedFloorList [(p₁,q₁), …, (pₖ,qₖ)]`,
    where the LHS is `Graph.bigStrongProduct` over `Fin l.length` of fraction
    graphs `E_{l[i].1/l[i].2}`.

    Note: the paper writes the bound in left-nested form
    `⌊⋯⌊⌊p₁/q₁⌋ · p₂/q₂⌋ ⋯ · pₖ/qₖ⌋`; this Lean statement uses the equivalent
    right-nested form (interchangeable by reversing the list of factors, since
    the LHS is permutation-invariant). -/
theorem main_nested_floor_list (l : List (ℕ+ × ℕ+))
    (hl : ∀ pq ∈ l, 2 * (pq.2 : ℕ) ≤ (pq.1 : ℕ)) :
    (Graph.bigStrongProduct (fun i : Fin l.length =>
      FractionGraph (l[i].1) (l[i].2))).indepNum ≤ nestedFloorList l := by
  have h_nf : ∀ l', nestedFloorList l' = Section6.nestedFloorList l' := by
    intro l'
    induction l' <;> simp [nestedFloorList, Section6.nestedFloorList, *]
  rw [h_nf]
  exact Section6.nested_floor_list_bundled l hl

/-- **Theorem 6.5** (`th:two-factors`):
    `α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) = min(⌊p₁/q₁ · ⌊p₂/q₂⌋⌋, ⌊p₂/q₂ · ⌊p₁/q₁⌋⌋)`.

    Both terms of the `min` are written here in right-nested form (floor
    applied innermost); they correspond to the two orderings of the factor
    list. The paper writes the same statement with left-nested floor. -/
theorem main_two_factor (p₁ q₁ p₂ q₂ : ℕ+)
    (h2q₁ : 2 * q₁ ≤ p₁) (h2q₂ : 2 * q₂ ≤ p₂) :
    (FractionGraph p₁ q₁ ⊠ FractionGraph p₂ q₂).indepNum =
    min ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂⌋₊⌋₊
        ⌊(p₂ : ℝ) / q₂ * ⌊(p₁ : ℝ) / q₁⌋₊⌋₊ :=
  Section6.theorem_6_5 p₁ q₁ p₂ q₂ q₁.pos h2q₁ q₂.pos h2q₂

/-! ### Theorem 6.9 (`th:discont`) -/

/-- Rational value of slot `i` of a triple. -/
abbrev tripleRat (v : Fin 3 → ℕ+ × ℕ+) (i : Fin 3) : ℚ :=
  ((v i).1 : ℚ) / (v i).2

/-- `u ≤ₚ v` iff there is a permutation `σ` of the three slots such that
    `tripleRat u (σ i) ≤ tripleRat v i` for every `i`. This is the paper's
    "u is dominated by v as a multiset of rationals" comparison. -/
abbrev lePermTriple (u v : Fin 3 → ℕ+ × ℕ+) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∀ i, tripleRat u (σ i) ≤ tripleRat v i

@[inherit_doc] infix:50 " ≤ₚ " => lePermTriple

/-- Strict version of `≤ₚ`: `u <ₚ v` iff `u ≤ₚ v` and not `v ≤ₚ u`. -/
abbrev ltPermTriple (u v : Fin 3 → ℕ+ × ℕ+) : Prop := u ≤ₚ v ∧ ¬ v ≤ₚ u

@[inherit_doc] infix:50 " <ₚ " => ltPermTriple

/-- `v` is a valid triple: each slot satisfies `(v i).1 / (v i).2 ≥ 2`,
    i.e. `2 * (v i).2 ≤ (v i).1`. -/
abbrev IsValidTriple (v : Fin 3 → ℕ+ × ℕ+) : Prop :=
  ∀ i, 2 * ((v i).2 : ℕ) ≤ (v i).1

/-- `α₃(v) = α(E_{(v 0).1/(v 0).2} ⊠ E_{(v 1).1/(v 1).2} ⊠ E_{(v 2).1/(v 2).2})`. -/
noncomputable abbrev alpha3 (v : Fin 3 → ℕ+ × ℕ+) : ℕ :=
  (Graph.bigStrongProduct (fun i => FractionGraph (v i).1 (v i).2)).indepNum

/-- `v` is an α₃-discontinuity iff every valid `u` strictly smaller than `v`
    (under `<ₚ`) has strictly smaller α₃. -/
abbrev IsAlpha3Discontinuity (v : Fin 3 → ℕ+ × ℕ+) : Prop :=
  ∀ u, IsValidTriple u → u <ₚ v → alpha3 u < alpha3 v

/-- The 12 paper-canonical α₃-discontinuity triples on `(ℚ ∩ [2, 3])³`
    from Theorem 6.9. Used by `main_theorem_6_9`. -/
abbrev discontinuityTriples : List (Fin 3 → ℚ) :=
  [ ![2,    2,    2],    ![2,    2,    3],    ![2,    3,    3],    ![3,    3,    3],
    ![2,    5/2,  5/2],  ![5/2,  5/2,  3],    ![5/2,  5/2,  8/3],  ![8/3,  8/3,  8/3],
    ![9/4,  7/3,  5/2],  ![11/5, 11/4, 11/4], ![11/4, 11/4, 11/4], ![14/5, 14/5, 14/5] ]

/-- **Theorem 6.9** (`th:discont`): the α₃-discontinuities on `(ℚ ∩ [2, 3])³`
    are exactly the 12 paper-canonical rational triples (`discontinuityTriples`)
    up to permutation. -/
theorem main_theorem_6_9
    (v : Fin 3 → ℕ+ × ℕ+)
    (hv_ge2 : ∀ i, (2 : ℚ) ≤ tripleRat v i)
    (hv_le3 : ∀ i, tripleRat v i ≤ 3) :
    IsAlpha3Discontinuity v ↔
    ∃ σ : Equiv.Perm (Fin 3), (fun i => tripleRat v (σ i)) ∈ discontinuityTriples :=
  Section6.theorem_6_9_rat v hv_ge2 hv_le3

/-! ### The 12 α₃ values at the discontinuity points (paper Theorem 6.9)

The naming convention `aobN` denotes the fraction `a/b`: e.g. `5o2 = 5/2`,
`8o3 = 8/3`, `11o4 = 11/4`. Integer slots use the literal value (e.g. `2`, `3`). -/

/-- `α₃(2, 2, 2) = 8`. -/
theorem main_alpha3_2_2_2 :
    (FractionGraph 2 1 ⊠ FractionGraph 2 1 ⊠ FractionGraph 2 1).indepNum = 8 :=
  Section6.alpha3_2_2_2_main

/-- `α₃(2, 2, 3) = 12`. -/
theorem main_alpha3_2_2_3 :
    (FractionGraph 2 1 ⊠ FractionGraph 2 1 ⊠ FractionGraph 3 1).indepNum = 12 :=
  Section6.alpha3_2_2_3_main

/-- `α₃(2, 3, 3) = 18`. -/
theorem main_alpha3_2_3_3 :
    (FractionGraph 2 1 ⊠ FractionGraph 3 1 ⊠ FractionGraph 3 1).indepNum = 18 :=
  Section6.alpha3_2_3_3_main

/-- `α₃(2, 5/2, 5/2) = 10`. -/
theorem main_alpha3_2_5o2_5o2 :
    (FractionGraph 2 1 ⊠ FractionGraph 5 2 ⊠ FractionGraph 5 2).indepNum = 10 :=
  Section6.alpha3_2_5o2_5o2_main

/-- `α₃(5/2, 5/2, 3) = 15`. -/
theorem main_alpha3_5o2_5o2_3 :
    (FractionGraph 5 2 ⊠ FractionGraph 5 2 ⊠ FractionGraph 3 1).indepNum = 15 :=
  Section6.alpha3_5o2_5o2_3_main

/-- `α₃(5/2, 5/2, 8/3) = 11`. -/
theorem main_alpha3_5o2_5o2_8o3 :
    (FractionGraph 5 2 ⊠ FractionGraph 5 2 ⊠ FractionGraph 8 3).indepNum = 11 :=
  Section6.alpha3_5o2_5o2_8o3_main

/-- `α₃(8/3, 8/3, 8/3) = 12`. -/
theorem main_alpha3_8o3_8o3_8o3 :
    (FractionGraph 8 3 ⊠ FractionGraph 8 3 ⊠ FractionGraph 8 3).indepNum = 12 :=
  Section6.alpha3_8o3_8o3_8o3_main

/-- `α₃(9/4, 7/3, 5/2) = 9`. -/
theorem main_alpha3_9o4_7o3_5o2 :
    (FractionGraph 9 4 ⊠ FractionGraph 7 3 ⊠ FractionGraph 5 2).indepNum = 9 :=
  Section6.alpha3_9o4_7o3_5o2_main

/-- `α₃(11/5, 11/4, 11/4) = 11`. -/
theorem main_alpha3_11o5_11o4_11o4 :
    (FractionGraph 11 5 ⊠ FractionGraph 11 4 ⊠ FractionGraph 11 4).indepNum = 11 :=
  Section6.alpha3_11o5_11o4_11o4_main

/-- `α₃(11/4, 11/4, 11/4) = 13`. -/
theorem main_alpha3_11o4_11o4_11o4 :
    (FractionGraph 11 4 ⊠ FractionGraph 11 4 ⊠ FractionGraph 11 4).indepNum = 13 :=
  Section6.alpha3_11o4_11o4_11o4_main

/-- `α₃(14/5, 14/5, 14/5) = 14`. -/
theorem main_alpha3_14o5_14o5_14o5 :
    (FractionGraph 14 5 ⊠ FractionGraph 14 5 ⊠ FractionGraph 14 5).indepNum = 14 :=
  Section6.alpha3_14o5_14o5_14o5_main

/-- `α₃(3, 3, 3) = 27`. -/
theorem main_alpha3_3_3_3 :
    (FractionGraph 3 1 ⊠ FractionGraph 3 1 ⊠ FractionGraph 3 1).indepNum = 27 :=
  Section6.alpha3_3_3_3_main

/-! ### Theorem 6.14 (`th:symm-disc` in the paper):
    The diagonal independence number `α(E_{p/q}^⊠3)` for `p/q ∈ ℚ ∩ [2, 3]`,
    given by 5 intervals plus the integer point `p/q = 3`. -/

/-- **Interval 1**: `α(E_{p/q}^⊠3) = 8` for `p/q ∈ [2, 5/2)`. -/
theorem main_diagonal_interval_1 (p q : ℕ+)
    (h2q : 2 * q ≤ p) (h_ub : 2 * p < 5 * q) :
    (FractionGraph p q ⊠ FractionGraph p q ⊠ FractionGraph p q).indepNum = 8 :=
  Section6.alpha3_diagonal_interval_1_main p q h2q h_ub

/-- **Interval 2**: `α(E_{p/q}^⊠3) = 10` for `p/q ∈ [5/2, 8/3)`. -/
theorem main_diagonal_interval_2 (p q : ℕ+)
    (h_lb : 5 * q ≤ 2 * p) (h_ub : 3 * p < 8 * q) :
    (FractionGraph p q ⊠ FractionGraph p q ⊠ FractionGraph p q).indepNum = 10 :=
  Section6.alpha3_diagonal_interval_2_main p q h_lb h_ub

/-- **Interval 3**: `α(E_{p/q}^⊠3) = 12` for `p/q ∈ [8/3, 11/4)`. -/
theorem main_diagonal_interval_3 (p q : ℕ+)
    (h_lb : 8 * q ≤ 3 * p) (h_ub : 4 * p < 11 * q) :
    (FractionGraph p q ⊠ FractionGraph p q ⊠ FractionGraph p q).indepNum = 12 :=
  Section6.alpha3_diagonal_interval_3_main p q h_lb h_ub

/-- **Interval 4**: `α(E_{p/q}^⊠3) = 13` for `p/q ∈ [11/4, 14/5)`. -/
theorem main_diagonal_interval_4 (p q : ℕ+)
    (h_lb : 11 * q ≤ 4 * p) (h_ub : 5 * p < 14 * q) :
    (FractionGraph p q ⊠ FractionGraph p q ⊠ FractionGraph p q).indepNum = 13 :=
  Section6.alpha3_diagonal_interval_4_main p q h_lb h_ub

/-- **Interval 5**: `α(E_{p/q}^⊠3) = 14` for `p/q ∈ [14/5, 3)`. -/
theorem main_diagonal_interval_5 (p q : ℕ+)
    (h_lb : 14 * q ≤ 5 * p) (h_ub : p < 3 * q) :
    (FractionGraph p q ⊠ FractionGraph p q ⊠ FractionGraph p q).indepNum = 14 :=
  Section6.alpha3_diagonal_interval_5_main p q h_lb h_ub

/-- **Endpoint**: `α(E_{p/q}^⊠3) = 27` for `p/q = 3`. -/
theorem main_diagonal_point_3 (p q : ℕ+) (hpq_eq : p = 3 * q) :
    (FractionGraph p q ⊠ FractionGraph p q ⊠ FractionGraph p q).indepNum = 27 :=
  Section6.alpha3_diagonal_point_3_main p q hpq_eq

/-! ## Shannon capacity lower bounds for small odd cycles (classical)

Best-known lower bounds for `Θ(C_n)`, `n ∈ {5, 7, 9, 11, 13, 15}`,
formalized in Lean. -/

/-- `Θ(C₅) ≥ √5`. Lower bound construction `α(C₅²) ≥ 5` is due to Shannon (1956);
    the matching upper bound `Θ(C₅) ≤ √5` is Lovász (1979). -/
theorem main_shannon_C5 :
    shannonCapacity (SimpleGraph.cycleGraph 5) ≥ (5 : ℝ) ^ ((1 : ℝ) / 2) :=
  C5Bound.shannonCapacity_cycleGraph_5_lower

/-- `Θ(C₇) ≥ 367^{1/5}` (Polak–Schrijver 2019), via `α(C₇⁵) ≥ 367`. -/
theorem main_shannon_C7 :
    shannonCapacity (SimpleGraph.cycleGraph 7) ≥ (367 : ℝ) ^ ((1 : ℝ) / 5) :=
  C7Bound.shannonCapacity_cycleGraph_7_lower

/-- `Θ(C₉) ≥ 81^{1/3}`, via `α(C₉³) ≥ 81` (Baumert orbit construction). -/
theorem main_shannon_C9 :
    shannonCapacity (SimpleGraph.cycleGraph 9) ≥ (81 : ℝ) ^ ((1 : ℝ) / 3) :=
  C9Bound.shannonCapacity_cycleGraph_9_lower

/-- `Θ(C₁₁) ≥ 148^{1/3}`, via `α(C₁₁³) ≥ 148`. -/
theorem main_shannon_C11 :
    shannonCapacity (SimpleGraph.cycleGraph 11) ≥ (148 : ℝ) ^ ((1 : ℝ) / 3) :=
  C11Bound.shannonCapacity_cycleGraph_11_lower

/-- `Θ(C₁₃) ≥ 247^{1/3}`, via `α(C₁₃³) ≥ 247`. -/
theorem main_shannon_C13 :
    shannonCapacity (SimpleGraph.cycleGraph 13) ≥ (247 : ℝ) ^ ((1 : ℝ) / 3) :=
  C13Bound.shannonCapacity_cycleGraph_13_lower

end IndependentSetResults
