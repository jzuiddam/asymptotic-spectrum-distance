/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Two-Factor Independence Number Formula

Proves Theorem 6.5 from Section 6:
  α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) = min(⌊⌊p₁/q₁⌋·p₂/q₂⌋, ⌊⌊p₂/q₂⌋·p₁/q₁⌋)

## Proof ideas

**Orbit bound** (used in proof of Theorem 6.5): α(E_{p/q} ⊠ E_{p/⌊p/q⌋}) = p.
Upper bound from nested floor. Lower bound from the orbit
{(t, t·m) : t ∈ Z_p} where m = ⌊p/q⌋.
Key: if distMod(t,s) < q then distMod(t·m, s·m) ≥ m.

**Theorem 6.5 upper bound**: Nested floor bound in both orderings.

**Theorem 6.5 lower bound**: Set N = min(F₁, F₂) where F₁ = ⌊n₂·p₁/q₁⌋ and
F₂ = ⌊n₁·p₂/q₂⌋. Apply the orbit bound at modulus N with divisor n₂ (or n₁),
then use product cohomomorphisms E_{N/n₂} → E_{p₁/q₁} and E_{N/n₁} → E_{p₂/q₂}.

## Main results

- `indepNum_fractionGraph_product_floor`: α(E_{p/q} ⊠ E_{p/⌊p/q⌋}) = p
- `theorem_6_5`: α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) = min(⌊⌊p₁/q₁⌋·p₂/q₂⌋, ⌊⌊p₂/q₂⌋·p₁/q₁⌋)
-/
import AsymptoticSpectrumDistance.Section6.Section6NestedFloor

open ShannonCapacity

namespace Section6

/-! ## Strong product commutativity -/

/-- The strong product is commutative up to graph isomorphism. -/
def strongProduct_comm_iso {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) :
    strongProduct G H ≃g strongProduct H G where
  toEquiv := Equiv.prodComm V W
  map_rel_iff' := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    simp only [strongProduct, Equiv.prodComm_apply,
      Prod.swap_prod_mk, Prod.mk.injEq, ne_eq]
    tauto

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Independence number is invariant under swapping factors. -/
theorem indepNum_strongProduct_comm {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (strongProduct G H).indepNum = (strongProduct H G).indepNum :=
  independenceNumber_iso (strongProduct_comm_iso G H)

/-! ## Key arithmetic lemmas -/

/-- distMod is symmetric under negation: distMod p x 0 = distMod p (-x) 0. -/
private lemma distMod_neg_zero (p : ℕ) [NeZero p] (x : ZMod p) :
    distMod p x 0 = distMod p (-x) 0 := by
  rw [distMod_comm p x 0]
  simp only [distMod, zero_sub, sub_zero]

/-- Floor of nat division as reals equals nat division. -/
private lemma nat_floor_div (p q : ℕ) (hq : 0 < q) :
    ⌊(p : ℝ) / q⌋₊ = p / q := by
  apply (Nat.floor_eq_iff (by positivity)).mpr
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < q)]
    exact_mod_cast Nat.div_mul_le_self p q
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < q)]
    have := @Nat.lt_div_mul_add p q hq
    exact_mod_cast show p < (p / q + 1) * q by linarith

/-- If `distMod p d 0 < q` and `d ≠ 0`, and `m = p / q`, then
    `distMod p (d * m) 0 ≥ m`. Key arithmetic fact for the orbit bound. -/
theorem distMod_mul_ge {p q : ℕ} [NeZero p] (hq : 0 < q)
    (h2q : 2 * q ≤ p) {d : ZMod p} (hd : d ≠ 0)
    (hdist : distMod p d 0 < q) :
    distMod p (d * (p / q : ℕ)) 0 ≥ p / q := by
  set m := p / q with hm_def
  have hp_pos : 0 < p := NeZero.pos p
  have hm_pos : 0 < m := Nat.div_pos (by omega) hq
  have hmq_le_p : m * q ≤ p := Nat.div_mul_le_self p q
  -- First establish 2 ≤ q (from d ≠ 0 and distMod d 0 < q)
  have hq_ge_2 : 2 ≤ q := by
    by_contra h; push_neg at h
    have hq1 : q = 1 := by omega
    subst hq1
    simp only [distMod, sub_zero] at hdist
    have : 0 < d.val := by
      rw [Nat.pos_iff_ne_zero]
      intro h; exact hd ((ZMod.val_eq_zero _).mp h)
    have : 0 < p - d.val := Nat.sub_pos_of_lt d.val_lt
    omega
  have hm_lt_p : m < p := by
    have : m * 2 ≤ m * q := Nat.mul_le_mul_left m hq_ge_2
    omega
  -- Suffices to prove for e with e.val < q
  suffices key : ∀ (e : ZMod p), e ≠ 0 → e.val < q →
      distMod p (e * (m : ZMod p)) 0 ≥ m by
    simp only [distMod, sub_zero] at hdist
    rcases min_lt_iff.mp hdist with hdv | hdp
    · exact key d hd hdv
    · -- p - d.val < q: use -d
      rw [distMod_neg_zero p (d * (m : ZMod p))]
      rw [show -(d * (m : ZMod p)) = (-d) * (m : ZMod p)
        from by ring]
      exact key (-d) (neg_ne_zero.mpr hd)
        (by rw [ZMod.neg_val, if_neg hd]; exact hdp)
  -- Prove key
  intro e he hev
  simp only [distMod, sub_zero]
  have he_pos : 0 < e.val := by
    rw [Nat.pos_iff_ne_zero]
    intro h; exact he ((ZMod.val_eq_zero _).mp h)
  have hem_lt_p : e.val * m < p :=
    calc e.val * m
        < q * m := Nat.mul_lt_mul_of_pos_right hev hm_pos
      _ = m * q := Nat.mul_comm q m
      _ ≤ p := hmq_le_p
  have hval : (e * (m : ZMod p)).val = e.val * m := by
    rw [ZMod.val_mul, ZMod.val_natCast_of_lt hm_lt_p,
      Nat.mod_eq_of_lt hem_lt_p]
  rw [hval]
  apply Nat.le_min.mpr
  constructor
  · exact Nat.le_mul_of_pos_left m he_pos
  · have : e.val * m + m ≤ p :=
      calc e.val * m + m
          = (e.val + 1) * m := by ring
        _ ≤ q * m := Nat.mul_le_mul_right m (by omega)
        _ = m * q := Nat.mul_comm q m
        _ ≤ p := hmq_le_p
    omega

/-! ## Orbit definition and independence -/

/-- The orbit {(t, t·m) : t ∈ Z_p} in Z_p × Z_p. -/
def orbitFinset (p m : ℕ) [NeZero p] :
    Finset (ZMod p × ZMod p) :=
  Finset.univ.image (fun t : ZMod p => (t, t * (m : ZMod p)))

/-- The orbit has cardinality p (injective via first coordinate). -/
theorem orbitFinset_card (p m : ℕ) [NeZero p] :
    (orbitFinset p m).card = Fintype.card (ZMod p) := by
  rw [orbitFinset,
    Finset.card_image_of_injective _
      (fun a b h => (Prod.ext_iff.mp h).1)]
  rfl

/-- The orbit is independent in E_{p/q} ⊠ E_{p/m} where m = p/q. -/
theorem orbitFinset_independent (p q : ℕ) [NeZero p]
    (hq : 0 < q) (h2q : 2 * q ≤ p) :
    (strongProduct (fractionGraph p q)
      (fractionGraph p (p / q))).IsIndepSet
      (↑(orbitFinset p (p / q)) : Set (ZMod p × ZMod p)) := by
  set m := p / q with hm_def
  have hm_pos : 0 < m := Nat.div_pos (by omega) hq
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hne hadj
  rw [Finset.mem_coe] at ha hb
  simp only [orbitFinset, Finset.mem_image, Finset.mem_univ,
    true_and] at ha hb
  obtain ⟨s₁, rfl⟩ := ha
  obtain ⟨s₂, rfl⟩ := hb
  have hs_ne : s₁ ≠ s₂ := fun h => hne (by subst h; rfl)
  -- Extract first coordinate adjacency
  have hadj_fst_or := hadj.2.1
  have hadj_snd_or := hadj.2.2
  -- First coord must be adj (not equal)
  rcases hadj_fst_or with h_eq | h_adj_fst
  · exact hs_ne h_eq
  · -- h_adj_fst : E[p/q].Adj s₁ s₂
    -- Get distMod (s₁ - s₂) 0 < q
    have hs_diff_ne : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hs_ne
    have hdist_fst : distMod p (s₁ - s₂) 0 < q := by
      calc distMod p (s₁ - s₂) 0
          = distMod p (s₂ + (s₁ - s₂)) (s₂ + 0) :=
            (distMod_add_left p s₂ (s₁ - s₂) 0).symm
        _ = distMod p s₁ s₂ := by congr 1 <;> ring
        _ < q := h_adj_fst.2
    have hmul_ge := distMod_mul_ge hq h2q hs_diff_ne hdist_fst
    -- Second coordinate: either equal or adjacent
    rcases hadj_snd_or with h_eq_snd | h_adj_snd
    · -- s₁ * m = s₂ * m: then (s₁ - s₂) * m = 0
      have h0 : (s₁ - s₂) * (m : ZMod p) = 0 := by
        rw [sub_mul, sub_eq_zero]
        exact h_eq_snd
      rw [show (s₁ - s₂) * ((m : ℕ) : ZMod p) =
        (s₁ - s₂) * (m : ZMod p) from rfl] at hmul_ge
      rw [h0] at hmul_ge
      simp [distMod] at hmul_ge
      omega
    · -- Both adj: distMod for second coord < m
      have hdist_snd :
          distMod p ((s₁ - s₂) * (m : ZMod p)) 0 < m := by
        calc distMod p ((s₁ - s₂) * (m : ZMod p)) 0
            = distMod p (s₂ * ↑m + (s₁ - s₂) * ↑m)
                (s₂ * ↑m + 0) :=
              (distMod_add_left p (s₂ * ↑m)
                ((s₁ - s₂) * ↑m) 0).symm
          _ = distMod p (s₁ * ↑m) (s₂ * ↑m) := by
              congr 1 <;> ring
          _ < m := h_adj_snd.2
      rw [show (s₁ - s₂) * ((m : ℕ) : ZMod p) =
        (s₁ - s₂) * (m : ZMod p) from rfl] at hmul_ge
      omega

/-! ## Orbit independent set in fraction graph products -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- α(E_{p/q} ⊠ E_{p/⌊p/q⌋}) = p.

    Used in the proof of Theorem 6.5 (two-factor formula).
    Upper bound from nested floor, lower bound from the orbit
    {(t, t·m) : t ∈ Z_p}. -/
theorem indepNum_fractionGraph_product_floor (p q : ℕ) [NeZero p]
    (hq : 2 ≤ q) (h2q : 2 * q ≤ p) :
    (strongProduct (fractionGraph p q)
      (fractionGraph p (p / q))).indepNum = p := by
  set m := p / q with hm_def
  have hp_pos : 0 < p := NeZero.pos p
  have hq_pos : 0 < q := by omega
  have hm_pos : 0 < m := Nat.div_pos (by omega) hq_pos
  have hmq_le_p : m * q ≤ p := Nat.div_mul_le_self p q
  have h2m_le_p : 2 * m ≤ p := by
    calc 2 * m = m * 2 := by ring
      _ ≤ m * q := Nat.mul_le_mul_left m hq
      _ ≤ p := hmq_le_p
  apply le_antisymm
  · -- Upper bound: commutativity + nested floor
    rw [indepNum_strongProduct_comm]
    calc (strongProduct (fractionGraph p m)
            (fractionGraph p q)).indepNum
        ≤ ⌊(p : ℝ) / m * ⌊(p : ℝ) / q⌋₊⌋₊ :=
          nested_floor_two p m p q hm_pos h2m_le_p hq_pos h2q
      _ = p := by
          rw [nat_floor_div p q hq_pos]
          change ⌊(p : ℝ) / ↑m * ↑m⌋₊ = p
          rw [div_mul_cancel₀]
          · simp [Nat.floor_natCast]
          · exact Nat.cast_ne_zero.mpr (by omega)
  · -- Lower bound: orbit of size p
    calc p
        = Fintype.card (ZMod p) := (ZMod.card p).symm
      _ = (orbitFinset p m).card := by rw [orbitFinset_card]
      _ ≤ (strongProduct (fractionGraph p q)
            (fractionGraph p m)).indepNum :=
          SimpleGraph.IsIndepSet.card_le_indepNum
            (orbitFinset_independent p q hq_pos h2q)

/-! ## Theorem 6.5: Two-factor formula -/

/-- Product of cohomomorphisms is a cohomomorphism for strong products. -/
private theorem strongProduct_isCohom {V₁ W₁ V₂ W₂ : Type*}
    (G₁ : SimpleGraph V₁) (H₁ : SimpleGraph W₁)
    (G₂ : SimpleGraph V₂) (H₂ : SimpleGraph W₂)
    (f₁ : V₁ → W₁) (f₂ : V₂ → W₂)
    (hf₁ : ∀ u v, u ≠ v → ¬G₁.Adj u v →
      f₁ u ≠ f₁ v ∧ ¬H₁.Adj (f₁ u) (f₁ v))
    (hf₂ : ∀ u v, u ≠ v → ¬G₂.Adj u v →
      f₂ u ≠ f₂ v ∧ ¬H₂.Adj (f₂ u) (f₂ v)) :
    ∀ p q : V₁ × V₂, p ≠ q →
    ¬(strongProduct G₁ G₂).Adj p q →
    (f₁ p.1, f₂ p.2) ≠ (f₁ q.1, f₂ q.2) ∧
    ¬(strongProduct H₁ H₂).Adj (f₁ p.1, f₂ p.2) (f₁ q.1, f₂ q.2) := by
  classical
  intro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩ hne hnadj
  have key : (u₁ ≠ v₁ ∧ ¬G₁.Adj u₁ v₁) ∨
      (u₂ ≠ v₂ ∧ ¬G₂.Adj u₂ v₂) := by
    by_contra h; push_neg at h; obtain ⟨h1, h2⟩ := h
    exact hnadj ⟨hne,
      if h : u₁ = v₁ then Or.inl h else Or.inr (h1 h),
      if h : u₂ = v₂ then Or.inl h else Or.inr (h2 h)⟩
  rcases key with ⟨hne₁, hna₁⟩ | ⟨hne₂, hna₂⟩
  · obtain ⟨hfne₁, hfna₁⟩ := hf₁ u₁ v₁ hne₁ hna₁
    exact ⟨fun h => hfne₁ (Prod.ext_iff.mp h).1,
      fun ⟨_, h1, _⟩ => h1.elim hfne₁ hfna₁⟩
  · obtain ⟨hfne₂, hfna₂⟩ := hf₂ u₂ v₂ hne₂ hna₂
    exact ⟨fun h => hfne₂ (Prod.ext_iff.mp h).2,
      fun ⟨_, _, h2⟩ => h2.elim hfne₂ hfna₂⟩

/-- Helper: (n * p) / q / n = p / q for natural division. -/
private lemma mul_div_div_cancel (n p q : ℕ) (hn : 0 < n) :
    n * p / q / n = p / q := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm q n,
    ← Nat.div_div_eq_div_mul]
  congr 1; exact Nat.mul_div_cancel_left p hn

/-- Helper: N ≤ (n * p) / q (nat div) implies (N : ℚ) / n ≤ p / q. -/
private lemma nat_div_le_rat_div (N n p q : ℕ)
    (hn : 0 < n) (hq : 0 < q)
    (hN : N ≤ n * p / q) : (N : ℚ) / n ≤ (p : ℚ) / q := by
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hq)]
  exact_mod_cast show N * q ≤ p * n by
    linarith [(Nat.le_div_iff_mul_le hq).mp hN]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Lower bound core: given N with appropriate conditions,
    α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) ≥ N. -/
private theorem two_factor_lower_bound
    {p₁ q₁ p₂ q₂ N n₁ n₂ : ℕ}
    [NeZero p₁] [NeZero p₂] [NeZero N]
    (hn₁_pos : 0 < n₁) (hn₂ : 2 ≤ n₂) (h2n₂ : 2 * n₂ ≤ N)
    (hNdiv : N / n₂ = n₁)
    (hle₁ : (N : ℚ) / n₂ ≤ p₁ / q₁)
    (hle₂ : (N : ℚ) / n₁ ≤ p₂ / q₂) :
    N ≤ (strongProduct (fractionGraph p₁ q₁)
      (fractionGraph p₂ q₂)).indepNum := by
  have hn₂_pos : 0 < n₂ := by omega
  have hlem65 := indepNum_fractionGraph_product_floor N n₂ hn₂ h2n₂
  rw [hNdiv] at hlem65
  obtain ⟨f₁, hf₁⟩ := fractionGraph_cohomomorphism N n₂ p₁ q₁
    hn₂_pos hle₁
  obtain ⟨f₂, hf₂⟩ := fractionGraph_cohomomorphism N n₁ p₂ q₂
    hn₁_pos hle₂
  have hprod := strongProduct_isCohom
    (fractionGraph N n₂) (fractionGraph p₁ q₁)
    (fractionGraph N n₁) (fractionGraph p₂ q₂)
    f₁ f₂ hf₁ hf₂
  calc N = (strongProduct (fractionGraph N n₂)
        (fractionGraph N n₁)).indepNum := hlem65.symm
    _ ≤ (strongProduct (fractionGraph p₁ q₁)
        (fractionGraph p₂ q₂)).indepNum :=
      independenceNumber_le_of_cohomomorphism _ _
        (fun p => (f₁ p.1, f₂ p.2)) hprod

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Theorem 6.5**: α(E_{p₁/q₁} ⊠ E_{p₂/q₂}) =
    min(⌊⌊p₁/q₁⌋·p₂/q₂⌋, ⌊⌊p₂/q₂⌋·p₁/q₁⌋).

Upper bound from nested floor in both orderings, lower bound from
`indepNum_fractionGraph_product_floor` and product cohomomorphism. -/
theorem theorem_6_5 (p₁ q₁ p₂ q₂ : ℕ) [NeZero p₁] [NeZero p₂]
    (hq₁ : 0 < q₁) (h2q₁ : 2 * q₁ ≤ p₁)
    (hq₂ : 0 < q₂) (h2q₂ : 2 * q₂ ≤ p₂) :
    (strongProduct (fractionGraph p₁ q₁)
      (fractionGraph p₂ q₂)).indepNum =
    min ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂⌋₊⌋₊
      ⌊(p₂ : ℝ) / q₂ * ⌊(p₁ : ℝ) / q₁⌋₊⌋₊ := by
  set n₁ := p₁ / q₁
  set n₂ := p₂ / q₂
  have hn₁ : 2 ≤ n₁ :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hn₂ : 2 ≤ n₂ :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hq₁_pos : 0 < q₁ := by omega
  have hq₂_pos : 0 < q₂ := by omega
  -- Simplify nested floor expressions to nat division
  have hsimp₁ : ⌊(p₁ : ℝ) / q₁ * ⌊(p₂ : ℝ) / q₂⌋₊⌋₊ =
      n₂ * p₁ / q₁ := by
    rw [nat_floor_div p₂ q₂ hq₂_pos,
      show (p₁ : ℝ) / q₁ * ↑n₂ = ↑(n₂ * p₁) / ↑q₁
        from by push_cast; ring]
    exact nat_floor_div (n₂ * p₁) q₁ hq₁_pos
  have hsimp₂ : ⌊(p₂ : ℝ) / q₂ * ⌊(p₁ : ℝ) / q₁⌋₊⌋₊ =
      n₁ * p₂ / q₂ := by
    rw [nat_floor_div p₁ q₁ hq₁_pos,
      show (p₂ : ℝ) / q₂ * ↑n₁ = ↑(n₁ * p₂) / ↑q₂
        from by push_cast; ring]
    exact nat_floor_div (n₁ * p₂) q₂ hq₂_pos
  rw [hsimp₁, hsimp₂]
  -- Useful arithmetic bounds
  have h2n₂_le : 2 * n₂ ≤ n₂ * p₁ / q₁ := calc
    2 * n₂ = n₂ * 2 := mul_comm 2 n₂
    _ ≤ n₂ * n₁ := Nat.mul_le_mul_left n₂ hn₁
    _ ≤ n₂ * p₁ / q₁ := Nat.mul_div_le_mul_div_assoc n₂ p₁ q₁
  have h2n₁_le : 2 * n₁ ≤ n₁ * p₂ / q₂ := calc
    2 * n₁ = n₁ * 2 := mul_comm 2 n₁
    _ ≤ n₁ * n₂ := Nat.mul_le_mul_left n₁ hn₂
    _ ≤ n₁ * p₂ / q₂ := Nat.mul_div_le_mul_div_assoc n₁ p₂ q₂
  apply le_antisymm
  · -- Upper bound: indepNum ≤ min(F₁, F₂)
    apply le_min
    · have := nested_floor_two p₁ q₁ p₂ q₂ hq₁_pos h2q₁ hq₂_pos h2q₂
      rwa [hsimp₁] at this
    · rw [indepNum_strongProduct_comm]
      have := nested_floor_two p₂ q₂ p₁ q₁ hq₂_pos h2q₂ hq₁_pos h2q₁
      rwa [hsimp₂] at this
  · -- Lower bound: min(F₁, F₂) ≤ indepNum
    rcases le_total (n₂ * p₁ / q₁) (n₁ * p₂ / q₂) with h | h
    · -- Case F₁ ≤ F₂
      rw [min_eq_left h]
      haveI : NeZero (n₂ * p₁ / q₁) := ⟨by omega⟩
      exact two_factor_lower_bound (n₁ := n₁) (n₂ := n₂)
        (by omega) hn₂ h2n₂_le
        (mul_div_div_cancel n₂ p₁ q₁ (by omega))
        (nat_div_le_rat_div _ n₂ p₁ q₁ (by omega) hq₁_pos le_rfl)
        (nat_div_le_rat_div _ n₁ p₂ q₂ (by omega) hq₂_pos h)
    · -- Case F₂ ≤ F₁
      rw [min_eq_right h]
      haveI : NeZero (n₁ * p₂ / q₂) := ⟨by omega⟩
      rw [← indepNum_strongProduct_comm]
      exact two_factor_lower_bound (n₁ := n₂) (n₂ := n₁)
        (by omega) hn₁ h2n₁_le
        (mul_div_div_cancel n₁ p₂ q₂ (by omega))
        (nat_div_le_rat_div _ n₁ p₂ q₂ (by omega) hq₂_pos le_rfl)
        (nat_div_le_rat_div _ n₂ p₁ q₁ (by omega) hq₁_pos h)

end Section6
