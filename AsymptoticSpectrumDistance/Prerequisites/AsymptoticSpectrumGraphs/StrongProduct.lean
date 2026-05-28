/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# Strong Product of Graphs

The strong product G ⊠ H of two graphs.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace ShannonCapacity

variable {V W : Type*}

/-- The strong product of two simple graphs.
    Vertices (a,x) and (b,y) are adjacent iff
    (a = b ∨ a ~ b) ∧ (x = y ∨ x ~ y) and (a,x) ≠ (b,y). -/
def strongProduct (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj p q := p ≠ q ∧ (p.1 = q.1 ∨ G.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ H.Adj p.2 q.2)
  symm := by
    intro p q ⟨hne, h1, h2⟩
    refine ⟨hne.symm, ?_, ?_⟩
    · cases h1 with
      | inl h => left; exact h.symm
      | inr h => right; exact h.symm
    · cases h2 with
      | inl h => left; exact h.symm
      | inr h => right; exact h.symm
  loopless := ⟨fun _ ⟨hne, _, _⟩ => (hne rfl).elim⟩

@[inherit_doc] infixl:70 " ⊠ " => strongProduct

theorem strongProduct_adj {G : SimpleGraph V} {H : SimpleGraph W} {p q : V × W} :
    (G ⊠ H).Adj p q ↔
    p ≠ q ∧ (p.1 = q.1 ∨ G.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ H.Adj p.2 q.2) := Iff.rfl

end ShannonCapacity
