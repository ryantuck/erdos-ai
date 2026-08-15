import Mathlib.SetTheory.Cardinal.Aleph

noncomputable section

open Cardinal Ordinal

/-!
# Erdős Problem #1168

A problem of Erdős, Hajnal, and Rado.

Prove that ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, …, 3)_{ℵ₀}² without assuming the generalised
continuum hypothesis.

This negative partition relation states that there exists a coloring of pairs
from a set of cardinality ℵ_{ω+1} using countably many colors such that:
- There is no monochromatic set of cardinality ℵ_{ω+1} for the first color
- There is no monochromatic triple for any other color

Tags: set theory, ramsey theory
-/

/--
Erdős Problem #1168 [Va99, 7.80]:

The negative partition relation ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, …, 3)_{ℵ₀}²:
for any type α of cardinality ℵ_{ω+1}, there exists a coloring of unordered pairs
of elements of α with countably many colors (indexed by ℕ) such that:
- No set of cardinality ℵ_{ω+1} is monochromatic in color 0
- No triple is monochromatic in any color n ≥ 1
-/
theorem erdos_problem_1168 :
    ∀ (α : Type*) (_ : #α = ℵ_ (ω + 1)),
    ∃ (c : α → α → ℕ),
      -- The coloring is symmetric
      (∀ a b, c a b = c b a) ∧
      -- No monochromatic set of cardinality ℵ_{ω+1} for color 0
      (∀ S : Set α, #S = ℵ_ (ω + 1) →
        ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ c a b ≠ 0) ∧
      -- No monochromatic triple for any color n ≥ 1
      (∀ (n : ℕ), n ≥ 1 →
        ∀ a b d : α, a ≠ b → a ≠ d → b ≠ d →
          ¬(c a b = n ∧ c a d = n ∧ c b d = n)) :=
  sorry

end
