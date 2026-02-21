import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Set

noncomputable section

/-!
# Erdős Problem #157

Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

Answered YES by Pilatte [Pi23].
-/

/-- An infinite set A ⊆ ℕ is a Sidon set (B₂ set) if all pairwise sums
    are distinct: whenever a + b = c + d with a, b, c, d ∈ A, we have
    {a, b} = {c, d} as multisets (i.e. either a = c and b = d, or a = d and b = c). -/
def IsInfiniteSidonSet (A : Set ℕ) : Prop :=
  Set.Infinite A ∧
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A set A ⊆ ℕ is an asymptotic basis of order 3 if every sufficiently
    large natural number can be represented as a sum of (exactly) 3 elements
    (with repetition allowed) from A. -/
def IsAsymptoticBasisOrder3 (A : Set ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, n = a + b + c

/--
Erdős Problem #157 [ESS94, Er94b]:

Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

A set A ⊆ ℕ is a Sidon set if all pairwise sums a + b (a, b ∈ A) are distinct.
A set A is an asymptotic basis of order 3 if every sufficiently large integer
is the sum of 3 elements from A.

Answered YES by Pilatte [Pi23].

Formalized as: there exists an infinite set A ⊆ ℕ that is a Sidon set and
an asymptotic basis of order 3.
-/
theorem erdos_problem_157 :
    ∃ A : Set ℕ, IsInfiniteSidonSet A ∧ IsAsymptoticBasisOrder3 A :=
  sorry

end
