import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic

open Finset

/-- A finset A of positive integers is *unit-fraction-pair-free* if there are
    no distinct a, b ∈ A satisfying (a + b) ∣ (a * b), equivalently, no distinct
    a, b ∈ A such that 1/a + 1/b is a unit fraction. -/
def UnitFractionPairFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬((a + b) ∣ (a * b))

/-- A finset A of positive integers satisfies the strong unit-fraction-pair
    condition if there are no distinct a, b ∈ A satisfying (a + b) ∣ (2 * a * b). -/
def StrongUnitFractionPairFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬((a + b) ∣ (2 * a * b))

/--
Erdős Problem #327, Part 1 [ErGr80]:

Suppose A ⊆ {1, …, N} is such that for all distinct a, b ∈ A,
(a + b) ∤ ab (equivalently, 1/a + 1/b is never a unit fraction).
Can A be 'substantially more' than the odd numbers?

The odd numbers in {1, …, N} give a set of size ~N/2 with this property
(if a and b are both odd, then a + b is even but ab is odd, so (a + b) ∤ ab).

We conjecture the answer is no: the maximum size is (1/2 + o(1))N.

Note: Wouter van Doorn has shown that the density cannot exceed 25/28.

We formalize:
(1) For every ε > 0, for sufficiently large N, every UnitFractionPairFree
    A ⊆ {1,…,N} has |A| ≤ (1/2 + ε)N.
(2) There exists a UnitFractionPairFree A ⊆ {1,…,N} with |A| ≥ (1/2 - ε)N
    (witnessed by the odd numbers).
-/
theorem erdos_problem_327_part1 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → UnitFractionPairFree A →
          (A.card : ℝ) ≤ (1 / 2 + ε) * (N : ℝ)) ∧
        (∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ UnitFractionPairFree A ∧
          (A.card : ℝ) ≥ (1 / 2 - ε) * (N : ℝ)) :=
  sorry

/--
Erdős Problem #327, Part 2 [ErGr80]:

What if a, b ∈ A with a ≠ b implies (a + b) ∤ 2ab? Must |A| = o(N)?

We formalize: for every ε > 0, for all sufficiently large N, every
StrongUnitFractionPairFree A ⊆ {1,…,N} has |A| ≤ εN.
-/
theorem erdos_problem_327_part2 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → StrongUnitFractionPairFree A →
          (A.card : ℝ) ≤ ε * (N : ℝ) :=
  sorry
