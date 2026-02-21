import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators

/-- A finset A of positive integers is *unit-fraction-sum-free* if for no
    element a ∈ A can 1/a be expressed as a sum ∑_{b ∈ S} 1/b for some
    nonempty S ⊆ A with a ∉ S. That is, there are no solutions to
    1/a = 1/b₁ + ⋯ + 1/bₖ with distinct a, b₁, …, bₖ ∈ A. -/
def UnitFractionSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A → a ∉ S → S.Nonempty →
    ∑ b ∈ S, (1 : ℝ) / (b : ℝ) ≠ (1 : ℝ) / (a : ℝ)

/--
Erdős Problem #301 [ErGr80]:

Let f(N) be the size of the largest A ⊆ {1, …, N} such that there are no
solutions to 1/a = 1/b₁ + ⋯ + 1/bₖ with distinct a, b₁, …, bₖ ∈ A.

Estimate f(N). In particular, is it true that f(N) = (1/2 + o(1))N?

The example A = (N/2, N] ∩ ℕ shows that f(N) ≥ N/2. Wouter van Doorn
has shown f(N) ≤ (25/28 + o(1))N.

We formalize the conjectured statement: for every ε > 0, for all
sufficiently large N,
(1) every unit-fraction-sum-free A ⊆ {1,…,N} has |A| ≤ (1/2 + ε)N, and
(2) there exists a unit-fraction-sum-free A ⊆ {1,…,N} with |A| ≥ (1/2 - ε)N.
-/
theorem erdos_problem_301 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → UnitFractionSumFree A →
          (A.card : ℝ) ≤ (1 / 2 + ε) * (N : ℝ)) ∧
        (∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ UnitFractionSumFree A ∧
          (A.card : ℝ) ≥ (1 / 2 - ε) * (N : ℝ)) :=
  sorry
