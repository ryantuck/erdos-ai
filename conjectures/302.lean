import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic

open Finset

/-- A finset A of positive integers is *unit-fraction-triple-free* if there are
    no distinct a, b, c ∈ A satisfying 1/a = 1/b + 1/c. -/
def UnitFractionTripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → b ≠ c →
    (1 : ℝ) / (a : ℝ) ≠ (1 : ℝ) / (b : ℝ) + (1 : ℝ) / (c : ℝ)

/--
Erdős Problem #302 [ErGr80]:

Let f(N) be the size of the largest A ⊆ {1, …, N} such that there are no
solutions to 1/a = 1/b + 1/c with distinct a, b, c ∈ A.

Estimate f(N). In particular, is f(N) = (1/2 + o(1))N?

The example A = all odd integers in [1,N] or A = [N/2, N] shows
f(N) ≥ (1/2 + o(1))N. Stijn Cambie improved this to f(N) ≥ (5/8 + o(1))N.
Wouter van Doorn proved f(N) ≤ (9/10 + o(1))N.

Note: The upper bound part (1) of the original conjecture f(N) = (1/2 + o(1))N
has been disproved by Cambie's lower bound. The true asymptotic of f(N) remains
open, with 5/8 ≤ liminf f(N)/N ≤ limsup f(N)/N ≤ 9/10.

We formalize the original conjecture as stated: for every ε > 0, for all
sufficiently large N,
(1) every unit-fraction-triple-free A ⊆ {1,…,N} has |A| ≤ (1/2 + ε)N, and
(2) there exists a unit-fraction-triple-free A ⊆ {1,…,N} with |A| ≥ (1/2 - ε)N.
-/
theorem erdos_problem_302 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → UnitFractionTripleFree A →
          (A.card : ℝ) ≤ (1 / 2 + ε) * (N : ℝ)) ∧
        (∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ UnitFractionTripleFree A ∧
          (A.card : ℝ) ≥ (1 / 2 - ε) * (N : ℝ)) :=
  sorry
