import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Finset BigOperators

/-- A finset A of positive integers is *Egyptian-1-free* if no nonempty subset S ⊆ A
    has ∑_{n ∈ S} 1/n = 1. -/
def Egyptian1Free (A : Finset ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ≠ 1

/--
Erdős Problem #300 [ErGr80] [Va99, 1.14]:

Let A(N) denote the maximal cardinality of A ⊆ {1,...,N} such that ∑_{n ∈ S} 1/n ≠ 1
for all nonempty S ⊆ A. Estimate A(N).

Erdős and Graham believed A(N) = (1 + o(1))N. Croot [Cr03] disproved this, showing
the existence of some constant c < 1 such that A(N) < cN for all large N. It is
trivial that A(N) ≥ (1 - 1/e + o(1))N.

Liu and Sawhney [LiSa24] proved that A(N) = (1 - 1/e + o(1))N, resolving the problem.

We formalize the resolved statement: for every ε > 0, for all sufficiently large N,
(1) every Egyptian-1-free A ⊆ {1,...,N} has |A| ≤ (1 - 1/e + ε)N, and
(2) there exists an Egyptian-1-free A ⊆ {1,...,N} with |A| ≥ (1 - 1/e - ε)N.
-/
theorem erdos_problem_300 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → Egyptian1Free A →
          (A.card : ℝ) ≤ (1 - Real.exp (-1) + ε) * (N : ℝ)) ∧
        (∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ Egyptian1Free A ∧
          (A.card : ℝ) ≥ (1 - Real.exp (-1) - ε) * (N : ℝ)) :=
  sorry
