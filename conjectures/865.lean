import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset

/--
Erdős Problem #865 [Er72, CES75, Er92c]:

There exists a constant C > 0 such that, for all large N, if A ⊆ {1,…,N}
has size at least (5/8)N + C then there are distinct a, b, c ∈ A such that
a + b, a + c, b + c ∈ A.

A problem of Erdős and Sós. Taking all integers in [N/8, N/4] and [N/2, N]
shows that 5/8 would be best possible.
-/
theorem erdos_problem_865 :
    ∃ C : ℝ, 0 < C ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ,
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
          (A.card : ℝ) ≥ 5 / 8 * N + C →
          ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
            a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
            a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A :=
  sorry
