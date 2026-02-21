import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Fintype.Fin

open Finset BigOperators

/--
Erdős Problem #493 (attributed to Schinzel):
Does there exist a k such that every sufficiently large integer can be written
in the form ∏ᵢ aᵢ - ∑ᵢ aᵢ for some integers aᵢ ≥ 2?

The answer is yes with k = 2: for any integer n we have
  n = 2·(n+2) - (2 + (n+2)).
-/
theorem erdos_problem_493 :
    ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, n ≥ N →
      ∃ a : Fin k → ℤ, (∀ i, a i ≥ 2) ∧
        (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n :=
  sorry
