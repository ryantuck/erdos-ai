import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators

/--
Erdős Problem #542 (proved by Schinzel and Szekeres):
If A ⊆ {1, ..., n} is such that lcm(a, b) > n for all distinct a, b ∈ A,
then ∑_{a ∈ A} 1/a ≤ 31/30.

The bound 31/30 = 1/2 + 1/3 + 1/5 is best possible, as A = {2, 3, 5} demonstrates.
-/
theorem erdos_problem_542 :
    ∀ (n : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.lcm a b > n) →
      (∑ a ∈ A, (1 : ℝ) / (a : ℝ)) ≤ 31 / 30 :=
  sorry
