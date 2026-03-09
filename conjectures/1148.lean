import Mathlib.Data.Int.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/--
Erdős Problem #1148 [Va99,1.25]:

Can every large integer n be written as n = x² + y² - z² with
max(x², y², z²) ≤ n?

The largest integer known which cannot be written this way is 6563.
-/
theorem erdos_problem_1148 :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ x y z : ℕ, (x ^ 2 + y ^ 2 : ℤ) - z ^ 2 = n ∧
        x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n :=
  sorry
