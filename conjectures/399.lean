import Mathlib.Data.Nat.Factorial.Basic

/--
Erdős Problem #399 [ErGr80, p.77]:

Is it true that there are no solutions to
  n! = xᵏ ± yᵏ
with x, y, n ∈ ℕ, xy > 1 and k > 2?

DISPROVED by Jonas Barfield, who found:
  10! = 48⁴ - 36⁴ = 3628800.

The formalization states the negation: there exist n, x, y, k with
xy > 1, k > 2, and n! = xᵏ - yᵏ (the minus case suffices for the
counterexample).
-/
theorem erdos_problem_399 :
    ∃ n x y k : ℕ, x * y > 1 ∧ k > 2 ∧ n.factorial = x ^ k - y ^ k :=
  sorry
