import Mathlib.Data.Rat.Defs

/--
Erdős Problem #242 [Er50c, Er61, Er79, ErGr80, Va99]:

The Erdős–Straus conjecture. For every n > 2 there exist distinct positive
integers 1 ≤ x < y < z such that
  4/n = 1/x + 1/y + 1/z.

This has been verified for all n ≤ 10^18.
-/
theorem erdos_problem_242 :
    ∀ n : ℕ, 2 < n →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x < y ∧ y < z ∧
        (4 : ℚ) / n = 1 / x + 1 / y + 1 / z :=
  sorry
