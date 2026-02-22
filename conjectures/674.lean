import Mathlib.Data.Nat.Basic

/-!
# Erdős Problem #674

Are there any integer solutions to x^x * y^y = z^z with x, y, z > 1?

Ko [Ko40] proved there are none if gcd(x, y) = 1, but there are in fact
infinitely many solutions in general - for example,
  x = 2^12 * 3^6, y = 2^8 * 3^8, z = 2^11 * 3^7.

In [Er79] Erdős asked if the infinite families found by Ko are the only
solutions.
-/

/--
Erdős Problem #674:
There exist natural numbers x, y, z > 1 such that x^x * y^y = z^z.
-/
theorem erdos_problem_674 :
    ∃ x y z : ℕ, x > 1 ∧ y > 1 ∧ z > 1 ∧ x ^ x * y ^ y = z ^ z :=
  sorry
