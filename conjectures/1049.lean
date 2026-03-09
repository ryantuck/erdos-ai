import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational

open scoped Topology

/--
Erdős Problem #1049 [Er88c,p.102]:

Let t > 1 be a rational number. Is
  ∑_{n=1}^∞ 1/(t^n - 1) = ∑_{n=1}^∞ τ(n)/t^n
irrational, where τ(n) counts the divisors of n?

A conjecture of Chowla. Erdős proved that this is true if t ≥ 2 is an integer.
-/
theorem erdos_problem_1049
    (t : ℚ) (ht : 1 < t) :
    Irrational (∑' (n : ℕ), (1 : ℝ) / ((t : ℝ) ^ (n + 1) - 1)) :=
  sorry
