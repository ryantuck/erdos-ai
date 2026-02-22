import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.Real.Irrational

open Finset

noncomputable section

/-!
# Erdős Problem #1049

Let t > 1 be a rational number. Is
  ∑_{n=1}^∞ 1/(t^n - 1) = ∑_{n=1}^∞ τ(n)/t^n
irrational, where τ(n) counts the divisors of n?

A conjecture of Chowla. Erdős [Er48] proved that this is true if t ≥ 2 is
an integer.
-/

/--
Erdős Problem #1049 [Er88c,p.102]:

For every rational number t > 1, the sum ∑_{n=1}^∞ τ(n)/t^n is irrational,
where τ(n) is the number of divisors of n.

Equivalently, ∑_{n=1}^∞ 1/(t^n - 1) is irrational.
-/
theorem erdos_problem_1049 (t : ℚ) (ht : t > 1) :
    Irrational (∑' (n : ℕ), ((Nat.divisors (n + 1)).card : ℝ) / (t : ℝ) ^ (n + 1)) :=
  sorry

end
