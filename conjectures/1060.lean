import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Nat Finset BigOperators

noncomputable section

/-!
# Erdős Problem #1060

Let f(n) count the number of solutions to k·σ(k) = n, where σ(k) is the sum
of divisors of k. Is it true that f(n) ≤ n^{o(1/log log n)}? Perhaps even
f(n) ≤ (log n)^{O(1)}?

This is discussed in problem B11 of Guy's collection [Gu04].
-/

/-- The sum of divisors function σ(k). -/
def sumOfDivisors (k : ℕ) : ℕ := ∑ d ∈ k.divisors, d

/-- f(n): the number of positive integers k such that k · σ(k) = n. -/
def erdos1060_f (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => k * sumOfDivisors k = n)).card

/--
Erdős Problem #1060 (weak form):
f(n) ≤ n^{o(1/log log n)}.

Formalized as: for every ε > 0, for all sufficiently large n,
  f(n) ≤ n^{ε / log(log n)}.
-/
theorem erdos_problem_1060_weak :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos1060_f n : ℝ) ≤ (n : ℝ) ^ (ε / Real.log (Real.log (n : ℝ))) :=
  sorry

/--
Erdős Problem #1060 (strong form):
f(n) ≤ (log n)^{O(1)}.

Formalized as: there exist constants C > 0 such that for all sufficiently
large n, f(n) ≤ (log n)^C.
-/
theorem erdos_problem_1060_strong :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos1060_f n : ℝ) ≤ (Real.log (n : ℝ)) ^ C :=
  sorry

end
