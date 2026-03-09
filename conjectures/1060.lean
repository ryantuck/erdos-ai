import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped ArithmeticFunction.sigma

/--
The number of solutions k to k * σ(k) = n.
-/
noncomputable def countSolns (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).filter (fun k => k * σ 1 k = n) |>.card

/--
Erdős Problem #1060 [Gu04]:

Let f(n) count the number of solutions to k·σ(k) = n, where σ(k) is the sum
of divisors of k. Is it true that f(n) ≤ n^{o(1/log log n)}?

More precisely, for every ε > 0, there exists N such that for all n ≥ N,
f(n) ≤ n^{ε / log(log n)}.

Perhaps even f(n) ≤ (log n)^{O(1)}?
-/
theorem erdos_problem_1060_weak :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (countSolns n : ℝ) ≤ (n : ℝ) ^ (ε / Real.log (Real.log n)) :=
  sorry

/--
Stronger form of Erdős Problem #1060: f(n) ≤ (log n)^{O(1)}.

There exists a constant C such that for all n ≥ 2,
the number of solutions to k·σ(k) = n is at most (log n)^C.
-/
theorem erdos_problem_1060_strong :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        (countSolns n : ℝ) ≤ (Real.log n) ^ C :=
  sorry
