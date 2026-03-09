import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real

noncomputable section

/--
The Erdős prime gap expression at index n:
  (log log n · log log log log n) / (log log log n)² · log n

This is the function appearing in Erdős' conjecture on large gaps between
consecutive primes.
-/
def erdosPrimeGapBound (n : ℕ) : ℝ :=
  let x := (n : ℝ)
  (Real.log (Real.log x) * Real.log (Real.log (Real.log (Real.log x)))) /
    (Real.log (Real.log (Real.log x))) ^ 2 * Real.log x

/--
Erdős Problem #4 [Er55c, Er57, Er61, Er65b, Er81k, Er82e, Er90, Er97c, Er97f]:

Is it true that, for any C > 0, there are infinitely many n such that
  p_{n+1} - pₙ > C · (log log n · log log log log n) / (log log log n)² · log n?

The peculiar quantitative form was motivated by an old result of Rankin (1938),
who proved the claim for some fixed C > 0. Solved by Maynard (2016) and
Ford–Green–Konyagin–Tao (2016). The best bound, due to all five authors (2018),
removes the square in the denominator.
-/
theorem erdos_problem_4 :
    ∀ C : ℝ, 0 < C →
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
        (nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ) >
          C * erdosPrimeGapBound n :=
  sorry

end
