import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Finset Real

namespace Erdos1138

/-- The maximal gap between consecutive primes up to x.
    For each index k with the k-th prime (0-indexed) less than x,
    compute the gap to the next prime and take the maximum.
    Returns 0 when there are no primes less than x. -/
noncomputable def maxPrimeGap (x : ℕ) : ℕ :=
  (Finset.range (Nat.primeCounting' x)).sup
    (fun k => Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k)

/--
Erdős Problem #1138 [Va99, 1.3]:

Let x/2 < y < x and C > 1. If d = max_{p_n < x} (p_{n+1} - p_n) is the maximal
prime gap below x, where p_n denotes the n-th prime, then is it true that
  π(y + Cd) - π(y) ~ Cd / log y?

In other words, the expected asymptotic formula for the number of primes in the
interval [y, y + Cd] holds. This is a combination of two well-studied problems:
finding the minimum h for which π(y + h) - π(y) ~ h / log y, and understanding
the maximal prime gap d. The conjectured size of d is ≈ (log x)², which is far
below the h obtainable even assuming the Riemann hypothesis.

Tags: number theory, primes
-/
theorem erdos_problem_1138 (C : ℝ) (hC : 1 < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∀ y : ℕ, x < 2 * y → y < x →
        |((Nat.primeCounting (y + ⌊C * (maxPrimeGap x : ℝ)⌋₊) : ℝ) -
          (Nat.primeCounting y : ℝ)) /
          (C * (maxPrimeGap x : ℝ) / Real.log (y : ℝ)) - 1| < ε :=
  sorry

end Erdos1138
