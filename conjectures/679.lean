import Mathlib.Data.Nat.Factors
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat

open Real Classical

noncomputable section

/-!
# Erdős Problem #679

Let ε > 0 and ω(n) count the number of distinct prime factors of n.
Are there infinitely many values of n such that
  ω(n - k) < (1 + ε) * log k / log log k
for all k < n which are sufficiently large depending on ε only?

Can one show the stronger version with
  ω(n - k) < log k / log log k + O(1)
is false?

The second (stronger) version has been disproved by DottedCalculator, who
proved that for all large n there exists k < n such that
  ω(n - k) ≥ log k / log log k + c * log k / (log log k)²
for some constant c > 0.

Reference: [Er79d]
https://www.erdosproblems.com/679
-/

/-- The number of distinct prime factors of n (ω(n) in analytic number theory). -/
noncomputable def erdos679_omega (n : ℕ) : ℕ :=
  (Nat.primeFactorsList n).toFinset.card

/--
Erdős Problem #679, Part 1 (open) [Er79d]:

For every ε > 0, there are infinitely many n such that for all sufficiently
large k (with 1 ≤ k < n), we have ω(n - k) < (1 + ε) * log k / log log k.

Here "sufficiently large" means there exists a threshold k₀ depending on ε
(but not on n) such that the bound holds for all k ≥ k₀ with k < n.
-/
theorem erdos_problem_679_part1 :
    ∀ ε : ℝ, ε > 0 →
    ∃ k₀ : ℕ,
    Set.Infinite {n : ℕ |
      ∀ k : ℕ, k₀ ≤ k → k < n →
        (erdos679_omega (n - k) : ℝ) <
          (1 + ε) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))} :=
  sorry

/--
Erdős Problem #679, Part 2 (disproved by DottedCalculator) [Er79d]:

The stronger version asking whether ω(n - k) < log k / log log k + O(1)
holds for infinitely many n is false. In fact, there exists a constant c > 0
such that for all sufficiently large n, there exists k < n with
  ω(n - k) ≥ log k / log log k + c * log k / (log log k)².
-/
theorem erdos_problem_679_part2 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ k : ℕ, k < n ∧
        (erdos679_omega (n - k) : ℝ) ≥
          Real.log (k : ℝ) / Real.log (Real.log (k : ℝ)) +
          c * Real.log (k : ℝ) / (Real.log (Real.log (k : ℝ))) ^ 2 :=
  sorry

end
