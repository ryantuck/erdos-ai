import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #370

Are there infinitely many n such that the largest prime factor of n is < n^{1/2}
and the largest prime factor of n+1 is < (n+1)^{1/2}?

This has a trivial solution: take n = m² − 1 for m such that m and m+1 are both
composite. Then n = (m−1)(m+1) so every prime factor of n is ≤ m+1 < n^{1/2},
and n+1 = m² so every prime factor of n+1 is ≤ m < (n+1)^{1/2}.

See also [369] and [928].
-/

/--
Erdős Problem #370 [ErGr80, p.69]:

There are infinitely many n such that every prime factor of n is < n^{1/2}
and every prime factor of n+1 is < (n+1)^{1/2}.
-/
theorem erdos_problem_370 :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (∀ p ∈ n.primeFactorsList, (p : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ)) ∧
      (∀ p ∈ (n + 1).primeFactorsList, (p : ℝ) < ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) :=
  sorry
