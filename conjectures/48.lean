import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors

open Finset Nat

/-- The sum of divisors function σ(n) = Σ_{d | n} d. -/
def sumDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/--
Erdős Problem #48 [Er59c, Er74b, ErGr80, Er95]:

Are there infinitely many integers n, m such that φ(n) = σ(m)?

This would follow immediately from the twin prime conjecture. The answer is yes,
proved by Ford, Luca, and Pomerance [FLP10].
-/
theorem erdos_problem_48 :
    ∀ N : ℕ, ∃ n m : ℕ, n ≥ N ∧ 0 < n ∧ 0 < m ∧
      Nat.totient n = sumDivisors m :=
  sorry
