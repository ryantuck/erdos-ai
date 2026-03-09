import Mathlib.NumberTheory.Divisors

/--
Erdős Problem #826 [Er74b] (OPEN):

Are there infinitely many n such that, for all k ≥ 1, τ(n+k) ≪ k?
(Here τ(n) is the number of divisors of n.)

A stronger form of [248], which asks the same with ω(n) (number of
distinct prime divisors) in place of τ(n).
-/
theorem erdos_problem_826 :
    ∃ C : ℕ, 0 < C ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        ∀ k : ℕ, 1 ≤ k → (Nat.divisors (n + k)).card ≤ C * k :=
  sorry
