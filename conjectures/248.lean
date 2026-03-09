import Mathlib.Data.Nat.PrimeFin

/--
Erdős Problem #248 [Er74b, ErGr80] (PROVED):

Are there infinitely many n such that, for all k ≥ 1, ω(n+k) ≪ k?
(Here ω(n) is the number of distinct prime divisors of n.)

Proved by Tao and Teräväinen [TaTe25], who showed there exists an
absolute constant C > 0 such that for infinitely many n, for all k ≥ 1,
ω(n+k) ≤ C·k.
-/
theorem erdos_problem_248 :
    ∃ C : ℕ, 0 < C ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        ∀ k : ℕ, 1 ≤ k → (n + k).primeFactors.card ≤ C * k :=
  sorry
