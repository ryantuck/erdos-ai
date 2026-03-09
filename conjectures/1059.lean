import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

/--
Erdős Problem #1059 [Gu04]:

Are there infinitely many primes $p$ such that $p - k!$ is composite for each
$k$ such that $1 \leq k! < p$?

Examples include $p = 101$ and $p = 211$.
-/
theorem erdos_problem_1059 :
    Set.Infinite {p : ℕ | Nat.Prime p ∧
      ∀ k : ℕ, 1 ≤ k.factorial → k.factorial < p →
        ¬ (p - k.factorial).Prime} :=
  sorry
