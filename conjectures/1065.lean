import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #1065

Are there infinitely many primes p such that p = 2^k · q + 1 for some prime q
and k ≥ 0? Or p = 2^k · 3^l · q + 1?

A problem mentioned in Guy's collection [Gu04], problem B46.
-/

/--
Erdős Problem #1065, part 1 [Gu04]:

There are infinitely many primes p such that p = 2^k · q + 1 for some
prime q and some k ≥ 0.
-/
theorem erdos_problem_1065a :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ k q : ℕ, q.Prime ∧ p = 2 ^ k * q + 1} :=
  sorry

/--
Erdős Problem #1065, part 2 [Gu04]:

There are infinitely many primes p such that p = 2^k · 3^l · q + 1 for some
prime q and some k, l ≥ 0.
-/
theorem erdos_problem_1065b :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ k l q : ℕ, q.Prime ∧ p = 2 ^ k * 3 ^ l * q + 1} :=
  sorry
