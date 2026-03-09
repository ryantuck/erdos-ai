import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

/--
Erdős Problem #1065 [Gu04]:

Are there infinitely many primes p such that p = 2^k * q + 1 for some prime q
and k ≥ 0?
-/
theorem erdos_problem_1065a :
    {p : ℕ | p.Prime ∧ ∃ k : ℕ, ∃ q : ℕ, q.Prime ∧ p = 2 ^ k * q + 1}.Infinite :=
  sorry

/--
Erdős Problem #1065 (second part) [Gu04]:

Are there infinitely many primes p such that p = 2^k * 3^l * q + 1 for some
prime q and k, l ≥ 0?
-/
theorem erdos_problem_1065b :
    {p : ℕ | p.Prime ∧ ∃ k l : ℕ, ∃ q : ℕ, q.Prime ∧ p = 2 ^ k * 3 ^ l * q + 1}.Infinite :=
  sorry
