import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic

open Nat

/-!
# Erdős Problem #649

Let $P(m)$ denote the greatest prime factor of $m$. Is it true that, for any
two primes $p, q$, there exists some integer $n$ such that $P(n) = p$ and
$P(n+1) = q$?

The answer is **no** (disproved). There are no solutions to $2^k \equiv -1 \pmod{7}$,
so this fails with $p = 2$ and $q = 7$. Alan Tong proved that for any given prime $p$,
there are infinitely many primes $q$ for which the statement is false.

Reference: [Er95c]
https://www.erdosproblems.com/649
-/

/-- The greatest prime factor of n, or 0 if n ≤ 1. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldr max 0

/--
Erdős Problem #649 (disproved):

The original conjecture asks whether for any two primes p, q there exists
an integer n such that P(n) = p and P(n+1) = q. This is false.

We formalise the negation: there exist primes p, q such that no positive
integer n has P(n) = p and P(n+1) = q.
-/
theorem erdos_problem_649 :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
      ¬∃ n : ℕ, 0 < n ∧ greatestPrimeFactor n = p ∧ greatestPrimeFactor (n + 1) = q :=
  sorry
