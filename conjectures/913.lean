import Mathlib.Data.Nat.Factorization.Basic

/--
The prime factorisation of a natural number has all distinct exponents:
for any two distinct primes p, q dividing n, their exponents in the
factorisation of n are different.
-/
def HasDistinctExponents (n : ℕ) : Prop :=
  ∀ p q : ℕ, p ∈ n.factorization.support → q ∈ n.factorization.support →
    n.factorization p = n.factorization q → p = q

/--
Erdős Problem #913 [Er82c,p.28]:

Are there infinitely many n such that if n(n+1) = ∏ pᵢ^{kᵢ} is the
factorisation into distinct primes, then all exponents kᵢ are distinct?

It is likely that there are infinitely many primes p such that 8p²−1 is
also prime, in which case this is true with exponents {1,2,3}, letting
n = 8p²−1.
-/
theorem erdos_problem_913 :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ HasDistinctExponents (n * (n + 1)) :=
  sorry
