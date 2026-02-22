import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

open Set

/-!
# Erdős Problem #1058

Let $2 = p_1 < p_2 < \cdots$ be the sequence of prime numbers. Are there only
finitely many $n$ such that $n \in [p_{k-1}, p_k)$ and the only primes dividing
$n! + 1$ are $p_k$ and $p_{k+1}$?

A conjecture of Erdős and Stewart, as reported in problem A2 of Guy's
collection [Gu04]. The only known cases are $n = 1, 2, 3, 4, 5$.

Luca [Lu01] proved that indeed these are the only solutions.

https://www.erdosproblems.com/1058
-/

/--
Erdős Problem #1058 (Erdős–Stewart conjecture):

There are only finitely many natural numbers `n` such that every prime
divisor of `n! + 1` belongs to `{q, r}`, where `q` is the smallest prime
greater than `n` and `r` is the smallest prime greater than `q`.

Equivalently, if `p_{k-1} ≤ n < p_k` in the sequence of primes,
then `n! + 1` has no prime factor other than `p_k` and `p_{k+1}`.

Proved by Luca (2001): the only solutions are `n = 1, 2, 3, 4, 5`.
-/
theorem erdos_problem_1058 :
    Set.Finite {n : ℕ | ∃ (q r : ℕ),
      -- q is the smallest prime strictly greater than n
      Nat.Prime q ∧ n < q ∧ (∀ p, Nat.Prime p → n < p → q ≤ p) ∧
      -- r is the next prime after q
      Nat.Prime r ∧ q < r ∧ (∀ p, Nat.Prime p → q < p → r ≤ p) ∧
      -- every prime factor of n! + 1 is either q or r
      (∀ p, Nat.Prime p → p ∣ (n.factorial + 1) → p = q ∨ p = r)} :=
  sorry
