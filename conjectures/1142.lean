import Mathlib.Data.Nat.Prime.Basic

open Nat

/--
A natural number n has the property that n - 2^k is prime
for every k ≥ 1 with 2^k < n.
-/
def AllPowerOfTwoComplementsPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → 2 ^ k < n → (n - 2 ^ k).Prime

/--
Erdős Problem #1142 [Va99, 1.7]:

Are there infinitely many n such that n - 2^k is prime for all 1 < 2^k < n?

The only known such n are 4, 7, 15, 21, 45, 75, 105 (OEIS A039669).
Mientka and Weitzenkamp proved there are no other such n ≤ 2^44.
Vaughan proved the count of such n ≤ N is at most
exp(-c · (log log log N / log log N) · log N) · N for some c > 0.

Tags: number theory, primes
-/
theorem erdos_problem_1142 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ AllPowerOfTwoComplementsPrime n :=
  sorry
