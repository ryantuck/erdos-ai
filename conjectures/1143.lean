import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

namespace Erdos1143

/-- Count of integers in {n+1, ..., n+k} divisible by at least one element of `S`. -/
def countDivisible (S : Finset ℕ) (k n : ℕ) : ℕ :=
  ((Finset.Icc (n + 1) (n + k)).filter (fun m =>
    (S.filter (· ∣ m)).Nonempty)).card

/--
Erdős Problem #1143 [Va99, 1.8]:

Let p₁ < ⋯ < p_u be primes and k ≥ 1. Define F_k(p₁,…,p_u) to be the
minimum, over all starting points n ≥ 0, of the count of integers in
{n+1, …, n+k} that are divisible by at least one pᵢ.

Estimate F_k(p₁,…,p_u), particularly in the range k = α·p_u for constant α > 2.

Erdős and Selfridge found the exact bound when 2 < α < 3.
For α > 3, very little is known.

We formalize a sieve lower bound: for any finite set of primes S,
every interval of k consecutive positive integers contains at least
k·(1 - ∏_{p∈S}(1 - 1/p)) - 2^|S| multiples of some element of S.
The open problem is to determine sharper estimates, particularly
the exact value of F_k for α > 3.

Tags: number theory, primes
-/
theorem erdos_problem_1143 (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (hne : S.Nonempty) (k : ℕ) (hk : 0 < k) :
    ∀ n : ℕ,
      (countDivisible S k n : ℝ) ≥
        (k : ℝ) * (1 - S.prod (fun p => (1 - 1 / (p : ℝ)))) - (2 : ℝ) ^ S.card :=
  sorry

end Erdos1143
