import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset Nat BigOperators

/--
Erdős Problem #383 [ErGr80]:

Is it true that for every k there are infinitely many primes p such that the
largest prime divisor of ∏_{0 ≤ i ≤ k} (p² + i) is p?

Heuristically, the 'probability' that n has no prime divisors ≥ n^{1/2} is
1 - log 2 > 0, so standard heuristics predict the answer is yes.
-/
theorem erdos_problem_383 :
    ∀ k : ℕ, ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ p ≥ N ∧
      ∀ q : ℕ, q.Prime →
        q ∣ ∏ i ∈ range (k + 1), (p ^ 2 + i) →
        q ≤ p :=
  sorry
