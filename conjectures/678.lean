import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat

open Finset

/--
M(n, k) = lcm{n+1, n+2, ..., n+k}, the least common multiple of k consecutive
integers starting from n+1.
-/
def lcmConsecutive (n k : ℕ) : ℕ :=
  (Finset.Icc (n + 1) (n + k)).lcm id

/--
Erdős Problem #678 [Er79, Er92e]:

Let M(n,k) = [n+1, ..., n+k] be the least common multiple of {n+1, ..., n+k}.
Are there infinitely many m, n and k ≥ 3 with m ≥ n + k such that
M(n,k) > M(m,k+1)?

The answer is yes, as proved by Cambie [Ca24].
-/
theorem erdos_problem_678 :
    ∀ N : ℕ, ∃ n m k : ℕ, k ≥ 3 ∧ m ≥ n + k ∧ n ≥ N ∧
      lcmConsecutive n k > lcmConsecutive m (k + 1) :=
  sorry
