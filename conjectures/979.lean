import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
Erdős Problem #979 [Er65b,p.224]:

Let k ≥ 2, and let f_k(n) count the number of solutions to
  n = p₁ᵏ + ⋯ + pₖᵏ,
where the pᵢ are prime numbers. Is it true that lim sup f_k(n) = ∞?

Equivalently: for every k ≥ 2 and every bound M, there exists n such that
f_k(n) ≥ M, i.e., n can be represented as a sum of k k-th powers of primes
in at least M distinct ways.

Erdős proved this for k = 2 and k = 3.
-/
theorem erdos_problem_979 (k : ℕ) (hk : 2 ≤ k) (M : ℕ) :
    ∃ n : ℕ, ∃ S : Finset (Fin k → ℕ),
      M ≤ S.card ∧
      (∀ f ∈ S, (∀ i, Nat.Prime (f i)) ∧ ∑ i, f i ^ k = n) :=
  sorry
