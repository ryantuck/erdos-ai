import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Int.Basic

open Classical

noncomputable section

/-!
# Erdős Problem #454

Let f(n) = min_{i<n} (p_{n+i} + p_{n-i}), where p_k is the kth prime.
Is it true that limsup_n (f(n) - 2·p_n) = ∞?

Pomerance [Po79] has proved the limsup is at least 2.

Tags: number theory, primes
-/

/-- The kth prime (0-indexed): nthPrime 0 = 2, nthPrime 1 = 3, nthPrime 2 = 5, ... -/
noncomputable def erdos454_nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/--
Erdős Problem #454 [ErGr80, p.90]:

Let f(n) = min_{i<n} (p_{n+i} + p_{n-i}), where p_k is the kth prime.
The conjecture states that limsup_n (f(n) - 2·p_n) = ∞.

Equivalently: for every bound M, there exist arbitrarily large n such that
  p_{n+i} + p_{n-i} - 2·p_n ≥ M  for all 0 < i < n.
-/
theorem erdos_problem_454 :
    ∀ M : ℤ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ i : ℕ, 0 < i → i < n →
        (erdos454_nthPrime (n + i) : ℤ) + (erdos454_nthPrime (n - i) : ℤ) -
          2 * (erdos454_nthPrime n : ℤ) ≥ M :=
  sorry

end
