import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős Problem #384

If 1 < k < n - 1, then the binomial coefficient C(n, k) is divisible by a prime
p < n/2, with the sole exception of C(7, 3) = C(7, 4) = 35 = 5 × 7.

A conjecture of Erdős and Selfridge, proved by Ecklund [Ec69].

Ecklund made the stronger conjecture that whenever n > k² the binomial coefficient
C(n, k) is divisible by a prime p < n/k.
-/

/--
Erdős Problem #384 [ErGr80, p.73]:

If 1 < k < n - 1, then Nat.choose n k is divisible by some prime p with
2 * p < n (equivalently p < n/2), except when (n, k) = (7, 3) or (7, 4).
-/
theorem erdos_problem_384 :
    ∀ n k : ℕ, 1 < k → k + 1 < n →
    ¬(n = 7 ∧ (k = 3 ∨ k = 4)) →
    ∃ p : ℕ, Nat.Prime p ∧ 2 * p < n ∧ p ∣ Nat.choose n k :=
  sorry
