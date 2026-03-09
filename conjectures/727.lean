import Mathlib.Data.Nat.Factorial.Basic

open Nat

/--
Erdős Problem #727 [EGRS75]:

Let k ≥ 2. Does (n+k)!² ∣ (2n)! for infinitely many n?

A conjecture of Erdős, Graham, Ruzsa, and Straus. It is open even for k = 2.
Balakran proved the case k = 1, i.e., (n+1)² ∣ C(2n,n) for infinitely many n.
-/
theorem erdos_problem_727
    (k : ℕ) (hk : 2 ≤ k) :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      (n + k).factorial ^ 2 ∣ (2 * n).factorial :=
  sorry
