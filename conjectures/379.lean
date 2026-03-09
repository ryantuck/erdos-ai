import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

open Nat

/--
Erdős Problem #379 [ErGr80,p.72]:

Let S(n) denote the largest integer such that, for all 1 ≤ k < n, the
binomial coefficient C(n,k) is divisible by p^{S(n)} for some prime p
(depending on k). Is it true that lim sup S(n) = ∞?

Equivalently: for every M, there exists n such that for every 1 ≤ k < n,
some prime power p^M divides C(n,k).

This was solved in the affirmative by Cambie, Kovač, and Tao.
-/
theorem erdos_problem_379 :
    ∀ M : ℕ, ∃ n : ℕ, 2 ≤ n ∧
      ∀ k : ℕ, 1 ≤ k → k < n →
        ∃ p : ℕ, Nat.Prime p ∧ p ^ M ∣ Nat.choose n k :=
  sorry
