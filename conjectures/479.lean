import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.ModEq

/--
Erdős Problem #479 [ErGr80, p.96]:

Is it true that, for all k ≠ 1, there are infinitely many n such that
2^n ≡ k (mod n)?

A conjecture of Graham. It is easy to see that 2^n ≢ 1 (mod n) for all
n > 1, so the restriction k ≠ 1 is necessary. As an indication of
difficulty, when k = 3 the smallest such n is n = 4700063497.
-/
theorem erdos_problem_479 (k : ℕ) (hk : k ≠ 1) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ 2 ^ n % n = k % n :=
  sorry
