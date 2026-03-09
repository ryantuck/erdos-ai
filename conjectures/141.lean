import Mathlib.Data.Nat.Prime.Basic

open Nat

/--
Erdős Problem #141 [Er75b, Er83, Er97c]:
Let k ≥ 3. Are there k consecutive primes in arithmetic progression?

That is, for every k ≥ 3, there exist a first prime a and common difference d > 0
such that a, a + d, a + 2d, ..., a + (k-1)d are all prime and consecutive
(no prime lies strictly between a + i*d and a + (i+1)*d for each i).

Green and Tao proved that there always exist k primes in arithmetic progression,
but these need not be consecutive. Verified for k ≤ 10.
-/
theorem erdos_problem_141 :
    ∀ k : ℕ, 3 ≤ k →
    ∃ a d : ℕ, 0 < d ∧
      (∀ i : ℕ, i < k → Nat.Prime (a + i * d)) ∧
      (∀ i : ℕ, i + 1 < k →
        ∀ p : ℕ, a + i * d < p → p < a + (i + 1) * d → ¬ Nat.Prime p) :=
  sorry
