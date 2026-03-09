import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic

open Nat

/--
Erdős Problem #385 [Er79d,p.73] [ErGr80,p.74]:

Let F(n) = max over composite m < n of (m + p(m)), where p(m) is the least
prime divisor of m. Is it true that F(n) > n for all sufficiently large n?
Does F(n) - n → ∞ as n → ∞?

A question of Erdős, Eggleton, and Selfridge.

Part 1: F(n) > n for all sufficiently large n.
-/
theorem erdos_problem_385a :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ m : ℕ, m < n ∧ ¬ m.Prime ∧ 2 ≤ m ∧ m + m.minFac > n :=
  sorry

/-- Part 2: F(n) - n → ∞ as n → ∞. -/
theorem erdos_problem_385b :
    ∀ C : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ m : ℕ, m < n ∧ ¬ m.Prime ∧ 2 ≤ m ∧ m + m.minFac ≥ n + C :=
  sorry
