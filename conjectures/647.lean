import Mathlib.NumberTheory.Divisors

open Finset

/-!
# Erdős Problem #647

Let τ(n) count the number of divisors of n. Is there some n > 24 such that
max_{m < n}(m + τ(m)) ≤ n + 2?

A problem of Erdős and Selfridge. This is true for n = 24.

Reference: [Er79, Er79d, Er92e, Er95c]
https://www.erdosproblems.com/647
-/

/-- The number of divisors function τ(n). -/
noncomputable def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/--
Erdős Problem #647 [Er79, Er79d, Er92e, Er95c]:

Is there some n > 24 such that m + τ(m) ≤ n + 2 for all m < n?
-/
theorem erdos_problem_647 :
    ∃ n : ℕ, n > 24 ∧ ∀ m : ℕ, m < n → m + tau m ≤ n + 2 :=
  sorry
