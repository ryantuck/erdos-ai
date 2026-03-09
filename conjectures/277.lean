import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic

open Finset Nat

/-- The sum of divisors function σ(n) = Σ_{d | n} d. -/
def sumDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/--
A covering system with moduli dividing n: a finite collection of congruences
{aᵢ (mod mᵢ)} where each mᵢ divides n, and every integer belongs to at least
one congruence class.
-/
def HasCoveringSystemWithDivisors (n : ℕ) : Prop :=
  ∃ (k : ℕ) (a : Fin k → ℤ) (m : Fin k → ℕ),
    (∀ i, 0 < m i) ∧
    (∀ i, m i ∣ n) ∧
    (∀ x : ℤ, ∃ i, x % (m i : ℤ) = a i % (m i : ℤ))

/--
Erdős Problem #277 [Er77c, ErGr80, Er82e]:

Is it true that, for every c, there exists an n such that σ(n) > cn but there
is no covering system whose moduli all divide n?

This was answered affirmatively by Haight [Ha79].
-/
theorem erdos_problem_277 :
    ∀ c : ℕ, ∃ n : ℕ, 0 < n ∧
      sumDivisors n > c * n ∧
      ¬ HasCoveringSystemWithDivisors n :=
  sorry
