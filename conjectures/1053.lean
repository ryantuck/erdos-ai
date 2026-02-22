import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Finite.Basic

open Finset Real

noncomputable section

/-!
# Erdős Problem #1053

Call a number k-perfect if σ(n) = kn, where σ(n) is the sum of the divisors
of n. Must k = o(log log n)?

A question of Erdős, as reported in problem B2 of Guy's collection [Gu04].
Guy further writes 'It has even been suggested that there may be only finitely
many k-perfect numbers with k ≥ 3.' These are known as multiply perfect
numbers. When k = 2 this is the definition of a perfect number.
-/

/-- The sum-of-divisors function σ(n) = ∑_{d ∣ n} d. -/
def sumOfDivisors (n : ℕ) : ℕ :=
  (Nat.divisors n).sum id

/-- A natural number n is k-perfect if n ≥ 1 and σ(n) = k · n. -/
def IsMultiplyPerfect (n k : ℕ) : Prop :=
  n ≥ 1 ∧ sumOfDivisors n = k * n

/--
Erdős Problem #1053 [Gu04]:

If n is a k-perfect number (σ(n) = kn), then k = o(log log n) as n → ∞
among multiply perfect numbers.

Equivalently: for every ε > 0, the set of multiply perfect numbers n
with σ(n)/n ≥ ε · log(log(n)) is finite.
-/
theorem erdos_problem_1053 :
    ∀ ε : ℝ, ε > 0 →
    Set.Finite {n : ℕ | ∃ k : ℕ, IsMultiplyPerfect n k ∧
      (k : ℝ) ≥ ε * Real.log (Real.log (n : ℝ))} :=
  sorry

end
