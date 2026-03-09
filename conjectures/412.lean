import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/--
The sum of divisors function σ(n) = ∑_{d | n} d.
-/
noncomputable def sumDivisors (n : ℕ) : ℕ :=
  (Nat.divisors n).sum id

/--
The k-th iterate of the sum of divisors function:
σ₀(n) = n, σₖ(n) = σ(σₖ₋₁(n)).
-/
noncomputable def iterSumDivisors : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => sumDivisors (iterSumDivisors k n)

/--
Erdős Problem #412 [Er79d, ErGr80]:

Let σ₁(n) = σ(n), the sum of divisors function, and σₖ(n) = σ(σₖ₋₁(n)).
Is it true that, for every m, n ≥ 2, there exist some i, j such that
σᵢ(m) = σⱼ(n)?

This conjecture, attributed to van Wijngaarden, asks whether the iterated
sum of divisors function eventually produces a single shared sequence for
all starting values ≥ 2.
-/
theorem erdos_problem_412 :
    ∀ m n : ℕ, 2 ≤ m → 2 ≤ n →
      ∃ i j : ℕ, iterSumDivisors i m = iterSumDivisors j n :=
  sorry
