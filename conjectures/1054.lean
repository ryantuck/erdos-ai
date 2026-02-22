import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #1054

Let f(n) be the minimal integer m such that n is the sum of the k smallest
divisors of m for some k ≥ 1.

Is it true that f(n) = o(n)? Or is this true only for almost all n, and
limsup f(n)/n = ∞?

A question of Erdős reported in problem B2 of Guy's collection [Gu04].
The function f(n) is undefined for n = 2 and n = 5, but is likely well-defined
for all n ≥ 6 (which would follow from a strong form of Goldbach's conjecture).

The strong claim that f(n) = o(n) was disproved by Tao, who proved that
the upper density of {n : f(n) ≤ δn} is O(δ²). The remaining open question
is whether limsup f(n)/n = ∞.
-/

/-- The sorted list of divisors of m in increasing order. -/
def sortedDivisors (m : ℕ) : List ℕ :=
  (Nat.divisors m).sort (· ≤ ·)

/-- Whether n equals the sum of the k smallest divisors of m, for some k ≥ 1. -/
def isSumOfSmallestDivisors (n m : ℕ) : Prop :=
  ∃ k : ℕ, k ≥ 1 ∧ ((sortedDivisors m).take k).sum = n

/-- f(n) is the minimal m such that n equals the sum of the k smallest divisors
    of m for some k ≥ 1. Returns 0 if no such m exists. -/
noncomputable def erdos1054_f (n : ℕ) : ℕ :=
  sInf {m : ℕ | isSumOfSmallestDivisors n m}

/--
Erdős Problem #1054 [Gu04]:

limsup_{n → ∞} f(n)/n = ∞, where f(n) is the minimal m such that n equals
the sum of the k smallest divisors of m for some k ≥ 1.

Equivalently: for every C > 0 and every N, there exists n ≥ N such that
f(n) > C · n.
-/
theorem erdos_problem_1054 :
    ∀ C : ℝ, C > 0 → ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      (erdos1054_f n : ℝ) > C * (n : ℝ) :=
  sorry

end
