import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/-!
# Erdős Problem #1052

A unitary divisor of n is d ∣ n such that gcd(d, n/d) = 1. A number n ≥ 1 is a
unitary perfect number if it is the sum of its unitary divisors (aside from n
itself).

Are there only finitely many unitary perfect numbers?

A problem of Carlitz, Erdős, and Subbarao [Gu04]. The five known unitary perfect
numbers are 6, 60, 90, 87360, and 146361946186458562560000. There are no odd
unitary perfect numbers.
-/

/-- The set of unitary divisors of n: those d ∣ n with gcd(d, n/d) = 1. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  (Finset.filter (fun d => d ∣ n ∧ Nat.gcd d (n / d) = 1) (Finset.range (n + 1)))

/-- The sum of proper unitary divisors of n (excluding n itself). -/
def unitaryAliquotSum (n : ℕ) : ℕ :=
  ((unitaryDivisors n).filter (· ≠ n)).sum id

/-- A unitary perfect number is n ≥ 1 such that the sum of its proper unitary
    divisors equals n. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  n ≥ 1 ∧ unitaryAliquotSum n = n

/--
Erdős Problem #1052 [Gu04]:

There are only finitely many unitary perfect numbers.
-/
theorem erdos_problem_1052 : Set.Finite {n : ℕ | IsUnitaryPerfect n} :=
  sorry
