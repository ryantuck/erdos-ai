import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
The set of unitary divisors of n: those d dividing n with gcd(d, n/d) = 1.
-/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => Nat.Coprime d (n / d)

/--
A natural number n ≥ 1 is a unitary perfect number if n equals the sum of its
unitary divisors other than n itself, i.e., σ*(n) - n = n where σ*(n) is the
sum of unitary divisors of n.
-/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  1 ≤ n ∧ ((unitaryDivisors n).filter (· ≠ n)).sum id = n

/--
Erdős Problem #1052 [Gu04]:

A unitary divisor of n is d ∣ n such that gcd(d, n/d) = 1. A number n ≥ 1 is a
unitary perfect number if it is the sum of its unitary divisors (aside from n
itself).

Are there only finitely many unitary perfect numbers?

Carlitz, Erdős, and Subbarao offer $10 for settling this question. There are
five known unitary perfect numbers: 6, 60, 90, 87360,
146361946186458562560000.
-/
theorem erdos_problem_1052 :
    Set.Finite {n : ℕ | IsUnitaryPerfect n} :=
  sorry
