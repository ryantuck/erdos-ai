import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/-!
# Erdős Problem #1052

*Reference:* [erdosproblems.com/1052](https://www.erdosproblems.com/1052)
(page last edited 28 September 2025; accessed 2026-02-22 and 2026-03-06).

A unitary divisor of $n$ is $d \mid n$ such that $(d, n/d) = 1$. A number
$n \geq 1$ is a unitary perfect number if it is the sum of its unitary
divisors (aside from $n$ itself).

Are there only finitely many unitary perfect numbers?

The problem is **OPEN**; a \$10 prize is attached. Guy [Gu04] reports that
Carlitz, Erdős, and Subbarao offer \$10 for settling this question, and that
Subbarao offers 10 cents for each new example. There are no odd unitary
perfect numbers. There are five known unitary perfect numbers
(OEIS [A002827](https://oeis.org/A002827)):
$$6, \quad 60, \quad 90, \quad 87360, \quad 146361946186458562560000.$$
This is problem B3 in Guy's collection [Gu04].

The authoritative upstream formalization of this problem lives in
google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/1052.lean`, linked from the problem page's
"Formalised statement? Yes") and is not present in this repository; this file
is the raw first pass.

[Gu04] Guy, Richard K., _Unsolved problems in number theory_. 3rd ed.,
Springer (2004), xviii+437. Problem B3.
-/

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

Guy [Gu04] reports that Carlitz, Erdős, and Subbarao offer $10 for settling
this question. There are five known unitary perfect numbers: 6, 60, 90,
87360, 146361946186458562560000.

Note: the problem is open; per this repository's raw-file convention, the
statement below directly asserts the "yes" (finiteness) direction of the
question as asked.
-/
theorem erdos_problem_1052 :
    Set.Finite {n : ℕ | IsUnitaryPerfect n} :=
  sorry

/--
There are no odd unitary perfect numbers, i.e., every unitary perfect number
is even (stated as `2 ∣ n`). Recorded as a remark on the problem page.
-/
theorem erdos_problem_1052.variants.even (n : ℕ) (hn : IsUnitaryPerfect n) :
    2 ∣ n :=
  sorry

/--
The five known unitary perfect numbers (OEIS A002827):
6, 60, 90, 87360, and 146361946186458562560000.
-/
theorem erdos_problem_1052.variants.known_examples :
    IsUnitaryPerfect 6 ∧ IsUnitaryPerfect 60 ∧ IsUnitaryPerfect 90 ∧
      IsUnitaryPerfect 87360 ∧ IsUnitaryPerfect 146361946186458562560000 :=
  sorry
