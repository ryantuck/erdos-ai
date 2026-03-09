import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/--
The proper divisors of n (all divisors except n itself).
-/
def Nat.properDivisors' (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).erase n

/--
A natural number n is **pseudoperfect** (or semiperfect) if n can be expressed
as the sum of some subset of its proper divisors.
-/
def IsPseudoperfect (n : ℕ) : Prop :=
  ∃ S ∈ (Nat.properDivisors' n).powerset,
    S.sum id = n

/--
A natural number n is **weird** if σ(n) ≥ 2n (i.e., n is abundant) and n is
not pseudoperfect.
-/
def IsWeird (n : ℕ) : Prop :=
  (Nat.divisors n).sum id ≥ 2 * n ∧ ¬IsPseudoperfect n

/--
A weird number n is **primitive weird** if no proper divisor of n is weird.
-/
def IsPrimitiveWeird (n : ℕ) : Prop :=
  IsWeird n ∧ ∀ d ∈ Nat.properDivisors' n, ¬IsWeird d

/--
Erdős Problem #470 [BeEr74, Er77c, ErGr80]:

Call n weird if σ(n) ≥ 2n and n is not pseudoperfect, that is, it is not
the sum of any subset of its proper divisors.

Part (a): Are there any odd weird numbers?
Part (b): Are there infinitely many primitive weird numbers, i.e. those
such that no proper divisor of n is weird?

The smallest weird number is 70. Benkoski and Erdős proved the set of weird
numbers has positive density. Fang has shown there are no odd weird numbers
below 10²¹.
-/
theorem erdos_problem_470a :
    ¬ ∃ n : ℕ, IsWeird n ∧ n % 2 = 1 :=
  sorry

theorem erdos_problem_470b :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ IsPrimitiveWeird n :=
  sorry
