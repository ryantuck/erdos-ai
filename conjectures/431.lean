import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SymmDiff

/-!
# Erdős Problem #431

Are there two infinite sets A and B of natural numbers such that the sumset
A + B = {a + b | a ∈ A, b ∈ B} agrees with the set of prime numbers up to
finitely many exceptions?

This is a problem of Ostmann, sometimes known as the 'inverse Goldbach problem'.
The expected answer is no.

Elsholtz and Harper [ElHa15] showed that if A, B are such sets then for all
large x we must have x^{1/2}/(log x · log log x) ≪ |A ∩ [1,x]| ≪ x^{1/2} · log log x
and similarly for B.

Elsholtz [El01] proved there are no sets A, B, C (all of size at least 2) such that
A + B + C agrees with the primes up to finitely many exceptions.
-/

/--
Erdős Problem #431 [Er61, ErGr80]:

There do not exist two infinite sets A and B of natural numbers such that the
sumset A + B = {a + b | a ∈ A, b ∈ B} agrees with the set of prime numbers
up to finitely many exceptions (i.e., the symmetric difference is finite).
-/
theorem erdos_problem_431 :
    ¬ ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      (symmDiff (Set.image2 (· + ·) A B) {n | n.Prime}).Finite :=
  sorry
