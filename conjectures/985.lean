import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/--
Erdős Problem #985 [Er65b]:

Is it true that, for every prime p, there is a prime q < p which is a primitive
root modulo p?

A primitive root modulo p means an element of multiplicative order p - 1 in
ℤ/pℤ. The case p = 2 is excluded since there is no prime less than 2.

Artin conjectured that 2 is a primitive root for infinitely many primes p,
which Hooley proved assuming the Generalised Riemann Hypothesis. Heath-Brown
proved that at least one of 2, 3, or 5 is a primitive root for infinitely
many primes p.
-/
theorem erdos_problem_985 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf ((q : ZMod p)) = p - 1 :=
  sorry
