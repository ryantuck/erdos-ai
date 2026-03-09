import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finite.Defs

open Nat

/--
The set of prime divisors of a positive natural number n.
-/
def primeFactors' (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p ∣ n}

/--
Erdős Problem #730 [EGRS75]:

Are there infinitely many pairs of integers n ≠ m such that C(2n, n) and
C(2m, m) have the same set of prime divisors?

A problem of Erdős, Graham, Ruzsa, and Straus, who believed there is
'no doubt' that the answer is yes. For example (87, 88) and (607, 608).
-/
theorem erdos_problem_730 :
    Set.Infinite {p : ℕ × ℕ | p.1 < p.2 ∧
      primeFactors' (Nat.centralBinom p.1) = primeFactors' (Nat.centralBinom p.2)} :=
  sorry
