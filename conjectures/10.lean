import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/--
A natural number `n` is the sum of a prime and at most `k` powers of 2
(with distinct exponents) if there exist a prime `p` and a finite set of
exponents `S` with `|S| ≤ k` such that `n = p + ∑_{e ∈ S} 2^e`.
-/
def IsSumPrimeAndPowersOf2 (n k : ℕ) : Prop :=
  ∃ (p : ℕ) (S : Finset ℕ), Nat.Prime p ∧ S.card ≤ k ∧
    n = p + S.sum (2 ^ ·)

/--
Erdős Problem #10 [Er77c, ErGr80, Er85c, Er92c, Er95, Er97, Er97c, Er97e]:

Is there some k such that every sufficiently large integer is the sum of a
prime and at most k powers of 2?

Erdős described this as 'probably unattackable'. Erdős and Graham suggest
that no such k exists.
-/
theorem erdos_problem_10 :
    ∃ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → IsSumPrimeAndPowersOf2 n k :=
  sorry
