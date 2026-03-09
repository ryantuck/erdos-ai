import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree

open Finset BigOperators

/--
A natural number is a **semiprime with distinct prime factors** if it is the
product of exactly two distinct primes, i.e., n = p · q with p < q both prime.
-/
def IsTwoDistinctPrimeProduct (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q

/--
Erdős Problem #306 [ErGr80]:

Let a/b ∈ ℚ_{>0} with b squarefree. Are there integers 1 < n₁ < ⋯ < n_k,
each the product of two distinct primes, such that
  a/b = 1/n₁ + ⋯ + 1/n_k?

For the analogous question with each nᵢ the product of three distinct primes,
the answer is yes when b = 1, as proved by Butler, Erdős, and Graham [BEG15].
-/
theorem erdos_problem_306 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hbsf : Squarefree b) :
    ∃ S : Finset ℕ,
      (∀ n ∈ S, IsTwoDistinctPrimeProduct n) ∧
      ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (a : ℚ) / (b : ℚ) :=
  sorry
