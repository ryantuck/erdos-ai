import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Lemmas

open Finset BigOperators

/--
A positive integer `k` is representable as a sum of distinct unit fractions with
denominators from `{1, ..., N}` if there exists a subset `S ⊆ {1, ..., N}` such
that `∑_{n ∈ S} 1/n = k`.
-/
def IsRepresentableUnitFractionSum (N : ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n ∧ n ≤ N) ∧
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (k : ℚ)

/--
Erdős Problem #308 [ErGr80]:

Let N ≥ 1. Is it true that the set of positive integers representable as sums of
distinct unit fractions with denominators from {1, ..., N} has the shape {1, ..., m}
for some m?

That is, there are no "gaps" among the representable integers — for every N there
exists m such that an integer k ≥ 1 is representable if and only if k ≤ m.

This was essentially solved by Croot [Cr99], who showed that if f(N) is the smallest
positive integer not so representable, and m_N = ⌊∑_{n ≤ N} 1/n⌋, then for all
sufficiently large N the set of representable positive integers is either
{1, ..., m_N − 1} or {1, ..., m_N}.
-/
theorem erdos_problem_308 :
    ∀ N : ℕ, 1 ≤ N →
      ∃ m : ℕ, (∀ k : ℕ, 1 ≤ k → k ≤ m → IsRepresentableUnitFractionSum N k) ∧
        (∀ k : ℕ, m < k → ¬ IsRepresentableUnitFractionSum N k) :=
  sorry
