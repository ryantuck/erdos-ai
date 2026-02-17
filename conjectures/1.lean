import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators

/--
A finset of natural numbers has distinct subset sums if every subset of it
sums to a unique value.
-/
def HasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ s t, s ⊆ A → t ⊆ A → (∑ i ∈ s, i) = (∑ i ∈ t, i) → s = t

/--
Erdős's conjecture on sum-distinct sets (Problem #1):
If A ⊆ {1, ..., N} is a sum-distinct set with |A| = n, then N ≫ 2^n.
This is formalized as: there exists a constant c > 0 such that for any such set A,
its maximum element N satisfies N ≥ c * 2^|A|.
-/
theorem erdos_problem_1_conjecture :
  ∃ c : ℝ, c > 0 ∧ ∀ (A : Finset ℕ),
    A.Nonempty →
    (∀ x ∈ A, x > 0) →
    HasDistinctSubsetSums A →
    ∀ (N : ℕ), (∀ x ∈ A, x ≤ N) →
    (N : ℝ) ≥ c * (2 : ℝ) ^ A.card :=
sorry
