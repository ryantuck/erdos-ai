import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
A finite set A of natural numbers has **distinct subset sums** if for any two
subsets S₁, S₂ ⊆ A, equality of their sums implies S₁ = S₂.
-/
def DistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ S₁ ∈ A.powerset, ∀ S₂ ∈ A.powerset,
    S₁.sum id = S₂.sum id → S₁ = S₂

/--
Erdős Problem #1 [Er56, Er57, Er61, Er65b, Er73, ErGr80, Er98]:

If A ⊆ {1,…,N} with |A| = n is such that the subset sums ∑_{a ∈ S} a are
distinct for all S ⊆ A, then N ≫ 2ⁿ, i.e., there exists an absolute constant
C > 0 such that N ≥ C · 2ⁿ.

The powers of 2 show that 2ⁿ would be best possible. Erdős called this
"perhaps my first serious problem" (dating it to 1931). The best known lower
bound is N ≥ C(n, ⌊n/2⌋), proved by Dubroff, Fox, and Xu (2021).
-/
theorem erdos_problem_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N n : ℕ) (A : Finset ℕ),
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        A.card = n →
        DistinctSubsetSums A →
        (N : ℝ) ≥ C * 2 ^ n :=
  sorry
