import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators Finset

/--
A finite set A of natural numbers is **square-sum free** if no nonempty subset
of A has a sum that is a perfect square.
-/
def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powerset, S ≠ ∅ → ¬∃ k : ℕ, S.sum id = k ^ 2

/--
Erdős Problem #587 [Er89]:

What is the size of the largest A ⊆ {1,…,N} such that, for all nonempty S ⊆ A,
∑_{n ∈ S} n is not a perfect square?

Erdős observed that |A| ≫ N^{1/3} is possible, by taking the first ≈ N^{1/3}
multiples of some prime p ≈ N^{2/3}. Nguyen and Vu proved that
|A| ≪ N^{1/3} (log N)^{O(1)}, essentially solving the problem.

Upper bound: there exist constants C, C' > 0 such that for all sufficiently
large N, any square-sum free A ⊆ {1,…,N} satisfies
|A| ≤ C · N^{1/3} · (log N)^{C'}.
-/
theorem erdos_problem_587_upper :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N →
        ∀ (A : Finset ℕ),
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
          SquareSumFree A →
          (A.card : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 3) * (Real.log N) ^ C' :=
  sorry

/--
Lower bound: there exist square-sum free subsets of {1,…,N} of size ≫ N^{1/3}.
-/
theorem erdos_problem_587_lower :
    ∃ c : ℝ, 0 < c ∧
      ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N →
        ∃ (A : Finset ℕ),
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
          SquareSumFree A ∧
          c * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (A.card : ℝ) :=
  sorry
