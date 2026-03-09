import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open BigOperators Finset

/--
Two closed intervals [a₁, b₁] and [a₂, b₂] in ℕ are **separated** if they are
non-overlapping and non-adjacent, i.e., b₁ + 1 < a₂ or b₂ + 1 < a₁.
-/
def IntervalsSeparated (a₁ b₁ a₂ b₂ : ℕ) : Prop :=
  b₁ + 1 < a₂ ∨ b₂ + 1 < a₁

/--
Erdős Problem #289 [ErGr80]:

Is it true that, for all sufficiently large k, there exist finite intervals
I₁, …, Iₖ ⊂ ℕ, distinct, non-overlapping, non-adjacent, with |Iᵢ| ≥ 2
for all i, such that

  1 = ∑_{i=1}^{k} ∑_{n ∈ Iᵢ} 1/n ?

Erdős and Graham posed this problem in [ErGr80]. Kovac observed that without the
restriction that the intervals be distinct, non-overlapping, and non-adjacent,
the problem is easily solvable.
-/
theorem erdos_problem_289 :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ (a b : Fin k → ℕ),
        -- Each interval [aᵢ, bᵢ] has at least 2 elements (aᵢ ≤ bᵢ and aᵢ ≥ 1)
        (∀ i, 1 ≤ a i ∧ a i < b i) ∧
        -- All pairs of intervals are separated (non-overlapping and non-adjacent)
        (∀ i j, i ≠ j → IntervalsSeparated (a i) (b i) (a j) (b j)) ∧
        -- The sum of reciprocals over all intervals equals 1
        ∑ i : Fin k, ∑ n ∈ Icc (a i) (b i), (1 : ℝ) / (n : ℝ) = 1 :=
  sorry
