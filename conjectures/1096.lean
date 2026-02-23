import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

noncomputable section

/-- The set of all numbers expressible as ∑_{i ∈ S} q^i for some finite set S ⊆ ℕ. -/
def powerSumSet (q : ℝ) : Set ℝ :=
  {x : ℝ | ∃ S : Finset ℕ, x = S.sum (fun i => q ^ i)}

/--
Erdős Problem #1096 [EJK90, GWNT91]:

Let 1 < q < 1 + ε and consider the set of numbers of the form ∑_{i ∈ S} q^i
(for all finite S ⊆ ℕ), ordered by size as 0 = x₁ < x₂ < ⋯.

Is it true that, provided ε > 0 is sufficiently small, x_{k+1} - x_k → 0?

Equivalently: there exists ε > 0 such that for all q ∈ (1, 1+ε), the gaps between
consecutive elements of the power sum set tend to zero. We formalize this as:
for every δ > 0, every sufficiently large element of the set has a successor
in the set within distance δ.

Erdős and Joó speculate that the threshold may be q₀ ≈ 1.3247, the real root
of x³ = x + 1, i.e., the smallest Pisot-Vijayaraghavan number.

Tags: number theory
-/
theorem erdos_problem_1096 :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : ℝ, 1 < q → q < 1 + ε →
        ∀ δ : ℝ, 0 < δ →
          ∃ M : ℝ, ∀ x ∈ powerSumSet q, M ≤ x →
            ∃ y ∈ powerSumSet q, x < y ∧ y - x < δ :=
  sorry

end
