import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic

open Finset Equiv.Perm BigOperators Matrix

/--
A real n×n matrix is **doubly stochastic** if all entries are non-negative
and every row and column sums to 1.
-/
def IsDoublyStochasticReal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧
  (∀ i, ∑ j, M i j = 1) ∧
  (∀ j, ∑ i, M i j = 1)

/--
Erdős Problem #499 [Er61, Er81]:

Let M = (a_{ij}) be a real n×n doubly stochastic matrix. Does there exist
some σ ∈ Sₙ such that ∏_{1 ≤ i ≤ n} a_{i,σ(i)} ≥ n⁻ⁿ?

This is a weaker form of van der Waerden's conjecture. It was proved by
Marcus and Minc [MaMi62].
-/
theorem erdos_problem_499
    {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsDoublyStochasticReal M) :
    ∃ σ : Equiv.Perm (Fin n),
      ∏ i, M i (σ i) ≥ (1 : ℝ) / (n : ℝ) ^ n :=
  sorry
