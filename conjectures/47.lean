import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

/--
Erdős's conjecture on unit fractions (Problem #47):
If δ > 0 and N is sufficiently large (depending on δ), and A ⊆ {1, ..., N} is such that
∑_{a ∈ A} 1/a > δ · log N, then there exists a nonempty subset S ⊆ A such that
∑_{n ∈ S} 1/n = 1.

Proved by Bloom, who showed the weaker threshold
∑ 1/n ≫ (log log log N / log log N) · log N suffices.
-/
theorem erdos_problem_47 (δ : ℝ) (hδ : δ > 0) :
  ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
  ∀ A : Finset ℕ,
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
    (∑ a ∈ A, (1 : ℝ) / a) > δ * Real.log N →
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, (1 : ℝ) / n) = 1 :=
sorry
