import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic

open Finset Classical

noncomputable section

/-!
# Erdős Problem #1136

Does there exist A ⊆ ℕ with lower density > 1/3 such that a + b ≠ 2^k for
any a, b ∈ A and k ≥ 0?

A question asked by Erdős at the DMV conference in Berlin 1987. Achieving
density 1/3 is trivial, taking A to be all multiples of 3.

Müller [Mu11] settled this question in the affirmative: one can take A to be
the set of all integers congruent to 3 · 2^i (mod 2^{i+2}) for any i ≥ 0,
which has density 1/2. Müller also proved this is best possible, in that
such A has lower density at most 1/2.
-/

/-- A set A ⊆ ℕ is power-of-2 sum-free if no two elements (not necessarily
    distinct) sum to a power of 2. -/
def PowerOfTwoSumFree (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → ∀ k : ℕ, a + b ≠ 2 ^ k

/-- The counting function |A ∩ [1, N]| for a set A ⊆ ℕ. -/
noncomputable def countInInterval1136 (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
Erdős Problem #1136 (Proved by Müller [Mu11]):
There exists A ⊆ ℕ with lower density strictly greater than 1/3 such that
no two elements of A sum to a power of 2.

The lower density condition is formalized as: there exists δ > 1/3 and N₀
such that |A ∩ [1, N]| ≥ δ · N for all N ≥ N₀.
-/
theorem erdos_problem_1136 :
    ∃ (A : Set ℕ),
      PowerOfTwoSumFree A ∧
      ∃ (δ : ℝ), δ > 1/3 ∧
        ∃ (N₀ : ℕ), ∀ (N : ℕ), N ≥ N₀ →
          δ * (N : ℝ) ≤ (countInInterval1136 A N : ℝ) :=
  sorry

end
