import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Classical

/--
A set A ⊆ ℕ is an additive complement of the squares if every sufficiently large
natural number can be written as n² + a for some n ≥ 0 and a ∈ A.
-/
def IsAdditiveComplementOfSquares (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m → ∃ n : ℕ, ∃ a ∈ A, m = n ^ 2 + a

/--
The counting function |A ∩ {1, …, N}| / N^{1/2} for a set A ⊆ ℕ.
-/
noncomputable def sqrtNormalizedCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ) ^ ((1 : ℝ) / 2)

/--
Erdős Problem #33 [Er56, p.134] (OPEN):

Let A ⊆ ℕ be such that every large integer can be written as n² + a for some
a ∈ A and n ≥ 0 (i.e., A is an additive complement of the squares).

Part 1: The limsup of |A ∩ {1,…,N}| / N^{1/2} is finite for some such A,
and we ask for the smallest possible value.

Part 2: Is liminf |A ∩ {1,…,N}| / N^{1/2} > 1 for every such A?

The best known lower bound is liminf ≥ 4/π ≈ 1.273, proved by Cilleruelo,
Habsieger, and Balasubramanian–Ramana.
-/
theorem erdos_problem_33_liminf :
    ∀ A : Set ℕ, IsAdditiveComplementOfSquares A →
      1 < Filter.liminf (fun N : ℕ => sqrtNormalizedCount A N) Filter.atTop :=
  sorry

/--
Erdős Problem #33 (Part 1): There exists an additive complement of the squares
with finite limsup of the normalized counting function.
-/
theorem erdos_problem_33_limsup_finite :
    ∃ A : Set ℕ, IsAdditiveComplementOfSquares A ∧
      ∃ C : ℝ, ∀ N : ℕ, 0 < N → sqrtNormalizedCount A N ≤ C :=
  sorry
