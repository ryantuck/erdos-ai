import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset

/--
A subset A of ℕ × ℕ contains the vertices of an axis-aligned square if there exist
a, b, d with d ≥ 1 such that all four corners (a,b), (a+d,b), (a,b+d), (a+d,b+d) lie in A.
-/
def ContainsAxisAlignedSquare (A : Finset (ℕ × ℕ)) : Prop :=
  ∃ a b d : ℕ, d ≥ 1 ∧
    (a, b) ∈ A ∧ (a + d, b) ∈ A ∧ (a, b + d) ∈ A ∧ (a + d, b + d) ∈ A

/--
Erdős Problem #658:
For any δ > 0, for all sufficiently large N, if A ⊆ {1,...,N}² has |A| ≥ δN²
then A must contain the vertices of an axis-aligned square.

This is a problem originally attributed to Graham. The qualitative statement
follows from the density Hales-Jewett theorem proved by Furstenberg and Katznelson.
A quantitative proof was given by Solymosi.
-/
theorem erdos_problem_658 :
    ∀ δ : ℝ, δ > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset (ℕ × ℕ),
          A ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N →
          (A.card : ℝ) ≥ δ * (N : ℝ) ^ 2 →
          ContainsAxisAlignedSquare A :=
  sorry
