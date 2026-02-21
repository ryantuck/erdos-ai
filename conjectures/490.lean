import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/--
The products ab with a ∈ A and b ∈ B are all distinct: the multiplication
map A × B → ℕ is injective.
-/
def HasDistinctProducts (A B : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
    a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂

/--
Erdős Problem #490 (proved by Szemerédi):
If A, B ⊆ {1, ..., N} are such that all products ab (a ∈ A, b ∈ B) are distinct,
then |A| · |B| ≪ N² / log N.

Formally: there exists a constant C > 0 such that for all N and all A, B ⊆ {1, ..., N}
with distinct products, |A| · |B| ≤ C · N² / log N.
-/
theorem erdos_problem_490 :
  ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ) (A B : Finset ℕ),
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
      HasDistinctProducts A B →
      (A.card : ℝ) * (B.card : ℝ) ≤ C * ((N : ℝ) ^ 2 / Real.log (N : ℝ)) := by
  sorry
