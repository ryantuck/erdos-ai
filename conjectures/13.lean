import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset

/--
The property that there are no a, b, c ∈ A such that a ∣ (b + c) and a < min(b, c).
-/
def Property13 (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < min b c → ¬ (a ∣ (b + c))

/--
Erdős Problem #13:
Let A ⊆ {1, ..., N} be such that there are no a, b, c ∈ A such that a ∣ (b + c)
and a < min(b, c). Is it true that |A| ≤ N/3 + O(1)?
-/
theorem erdos_problem_13_conjecture :
  ∃ C : ℝ, ∀ N : ℕ, ∀ A : Finset ℕ,
    (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
    Property13 A →
    (A.card : ℝ) ≤ (N : ℝ) / 3 + C :=
sorry
