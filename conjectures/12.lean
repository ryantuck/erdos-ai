import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators Classical

/--
Problem #12:
Let A be an infinite set such that there are no distinct a, b, c ∈ A
such that a ∣ (b + c) and b, c > a.
Is there such an A with liminf |A ∩ {1, ..., N}| / N^{1/2} > 0?
-/
def Property12 (A : Set ℕ) : Prop :=
  A.Infinite ∧
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    b ≠ c → a < b → a < c → ¬ (a ∣ (b + c))

/--
Erdős's conjecture on sum-distinct sets (Problem #12):
There exists a set A satisfying Property12 such that
liminf |A ∩ {1, ..., N}| / N^{1/2} > 0.
-/
theorem erdos_problem_12_conjecture :
  ∃ A : Set ℕ, Property12 A ∧
  ∃ c : ℝ, c > 0 ∧
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ((Finset.Ico 1 (N + 1)).filter (· ∈ A)).card ≥ c * Real.sqrt N :=
sorry
