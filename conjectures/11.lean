import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree

/--
Erdős Problem #11 [Er77c, ErGr80, Er85c, Er90, Er92c, Er97, Er97e, Er97f]:

Is every large odd integer n the sum of a squarefree number and a power of 2?
-/
theorem erdos_problem_11 :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ¬Even n →
      ∃ (s k : ℕ), Squarefree s ∧ s > 0 ∧ n = s + 2 ^ k :=
  sorry
