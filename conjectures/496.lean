import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational

/--
Erdős Problem #496 (Oppenheim conjecture, proved by Margulis):
Let α ∈ ℝ be irrational and ε > 0. Then there exist positive integers x, y, z
such that |x² + y² - z²·α| < ε.
-/
theorem erdos_problem_496 (α : ℝ) (hα : Irrational α) (ε : ℝ) (hε : ε > 0) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      |((x : ℝ) ^ 2 + (y : ℝ) ^ 2 - (z : ℝ) ^ 2 * α)| < ε :=
  sorry
