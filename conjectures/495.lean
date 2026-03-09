import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean

/--
The distance from a real number to the nearest integer.
-/
noncomputable def distToNearestInt (x : ℝ) : ℝ :=
  |x - round x|

/--
Erdős Problem #495 [Er61] — the Littlewood conjecture:

Let α, β ∈ ℝ. Is it true that
  lim inf_{n → ∞} n ‖nα‖ ‖nβ‖ = 0
where ‖x‖ is the distance from x to the nearest integer?

Equivalently, for every ε > 0, there exist arbitrarily large n such that
n · ‖nα‖ · ‖nβ‖ < ε.
-/
theorem erdos_problem_495 (α β : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) < ε :=
  sorry
