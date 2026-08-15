import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set

noncomputable section

namespace Erdos1147

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- The set A(α) = { n ≥ 1 : ‖αn²‖ < 1/log n }.
    Note: for n = 1, log n = 0, so the threshold 1/log n = 0 in Lean's field division
    (division by zero returns 0). This causes the membership condition to be false
    (distNearestInt ≥ 0 cannot be < 0), effectively excluding n = 1 from A(α).
    This is mathematically harmless for the additive basis property. -/
def setA (α : ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ distNearestInt (α * (↑n) ^ 2) < 1 / Real.log (↑n)}

/-- A set S ⊆ ℕ is an additive basis of order 2 if every sufficiently large
    natural number can be written as a sum of two elements from S. -/
def IsAdditiveBasisOrder2 (S : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ∃ a ∈ S, ∃ b ∈ S, n = a + b

/--
Erdős Problem #1147 [Va99, 1.21] (Disproved):

Let α > 0 be an irrational number. Is the set
  A = { n ≥ 1 : ‖αn²‖ < 1/log n },
where ‖·‖ denotes the distance to the nearest integer, an additive basis
of order 2?

This was disproved by Konieczny [Ko16b]. In particular, for α = √2,
the set A is not an additive basis of order 2.

More generally, for any ε(n) → 0, the set { n ≥ 1 : ‖αn²‖ < ε(n) }
is not an additive basis of order 2 for almost every α > 0.

Tags: irrational, additive basis

## References

[Va99]: Vaughan, R.C., *The Hardy-Littlewood method*, 2nd edition, Cambridge University Press, 1997.
[Ko16b]: Konieczny, J., 2016.
-/
theorem erdos_problem_1147 :
    answer(False) ↔ IsAdditiveBasisOrder2 (setA (Real.sqrt 2)) :=
  sorry

/-- Generalization: for any monotone decreasing sequence ε(n) → 0,
    the set { n ≥ 1 : ‖αn²‖ < ε(n) } is not an additive basis of order 2
    for almost every α > 0. (Stated without proof as a conjecture variant.) -/
theorem erdos_problem_1147_generalized (ε : ℕ → ℝ) (ε_pos : ∀ n : ℕ, ε n > 0)
    (ε_tendsto : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    (∀ α : ℝ, α > 0 → ¬ IsAdditiveBasisOrder2 {n : ℕ | n ≥ 1 ∧
      distNearestInt (α * (↑n) ^ 2) < ε n}) :=
  sorry

end Erdos1147
