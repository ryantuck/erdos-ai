import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Real Filter Topology

noncomputable section

/-- The Erdős separation condition: for all distinct elements x, y and all
    positive integers k, we have |k * x - y| ≥ 1. -/
def ErdosSeparated (a : ℕ → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ k : ℕ, 0 < k → |↑k * a i - a j| ≥ 1

/--
Erdős Problem #143a [Er61, Er73, Er77c, Er92c, Er97c]:
Let A ⊂ (1,∞) be a countably infinite set such that for all distinct x, y ∈ A
and positive integers k, |kx − y| ≥ 1. Does this imply that
  ∑_{x ∈ A} 1/(x log x) < ∞?
-/
theorem erdos_problem_143a
    (a : ℕ → ℝ) (ha_inj : Function.Injective a)
    (ha_gt : ∀ i, 1 < a i)
    (ha_sep : ErdosSeparated a) :
    Summable (fun i => 1 / (a i * Real.log (a i))) :=
  sorry

/--
Erdős Problem #143b [Er61, Er73, Er77c, Er92c, Er97c]:
Let A ⊂ (1,∞) be a countably infinite set such that for all distinct x, y ∈ A
and positive integers k, |kx − y| ≥ 1. Does this imply that
  ∑_{x < n, x ∈ A} 1/x = o(log n)?

Proved by Koukoulopoulos, Lamzouri, and Lichtman [KLL25].
-/
theorem erdos_problem_143b
    (a : ℕ → ℝ) (ha_inj : Function.Injective a)
    (ha_gt : ∀ i, 1 < a i)
    (ha_sep : ErdosSeparated a) :
    Tendsto
      (fun n : ℕ =>
        (∑' i, if a i < (n : ℝ) then 1 / a i else 0) / Real.log (n : ℝ))
      atTop (𝓝 0) :=
  sorry

end
