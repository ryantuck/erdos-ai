import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

open MeasureTheory

/--
Erdős Problem #908 (proved by Laczkovich [La80]):

Let f : ℝ → ℝ be such that for every h > 0, the function x ↦ f(x + h) - f(x)
is measurable. Is it true that f = g + φ + r where g is continuous,
φ is additive (i.e., φ(x + y) = φ(x) + φ(y)), and r(x + h) - r(x) = 0
for every h and almost all (depending on h) x?

A conjecture of de Bruijn and Erdős. Answered in the affirmative by Laczkovich.
See also [907].
-/
theorem erdos_problem_908 (f : ℝ → ℝ)
    (hf : ∀ h : ℝ, h > 0 → Measurable (fun x => f (x + h) - f x)) :
    ∃ g φ r : ℝ → ℝ, Continuous g ∧ (∀ x y : ℝ, φ (x + y) = φ x + φ y) ∧
      (∀ h : ℝ, h > 0 → ∀ᵐ x ∂volume, r (x + h) - r x = 0) ∧
      ∀ x : ℝ, f x = g x + φ x + r x :=
  sorry
