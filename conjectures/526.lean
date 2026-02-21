import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring

open MeasureTheory ProbabilityTheory Filter Finset BigOperators Set

noncomputable section

/-- Point y is covered by an arc of length ℓ starting at x on the unit circle ℝ/ℤ.
    The clockwise arc-distance from x to y is the fractional part of (y - x). -/
def circArcCovers (x y ℓ : ℝ) : Prop :=
  Int.fract (y - x) < ℓ

/-- The full unit circle [0,1) is covered by arcs at centers ω(n) of lengths a(n). -/
def circleFullyCovered (ω a : ℕ → ℝ) : Prop :=
  ∀ y : ℝ, 0 ≤ y → y < 1 → ∃ n : ℕ, circArcCovers (ω n) y (a n)

/--
Erdős Problem #526 [Er61, p.253] (Solved by Shepp [Sh72]):

Dvoretzky's covering problem. Let aₙ ≥ 0 with aₙ → 0 and ∑ aₙ = ∞. If we
independently and uniformly place random arcs of length aₙ on the unit circle,
Shepp showed the circle is covered with probability 1 if and only if
  ∑ₙ exp(a₁ + ⋯ + aₙ) / n² = ∞.

The probability space (Ω, μ) carries independent Uniform[0,1) random variables
X(n) giving the starting point of the n-th arc.
-/
theorem erdos_problem_526
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (a : ℕ → ℝ)
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (ha_tendsto : Tendsto a atTop (nhds 0))
    (ha_diverges : ¬Summable a)
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_unif : ∀ n, Measure.map (X n) μ = volume.restrict (Ico (0 : ℝ) 1))
    (hX_indep : iIndepFun X μ) :
    (∀ᵐ ω ∂μ, circleFullyCovered (fun n => X n ω) a) ↔
      ¬Summable (fun n => Real.exp (∑ i ∈ range (n + 1), a i) / ((n : ℝ) + 1) ^ 2) :=
  sorry

end
