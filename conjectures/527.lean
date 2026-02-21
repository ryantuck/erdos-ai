import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

/-- A random variable is Rademacher distributed: it takes values in {-1, 1}
with equal probability. -/
def IsRademacher527 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The partial sum of the random power series ∑_{k=0}^{n-1} ε_k a_k z^k. -/
noncomputable def randomPowerPartialSum527 (ε : ℕ → ℝ) (a : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, ((ε k * a k : ℝ) : ℂ) * z ^ k

/--
Erdős Problem #527 [Er61, p.254]:

Let a_n ∈ ℝ be such that ∑ |a_n|² = ∞ and |a_n| = o(1/√n). Is it true that,
for almost all ε_n = ±1, there exists some z with |z| = 1 (depending on the
choice of signs) such that ∑ ε_n a_n z^n converges?

Proved by Michelen and Sawhney [MiSa25], who showed that the set of such z
has Hausdorff dimension 1.
-/
theorem erdos_problem_527
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hRad : ∀ k, IsRademacher527 μ (ε k))
    (hIndep : iIndepFun ε μ)
    (a : ℕ → ℝ)
    (ha_sq_div : ¬Summable (fun n => a n ^ 2))
    (ha_little_o : Tendsto (fun n => |a n| * Real.sqrt (↑n : ℝ)) atTop (nhds 0)) :
    ∀ᵐ ω ∂μ, ∃ z : ℂ, ‖z‖ = 1 ∧
      ∃ S : ℂ, Tendsto (randomPowerPartialSum527 (fun k => ε k ω) a z) atTop (nhds S) :=
  sorry

end
