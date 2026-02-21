import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

/-- A random variable is Rademacher distributed: it takes values in {-1, 1}
with equal probability. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The supremum of |∑_{k=0}^n ε_k z^k| over the unit circle |z| = 1. -/
noncomputable def supNormCircle (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
    x = ‖(∑ k ∈ Finset.range (n + 1), (ε k : ℂ) * z ^ k)‖}

/--
Erdős Problem #523:
Let f(z) = ∑_{k=0}^n ε_k z^k be a random polynomial, where ε_k ∈ {-1, 1}
independently uniformly at random.

Does there exist some constant C > 0 such that, almost surely,
  max_{|z|=1} |∑_{k≤n} ε_k z^k| = (C + o(1))√(n log n)?

Salem and Zygmund proved that √(n log n) is the right order of magnitude.
This was settled by Halász, who proved this is true with C = 1.
-/
theorem erdos_problem_523
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => supNormCircle (fun k => ε k ω) n /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
      atTop (nhds C) :=
  sorry
