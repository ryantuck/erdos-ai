import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Card

open MeasureTheory ProbabilityTheory Polynomial Filter Finset BigOperators

/-- The polynomial with prescribed ±1 coefficients:
f_n(z) = Σ_{k=0}^{n} ε(k) · z^k. -/
noncomputable def signPoly (ε : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (n + 1), C (ε k) * X ^ k

/-- The number of distinct real roots of a real polynomial. -/
noncomputable def numRealRoots (p : Polynomial ℝ) : ℕ :=
  Set.ncard {x : ℝ | p.IsRoot x}

/-- A random variable is Rademacher distributed: it takes values in {-1, 1}
with equal probability (each with probability 1/2 on a probability space). -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/--
Erdős Problem #521:
Let (ε_k)_{k ≥ 0} be independently uniformly chosen at random from {-1, 1}.
If R_n counts the number of real roots of f_n(z) = Σ_{k=0}^{n} ε_k z^k,
then, almost surely, lim_{n→∞} R_n / log n = 2/π.

Erdős and Offord showed that the number of real roots of a random degree n
polynomial with ±1 coefficients is (2/π + o(1)) log n in expectation.
This conjecture asks whether the convergence holds almost surely.
-/
theorem erdos_problem_521
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (numRealRoots (signPoly (fun k => ε k ω) n) : ℝ) / Real.log (n : ℝ))
      atTop (nhds (2 / Real.pi)) :=
  sorry
