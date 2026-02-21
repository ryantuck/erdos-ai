import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators Set

/-- A random variable is Rademacher distributed: it takes values in {-1, 1}
with equal probability. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The supremum of |∑_{k=1}^n ε_k x^k| over x ∈ [-1, 1]. -/
noncomputable def supNormInterval (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ x : ℝ, x ∈ Icc (-1 : ℝ) 1 ∧
    y = |∑ k ∈ Finset.range n, ε (k + 1) * x ^ (k + 1)|}

/--
Erdős Problem #524:
For any t ∈ (0,1) let t = ∑_{k=1}^∞ ε_k(t) 2^{-k} be the binary expansion
(where ε_k(t) ∈ {0,1}). What is the correct order of magnitude (for almost
all t ∈ (0,1)) for
  M_n(t) = max_{x ∈ [-1,1]} |∑_{k≤n} (-1)^{ε_k(t)} x^k|?

A problem of Salem and Zygmund. The binary digits ε_k(t) are i.i.d.
Bernoulli(1/2) under Lebesgue measure, so (-1)^{ε_k(t)} are i.i.d.
Rademacher random variables.

Known partial results:
- Erdős (unpublished) showed: for a.a. t and every δ > 0,
  lim_{n→∞} M_n(t)/n^{1/2-δ} = ∞.
- Chung showed: for a.a. t, there exist infinitely many n such that
  M_n(t) ≪ (n/log log n)^{1/2}.

Formalized as the Erdős lower bound: for a.a. ω and every δ > 0,
M_n(ω)/n^{1/2-δ} → ∞. The exact order of magnitude remains open.
-/
theorem erdos_problem_524
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∀ᵐ ω ∂μ, ∀ δ > (0 : ℝ),
      Tendsto (fun n => supNormInterval (fun k => ε k ω) n /
        (↑n : ℝ) ^ ((1 : ℝ)/2 - δ))
        atTop atTop :=
  sorry
