import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

namespace Erdos1144

/-- A random variable is Rademacher distributed: takes values ±1 with equal probability. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The random completely multiplicative function built from Rademacher signs at primes.
    For n ≥ 1: f(n) = ∏_{p ∈ primeFactors(n)} ε(p)^{v_p(n)}.
    For n = 0: f(0) = 0. -/
noncomputable def randMultFun {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else ∏ p ∈ n.factorization.support, (ε p ω) ^ (n.factorization p)

/-- The partial sum ∑_{m=1}^{N} f(m). -/
noncomputable def partialSum {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, randMultFun ε ω m

/--
Erdős Problem #1144 [Va99, 1.11]:

Let f be a random completely multiplicative function, where for each prime p
we independently choose f(p) ∈ {-1, 1} uniformly at random. Is it true that
  limsup_{N → ∞} (∑_{m ≤ N} f(m)) / √N = ∞
with probability 1?

This model is sometimes called a Rademacher random multiplicative function.
Atherfold [At25] proved that, almost surely,
  ∑_{m ≤ N} f(m) ≪ N^{1/2} (log N)^{1+o(1)}.

Tags: number theory, probability
-/
theorem erdos_problem_1144
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∀ᵐ ω ∂μ, ∀ C : ℝ,
      ∃ᶠ N in atTop,
        partialSum ε ω N > C * Real.sqrt (N : ℝ) :=
  sorry

end Erdos1144
