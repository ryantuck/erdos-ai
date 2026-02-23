import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

namespace Erdos1164

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A step distribution for a simple random walk on ℤ²: the random variable takes
    values in {(1,0), (-1,0), (0,1), (0,-1)} each with equal probability. -/
def IsUniformStep (μ : Measure Ω) (X : Ω → ℤ × ℤ) : Prop :=
  (∀ ω, X ω ∈ ({((1 : ℤ), 0), (-1, 0), (0, 1), (0, -1)} : Set (ℤ × ℤ))) ∧
  μ {ω | X ω = (1, 0)} = μ {ω | X ω = (-1, 0)} ∧
  μ {ω | X ω = (-1, 0)} = μ {ω | X ω = (0, 1)} ∧
  μ {ω | X ω = (0, 1)} = μ {ω | X ω = (0, -1)}

/-- Position of the random walk at time n: S_n = X₀ + X₁ + ⋯ + X_{n-1},
    starting at the origin S₀ = (0, 0). -/
def walkPosition (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℤ × ℤ :=
  ∑ i ∈ Finset.range n, X i ω

/-- The covering radius R_n(ω): the largest R ∈ ℕ such that every lattice point
    (a, b) ∈ ℤ² with a² + b² ≤ R² is visited by the walk within its first n steps. -/
noncomputable def coveringRadius (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℕ :=
  sSup {R : ℕ | ∀ (a b : ℤ), a ^ 2 + b ^ 2 ≤ ↑R ^ 2 →
    ∃ k, k ≤ n ∧ walkPosition X ω k = (a, b)}

/--
Erdős Problem #1164 (Erdős–Taylor) [Va99, 6.76]:

Let R_n be the maximal integer such that almost every random walk from the origin
in ℤ² visits every x ∈ ℤ² with ‖x‖ ≤ R_n in at most n steps. Is it true that
  log R_n ≍ √(log n)?

That is, there exist constants c₁, c₂ > 0 such that almost surely, for all
sufficiently large n:
  c₁ · √(log n) ≤ log R_n ≤ c₂ · √(log n).

Proved independently by Révész [Re90] and Kesten. The stronger conjecture
  lim P((log R_n)² / log n ≤ x) = e^{-4x}  for all x > 0
was proved by Dembo, Peres, Rosen, and Zeitouni [DPRZ04].

Tags: probability
-/
theorem erdos_problem_1164
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ᵐ ω ∂μ, ∀ᶠ (n : ℕ) in atTop,
        c₁ * Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (coveringRadius X ω n : ℝ) ∧
        Real.log (coveringRadius X ω n : ℝ) ≤ c₂ * Real.sqrt (Real.log (n : ℝ)) :=
  sorry

end Erdos1164
