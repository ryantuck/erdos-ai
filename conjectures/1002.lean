import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter MeasureTheory

noncomputable section

/-!
# Erdős Problem #1002

For any 0 < α < 1, let
  f(α, n) = (1 / log n) ∑_{1 ≤ k ≤ n} (1/2 - {αk})
where {·} denotes the fractional part.

Does f(α, n) have an asymptotic distribution function? In other words, is there
a non-decreasing function g such that g(-∞) = 0, g(∞) = 1, and
  lim_{n → ∞} |{α ∈ (0,1) : f(α,n) ≤ c}| = g(c)
where |·| denotes Lebesgue measure?

Kesten [Ke60] proved the analogous result with an additional shift β:
if f(α, β, n) = (1/log n) ∑_{k=1}^n (1/2 - {β + αk}), then f(α, β, n) has
asymptotic distribution function g(c) = (1/π) ∫_{-∞}^{ρc} 1/(1+t²) dt
where ρ > 0 is an explicit constant.
-/

/-- The function f(α, n) = (1/log n) ∑_{k=1}^{n} (1/2 - {αk}),
    where {·} denotes the fractional part. -/
def erdosF (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, ((1 : ℝ) / 2 - Int.fract (α * ↑k))) / Real.log ↑n

/--
Erdős Problem #1002 [Er64b]:

The function f(α, n) = (1/log n) ∑_{k=1}^n (1/2 - {αk}) has an asymptotic
distribution function. That is, there exists a non-decreasing function
g : ℝ → ℝ with g(-∞) = 0 and g(∞) = 1 such that for every c ∈ ℝ,
  lim_{n → ∞} μ({α ∈ (0,1) : f(α,n) ≤ c}) = g(c)
where μ is Lebesgue measure.
-/
theorem erdos_problem_1002 :
    ∃ g : ℝ → ℝ, Monotone g ∧
    Filter.Tendsto g Filter.atBot (nhds 0) ∧
    Filter.Tendsto g Filter.atTop (nhds 1) ∧
    ∀ c : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        (volume (Set.Ioo (0 : ℝ) 1 ∩ {α : ℝ | erdosF α n ≤ c})).toReal)
      Filter.atTop (nhds (g c)) :=
  sorry

end
