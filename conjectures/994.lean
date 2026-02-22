import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Floor.Ring

open Classical Filter MeasureTheory Finset Set

noncomputable section

/-- The Cesàro frequency of visits of the fractional parts {kα} to a set E,
    for k = 1, ..., n. That is, (1/n) · #{1 ≤ k ≤ n : fract(kα) ∈ E}. -/
def cesaroFrequency994 (α : ℝ) (E : Set ℝ) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun (k : ℕ) =>
    Int.fract (((k : ℝ) + 1) * α) ∈ E)).card / (n : ℝ)

/--
Erdős Problem #994 (Khintchine's conjecture, disproved by Marstrand [Ma70]):

Let E ⊆ (0,1) be a measurable subset with Lebesgue measure λ(E). Is it true
that, for almost all α,
  lim_{n → ∞} (1/n) ∑_{1 ≤ k ≤ n} 1_{fract(kα) ∈ E} = λ(E)
for all E?

This is false, and was disproved by Marstrand [Ma70].
-/
theorem erdos_problem_994_conjecture :
    ∀ᵐ α ∂(volume : Measure ℝ),
      ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Ioo 0 1 →
        Tendsto (cesaroFrequency994 α E) atTop
          (nhds (volume E).toReal) :=
  sorry

end
