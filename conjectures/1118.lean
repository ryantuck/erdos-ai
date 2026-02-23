import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

noncomputable section
open Complex Set MeasureTheory

namespace Erdos1118

/-- The maximum modulus of f on the circle of radius r:
    M(r) = sup{‖f(z)‖ : ‖z‖ = r}. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- The exceedance set E(c) = {z : ℂ | ‖f(z)‖ > c}. -/
def exceedanceSet (f : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  {z : ℂ | c < ‖f z‖}

/--
Erdős Problem #1118 — Part 1 (Hayman's conjecture, proved by Camera [Ca77]
and Gol'dberg [Go79b]):

Let f(z) be a non-constant entire function such that for some c > 0, the set
E(c) = {z : |f(z)| > c} has finite (Lebesgue) measure. Then
  ∫₀^∞ r / (log log M(r)) dr < ∞
where M(r) = max_{|z|=r} |f(z)|. This growth condition is best possible.
-/
theorem erdos_problem_1118_growth_rate (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hnc : ∃ z : ℂ, f z ≠ f 0)
    (c : ℝ) (hc : 0 < c)
    (hfin : volume (exceedanceSet f c) < ⊤) :
    IntegrableOn (fun r => r / Real.log (Real.log (maxModulus f r)))
      (Ioi 0) volume :=
  sorry

/--
Erdős Problem #1118 — Part 2 (Gol'dberg [Go79b]):

The answer to the second question is negative: there exists a non-constant entire
function f and c > 0 such that E(c) has finite measure, but E(c') has infinite
measure for all 0 < c' < c.

Gol'dberg proved that T = {c > 0 : |E(c)| < ∞} can equal [m, ∞) or (m, ∞)
for any m > 0.
-/
theorem erdos_problem_1118_negative_answer :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z : ℂ, f z ≠ f 0) ∧
      ∃ c : ℝ, 0 < c ∧
        volume (exceedanceSet f c) < ⊤ ∧
        ∀ c' : ℝ, 0 < c' → c' < c → volume (exceedanceSet f c') = ⊤ :=
  sorry

end Erdos1118
