import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Polynomial MeasureTheory Complex

noncomputable section

/-- The sublevel set (lemniscate) of a polynomial f: {z ∈ ℂ : ‖f(z)‖ ≤ 1}. -/
def sublevelSet1043 (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

/-- Projection of a subset of ℂ onto the line through the origin at angle θ:
    the set {Re(z) · cos θ + Im(z) · sin θ | z ∈ S}. -/
def lineProjection1043 (S : Set ℂ) (θ : ℝ) : Set ℝ :=
  {t : ℝ | ∃ z ∈ S, t = z.re * Real.cos θ + z.im * Real.sin θ}

/--
Erdős Problem #1043 [EHP58]:

Let f ∈ ℂ[x] be a monic non-constant polynomial. Must there exist a straight
line ℓ such that the projection of {z : |f(z)| ≤ 1} onto ℓ has measure at
most 2?

A problem of Erdős, Herzog, and Piranian. Disproved by Pommerenke [Po61]
(using [Po59]), who showed there exists a monic polynomial f for which the
projection of {z : |f(z)| ≤ 1} onto every line has measure at least 2.386.
On the other hand, Pommerenke also proved there always exists a line such
that the projection has measure at most 3.3.
-/
theorem erdos_problem_1043 :
    ∀ (f : Polynomial ℂ), f.Monic → 1 ≤ f.natDegree →
      ∃ θ : ℝ,
        volume (lineProjection1043 (sublevelSet1043 f) θ) ≤ ENNReal.ofReal 2 :=
  sorry

end
