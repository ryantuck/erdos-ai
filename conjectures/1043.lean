import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Polynomial MeasureTheory

noncomputable section

/-!
# Erdős Problem #1043

Let f ∈ ℂ[x] be a monic non-constant polynomial. Must there exist a straight
line ℓ such that the projection of { z : |f(z)| ≤ 1 } onto ℓ has measure at
most 2?

A problem of Erdős, Herzog, and Piranian [EHP58].

Pommerenke [Po61] proved that the answer is no, and there exists such an f for
which the projection of this set onto every line has measure at least 2.386.
On the other hand, Pommerenke also proved there always exists a line such that
the projection has measure at most 3.3.
-/

/-- The lemniscate (filled sublevel set) of a complex polynomial p:
    { z ∈ ℂ : ‖p(z)‖ ≤ 1 }. -/
def lemniscate (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ ≤ 1}

/-- The projection of a complex number z onto the line through unit vector u,
    given by Re(z · conj u). When ‖u‖ = 1 this equals the signed coordinate
    along the line through the origin in direction u. -/
def lineProj (u : ℂ) (z : ℂ) : ℝ :=
  (z * starRingEnd ℂ u).re

/--
Erdős Problem #1043 (disproved by Pommerenke [Po61]):

It is NOT the case that for every monic non-constant polynomial f ∈ ℂ[x],
there exists a line ℓ such that the projection of { z : |f(z)| ≤ 1 } onto ℓ
has Lebesgue measure at most 2.
-/
theorem erdos_problem_1043 :
    ¬ ∀ (f : Polynomial ℂ), f.Monic → f.natDegree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
        volume (lineProj u '' lemniscate f) ≤ 2 :=
  sorry

/--
Pommerenke's upper bound [Po61]:

For every monic non-constant polynomial f ∈ ℂ[x], there always exists a line
such that the projection of { z : |f(z)| ≤ 1 } onto that line has Lebesgue
measure at most 3.3.
-/
theorem erdos_problem_1043_weak :
    ∀ (f : Polynomial ℂ), f.Monic → f.natDegree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
        volume (lineProj u '' lemniscate f) ≤ ENNReal.ofReal 3.3 :=
  sorry

end
