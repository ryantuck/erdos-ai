import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Path
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

open scoped ENNReal
open MeasureTheory Polynomial

noncomputable section

/-!
# Erdős Problem #1041

Let f(z) = ∏_{i=1}^n (z - zᵢ) ∈ ℂ[z] with |zᵢ| < 1 for all i.

Must there always exist a path of length less than 2 in
  {z : |f(z)| < 1}
which connects two of the roots of f?

A problem of Erdős, Herzog, and Piranian [EHP58, p.139], who proved that this
set always has a connected component containing at least two of the roots.
-/

/--
Erdős Problem #1041 [EHP58, p.139]:

Let f(z) = ∏(z - zᵢ) be a monic polynomial over ℂ with all roots in the open
unit disk. Then there exist two roots z₁, z₂ of f and a path γ from z₁ to z₂
contained in {z : ‖f(z)‖ < 1} of 1-dimensional Hausdorff measure less than 2.
-/
theorem erdos_problem_1041 (f : ℂ[X]) (hf : f.Monic) (hdeg : f.natDegree ≥ 2)
    (hroots : f.rootSet ℂ ⊆ Metric.ball 0 1) :
    ∃ (z₁ z₂ : ℂ) (_ : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
      Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
      μH[1] (Set.range γ) < 2 :=
  sorry

end
