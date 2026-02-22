import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

open Complex Polynomial MeasureTheory

noncomputable section

/--
The sublevel set {z : ‖f(z)‖ < 1} for a function f : ℂ → ℂ.
-/
def lemniscateSublevel (f : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | ‖f z‖ < 1}

/--
Λ(f): the supremum of the 1-dimensional Hausdorff measures of the frontiers
of the connected components of {z : ‖f(z)‖ < 1}. A connected component
containing x in the sublevel set S is connectedComponentIn S x.
-/
noncomputable def maxBoundaryLength (f : ℂ → ℂ) : ℝ :=
  sSup {ℓ : ℝ | ∃ x ∈ lemniscateSublevel f,
    ℓ = (Measure.hausdorffMeasure 1
      (frontier (connectedComponentIn (lemniscateSublevel f) x))).toReal}

/--
Erdős Problem #1044 (Erdős–Herzog–Piranian [EHP58]):

Let f(z) = ∏ᵢ₌₁ⁿ (z - zᵢ) ∈ ℂ[z] where |zᵢ| ≤ 1 for all i. If Λ(f)
is the maximum of the lengths of the boundaries of the connected components
of {z : |f(z)| < 1}, then the infimum of Λ(f) over all such f equals 2.

Resolved by Tang, who proved that the infimum of Λ(f) over all such f is 2.
-/
theorem erdos_problem_1044 :
    (∀ (f : Polynomial ℂ), f.Monic → (∀ z, f.IsRoot z → ‖z‖ ≤ 1) →
      maxBoundaryLength (fun z => Polynomial.eval z f) ≥ 2) ∧
    (∀ ε > 0, ∃ (f : Polynomial ℂ), f.Monic ∧ (∀ z, f.IsRoot z → ‖z‖ ≤ 1) ∧
      maxBoundaryLength (fun z => Polynomial.eval z f) < 2 + ε) :=
  sorry

end
