import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Hausdorff

open scoped ENNReal
open Polynomial MeasureTheory

/-- The unit level curve of a complex polynomial p: the set of z ∈ ℂ with |p(z)| = 1. -/
def levelCurveUnit (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ = 1}

/-- The arc length of a subset of ℂ, given by the 1-dimensional Hausdorff measure. -/
noncomputable def arcLength (S : Set ℂ) : ℝ≥0∞ :=
  Measure.hausdorffMeasure 1 S

/--
Erdős-Herzog-Piranian Conjecture (Problem #114) [EHP58]:
If p(z) ∈ ℂ[z] is a monic polynomial of degree n ≥ 1, then the length of the
curve {z ∈ ℂ : |p(z)| = 1} is maximized when p(z) = z^n - 1.

That is, for every monic polynomial p of degree n,
  length({z : |p(z)| = 1}) ≤ length({z : |z^n - 1| = 1}).

Known partial results:
- The curve for p(z) = z^n - 1 has length 2n + O(1), so the conjecture implies
  the maximal length f(n) satisfies f(n) = 2n + O(1).
- Dolzhenko (1961): f(n) ≤ 4πn.
- Borwein (1995): f(n) ≪ n.
- Eremenko–Hayman (1999): f(n) ≤ 9.173n; full conjecture holds for n = 2.
- Danchenko (2007): f(n) ≤ 2πn.
- Fryntov–Nazarov (2008): f(n) ≤ 2n + O(n^{7/8}); z^n - 1 is a local maximiser.
- Tao (2025): z^n - 1 is the unique maximiser (up to rotation) for all large n.
-/
theorem erdos_problem_114 :
    ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤
      arcLength (levelCurveUnit ((X : Polynomial ℂ) ^ n - 1)) :=
  sorry
