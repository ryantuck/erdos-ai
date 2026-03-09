import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits

open Polynomial MeasureTheory Set

noncomputable section

/--
The set of non-constant monic real polynomials that split over ℝ with all roots in [-1,1].
-/
def MonicRealRootsInUnitInterval : Set (Polynomial ℝ) :=
  { f : Polynomial ℝ |
    f.Monic ∧
    f.natDegree ≥ 1 ∧
    f.Splits ∧
    (∀ r : ℝ, f.IsRoot r → -1 ≤ r ∧ r ≤ 1) }

/--
The Lebesgue measure of the set {x ∈ ℝ : |f(x)| < 1} for a polynomial f.
-/
def sublevelMeasure (f : Polynomial ℝ) : ENNReal :=
  volume { x : ℝ | |f.eval x| < 1 }

/--
Erdős Problem #1038 [EHP58, p.131]:

Determine the infimum and supremum of |{x ∈ ℝ : |f(x)| < 1}| as f ranges over
all non-constant monic polynomials, all of whose roots are real and in [-1,1].

Erdős, Herzog, and Piranian proved that under the assumption all roots are in
{-1,1}, the measure is at most 2√2, and conjectured this is the best possible
upper bound. The supremum is now known to equal 2√2.

For the infimum, the current best known bounds are:
  2^(4/3) - 1 ≈ 1.519 ≤ inf ≤ 1.835...

The infimum is witnessed to be less than 2 by f(x) = (x+1)(x-1)^m for m ≥ 3.
-/
theorem erdos_problem_1038_sup :
    ⨆ f ∈ MonicRealRootsInUnitInterval, sublevelMeasure f =
      ENNReal.ofReal (2 * Real.sqrt 2) :=
  sorry

theorem erdos_problem_1038_inf :
    ⨅ f ∈ MonicRealRootsInUnitInterval, sublevelMeasure f > 0 :=
  sorry

end
